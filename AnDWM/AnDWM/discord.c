#include "discord.h"

#include <curl/curl.h>
#include <json-c/json.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/eventfd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define DISCORD_IPC_MAX 65536
#define DISCORD_USERS_PENDING 32
#define DISCORD_TOKEN_MAX 4096

typedef struct {
	char id[32];
	char username[128];
	char avatar_path[512];
	int speaking;
} Speaker;

typedef struct {
	char access[2048];
	char refresh[2048];
	time_t expires;
	int voice_write;
	int screenshare_read;
	int screenshare_write;
} Token;

static Speaker speakers[DWM_DISCORD_SPEAKERS];
static char pending_users[DISCORD_USERS_PENDING][32];
static size_t pending_count;
static pthread_mutex_t state_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_t worker;
static pthread_t mic_worker;
static int event_fd = -1;
static int started;
static int mic_worker_started;
static _Atomic int stopping;
static _Atomic int ipc_fd = -1;
static _Atomic int mic_mute_state = -1;
static char client_id[32];
static char *client_secret;
static unsigned int nonce_counter;
static char token_dir[1024];
static char token_file[1200];
static char voice_channel_id[32];

static void rpc_cache_voice_users(struct json_object *reply);

static void
signal_change(void)
{
	uint64_t one = 1;
	if (event_fd >= 0)
		(void)write(event_fd, &one, sizeof one);
}

static int
curl_abort_if_stopping(void *unused, curl_off_t download_total,
                       curl_off_t download_now, curl_off_t upload_total,
                       curl_off_t upload_now)
{
	(void)unused;
	(void)download_total;
	(void)download_now;
	(void)upload_total;
	(void)upload_now;
	return atomic_load(&stopping);
}

static void
copy_string(char *dst, size_t size, const char *src)
{
	size_t length;
	if (!size)
		return;
	if (!src)
		src = "";
	length = strnlen(src, size - 1);
	memcpy(dst, src, length);
	dst[length] = '\0';
}

static int
valid_user_id(const char *s)
{
	const unsigned char *p;
	if (!s || !*s || strlen(s) >= sizeof speakers[0].id)
		return 0;
	for (p = (const unsigned char *)s; *p; p++)
		if (*p < '0' || *p > '9')
			return 0;
	return 1;
}

static void
set_voice_channel(const char *id)
{
	if (!valid_user_id(id))
		id = "";
	if (strcmp(voice_channel_id, id) == 0)
		return;
	copy_string(voice_channel_id, sizeof voice_channel_id, id);
	pthread_mutex_lock(&state_mutex);
	memset(speakers, 0, sizeof speakers);
	pending_count = 0;
	pthread_mutex_unlock(&state_mutex);
	signal_change();
}

static int
make_token_paths(void)
{
	const char *base = getenv("XDG_DATA_HOME");
	const char *home = getenv("HOME");
	if (base && *base)
		snprintf(token_dir, sizeof token_dir, "%s/andwm", base);
	else if (home && *home)
		snprintf(token_dir, sizeof token_dir,
		         "%s/.local/share/andwm", home);
	else
		return 0;
	if (mkdir(token_dir, 0700) < 0 && errno != EEXIST)
		return 0;
	if (chmod(token_dir, 0700) < 0)
		return 0;
	snprintf(token_file, sizeof token_file, "%s/discord-token.json", token_dir);
	return 1;
}

static char *
config_trim(char *text)
{
	char *end;
	while (*text == ' ' || *text == '\t' || *text == '\r')
		text++;
	end = text + strlen(text);
	while (end > text && (end[-1] == ' ' || end[-1] == '\t' ||
	                     end[-1] == '\r'))
		*--end = '\0';
	return text;
}

static int
load_client_config(void)
{
	const char *base = getenv("XDG_CONFIG_HOME");
	const char *home = getenv("HOME");
	char path[1200], contents[4097], configured_id[sizeof client_id];
	char secret[sizeof contents];
	struct stat st;
	int fd, have_id = 0, have_secret = 0, ok = 0;
	size_t total = 0;
	ssize_t n;
	memset(configured_id, 0, sizeof configured_id);
	memset(secret, 0, sizeof secret);
	if (base && *base)
		snprintf(path, sizeof path, "%s/andwm/discord-client-secret", base);
	else if (home && *home)
		snprintf(path, sizeof path,
		         "%s/.config/andwm/discord-client-secret", home);
	else {
		fprintf(stderr,
		        "AnDWM: Discord speaker indicator disabled; configure client_id and client_secret in ~/.config/andwm/discord-client-secret (mode 0600)\n");
		return 0;
	}
	fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
	if (fd < 0) {
		fprintf(stderr,
		        "AnDWM: Discord speaker indicator disabled; cannot open %s\n",
		        path);
		return 0;
	}
	if (fstat(fd, &st) < 0 || !S_ISREG(st.st_mode) || st.st_uid != getuid() ||
	    (st.st_mode & 07777) != 0600 || st.st_size <= 0 || st.st_size > 4096) {
		close(fd);
		fprintf(stderr,
		        "AnDWM: Discord config must be a regular, user-owned file with mode 0600\n");
		return 0;
	}
	while (total < (size_t)st.st_size) {
		n = read(fd, contents + total, (size_t)st.st_size - total);
		if (n < 0 && errno == EINTR)
			continue;
		if (n <= 0)
			goto done;
		total += (size_t)n;
	}
	close(fd);
	fd = -1;
	if (memchr(contents, '\0', total))
		goto done;
	contents[total] = '\0';
	{
		char *saveptr = NULL;
		char *line = strtok_r(contents, "\n", &saveptr);
		for (; line; line = strtok_r(NULL, "\n", &saveptr)) {
			char *entry = config_trim(line);
			char *equals, *key, *value;
			if (!*entry || *entry == '#')
				continue;
			equals = strchr(entry, '=');
			if (!equals)
				goto done;
			*equals = '\0';
			key = config_trim(entry);
			value = config_trim(equals + 1);
			if (!*value)
				goto done;
			if (!strcmp(key, "client_id")) {
				size_t length = strlen(value);
				if (have_id || length < 17 || length > 20 ||
				    length >= sizeof configured_id)
					goto done;
				for (size_t i = 0; i < length; i++)
					if (value[i] < '0' || value[i] > '9')
						goto done;
				memcpy(configured_id, value, length + 1);
				have_id = 1;
			} else if (!strcmp(key, "client_secret")) {
				size_t length = strlen(value);
				if (have_secret || length >= sizeof secret)
					goto done;
				memcpy(secret, value, length + 1);
				have_secret = 1;
			} else {
				goto done;
			}
		}
	}
	if (!have_id || !have_secret || !(client_secret = strdup(secret)))
		goto done;
	copy_string(client_id, sizeof client_id, configured_id);
	ok = 1;
done:
	if (fd >= 0)
		close(fd);
	memset(contents, 0, sizeof contents);
	memset(secret, 0, sizeof secret);
	if (!ok) {
		memset(configured_id, 0, sizeof configured_id);
		if (client_secret) {
			memset(client_secret, 0, strlen(client_secret));
			free(client_secret);
			client_secret = NULL;
		}
		client_id[0] = '\0';
		fprintf(stderr,
		        "AnDWM: Discord speaker indicator disabled; config must contain valid client_id and client_secret entries\n");
	}
	return ok;
}

static int
token_save(const Token *token)
{
	char tmp[1300];
	int fd;
	FILE *fp;
	struct json_object *obj = json_object_new_object();
	if (!obj)
		return 0;
	json_object_object_add(obj, "access_token",
	                       json_object_new_string(token->access));
	json_object_object_add(obj, "refresh_token",
	                       json_object_new_string(token->refresh));
	json_object_object_add(obj, "expires",
	                       json_object_new_int64((int64_t)token->expires));
	json_object_object_add(obj, "voice_write",
	                       json_object_new_boolean(token->voice_write));
	json_object_object_add(obj, "screenshare_read",
	                       json_object_new_boolean(token->screenshare_read));
	json_object_object_add(obj, "screenshare_write",
	                       json_object_new_boolean(token->screenshare_write));
	snprintf(tmp, sizeof tmp, "%s.tmp.%ld", token_file, (long)getpid());
	fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
	if (fd < 0) {
		json_object_put(obj);
		return 0;
	}
	(void)fchmod(fd, 0600);
	fp = fdopen(fd, "w");
	if (!fp) {
		close(fd);
		unlink(tmp);
		json_object_put(obj);
		return 0;
	}
	if (fprintf(fp, "%s\n", json_object_to_json_string(obj)) < 0 ||
	    fflush(fp) != 0 || fsync(fd) != 0) {
		fclose(fp);
		unlink(tmp);
		json_object_put(obj);
		return 0;
	}
	if (fclose(fp) != 0) {
		unlink(tmp);
		json_object_put(obj);
		return 0;
	}
	json_object_put(obj);
	if (rename(tmp, token_file) < 0) {
		unlink(tmp);
		return 0;
	}
	return 1;
}

static int
token_load(Token *token)
{
	char buf[DISCORD_TOKEN_MAX + 1];
	int fd;
	ssize_t n;
	struct stat st;
	struct json_object *obj, *value;
	if (!make_token_paths())
		return 0;
	fd = open(token_file, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
	if (fd < 0)
		return 0;
	if (fstat(fd, &st) < 0 || !S_ISREG(st.st_mode) || st.st_uid != getuid() ||
	    (st.st_mode & 077) != 0) {
		close(fd);
		fprintf(stderr,
		        "AnDWM: Discord token file must be a regular, user-owned file with mode 0600\n");
		return 0;
	}
	n = read(fd, buf, sizeof buf - 1);
	close(fd);
	if (n <= 0 || n >= (ssize_t)sizeof buf - 1)
		return 0;
	buf[n] = '\0';
	obj = json_tokener_parse(buf);
	if (!obj)
		return 0;
	memset(token, 0, sizeof *token);
	if (json_object_object_get_ex(obj, "access_token", &value))
		copy_string(token->access, sizeof token->access,
		            json_object_get_string(value));
	if (json_object_object_get_ex(obj, "refresh_token", &value))
		copy_string(token->refresh, sizeof token->refresh,
		            json_object_get_string(value));
	if (json_object_object_get_ex(obj, "expires", &value))
		token->expires = (time_t)json_object_get_int64(value);
	if (json_object_object_get_ex(obj, "voice_write", &value))
		token->voice_write = json_object_get_boolean(value);
	if (json_object_object_get_ex(obj, "screenshare_read", &value))
		token->screenshare_read = json_object_get_boolean(value);
	if (json_object_object_get_ex(obj, "screenshare_write", &value))
		token->screenshare_write = json_object_get_boolean(value);
	json_object_put(obj);
	return token->access[0] != '\0' && token->refresh[0] != '\0';
}

typedef struct {
	char *data;
	size_t length;
	size_t capacity;
} CurlBuffer;

static size_t
curl_buffer_write(char *data, size_t size, size_t count, void *userdata)
{
	CurlBuffer *buf = userdata;
	size_t n = size * count;
	char *next;
	if (n > 1024 * 1024 || buf->length + n > 1024 * 1024)
		return 0;
	if (buf->length + n + 1 > buf->capacity) {
		size_t cap = buf->capacity ? buf->capacity * 2 : 4096;
		while (cap < buf->length + n + 1)
			cap *= 2;
		next = realloc(buf->data, cap);
		if (!next)
			return 0;
		buf->data = next;
		buf->capacity = cap;
	}
	memcpy(buf->data + buf->length, data, n);
	buf->length += n;
	buf->data[buf->length] = '\0';
	return n;
}

static int
oauth_post(const char *body, struct json_object **response)
{
	CURL *curl;
	CURLcode result;
	long status = 0;
	struct curl_slist *headers = NULL;
	CurlBuffer buf = {0};
	int ok = 0;
	if (!body || !response || !(curl = curl_easy_init()))
		return 0;
	headers = curl_slist_append(headers,
	                            "Content-Type: application/x-www-form-urlencoded");
	curl_easy_setopt(curl, CURLOPT_URL, "https://discord.com/api/oauth2/token");
	curl_easy_setopt(curl, CURLOPT_POST, 1L);
	curl_easy_setopt(curl, CURLOPT_POSTFIELDS, body);
	curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
	curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, curl_buffer_write);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, &buf);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 10L);
	curl_easy_setopt(curl, CURLOPT_TIMEOUT, 20L);
	curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(curl, CURLOPT_NOPROGRESS, 0L);
	curl_easy_setopt(curl, CURLOPT_XFERINFOFUNCTION, curl_abort_if_stopping);
	curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 0L);
	result = curl_easy_perform(curl);
	curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &status);
	if (result == CURLE_OK && status >= 200 && status < 300 && buf.data) {
		*response = json_tokener_parse(buf.data);
		ok = *response != NULL;
	}
	curl_slist_free_all(headers);
	curl_easy_cleanup(curl);
	free(buf.data);
	return ok;
}

static int
token_from_response(struct json_object *obj, Token *token)
{
	struct json_object *value;
	int64_t expires_in = 0;
	const char *s, *scope;
	if (!obj || !token)
		return 0;
	if (!json_object_object_get_ex(obj, "access_token", &value) ||
	    !(s = json_object_get_string(value)) || !*s)
		return 0;
	copy_string(token->access, sizeof token->access, s);
	if (json_object_object_get_ex(obj, "refresh_token", &value)) {
		s = json_object_get_string(value);
		if (s && *s)
			copy_string(token->refresh, sizeof token->refresh, s);
	}
	if (json_object_object_get_ex(obj, "expires_in", &value))
		expires_in = json_object_get_int64(value);
	if (json_object_object_get_ex(obj, "scope", &value) &&
	    (scope = json_object_get_string(value))) {
		const char *p = scope;
		token->voice_write = 0;
		token->screenshare_read = 0;
		token->screenshare_write = 0;
		while (*p) {
			const char *start;
			size_t length;
			while (*p == ' ' || *p == '\t')
				p++;
			start = p;
			while (*p && *p != ' ' && *p != '\t')
			p++;
			length = (size_t)(p - start);
			if (length == sizeof("rpc.voice.write") - 1 &&
			    !memcmp(start, "rpc.voice.write", length)) {
				token->voice_write = 1;
			}
			if (length == sizeof("rpc.screenshare.read") - 1 &&
			    !memcmp(start, "rpc.screenshare.read", length))
				token->screenshare_read = 1;
			if (length == sizeof("rpc.screenshare.write") - 1 &&
			    !memcmp(start, "rpc.screenshare.write", length))
				token->screenshare_write = 1;
		}
	}
	if (expires_in < 60)
		expires_in = 3600;
	token->expires = time(NULL) + (time_t)expires_in;
	return token->refresh[0] != '\0';
}

static int
token_has_required_scopes(const Token *token)
{
	return token->voice_write && token->screenshare_read &&
	       token->screenshare_write;
}

static int
token_exchange_code(const char *code, Token *token)
{
	CURL *curl = curl_easy_init();
	char *e_code, *e_secret, *e_redirect;
	char *body;
	size_t len;
	struct json_object *response = NULL;
	int ok;
	if (!curl || !client_secret || !*client_secret)
		return 0;
	e_code = curl_easy_escape(curl, code, 0);
	e_secret = curl_easy_escape(curl, client_secret, 0);
	e_redirect = curl_easy_escape(curl,
	    "http://127.0.0.1/discord-rpc/callback", 0);
	if (!e_code || !e_secret || !e_redirect) {
		curl_free(e_code);
		curl_free(e_secret);
		curl_free(e_redirect);
		curl_easy_cleanup(curl);
		return 0;
	}
	len = strlen(e_code) + strlen(e_secret) + strlen(e_redirect) + 256;
	body = malloc(len);
	if (!body) {
		curl_free(e_code);
		curl_free(e_secret);
		curl_free(e_redirect);
		curl_easy_cleanup(curl);
		return 0;
	}
	snprintf(body, len,
	         "client_id=%s&client_secret=%s&grant_type=authorization_code&"
	         "code=%s&redirect_uri=%s",
	         client_id, e_secret, e_code, e_redirect);
	curl_free(e_code);
	curl_free(e_secret);
	curl_free(e_redirect);
	curl_easy_cleanup(curl);
	ok = oauth_post(body, &response) && token_from_response(response, token);
	free(body);
	if (response)
		json_object_put(response);
	if (ok)
		(void)token_save(token);
	return ok;
}

static int
token_refresh(Token *token)
{
	CURL *curl;
	char *e_refresh, *e_secret, *body;
	size_t len;
	struct json_object *response = NULL;
	int ok;
	if (!token->refresh[0] || !client_secret || !*client_secret ||
	    !(curl = curl_easy_init()))
		return 0;
	e_refresh = curl_easy_escape(curl, token->refresh, 0);
	e_secret = curl_easy_escape(curl, client_secret, 0);
	if (!e_refresh || !e_secret) {
		curl_free(e_refresh);
		curl_free(e_secret);
		curl_easy_cleanup(curl);
		return 0;
	}
	len = strlen(e_refresh) + strlen(e_secret) + 192;
	body = malloc(len);
	if (!body) {
		curl_free(e_refresh);
		curl_free(e_secret);
		curl_easy_cleanup(curl);
		return 0;
	}
	snprintf(body, len,
	         "client_id=%s&client_secret=%s&grant_type=refresh_token&"
	         "refresh_token=%s",
	         client_id, e_secret, e_refresh);
	curl_free(e_refresh);
	curl_free(e_secret);
	curl_easy_cleanup(curl);
	ok = oauth_post(body, &response) && token_from_response(response, token);
	free(body);
	if (response)
		json_object_put(response);
	if (ok)
		(void)token_save(token);
	return ok;
}

static int
wait_fd(int fd, short events, int timeout_ms)
{
	struct pollfd pfd = { .fd = fd, .events = events };
	int result;
	do {
		result = poll(&pfd, 1, timeout_ms);
	} while (result < 0 && errno == EINTR && !atomic_load(&stopping));
	return result > 0 &&
	       (pfd.revents & (events | POLLHUP | POLLERR | POLLNVAL)) != 0;
}

static int
read_exact(int fd, void *buffer, size_t size)
{
	char *p = buffer;
	size_t done = 0;
	while (done < size && !atomic_load(&stopping)) {
		ssize_t n;
		if (!wait_fd(fd, POLLIN, 1000))
			continue;
		n = recv(fd, p + done, size - done, 0);
		if (n > 0)
			done += (size_t)n;
		else if (n < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK))
			continue;
		else
			return 0;
	}
	return done == size;
}

static int
write_exact(int fd, const void *buffer, size_t size)
{
	const char *p = buffer;
	size_t done = 0;
	while (done < size && !atomic_load(&stopping)) {
		ssize_t n = send(fd, p + done, size - done, MSG_NOSIGNAL);
		if (n > 0)
			done += (size_t)n;
		else if (n < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)) {
			if (!wait_fd(fd, POLLOUT, 1000))
				continue;
		} else
			return 0;
	}
	return done == size;
}

static int
rpc_send_json(struct json_object *obj)
{
	const char *text = json_object_to_json_string_ext(obj, JSON_C_TO_STRING_PLAIN);
	uint32_t header[2];
	size_t len = strlen(text);
	if (len > DISCORD_IPC_MAX)
		return 0;
	header[0] = 1;
	header[1] = (uint32_t)len;
	return write_exact(ipc_fd, header, sizeof header) &&
	       write_exact(ipc_fd, text, len);
}

static int
rpc_receive(struct json_object **obj, int timeout_ms)
{
	uint32_t header[2];
	char *payload = NULL;
	if (!wait_fd(ipc_fd, POLLIN, timeout_ms))
		return 0;
	if (!read_exact(ipc_fd, header, sizeof header) ||
	    header[1] > DISCORD_IPC_MAX || (header[1] == 0 && header[0] != 3))
		return -1;
	if (header[0] == 3) { /* Discord IPC ping */
		uint32_t pong[2] = {4, header[1]};
		if (header[1]) {
			payload = malloc(header[1]);
			if (!payload)
				return -1;
			if (!read_exact(ipc_fd, payload, header[1])) {
				free(payload);
				return -1;
			}
		}
		(void)write_exact(ipc_fd, pong, sizeof pong);
		if (header[1]) {
			(void)write_exact(ipc_fd, payload, header[1]);
			free(payload);
		}
		return 0;
	}
	payload = malloc((size_t)header[1] + 1);
	if (!payload)
		return -1;
	if (!read_exact(ipc_fd, payload, header[1])) {
		free(payload);
		return -1;
	}
	payload[header[1]] = '\0';
	if (header[0] != 1) {
		free(payload);
		return 0;
	}
	*obj = json_tokener_parse(payload);
	free(payload);
	return *obj ? 1 : -1;
}

static Speaker *
speaker_for_id_locked(const char *id, int create)
{
	Speaker *empty = NULL;
	size_t i;
	for (i = 0; i < DWM_DISCORD_SPEAKERS; i++) {
		if (strcmp(speakers[i].id, id) == 0)
			return &speakers[i];
		if (!speakers[i].id[0] && !empty)
			empty = &speakers[i];
	}
	if (!create)
		return NULL;
	if (!empty) {
		for (i = 0; i < DWM_DISCORD_SPEAKERS; i++)
			if (!speakers[i].speaking) {
				empty = &speakers[i];
				break;
			}
	}
	if (empty) {
		memset(empty, 0, sizeof *empty);
		copy_string(empty->id, sizeof empty->id, id);
	}
	return empty;
}

static void
rpc_event(struct json_object *obj)
{
	struct json_object *value, *data;
	const char *evt, *id = NULL;
	int changed = 0;
	if (!json_object_object_get_ex(obj, "evt", &value) ||
	    !(evt = json_object_get_string(value)) ||
	    !json_object_object_get_ex(obj, "data", &data))
		return;
	if (!strcmp(evt, "VOICE_CHANNEL_SELECT")) {
		if (json_object_object_get_ex(data, "channel_id", &value))
			id = json_object_get_string(value);
		set_voice_channel(id);
		return;
	} else if (!strcmp(evt, "SPEAKING_START")) {
		if (json_object_object_get_ex(data, "user_id", &value))
			id = json_object_get_string(value);
		if (!valid_user_id(id))
			return;
		pthread_mutex_lock(&state_mutex);
		Speaker *speaker = speaker_for_id_locked(id, 1);
		if (speaker && !speaker->speaking) {
			speaker->speaking = 1;
			changed = 1;
			if ((!speaker->username[0] || !speaker->avatar_path[0]) &&
			    pending_count < DISCORD_USERS_PENDING) {
				copy_string(pending_users[pending_count],
				            sizeof pending_users[pending_count], id);
				pending_count++;
			}
		}
		pthread_mutex_unlock(&state_mutex);
	} else if (!strcmp(evt, "SPEAKING_STOP")) {
		if (json_object_object_get_ex(data, "user_id", &value))
			id = json_object_get_string(value);
		if (!valid_user_id(id))
			return;
		pthread_mutex_lock(&state_mutex);
		Speaker *speaker = speaker_for_id_locked(id, 0);
		if (speaker && speaker->speaking) {
			speaker->speaking = 0;
			changed = 1;
		}
		pthread_mutex_unlock(&state_mutex);
	}
	if (changed)
		signal_change();
}

static int
rpc_connect_socket(void)
{
	const char *runtime = getenv("XDG_RUNTIME_DIR");
	const char *config = getenv("XDG_CONFIG_HOME");
	const char *home = getenv("HOME");
	const char *override = getenv("DISCORD_IPC_PATH");
	char paths[8][sizeof(((struct sockaddr_un *)0)->sun_path)];
	int npaths = 0, i;
	if (override && *override)
		copy_string(paths[npaths++], sizeof paths[0], override);
	if (runtime && *runtime) {
		snprintf(paths[npaths++], sizeof paths[0], "%s/discord-ipc-0", runtime);
		snprintf(paths[npaths++], sizeof paths[0],
		         "%s/app/com.discordapp.Discord/discord-ipc-0", runtime);
	}
	if (config && *config)
		snprintf(paths[npaths++], sizeof paths[0], "%s/discord/discord-ipc-0", config);
	if (home && *home)
		snprintf(paths[npaths++], sizeof paths[0], "%s/.config/discord/discord-ipc-0", home);
	if (runtime && *runtime)
		snprintf(paths[npaths++], sizeof paths[0],
		         "%s/app/com.discordapp.DiscordCanary/discord-ipc-0", runtime);
	for (i = 0; i < npaths; i++) {
		struct sockaddr_un addr = {0};
		int fd;
		if (!paths[i][0])
			continue;
		fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
		if (fd < 0)
			continue;
		addr.sun_family = AF_UNIX;
		copy_string(addr.sun_path, sizeof addr.sun_path, paths[i]);
		if (connect(fd, (struct sockaddr *)&addr, sizeof addr) == 0)
			return fd;
		close(fd);
	}
	return -1;
}

static int
rpc_handshake(void)
{
	struct json_object *obj = json_object_new_object();
	struct json_object *reply = NULL, *value;
	const char *text;
	uint32_t header[2];
	if (!obj)
		return 0;
	json_object_object_add(obj, "v", json_object_new_int(1));
	json_object_object_add(obj, "client_id",
	                       json_object_new_string(client_id));
	text = json_object_to_json_string_ext(obj, JSON_C_TO_STRING_PLAIN);
	header[0] = 0;
	header[1] = (uint32_t)strlen(text);
	if (!write_exact(ipc_fd, header, sizeof header) ||
	    !write_exact(ipc_fd, text, header[1])) {
		json_object_put(obj);
		return 0;
	}
	json_object_put(obj);
	if (rpc_receive(&reply, 10000) != 1)
		return 0;
	if (json_object_object_get_ex(reply, "evt", &value)) {
		text = json_object_get_string(value);
		if (text && !strcmp(text, "READY")) {
			json_object_put(reply);
			return 1;
		}
	}
	json_object_put(reply);
	return 0;
}

static void
rpc_handle_message(struct json_object *obj)
{
	struct json_object *value;
	if (json_object_object_get_ex(obj, "evt", &value)) {
		rpc_event(obj);
		return;
	}
	/* RPC replies are consumed by rpc_call; do not interpret them as events. */
	(void)json_object_object_get_ex(obj, "cmd", &value);
}

static struct json_object *
rpc_call(const char *command, struct json_object *args, const char *event,
         int timeout_ms)
{
	struct json_object *request, *reply, *value, *nonce_value, *data = NULL;
	char nonce[32];
	int elapsed = 0;
	if (ipc_fd < 0)
		return NULL;
	request = json_object_new_object();
	if (!request)
		return NULL;
	snprintf(nonce, sizeof nonce, "andwm-%u", ++nonce_counter);
	json_object_object_add(request, "cmd", json_object_new_string(command));
	json_object_object_add(request, "nonce", json_object_new_string(nonce));
	if (args)
		json_object_object_add(request, "args", json_object_get(args));
	if (event)
		json_object_object_add(request, "evt", json_object_new_string(event));
	if (!rpc_send_json(request)) {
		json_object_put(request);
		return NULL;
	}
	json_object_put(request);
	while (elapsed < timeout_ms && !atomic_load(&stopping)) {
		int result = rpc_receive(&reply, 1000);
		elapsed += 1000;
		if (result < 0)
			return NULL;
		if (!result)
			continue;
		if (json_object_object_get_ex(reply, "nonce", &nonce_value) &&
		    (value = nonce_value) && json_object_get_string(value) &&
		    !strcmp(json_object_get_string(value), nonce)) {
			struct json_object *tmp;
			struct json_object *evt_value;
			if (json_object_object_get_ex(reply, "evt", &evt_value) &&
			    json_object_get_string(evt_value) &&
			    !strcmp(json_object_get_string(evt_value), "ERROR")) {
				json_object_put(reply);
				return NULL;
			}
			if (json_object_object_get_ex(reply, "data", &tmp))
				data = json_object_get(tmp);
			json_object_put(reply);
			return data;
		}
		rpc_handle_message(reply);
		json_object_put(reply);
	}
	return NULL;
}

static int
rpc_authorize(Token *token)
{
	struct json_object *args = json_object_new_object();
	struct json_object *scopes = json_object_new_array();
	struct json_object *reply;
	struct json_object *value;
	const char *code;
	int ok = 0;
	if (!args || !scopes)
		goto done;
	json_object_array_add(scopes, json_object_new_string("rpc"));
	json_object_array_add(scopes, json_object_new_string("rpc.voice.read"));
	json_object_array_add(scopes, json_object_new_string("rpc.voice.write"));
	json_object_array_add(scopes, json_object_new_string("rpc.screenshare.read"));
	json_object_array_add(scopes, json_object_new_string("rpc.screenshare.write"));
	json_object_object_add(args, "client_id",
	                       json_object_new_string(client_id));
	json_object_object_add(args, "scopes", scopes);
	scopes = NULL;
	reply = rpc_call("AUTHORIZE", args, NULL, 120000);
	if (!reply)
		goto done;
	if (json_object_object_get_ex(reply, "code", &value) &&
	    (code = json_object_get_string(value)) && *code)
		ok = token_exchange_code(code, token);
	json_object_put(reply);
done:
	if (scopes)
		json_object_put(scopes);
	if (args)
		json_object_put(args);
	return ok;
}

static int
rpc_authenticate(Token *token)
{
	struct json_object *args = json_object_new_object();
	struct json_object *reply;
	int ok;
	if (!args)
		return 0;
	json_object_object_add(args, "access_token",
	                       json_object_new_string(token->access));
	reply = rpc_call("AUTHENTICATE", args, NULL, 30000);
	json_object_put(args);
	ok = reply != NULL;
	if (reply)
		json_object_put(reply);
	return ok;
}

static int
rpc_subscribe(const char *command, const char *event,
              const char *channel_id)
{
	struct json_object *args = json_object_new_object();
	struct json_object *reply;
	int ok;
	if (!args)
		return 0;
	if (channel_id && *channel_id)
		json_object_object_add(args, "channel_id",
		                       json_object_new_string(channel_id));
	reply = rpc_call(command, args, event, 15000);
	json_object_put(args);
	ok = reply != NULL;
	if (reply)
		json_object_put(reply);
	return ok;
}

static void
rpc_update_voice_channel(void)
{
	struct json_object *reply, *value;
	const char *id = NULL;
	reply = rpc_call("GET_SELECTED_VOICE_CHANNEL", NULL, NULL, 15000);
	if (reply && json_object_is_type(reply, json_type_object) &&
	    json_object_object_get_ex(reply, "id", &value))
		id = json_object_get_string(value);
	set_voice_channel(id);
	if (reply)
		rpc_cache_voice_users(reply);
	if (reply)
		json_object_put(reply);
}

static int
rpc_sync_speaking_subscriptions(char subscribed_channel[32])
{
	char current_channel[32];
	copy_string(current_channel, sizeof current_channel, voice_channel_id);
	if (!strcmp(current_channel, subscribed_channel))
		return 1;
	if (subscribed_channel[0]) {
		if (!rpc_subscribe("UNSUBSCRIBE", "SPEAKING_START",
		                   subscribed_channel) ||
		    !rpc_subscribe("UNSUBSCRIBE", "SPEAKING_STOP",
		                   subscribed_channel))
			return 0;
		subscribed_channel[0] = '\0';
	}
	if (!current_channel[0])
		return 1;
	if (!rpc_subscribe("SUBSCRIBE", "SPEAKING_START", current_channel) ||
	    !rpc_subscribe("SUBSCRIBE", "SPEAKING_STOP", current_channel))
		return 0;
	copy_string(subscribed_channel, 32, current_channel);
	return 1;
}

static int
rpc_set_voice_mute(int muted)
{
	struct json_object *args = json_object_new_object();
	struct json_object *reply;
	if (!args)
		return 0;
	json_object_object_add(args, "mute", json_object_new_boolean(muted));
	reply = rpc_call("SET_VOICE_SETTINGS", args, NULL, 5000);
	json_object_put(args);
	if (!reply)
		return 0;
	json_object_put(reply);
	return 1;
}

/* Read PipeWire-Pulse's current default source, rather than the sound-bar
 * capture stream (which may be connected to a different input). */
static int
mic_read_default_source_mute(void)
{
	int fds[2];
	char output[128] = "";
	size_t used = 0;
	pid_t child;
	if (pipe(fds) < 0)
		return -1;
	(void)fcntl(fds[0], F_SETFD, FD_CLOEXEC);
	(void)fcntl(fds[1], F_SETFD, FD_CLOEXEC);
	child = fork();
	if (child < 0) {
		close(fds[0]);
		close(fds[1]);
		return -1;
	}
	if (child == 0) {
		int devnull;
		close(fds[0]);
		if (dup2(fds[1], STDOUT_FILENO) < 0)
			_exit(127);
		close(fds[1]);
		devnull = open("/dev/null", O_WRONLY);
		if (devnull >= 0) {
			(void)dup2(devnull, STDERR_FILENO);
			close(devnull);
		}
		execl("/usr/bin/pactl", "pactl", "get-source-mute",
		      "@DEFAULT_SOURCE@", (char *)NULL);
		_exit(127);
	}
	close(fds[1]);
	while (used + 1 < sizeof output) {
		struct pollfd pfd = { .fd = fds[0], .events = POLLIN };
		int ready;
		do {
			ready = poll(&pfd, 1, 1500);
		} while (ready < 0 && errno == EINTR);
		if (ready <= 0) {
			(void)kill(child, SIGTERM);
			break;
		}
		ssize_t n = read(fds[0], output + used, sizeof output - used - 1);
		if (n > 0)
			used += (size_t)n;
		else if (n == 0)
			break;
		else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK)
			break;
	}
	close(fds[0]);
	output[used] = '\0';
	if (strstr(output, "Mute: yes"))
		return 1;
	if (strstr(output, "Mute: no"))
		return 0;
	return -1;
}

static void *
mic_status_worker(void *unused)
{
	(void)unused;
	while (!atomic_load(&stopping)) {
		int muted = mic_read_default_source_mute();
		if (muted >= 0)
			atomic_store(&mic_mute_state, muted);
		for (int i = 0; i < 5 && !atomic_load(&stopping); i++) {
			struct timespec ts = { .tv_sec = 0, .tv_nsec = 200000000 };
			nanosleep(&ts, NULL);
		}
	}
	return NULL;
}

static int
rpc_sync_mic_mute(int *last_sent)
{
	int muted = atomic_load(&mic_mute_state);
	if (muted < 0 || muted == *last_sent)
		return 1;
	if (!rpc_set_voice_mute(muted))
		fprintf(stderr, "AnDWM: Discord microphone mute update failed\n");
	*last_sent = muted;
	return 1;
}

static int
fetch_to_file(const char *url, const char *path)
{
	CURL *curl;
	CURLcode result;
	char tmp[1300];
	int fd, ok;
	FILE *fp;
	snprintf(tmp, sizeof tmp, "%s.tmp.%ld", path, (long)getpid());
	fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
	if (fd < 0)
		return 0;
	fp = fdopen(fd, "wb");
	if (!fp) {
		close(fd);
		unlink(tmp);
		return 0;
	}
	curl = curl_easy_init();
	if (!curl) {
		fclose(fp);
		unlink(tmp);
		return 0;
	}
	curl_easy_setopt(curl, CURLOPT_URL, url);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, fp);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 10L);
	curl_easy_setopt(curl, CURLOPT_TIMEOUT, 20L);
	curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(curl, CURLOPT_NOPROGRESS, 0L);
	curl_easy_setopt(curl, CURLOPT_XFERINFOFUNCTION, curl_abort_if_stopping);
	curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
	curl_easy_setopt(curl, CURLOPT_FAILONERROR, 1L);
	curl_easy_setopt(curl, CURLOPT_USERAGENT, "AnDWM/1.0");
	result = curl_easy_perform(curl);
	if (result != CURLE_OK)
		fprintf(stderr, "AnDWM: download failed for %s: %s (%ld)\n", url,
		        curl_easy_strerror(result), (long)result);
	ok = result == CURLE_OK && fflush(fp) == 0 && fsync(fd) == 0;
	curl_easy_cleanup(curl);
	if (fclose(fp) != 0)
		ok = 0;
	if (ok && rename(tmp, path) == 0)
		return 1;
	unlink(tmp);
	return 0;
}

static int
download_avatar(const char *user_id, const char *hash, char *path,
                size_t path_size)
{
	char url[1024];
	const char *extension;
	size_t offset, id_len, hash_len, extension_len;
	int animated;
	if (!valid_user_id(user_id) || !hash || !*hash || !make_token_paths())
		return 0;
	for (const char *p = hash; *p; p++)
		if (!((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') ||
		      (*p >= '0' && *p <= '9') || *p == '_'))
			return 0;
	animated = hash[0] == 'a' && hash[1] == '_';
	extension = animated ? "gif" : "png";
	id_len = strlen(user_id);
	hash_len = strlen(hash);
	extension_len = strlen(extension);
	if (strlen(token_dir) + 1 + 7 + id_len + 1 + hash_len + 1 +
	    extension_len + 1 > path_size)
		return 0;
	offset = strlen(token_dir);
	memcpy(path, token_dir, offset);
	path[offset++] = '/';
	memcpy(path + offset, "avatar-", 7);
	offset += 7;
	memcpy(path + offset, user_id, id_len);
	offset += id_len;
	path[offset++] = '-';
	memcpy(path + offset, hash, hash_len);
	offset += hash_len;
	path[offset++] = '.';
	memcpy(path + offset, extension, extension_len);
	offset += extension_len;
	path[offset] = '\0';
	if (access(path, R_OK) == 0)
		return 1;
	snprintf(url, sizeof url,
	         "https://cdn.discordapp.com/avatars/%s/%s.%s?size=128&animated=false",
	         user_id, hash, extension);
	return fetch_to_file(url, path);
}

static int
download_default_avatar(const char *user_id, char *path, size_t path_size)
{
	char url[256];
	unsigned long long numeric_id;
	unsigned int index;
	int length;
	if (!valid_user_id(user_id) || !make_token_paths())
		return 0;
	numeric_id = strtoull(user_id, NULL, 10);
	index = (unsigned int)((numeric_id >> 22) % 6);
	length = snprintf(path, path_size, "%s/avatar-%s-default-%u.png",
	                  token_dir, user_id, index);
	if (length <= 0 || (size_t)length >= path_size)
		return 0;
	if (access(path, R_OK) == 0)
		return 1;
	snprintf(url, sizeof url,
	         "https://cdn.discordapp.com/embed/avatars/%u.png", index);
	return fetch_to_file(url, path);
}

static void
rpc_cache_voice_users(struct json_object *reply)
{
	struct json_object *states, *state, *user, *value;
	size_t i, count;
	if (!reply ||
	    !json_object_object_get_ex(reply, "voice_states", &states) ||
	    !json_object_is_type(states, json_type_array))
		return;
	count = json_object_array_length(states);
	for (i = 0; i < count; i++) {
		const char *id = NULL, *name = NULL, *avatar = NULL;
		char avatar_path[512] = "";
		state = json_object_array_get_idx(states, i);
		if (!json_object_is_type(state, json_type_object) ||
		    !json_object_object_get_ex(state, "user", &user) ||
		    !json_object_is_type(user, json_type_object))
			continue;
		if (json_object_object_get_ex(user, "id", &value))
			id = json_object_get_string(value);
		if (!valid_user_id(id))
			continue;
		if (json_object_object_get_ex(user, "username", &value))
			name = json_object_get_string(value);
		if (json_object_object_get_ex(user, "avatar", &value))
			avatar = json_object_get_string(value);
		if (avatar && *avatar)
			(void)download_avatar(id, avatar, avatar_path,
			                      sizeof avatar_path);
		else
			(void)download_default_avatar(id, avatar_path,
			                              sizeof avatar_path);
		pthread_mutex_lock(&state_mutex);
		Speaker *speaker = speaker_for_id_locked(id, 1);
		if (speaker) {
			if (name)
				copy_string(speaker->username,
				            sizeof speaker->username, name);
			if (avatar_path[0])
				copy_string(speaker->avatar_path,
				            sizeof speaker->avatar_path, avatar_path);
		}
		pthread_mutex_unlock(&state_mutex);
	}
}

static void
rpc_process_user(const char *id)
{
	struct json_object *args = json_object_new_object();
	struct json_object *reply, *user = NULL, *value;
	const char *name = NULL, *avatar = NULL;
	char avatar_path[512] = "";
	if (!args)
		return;
	json_object_object_add(args, "id", json_object_new_string(id));
	reply = rpc_call("GET_USER", args, NULL, 15000);
	json_object_put(args);
	if (!reply)
		return;
	if (json_object_object_get_ex(reply, "user", &user) &&
	    json_object_is_type(user, json_type_object)) {
		if (json_object_object_get_ex(user, "username", &value))
			name = json_object_get_string(value);
		if (json_object_object_get_ex(user, "avatar", &value))
			avatar = json_object_get_string(value);
	} else {
		user = reply;
		if (json_object_object_get_ex(user, "username", &value))
			name = json_object_get_string(value);
		if (json_object_object_get_ex(user, "avatar", &value))
			avatar = json_object_get_string(value);
	}
	if (avatar && *avatar)
		(void)download_avatar(id, avatar, avatar_path, sizeof avatar_path);
	else
		(void)download_default_avatar(id, avatar_path, sizeof avatar_path);
	pthread_mutex_lock(&state_mutex);
	Speaker *speaker = speaker_for_id_locked(id, 0);
	if (speaker) {
		if (name)
			copy_string(speaker->username, sizeof speaker->username, name);
		if (avatar_path[0])
			copy_string(speaker->avatar_path, sizeof speaker->avatar_path,
			            avatar_path);
	}
	pthread_mutex_unlock(&state_mutex);
	if (name || avatar_path[0])
		signal_change();
	json_object_put(reply);
}

static void
rpc_process_pending_users(void)
{
	char ids[DISCORD_USERS_PENDING][32];
	size_t n, i;
	pthread_mutex_lock(&state_mutex);
	n = pending_count;
	memcpy(ids, pending_users, n * sizeof ids[0]);
	pending_count = 0;
	pthread_mutex_unlock(&state_mutex);
	for (i = 0; i < n && !atomic_load(&stopping); i++)
		rpc_process_user(ids[i]);
}

static void
rpc_clear_speakers(void)
{
	pthread_mutex_lock(&state_mutex);
	memset(speakers, 0, sizeof speakers);
	pending_count = 0;
	pthread_mutex_unlock(&state_mutex);
	signal_change();
}

static int
rpc_session(void)
{
	Token token = {0};
	struct json_object *message = NULL;
	char subscribed_channel[32] = "";
	int result, ok = 0, last_mute_sent = -1;
	ipc_fd = rpc_connect_socket();
	if (ipc_fd < 0 || !rpc_handshake())
		goto done;
	if (!token_load(&token)) {
		if (!client_id[0] || !client_secret || !*client_secret) {
			goto done;
		}
		if (!rpc_authorize(&token))
			goto done;
	} else if (!token_has_required_scopes(&token) ||
	           (token.expires <= time(NULL) + 30 &&
	            (!token_refresh(&token) ||
	             !token_has_required_scopes(&token)))) {
		memset(&token, 0, sizeof token);
		if (!client_id[0] || !client_secret || !*client_secret ||
		    !rpc_authorize(&token))
			goto done;
	}
	if (!rpc_authenticate(&token) ||
	    !rpc_subscribe("SUBSCRIBE", "VOICE_CHANNEL_SELECT", NULL))
		goto done;
	if (!token_has_required_scopes(&token)) {
		fprintf(stderr,
		        "AnDWM: Discord authorization did not grant the required voice/screenshare scopes\n");
		goto done;
	}
	rpc_update_voice_channel();
	if (!rpc_sync_speaking_subscriptions(subscribed_channel))
		goto done;
	ok = 1;
	while (!atomic_load(&stopping)) {
		result = rpc_receive(&message, 1000);
		if (result < 0)
			break;
		if (result > 0) {
			rpc_handle_message(message);
			json_object_put(message);
			message = NULL;
			rpc_process_pending_users();
		}
		(void)rpc_sync_mic_mute(&last_mute_sent);
		if (!rpc_sync_speaking_subscriptions(subscribed_channel))
			break;
	}
done:
	if (message)
		json_object_put(message);
	if (ipc_fd >= 0) {
		close(ipc_fd);
		ipc_fd = -1;
	}
	voice_channel_id[0] = '\0';
	memset(&token, 0, sizeof token);
	return ok;
}

static void *
discord_worker(void *unused)
{
	int delay = 1;
	(void)unused;
	while (!atomic_load(&stopping)) {
		(void)rpc_session();
		rpc_clear_speakers();
		for (int i = 0; i < delay && !atomic_load(&stopping); i++) {
			struct timespec ts = { .tv_sec = 1, .tv_nsec = 0 };
			nanosleep(&ts, NULL);
		}
		if (delay < 16)
			delay *= 2;
	}
	return NULL;
}

int
discord_start(void)
{
	if (started)
		return event_fd;
	if (!load_client_config())
		return -1;
	curl_global_init(CURL_GLOBAL_DEFAULT);
	event_fd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
	if (event_fd < 0) {
		free(client_secret);
		client_secret = NULL;
		client_id[0] = '\0';
		curl_global_cleanup();
		return -1;
	}
	atomic_store(&stopping, 0);
	atomic_store(&mic_mute_state, -1);
	if (pthread_create(&mic_worker, NULL, mic_status_worker, NULL) == 0)
		mic_worker_started = 1;
	else
		fprintf(stderr,
		        "AnDWM: cannot start PipeWire microphone status monitor\n");
	if (pthread_create(&worker, NULL, discord_worker, NULL) != 0) {
		atomic_store(&stopping, 1);
		if (mic_worker_started) {
			pthread_join(mic_worker, NULL);
			mic_worker_started = 0;
		}
		close(event_fd);
		event_fd = -1;
		free(client_secret);
		client_secret = NULL;
		client_id[0] = '\0';
		curl_global_cleanup();
		return -1;
	}
	started = 1;
	return event_fd;
}

int
discord_event_fd(void)
{
	return event_fd;
}

size_t
discord_speakers(DwmDiscordSpeaker *out, size_t capacity)
{
	size_t i, count = 0;
	if (!out || !capacity)
		return 0;
	pthread_mutex_lock(&state_mutex);
	for (i = 0; i < DWM_DISCORD_SPEAKERS && count < capacity; i++) {
		if (!speakers[i].speaking)
			continue;
		copy_string(out[count].user_id, sizeof out[count].user_id,
		            speakers[i].id);
		copy_string(out[count].username, sizeof out[count].username,
		            speakers[i].username);
		copy_string(out[count].avatar_path, sizeof out[count].avatar_path,
		            speakers[i].avatar_path);
		out[count].speaking = 1;
		count++;
	}
	pthread_mutex_unlock(&state_mutex);
	return count;
}

void
discord_stop(void)
{
	if (!started)
		return;
	atomic_store(&stopping, 1);
	if (ipc_fd >= 0)
		shutdown(ipc_fd, SHUT_RDWR);
	pthread_join(worker, NULL);
	if (mic_worker_started) {
		pthread_join(mic_worker, NULL);
		mic_worker_started = 0;
	}
	rpc_clear_speakers();
	if (event_fd >= 0)
		close(event_fd);
	event_fd = -1;
	free(client_secret);
	client_secret = NULL;
	client_id[0] = '\0';
	curl_global_cleanup();
	started = 0;
}
