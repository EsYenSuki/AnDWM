#ifndef DWM_DISCORD_H
#define DWM_DISCORD_H

#include <stddef.h>

#define DWM_DISCORD_SPEAKERS 16

typedef struct {
	char user_id[32];
	char username[128];
	char avatar_path[512];
	int speaking;
} DwmDiscordSpeaker;

int discord_start(void);
int discord_event_fd(void);
size_t discord_speakers(DwmDiscordSpeaker *speakers, size_t capacity);
void discord_stop(void);

#endif
