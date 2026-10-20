/* See LICENSE file for copyright and license details.
 *
 * dynamic window manager is designed like any other X client as well. It is
 * driven through handling X events. In contrast to other X clients, a window
 * manager selects for SubstructureRedirectMask on the root window, to receive
 * events about window (dis-)appearance. Only one X connection at a time is
 * allowed to select for this event mask.
 *
 * The event handlers of dwm are organized in an array which is accessed
 * whenever a new event has been fetched. This allows event dispatchingw
 * in O(1) time.
 *
 * Each child of the root window is called a client, except windows which have
 * set the override_redirect flag. Clients are organized in a linked client
 * list on each monitor, the focus history is remembered through a stack list
 * on each monitor. Each client contains a bit array to indicate the tags of a
 * client.
 *
 * Keys and tagging rules are organized as arrays and defined in config.h.
 *
 * To understand everything else, start reading main().
 */
#include <X11/Xatom.h>
#include <X11/Xlib.h>
#include <X11/Xproto.h>
#include <X11/Xutil.h>
#include <X11/cursorfont.h>
#include <X11/XKBlib.h>
#include <X11/keysym.h>
#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <glob.h>
#include <errno.h>
#include <limits.h>
#include <locale.h>
#include <math.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <poll.h>
#include <unistd.h>
#include <net/if.h>
#include <pthread.h>
#include <stdatomic.h>
#ifdef __linux__
#include <sys/eventfd.h>
#endif
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif /* XINERAMA */
#include "drw.h"
#include "util.h"
#include <Imlib2.h>
#include <X11/Xft/Xft.h>
#include <X11/extensions/Xrender.h>
#include <stdbool.h>
#include <dbus/dbus.h>
#include <pipewire/pipewire.h>
#include <spa/param/audio/format-utils.h>

#define SIDEBAR_WIDTH 64
#define SIDEBAR_CLICK_THRESH 5
#define DIALOG_ONTOP_PRIORITY 1000

#define FIFO_PATH "/tmp/dwm-pipn.fifo"
static void
sendn(const char *msg)
{
	int fd = open(FIFO_PATH, O_WRONLY | O_NONBLOCK);
	if (fd >= 0) {
		write(fd, msg, strlen(msg));
		write(fd, "\n", 1);
		close(fd);
	}
}




/* tile animation config */
#define TILE_ANIM_STEPS 1   /* more = smoother, smoother */
#define TILE_ANIM_DELAY 500 /* microseconds */

/* clock bar grow animation config */
#define CLOCK_ANIMATE    1     /* 0 disables, bar stays fixed-size */
#define CLOCK_ANIM_EXTRA 280   /* max px the bar grows past text width */
#define PW_MONITOR_SINK  1     /* 1 = system audio (what you hear), 0 = mic */
#define DRAW_FPS         50     /* visualizer update rate */
#define NOTIFY_MAX       5
#define NOTIFY_TIMEOUT   5
#define NOTIFY_TRANSITION_MS 500
#define NOTIFY_TWO_CONTENT_H 70
#define NOTIFY_MAX_W     300
#define NOTIFY_IMAGE_RADIUS 8
#define NOTIFY_MAX_TEXT  4096
#define NOTIFY_ACTION_H  30
#define NOTIFY_INPUT_ROW_H 30
#define NOTIFY_BUTTON_H (NOTIFY_ACTION_H - 6)
#define NOTIFY_BUTTON_ROW_H NOTIFY_ACTION_H
#define NOTIFY_ACTION_X  12
#define NOTIFY_TEXT_TOP_OFFSET 3
#define NOTIFY_TEXT_BOTTOM_GAP 0
#define NOTIFY_IMAGE_BUTTON_GAP 2
#define NOTIFY_HISTORY_MAX     10
#define NOTIFY_HISTORY_ENTRY_H 70
#define NOTIFY_HISTORY_MAX_H   (NOTIFY_HISTORY_ENTRY_H * 5)
#define NOTIFY_HISTORY_SCROLL_MS 500

static volatile int clockanim_running = 0;
static volatile unsigned int clockbar_dynw = 0; /* 0 = use fixed clockwidth() */
static volatile Window clockbar_win = 0;
static volatile int clockbar_cx = 0, clockbar_by = 0, clockbar_bh = 0;
static volatile int clockbar_cw = 0;
static volatile float clockbar_peak = 0.0f; /* 0..1, written by on_process */
static pthread_t clock_draw_thread;
static volatile int clock_draw_running = 0;
static volatile bool fullscreen_st; /* focused window is fullscreen */

typedef struct Notification Notification;
struct Notification {
  unsigned int id;
  char *app_name;
  char *summary;
  char *body;
  char *icon;
  char **actions;
  unsigned int action_count;
  int input_enabled;
  char *input_action;
  char *input_placeholder;
  char *input_text;
  Picture image;
  unsigned int image_w, image_h;
  int image_hint;
  struct timespec shown_at;
  Notification *next;
};

static DBusConnection *notify_conn;
static int notify_fd = -1;
static unsigned int notify_next_id = 1;
static Notification *notify_head, *notify_tail, *notify_current;
static Notification *notify_history_head, *notify_history_tail;
static int notify_active;
static int notify_transition_pending;
static struct timespec notify_transition_started;
static int notify_history_active;
static int notify_clock_hovered;
static unsigned int notify_width, notify_height;
static unsigned int notify_count;
static unsigned int notify_history_count;
static int notify_history_scroll;
static int notify_history_scroll_target;
static int notify_history_scroll_start;
static int notify_history_scroll_end;
static struct timespec notify_history_scroll_started;
static Clr notify_bg, notify_fg, notify_body;
static Clr notify_summary_scheme[3], notify_body_scheme[3];
static Clr notify_control_scheme[3], notify_control_hover_scheme[3];
static Clr notify_action_scheme[3], notify_action_hover_scheme[3];
static int notify_action_x[16], notify_action_w[16];
static int notify_input_x, notify_input_y, notify_input_w, notify_input_h;
static int notify_input_focus;
static Notification *notify_history_input;
static int notify_hovered;
static int notify_hover = -1;
static Notification *notify_history_hover_entry;
static int notify_history_hover_action = -1;
static struct timespec notify_hover_started;

static struct pw_thread_loop *sound_loop = NULL;
static struct pw_context *sound_context = NULL;
static struct pw_core *sound_core = NULL;
static struct spa_hook sound_core_listener;
static struct spa_hook sound_stream_listener;
static struct pw_stream *sound_stream = NULL;
static struct spa_audio_info sound_format;

/* macros */
#define BUTTONMASK (ButtonPressMask | ButtonReleaseMask)
#define CLEANMASK(mask)                                                        \
  (mask & ~(numlockmask | LockMask) &                                          \
   (ShiftMask | ControlMask | Mod1Mask | Mod2Mask | Mod3Mask | Mod4Mask |      \
    Mod5Mask))
#define INTERSECT(x, y, w, h, m)                                               \
  (MAX(0, MIN((x) + (w), (m)->wx + (m)->ww) - MAX((x), (m)->wx)) *             \
   MAX(0, MIN((y) + (h), (m)->wy + (m)->wh) - MAX((y), (m)->wy)))
#define INTERSECTC(x, y, w, h, z)                                              \
  (MAX(0, MIN((x) + (w), (z)->x + (z)->w) - MAX((x), (z)->x)) *                \
   MAX(0, MIN((y) + (h), (z)->y + (z)->h) - MAX((y), (z)->y)))
#define ISVISIBLE(C) ((C->tags & C->mon->tagset[C->mon->seltags]) || \
                      C->issticky || !shouldminimize(C))
#define HIDDEN(C) ((C)->isiconic)
#define LENGTH(X) (sizeof X / sizeof X[0])
#define MOUSEMASK (BUTTONMASK | PointerMotionMask)
#define WIDTH(X) ((X)->w + 2 * (X)->bw)
#define HEIGHT(X) ((X)->h + 2 * (X)->bw)
#define TAGMASK ((1 << LENGTH(tags)) - 1)
#define TAGSLENGTH (LENGTH(tags))
#define TEXTW(X) (drw_fontset_getwidth(drw, (X)) + lrpad)
#define MAXTABS 50

#define SYSTEM_TRAY_REQUEST_DOCK 0

/* XEMBED messages */
#define XEMBED_EMBEDDED_NOTIFY 0
#define XEMBED_WINDOW_ACTIVATE 1
#define XEMBED_FOCUS_IN 4
#define XEMBED_MODALITY_ON 10

#define XEMBED_MAPPED (1 << 0)
#define XEMBED_WINDOW_ACTIVATE 1
#define XEMBED_WINDOW_DEACTIVATE 2

#define VERSION_MAJOR 0
#define VERSION_MINOR 0
#define XEMBED_EMBEDDED_VERSION (VERSION_MAJOR << 16) | VERSION_MINOR

/* enums */
enum {
  CurNormal,
  CurResize,
  CurMove,
  CurResizeHorzArrow,
  CurResizeVertArrow,
  CurTopLeft,
  CurTopRight,
  CurBottomLeft,
  CurBottomRight,
  CurLast
}; /* cursor */
enum {
  SchemeNorm,
  SchemeSel,
  SchemeTitle,
  SchemeTag,
  SchemeTag1,
  SchemeTag2,
  SchemeTag3,
  SchemeTag4,
  SchemeTag5,
  SchemeTag6,
  SchemeTag7,
  SchemeTag8,
  SchemeTag9,
  SchemeLayout,
  TabSel,
  TabNorm,
  SchemeBtnPrev,
  SchemeBtnNext,
  SchemeBtnClose
}; /* color schemes */
enum {
  NetSupported,
  NetWMName,
  NetWMIcon,
  NetWMState,
  NetWMCheck,
  NetSystemTray,
  NetSystemTrayOP,
  NetSystemTrayOrientation,
  NetSystemTrayOrientationHorz,
  NetWMFullscreen,
  NetWMStateHidden,
  NetActiveWindow,
  NetWMSkipTaskbar,
  NetWMWindowType,
  NetWMWindowTypeDialog,
  NetWMWindowOpacity,
  NetWMBypassCompositor,
  NetClientList,
  NetClientInfo,
  NetDesktopNames,
  NetDesktopViewport,
  NetNumberOfDesktops,
  NetCurrentDesktop,
  NetNoAnimation,
  NetBarLeft,
  NetLast
}; /* EWMH atoms */
enum { Manager, Xembed, XembedInfo, XLast }; /* Xembed atoms */
enum {
  WMProtocols,
  WMDelete,
  WMState,
  WMTakeFocus,
  WMLast
}; /* default atoms */
enum {
  ClkTagBar,
  ClkTabBar,
  ClkTabPrev,
  ClkTabNext,
  ClkTabClose,
  ClkLtSymbol,
  ClkStatusText,
  ClkWinTitle,
  ClkClientWin,
  ClkRootWin,
  ClkLast
}; /* clicks */

enum showtab_modes {
  showtab_never,
  showtab_auto,
  showtab_nmodes,
  showtab_always
}; /* tab modes */

typedef union {
  int i;
  unsigned int ui;
  float f;
  const void *v;
} Arg;

typedef struct {
  unsigned int click;
  unsigned int mask;
  unsigned int button;
  void (*func)(const Arg *arg);
  const Arg arg;
} Button;

typedef struct Monitor Monitor;
typedef struct Client Client;
struct Client {
  char name[256];
  float mina, maxa;
  float cfact;
  int x, y, w, h;
  int oldx, oldy, oldw, oldh;
  int basew, baseh, incw, inch, maxw, maxh, minw, minh, hintsvalid;
  int bw, oldbw;
  unsigned int tags;
  int isfixed, iscentered, isfloating, isurgent, neverfocus, oldstate,
      isfullscreen;
  int isontop;
  int issticky;     /* sticky to background */
  int stickeystate; /* previous state before being sticky */
  int prevfloating;
  int prevx, prevy;
  int prevw, prevh;
  int wasfloating;
  unsigned int oldtags;
  unsigned int icw, ich;
  unsigned int ic_pw, ic_ph; /* actual picture pixel dimensions after drw_picture_create_resized */
  Picture icon;
  int beingmoved;
  Client *next;
  Client *snext;
  Monitor *mon;
  Window win;
  time_t lastvisible;
  int isautominimized;
  int fshidden;     /* hidden by fullscreen window */
  int wm_unmapped; /* unmap was initiated by WM, not client */
  int isiconic;    /* internal hidden state; true when we unmapped it */
  Client *pipparent; /* parent browser window that spawned this PIP */
};

typedef struct {
  unsigned int mod;
  KeySym keysym;
  void (*func)(const Arg *);
  const Arg arg;
} Key;

typedef struct {
  const char *symbol;
  void (*arrange)(Monitor *);
} Layout;

typedef struct {
  const char *class;
  const char *instance;
  const char *title;
  unsigned int tags;
  int iscentered;
  int isfloating;
  int isontop;
  int monitor;
} Rule;

typedef struct Systray Systray;
struct Systray {
  Window win;
  Client *icons;
};

typedef struct {
  const char **command;
  const char *name;
} Launcher;

typedef struct {
  char *display_name;
  Window win;
  long animation_data;
} AnimationPropertyArgs;

/* function declarations */
static Client *find_pipparent(Client *c);
static void applyrules(Client *c);
static int applysizehints(Client *c, int *x, int *y, int *w, int *h,
                          int interact);
static void arrange(Monitor *m);
static void arrangemon(Monitor *m);
static void attach(Client *c);
static void attachstack(Client *c);
static void buttonpress(XEvent *e);
static void checkotherwm(void);
static void cleanup(void);
static void prepare_workspace_switch(Monitor *m, unsigned int oldtags, unsigned int newtags);
static void checkminimize(void);
static time_t next_minimize_deadline(void);
static void cleanupmon(Monitor *mon);
static void clientmessage(XEvent *e);
static void configure(Client *c);
static void configurenotify(XEvent *e);
static void configurerequest(XEvent *e);
static Monitor *createmon(void);
static void cyclelayout(const Arg *arg);
static unsigned int clockwidth(void);
static unsigned int kblayoutwidth(void);
static void destroynotify(XEvent *e);
static void detach(Client *c);
static void detachstack(Client *c);
static Monitor *dirtomon(int dir);
static void dragmfact(const Arg *arg);
static void dragcfact(const Arg *arg);
static void drawbar(Monitor *m);
static void drawbars(void);
static int drawstatusbar(Monitor *m, int bh, char *text);
static void drawtab(Monitor *m);
static void drawtabs(void);
static void calcsidebar(Monitor *m);
static void drawsidebar(Monitor *m);
static void drawsidbars(void);
static void showsidbar(Monitor *m);
static void hideosidebar(Monitor *m);
static void enternotify(XEvent *e);
static void expose(XEvent *e);
static void focus(Client *c);
static void focusin(XEvent *e);
static void focusmon(const Arg *arg);
static void focusstack(const Arg *arg);
static void focuswin(const Arg *arg);
static Atom getatomprop(Client *c, Atom prop);
static Picture geticonprop(Window w, unsigned int *icw, unsigned int *ich, unsigned int *pw, unsigned int *ph);
static int getrootptr(int *x, int *y);
static long getstate(Window w);
static unsigned int getsystraywidth();
static int gettextprop(Window w, Atom atom, char *text, unsigned int size);
static void grabbuttons(Client *c, int focused);
static void grabkeys(void);
static void hide(Client *c);
static void incnmaster(const Arg *arg);
static void keypress(XEvent *e);
static void killclient(const Arg *arg);
static void forcekillclient(const Arg *arg);
static void manage(Window w, XWindowAttributes *wa);
static void mappingnotify(XEvent *e);
static void maprequest(XEvent *e);
static void mapnotify(XEvent *e);
static void monocle(Monitor *m);
static void motionnotify(XEvent *e);
static void movemouse(const Arg *arg);
static void moveorplace(const Arg *arg);
static Client *nexttiled(Client *c);
static void placemouse(const Arg *arg);
static void pop(Client *c);
static void propertynotify(XEvent *e);
static void restart(const Arg *arg);
static Client *recttoclient(int x, int y, int w, int h);
static Monitor *recttomon(int x, int y, int w, int h);
static void removesystrayicon(Client *i);
static void resize(Client *c, int x, int y, int w, int h, int interact);
static void resizebarwin(Monitor *m);
static void resizeclient(Client *c, int x, int y, int w, int h);
static void resizemouse(const Arg *arg);
static void resizerequest(XEvent *e);
static void restack(Monitor *m);
static void run(void);
static void scan(void);
static int sendevent(Window w, Atom proto, int m, long d0, long d1, long d2,
                     long d3, long d4);
static void sendmon(Client *c, Monitor *m);
static void setclientstate(Client *c, long state);
static void setclienttagprop(Client *c);
static void sound_monitor_start(void);
static void sound_monitor_stop(void);
static void setnoanimation_async(Client *c, long val);
static void setnoanimation_sync(Client *c, long val);
static void setworkspaceanimation(Monitor *m, int val);
static void setcurrentdesktop(void);
static void setdesktopnames(void);
static void setfocus(Client *c);
static int shouldminimize(Client *c);
static void setfullscreen(Client *c, int fullscreen);
static void sync_bypass_compositor(Client *c);
static int get_bypass_compositor_value(Client *c);
static int haswindowproperty(Client *c, Atom prop);
static int window_has_transparency(Client *c);
static void setwindowopacity(Client *c);
static void clearwindowopacity(Client *c);
static void setlayout(const Arg *arg);
static void setcfact(const Arg *arg);
static void setmfact(const Arg *arg);
static void setnumdesktops(void);
static void setup(void);
static void setviewport(void);
static void seturgent(Client *c, int urg);
static void show(Client *c);
static void showhide(Client *c);
static void restorefullscreenhidden(Monitor *m);
static void showtagpreview(int tag);
static void spawn(const Arg *arg);
static unsigned int statuswidth(char *text);
static void switchtag(void);
static Monitor *systraytomon(Monitor *m);
static void tabmode(const Arg *arg);
static void tag(const Arg *arg);
static void tagmon(const Arg *arg);
static void togglebar(const Arg *arg);
static void togglefloating(const Arg *arg);
static void togglefloating_noarrange(Client *c);
static void togglefullscr(const Arg *arg);
static void togglesticky(Client *c, int fullscreen);
static void togglestickyclient(const Arg *arg);
static void toggletag(const Arg *arg);
static void toggleview(const Arg *arg);
static void freeicon(Client *c);
static void hidewin(const Arg *arg);
static void restorewin(const Arg *arg);
static void togglewin(const Arg *arg);
static void unfocus(Client *c, int setfocus);
static void unmanage(Client *c, int destroyed);
static void unmapnotify(XEvent *e);
static void updatenumberofdesktops(void);
static void updatecurrentdesktop(unsigned int tagset);
static void updatebarpos(Monitor *m);
static void updatebars(void);
static void updatepreview(void);
static void updateclientlist(void);
static void updateclock(void);
static void updateclockbar(void);
static void status_start(void);
static void status_stop(void);
static void status_consume(void);
static int update_mpris_scroll(void);
static int drag_next_event(XEvent *ev);

#define STATUS_SLOTS 3
#define STATUS_SIZE 1024
#define MPRIS_WIDTH 240
#define MPRIS_SCROLL_GAP 32
#define MPRIS_SCROLL_PAD 8
#define MPRIS_SCROLL_INTERVAL_NS 33333333ULL
#define MPRIS_COMPLETE_THRESHOLD 0.995
enum status_slot_state { STATUS_FREE, STATUS_WRITING, STATUS_PUBLISHED,
                         STATUS_READING };
typedef struct {
	_Atomic int state;
	char text[STATUS_SIZE];
	char mpris[768];
	double mpris_progress;
} StatusSlot;
static StatusSlot status_slots[STATUS_SLOTS];
static pthread_t status_thread;
static _Atomic int status_running;
static int status_event_fd = -1;
static char stext[1024];
static char mpris_text[768];
static int mpris_scroll_px;
static struct timespec mpris_scroll_last;
static uint64_t mpris_scroll_accum_ns;
static int mpris_scroll_clock_valid;
static int mpris_active;
static unsigned int mpris_scroll_text_width;
static double mpris_progress = -1.0;
static Clr mpris_scroll_bg_clr;
static Clr mpris_progress_clr;
static int bar_dirty;

static int status_read_int(const char *path, int fallback) {
	FILE *f = fopen(path, "r");
	int value;
	if (!f) return fallback;
	if (fscanf(f, "%d", &value) != 1) value = fallback;
	fclose(f);
	return value;
}

static int status_read_cpu(unsigned long long *total, unsigned long long *active) {
	FILE *f = fopen("/proc/stat", "r");
	unsigned long long user, nice, system, idle, iowait, irq, softirq, steal;
	char cpu[8];
	int ok = 0;
	if (f && fscanf(f, "%7s %llu %llu %llu %llu %llu %llu %llu %llu", cpu,
	                &user, &nice, &system, &idle, &iowait, &irq, &softirq,
	                &steal) == 9) {
		*total = user + nice + system + idle + iowait + irq + softirq + steal;
		*active = *total - idle - iowait;
		ok = 1;
	}
	if (f) fclose(f);
	return ok;
}

static void status_read_memory(unsigned long long *used, unsigned long long *total,
                               int *percent) {
	FILE *f = fopen("/proc/meminfo", "r");
	char key[32], unit[16];
	unsigned long long value, available = 0;
	*used = *total = 0;
	if (f) {
		while (fscanf(f, "%31s %llu %15s", key, &value, unit) == 3) {
			if (!strcmp(key, "MemTotal:")) *total = value;
			else if (!strcmp(key, "MemAvailable:")) available = value;
		}
		fclose(f);
	}
	*used = (*total > available) ? *total - available : 0;
	*percent = *total ? (int)((*used * 100 + *total / 2) / *total) : 0;
}

static int status_read_line(const char *path, char *out, size_t outlen) {
	FILE *f = fopen(path, "r");
	if (!f) return 0;
	if (!fgets(out, outlen, f)) { fclose(f); return 0; }
	fclose(f);
	out[strcspn(out, "\r\n")] = '\0';
	return 1;
}

static DBusMessage *status_nm_property(DBusConnection *connection,
                                        const char *path, const char *interface,
                                        const char *property) {
	DBusMessage *message, *reply;

	message = dbus_message_new_method_call(
		"org.freedesktop.NetworkManager", path,
		"org.freedesktop.DBus.Properties", "Get");
	if (!message)
		return NULL;
	dbus_message_append_args(message, DBUS_TYPE_STRING, &interface,
	                         DBUS_TYPE_STRING, &property, DBUS_TYPE_INVALID);
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, NULL);
	dbus_message_unref(message);
	return reply;
}

static int status_wifi(char *name, size_t namelen, int *strength) {
	static DBusConnection *connection;
	DBusMessage *reply;
	DBusMessageIter iter, variant, value;
	const char *path;
	const char *device_path = NULL;
	const char *ap_path = NULL;
	uint32_t device_type;
	unsigned char signal_strength;

	name[0] = '\0';
	*strength = 0;
	if (!connection)
		connection = dbus_bus_get(DBUS_BUS_SYSTEM, NULL);
	if (!connection)
		return 0;

	/* Follow NetworkManager's PrimaryConnection, just like bar.cpp. */
	reply = status_nm_property(connection, "/org/freedesktop/NetworkManager",
	                           "org.freedesktop.NetworkManager", "PrimaryConnection");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_OBJECT_PATH) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &path);
	if (!path || !strcmp(path, "/")) {
		dbus_message_unref(reply);
		return 0;
	}
	char connection_path[PATH_MAX];
	snprintf(connection_path, sizeof connection_path, "%s", path);
	dbus_message_unref(reply);

	reply = status_nm_property(connection, connection_path,
	                           "org.freedesktop.NetworkManager.Connection.Active",
	                           "Devices");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_ARRAY) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&variant, &value);
	if (dbus_message_iter_get_arg_type(&value) != DBUS_TYPE_OBJECT_PATH) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&value, &device_path);
	char device_path_copy[PATH_MAX];
	snprintf(device_path_copy, sizeof device_path_copy, "%s", device_path);
	dbus_message_unref(reply);

	reply = status_nm_property(connection, device_path_copy,
	                           "org.freedesktop.NetworkManager.Device", "DeviceType");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_UINT32) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &device_type);
	dbus_message_unref(reply);
	if (device_type != 2)
		return 0;

	reply = status_nm_property(connection, device_path_copy,
	                           "org.freedesktop.NetworkManager.Device.Wireless",
	                           "ActiveAccessPoint");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_OBJECT_PATH) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &ap_path);
	char ap_path_copy[PATH_MAX];
	snprintf(ap_path_copy, sizeof ap_path_copy, "%s", ap_path);
	dbus_message_unref(reply);
	if (!strcmp(ap_path_copy, "/"))
		return 0;

	reply = status_nm_property(connection, ap_path_copy,
	                           "org.freedesktop.NetworkManager.AccessPoint", "Ssid");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_ARRAY) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&variant, &value);
	if (dbus_message_iter_get_arg_type(&value) != DBUS_TYPE_BYTE) {
		dbus_message_unref(reply);
		return 0;
	}
	{
		size_t n = 0;
		while (dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_BYTE) {
			unsigned char byte;
			dbus_message_iter_get_basic(&value, &byte);
			if (n + 1 < namelen)
				name[n] = (char)byte;
			n++;
			if (!dbus_message_iter_next(&value))
				break;
		}
		if (namelen)
			name[n < namelen ? n : namelen - 1] = '\0';
	}
	dbus_message_unref(reply);

	reply = status_nm_property(connection, ap_path_copy,
	                           "org.freedesktop.NetworkManager.AccessPoint", "Strength");
	if (!reply)
		return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_BYTE) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &signal_strength);
	*strength = signal_strength;
	dbus_message_unref(reply);
	return name[0] != '\0';
}

static DBusMessage *status_dbus_call(DBusConnection *connection, const char *service,
                                     const char *path, const char *interface,
                                     const char *method) {
	DBusMessage *message, *reply;
	DBusError error;
	message = dbus_message_new_method_call(service, path, interface, method);
	if (!message) return NULL;
	dbus_error_init(&error);
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, &error);
	dbus_message_unref(message);
	dbus_error_free(&error);
	return reply;
}

static int status_dbus_property_string(DBusConnection *connection, const char *service,
                                       const char *property, char *out, size_t outlen) {
	DBusMessage *message, *reply;
	DBusMessageIter iter, variant;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	const char *value;
	message = dbus_message_new_method_call(service, "/org/mpris/MediaPlayer2",
	        "org.freedesktop.DBus.Properties", "Get");
	if (!message) return 0;
	dbus_message_append_args(message, DBUS_TYPE_STRING, &interface,
	                         DBUS_TYPE_STRING, &property, DBUS_TYPE_INVALID);
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, NULL);
	dbus_message_unref(message);
	if (!reply) return 0;
	if (!dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_STRING) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &value);
	snprintf(out, outlen, "%s", value ? value : "");
	dbus_message_unref(reply);
	return 1;
}

static int status_dbus_property_int64(DBusConnection *connection, const char *service,
                                      const char *property, int64_t *out) {
	DBusMessage *message, *reply;
	DBusMessageIter iter, variant;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	int64_t value;
	uint64_t unsigned_value;
	message = dbus_message_new_method_call(service, "/org/mpris/MediaPlayer2",
	        "org.freedesktop.DBus.Properties", "Get");
	if (!message) return 0;
	dbus_message_append_args(message, DBUS_TYPE_STRING, &interface,
	                         DBUS_TYPE_STRING, &property, DBUS_TYPE_INVALID);
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, NULL);
	dbus_message_unref(message);
	if (!reply || !dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		if (reply) dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) == DBUS_TYPE_INT64) {
		dbus_message_iter_get_basic(&variant, &value);
	} else if (dbus_message_iter_get_arg_type(&variant) == DBUS_TYPE_UINT64) {
		dbus_message_iter_get_basic(&variant, &unsigned_value);
		if (unsigned_value > INT64_MAX) {
			dbus_message_unref(reply);
			return 0;
		}
		value = (int64_t)unsigned_value;
	} else {
		dbus_message_unref(reply);
		return 0;
	}
	*out = value;
	dbus_message_unref(reply);
	return 1;
}

static int status_mpris_metadata(DBusConnection *connection, const char *service,
                                 char *artist, size_t artistlen,
                                 char *title, size_t titlelen,
                                 int64_t *length_us) {
	DBusMessage *message, *reply;
	DBusMessageIter iter, variant, dict;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	const char *property = "Metadata";
	artist[0] = title[0] = '\0';
	*length_us = 0;
	message = dbus_message_new_method_call(service, "/org/mpris/MediaPlayer2",
	        "org.freedesktop.DBus.Properties", "Get");
	if (!message) return 0;
	dbus_message_append_args(message, DBUS_TYPE_STRING, &interface,
	                         DBUS_TYPE_STRING, &property, DBUS_TYPE_INVALID);
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, NULL);
	dbus_message_unref(message);
	if (!reply || !dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT) {
		if (reply) dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &variant);
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_ARRAY) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_recurse(&variant, &dict);
	while (dbus_message_iter_get_arg_type(&dict) == DBUS_TYPE_DICT_ENTRY) {
		DBusMessageIter entry, value;
		const char *key;
		dbus_message_iter_recurse(&dict, &entry);
		if (dbus_message_iter_get_arg_type(&entry) != DBUS_TYPE_STRING) goto next;
		dbus_message_iter_get_basic(&entry, &key);
		if (!dbus_message_iter_next(&entry) ||
		    dbus_message_iter_get_arg_type(&entry) != DBUS_TYPE_VARIANT) goto next;
		dbus_message_iter_recurse(&entry, &value);
		if (!strcmp(key, "xesam:title") &&
		    dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_STRING) {
			const char *s;
			dbus_message_iter_get_basic(&value, &s);
			snprintf(title, titlelen, "%s", s ? s : "");
		} else if (!strcmp(key, "xesam:artist") &&
		           dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_ARRAY) {
			DBusMessageIter artists;
			dbus_message_iter_recurse(&value, &artists);
			if (dbus_message_iter_get_arg_type(&artists) == DBUS_TYPE_STRING) {
				const char *s;
				dbus_message_iter_get_basic(&artists, &s);
				snprintf(artist, artistlen, "%s", s ? s : "");
			}
		} else if (!strcmp(key, "mpris:length")) {
			int type = dbus_message_iter_get_arg_type(&value);
			if (type == DBUS_TYPE_INT64) {
				dbus_message_iter_get_basic(&value, length_us);
			} else if (type == DBUS_TYPE_UINT64) {
				uint64_t unsigned_length;
				dbus_message_iter_get_basic(&value, &unsigned_length);
				if (unsigned_length <= INT64_MAX)
					*length_us = (int64_t)unsigned_length;
			}
		}
next:
		dbus_message_iter_next(&dict);
	}
	dbus_message_unref(reply);
	return *title != '\0';
}

static int status_mpris(char *out, size_t outlen, char *raw, size_t rawlen,
                        double *progress) {
	DBusConnection *connection;
	DBusMessage *reply;
	DBusMessageIter iter, names;
	char artist[192], title[384], state[32];
	int64_t position_us = 0, length_us = 0;
	char service[128] = "";
	*progress = -1.0;
	connection = dbus_bus_get(DBUS_BUS_SESSION, NULL);
	if (!connection) return 0;
	reply = status_dbus_call(connection, "org.freedesktop.DBus", "/org/freedesktop/DBus",
	                         "org.freedesktop.DBus", "ListNames");
	if (!reply || !dbus_message_iter_init(reply, &iter) ||
	    dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_ARRAY) {
		if (reply) dbus_message_unref(reply);
		dbus_connection_unref(connection);
		return 0;
	}
	dbus_message_iter_recurse(&iter, &names);
	while (dbus_message_iter_get_arg_type(&names) == DBUS_TYPE_STRING) {
		const char *name;
		dbus_message_iter_get_basic(&names, &name);
		if (name && !strncmp(name, "org.mpris.MediaPlayer2.", 23)) {
			snprintf(state, sizeof state, "Stopped");
			if (status_dbus_property_string(connection, name, "PlaybackStatus",
			                               state, sizeof state) && !strcmp(state, "Playing")) {
				snprintf(service, sizeof service, "%s", name);
				break;
			}
		}
		dbus_message_iter_next(&names);
	}
	dbus_message_unref(reply);
	if (!service[0] || !status_mpris_metadata(connection, service, artist, sizeof artist,
	                                       title, sizeof title, &length_us)) {
		dbus_connection_unref(connection);
		return 0;
	}
	if (length_us > 0 && status_dbus_property_int64(connection, service,
	                                                  "Position", &position_us)) {
		if (position_us < 0) position_us = 0;
		if (position_us > length_us) position_us = length_us;
		*progress = (double)position_us / (double)length_us;
		if (*progress >= MPRIS_COMPLETE_THRESHOLD)
			*progress = 1.0;
	}
	for (char *s = artist; *s; s++) *s = (char)toupper((unsigned char)*s);
	if (strlen(artist) >= 8 && !strcmp(artist + strlen(artist) - 8, " - TOPIC"))
		artist[strlen(artist) - 8] = '\0';
	/* Keep the same wrapper and spacing as bar.cpp::player_info().  The
	 * position bar is intentionally generated only after metadata succeeds;
	 * malformed players fall back to the normal status branch. */
	if (raw && rawlen)
		snprintf(raw, rawlen, "[%s]  %s", artist[0] ? artist : "UNKNOWN ARTIST", title);
	snprintf(out, outlen,
	         "^c#1E1D2D^ ^b#B8E9B4^ 󰎆^c#1E1D2D^ ^m^%s^M^^d^^c#96CDFB^",
	         raw && rawlen ? raw : "");
	dbus_connection_unref(connection);
	return 1;
}

static int status_temperature(void) {
	static const char *paths[] = {
		"/sys/class/thermal/thermal_zone0/temp",
		"/sys/class/thermal/thermal_zone1/temp",
		"/sys/class/hwmon/hwmon0/temp1_input",
		"/sys/class/hwmon/hwmon1/temp1_input",
		"/sys/class/hwmon/hwmon2/temp1_input",
		"/sys/class/hwmon/hwmon3/temp1_input"
	};
	int max = -1;
	for (size_t i = 0; i < LENGTH(paths); i++) {
		int value = status_read_int(paths[i], -1);
		if (value > 1000) value /= 1000;
		if (value > max) max = value;
	}
	return max;
}

static int status_fan(char *icon, size_t iconlen) {
	glob_t matches;
	char value[16];
	int enabled = 0;
	icon[0] = '\0';
	if (glob("/sys/devices/platform/asus-nb-wmi/hwmon/*/pwm1_enable", 0, NULL,
	         &matches) != 0)
		return 0;
	if (matches.gl_pathc) {
		if (status_read_line(matches.gl_pathv[0], value, sizeof value) &&
		    strcmp(value, "2")) {
			snprintf(icon, iconlen, "");
			enabled = 1;
		}
	}
	globfree(&matches);
	return enabled;
}

static void status_make(char *out, size_t outlen, char *mpris_out, size_t mpris_len,
                        double *mpris_progress_out,
                        unsigned long long *last_total, unsigned long long *last_active) {
	unsigned long long total = 0, active = 0, used, memtotal;
	int mempercent, cpu = 0, cap, charging, strength, temp;
	char memtext[32], ssid[128], player[768], fan[16], sav_icon[64], governor[32], tlp[32];
	const char *icon, *wicon, *bicon, *memcolor;
	static int fan_st;
	int wifi = status_wifi(ssid, sizeof ssid, &strength);
	int has_player;
	ssid[sizeof ssid - 1] = '\0';
	if (status_read_cpu(&total, &active) && *last_total && total > *last_total) {
		unsigned long long td = total - *last_total;
		unsigned long long ad = active - *last_active;
		cpu = (int)((ad * 1000 + td / 2) / td);
	}
	*last_total = total;
	*last_active = active;
	status_read_memory(&used, &memtotal, &mempercent);
	if (used >= 1024ULL * 1024ULL) snprintf(memtext, sizeof memtext, "%.1fGi", used / (1024.0 * 1024.0));
	else if (used >= 1024ULL) snprintf(memtext, sizeof memtext, "%.1fMi", used / 1024.0);
	else snprintf(memtext, sizeof memtext, "%.1fkB", (double)used);
	cap = status_read_int("/sys/class/power_supply/BAT0/capacity", 0);
	charging = status_read_int("/sys/class/power_supply/AC0/online", 0);
	icon = mempercent < 40 ? "󰾆" : (mempercent < 80 ? "󰾅" : "󰓅");
	memcolor = mempercent < 80 ? "#1E1D2D" : "#ed8796";
	if (!wifi) wicon = "󰤭";
	else if (strength > 60) wicon = "󰤨";
	else if (strength > 45) wicon = "󰤥";
	else if (strength > 35) wicon = "󰤢";
	else wicon = "󰤟";
	bicon = charging ? "󰂄" : (cap >= 90 ? "󰁹" : (cap >= 50 ? "󰁿" :
	        (cap >= 20 ? "󰁼" : "󰁺")));
	temp = status_temperature();
	status_read_line("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor",
	                 governor, sizeof governor);
	status_read_line("/run/tlp/last_pwr", tlp, sizeof tlp);
	status_fan(fan, sizeof fan);
	if (!strcmp(tlp, "0 0") && !strcmp(governor, "ondemand") && temp > 79 && !fan_st) {
		/* Same fan policy as bar.cpp, but the worker writes only sysfs. */
		glob_t matches;
		if (glob("/sys/devices/platform/asus-nb-wmi/hwmon/*/pwm1_enable", 0, NULL, &matches) == 0) {
			if (matches.gl_pathc) { FILE *f = fopen(matches.gl_pathv[0], "w"); if (f) { fputs("0", f); fclose(f); } }
			globfree(&matches);
		}
		fan_st = 1;
	} else if ((strcmp(tlp, "0 0") || (!strcmp(governor, "ondemand") && temp <= 72)) && fan_st) {
		glob_t matches;
		if (glob("/sys/devices/platform/asus-nb-wmi/hwmon/*/pwm1_enable", 0, NULL, &matches) == 0) {
			if (matches.gl_pathc) { FILE *f = fopen(matches.gl_pathv[0], "w"); if (f) { fputs("2", f); fclose(f); } }
			globfree(&matches);
		}
		fan_st = 0;
	}
	if (!fan_st) fan[0] = '\0';
	if (mpris_out && mpris_len) mpris_out[0] = '\0';
	if (mpris_progress_out) *mpris_progress_out = -1.0;
	has_player = status_mpris(player, sizeof player, mpris_out, mpris_len,
	                          mpris_progress_out);
	sav_icon[0] = '\0';
	if (fan[0] || !strcmp(governor, "performance")) {
		snprintf(sav_icon, sizeof sav_icon, "  %s%s%s", fan,
		         fan[0] && !strcmp(governor, "performance") ? " " : "",
		         !strcmp(governor, "performance") ? "" : "");
	}
	if (has_player) {
			snprintf(out, outlen,
			"^c#a6e3a1^%s %s^c%s^ ^b#96CDFB^ %s ^d^"
			"^c#1E1D2D^ ^b#96CDFB^ %s ^d^"
			"^c#96CDFB^ %s^b#1E1D2D^ ",
				sav_icon, player, memcolor, icon, wicon, bicon);
	} else {
		snprintf(out, outlen,
			"^c#a6e3a1^%s  ^c#96CDFB^%s %d%%^c#1E1D2D^ ^b#a6e3a1^ "
			"^c#D9E0EE^ ^b#282737^ %4.1f%% ^d^"
			"^c%s^ ^b#a6e3a1^ %s^c#D9E0EE^ ^b#282737^ %s ^d^"
			"^c#1E1D2D^ ^b#96CDFB^ %s^c#D9E0EE^ ^b#282737^ %s ^d^^b#1E1D2D^ ",
			sav_icon, bicon, cap, cpu / 10.0, memcolor, icon, memtext,
			wicon, wifi ? ssid : "Disconnected");
	}
}

static void *status_worker(void *arg) {
	char local[STATUS_SIZE], local_mpris[768];
	char last_mpris[768] = "";
	double local_mpris_progress;
	double last_mpris_progress = -1.0;
	unsigned long long last_total = 0, last_active = 0;
	(void)arg;
	while (atomic_load_explicit(&status_running, memory_order_acquire)) {
		struct timespec ts = { .tv_sec = 1, .tv_nsec = 0 };
		status_make(local, sizeof local, local_mpris, sizeof local_mpris,
		            &local_mpris_progress,
		            &last_total, &last_active);
		/* Some browser players briefly omit Position while refreshing their
		 * metadata. Keep the last known value for the same track instead of
		 * making the progress layer blink off for one status interval. */
		if (local_mpris_progress < 0.0 && local_mpris[0] &&
		    !strcmp(local_mpris, last_mpris))
			local_mpris_progress = last_mpris_progress;
		if (local_mpris_progress >= 0.0) {
			last_mpris_progress = local_mpris_progress;
			snprintf(last_mpris, sizeof last_mpris, "%s", local_mpris);
		} else if (!local_mpris[0]) {
			last_mpris[0] = '\0';
			last_mpris_progress = -1.0;
		}
		for (int i = 0; i < STATUS_SLOTS; i++) {
			int expected = STATUS_FREE;
			if (atomic_compare_exchange_strong_explicit(&status_slots[i].state, &expected,
				STATUS_WRITING, memory_order_acquire, memory_order_relaxed)) {
				memcpy(status_slots[i].text, local, sizeof local);
				memcpy(status_slots[i].mpris, local_mpris, sizeof local_mpris);
				status_slots[i].mpris_progress = local_mpris_progress;
				atomic_store_explicit(&status_slots[i].state, STATUS_PUBLISHED, memory_order_release);
				if (status_event_fd >= 0) { uint64_t one = 1; (void)write(status_event_fd, &one, sizeof one); }
				break;
			}
		}
		nanosleep(&ts, NULL);
	}
	return NULL;
}

static void status_start(void) {
	for (int i = 0; i < STATUS_SLOTS; i++) atomic_init(&status_slots[i].state, STATUS_FREE);
	atomic_init(&status_running, 1);
#ifdef __linux__
	status_event_fd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
#endif
	if (pthread_create(&status_thread, NULL, status_worker, NULL) != 0) {
		atomic_store(&status_running, 0);
		if (status_event_fd >= 0) { close(status_event_fd); status_event_fd = -1; }
	}
}

static void status_stop(void) {
	if (!atomic_exchange(&status_running, 0)) return;
	if (status_event_fd >= 0) { uint64_t one = 1; (void)write(status_event_fd, &one, sizeof one); }
	pthread_join(status_thread, NULL);
	if (status_event_fd >= 0) { close(status_event_fd); status_event_fd = -1; }
}

static void status_consume(void) {
	uint64_t value;
	if (status_event_fd >= 0) while (read(status_event_fd, &value, sizeof value) == sizeof value) ;
	for (int i = 0; i < STATUS_SLOTS; i++) {
		int expected = STATUS_PUBLISHED;
		if (atomic_compare_exchange_strong_explicit(&status_slots[i].state, &expected,
			STATUS_READING, memory_order_acquire, memory_order_relaxed)) {
			memcpy(stext, status_slots[i].text, sizeof stext);
			stext[sizeof stext - 1] = '\0';
			if (strcmp(mpris_text, status_slots[i].mpris)) {
				mpris_scroll_px = 0;
				/* The cached width belongs to the previous title. */
				mpris_scroll_text_width = 0;
				mpris_scroll_accum_ns = 0;
				mpris_scroll_clock_valid = 0;
				memcpy(mpris_text, status_slots[i].mpris, sizeof mpris_text);
				mpris_text[sizeof mpris_text - 1] = '\0';
				mpris_active = mpris_text[0] != '\0';
			}
			mpris_progress = status_slots[i].mpris_progress;
			atomic_store_explicit(&status_slots[i].state, STATUS_FREE, memory_order_release);
			bar_dirty = 1;
			break;
		}
	}
}

static void notification_init(void);
static void notification_shutdown(void);
static void notification_dispatch(void);
static void notification_tick(void);
static void notification_draw(void);
static void notification_advance(void);
static void notification_clear_queue(void);
static void notification_emit_closed(Notification *n, uint32_t reason);
static void notification_emit_action(Notification *n, const char *action);
static void notification_emit_input(Notification *n);
static int notification_buttonpress(XButtonPressedEvent *ev);
static int notification_input_keypress(XKeyEvent *ev);
static void notification_update_layout(Notification *n);
static void notification_motion(XMotionEvent *ev);
static void notification_history_motion(XMotionEvent *ev);
static void notification_history_draw(void);
static void notification_history_layout(void);
static void notification_history_add(Notification *n);
static void notification_history_show(void);
static void notification_history_hide(void);
static int notification_center_active(void);
static int notification_history_buttonpress(XButtonPressedEvent *ev);
static int notification_history_tick(void);
static void leavenotify(XEvent *e);
static int updategeom(void);
static void updatenumlockmask(void);
static void updatesizehints(Client *c);
static void updatestatus(void);
static void updatesystray(void);
static void updatesystrayicongeom(Client *i, int w, int h);
static void updatesystrayiconstate(Client *i, XPropertyEvent *ev);
static void updatetitle(Client *c);
static void updateicon(Client *c);
static void updatewindowtype(Client *c);
static void updatewmhints(Client *c);
static void view(const Arg *arg);
static void *set_animation_property_thread(void *arg);
static Client *wintoclient(Window w);
static Monitor *wintomon(Window w);
static Client *wintosystrayicon(Window w);
static int xerror(Display *dpy, XErrorEvent *ee);
static int xerrordummy(Display *dpy, XErrorEvent *ee);
static int xerrorstart(Display *dpy, XErrorEvent *ee);
static Window ontopsibling(Monitor *m, Client *exclude);
static void zoom(const Arg *arg);
static void alttab(const Arg *arg);

/* variables */
static Systray *systray = NULL;
static const char broken[] = "broken";
static char clockstr[8] = "00:00";
static char kbstr[16] = "us";
static int screen;
static int sw, sh; /* X display screen geometry width, height */
static int bh;     /* bar height */
static int th = 0; /* tab bar geometry */
static int lrpad;  /* sum of left and right padding for text */
static int (*xerrorxlib)(Display *, XErrorEvent *);
static unsigned int numlockmask = 0;
static Time last_ev_time;
static void (*handler[LASTEvent])(XEvent *) = {
    [ButtonPress] = buttonpress,
    [ClientMessage] = clientmessage,
    [ConfigureRequest] = configurerequest,
    [ConfigureNotify] = configurenotify,
    [DestroyNotify] = destroynotify,
    [EnterNotify] = enternotify,
    [Expose] = expose,
    [FocusIn] = focusin,
    [KeyPress] = keypress,
    [KeyRelease] = keypress,
    [LeaveNotify] = leavenotify,
    [MappingNotify] = mappingnotify,
    [MapRequest] = maprequest,
    [MapNotify] = mapnotify,
    [MotionNotify] = motionnotify,
    [PropertyNotify] = propertynotify,
    [ResizeRequest] = resizerequest,
    [UnmapNotify] = unmapnotify};
static Atom wmatom[WMLast], netatom[NetLast], xatom[XLast];
static int running = 1;
static int xkb_event_base = 0;
static int alt_held = 0;
/* Client currently being dragged; used to keep it visible across tag views. */
static Client *dragclient = NULL;
/* When non-zero, tiled-resizes use animated transitions via
 * resizeclient_animated. You can temporarily disable it to have
 * instant resize via resizeclient. */
static Bool animate_tiled = 1;
static Cur *cursor[CurLast];
static Clr **scheme, clrborder;
static Display *dpy;
static Drw *drw;
static Monitor *mons, *selmon;
static Window root, wmcheckwin;

static int update_mpris_scroll(void) {
	struct timespec now_mono;
	unsigned int textw;
	unsigned int cycle;
	uint64_t elapsed_ns = 0;
	uint64_t steps;

	if (!mpris_active) {
		mpris_scroll_clock_valid = 0;
		mpris_scroll_accum_ns = 0;
		return 0;
	}

	textw = mpris_scroll_text_width ? mpris_scroll_text_width : TEXTW(mpris_text);
	cycle = textw + MPRIS_SCROLL_GAP;
	clock_gettime(CLOCK_MONOTONIC, &now_mono);
	if (mpris_scroll_clock_valid) {
		elapsed_ns = (uint64_t)(now_mono.tv_sec - mpris_scroll_last.tv_sec) * 1000000000ULL;
		if (now_mono.tv_nsec >= mpris_scroll_last.tv_nsec)
			elapsed_ns += (uint64_t)(now_mono.tv_nsec - mpris_scroll_last.tv_nsec);
		else
			elapsed_ns -= (uint64_t)(mpris_scroll_last.tv_nsec - now_mono.tv_nsec);
		/* Do not jump several seconds after a suspend or a blocked loop. */
		if (elapsed_ns > 250000000ULL)
			elapsed_ns = 250000000ULL;
		mpris_scroll_accum_ns += elapsed_ns;
	} else {
		mpris_scroll_clock_valid = 1;
	}
	mpris_scroll_last = now_mono;
	steps = mpris_scroll_accum_ns / MPRIS_SCROLL_INTERVAL_NS;
	mpris_scroll_accum_ns %= MPRIS_SCROLL_INTERVAL_NS;
	if (textw + 2 * MPRIS_SCROLL_PAD > MPRIS_WIDTH && cycle && steps) {
		mpris_scroll_px = (mpris_scroll_px + steps) % cycle;
		return 1;
	} else if (textw + 2 * MPRIS_SCROLL_PAD <= MPRIS_WIDTH) {
		if (mpris_scroll_px == 0)
			return 0;
		mpris_scroll_px = 0;
		return 1;
	}
	return 0;
}

/* Keep short MPRIS fields close to their content while retaining the fixed
 * maximum viewport for long titles.  The padding is part of the field, not
 * part of the scrolling text. */
static unsigned int mpris_field_width(const char *text) {
	unsigned int textw = TEXTW(text) - lrpad;
	unsigned int width = textw + 2 * MPRIS_SCROLL_PAD;

	return MIN(MPRIS_WIDTH, MAX(1U, width));
}

static int drag_next_event(XEvent *ev) {
	struct pollfd pfd[2] = {
		{ .fd = ConnectionNumber(dpy), .events = POLLIN },
		{ .fd = status_event_fd, .events = POLLIN }
	};
	int ready;
	int redraw;

	do {
		ready = poll(pfd, LENGTH(pfd), XPending(dpy) ? 0 : 1000 / DRAW_FPS);
	} while (ready < 0 && errno == EINTR);
	if (ready < 0)
		return 0;
	if (status_event_fd >= 0 && (pfd[1].revents & POLLIN))
		status_consume();
	updateclockbar();
	redraw = bar_dirty;
	bar_dirty = 0;
	if (update_mpris_scroll())
		redraw = 1;
	if (redraw)
		drawbars();
	if (!XPending(dpy) && !(pfd[0].revents & POLLIN))
		return 0;
	XNextEvent(dpy, ev);
	if (ev->type == MotionNotify)
		while (XCheckTypedEvent(dpy, MotionNotify, ev))
			;
	return 1;
}

#define hiddenWinStackMax 100
static int hiddenWinStackTop = -1;
static Client *hiddenWinStack[hiddenWinStackMax];

/* configuration, allows nested code to access above variables */
#include "config.h"

typedef struct Pertag Pertag;
struct Monitor {
  char ltsymbol[16];
  float mfact;
  int nmaster;
  int num;
  int by;             /* bar geometry */
  int ty;             /* tab bar geometry */
  int mx, my, mw, mh; /* screen size */
  int wx, wy, ww, wh; /* window area  */
  int gappih;         /* horizontal gap between windows */
  int gappiv;         /* vertical gap between windows */
  int gappoh;         /* horizontal outer gaps */
  int gappov;         /* vertical outer gaps */
  unsigned int borderpx;
  unsigned int seltags;
  unsigned int sellt;
  unsigned int tagset[2];
  unsigned int colorfultag;
  int showbar, showtab;
  int topbar, toptab;
  Client *clients;
  Client *sel;
  Client *stack;
  Monitor *next;
  Window barwin;
  Window bartitlewin;
  Window barcenterwin;
  Window barkbwin;
  Window barrightwin;
  Window tabwin;
  Window tagwin;
  Window sidebarwin;
  int sidebarvisible;
  int sidebarh;
  int sidebarw;
  Pixmap tagmap[LENGTH(tags)];
  int previewshow;
  int ntabs;
  int tab_widths[MAXTABS];
  int tab_btn_w[3];
  const Layout *lt[2];
  Pertag *pertag;
};

#include "movestack.c"
#include "shiftview.c"
#include "vanitygaps.c"

struct Pertag {
  unsigned int curtag, prevtag;          /* current and previous tag */
  int nmasters[LENGTH(tags) + 1];        /* number of windows in master area */
  float mfacts[LENGTH(tags) + 1];        /* mfacts per tag */
  unsigned int sellts[LENGTH(tags) + 1]; /* selected layouts */
  const Layout
      *ltidxs[LENGTH(tags) + 1][2]; /* matrix of tags and layouts indexes  */
  int showbars[LENGTH(tags) + 1];   /* display bar for the current tag */
};

/* compile-time check if all tags fit into an unsigned int bit array. */
struct NumTags {
  char limitexceeded[LENGTH(tags) > 31 ? -1 : 1];
};

/* function implementations */
void applyrules(Client *c) {
  const char *class, *instance;
  unsigned int i;
  const Rule *r;
  Monitor *m;
  XClassHint ch = {NULL, NULL};

  /* rule matching */
  c->iscentered = 0;
  c->isfloating = 0;
  c->isontop = 0;
  c->tags = 0;
  XGetClassHint(dpy, c->win, &ch);
  class = ch.res_class ? ch.res_class : broken;
  instance = ch.res_name ? ch.res_name : broken;

  for (i = 0; i < LENGTH(rules); i++) {
    r = &rules[i];
    if ((!r->title || strstr(c->name, r->title)) &&
        (!r->class || strstr(class, r->class)) &&
        (!r->instance || strstr(instance, r->instance))) {
      c->iscentered = r->iscentered;
      c->isfloating = r->isfloating;
      c->isontop = r->isontop;
      if (c->isontop)
        c->isfloating = 1;
      c->tags |= r->tags;
      for (m = mons; m && m->num != r->monitor; m = m->next)
        ;
      if (m)
        c->mon = m;
    }
  }
  if (ch.res_class)
    XFree(ch.res_class);
  if (ch.res_name)
    XFree(ch.res_name);
  c->tags =
      c->tags & TAGMASK ? c->tags & TAGMASK : c->mon->tagset[c->mon->seltags];
}

int applysizehints(Client *c, int *x, int *y, int *w, int *h, int interact) {
  int baseismin;
  Monitor *m = c->mon;

  if (c->issticky) {
    *w = MAX(1, *w);
    *h = MAX(1, *h);
    return 1;
  }

  /* set minimum possible */
  *w = MAX(1, *w);
  *h = MAX(1, *h);
  if (interact) {
    if (*x > sw)
      *x = sw - WIDTH(c);
    if (*y > sh)
      *y = sh - HEIGHT(c);
    if (*x + *w + 2 * c->bw < 0)
      *x = 0;
    if (*y + *h + 2 * c->bw < 0)
      *y = 0;
  } else {
    if (*x >= m->wx + m->ww)
      *x = m->wx + m->ww - WIDTH(c);
    if (*y >= m->wy + m->wh)
      *y = m->wy + m->wh - HEIGHT(c);
    if (*x + *w + 2 * c->bw <= m->wx)
      *x = m->wx;
    if (*y + *h + 2 * c->bw <= m->wy)
      *y = m->wy;
  }
  if (*h < bh)
    *h = bh;
  if (*w < bh)
    *w = bh;
  if (resizehints || c->isfloating || !c->mon->lt[c->mon->sellt]->arrange) {
    if (!c->hintsvalid)
      updatesizehints(c);
    /* see last two sentences in ICCCM 4.1.2.3 */
    baseismin = c->basew == c->minw && c->baseh == c->minh;
    if (!baseismin) { /* temporarily remove base dimensions */
      *w -= c->basew;
      *h -= c->baseh;
    }
    /* adjust for aspect limits */
    if (c->mina > 0 && c->maxa > 0) {
      if (c->maxa < (float)*w / *h)
        *w = *h * c->maxa + 0.5;
      else if (c->mina < (float)*h / *w)
        *h = *w * c->mina + 0.5;
    }
    if (baseismin) { /* increment calculation requires this */
      *w -= c->basew;
      *h -= c->baseh;
    }
    /* adjust for increment value */
    if (c->incw)
      *w -= *w % c->incw;
    if (c->inch)
      *h -= *h % c->inch;
    /* restore base dimensions */
    *w = MAX(*w + c->basew, c->minw);
    *h = MAX(*h + c->baseh, c->minh);
    if (c->maxw)
      *w = MIN(*w, c->maxw);
    if (c->maxh)
      *h = MIN(*h, c->maxh);
  }
  return *x != c->x || *y != c->y || *w != c->w || *h != c->h;
}

void arrange(Monitor *m) {
  if (m) {
    restorefullscreenhidden(m);
    showhide(m->stack);
  } else {
    for (m = mons; m; m = m->next) {
      restorefullscreenhidden(m);
      showhide(m->stack);
    }
  }
  if (m) {
    arrangemon(m);
    restack(m);
  }   else
    for (m = mons; m; m = m->next)
      arrangemon(m);
}

void arrangemon(Monitor *m) {
  updatebarpos(m);
  updatesystray();
  XMoveResizeWindow(dpy, m->tabwin, m->wx + m->gappov, m->ty,
                    m->ww - 2 * m->gappov, th);
  XMoveResizeWindow(dpy, m->tagwin, m->wx + m->gappov + tag_preview_x_offset,
                    m->by + (m->topbar ? (bh + m->gappoh + tag_preview_y_offset)
                                       : (-(m->mh / scalepreview) - m->gappoh - tag_preview_y_offset)),
                    m->mw / scalepreview, m->mh / scalepreview);
  strncpy(m->ltsymbol, m->lt[m->sellt]->symbol, sizeof(m->ltsymbol) - 1);
  m->ltsymbol[sizeof(m->ltsymbol) - 1] = '\0';
  if (m->lt[m->sellt]->arrange)
    m->lt[m->sellt]->arrange(m);
}

void attach(Client *c) {
  if (new_window_attach_on_end) {
    Client **tmp = &c->mon->clients;
    while (*tmp)
      tmp = &(*tmp)->next;
    *tmp = c;
  } else {
    c->next = c->mon->clients;
    c->mon->clients = c;
  }
}

void attachstack(Client *c) {
  c->snext = c->mon->stack;
  c->mon->stack = c;
}

void buttonpress(XEvent *e) {
  unsigned int i, x, click;
  int clientbinding;
  int loop;
  Arg arg = {0};
  Client *c;
  Monitor *m;
  XButtonPressedEvent *ev = &e->xbutton;

  click = ClkRootWin;
  /* focus monitor if necessary */
  if ((m = wintomon(ev->window)) && m != selmon) {
    unfocus(selmon->sel, 1);
    selmon = m;
    focus(NULL);
  }
  if (ev->window == selmon->barwin) {
    if (selmon->previewshow) {
      XUnmapWindow(dpy, selmon->tagwin);
      selmon->previewshow = 0;
    }
    i = x = 0;
    do
      x += TEXTW(tags[i]);
    while (ev->x >= x && ++i < LENGTH(tags));
    if (i < LENGTH(tags)) {
      click = ClkTagBar;
      arg.ui = 1 << i;
      goto execute_handler;
    } else if (ev->x < x + TEXTW(selmon->ltsymbol)) {
      click = ClkLtSymbol;
      goto execute_handler;
    }
    click = ClkWinTitle;
  } else if (ev->window == selmon->bartitlewin) {
    x = 0;
    for (i = 0; i < LENGTH(launchers); i++) {
      x += TEXTW(launchers[i].name);

      if (ev->x < x) {
        Arg a;
        a.v = launchers[i].command;
        spawn(&a);
        return;
      }
    }

    /* the remaining area of the title bar is the app icon + app name */
    click = ClkWinTitle;
  } else if (ev->window == selmon->barrightwin) {
    click = ClkStatusText;
  } else if (ev->window == selmon->barcenterwin) {
    /* While a notification is visible, the center window belongs entirely
     * to it.  Do not let clicks which miss a control fall through to the
     * normal root/bar bindings; those bindings may change focus or reload
     * the bar while an input notification is being edited. */
    if (notify_active) {
      notification_buttonpress(ev);
      return;
    }
    if (notify_history_active) {
      notification_history_buttonpress(ev);
      return;
    }
    click = ClkRootWin;
  } else if (ev->window == selmon->barkbwin) {
    click = ClkRootWin;
  }

  if (ev->window == selmon->tabwin) {
    i = 0;
    x = 0;
    for (c = selmon->clients; c; c = c->next) {
      if (!ISVISIBLE(c))
        continue;
      x += selmon->tab_widths[i];
      if (ev->x > x)
        ++i;
      else
        break;
      if (i >= m->ntabs)
        break;
    }
    if (c && ev->x <= x) {
      click = ClkTabBar;
      arg.ui = i;
    } else {
      x = selmon->ww - 2 * m->gappov;
      for (loop = 2; loop >= 0; loop--) {
        x -= selmon->tab_btn_w[loop];
        if (ev->x > x)
          break;
      }
      if (ev->x >= x)
        click = ClkTabPrev + loop;
    }
  } else if (enablesidebar && ev->window == selmon->sidebarwin) {
    /* sidebar click - find which app was clicked */
    int count = 0;
    Client *visible[MAXTABS];
    Client *clicked = NULL;
    for (c = selmon->clients; c; c = c->next) {
      if (ISVISIBLE(c) && count < MAXTABS) {
        visible[count++] = c;
      }
    }
    if (count > 0) {
      int itemh = selmon->mh / 3 / count;
      int clicked_idx = ev->y / itemh;
      if (clicked_idx >= 0 && clicked_idx < count) {
        clicked = visible[clicked_idx];
      }
    }
    if (clicked) {
      selmon = clicked->mon;
      focus(clicked);
    }
  } else if ((c = wintoclient(ev->window))) {
    click = ClkClientWin;
    clientbinding = 0;
    for (i = 0; i < LENGTH(buttons); i++)
      if (buttons[i].click == ClkClientWin &&
          buttons[i].button == ev->button &&
          CLEANMASK(buttons[i].mask) == CLEANMASK(ev->state)) {
        clientbinding = 1;
        break;
    }
    XAllowEvents(dpy, clientbinding ? AsyncPointer : ReplayPointer, CurrentTime);
    if (clientbinding) {
      selmon = c->mon;
      selmon->sel = c;
      goto execute_handler;
    }
    focus(c);
    restack(selmon);
  }

execute_handler:

  for (i = 0; i < LENGTH(buttons); i++)
    if (click == buttons[i].click && buttons[i].func &&
        buttons[i].button == ev->button &&
        CLEANMASK(buttons[i].mask) == CLEANMASK(ev->state))
      buttons[i].func(
          ((click == ClkTagBar || click == ClkTabBar) && buttons[i].arg.i == 0)
              ? &arg
              : &buttons[i].arg);
}

void checkotherwm(void) {
  xerrorxlib = XSetErrorHandler(xerrorstart);
  /* this causes an error if some other window manager is running */
  XSelectInput(dpy, DefaultRootWindow(dpy), SubstructureRedirectMask);
  XSync(dpy, False);
  XSetErrorHandler(xerror);
  XSync(dpy, False);
}

void cleanup(void) {
  Arg a = {.ui = ~0};
  Layout foo = {"", NULL};
  Monitor *m;
  size_t i;

  status_stop();
  if (CLOCK_ANIMATE)
    sound_monitor_stop();
  notification_shutdown();

  view(&a);
  selmon->lt[selmon->sellt] = &foo;
  for (m = mons; m; m = m->next)
    while (m->stack)
      unmanage(m->stack, 0);
  XUngrabKey(dpy, AnyKey, AnyModifier, root);
  while (mons)
    cleanupmon(mons);
  if (showsystray) {
    XUnmapWindow(dpy, systray->win);
    XDestroyWindow(dpy, systray->win);
    free(systray);
  }
  for (i = 0; i < CurLast; i++)
    drw_cur_free(drw, cursor[i]);
  for (i = 0; i < LENGTH(colors) + 1; i++)
    free(scheme[i]);
  free(scheme);
  XDestroyWindow(dpy, wmcheckwin);
  drw_free(drw);
  XFlush(dpy);
  XSetInputFocus(dpy, PointerRoot, RevertToPointerRoot, CurrentTime);
  XDeleteProperty(dpy, root, netatom[NetActiveWindow]);
}

void cleanupmon(Monitor *mon) {
  Monitor *m;
  size_t i;

  if (mon == mons)
    mons = mons->next;
  else {
    for (m = mons; m && m->next != mon; m = m->next)
      ;
    m->next = mon->next;
  }
  for (i = 0; i < LENGTH(tags); i++) {
    if (mon->tagmap[i])
      XFreePixmap(dpy, mon->tagmap[i]);
  }
  XUnmapWindow(dpy, mon->barwin);
  XDestroyWindow(dpy, mon->barwin);
  XUnmapWindow(dpy, mon->bartitlewin);
  XDestroyWindow(dpy, mon->bartitlewin);
  XUnmapWindow(dpy, mon->barcenterwin);
  XDestroyWindow(dpy, mon->barcenterwin);
  XUnmapWindow(dpy, mon->barkbwin);
  XDestroyWindow(dpy, mon->barkbwin);
  XUnmapWindow(dpy, mon->barrightwin);
  XDestroyWindow(dpy, mon->barrightwin);
  XUnmapWindow(dpy, mon->tabwin);
  XDestroyWindow(dpy, mon->tabwin);
  XUnmapWindow(dpy, mon->tagwin);
  XDestroyWindow(dpy, mon->tagwin);
  XUnmapWindow(dpy, mon->sidebarwin);
  XDestroyWindow(dpy, mon->sidebarwin);
  free(mon);
}

void clientmessage(XEvent *e) {
  XWindowAttributes wa;
  XSetWindowAttributes swa;
  XClientMessageEvent *cme = &e->xclient;
  Client *c = wintoclient(cme->window);

  if (showsystray && cme->window == systray->win &&
      cme->message_type == netatom[NetSystemTrayOP]) {
    /* add systray icons */
    if (cme->data.l[1] == SYSTEM_TRAY_REQUEST_DOCK) {
      if (!(c = (Client *)calloc(1, sizeof(Client))))
        die("fatal: could not malloc() %u bytes\n", sizeof(Client));
      if (!(c->win = cme->data.l[2])) {
        free(c);
        return;
      }
      c->mon = selmon;
      c->next = systray->icons;
      systray->icons = c;
      if (!XGetWindowAttributes(dpy, c->win, &wa)) {
        /* use sane defaults */
        wa.width = bh;
        wa.height = bh;
        wa.border_width = 0;
      }
      c->x = c->oldx = c->y = c->oldy = 0;
      c->w = c->oldw = wa.width;
      c->h = c->oldh = wa.height;
      c->oldbw = wa.border_width;
      c->bw = 0;
      c->isfloating = True;
      /* reuse tags field as mapped status */
      c->tags = 1;
      updatesizehints(c);
      updatesystrayicongeom(c, wa.width, wa.height);
      XAddToSaveSet(dpy, c->win);
      XSelectInput(dpy, c->win,
                   StructureNotifyMask | PropertyChangeMask |
                       ResizeRedirectMask);
      XClassHint ch = {"dwmsystray", "dwmsystray"};
      XSetClassHint(dpy, c->win, &ch);
      XReparentWindow(dpy, c->win, systray->win, 0, 0);
      /* use parents background color */
      swa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
      XChangeWindowAttributes(dpy, c->win, CWBackPixel, &swa);
      sendevent(c->win, netatom[Xembed], StructureNotifyMask, CurrentTime,
                XEMBED_EMBEDDED_NOTIFY, 0, systray->win,
                XEMBED_EMBEDDED_VERSION);
      /* FIXME not sure if I have to send these events, too */
      sendevent(c->win, netatom[Xembed], StructureNotifyMask, CurrentTime,
                XEMBED_FOCUS_IN, 0, systray->win, XEMBED_EMBEDDED_VERSION);
      sendevent(c->win, netatom[Xembed], StructureNotifyMask, CurrentTime,
                XEMBED_WINDOW_ACTIVATE, 0, systray->win,
                XEMBED_EMBEDDED_VERSION);
      sendevent(c->win, netatom[Xembed], StructureNotifyMask, CurrentTime,
                XEMBED_MODALITY_ON, 0, systray->win, XEMBED_EMBEDDED_VERSION);
       XFlush(dpy);
      resizebarwin(selmon);
      updatesystray();
      setclientstate(c, NormalState);
    }
    return;
  }
  if (cme->message_type == netatom[NetCurrentDesktop]) {
    if (cme->data.l[0] >= 0 && (unsigned long)cme->data.l[0] < LENGTH(tags)) {
      Arg a = {.ui = 1 << cme->data.l[0]};
      view(&a);
    }
    return;
  }
  if (!c)
    return;
  if (cme->message_type == netatom[NetWMState]) {
    if (cme->data.l[1] == netatom[NetWMFullscreen] ||
        cme->data.l[2] == netatom[NetWMFullscreen])
      setfullscreen(c, (cme->data.l[0] == 1 /* _NET_WM_STATE_ADD    */
                        || (cme->data.l[0] == 2 /* _NET_WM_STATE_TOGGLE */ &&
                            !c->isfullscreen)));
  } else if (cme->message_type == netatom[NetActiveWindow]) {
    if (c != selmon->sel && !c->isurgent)
      seturgent(c, 1);
  }
}

void configure(Client *c) {
  XConfigureEvent ce;

  ce.type = ConfigureNotify;
  ce.display = dpy;
  ce.event = c->win;
  ce.window = c->win;
  ce.x = c->x;
  ce.y = c->y;
  ce.width = c->w;
  ce.height = c->h;
  ce.border_width = c->bw;
  ce.above = None;
  ce.override_redirect = False;
  XSendEvent(dpy, c->win, False, StructureNotifyMask, (XEvent *)&ce);
}

void configurenotify(XEvent *e) {
  Monitor *m;
  Client *c;
  XConfigureEvent *ev = &e->xconfigure;
  int dirty;

  /* TODO: updategeom handling sucks, needs to be simplified */
  if (ev->window == root) {
    dirty = (sw != ev->width || sh != ev->height);
    sw = ev->width;
    sh = ev->height;
    if (updategeom() || dirty) {
      drw_resize(drw, sw, sh);
      updatebars();
      for (m = mons; m; m = m->next) {
        for (c = m->clients; c; c = c->next)
          if (c->isfullscreen)
            resizeclient(c, m->mx, m->my, m->mw, m->mh);
        resizebarwin(m);
      }
      for (m = mons; m; m = m->next)
        if (m->sidebarvisible)
          drawsidebar(m);
      focus(NULL);
      arrange(NULL);
    }
  }
}

void configurerequest(XEvent *e) {
  Client *c;
  Monitor *m;
  XConfigureRequestEvent *ev = &e->xconfigurerequest;
  XWindowChanges wc;

  if ((c = wintoclient(ev->window))) {
    if (ev->value_mask & CWBorderWidth)
      c->bw = ev->border_width;
    else if (c->isfloating || !selmon->lt[selmon->sellt]->arrange) {
      m = c->mon;
      if (ev->value_mask & CWX) {
        c->oldx = c->x;
        c->x = m->mx + ev->x;
      }
      if (ev->value_mask & CWY) {
        c->oldy = c->y;
        c->y = m->my + ev->y;
      }
      if (ev->value_mask & CWWidth) {
        c->oldw = c->w;
        c->w = ev->width;
      }
      if (ev->value_mask & CWHeight) {
        c->oldh = c->h;
        c->h = ev->height;
      }
      if ((c->x + c->w) > m->mx + m->mw && c->isfloating)
        c->x = m->mx + (m->mw / 2 - WIDTH(c) / 2); /* center in x direction */
      if ((c->y + c->h) > m->my + m->mh && c->isfloating)
        c->y = m->my + (m->mh / 2 - HEIGHT(c) / 2); /* center in y direction */
      if ((ev->value_mask & (CWX | CWY)) &&
          !(ev->value_mask & (CWWidth | CWHeight)))
        configure(c);
      if (ISVISIBLE(c))
        XMoveResizeWindow(dpy, c->win, c->x, c->y, c->w, c->h);
    } else
      configure(c);
  } else {
    wc.x = ev->x;
    wc.y = ev->y;
    wc.width = ev->width;
    wc.height = ev->height;
    wc.border_width = ev->border_width;
    wc.sibling = ev->above;
    wc.stack_mode = ev->detail;
    XConfigureWindow(dpy, ev->window, ev->value_mask, &wc);
  }
  XFlush(dpy);
}

Monitor *createmon(void) {
  Monitor *m;
  size_t i;

  m = ecalloc(1, sizeof(Monitor));
  m->tagset[0] = m->tagset[1] = 1;
  m->mfact = mfact;
  m->nmaster = nmaster;
  m->showbar = showbar;
  m->showtab = showtab;
  m->topbar = topbar;
  m->toptab = toptab;
  m->ntabs = 0;
  m->colorfultag = colorfultag ? colorfultag : 0;
  m->gappih = gappih;
  m->gappiv = gappiv;
  m->gappoh = gappoh;
  m->gappov = gappov;
  m->borderpx = borderpx;
  m->lt[0] = &layouts[0];
  m->lt[1] = &layouts[1 % LENGTH(layouts)];
  for (i = 0; i < LENGTH(tags); i++)
    m->tagmap[i] = 0;
  m->previewshow = 0;
  m->sidebarw = SIDEBAR_WIDTH;
  m->sidebarh = 1;
  strncpy(m->ltsymbol, layouts[0].symbol, sizeof m->ltsymbol);
  m->pertag = ecalloc(1, sizeof(Pertag));
  m->pertag->curtag = m->pertag->prevtag = 1;

  for (i = 0; i <= LENGTH(tags); i++) {
    m->pertag->nmasters[i] = m->nmaster;
    m->pertag->mfacts[i] = m->mfact;

    m->pertag->ltidxs[i][0] = m->lt[0];
    m->pertag->ltidxs[i][1] = m->lt[1];
    m->pertag->sellts[i] = m->sellt;

    m->pertag->showbars[i] = m->showbar;
  }

  return m;
}

void cyclelayout(const Arg *arg) {
  Layout *l;
  for (l = (Layout *)layouts; l != selmon->lt[selmon->sellt]; l++)
    ;
  if (arg->i > 0) {
    if (l->symbol && (l + 1)->symbol)
      setlayout(&((Arg){.v = (l + 1)}));
    else
      setlayout(&((Arg){.v = layouts}));
  } else {
    if (l != layouts && (l - 1)->symbol)
      setlayout(&((Arg){.v = (l - 1)}));
    else
      setlayout(&((Arg){.v = &layouts[LENGTH(layouts) - 2]}));
  }
}

void destroynotify(XEvent *e) {
  Client *c;
  XDestroyWindowEvent *ev = &e->xdestroywindow;

  if ((c = wintoclient(ev->window)))
    unmanage(c, 1);
  else if ((c = wintosystrayicon(ev->window))) {
    removesystrayicon(c);
    resizebarwin(selmon);
    updatesystray();
  }
}

void detach(Client *c) {
  Client **tc;


  for (tc = &c->mon->clients; *tc && *tc != c; tc = &(*tc)->next)
    ;
  *tc = c->next;

}

void detachstack(Client *c) {
  Client **tc, *t;


  for (tc = &c->mon->stack; *tc && *tc != c; tc = &(*tc)->snext)
    ;
  *tc = c->snext;

  if (c == c->mon->sel) {
    for (t = c->mon->stack; t && !ISVISIBLE(t); t = t->snext)
      ;
    c->mon->sel = t;
  }

}

Monitor *dirtomon(int dir) {
  Monitor *m = NULL;

  if (dir > 0) {
    if (!(m = selmon->next))
      m = mons;
  } else if (selmon == mons)
    for (m = mons; m->next; m = m->next)
      ;
  else
    for (m = mons; m->next != selmon; m = m->next)
      ;
  return m;
}

unsigned int statuswidth(char *stext) {
  int i, w;
  short isCode = 0;
  char *text;
  char *p;
  short isScroll = 0;
  size_t len = strlen(stext) + 1;

  if (!(text = (char *)malloc(sizeof(char) * len)))
    die("malloc");
  p = text;
  memcpy(text, stext, len);

  /* compute width of the status text */
  w = 0;
  i = -1;
  while (text[++i]) {
    if (text[i] == '^') {
      if (!isCode) {
        isCode = 1;
        text[i] = '\0';
			w += isScroll ? mpris_field_width(text) : TEXTW(text) - lrpad;
        text[i] = '^';
        if (text[++i] == 'm')
          isScroll = 1;
        else if (text[i] == 'M')
          isScroll = 0;
        else if (text[i] == 'f')
          w += atoi(text + ++i);
      } else {
        isCode = 0;
        text = text + i + 1;
        i = -1;
      }
    }
  }
  if (!isCode)
		w += isScroll ? mpris_field_width(text) : TEXTW(text) - lrpad;
  else
    isCode = 0;
  free(p);

  return w + horizpadbar;
}

int drawstatusbar(Monitor *m, int bh, char *stext) {
  int i, w, x, len;
  short isCode = 0;
  short isScroll = 0;
  char *text;
  char *p;

  len = strlen(stext) + 1;
  if (!(text = (char *)malloc(sizeof(char) * len)))
    die("malloc");
  p = text;
  memcpy(text, stext, len);

  w = statuswidth(stext);
  x = horizpadbar / 2;

  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, w, bh);

  drw_setscheme(drw, scheme[LENGTH(colors)]);
  drw->scheme[ColFg] = scheme[SchemeNorm][ColFg];
  drw->scheme[ColBg] = scheme[SchemeNorm][ColBg];
  drw_rect(drw, 0, borderpx, w, bh, 1, 1);

  /* process status text */
  i = -1;
  while (text[++i]) {
    if (text[i] == '^' && !isCode) {
      isCode = 1;

      text[i] = '\0';
       w = isScroll ? mpris_field_width(text) : TEXTW(text) - lrpad;
        if (isScroll) {
          double progress = mpris_progress;
          unsigned int progressw = 0;
          if (progress >= 0.0) {
            if (progress > 1.0) progress = 1.0;
            if (progress >= MPRIS_COMPLETE_THRESHOLD) progress = 1.0;
            progressw = (unsigned int)(progress * w + 0.5);
          }
          mpris_scroll_text_width = drw_text_scroll_progress(
              drw, x, borderpx + vertpadbar / 2, w,
              bh - vertpadbar, MPRIS_SCROLL_PAD, text, mpris_scroll_px,
              MPRIS_SCROLL_GAP, 0, &mpris_scroll_bg_clr,
              progress >= 0.0 ? &mpris_progress_clr : NULL,
              progressw);
        }
       else
         drw_text(drw, x, borderpx + vertpadbar / 2, w, bh - vertpadbar, 0, text,
                  0);

      x += w;

      /* process code */
      while (text[++i] != '^') {
        if (text[i] == 'c') {
          char buf[8];
          memcpy(buf, (char *)text + i + 1, 7);
          buf[7] = '\0';
          drw_clr_create(drw, &drw->scheme[ColFg], buf);
          i += 7;
        } else if (text[i] == 'b') {
          char buf[8];
          memcpy(buf, (char *)text + i + 1, 7);
          buf[7] = '\0';
          drw_clr_create(drw, &drw->scheme[ColBg], buf);
          i += 7;
        } else if (text[i] == 'd') {
          drw->scheme[ColFg] = scheme[SchemeNorm][ColFg];
          drw->scheme[ColBg] = scheme[SchemeNorm][ColBg];
        } else if (text[i] == 'r') {
          int rx = atoi(text + ++i);
          while (text[++i] != ',')
            ;
          int ry = atoi(text + ++i);
          while (text[++i] != ',')
            ;
          int rw = atoi(text + ++i);
          while (text[++i] != ',')
            ;
          int rh = atoi(text + ++i);

          drw_rect(drw, rx + x, ry + borderpx + vertpadbar / 2, rw, rh, 1, 0);
        } else if (text[i] == 'f') {
          x += atoi(text + ++i);
        } else if (text[i] == 'm') {
          isScroll = 1;
        } else if (text[i] == 'M') {
          isScroll = 0;
        }
      }

      text = text + i + 1;
      i = -1;
      isCode = 0;
    }
  }

  if (!isCode) {
    w = isScroll ? mpris_field_width(text) : TEXTW(text) - lrpad;
    if (isScroll) {
      double progress = mpris_progress;
      unsigned int progressw = 0;
      if (progress >= 0.0) {
        if (progress > 1.0) progress = 1.0;
        if (progress >= MPRIS_COMPLETE_THRESHOLD) progress = 1.0;
        progressw = (unsigned int)(progress * w + 0.5);
      }
      mpris_scroll_text_width = drw_text_scroll_progress(
          drw, x, borderpx + vertpadbar / 2, w,
          bh - vertpadbar, MPRIS_SCROLL_PAD, text, mpris_scroll_px,
          MPRIS_SCROLL_GAP, 0, &mpris_scroll_bg_clr,
          progress >= 0.0 ? &mpris_progress_clr : NULL,
          progressw);
    }
    else
      drw_text(drw, x, borderpx + vertpadbar / 2, w, bh - vertpadbar, 0, text, 0);
  }

  drw_setscheme(drw, scheme[SchemeNorm]);
  free(p);

  return statuswidth(stext);
}

void dragcfact(const Arg *arg) {
  int prev_x, prev_y, dist_x, dist_y;
  float fact;
  Client *c;
  XEvent ev;
  Time lasttime = 0;

  if (!(c = selmon->sel))
    return;
  if (c->isfloating) {
    resizemouse(arg);
    return;
  }
#if !FAKEFULLSCREEN_PATCH
#if FAKEFULLSCREEN_CLIENT_PATCH
  if (c->isfullscreen &&
      !c->fakefullscreen) /* no support resizing fullscreen windows by mouse */
    return;
#else
  if (c->isfullscreen) /* no support resizing fullscreen windows by mouse */
    return;
#endif // FAKEFULLSCREEN_CLIENT_PATCH
#endif // !FAKEFULLSCREEN_PATCH
  restack(selmon);

  if (XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
                   None, cursor[CurResize]->cursor, CurrentTime) != GrabSuccess)
    return;
  XFlush(dpy);
  setworkspaceanimation(selmon, 1);
  int prev_animate = animate_tiled;
  /* disable animated tiled resize while dragging to use instant resizeclient */
  animate_tiled = 0;
  prev_x = prev_y = -999999;

  do {
    XMaskEvent(dpy, MOUSEMASK | ExposureMask | SubstructureRedirectMask, &ev);
    switch (ev.type) {
    case ConfigureRequest:
    case Expose:
    case MapRequest:
      handler[ev.type](&ev);
      break;
    case MotionNotify:
      if ((ev.xmotion.time - lasttime) <= (1000 / 120))
        continue;
      lasttime = ev.xmotion.time;
      if (prev_x == -999999) {
        prev_x = ev.xmotion.x_root;
        prev_y = ev.xmotion.y_root;
      }

      dist_x = ev.xmotion.x - prev_x;
      dist_y = ev.xmotion.y - prev_y;

      if (abs(dist_x) > abs(dist_y)) {
        fact = (float)4.0 * dist_x / c->mon->ww;
      } else {
        fact = (float)-4.0 * dist_y / c->mon->wh;
      }

      if (fact)
        setcfact(&((Arg){.f = fact}));

      prev_x = ev.xmotion.x;
      prev_y = ev.xmotion.y;
      break;
    }
  } while (ev.type != ButtonRelease);

  XUngrabPointer(dpy, CurrentTime);
  setworkspaceanimation(selmon, 0);
  animate_tiled = prev_animate;
  while (XCheckMaskEvent(dpy, EnterWindowMask, &ev))
    ;
}

void dragmfact(const Arg *arg) {
  unsigned int n;
  int py, px;         // pointer coordinates
  int ax, ay, aw, ah; // area position, width and height
  int center = 0, horizontal = 0, mirror = 0, fixed = 0; // layout configuration
  double fact;
  Monitor *m;
  XEvent ev;
  Time lasttime = 0;

  m = selmon;

#if VANITYGAPS_PATCH
  int oh, ov, ih, iv;
  getgaps(m, &oh, &ov, &ih, &iv, &n);
#else
  Client *c;
  for (n = 0, c = nexttiled(m->clients); c; c = nexttiled(c->next), n++)
    ;
#endif // VANITYGAPS_PATCH

  ax = m->wx;
  ay = m->wy;
  ah = m->wh;
  aw = m->ww;

  if (!n)
    return;
#if FLEXTILE_DELUXE_LAYOUT
  else if (m->lt[m->sellt]->arrange == &flextile) {
    int layout = m->ltaxis[LAYOUT];
    if (layout < 0) {
      mirror = 1;
      layout *= -1;
    }
    if (layout > FLOATING_MASTER) {
      layout -= FLOATING_MASTER;
      fixed = 1;
    }

    if (layout == SPLIT_HORIZONTAL || layout == SPLIT_HORIZONTAL_DUAL_STACK)
      horizontal = 1;
    else if (layout == SPLIT_CENTERED_VERTICAL && (fixed || n - m->nmaster > 1))
      center = 1;
    else if (layout == FLOATING_MASTER) {
      center = 1;
      if (aw < ah)
        horizontal = 1;
    } else if (layout == SPLIT_CENTERED_HORIZONTAL) {
      if (fixed || n - m->nmaster > 1)
        center = 1;
      horizontal = 1;
    }
  }
#endif // FLEXTILE_DELUXE_LAYOUT
#if CENTEREDMASTER_LAYOUT
  else if (m->lt[m->sellt]->arrange == &centeredmaster &&
           (fixed || n - m->nmaster > 1))
    center = 1;
#endif // CENTEREDMASTER_LAYOUT
#if CENTEREDFLOATINGMASTER_LAYOUT
  else if (m->lt[m->sellt]->arrange == &centeredfloatingmaster)
    center = 1;
#endif // CENTEREDFLOATINGMASTER_LAYOUT
#if BSTACK_LAYOUT
  else if (m->lt[m->sellt]->arrange == &bstack)
    horizontal = 1;
#endif // BSTACK_LAYOUT
#if BSTACKHORIZ_LAYOUT
  else if (m->lt[m->sellt]->arrange == &bstackhoriz)
    horizontal = 1;
#endif // BSTACKHORIZ_LAYOUT

  /* do not allow mfact to be modified under certain conditions */
  if (!m->lt[m->sellt]->arrange                    // floating layout
      || (!fixed && m->nmaster && n <= m->nmaster) // no master
#if MONOCLE_LAYOUT
      || m->lt[m->sellt]->arrange == &monocle
#endif // MONOCLE_LAYOUT
#if GRIDMODE_LAYOUT
      || m->lt[m->sellt]->arrange == &grid
#endif // GRIDMODE_LAYOUT
#if HORIZGRID_LAYOUT
      || m->lt[m->sellt]->arrange == &horizgrid
#endif // HORIZGRID_LAYOUT
#if GAPPLESSGRID_LAYOUT
      || m->lt[m->sellt]->arrange == &gaplessgrid
#endif // GAPPLESSGRID_LAYOUT
#if NROWGRID_LAYOUT
      || m->lt[m->sellt]->arrange == &nrowgrid
#endif // NROWGRID_LAYOUT
#if FLEXTILE_DELUXE_LAYOUT
      ||
      (m->lt[m->sellt]->arrange == &flextile && m->ltaxis[LAYOUT] == NO_SPLIT)
#endif // FLEXTILE_DELUXE_LAYOUT
  )
    return;

#if VANITYGAPS_PATCH
  ay += oh;
  ax += ov;
  aw -= 2 * ov;
  ah -= 2 * oh;
#endif // VANITYGAPS_PATCH

  if (center) {
    if (horizontal) {
      px = ax + aw / 2;
#if VANITYGAPS_PATCH
      py = ay + ah / 2 + (ah - 2 * ih) * (m->mfact / 2.0) + ih / 2;
#else
      py = ay + ah / 2 + ah * m->mfact / 2.0;
#endif       // VANITYGAPS_PATCH
    } else { // vertical split
#if VANITYGAPS_PATCH
      px = ax + aw / 2 + (aw - 2 * iv) * m->mfact / 2.0 + iv / 2;
#else
      px = ax + aw / 2 + aw * m->mfact / 2.0;
#endif // VANITYGAPS_PATCH
      py = ay + ah / 2;
    }
  } else if (horizontal) {
    px = ax + aw / 2;
    if (mirror)
#if VANITYGAPS_PATCH
      py = ay + (ah - ih) * (1.0 - m->mfact) + ih / 2;
#else
      py = ay + (ah * (1.0 - m->mfact));
#endif // VANITYGAPS_PATCH
    else
#if VANITYGAPS_PATCH
      py = ay + ((ah - ih) * m->mfact) + ih / 2;
#else
      py = ay + (ah * m->mfact);
#endif     // VANITYGAPS_PATCH
  } else { // vertical split
    if (mirror)
#if VANITYGAPS_PATCH
      px = ax + (aw - iv) * (1.0 - m->mfact) + iv / 2;
#else
      px = ax + (aw * m->mfact);
#endif // VANITYGAPS_PATCH
    else
#if VANITYGAPS_PATCH
      px = ax + ((aw - iv) * m->mfact) + iv / 2;
#else
      px = ax + (aw * m->mfact);
#endif // VANITYGAPS_PATCH
    py = ay + ah / 2;
  }

  if (XGrabPointer(
          dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync, None,
          cursor[horizontal ? CurResizeVertArrow : CurResizeHorzArrow]->cursor,
          CurrentTime) != GrabSuccess)
    return;
  XFlush(dpy);
  if (m->sel)
    setworkspaceanimation(m, 1);

  int prev_animate = animate_tiled;
  /* disable animated tiled resize while dragging to use instant resizeclient */
  animate_tiled = 0;

  do {
    XMaskEvent(dpy, MOUSEMASK | ExposureMask | SubstructureRedirectMask, &ev);
    switch (ev.type) {
    case ConfigureRequest:
    case Expose:
    case MapRequest:
      handler[ev.type](&ev);
      break;
    case MotionNotify:
      if ((ev.xmotion.time - lasttime) <= (1000 / 40))
        continue;
      if (lasttime != 0) {
        px = ev.xmotion.x;
        py = ev.xmotion.y;
      }
      lasttime = ev.xmotion.time;

#if VANITYGAPS_PATCH
      if (center)
        if (horizontal)
          if (py - ay > ah / 2)
            fact = (double)1.0 -
                   (ay + ah - py - ih / 2) * 2 / (double)(ah - 2 * ih);
          else
            fact = (double)1.0 - (py - ay - ih / 2) * 2 / (double)(ah - 2 * ih);
        else if (px - ax > aw / 2)
          fact =
              (double)1.0 - (ax + aw - px - iv / 2) * 2 / (double)(aw - 2 * iv);
        else
          fact = (double)1.0 - (px - ax - iv / 2) * 2 / (double)(aw - 2 * iv);
      else if (horizontal)
        fact = (double)(py - ay - ih / 2) / (double)(ah - ih);
      else
        fact = (double)(px - ax - iv / 2) / (double)(aw - iv);
#else
      if (center)
        if (horizontal)
          if (py - ay > ah / 2)
            fact = (double)1.0 - (ay + ah - py) * 2 / (double)ah;
          else
            fact = (double)1.0 - (py - ay) * 2 / (double)ah;
        else if (px - ax > aw / 2)
          fact = (double)1.0 - (ax + aw - px) * 2 / (double)aw;
        else
          fact = (double)1.0 - (px - ax) * 2 / (double)aw;
      else if (horizontal)
        fact = (double)(py - ay) / (double)ah;
      else
        fact = (double)(px - ax) / (double)aw;
#endif // VANITYGAPS_PATCH

      if (!center && mirror)
        fact = 1.0 - fact;

      setmfact(&((Arg){.f = 1.0 + fact}));
      px = ev.xmotion.x;
      py = ev.xmotion.y;
      break;
    }
  } while (ev.type != ButtonRelease);

  XUngrabPointer(dpy, CurrentTime);
  if (m->sel)
    setworkspaceanimation(m, 0);
  animate_tiled = prev_animate;
  while (XCheckMaskEvent(dpy, EnterWindowMask, &ev))
    ;
}

static unsigned int tagsbarwidth(Monitor *m) {
  unsigned int i, w = 0;
  for (i = 0; i < LENGTH(tags); i++)
    w += TEXTW(tags[i]);
  return borderpx + w + TEXTW(m->ltsymbol);
}

static unsigned int bartitlewidth(Monitor *m, unsigned int budget) {
  unsigned int i, w = 0;
  for (i = 0; i < LENGTH(launchers); i++)
    w += TEXTW(launchers[i].name);
  if (m->sel) {
    w += m->sel->icon ? m->sel->icw + ICONSPACING : 0;
    w += drw_fontset_getwidth(drw, m->sel->name) + lrpad;
  }
  return MIN(w, budget);
}

unsigned int clockwidth(void) {
  return TEXTW(clockstr) - lrpad + 2 * clockpad;
}

static char *notify_strdup(const char *s) {
  return s ? strdup(s) : strdup("");
}

static void notification_free(Notification *n) {
  unsigned int i;
  if (!n)
    return;
  free(n->app_name);
  free(n->summary);
  free(n->body);
  free(n->icon);
  for (i = 0; i < n->action_count; i++)
    free(n->actions[i]);
  free(n->actions);
  free(n->input_action);
  free(n->input_placeholder);
  free(n->input_text);
  if (n->image)
    XRenderFreePicture(dpy, n->image);
  free(n);
}

static void notification_free_contents(Notification *n) {
  unsigned int i;
  if (!n)
    return;
  free(n->app_name);
  free(n->summary);
  free(n->body);
  free(n->icon);
  for (i = 0; i < n->action_count; i++)
    free(n->actions[i]);
  free(n->actions);
  free(n->input_action);
  free(n->input_placeholder);
  free(n->input_text);
  if (n->image)
    XRenderFreePicture(dpy, n->image);
  n->app_name = n->summary = n->body = n->icon = NULL;
  n->actions = NULL;
  n->action_count = 0;
  n->input_action = n->input_placeholder = n->input_text = NULL;
  n->input_enabled = 0;
  n->image = 0;
  n->image_w = n->image_h = 0;
  n->image_hint = 0;
}

static void notification_history_clear_controls(Notification *n) {
  unsigned int i;

  if (!n)
    return;
  for (i = 0; i < n->action_count; i++)
    free(n->actions[i]);
  free(n->actions);
  free(n->input_action);
  free(n->input_placeholder);
  free(n->input_text);
  n->actions = NULL;
  n->action_count = 0;
  n->input_action = n->input_placeholder = n->input_text = NULL;
  n->input_enabled = 0;
}

static int notification_center_active(void) {
  return notify_active || notify_history_active;
}

/* The audio visualizer may make barcenterwin wider than the clock.  Only the
 * fixed clock-sized portion should act as the history hover target while the
 * center is in its normal clock state. */
static int notification_clock_hit(int x, unsigned int width) {
  unsigned int hover_width = clockbar_cw;
  int left;

  if (!hover_width || hover_width >= width)
    return 1;
  left = ((int)width - (int)hover_width) / 2;
  return x >= left && x < left + (int)hover_width;
}

static void notification_history_add(Notification *n) {
  Notification *old;

  if (!n)
    return;
  n->next = NULL;
  if (notify_history_tail)
    notify_history_tail->next = n;
  else
    notify_history_head = n;
  notify_history_tail = n;
  notify_history_count++;
  while (notify_history_count > NOTIFY_HISTORY_MAX) {
    old = notify_history_head;
    notify_history_head = old->next;
    old->next = NULL;
    notification_free(old);
    notify_history_count--;
  }
}

static void notification_fit_size(unsigned int srcw, unsigned int srch,
                                  unsigned int maxw, unsigned int maxh,
                                  unsigned int *dstw, unsigned int *dsth) {
  unsigned int w = srcw, h = srch;
  if (!srcw || !srch) {
    *dstw = *dsth = 1;
    return;
  }
  if (w > maxw) {
    w = maxw;
    h = MAX(1U, (unsigned int)((uint64_t)srch * w / srcw));
  }
  if (h > maxh) {
    h = maxh;
    w = MAX(1U, (unsigned int)((uint64_t)srcw * h / srch));
  }
  *dstw = w;
  *dsth = h;
}

static Picture notification_round_picture(Picture source, unsigned int w,
                                           unsigned int h) {
  Pixmap mask_pm, picture_pm;
  Picture mask, rounded;
  GC mask_gc;
  XRenderPictFormat *argb_format, *a8_format;
  unsigned int radius = NOTIFY_IMAGE_RADIUS;

  if (!source || !w || !h)
    return source;
  /* Keep the corner radius fixed instead of scaling it with the image
   * dimensions.  Tiny images cannot contain a 12 px radius cleanly. */
  if (w < 2 * radius || h < 2 * radius)
    return source;

  a8_format = XRenderFindStandardFormat(dpy, PictStandardA8);
  argb_format = XRenderFindStandardFormat(dpy, PictStandardARGB32);
  if (!a8_format || !argb_format)
    return source;

  mask_pm = XCreatePixmap(dpy, drw->drawable, w, h, 8);
  picture_pm = XCreatePixmap(dpy, drw->drawable, w, h, 32);
  if (!mask_pm || !picture_pm) {
    if (mask_pm)
      XFreePixmap(dpy, mask_pm);
    if (picture_pm)
      XFreePixmap(dpy, picture_pm);
    return source;
  }

  mask_gc = XCreateGC(dpy, mask_pm, 0, NULL);
  if (!mask_gc) {
    XFreePixmap(dpy, mask_pm);
    XFreePixmap(dpy, picture_pm);
    return source;
  }
  XSetForeground(dpy, mask_gc, 0);
  XFillRectangle(dpy, mask_pm, mask_gc, 0, 0, w, h);
  XSetForeground(dpy, mask_gc, 255);
  XFillRectangle(dpy, mask_pm, mask_gc, radius, 0, w - 2 * radius, h);
  XFillRectangle(dpy, mask_pm, mask_gc, 0, radius, w, h - 2 * radius);
  XFillArc(dpy, mask_pm, mask_gc, 0, 0, 2 * radius, 2 * radius, 90 * 64,
           90 * 64);
  XFillArc(dpy, mask_pm, mask_gc, w - 2 * radius, 0, 2 * radius,
           2 * radius, 0, 90 * 64);
  XFillArc(dpy, mask_pm, mask_gc, 0, h - 2 * radius, 2 * radius,
           2 * radius, 180 * 64, 90 * 64);
  XFillArc(dpy, mask_pm, mask_gc, w - 2 * radius, h - 2 * radius,
           2 * radius, 2 * radius, 270 * 64, 90 * 64);
  XFreeGC(dpy, mask_gc);

  mask = XRenderCreatePicture(dpy, mask_pm, a8_format, 0, NULL);
  rounded = XRenderCreatePicture(dpy, picture_pm, argb_format, 0, NULL);
  if (!mask || !rounded) {
    if (mask)
      XRenderFreePicture(dpy, mask);
    if (rounded)
      XRenderFreePicture(dpy, rounded);
    XFreePixmap(dpy, mask_pm);
    XFreePixmap(dpy, picture_pm);
    return source;
  }
  {
    XRenderColor clear = {0, 0, 0, 0};
    XRenderFillRectangle(dpy, PictOpSrc, rounded, &clear, 0, 0, w, h);
  }
  XRenderComposite(dpy, PictOpSrc, source, mask, rounded, 0, 0, 0, 0, 0,
                   0, w, h);
  XRenderFreePicture(dpy, mask);
  XFreePixmap(dpy, mask_pm);
  XRenderFreePicture(dpy, source);
  XFreePixmap(dpy, picture_pm);
  return rounded;
}

static void notification_load_image(Notification *n, const char *path) {
  Imlib_Image image;
  DATA32 *data;
  int w, h;

  if (!n || !path || !*path)
    return;
  image = imlib_load_image(path);
  if (!image)
    return;
  imlib_context_set_image(image);
  w = imlib_image_get_width();
  h = imlib_image_get_height();
  data = imlib_image_get_data_for_reading_only();
  if (data && w > 0 && h > 0) {
    unsigned int dw, dh;
    /* Keep the image's aspect ratio.  Images normally fit at their source
     * size, while larger images are reduced to no more than 50 px high. */
    notification_fit_size(w, h, NOTIFY_MAX_W - 40, 50, &dw, &dh);
    n->image = notification_round_picture(
        drw_picture_create_resized(drw, (char *)data, w, h, dw, dh), dw, dh);
    n->image_w = dw;
    n->image_h = dh;
  }
  if (imlib_context_get_image())
    imlib_free_image();
}

static void notification_load_image_data(Notification *n, int w, int h,
                                         int rowstride, int has_alpha,
                                         const unsigned char *bytes,
                                         int nbytes) {
  uint32_t *pixels;
  int x, y;
  size_t required;

  if (!n || !bytes || w <= 0 || h <= 0 || w > 2048 || h > 2048 ||
      rowstride < w * 4 || rowstride <= 0 || nbytes < 0)
    return;
  required = (size_t)rowstride * (size_t)h;
  if (required > (size_t)nbytes)
    return;
  pixels = ecalloc((size_t)w * h, sizeof(*pixels));
  for (y = 0; y < h; y++)
    for (x = 0; x < w; x++) {
      const unsigned char *p = bytes + y * rowstride + x * 4;
      uint32_t a = has_alpha ? p[3] : 255;
      pixels[y * w + x] = (a << 24) | (p[2] << 16) | (p[1] << 8) | p[0];
    }
  {
    unsigned int dw, dh;
    notification_fit_size(w, h, NOTIFY_MAX_W - 40, 50, &dw, &dh);
    n->image = notification_round_picture(
        drw_picture_create_resized(drw, (char *)pixels, w, h, dw, dh), dw,
        dh);
    n->image_w = dw;
    n->image_h = dh;
  }
  n->image_hint = 1;
  free(pixels);
}

static unsigned int notification_text_width(const char *text) {
  const char *start, *end, *next;
  char line[512];
  unsigned int width = 0, line_width;

  if (!text || !*text)
    return 0;
  start = text;
  while (*start) {
    next = strchr(start, '\n');
    end = next ? next : start + strlen(start);
    {
      size_t len = MIN((size_t)(end - start), sizeof(line) - 1);
      memcpy(line, start, len);
      line[len] = '\0';
    }
    line_width = drw_fontset_getwidth(drw, line);
    width = MAX(width, line_width);
    start = next ? next + 1 : end;
  }
  return width;
}

static unsigned int notification_history_entry_height(Notification *n) {
  unsigned int height;
  int has_summary, has_body, has_two_content;

  if (!n)
    return NOTIFY_HISTORY_ENTRY_H;
  has_summary = n->summary && *n->summary;
  has_body = n->body && *n->body;
  has_two_content = (has_summary && has_body) ||
                    (n->image && (has_summary || has_body));
  height = (!has_two_content && !n->image) ? bh : NOTIFY_HISTORY_ENTRY_H;
  if (n->input_enabled)
    height += NOTIFY_INPUT_ROW_H;
  if (n->action_count >= 2)
    height += NOTIFY_BUTTON_ROW_H;
  return height;
}

static void notification_history_layout(void) {
  Notification *n;
  unsigned int content_h;
  int max_scroll;

  /* Keep history stable while entries are added or removed. */
  notify_width = NOTIFY_MAX_W;
  content_h = 0;
  for (n = notify_history_head; n; n = n->next)
    content_h += notification_history_entry_height(n);
  notify_height = MIN(MAX(content_h, bh), (unsigned int)NOTIFY_HISTORY_MAX_H);
  max_scroll = content_h > notify_height ? (int)(content_h - notify_height) : 0;
  notify_history_scroll = MAX(0, MIN(notify_history_scroll, max_scroll));
  notify_history_scroll_target = MAX(0, MIN(notify_history_scroll_target,
                                             max_scroll));
  if (!max_scroll)
    notify_history_scroll = 0;
  if (!max_scroll)
    notify_history_scroll_target = 0;
}

static void notification_history_show(void) {
  if (!notify_history_count)
    return;
  notify_history_active = 1;
  notification_history_layout();
  drawbars();
  resizebarwin(selmon);
}

static void notification_history_hide(void) {
  if (!notify_history_active)
    return;
  notify_history_active = 0;
  notify_history_input = NULL;
  notify_input_focus = 0;
  notify_history_hover_entry = NULL;
  notify_history_hover_action = -1;
  notify_history_scroll = 0;
  notify_history_scroll_target = 0;
  notify_history_scroll_start = 0;
  notify_history_scroll_end = 0;
  drawbars();
  resizebarwin(selmon);
}

static void notification_update_layout(Notification *n) {
  unsigned int text_w, line_w;
  unsigned int min_width;
  int has_summary, has_body, has_two_content;

  if (!n)
    return;
  text_w = notification_text_width(n->summary);
  line_w = notification_text_width(n->body);
  text_w = MAX(text_w, line_w);
  has_summary = n->summary && *n->summary;
  has_body = n->body && *n->body;
  has_two_content = (has_summary && has_body) || (n->image && (has_summary || has_body));

  text_w = MAX(text_w, 1);
  if (n->image)
    text_w += n->image_w + 16;
  if (n->input_enabled)
    text_w = MAX(text_w, notification_text_width(n->input_placeholder) + 32);
  if (n->action_count >= 2) {
    unsigned int action_w = 0, i;
    for (i = 1; i < n->action_count; i += 2)
      action_w += notification_text_width(n->actions[i]) + 24;
    text_w = MAX(text_w, action_w);
  }
  notify_width = MIN(NOTIFY_MAX_W, text_w + 40);
  min_width = clockbar_cw ? clockbar_cw : clockwidth();
  min_width = MIN(min_width, NOTIFY_MAX_W);
  notify_width = MAX(notify_width, min_width);

  /* A one-line notification stays at the normal clock-bar height. */
  notify_height = bh;
  if (has_two_content)
    notify_height = NOTIFY_TWO_CONTENT_H;
  if (n->input_enabled || (notify_hovered && n->action_count >= 2)) {
    unsigned int content_height = has_two_content ? NOTIFY_TWO_CONTENT_H : bh;
    unsigned int controls = (n->input_enabled ? NOTIFY_INPUT_ROW_H : 0) +
                            (notify_hovered && n->action_count >= 2
                                 ? NOTIFY_BUTTON_ROW_H
                                 : 0);
    if (notify_hovered && n->image && n->action_count >= 2)
      controls += NOTIFY_IMAGE_BUTTON_GAP + 6;
    notify_height = MAX(notify_height, content_height + controls);
  }
}

static void notification_set_hovered(int hovered) {
  struct timespec now;
  time_t paused_sec;
  long paused_nsec;

  hovered = !!hovered;
  if (notify_hovered == hovered)
    return;

  if (hovered) {
    clock_gettime(CLOCK_MONOTONIC, &notify_hover_started);
  } else if (notify_current) {
    clock_gettime(CLOCK_MONOTONIC, &now);
    paused_sec = now.tv_sec - notify_hover_started.tv_sec;
    paused_nsec = now.tv_nsec - notify_hover_started.tv_nsec;
    if (paused_nsec < 0) {
      paused_sec--;
      paused_nsec += 1000000000L;
    }
    notify_current->shown_at.tv_sec += paused_sec;
    notify_current->shown_at.tv_nsec += paused_nsec;
    if (notify_current->shown_at.tv_nsec >= 1000000000L) {
      notify_current->shown_at.tv_sec++;
      notify_current->shown_at.tv_nsec -= 1000000000L;
    }
  }
  notify_hovered = hovered;
  notification_update_layout(notify_current);
  drawbars();
  resizebarwin(selmon);
}

static void notification_queue(Notification *n) {
  Notification *p;
  if (!n)
    return;

  /* Updates to an entry already in history stay in history. */
  for (p = notify_history_head; p; p = p->next) {
    if (p->id == n->id) {
      unsigned int id = p->id;
      notification_free_contents(p);
      p->app_name = n->app_name;
      p->summary = n->summary;
      p->body = n->body;
      p->icon = n->icon;
      p->actions = n->actions;
      p->action_count = n->action_count;
      p->input_enabled = n->input_enabled;
      p->input_action = n->input_action;
      p->input_placeholder = n->input_placeholder;
      p->input_text = n->input_text;
      p->image = n->image;
      p->image_w = n->image_w;
      p->image_h = n->image_h;
      p->image_hint = n->image_hint;
      p->id = id;
      free(n);
      if (notify_history_active) {
        notification_history_layout();
        drawbars();
        resizebarwin(selmon);
      }
      return;
    }
  }

  /* Notifications received while history is open are history entries, not
   * a new timed notification. */
  if (notify_history_active && !notify_current) {
    notification_history_add(n);
    notification_history_layout();
    drawbars();
    resizebarwin(selmon);
    return;
  }

  /* A non-zero replaces_id updates the existing notification in place. */
  for (p = notify_current; p; p = NULL) {
    if (p->id == n->id) {
      unsigned int id = p->id;
      notification_free_contents(p);
      p->app_name = n->app_name;
      p->summary = n->summary;
      p->body = n->body;
      p->icon = n->icon;
       p->actions = n->actions;
       p->action_count = n->action_count;
       p->input_enabled = n->input_enabled;
       p->input_action = n->input_action;
       p->input_placeholder = n->input_placeholder;
       p->input_text = n->input_text;
      p->image = n->image;
      p->image_w = n->image_w;
      p->image_h = n->image_h;
       p->image_hint = n->image_hint;
        p->id = id;
        notify_input_focus = 0;
        notify_hovered = 0;
        notify_hover = -1;
       clock_gettime(CLOCK_MONOTONIC, &p->shown_at);
      notification_update_layout(p);
      free(n);
      drawbars();
      resizebarwin(selmon);
      return;
    }
  }
  for (p = notify_head; p; p = p->next) {
    if (p->id == n->id) {
      unsigned int id = p->id;
      notification_free_contents(p);
      p->app_name = n->app_name;
      p->summary = n->summary;
      p->body = n->body;
      p->icon = n->icon;
       p->actions = n->actions;
       p->action_count = n->action_count;
       p->input_enabled = n->input_enabled;
       p->input_action = n->input_action;
       p->input_placeholder = n->input_placeholder;
       p->input_text = n->input_text;
      p->image = n->image;
      p->image_w = n->image_w;
      p->image_h = n->image_h;
      p->image_hint = n->image_hint;
      p->id = id;
      free(n);
      return;
    }
  }
  if (notify_count >= NOTIFY_MAX) {
    notification_free(n);
    return;
  }
  n->next = NULL;
  if (notify_tail)
    notify_tail->next = n;
  else
    notify_head = n;
  notify_tail = n;
  notify_count++;
  if (!notify_current && !notify_transition_pending) {
    notify_current = notify_head;
    notify_head = notify_current->next;
    if (!notify_head)
      notify_tail = NULL;
     notify_current->next = NULL;
     notify_input_focus = 0;
     notify_hovered = 0;
     notify_hover = -1;
    clock_gettime(CLOCK_MONOTONIC, &notify_current->shown_at);
    notification_update_layout(notify_current);
    notify_active = 1;
    clockbar_dynw = notify_width;
    clockbar_peak = 0.0f;
    drawbars();
    resizebarwin(selmon);
  }
}

static void notification_advance(void) {
  Notification *old = notify_current;
  notify_input_focus = 0;
  notify_hovered = 0;
  notify_hover = -1;
  notify_current = NULL;
  notify_active = 0;
  clockbar_dynw = 0;
  if (notify_count)
    notify_count--;
  notification_history_add(old);
  notify_transition_pending = 1;
  clock_gettime(CLOCK_MONOTONIC, &notify_transition_started);
  drawbars();
  resizebarwin(selmon);
}

static void notification_clear_queue(void) {
  Notification *n, *next;

  notify_transition_pending = 0;
  if (notify_current) {
    notification_history_add(notify_current);
    notify_current = NULL;
  }
  for (n = notify_head; n; n = next) {
    next = n->next;
    n->next = NULL;
    notification_history_add(n);
  }
  notify_head = notify_tail = NULL;
  notify_count = 0;
  notify_active = 0;
  notify_input_focus = 0;
  notify_hovered = 0;
  notify_hover = -1;
  clockbar_dynw = 0;
  notify_transition_pending = 1;
  clock_gettime(CLOCK_MONOTONIC, &notify_transition_started);
  drawbars();
  resizebarwin(selmon);
}

static char *notification_variant_string(DBusMessageIter *variant) {
  DBusMessageIter value;
  char *s = NULL;
  if (dbus_message_iter_get_arg_type(variant) != DBUS_TYPE_VARIANT)
    return NULL;
  dbus_message_iter_recurse(variant, &value);
  if (dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_STRING)
    dbus_message_iter_get_basic(&value, &s);
  return s ? strdup(s) : NULL;
}

static int notification_variant_bool(DBusMessageIter *variant, int *result) {
  DBusMessageIter value;
  dbus_bool_t b;

  if (dbus_message_iter_get_arg_type(variant) != DBUS_TYPE_VARIANT)
    return 0;
  dbus_message_iter_recurse(variant, &value);
  if (dbus_message_iter_get_arg_type(&value) != DBUS_TYPE_BOOLEAN)
    return 0;
  dbus_message_iter_get_basic(&value, &b);
  *result = b != FALSE;
  return 1;
}

static void notification_parse_actions(Notification *n, DBusMessageIter *iter) {
  DBusMessageIter actions;
  char *value;

  if (!n || dbus_message_iter_get_arg_type(iter) != DBUS_TYPE_ARRAY)
    return;
  dbus_message_iter_recurse(iter, &actions);
  while (dbus_message_iter_get_arg_type(&actions) == DBUS_TYPE_STRING) {
    value = NULL;
    dbus_message_iter_get_basic(&actions, &value);
    if (value) {
      n->actions = realloc(n->actions,
                           (n->action_count + 1) * sizeof(*n->actions));
      if (!n->actions)
        die("realloc:");
      n->actions[n->action_count++] = strdup(value);
    }
    dbus_message_iter_next(&actions);
  }
  /* The protocol stores action ID and label as alternating strings. */
  if (n->action_count & 1) {
    free(n->actions[n->action_count - 1]);
    n->action_count--;
  }
}

static void notification_parse_hints(Notification *n, DBusMessageIter *iter) {
  DBusMessageIter dict, value, image;
  char *key, *path;
  if (dbus_message_iter_get_arg_type(iter) != DBUS_TYPE_ARRAY)
    return;
  dbus_message_iter_recurse(iter, &dict);
  while (dbus_message_iter_get_arg_type(&dict) == DBUS_TYPE_DICT_ENTRY) {
    dbus_message_iter_recurse(&dict, &value);
    key = NULL;
    dbus_message_iter_get_basic(&value, &key);
    dbus_message_iter_next(&value);
    if (key && strcmp(key, "x-andwm-input") == 0) {
      int enabled;
      if (notification_variant_bool(&value, &enabled))
        n->input_enabled = enabled;
    } else if (key && strcmp(key, "x-andwm-input-action") == 0) {
      path = notification_variant_string(&value);
      if (path) {
        free(n->input_action);
        n->input_action = path;
        n->input_enabled = 1;
      }
    } else if (key && strcmp(key, "x-andwm-input-placeholder") == 0) {
      path = notification_variant_string(&value);
      if (path) {
        free(n->input_placeholder);
        n->input_placeholder = path;
      }
    } else if (key && strcmp(key, "image-path") == 0) {
      path = notification_variant_string(&value);
      if (path) {
        free(n->icon);
        n->icon = path;
        n->image_hint = 1;
      }
    } else if (key && strcmp(key, "image-data") == 0 &&
               dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_VARIANT) {
      dbus_message_iter_recurse(&value, &image);
      if (dbus_message_iter_get_arg_type(&image) == DBUS_TYPE_STRUCT) {
        DBusMessageIter field, bytes;
        int w, h, rowstride, bits, channels;
        dbus_bool_t has_alpha;
        unsigned char *data = NULL;
        int len;
        dbus_message_iter_recurse(&image, &field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_INT32)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &w); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_INT32)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &h); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_INT32)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &rowstride); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_BOOLEAN)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &has_alpha); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_INT32)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &bits); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) != DBUS_TYPE_INT32)
          goto next_hint;
        dbus_message_iter_get_basic(&field, &channels); dbus_message_iter_next(&field);
        if (dbus_message_iter_get_arg_type(&field) == DBUS_TYPE_ARRAY &&
            dbus_message_iter_get_element_type(&field) == DBUS_TYPE_BYTE) {
          len = dbus_message_iter_get_element_count(&field);
          if (len > 0 && len <= 16 * 1024 * 1024) {
            data = ecalloc((size_t)len, sizeof(*data));
            dbus_message_iter_recurse(&field, &bytes);
            for (int i = 0; i < len; i++) {
              dbus_message_iter_get_basic(&bytes, &data[i]);
              dbus_message_iter_next(&bytes);
            }
            if (bits == 8 && channels == 4)
              notification_load_image_data(n, w, h, rowstride, has_alpha,
                                           data, len);
            free(data);
          }
        }
      }
    }
next_hint:
    dbus_message_iter_next(&dict);
  }
}

static DBusHandlerResult notification_message(DBusConnection *conn,
                                               DBusMessage *msg, void *data) {
  DBusError error;
  DBusMessageIter iter;
  DBusMessage *reply;
  const char *app, *icon, *summary, *body;
  int replaces_id, expire;
  uint32_t notification_id;
  Notification *n;
  unsigned int i;

  dbus_error_init(&error);

  if (dbus_message_is_method_call(msg, "org.freedesktop.Notifications", "GetCapabilities")) {
    reply = dbus_message_new_method_return(msg);
    if (reply) {
      DBusMessageIter out;
      const char *caps[] = {"actions", "body", "body-markup", "icon-static", "image-data", "image-path"};
      dbus_message_iter_init_append(reply, &out);
      dbus_message_iter_open_container(&out, DBUS_TYPE_ARRAY, "s", &iter);
      for (i = 0; i < sizeof(caps) / sizeof(caps[0]); i++)
        dbus_message_iter_append_basic(&iter, DBUS_TYPE_STRING, &caps[i]);
      dbus_message_iter_close_container(&out, &iter);
      dbus_connection_send(conn, reply, NULL);
      dbus_message_unref(reply);
    }
    return DBUS_HANDLER_RESULT_HANDLED;
  }
  if (dbus_message_is_method_call(msg, "org.freedesktop.Notifications", "GetServerInformation")) {
    reply = dbus_message_new_method_return(msg);
    if (reply) {
      const char *name = "AnDWM", *vendor = "AnDWM", *version = "1", *spec = "1.2";
      dbus_message_append_args(reply, DBUS_TYPE_STRING, &name, DBUS_TYPE_STRING,
                               &vendor, DBUS_TYPE_STRING, &version,
                               DBUS_TYPE_STRING, &spec, DBUS_TYPE_INVALID);
      dbus_connection_send(conn, reply, NULL);
      dbus_message_unref(reply);
    }
    return DBUS_HANDLER_RESULT_HANDLED;
  }
  if (dbus_message_is_method_call(msg, "org.freedesktop.Notifications",
                                  "CloseNotification")) {
    uint32_t id;
    Notification *n, *prev;

    if (!dbus_message_get_args(msg, &error, DBUS_TYPE_UINT32, &id,
                               DBUS_TYPE_INVALID)) {
      dbus_error_free(&error);
      return DBUS_HANDLER_RESULT_HANDLED;
    }
    if (notify_current && notify_current->id == id) {
      notification_emit_closed(notify_current, 3);
      notification_advance();
    } else {
      prev = NULL;
      for (n = notify_head; n; prev = n, n = n->next) {
        if (n->id == id) {
          if (prev)
            prev->next = n->next;
          else
            notify_head = n->next;
           if (notify_tail == n)
             notify_tail = prev;
           notification_free(n);
           if (notify_count)
             notify_count--;
           break;
        }
      }
    }
    reply = dbus_message_new_method_return(msg);
    if (reply) {
      dbus_connection_send(conn, reply, NULL);
      dbus_message_unref(reply);
    }
    return DBUS_HANDLER_RESULT_HANDLED;
  }
  if (!dbus_message_is_method_call(msg, "org.freedesktop.Notifications", "Notify"))
    return DBUS_HANDLER_RESULT_NOT_YET_HANDLED;
  if (!dbus_message_iter_init(msg, &iter) ||
      dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING)
    return DBUS_HANDLER_RESULT_HANDLED;
  dbus_message_iter_get_basic(&iter, &app); dbus_message_iter_next(&iter);
  dbus_message_iter_get_basic(&iter, &replaces_id); dbus_message_iter_next(&iter);
  dbus_message_iter_get_basic(&iter, &icon); dbus_message_iter_next(&iter);
  dbus_message_iter_get_basic(&iter, &summary); dbus_message_iter_next(&iter);
  dbus_message_iter_get_basic(&iter, &body); dbus_message_iter_next(&iter);
  n = ecalloc(1, sizeof(*n));
  n->id = replaces_id ? replaces_id : notify_next_id++;
  notification_id = n->id;
  n->app_name = notify_strdup(app); n->summary = notify_strdup(summary);
  n->body = notify_strdup(body); n->icon = notify_strdup(icon);
  notification_parse_actions(n, &iter);
  dbus_message_iter_next(&iter);
  notification_parse_hints(n, &iter);
  if (n->input_enabled && !n->input_action)
    n->input_action = notify_strdup("submit");
  /* app_icon is commonly an absolute path, but accepting a plain image name
   * as well keeps metadata supplied by small notification clients useful. */
  if (!n->image && n->icon && *n->icon)
    notification_load_image(n, n->icon);
  dbus_message_iter_next(&iter);
  expire = 0;
  if (dbus_message_iter_get_arg_type(&iter) == DBUS_TYPE_INT32)
    dbus_message_iter_get_basic(&iter, &expire);
  notification_queue(n);
  reply = dbus_message_new_method_return(msg);
  if (reply) {
    dbus_message_append_args(reply, DBUS_TYPE_UINT32, &notification_id,
                             DBUS_TYPE_INVALID);
    dbus_connection_send(conn, reply, NULL);
    dbus_message_unref(reply);
  }
  return DBUS_HANDLER_RESULT_HANDLED;
}

static void notification_draw_text(int x, int y, int width, int bottom,
                                   const char *text) {
  char line[512], *p, *start;
  int line_h = drw->fonts->h + 4;
  if (!text || !*text)
    return;
  start = (char *)text;
  while (*start && y < bottom - NOTIFY_TEXT_BOTTOM_GAP) {
    p = strchr(start, '\n');
    if (p) {
      size_t len = MIN((size_t)(p - start), sizeof(line) - 1);
      memcpy(line, start, len); line[len] = '\0';
      start = p + 1;
    } else {
      strncpy(line, start, sizeof(line) - 1);
      line[sizeof(line) - 1] = '\0';
      start += strlen(start);
    }
    drw_text(drw, x, y, width, line_h, 8, line, 0);
    y += line_h;
  }
}

static void notification_draw(void) {
  Notification *n = notify_current;
  int text_x = 12, text_w = notify_width - 24;
  int content_h;
  int controls_h;
  int summary_y, body_y;
  int has_summary, has_body;
  if (!n)
    return;
  has_summary = n->summary && *n->summary;
  has_body = n->body && *n->body;
  controls_h = (n->input_enabled ? NOTIFY_INPUT_ROW_H : 0) +
               (notify_hovered && n->action_count >= 2
                    ? NOTIFY_BUTTON_ROW_H
                    : 0);
  if (notify_hovered && n->image && n->action_count >= 2)
    controls_h += NOTIFY_IMAGE_BUTTON_GAP + 6;
  content_h = notify_height - controls_h;
  XSetForeground(drw->dpy, drw->gc, notify_bg.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0,
                 notify_width, notify_height);
  if (n->image) {
    int image_x = 12;
    int image_y = (content_h - (int)n->image_h) / 2;
    drw_pic(drw, image_x, image_y, n->image_w, n->image_h, n->image);
    text_x = image_x + n->image_w + 8;
    text_w = notify_width - text_x - 12;
  } else {
    unsigned int content_w = MAX(notification_text_width(n->summary),
                                 notification_text_width(n->body));
    if (content_w && content_w < notify_width)
      text_x = MAX(0, ((int)notify_width - (int)content_w) / 2 - 8);
    text_w = notify_width - text_x - 8;
  }
  if (has_body && has_summary) {
    summary_y = 7 + NOTIFY_TEXT_TOP_OFFSET;
    body_y = 32 + NOTIFY_TEXT_TOP_OFFSET;
  } else {
    summary_y = body_y = MAX(0, (content_h - (drw->fonts->h + 8)) / 2);
  }
  drw_setscheme(drw, notify_summary_scheme);
  if (has_summary)
    drw_text(drw, text_x, summary_y, text_w, drw->fonts->h + 8, 8,
             n->summary, 0);
  drw_setscheme(drw, notify_body_scheme);
  if (has_body)
    notification_draw_text(text_x, body_y, text_w, content_h, n->body);

  memset(notify_action_x, 0, sizeof(notify_action_x));
  memset(notify_action_w, 0, sizeof(notify_action_w));
  if (n->input_enabled) {
    notify_input_x = 8;
    notify_input_y = notify_height - NOTIFY_INPUT_ROW_H -
                     (notify_hovered && n->action_count >= 2
                           ? NOTIFY_BUTTON_ROW_H
                           : 0);
    notify_input_w = notify_width - 16;
    notify_input_h = NOTIFY_ACTION_H - 6;
    drw_setscheme(drw, notify_hover == -2 ? notify_control_hover_scheme
                                          : notify_control_scheme);
    drw_rect(drw, notify_input_x, notify_input_y, notify_input_w,
             notify_input_h, 1, 1);
    drw_text(drw, notify_input_x + 6, notify_input_y, notify_input_w - 12,
             notify_input_h, 6,
             n->input_text && *n->input_text ? n->input_text
                                              : n->input_placeholder,
             0);
  }
  if (n->action_count >= 2) {
    unsigned int i, x = NOTIFY_ACTION_X, button = 0;
    int y = notify_height - NOTIFY_ACTION_H;
    for (i = 0; i + 1 < n->action_count && button < LENGTH(notify_action_x);
         i += 2, button++) {
      unsigned int w = notification_text_width(n->actions[i + 1]) + 24;
      if (x + w > notify_width - 8)
        break;
      notify_action_x[button] = x;
      notify_action_w[button] = w;
      if (notify_hovered) {
        drw_setscheme(drw, notify_hover == (int)button
                                ? notify_action_hover_scheme
                                : notify_action_scheme);
        drw_text(drw, x, y, w, NOTIFY_BUTTON_H, 12, n->actions[i + 1], 0);
      }
      x += w + 6;
    }
  }
}

static void notification_history_draw(void) {
  Notification *n;
  Notification *entries[NOTIFY_HISTORY_MAX];
  unsigned int count = 0, index;
  int y, text_x, text_w, entry_bottom, body_bottom;
  int action_y, input_y;
  unsigned int entry_h;

  notification_history_layout();
  for (n = notify_history_head; n && count < LENGTH(entries); n = n->next)
    entries[count++] = n;
  XSetForeground(drw->dpy, drw->gc, notify_bg.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0,
                 notify_width, notify_height);
  for (index = 0; index < count; index++) {
    /* The newest notification is shown at the top. */
    n = entries[count - 1 - index];
    unsigned int image_w, image_h, content_h;
    int has_summary, has_body, has_two_content, controls_h, text_y;
    entry_h = notification_history_entry_height(n);
    y = -notify_history_scroll;
    for (unsigned int previous = 0; previous < index; previous++)
      y += notification_history_entry_height(entries[count - 1 - previous]);
    entry_bottom = y + entry_h;
    has_summary = n->summary && *n->summary;
    has_body = n->body && *n->body;
    has_two_content = (has_summary && has_body) ||
                      (n->image && (has_summary || has_body));
    controls_h = (n->input_enabled ? NOTIFY_INPUT_ROW_H : 0) +
                 (n->action_count >= 2 ? NOTIFY_BUTTON_ROW_H : 0);
    content_h = entry_h - controls_h;
    if (entry_bottom <= 0 || y >= (int)notify_height)
      continue;
    text_x = 12;
    text_w = notify_width - 24;
    if (n->image) {
      /* The picture has already been resized when the notification was
       * received.  Use its real dimensions here: drw_pic composites the
       * source without scaling, so drawing it into a different aspect ratio
       * would crop or distort it. */
      image_w = n->image_w;
      image_h = n->image_h;
      text_x = 12 + image_w + 8;
      text_w = notify_width - text_x - 12;
      drw_pic(drw, 12, y + ((int)content_h - image_h) / 2,
              image_w, image_h, n->image);
    }
    drw_setscheme(drw, notify_summary_scheme);
    text_y = has_two_content ? y + 7 + NOTIFY_TEXT_TOP_OFFSET
                             : y + MAX(0, ((int)content_h -
                                           (drw->fonts->h + 8)) / 2);
    if (has_summary)
      drw_text(drw, text_x, text_y, text_w,
               drw->fonts->h + 6, 8,
               n->summary, 0);
    drw_setscheme(drw, notify_body_scheme);
    action_y = entry_bottom - NOTIFY_ACTION_H;
    input_y = n->action_count >= 2
                  ? action_y - NOTIFY_INPUT_ROW_H
                  : entry_bottom - NOTIFY_INPUT_ROW_H;
    body_bottom = entry_bottom - 6;
    if (n->action_count >= 2)
      body_bottom = MIN(body_bottom, action_y - 4);
    if (n->input_enabled)
      body_bottom = MIN(body_bottom, input_y - 4);
    notification_draw_text(text_x, has_two_content
                                      ? y + 32 + NOTIFY_TEXT_TOP_OFFSET
                                      : text_y,
                           text_w,
                           MIN(body_bottom, (int)notify_height), n->body);
    if (n->input_enabled) {
      notify_input_x = 8;
      notify_input_y = input_y;
      notify_input_w = notify_width - 16;
      notify_input_h = NOTIFY_ACTION_H - 6;
      drw_setscheme(drw, notify_history_hover_entry == n &&
                            notify_history_hover_action == -2
                            ? notify_control_hover_scheme
                            : notify_control_scheme);
      drw_rect(drw, notify_input_x, notify_input_y, notify_input_w,
               notify_input_h, 1, 1);
      drw_text(drw, notify_input_x + 6, notify_input_y,
               notify_input_w - 12, notify_input_h, 6,
               n->input_text && *n->input_text ? n->input_text
                                                : n->input_placeholder,
               0);
    }
    if (n->action_count >= 2) {
      unsigned int i, x = NOTIFY_ACTION_X;
      for (i = 1; i < n->action_count; i += 2) {
        unsigned int w = notification_text_width(n->actions[i]) + 24;
        if (x + w > notify_width - 8)
          break;
        drw_setscheme(drw, notify_history_hover_entry == n &&
                              notify_history_hover_action == (int)(i / 2)
                              ? notify_action_hover_scheme
                              : notify_action_scheme);
        drw_text(drw, x, action_y, w, NOTIFY_BUTTON_H, 12,
                 n->actions[i], 0);
        x += w + 6;
      }
    }
    if (index + 1 < count) {
      XSetForeground(drw->dpy, drw->gc, notify_body.pixel);
      XDrawLine(drw->dpy, drw->drawable, drw->gc, 8, entry_bottom - 1,
                notify_width - 8, entry_bottom - 1);
    }
  }
}

static void notification_motion(XMotionEvent *ev) {
  Notification *n = notify_current;
  int hover = -1;
  unsigned int i;

  if (!notify_active || !n)
    return;
  notification_set_hovered(ev->x >= 0 && ev->x < (int)notify_width &&
                           ev->y >= 0 && ev->y < (int)notify_height);
  if (n->input_enabled && ev->x >= notify_input_x &&
      ev->x < notify_input_x + notify_input_w && ev->y >= notify_input_y &&
      ev->y < notify_input_y + notify_input_h)
    hover = -2;
  else if (n->action_count >= 2) {
    for (i = 0; i < LENGTH(notify_action_x); i++)
      if (notify_action_w[i] && ev->x >= notify_action_x[i] &&
          ev->x < notify_action_x[i] + notify_action_w[i] &&
           ev->y >= notify_height - NOTIFY_ACTION_H &&
           ev->y < notify_height) {
        hover = (int)i;
        break;
      }
  }
  if (hover != notify_hover) {
    notify_hover = hover;
    drawbars();
  }
}

static void notification_history_motion(XMotionEvent *ev) {
  Notification *n;
  Notification *entries[NOTIFY_HISTORY_MAX];
  unsigned int count = 0, index, action;
  unsigned int entry_h, action_w;
  int content_y, y = 0, entry_bottom, action_y, input_y, action_x;
  int hover_action = -1;
  int hover_input = 0;

  for (n = notify_history_head; n && count < LENGTH(entries); n = n->next)
    entries[count++] = n;
  content_y = ev->y + notify_history_scroll;
  for (index = 0; index < count; index++) {
    n = entries[count - index - 1];
    entry_h = notification_history_entry_height(n);
    if (content_y >= y && content_y < y + (int)entry_h)
      break;
    y += entry_h;
  }
  if (index < count) {
    n = entries[count - index - 1];
    y -= notify_history_scroll;
    entry_bottom = y + entry_h;
    action_y = entry_bottom - NOTIFY_ACTION_H;
    input_y = n->action_count >= 2
                  ? action_y - NOTIFY_INPUT_ROW_H
                  : entry_bottom - NOTIFY_INPUT_ROW_H;
    if (n->input_enabled && ev->x >= 8 && ev->x < (int)notify_width - 8 &&
        ev->y >= input_y && ev->y < input_y + NOTIFY_INPUT_ROW_H)
      hover_input = 1;
    if (n->action_count >= 2 && ev->y >= action_y &&
        ev->y < action_y + NOTIFY_ACTION_H) {
      action_x = NOTIFY_ACTION_X;
      for (action = 1; action < n->action_count; action += 2) {
        action_w = notification_text_width(n->actions[action]) + 24;
        if (action_x + (int)action_w > (int)notify_width - 8)
          break;
        if (ev->x >= action_x && ev->x < action_x + (int)action_w) {
          hover_action = (int)(action / 2);
          break;
        }
        action_x += action_w + 6;
      }
    }
    if (hover_input)
      hover_action = -2;
  } else {
    n = NULL;
  }
  if (notify_history_hover_entry != n ||
      notify_history_hover_action != hover_action) {
    notify_history_hover_entry = n;
    notify_history_hover_action = hover_action;
    drawbars();
  }
}

static int notification_history_buttonpress(XButtonPressedEvent *ev) {
  Notification *n;
  Notification *entries[NOTIFY_HISTORY_MAX];
  unsigned int count = 0, index;
  unsigned int entry_h;
  int y, entry_bottom, action_y, input_y, content_y;
  int action_x, action_w;
  int old_target;

  if (!notify_history_active)
    return 0;
  /* Middle and right clicks must not alter history.  Left clicks are handled
   * below only when they land on an action button or input field. */
  if (ev->button == Button2 || ev->button == Button3)
    return 1;
  if (ev->button != Button4 && ev->button != Button5) {
    if (ev->button != Button1)
      return 1;
    for (n = notify_history_head; n && count < NOTIFY_HISTORY_MAX;
         n = n->next)
      entries[count++] = n;
    if (ev->y < 0 || ev->y >= (int)notify_height)
      return 1;
    content_y = (int)ev->y + notify_history_scroll;
    y = 0;
    for (index = 0; index < count; index++) {
      n = entries[count - index - 1];
      entry_h = notification_history_entry_height(n);
      if (content_y >= y && content_y < y + (int)entry_h)
        break;
      y += entry_h;
    }
    if (index >= count)
      return 1;
    n = entries[count - index - 1];
    y -= notify_history_scroll;
    entry_bottom = y + entry_h;
    action_y = entry_bottom - NOTIFY_ACTION_H;
    input_y = n->action_count >= 2
                  ? action_y - NOTIFY_INPUT_ROW_H
                  : entry_bottom - NOTIFY_INPUT_ROW_H;
    if (n->input_enabled && ev->y >= input_y && ev->y < input_y +
        NOTIFY_INPUT_ROW_H && ev->x >= 8 && ev->x < (int)notify_width - 8) {
      if (ev->button == Button1) {
        notify_history_input = n;
        notify_input_focus = 1;
        XSetInputFocus(dpy, selmon->barcenterwin, RevertToParent,
                       CurrentTime);
        XFlush(dpy);
      }
      return 1;
    }
    if (n->action_count >= 2 && ev->y >= action_y &&
        ev->y < action_y + NOTIFY_ACTION_H) {
      action_x = NOTIFY_ACTION_X;
      for (unsigned int action = 1; action < n->action_count; action += 2) {
        action_w = notification_text_width(n->actions[action]) + 24;
        if (action_x + action_w > (int)notify_width - 8)
          break;
        if (ev->x >= action_x && ev->x < action_x + action_w) {
          if (ev->button == Button1) {
            notification_emit_action(n, n->actions[action - 1]);
            /* Match active-notification behavior: the application receives
             * both the action and the close notification for this ID. */
            notification_emit_closed(n, 2);
            notification_history_clear_controls(n);
            if (notify_history_input == n) {
              notify_history_input = NULL;
              notify_input_focus = 0;
            }
            notification_history_layout();
            drawbars();
          }
          return 1;
        }
        action_x += action_w + 6;
      }
    }
    /* A click on the notification content itself has no history action. */
    return 1;
  }
  old_target = notify_history_scroll_target;
  if (ev->button == Button4)
    notify_history_scroll_target -= NOTIFY_HISTORY_ENTRY_H;
  else
    notify_history_scroll_target += NOTIFY_HISTORY_ENTRY_H;
  notification_history_layout();
  if (notify_history_scroll_target != old_target) {
    /* Start a new transition at the currently displayed pixel position so
     * repeated wheel input remains continuous. */
    notify_history_scroll_start = notify_history_scroll;
    notify_history_scroll_end = notify_history_scroll_target;
    clock_gettime(CLOCK_MONOTONIC, &notify_history_scroll_started);
    drawbars();
  }
  return 1;
}

static int notification_history_tick(void) {
  struct timespec now;
  double elapsed, progress, u, lo, hi, x;
  int i;

  if (!notify_history_active ||
      notify_history_scroll == notify_history_scroll_target)
    return 0;

  clock_gettime(CLOCK_MONOTONIC, &now);
  elapsed = (double)(now.tv_sec - notify_history_scroll_started.tv_sec) * 1000.0 +
            (double)(now.tv_nsec - notify_history_scroll_started.tv_nsec) /
            1000000.0;
  progress = MIN(1.0, MAX(0.0, elapsed / NOTIFY_HISTORY_SCROLL_MS));

  /* cubic-bezier(0, .6, .4, 1). Solve the X component for the
   * parametric position, then evaluate the Y component. */
  lo = 0.0;
  hi = 1.0;
  for (i = 0; i < 16; i++) {
    u = (lo + hi) / 2.0;
    x = 3.0 * (1.0 - u) * u * u * 0.4 + u * u * u;
    if (x < progress)
      lo = u;
    else
      hi = u;
  }
  u = (lo + hi) / 2.0;
  progress = 3.0 * (1.0 - u) * (1.0 - u) * u * 0.6 +
             3.0 * (1.0 - u) * u * u + u * u * u;
  notify_history_scroll = notify_history_scroll_start +
                          (int)((notify_history_scroll_end -
                                 notify_history_scroll_start) * progress);
  if (elapsed >= NOTIFY_HISTORY_SCROLL_MS)
    notify_history_scroll = notify_history_scroll_target;
  drawbars();
  return 1;
}

static void notification_emit_closed(Notification *n, uint32_t reason) {
  DBusMessage *signal;
  if (!notify_conn || !n)
    return;
  signal = dbus_message_new_signal("/org/freedesktop/Notifications",
                                  "org.freedesktop.Notifications",
                                  "NotificationClosed");
  if (signal) {
    dbus_message_append_args(signal, DBUS_TYPE_UINT32, &n->id,
                             DBUS_TYPE_UINT32, &reason, DBUS_TYPE_INVALID);
    dbus_connection_send(notify_conn, signal, NULL);
    dbus_message_unref(signal);
  }
}

static void notification_emit_action(Notification *n, const char *action) {
  DBusMessage *signal;
  if (!notify_conn || !n || !action)
    return;
  signal = dbus_message_new_signal("/org/freedesktop/Notifications",
                                  "org.freedesktop.Notifications",
                                  "ActionInvoked");
  if (signal) {
    dbus_message_append_args(signal, DBUS_TYPE_UINT32, &n->id,
                             DBUS_TYPE_STRING, &action, DBUS_TYPE_INVALID);
    dbus_connection_send(notify_conn, signal, NULL);
    dbus_message_unref(signal);
  }
}

static void notification_emit_input(Notification *n) {
  DBusMessage *signal;
  const char *action;
  const char *text;
  if (!notify_conn || !n || !n->input_action)
    return;
  action = n->input_action;
  text = n->input_text ? n->input_text : "";
  signal = dbus_message_new_signal("/org/freedesktop/Notifications",
                                  "org.freedesktop.Notifications",
                                  "InputSubmitted");
  if (signal) {
    dbus_message_append_args(signal, DBUS_TYPE_UINT32, &n->id,
                             DBUS_TYPE_STRING, &action,
                             DBUS_TYPE_STRING, &text, DBUS_TYPE_INVALID);
    dbus_connection_send(notify_conn, signal, NULL);
    dbus_message_unref(signal);
  }
}

static int notification_buttonpress(XButtonPressedEvent *ev) {
  Notification *n = notify_current;
  int in_input = 0, in_action = 0;
  unsigned int i;

  if (!n)
    return 0;
  if (n->input_enabled && ev->x >= notify_input_x &&
      ev->x < notify_input_x + notify_input_w && ev->y >= notify_input_y &&
      ev->y < notify_input_y + notify_input_h) {
    in_input = 1;
    if (ev->button == Button1) {
      notify_input_focus = 1;
      XSetInputFocus(dpy, selmon->barcenterwin, RevertToParent, CurrentTime);
      XFlush(dpy);
    }
    return 1;
  }
  for (i = 0; i < LENGTH(notify_action_x); i++) {
    if (notify_action_w[i] && ev->x >= notify_action_x[i] &&
        ev->x < notify_action_x[i] + notify_action_w[i] &&
           ev->y >= notify_height - NOTIFY_ACTION_H &&
           ev->y < notify_height) {
      in_action = 1;
      if (ev->button == Button1) {
        notification_emit_action(n, n->actions[i * 2]);
        notification_emit_closed(n, 2);
        /* An action was handled, so the archived copy keeps only the
         * notification content, not controls which can no longer be used. */
        notification_history_clear_controls(n);
        notification_advance();
      }
      return 1;
    }
  }

  /* Mouse bindings below apply only to the notification text/image area. */
  if (in_input || in_action)
    return 1;
  if (ev->button == Button1) {
    if (n->action_count >= 2) {
      notification_emit_action(n, n->actions[0]);
      notification_emit_closed(n, 2);
      notification_history_clear_controls(n);
      notification_advance();
    }
    return 1;
  }
  if (ev->button == Button3) {
    /* Right-click skips this notification silently and archives it. */
    notification_advance();
    return 1;
  }
  if (ev->button == Button2) {
    notification_clear_queue();
    return 1;
  }
  return 0;
}

static int notification_input_keypress(XKeyEvent *ev) {
  Notification *n = notify_active ? notify_current : notify_history_input;
  int history_input = !notify_active && notify_history_input == n;
  KeySym keysym;
  char text[64];
  int len;

  if (!notify_input_focus || !n || !n->input_enabled)
    return 0;
  keysym = XLookupKeysym(ev, 0);
  if (keysym == XK_Escape) {
    notify_input_focus = 0;
    if (history_input) {
      notification_history_clear_controls(n);
      notify_history_input = NULL;
      notification_history_layout();
      drawbars();
    } else {
      notification_emit_closed(n, 2);
      notification_history_clear_controls(n);
      notification_advance();
    }
    XSetInputFocus(dpy, root, RevertToParent, CurrentTime);
    return 1;
  }
  if (keysym == XK_Return || keysym == XK_KP_Enter) {
    notify_input_focus = 0;
    notification_emit_input(n);
    if (history_input) {
      notification_history_clear_controls(n);
      notify_history_input = NULL;
      notification_history_layout();
      drawbars();
    } else {
      notification_emit_closed(n, 2);
      notification_history_clear_controls(n);
      notification_advance();
    }
    XSetInputFocus(dpy, root, RevertToParent, CurrentTime);
    return 1;
  }
  if (keysym == XK_BackSpace) {
    size_t length = n->input_text ? strlen(n->input_text) : 0;
    if (length) {
      n->input_text[length - 1] = '\0';
      drawbars();
    }
    return 1;
  }
  len = XLookupString(ev, text, sizeof(text) - 1, NULL, NULL);
  if (len > 0) {
    size_t oldlen = n->input_text ? strlen(n->input_text) : 0;
    size_t room = NOTIFY_MAX_TEXT - 1 - oldlen;
    if (room) {
      size_t add = MIN((size_t)len, room);
      n->input_text = realloc(n->input_text, oldlen + add + 1);
      if (!n->input_text)
        die("realloc:");
      memcpy(n->input_text + oldlen, text, add);
      n->input_text[oldlen + add] = '\0';
      drawbars();
    }
    return 1;
  }
  return 1;
}

static double notification_elapsed(const struct timespec *started) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (double)(now.tv_sec - started->tv_sec) +
         (double)(now.tv_nsec - started->tv_nsec) / 1000000000.0;
}

static void notification_dispatch(void) {
  if (notify_conn) {
    dbus_connection_read_write(notify_conn, 0);
    while (dbus_connection_dispatch(notify_conn) == DBUS_DISPATCH_DATA_REMAINS)
      ;
  }
}

static void notification_tick(void) {
  if (notify_transition_pending &&
      notification_elapsed(&notify_transition_started) >=
          NOTIFY_TRANSITION_MS / 1000.0) {
    notify_transition_pending = 0;
    if (notify_head) {
      notify_current = notify_head;
      notify_head = notify_current->next;
      if (!notify_head)
        notify_tail = NULL;
      notify_current->next = NULL;
      notify_input_focus = 0;
      notify_hovered = 0;
      notify_hover = -1;
      clock_gettime(CLOCK_MONOTONIC, &notify_current->shown_at);
      notification_update_layout(notify_current);
      notify_active = 1;
      clockbar_dynw = notify_width;
      clockbar_peak = 0.0f;
      drawbars();
      resizebarwin(selmon);
    } else if (notify_clock_hovered && notify_history_count) {
      notification_history_show();
    } else {
      drawbars();
      resizebarwin(selmon);
    }
    return;
  }
  if (!notify_hovered && notify_current &&
      notification_elapsed(&notify_current->shown_at) >=
                           NOTIFY_TIMEOUT) {
    /* Timed-out notifications remain actionable from history.  Do not send
     * NotificationClosed here; the application must stay able to receive a
     * later ActionInvoked or InputSubmitted for this notification. */
    notification_advance();
  }
}

static void notification_init(void) {
  DBusError error;
  int result;
  dbus_error_init(&error);
  notify_conn = dbus_bus_get(DBUS_BUS_SESSION, &error);
  if (!notify_conn) {
    fprintf(stderr, "AnDWM: cannot connect to session D-Bus: %s\n",
            error.message ? error.message : "unknown error");
    dbus_error_free(&error);
    return;
  }
  result = dbus_bus_request_name(notify_conn, "org.freedesktop.Notifications",
                                 DBUS_NAME_FLAG_REPLACE_EXISTING, &error);
  if (result != DBUS_REQUEST_NAME_REPLY_PRIMARY_OWNER) {
    fprintf(stderr, "AnDWM: cannot own notification service: %s\n",
            error.message ? error.message : "another daemon owns it");
    dbus_error_free(&error);
    dbus_connection_unref(notify_conn);
    notify_conn = NULL;
    return;
  }
  dbus_connection_add_filter(notify_conn, notification_message, NULL, NULL);
  dbus_connection_read_write(notify_conn, 0);
  if (!dbus_connection_get_unix_fd(notify_conn, &notify_fd))
    notify_fd = -1;
  dbus_connection_set_exit_on_disconnect(notify_conn, FALSE);
  dbus_error_free(&error);
}

static void notification_shutdown(void) {
  Notification *n, *next;
  for (n = notify_current; n; n = next) {
    next = n->next;
    notification_free(n);
  }
  for (n = notify_head; n; n = next) {
    next = n->next;
    notification_free(n);
  }
  for (n = notify_history_head; n; n = next) {
    next = n->next;
    notification_free(n);
  }
  notify_current = notify_head = notify_tail = NULL;
  notify_history_head = notify_history_tail = NULL;
  notify_history_count = 0;
  if (notify_conn) {
    dbus_bus_release_name(notify_conn, "org.freedesktop.Notifications", NULL);
    dbus_connection_remove_filter(notify_conn, notification_message, NULL);
    dbus_connection_unref(notify_conn);
    notify_conn = NULL;
  }
}

void getkblayout(void) {
  /* Read _XKB_RULES_NAMES to get raw layout codes like "us,th" */
  Atom xkbRulesNames = XInternAtom(dpy, "_XKB_RULES_NAMES", True);
  if (xkbRulesNames) {
    Atom actual_type;
    int actual_format;
    unsigned long nitems, bytes_after;
    unsigned char *prop = NULL;
    if (XGetWindowProperty(dpy, root, xkbRulesNames, 0, 1024, False,
                           XA_STRING, &actual_type, &actual_format,
                           &nitems, &bytes_after, &prop) == Success
        && actual_type == XA_STRING && nitems > 0) {
      /* Prop contains: rules\0model\0layout\0variant\0options (null-separated) */
      int entry = 0;
      char *p = (char *)prop;
      char *layout_start = NULL;
      while (*p && entry < 3) {
        if (entry == 2) {
          layout_start = p;
          break;
        }
        /* skip to next null-terminated string */
        while (*p) p++;
        p++; /* skip null */
        entry++;
      }
      if (layout_start) {
        /* layout_start now points to "us,th" or similar */
        XkbStateRec state;
        if (XkbGetState(dpy, XkbUseCoreKbd, &state) == Success) {
          int group = state.group;
          /* Split layout_start by comma and pick group index */
          char *saveptr;
          char *token;
          int idx = 0;
          char *tmp = strdup(layout_start);
          if (tmp) {
            token = strtok_r(tmp, ",", &saveptr);
            while (token) {
              if (idx == group) {
                size_t len = strlen(token);
                if (len < sizeof(kbstr))
                  strcpy(kbstr, token);
                break;
              }
              token = strtok_r(NULL, ",", &saveptr);
              idx++;
            }
            free(tmp);
          }
        }
      }
      XFree(prop);
    }
  }
  /* Fallback: if kbstr is empty */
  if (kbstr[0] == '\0')
    strcpy(kbstr, "us");
}

unsigned int kblayoutwidth(void) {
  return TEXTW(kbstr) - lrpad + 2 * kblayoutpad;
}

static void barwidths(Monitor *m, unsigned int *tw, unsigned int *tlw,
                      unsigned int *cw, unsigned int *kw, unsigned int *rw) {
  unsigned int avail, barW, stw = 0, stgap = 0;
  if (showsystray && m == systraytomon(m)) {
    stw = getsystraywidth();
    if (stw)
      stgap = bargap;
  }
  barW = (floatbar ? m->ww - 2 * m->gappov : m->ww) - stw;
  *rw = statuswidth(stext);
  clockbar_cw = clockwidth();
  /* Notifications participate in the bar layout and push the other bar
   * sections aside.  The visualizer is an overlay: its animated width must
   * not change the layout of the title, keyboard, or status sections. */
   *cw = (notification_center_active() && m == selmon) ? notify_width : clockbar_cw;
  *kw = kblayoutwidth();
  *tw = tagsbarwidth(m);
  avail = (barW > *tw + *rw + *cw + *kw + 4 * bargap + stgap)
              ? barW - *tw - *rw - *cw - *kw - 4 * bargap - stgap
              : 0;
  *tlw = borderpx + bartitlewidth(m, avail > borderpx ? avail - borderpx : 0);
  if (*tlw > avail)
    *tlw = avail;
}

void drawbar(Monitor *m) {
  int y = borderpx;
  int bh_n = bh - borderpx * 2;
  int boxs = drw->fonts->h / 9;
  int boxw = drw->fonts->h / 6 + 2;
  int x, w;
  unsigned int i, occ = 0, urg = 0;
  unsigned int tw, tlw, cw, kw, rw;
  Client *c;

  if (!m->showbar) {
    if (m == selmon)
      clockbar_win = 0;
    return;
  }

  for (c = m->clients; c; c = c->next) {
    occ |= (c->issticky ? c->oldtags : c->tags);
    if (c->isurgent)
      urg |= (c->issticky ? c->oldtags : c->tags);
  }

  barwidths(m, &tw, &tlw, &cw, &kw, &rw);
  resizebarwin(m);

  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, tw, bh);

  /* tags bar: tags + layout indicator, fixed size */
  x = borderpx;
  for (i = 0; i < LENGTH(tags); i++) {
    w = TEXTW(tags[i]);
    drw_setscheme(
        drw, scheme[occ & 1 << i ? (m->colorfultag ? tagschemes[i] : SchemeSel)
                                 : SchemeTag]);
    drw_text(drw, x, y, w, bh_n, lrpad / 2, tags[i], urg & 1 << i);
    if (ulineall ||
        m->tagset[m->seltags] &
            1 << i) /* if there are conflicts, just move these lines directly
                       underneath both 'drw_setscheme' and 'drw_text' :) */
      drw_rect(drw, x + ulinepad, bh_n - ulinestroke - ulinevoffset,
               w - (ulinepad * 2), ulinestroke, 1, 0);
    x += w;
  }
  w = TEXTW(m->ltsymbol);
  drw_setscheme(drw, scheme[SchemeLayout]);
  drw_text(drw, x, 0, w, bh, lrpad / 2, m->ltsymbol, 0);
  drw_map(drw, m->barwin, 0, 0, tw, bh);

  /* title bar: arch logo + app icon + app name, dynamic size */
  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, tlw, bh);
  x = borderpx;
  for (i = 0; i < LENGTH(launchers); i++) {
    w = TEXTW(launchers[i].name);
    drw_setscheme(drw, scheme[SchemeLayout]);
    drw_text(drw, x, 0, w, bh, lrpad / 2, launchers[i].name, 0);
    x += w;
  }
  if (m->sel) {
    w = tlw - x;
    if (w > 0) {
      drw_setscheme(drw, scheme[m == selmon ? SchemeTitle : SchemeNorm]);
      drw_text(drw, x, 0, w, bh,
               lrpad / 2 + (m->sel->icon ? m->sel->icw + ICONSPACING : 0),
               m->sel->name, 0);
      if (m->sel->icon)
        drw_pic(drw, x + lrpad / 2, (bh - m->sel->ich) / 2, m->sel->icw,
                m->sel->ich, m->sel->icon);
      if (m->sel->isfloating)
        drw_rect(drw, x + boxs, boxs, boxw, boxw, m->sel->isfixed, 0);
    }
  }
  drw_map(drw, m->bartitlewin, 0, 0, tlw, bh);

  /* center bar: clock in normal mode, notification panel when active */
   unsigned int dcw = (notification_center_active() && m == selmon) ? notify_width
                                     : ((clockbar_dynw && !notify_clock_hovered &&
                                         !fullscreen_st && m == selmon)
                                           ? clockbar_dynw : cw);
  unsigned int tcw = clockbar_cw;
  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, dcw, bh);
   if (notify_active && m == selmon) {
     notification_draw();
     drw_map(drw, m->barcenterwin, 0, 0, notify_width, notify_height);
   } else if (notify_history_active && m == selmon) {
     notification_history_draw();
     drw_map(drw, m->barcenterwin, 0, 0, notify_width, notify_height);
  } else {
    drw_setscheme(drw, scheme[m == selmon ? SchemeTitle : SchemeNorm]);
    drw_rect(drw, 0, borderpx, dcw, bh_n, 1, 1);
    drw_text(drw, dcw > tcw ? (int)((dcw - tcw) / 2) : 0,
             borderpx + vertpadbar / 2, tcw, bh - vertpadbar, clockpad, clockstr,
             0);
    drw_map(drw, m->barcenterwin, 0, 0, dcw, bh);
  }

  /* center bar: keyboard layout */
  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, kw, bh);
  drw_setscheme(drw, scheme[m == selmon ? SchemeTitle : SchemeNorm]);
  drw_rect(drw, 0, borderpx, kw, bh_n, 1, 1);
  drw_text(drw, 0, borderpx + vertpadbar / 2, kw, bh - vertpadbar, kblayoutpad,
           kbstr, 0);
  drw_map(drw, m->barkbwin, 0, 0, kw, bh);

  /* right bar: status produced by the lock-free worker */
  drawstatusbar(m, bh_n, stext);
  drw_map(drw, m->barrightwin, 0, 0, rw, bh);
}

static uint32_t prealpha(uint32_t p) {
  uint8_t a = p >> 24u;
  uint32_t rb = (a * (p & 0xFF00FFu)) >> 8u;
  uint32_t g = (a * (p & 0x00FF00u)) >> 8u;
  return (rb & 0xFF00FFu) | (g & 0x00FF00u) | (a << 24u);
}

Picture geticonprop(Window win, unsigned int *picw, unsigned int *pich, unsigned int *pw, unsigned int *ph) {
  int format;
  unsigned long n, extra, *p = NULL;
  Atom real;

  if (XGetWindowProperty(dpy, win, netatom[NetWMIcon], 0L, LONG_MAX, False,
                         AnyPropertyType, &real, &format, &n, &extra,
                         (unsigned char **)&p) != Success)
    return None;
  if (n == 0 || format != 32) {
    XFree(p);
    return None;
  }

  unsigned long *bstp = NULL;
  uint32_t w, h, sz;
  {
    unsigned long *i;
    const unsigned long *end = p + n;
    uint32_t bstd = UINT32_MAX, d, m;
    for (i = p; i < end - 1; i += sz) {
      if ((w = *i++) >= 16384 || (h = *i++) >= 16384) {
        XFree(p);
        return None;
      }
      if ((sz = w * h) > end - i)
        break;
      if ((m = w > h ? w : h) >= ICONSIZE && (d = m - ICONSIZE) < bstd) {
        bstd = d;
        bstp = i;
      }
    }
    if (!bstp) {
      for (i = p; i < end - 1; i += sz) {
        if ((w = *i++) >= 16384 || (h = *i++) >= 16384) {
          XFree(p);
          return None;
        }
        if ((sz = w * h) > end - i)
          break;
        if ((d = ICONSIZE - (w > h ? w : h)) < bstd) {
          bstd = d;
          bstp = i;
        }
      }
    }
    if (!bstp) {
      XFree(p);
      return None;
    }
  }

  if ((w = *(bstp - 2)) == 0 || (h = *(bstp - 1)) == 0) {
    XFree(p);
    return None;
  }

  uint32_t icw, ich;
  if (w <= h) {
    ich = ICONSIZE;
    icw = w * ICONSIZE / h;
    if (icw == 0)
      icw = 1;
  } else {
    icw = ICONSIZE;
    ich = h * ICONSIZE / w;
    if (ich == 0)
      ich = 1;
  }
  *picw = icw;
  *pich = ich;

  uint32_t i, *bstp32 = (uint32_t *)bstp;
  for (sz = w * h, i = 0; i < sz; ++i)
    bstp32[i] = prealpha(bstp[i]);

  Picture ret = drw_picture_create_resized(drw, (char *)bstp, w, h, icw, ich);
  if (ret) {
    if (w <= 2 * icw && h <= 2 * ich) {
      *pw = w; *ph = h; /* XRender path: picture pixmap at original source size */
    } else {
      *pw = icw; *ph = ich; /* Imlib2 path: picture pixmap at target size */
    }
  } else {
    *pw = 0; *ph = 0;
  }
  XFree(p);

  return ret;
}

void drawbars(void) {
  Monitor *m;

  for (m = mons; m; m = m->next)
    drawbar(m);
}

void drawtabs(void) {
  Monitor *m;

  for (m = mons; m; m = m->next)
    drawtab(m);
}

static int cmpint(const void *p1, const void *p2) {
  /* The actual arguments to this function are "pointers to
     pointers to char", but strcmp(3) arguments are "pointers
     to char", hence the following cast plus dereference */
  return *((int *)p1) > *(int *)p2;
}

void drawtab(Monitor *m) {
  Client *c;
  int i;
  char *btn_prev = "";
  char *btn_next = "";
  char *btn_close = " ";
  int buttons_w = 0;
  int sorted_label_widths[MAXTABS];
  int tot_width = 0;
  int maxsize = bh;
  int x = 0;
  int w = 0;
  int mw = floatbar ? m->ww - 2 * m->gappov : m->ww;
  buttons_w += TEXTW(btn_prev) - lrpad + horizpadtabo;
  buttons_w += TEXTW(btn_next) - lrpad + horizpadtabo;
  buttons_w += TEXTW(btn_close) - lrpad + horizpadtabo;
  tot_width = buttons_w;

  /* Calculates number of labels and their width */
  m->ntabs = 0;
  for (c = m->clients; c; c = c->next) {
    if (!ISVISIBLE(c))
      continue;
    m->tab_widths[m->ntabs] =
        MIN(TEXTW(c->name) - lrpad + horizpadtabi + horizpadtabo, 250);
    tot_width += m->tab_widths[m->ntabs];
    ++m->ntabs;
    if (m->ntabs >= MAXTABS)
      break;
  }

  if (tot_width >
      mw) { // not enough space to display the labels, they need to be truncated
    memcpy(sorted_label_widths, m->tab_widths, sizeof(int) * m->ntabs);
    qsort(sorted_label_widths, m->ntabs, sizeof(int), cmpint);
    for (i = 0; i < m->ntabs; ++i) {
      if (tot_width + (m->ntabs - i) * sorted_label_widths[i] > mw)
        break;
      tot_width += sorted_label_widths[i];
    }
    maxsize = (mw - tot_width) / (m->ntabs - i);
    maxsize = (m->ww - tot_width) / (m->ntabs - i);
  } else {
    maxsize = mw;
  }
  i = 0;

  /* cleans window */
  drw_setscheme(drw, scheme[TabNorm]);
  drw_rect(drw, 0, 0, mw, th, 1, 1);

  for (c = m->clients; c; c = c->next) {
    if (!ISVISIBLE(c))
      continue;
    if (i >= m->ntabs)
      break;
    if (m->tab_widths[i] > maxsize)
      m->tab_widths[i] = maxsize;
    w = m->tab_widths[i];
    drw_setscheme(drw, scheme[(c == m->sel) ? TabSel : TabNorm]);
    drw_text(drw, x + horizpadtabo / 2, vertpadbar / 2, w - horizpadtabo,
             th - vertpadbar, horizpadtabi / 2, c->name, 0);
    x += w;
    ++i;
  }

  w = mw - buttons_w - x;
  x += w;
  drw_setscheme(drw, scheme[SchemeBtnPrev]);
  w = TEXTW(btn_prev) - lrpad + horizpadtabo;
  m->tab_btn_w[0] = w;
  drw_text(drw, x + horizpadtabo / 2, vertpadbar / 2, w, th - vertpadbar, 0,
           btn_prev, 0);
  x += w;
  drw_setscheme(drw, scheme[SchemeBtnNext]);
  w = TEXTW(btn_next) - lrpad + horizpadtabo;
  m->tab_btn_w[1] = w;
  drw_text(drw, x + horizpadtabo / 2, vertpadbar / 2, w, th - vertpadbar, 0,
           btn_next, 0);
  x += w;
  drw_setscheme(drw, scheme[SchemeBtnClose]);
  w = TEXTW(btn_close) - lrpad + horizpadtabo;
  m->tab_btn_w[2] = w;
  drw_text(drw, x + horizpadtabo / 2, vertpadbar / 2, w, th - vertpadbar, 0,
           btn_close, 0);
  x += w;

  drw_map(drw, m->tabwin, 0, 0, m->ww, th);
}

void calcsidebar(Monitor *m) {
  Client *c;
  int cnt = 0;
  for (c = m->clients; c; c = c->next)
    if (ISVISIBLE(c) && !HIDDEN(c))
      cnt++;

  if (cnt == 0) {
    m->sidebarh = m->mh / 3;
    m->sidebarw = SIDEBAR_WIDTH;
    return;
  }

  int base;
  if (cnt > 7) {
    base = 30;
    m->sidebarw = 48;
  } else if (cnt > 3) {
    base = 42;
    m->sidebarw = SIDEBAR_WIDTH;
  } else {
    base = 48;
    m->sidebarw = SIDEBAR_WIDTH;
  }

  m->sidebarh = cnt * base + 8;
  if (m->sidebarh > m->mh * 2 / 5)
    m->sidebarh = m->mh * 2 / 5;
  if (m->sidebarh < 50)
    m->sidebarh = 50;
}

void drawsidebar(Monitor *m) {
  if (!m->sidebarvisible)
    return;

  Client *c;
  int count = 0;
  Client *visible[MAXTABS];

  for (c = m->clients; c; c = c->next) {
    if (ISVISIBLE(c) && !HIDDEN(c)) {
      visible[count++] = c;
      if (count >= MAXTABS)
        break;
    }
  }

  if (!count) {
    XUnmapWindow(dpy, m->sidebarwin);
    m->sidebarvisible = 0;
    return;
  }

  calcsidebar(m);
  int sh = m->sidebarh;
  int sw = m->sidebarw;

  /* reposition window to centered y */
  int sidebary = m->my + (m->mh - sh) / 2;
  XMoveResizeWindow(dpy, m->sidebarwin, m->mx + m->gappov * 2, sidebary, sw, sh);

  int margin = 6;
  int pad = 4;
  int content_h = sh - 2 * margin;
  int itemh = (content_h - pad * (count - 1)) / count;

  /* find current workspace tag color index */
  int tagcolor_idx = SchemeTag1;
  for (int t = 0; t < LENGTH(tags); t++) {
    if (m->tagset[m->seltags] & (1 << t)) {
      tagcolor_idx = tagschemes[t];
      break;
    }
  }

  /* clear background */
  drw_setscheme(drw, scheme[SchemeNorm]);
  drw_rect(drw, 0, 0, sw, sh, 1, 1);

  for (int i = 0; i < count; i++) {
    c = visible[i];
    int y = margin + i * (itemh + pad);

    /* focus indicator — only for current focus, small indicator */
    if (c == m->sel) {
      drw_setscheme(drw, scheme[tagcolor_idx]);
      drw_rect(drw, 2, y + itemh / 2 - 5, 3, 10, 1, 0);
    }

    /* draw app icon if available */
    if (c->icon && c->icw > 0 && c->ic_pw > 0) {
      int icon_h = itemh - pad;
      if (icon_h > sw - 2 * margin) icon_h = sw - 2 * margin;
      if (icon_h < 16) icon_h = 16;
      int icon_y = y + (itemh - icon_h) / 2;
      int icon_x = (sw - icon_h) / 2;
      /* set sidebar-scale transform */
      XTransform xf;
      xf.matrix[0][0] = (c->ic_pw << 16) / icon_h;
      xf.matrix[0][1] = 0; xf.matrix[0][2] = 0;
      xf.matrix[1][0] = 0; xf.matrix[1][1] = (c->ic_ph << 16) / icon_h;
      xf.matrix[1][2] = 0;
      xf.matrix[2][0] = 0; xf.matrix[2][1] = 0; xf.matrix[2][2] = 65536;
      XRenderSetPictureTransform(drw->dpy, c->icon, &xf);
      drw_pic(drw, icon_x, icon_y, icon_h, icon_h, c->icon);
      /* restore original transform */
      xf.matrix[0][0] = (c->ic_pw << 16) / c->icw;
      xf.matrix[1][1] = (c->ic_ph << 16) / c->ich;
      XRenderSetPictureTransform(drw->dpy, c->icon, &xf);
    } else {
      /* fallback */
      drw_setscheme(drw, scheme[c == m->sel ? SchemeSel : SchemeNorm]);
      drw_rect(drw, 4, y + 2, itemh - 4, itemh - 4, 1, 0);
    }
  }

  drw_map(drw, m->sidebarwin, 0, 0, sw, sh);
}

void drawsidbars(void) {
  Monitor *m;
  for (m = mons; m; m = m->next)
    drawsidebar(m);
}

void showsidbar(Monitor *m) {
  Client *c;
  int count = 0;
  /* only show if there are visible apps */
  for (c = m->clients; c; c = c->next)
    if (ISVISIBLE(c) && !HIDDEN(c)) {
      count++;
      break;
    }
  if (!count) {
    hideosidebar(m);
    return;
  }
  if (!m->sidebarvisible) {
    m->sidebarvisible = 1;
    XMapWindow(dpy, m->sidebarwin);
    XRaiseWindow(dpy, m->sidebarwin);
    drawsidebar(m);
  }
}

void hideosidebar(Monitor *m) {
  if (m->sidebarvisible) {
    m->sidebarvisible = 0;
    XUnmapWindow(dpy, m->sidebarwin);
  }
}

void alttab(const Arg *arg) {
  static int alttab_idx = 0;
  static int alttab_count = 0;
  static Client *alttab_list[MAXTABS];
  int forward = arg->i;
  Client *c;

  /* build candidate list */
  alttab_count = 0;
  for (c = selmon->clients; c; c = c->next)
    if (ISVISIBLE(c) && !HIDDEN(c))
      alttab_list[alttab_count++] = c;

  if (alttab_count == 0)
    return;

  alttab_idx = (alttab_idx + forward + alttab_count) % alttab_count;
  focus(alttab_list[alttab_idx]);
  showsidbar(selmon);
  drawsidebar(selmon);
}

void enternotify(XEvent *e) {
  Client *c;
  Monitor *m;
  XCrossingEvent *ev = &e->xcrossing;

  if (ev->window == selmon->barcenterwin) {
    if (!notification_center_active() &&
        !notification_clock_hit(ev->x,
                                clockbar_dynw ? clockbar_dynw : clockbar_cw))
      return;
    notify_clock_hovered = 1;
    if (notify_active)
      notification_set_hovered(1);
    else if (!notify_transition_pending && notify_history_count)
      notification_history_show();
    return;
  }
  if ((ev->mode != NotifyNormal || ev->detail == NotifyInferior) &&
      ev->window != root)
    return;
  c = wintoclient(ev->window);
  m = c ? c->mon : wintomon(ev->window);
  if (m != selmon) {
    unfocus(selmon->sel, 1);
    selmon = m;
  } else if (!c || c == selmon->sel)
    return;
  focus(c);
}

static void leavenotify(XEvent *e) {
  XCrossingEvent *ev = &e->xcrossing;

  if (ev->window == selmon->barcenterwin) {
    notify_clock_hovered = 0;
    if (notify_active)
      notification_set_hovered(0);
    if (notify_history_active)
      notification_history_hide();
    notify_hover = -1;
    if (notify_active)
      drawbars();
  }
}

void expose(XEvent *e) {
  Monitor *m;
  XExposeEvent *ev = &e->xexpose;

  if (ev->count == 0 && (m = wintomon(ev->window))) {
    drawbar(m);
    if (m == selmon)
      updatesystray();
  }
}

void write_fullscreen(int value) {
  FILE *f = fopen("/tmp/isfullscreen", "w");
  if (!f)
    return;

  fprintf(f, "%d", value); // write 0 or 1
  fclose(f);
}

static volatile bool fullscreen_st = false;

static void updatefullscreenstatus(Client *c) {
  bool isfullscreen = c && c->isfullscreen && !c->issticky;

  if (fullscreen_st == isfullscreen)
    return;

  write_fullscreen(isfullscreen);
  fullscreen_st = isfullscreen;
}

void focus(Client *c) {
  if (!c || (!ISVISIBLE(c) || HIDDEN(c)))
    for (c = selmon->stack; c && (!ISVISIBLE(c) || HIDDEN(c) || c->issticky); c = c->snext)
      ;
  if (selmon->sel && selmon->sel != c)
    unfocus(selmon->sel, 0);
  if (c) {
    if (c->mon != selmon)
      selmon = c->mon;
    if (c->isurgent)
      seturgent(c, 0);
    detachstack(c);
    attachstack(c);
    grabbuttons(c, 1);
    XSetWindowBorder(dpy, c->win, scheme[SchemeSel][ColBorder].pixel);
    setfocus(c);
  } else {
    XSetInputFocus(dpy, root, RevertToPointerRoot, CurrentTime);
    XDeleteProperty(dpy, root, netatom[NetActiveWindow]);
  }
  selmon->sel = c;

  updatefullscreenstatus(c);

  drawbars();
  drawtabs();
  drawsidbars();
}

/* there are some broken focus acquiring clients needing extra handling */
void focusin(XEvent *e) {
  /* Let applications, especially Java, manage focus within their window. */
  (void)e;
}

void focusmon(const Arg *arg) {
  Monitor *m;

  if (!mons->next)
    return;
  if ((m = dirtomon(arg->i)) == selmon)
    return;
  unfocus(selmon->sel, 0);
  selmon = m;
  focus(NULL);
}

void focusstack(const Arg *arg) {
  Client *c = NULL, *i;

  if (!selmon->sel || (selmon->sel->isfullscreen && lockfullscreen))
    return;
  if (arg->i > 0) {
    for (c = selmon->sel->next;
         c && (!ISVISIBLE(c) || HIDDEN(c) || c->issticky); c = c->next)
      ;
    if (!c)
      for (c = selmon->clients;
           c && (!ISVISIBLE(c) || HIDDEN(c) || c->issticky); c = c->next)
        ;
  } else {
    for (i = selmon->clients; i != selmon->sel; i = i->next)
      if (ISVISIBLE(i) && !HIDDEN(i) && !i->issticky)
        c = i;
    if (!c)
      for (; i; i = i->next)
        if (ISVISIBLE(i) && !HIDDEN(i) && !i->issticky)
          c = i;
  }
  if (c) {
    focus(c);
    restack(selmon);
    XWarpPointer(dpy, None, c->win, 0, 0, 0, 0,
                 c->w / 2, c->h / 2);
    XFlush(dpy);
  }
}

void focuswin(const Arg *arg) {
  int iwin = arg->i;
  Client *c = NULL;
  for (c = selmon->clients; c && (iwin || !ISVISIBLE(c)); c = c->next) {
    if (ISVISIBLE(c) && !c->issticky)
      --iwin;
  };
  if (c) {
    focus(c);
    restack(selmon);
  }
}

Atom getatomprop(Client *c, Atom prop) {
  int di;
  unsigned long dl;
  unsigned char *p = NULL;
  Atom da, atom = None;
  /* FIXME getatomprop should return the number of items and a pointer to
   * the stored data instead of this workaround */
  Atom req = XA_ATOM;
  if (prop == xatom[XembedInfo])
    req = xatom[XembedInfo];

  if (XGetWindowProperty(dpy, c->win, prop, 0L, sizeof atom, False, req, &da,
                         &di, &dl, &dl, &p) == Success &&
      p) {
    atom = *(Atom *)p;
    if (da == xatom[XembedInfo] && dl == 2)
      atom = ((Atom *)p)[1];
    XFree(p);
  }
  return atom;
}

int getrootptr(int *x, int *y) {
  int di;
  unsigned int dui;
  Window dummy;

  return XQueryPointer(dpy, root, &dummy, &dummy, x, y, &di, &di, &dui);
}

long getstate(Window w) {
  int format;
  long result = -1;
  unsigned char *p = NULL;
  unsigned long n, extra;
  Atom real;

  if (XGetWindowProperty(dpy, w, wmatom[WMState], 0L, 2L, False,
                         wmatom[WMState], &real, &format, &n, &extra,
                         (unsigned char **)&p) != Success)
    return -1;
  if (n != 0)
    result = *p;
  XFree(p);
  return result;
}

unsigned int getsystraywidth() {
  unsigned int w = 0;
  Client *i;
  if (showsystray && systray)
    for (i = systray->icons; i; w += i->w + systrayspacing, i = i->next)
      ;
  return w ? w + systrayspacing : 0;
}

int gettextprop(Window w, Atom atom, char *text, unsigned int size) {
  char **list = NULL;
  int n;
  XTextProperty name;

  if (!text || size == 0)
    return 0;
  text[0] = '\0';
  if (!XGetTextProperty(dpy, w, &name, atom) || !name.nitems)
    return 0;
  if (name.encoding == XA_STRING) {
    strncpy(text, (char *)name.value, size - 1);
  } else if (XmbTextPropertyToTextList(dpy, &name, &list, &n) >= Success &&
             n > 0 && *list) {
    strncpy(text, *list, size - 1);
    XFreeStringList(list);
  }
  text[size - 1] = '\0';
  XFree(name.value);
  return 1;
}

void grabbuttons(Client *c, int focused) {
  updatenumlockmask();
  {
    unsigned int i, j;
    unsigned int modifiers[] = {0, LockMask, numlockmask,
                                numlockmask | LockMask};
    XUngrabButton(dpy, AnyButton, AnyModifier, c->win);
    if (!focused)
      XGrabButton(dpy, AnyButton, AnyModifier, c->win, False, BUTTONMASK,
                  GrabModeAsync, GrabModeAsync, None, None);
    for (i = 0; i < LENGTH(buttons); i++)
      if (buttons[i].click == ClkClientWin)
        for (j = 0; j < LENGTH(modifiers); j++)
          XGrabButton(dpy, buttons[i].button, buttons[i].mask | modifiers[j],
                      c->win, False, BUTTONMASK, GrabModeAsync, GrabModeAsync,
                      None, None);
  }
}

void grabkeys(void) {
  updatenumlockmask();
  {
    unsigned int i, j, k;
    unsigned int modifiers[] = {0, LockMask, numlockmask,
                                numlockmask | LockMask};
    int start, end, skip;
    KeySym *syms;
    XUngrabKey(dpy, AnyKey, AnyModifier, root);
    XDisplayKeycodes(dpy, &start, &end);
    syms = XGetKeyboardMapping(dpy, start, end - start + 1, &skip);
    if (!syms)
      return;
    for (k = start; k <= end; k++)
      for (i = 0; i < LENGTH(keys); i++)
        /* skip modifier codes, we do that ourselves */
        if (keys[i].keysym == syms[(k - start) * skip])
          for (j = 0; j < LENGTH(modifiers); j++)
            XGrabKey(dpy, k, keys[i].mod | modifiers[j], root, True,
                     GrabModeAsync, GrabModeAsync);
    XFree(syms);
  }
}

void freeicon(Client *c) {
  if (c->icon) {
    XRenderFreePicture(dpy, c->icon);
    c->icon = None;
  }
}

/* Centralized show/hide of a managed client. Keeps the internal isiconic
 * flag, the wm_unmapped guard and the X server state consistent so that
 * focus()/showhide() never depend on stale X round-trips. */
static void xmapclient(Client *c) {
  if (!c)
    return;
  /* Discard stale UnmapNotify events generated by our own XUnmapWindow
   * calls; client-initiated unmaps (send_event) are put back. */
  XEvent ev;
  while (XCheckTypedWindowEvent(dpy, c->win, UnmapNotify, &ev)) {
    if (ev.xunmap.send_event) {
      XPutBackEvent(dpy, &ev);
      break;
    }
  }
  c->isiconic = 0;
  c->wm_unmapped = 0;
  XMapWindow(dpy, c->win);
  if (shouldminimize(c))
    setclientstate(c, NormalState);
  grabbuttons(c, 0);
  XSync(dpy, False);
}

static void xunmapclient(Client *c) {
  if (!c)
    return;
  c->isiconic = 1;
  c->wm_unmapped = 1;
  if (shouldminimize(c))
    setclientstate(c, IconicState);
  XUnmapWindow(dpy, c->win);
}

void hide(Client *c) {
  if (!c || HIDDEN(c))
    return;

  xunmapclient(c);

  if (ISVISIBLE(c)) {
    focus(NULL);
    arrange(c->mon);
  }
}

int shouldminimize(Client *c) {
  Atom *states = NULL;
  Atom actual;
  int format;
  unsigned long n, extra;
  unsigned long i;
  int result = 1;

  if (!c || !c->win)
    return 0;

  if (XGetWindowProperty(dpy, c->win, netatom[NetWMState], 0L, LONG_MAX,
                         False, XA_ATOM, &actual, &format, &n, &extra,
                         (unsigned char **)&states) != Success)
    return 1;

  /* Skip taskbar windows are often special/helper windows that should not be
   * sent through the minimize state transition during tag changes. */
  for (i = 0; i < n; i++)
    if (states[i] == netatom[NetWMSkipTaskbar]) {
      result = 0;
      goto done;
    }

done:
  XFree(states);
  return result;
}

void incnmaster(const Arg *arg) {
  selmon->nmaster = selmon->pertag->nmasters[selmon->pertag->curtag] =
      MAX(selmon->nmaster + arg->i, 0);
  arrange(selmon);
}

#ifdef XINERAMA
static int isuniquegeom(XineramaScreenInfo *unique, size_t n,
                        XineramaScreenInfo *info) {
  while (n--)
    if (unique[n].x_org == info->x_org && unique[n].y_org == info->y_org &&
        unique[n].width == info->width && unique[n].height == info->height)
      return 0;
  return 1;
}
#endif /* XINERAMA */

void keypress(XEvent *e) {
  unsigned int i;
  KeySym keysym;
  XKeyEvent *ev;

  ev = &e->xkey;
  keysym = XKeycodeToKeysym(dpy, (KeyCode)ev->keycode, 0);

  /* only KeyPress triggers normal keybindings (avoid double-fire on KeyRelease) */
  if (ev->type != KeyPress)
    return;
  if (notification_input_keypress(ev))
    return;

  for (i = 0; i < LENGTH(keys); i++)
    if (keysym == keys[i].keysym &&
        CLEANMASK(keys[i].mod) == CLEANMASK(ev->state) && keys[i].func) {
      if (dragclient && keys[i].func == view && (keys[i].arg.ui & TAGMASK)) {
        dragclient->tags = keys[i].arg.ui & TAGMASK;
        setclienttagprop(dragclient);
      }

      keys[i].func(&(keys[i].arg));
    }
}

int countwindows(void) {
  Client *c;
  int count = 0;

  for (c = selmon->clients; c; c = c->next) {
    if (ISVISIBLE(c)) // only count windows visible on current tag
      count++;
  }

  return count;
}

int picom_state = 0;
const char *class_name; // Renamed to avoid confusion with C++ 'class' keyword
static Display *cached_dpy = NULL;
static Window cached_win = 0;
static int cached_valid = 0;

int haswindowproperty(Client *c, Atom prop) {
  Atom actual;
  int format;
  unsigned long n, extra;
  unsigned char *data = NULL;
  int exists = 0;

  if (!c || !c->win || prop == None)
    return 0;

  if (XGetWindowProperty(dpy, c->win, prop, 0L, 0L, False, AnyPropertyType,
                         &actual, &format, &n, &extra, &data) == Success)
    exists = actual != None;

  if (data)
    XFree(data);

  return exists;
}

void
set_bypass_compositor(Client *c, unsigned long val)
{
  if (!c || !c->win || netatom[NetWMBypassCompositor] == None)
    return;
  XChangeProperty(dpy, c->win, netatom[NetWMBypassCompositor], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)&val, 1);
}

static int
get_bypass_compositor_value(Client *c)
{
  Atom actual;
  int format;
  unsigned long n, extra;
  unsigned char *data = NULL;
  int value = 0;

  if (!c || !c->win || netatom[NetWMBypassCompositor] == None)
    return 0;

  if (XGetWindowProperty(dpy, c->win, netatom[NetWMBypassCompositor],
                         0L, 1L, False, XA_CARDINAL, &actual, &format, &n,
                         &extra, &data) == Success && actual != None && data)
    value = *(unsigned long *)data;
  if (data)
    XFree(data);
  return value;
}

static void
sync_bypass_compositor(Client *c)
{
  if (!c || !c->win || netatom[NetWMBypassCompositor] == None)
    return;

  if (c->isfullscreen) {
    if (get_bypass_compositor_value(c) != 1)
      set_bypass_compositor(c, 1);
  } else {
    XDeleteProperty(dpy, c->win, netatom[NetWMBypassCompositor]);
  }
}

int window_has_transparency(Client *c) {
  if (!c || !c->win)
    return 0;
  if (get_bypass_compositor_value(c) == 2)
    return 1;
  if (transparent_fullscreen_classes[0]) {
    XClassHint ch = {NULL, NULL};
    if (XGetClassHint(dpy, c->win, &ch) && ch.res_class) {
      for (int i = 0; transparent_fullscreen_classes[i]; i++) {
        if (strcmp(ch.res_class, transparent_fullscreen_classes[i]) == 0) {
          XFree(ch.res_class);
          if (ch.res_name) XFree(ch.res_name);
          return 1;
        }
      }
    }
    if (ch.res_class) XFree(ch.res_class);
    if (ch.res_name) XFree(ch.res_name);
  }
  return 0;
}

void setwindowopacity(Client *c) {
  unsigned long value = 0xffffffffUL;

  if (!c || !c->win || netatom[NetWMWindowOpacity] == None ||
      haswindowproperty(c, netatom[NetWMBypassCompositor]))
    return;

  XChangeProperty(dpy, c->win, netatom[NetWMWindowOpacity], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)&value, 1);
}

void clearwindowopacity(Client *c) {
  if (!c || !c->win || netatom[NetWMWindowOpacity] == None)
    return;

  XDeleteProperty(dpy, c->win, netatom[NetWMWindowOpacity]);
}

void togglepicom(const Arg *arg) {
  if (netatom[NetWMWindowOpacity] == None)
    return;

  if (picom_state == 0) {
    Client *c = selmon->sel;
    if (!c || !c->win)
      return;

    // Cache values
    cached_dpy = dpy;
    cached_win = c->win;
    cached_valid = 1;

    setwindowopacity(c);

    picom_state = 1;

  } else {
    if (!cached_valid)
      return;

    XWindowAttributes wa;
    if (!XGetWindowAttributes(cached_dpy, cached_win, &wa)) {
      cached_valid = 0;
      return;
    }

    XDeleteProperty(cached_dpy, cached_win, netatom[NetWMWindowOpacity]);

    // Reset cache (important!)
    cached_valid = 0;
    cached_win = 0;
    cached_dpy = NULL;

    picom_state = 0;
  }
}

// Example of fullscreen function
/*
void togglefullscr(const Arg *arg) {
  if (selmon->sel)
    setfullscreen(selmon->sel, !selmon->sel->isfullscreen);
}
*/

//    unsigned stick_state;
//    void togglesticky(const Arg *arg){
//      if (!selmon || (!selmon->sel && !stickywin))
//        return;
//
//      if (!c)
//        return;
//
//      if (c->isfullscreen)
//        return;
//
//      if (!stickywin){
//        stickywin = c;
//        // Save state
//        stickywin->oldtags = c->tags;
//        // Visible on all tags
//        stickywin->tags = TAGMASK;
//        // Keep sticky windows tiled/managed, no fullscreen toggle on error
//        path setfullscreen(stickywin, 0); stickywin->issticky = 1;
//        stick_state=1;
//
//        // Move sticky window to bottom of stack so it does not cover others
//        detachstack(stickywin);
//        attachstack(stickywin);
//        XLowerWindow(dpy, stickywin->win);
//      } else {
//        stickywin->tags = stickywin->oldtags ? stickywin->oldtags :
//        selmon->tagset[selmon->seltags]; setfullscreen(stickywin, 0);
//        stickywin->issticky = 0;
//        stick_state=0;
//
//        stickywin = NULL; /* assignment, not comparison */
//        arrange(selmon);
//      }
//    }
// Global enviroment to store client name
static Client *stickywin = NULL;
unsigned stick_state;
void togglesticky(Client *c, int fullscreen) {
  if (!c || c->isfullscreen)
    return;

  /* 1. If a DIFFERENT window is already sticky, unstick it first */
  if (stickywin && stickywin != c) {
    stickywin->isfloating = stickywin->wasfloating;
    stickywin->tags = stickywin->oldtags;
    stickywin->issticky = 0;

    /* Restore original geometry */
    resizeclient(stickywin, stickywin->prevx, stickywin->prevy,
                 stickywin->prevw, stickywin->prevh);

    /* Remove EWMH Fullscreen state */
    XChangeProperty(dpy, stickywin->win, netatom[NetWMState], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)0, 0);
    clearwindowopacity(stickywin);

    detachstack(stickywin);
    attachstack(stickywin);
    stickywin->fshidden = 0;
    XRaiseWindow(dpy, stickywin->win);

    stickywin = NULL;
    /* After unsticking the old one, we continue below to stick the new one */
  }

  /* 2. Toggle the current window 'c' */
  if (!stickywin) {
    /* Make it Sticky */
    stickywin = c;
    stickywin->issticky = 1;
    stickywin->wasfloating = stickywin->isfloating;

    /* Save state */
    stickywin->oldtags = stickywin->tags;
    stickywin->prevx = stickywin->x;
    stickywin->prevy = stickywin->y;
    stickywin->prevw = stickywin->w;
    stickywin->prevh = stickywin->h;

    stickywin->isfloating = 1;
    stickywin->tags = TAGMASK;

    /* Set EWMH state to Fullscreen so other windows don't overlap it easily */
    XChangeProperty(dpy, stickywin->win, netatom[NetWMState], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)&netatom[NetWMFullscreen],
                    1);
    setwindowopacity(stickywin);

    /* Resize to fill the monitor */
    resizeclient(stickywin, stickywin->mon->mx - borderpx, stickywin->mon->my - borderpx,
                 stickywin->mon->mw, stickywin->mon->mh);

    detachstack(stickywin);
    attachstack(stickywin);
    XLowerWindow(dpy, stickywin->win);
  } else {
    /* 1. Reset EWMH first */
    XChangeProperty(dpy, stickywin->win, netatom[NetWMState], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)0, 0);
    clearwindowopacity(stickywin);

    /* 2. Restore the floating status */
    stickywin->isfloating = stickywin->wasfloating;
    stickywin->tags = stickywin->oldtags;
    stickywin->issticky = 0;
    stickywin->isfullscreen = 0;

    /* 3. Explicitly move the client's variables back to old state */
    stickywin->x = stickywin->prevx;
    stickywin->y = stickywin->prevy;
    stickywin->w = stickywin->prevw;
    stickywin->h = stickywin->prevh;

    /* 4. Now call resize to tell X11 where to put it */
    resizeclient(stickywin, stickywin->x, stickywin->y, stickywin->w,
                 stickywin->h);

    detachstack(stickywin);
    attachstack(stickywin);
    stickywin->fshidden = 0;
    XRaiseWindow(dpy, stickywin->win);

    stickywin = NULL;
  }

  /* Finalize layout */
  focus(NULL);
  if (c->mon)
    arrange(c->mon);
}

void togglestickyclient(const Arg *arg) {
  /* if sticky window exists, always just toggle it off */
  if (stickywin) {
    togglesticky(stickywin, stickywin->isfullscreen);
    return;
  }

  /* if no sticky window, make current focused window sticky */
  Client *c = selmon->sel;
  if (!c)
    return;

  togglesticky(c, c->isfullscreen);
}

void killclient(const Arg *arg) {
  if (!selmon->sel)
    return;
  if (!sendevent(selmon->sel->win, wmatom[WMDelete], NoEventMask,
                 wmatom[WMDelete], CurrentTime, 0, 0, 0)) {
    XGrabServer(dpy);
    XSetErrorHandler(xerrordummy);
    XSetCloseDownMode(dpy, DestroyAll);
    XKillClient(dpy, selmon->sel->win);
   XSync(dpy, False);
    XSetErrorHandler(xerror);
    XUngrabServer(dpy);
  }
}

void forcekillclient(const Arg *arg) {
  if (!selmon->sel || selmon->sel->issticky)
    return;

  XGrabServer(dpy);
  XSetErrorHandler(xerrordummy);
  XSetCloseDownMode(dpy, DestroyAll);
  XKillClient(dpy, selmon->sel->win);
  XSync(dpy, False);
  XSetErrorHandler(xerror);
  XUngrabServer(dpy);
}

void manage(Window w, XWindowAttributes *wa) {
  Client *c, *t = NULL;
  Window trans = None;
  XWindowChanges wc;

  c = ecalloc(1, sizeof(Client));
  c->win = w;
  /* geometry */
  c->x = c->oldx = wa->x;
  c->y = c->oldy = wa->y;
  c->w = c->oldw = wa->width;
  c->h = c->oldh = wa->height;
  c->oldbw = wa->border_width;
  c->cfact = 1.0;
  updateicon(c);
  updatetitle(c);

  if (XGetTransientForHint(dpy, w, &trans) && (t = wintoclient(trans))) {
    c->mon = t->mon;
    c->tags = t->tags;
  } else {
    c->mon = selmon;
    applyrules(c);
  }

  if (c->x + WIDTH(c) > c->mon->wx + c->mon->ww)
    c->x = c->mon->wx + c->mon->ww - WIDTH(c);
  if (c->y + HEIGHT(c) > c->mon->wy + c->mon->wh)
    c->y = c->mon->wy + c->mon->wh - HEIGHT(c);
  c->x = MAX(c->x, c->mon->wx);
  c->y = MAX(c->y, c->mon->wy);
  c->bw = c->mon->borderpx;

  wc.border_width = c->bw;
  XConfigureWindow(dpy, w, CWBorderWidth, &wc);
  XSetWindowBorder(dpy, w, scheme[SchemeNorm][ColBorder].pixel);
  configure(c); /* propagates border_width, if size doesn't change */
  updatewindowtype(c);
  if (trans != None)
    c->isontop = DIALOG_ONTOP_PRIORITY;
  updatesizehints(c);
  updatewmhints(c);
  {
    int format;
    unsigned long *data, n, extra;
    Monitor *m;
    Atom atom;
    if (XGetWindowProperty(dpy, c->win, netatom[NetClientInfo], 0L, 2L, False,
                           XA_CARDINAL, &atom, &format, &n, &extra,
                           (unsigned char **)&data) == Success &&
        n == 2) {
      c->tags = *data;
      for (m = mons; m; m = m->next) {
        if (m->num == *(data + 1)) {
          c->mon = m;
          break;
        }
      }
    }
    if (n > 0)
      XFree(data);
  }
  setclienttagprop(c);

  if (c->iscentered) {
    c->x = c->mon->mx + (c->mon->mw - WIDTH(c)) / 2;
    c->y = c->mon->my + (c->mon->mh - HEIGHT(c)) / 2;
  }
  XSelectInput(dpy, w,
               EnterWindowMask | FocusChangeMask | PropertyChangeMask |
                   StructureNotifyMask);
  grabbuttons(c, 0);
  if (!c->isfloating)
    c->isfloating = c->oldstate = trans != None || c->isfixed;
  if (c->isfloating)
    XRaiseWindow(dpy, c->win);
  attach(c);
  attachstack(c);
  XChangeProperty(dpy, root, netatom[NetClientList], XA_WINDOW, 32,
                  PropModeAppend, (unsigned char *)&(c->win), 1);
  XMoveResizeWindow(dpy, c->win, c->x + 2 * sw, c->y, c->w,
                    c->h); /* some windows require this */
  if (!HIDDEN(c))
    setclientstate(c, NormalState);
  if (c->mon == selmon)
    unfocus(selmon->sel, 0);
  updatetitle(c);
  if (strstr(c->name, "Picture in picture") ||
      strstr(c->name, "Picture-in-Picture")) {
    c->pipparent = find_pipparent(c);
    togglesticky(c, 0);
  }
  else
    arrange(c->mon);

  sync_bypass_compositor(c);

  if (!HIDDEN(c))
    XMapWindow(dpy, c->win);

  /* Mapping can reset the window's position in the X stacking order. Keep
   * managed dialogs above existing floating windows after they are visible. */
  if (!HIDDEN(c) && c->isontop == DIALOG_ONTOP_PRIORITY) {
    XRaiseWindow(dpy, c->win);
    XFlush(dpy);
  }

  /* Focus the client currently under the pointer. */
  {
    Window dummy, pointerwin;
    int pointerx, pointery, pointerxwin, pointerywin;
    unsigned int pointermask;
    Client *pointerc = NULL;

    if (XQueryPointer(dpy, root, &dummy, &pointerwin, &pointerx, &pointery,
                      &pointerxwin, &pointerywin, &pointermask))
      pointerc = wintoclient(pointerwin);
    focus(pointerc);
  }
}

void mappingnotify(XEvent *e) {
  XMappingEvent *ev = &e->xmapping;

  XRefreshKeyboardMapping(ev);
  if (ev->request == MappingKeyboard)
    grabkeys();
}

void maprequest(XEvent *e) {
  static XWindowAttributes wa;
  XMapRequestEvent *ev = &e->xmaprequest;
  Client *i;
  if ((i = wintosystrayicon(ev->window))) {
    sendevent(i->win, netatom[Xembed], StructureNotifyMask, CurrentTime,
              XEMBED_WINDOW_ACTIVATE, 0, systray->win, XEMBED_EMBEDDED_VERSION);
    resizebarwin(selmon);
    updatesystray();
  }

  if (!XGetWindowAttributes(dpy, ev->window, &wa) || wa.override_redirect)
    return;
  if (!wintoclient(ev->window))
    manage(ev->window, &wa);
}

void mapnotify(XEvent *e) {
  XMapEvent *ev = &e->xmap;
  XWindowAttributes wa;

  /* Override-redirect windows (menus, popovers and tooltips) bypass manage().
   * Raise them when they become visible so a floating client cannot cover
   * the popup. */
  if (ev->window != root && XGetWindowAttributes(dpy, ev->window, &wa) &&
      wa.override_redirect)
    XRaiseWindow(dpy, ev->window);
}

void monocle(Monitor *m) {
  unsigned int n = 0;

  Client *c;

  for (c = m->clients; c; c = c->next)
    if (ISVISIBLE(c))
      n++;

  if (n > 0) /* override layout symbol */
    snprintf(m->ltsymbol, sizeof m->ltsymbol, "[%d]", n);

  int newx, newy, neww, newh;

  for (c = nexttiled(m->clients); c; c = nexttiled(c->next)) {
    newx = m->wx + m->gappov - c->bw;
    newy = m->wy + m->gappoh - c->bw;
    neww = m->ww - 2 * (m->gappov + c->bw);
    newh = m->wh - 2 * (m->gappoh + c->bw);

    applysizehints(c, &newx, &newy, &neww, &newh, 0);

    if (neww < m->ww)
      newx = m->wx + (m->ww - (neww + 2 * c->bw)) / 2;

    if (newh < m->wh)
      newy = m->wy + (m->wh - (newh + 2 * c->bw)) / 2;

    resize(c, newx, newy, neww, newh, 0);
  }
}

void motionnotify(XEvent *e) {
  unsigned int i, x;
  static Monitor *mon = NULL;
  Monitor *m;
  XMotionEvent *ev = &e->xmotion;

  if (ev->window == selmon->barcenterwin) {
    if (!notification_center_active() &&
        !notification_clock_hit(ev->x,
                                clockbar_dynw ? clockbar_dynw : clockbar_cw))
      return;
    notify_clock_hovered = 1;
    if (notify_active)
      notification_motion(ev);
    else if (notify_history_active)
      notification_history_motion(ev);
    else if (!notify_transition_pending && notify_history_count)
      notification_history_show();
    return;
  }

  if (ev->window == selmon->barwin) {
    i = x = 0;
    do
      x += TEXTW(tags[i]);
    while (ev->x >= x && ++i < LENGTH(tags));
    if (i < LENGTH(tags)) {
      if ((i + 1) != selmon->previewshow &&
          !(selmon->tagset[selmon->seltags] & 1 << i)) {
        selmon->previewshow = i + 1;
        showtagpreview(i);
      } else if (selmon->tagset[selmon->seltags] & 1 << i) {
        selmon->previewshow = 0;
        showtagpreview(0);
      }
    } else if (selmon->previewshow != 0) {
      selmon->previewshow = 0;
      showtagpreview(0);
    }
  } else if (selmon->previewshow != 0) {
    selmon->previewshow = 0;
    showtagpreview(0);
  }

  if (ev->window != root) {
    return;
  }
  if ((m = recttomon(ev->x_root, ev->y_root, 1, 1)) != mon && mon) {
    unfocus(selmon->sel, 1);
    selmon = m;
    if (alt_held && enablesidebar) {
      hideosidebar(mon);
      showsidbar(selmon);
    }
    focus(NULL);
  }
  mon = m;
}

void updateicon(Client *c) {
  freeicon(c);
  c->icon = geticonprop(c->win, &c->icw, &c->ich, &c->ic_pw, &c->ic_ph);
}

void moveorplace(const Arg *arg) {
  if ((!selmon->lt[selmon->sellt]->arrange ||
       (selmon->sel && selmon->sel->isfloating)))
    movemouse(arg);
  else
    placemouse(arg);
}

static void *
set_animation_property_thread(void *arg)
{
  AnimationPropertyArgs *args = arg;
  Display *thread_dpy;
  Atom atom;

  if ((thread_dpy = XOpenDisplay(args->display_name))) {
    atom = XInternAtom(thread_dpy, "_NO_ANIMATION", False);
    XChangeProperty(thread_dpy, args->win, atom, XA_CARDINAL, 32,
                    PropModeReplace, (unsigned char *)&args->animation_data, 1);
    XCloseDisplay(thread_dpy);
  }

  free(args->display_name);
  free(args);
  return NULL;
}

static void
setnoanimation_async(Client *c, long val)
{
  AnimationPropertyArgs *args;
  pthread_t thread;
  const char *display_name;

  if (!c || !c->win)
    return;

  if (!(args = malloc(sizeof *args)))
    return;

  display_name = DisplayString(dpy);
  args->display_name = display_name ? strdup(display_name) : NULL;
  args->win = c->win;
  args->animation_data = val;

  if (display_name && !args->display_name) {
    free(args);
    return;
  }

  if (pthread_create(&thread, NULL, set_animation_property_thread, args) == 0)
    pthread_detach(thread);
  else {
    free(args->display_name);
    free(args);
  }
}

static void
setnoanimation_sync(Client *c, long val)
{
  if (!c || !c->win)
    return;

  XChangeProperty(dpy, c->win, netatom[NetNoAnimation], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)&val, 1);
  XSync(dpy, False);
}

static void on_stream_param_changed(void *userdata, uint32_t id,
                                   const struct spa_pod *param) {
  if (param == NULL || id != SPA_PARAM_Format)
    return;
  if (spa_format_parse(param, &sound_format.media_type,
                       &sound_format.media_subtype) < 0)
    return;
  if (sound_format.media_type != SPA_MEDIA_TYPE_audio ||
      sound_format.media_subtype != SPA_MEDIA_SUBTYPE_raw)
    return;
  spa_format_audio_raw_parse(param, &sound_format.info.raw);
}

static void on_process(void *userdata) {
  struct pw_buffer *b;
  struct spa_buffer *buf;
  float *samples, max;
  uint32_t n, n_channels, n_samples;

  if (!(b = pw_stream_dequeue_buffer(sound_stream)))
    return;
  buf = b->buffer;
  if (!buf->datas[0].data) {
    pw_stream_queue_buffer(sound_stream, b);
    return;
  }

  n_channels = sound_format.info.raw.channels;
  if (!n_channels) {
    pw_stream_queue_buffer(sound_stream, b);
    return;
  }
   /* frozen in fullscreen: node stays connected, no peak is computed */
    if (fullscreen_st || notification_center_active()) {
    clockbar_peak = 0.0f;
    pw_stream_queue_buffer(sound_stream, b);
    return;
  }
  n_samples = buf->datas[0].chunk->size / sizeof(float);

  /* peak volume across all channels, raw like main.c */
  samples = buf->datas[0].data;
  max = 0.0f;
  for (n = 0; n < n_samples; n++)
    if (fabsf(samples[n]) > max)
      max = fabsf(samples[n]);

  if (max > 1.0f)
    max = 1.0f;
  max = sqrtf(max); /* perceptual loudness mapping */

  /* store the peak for the draw thread */
  clockbar_peak = max;

  pw_stream_queue_buffer(sound_stream, b);
}

static const struct pw_stream_events sound_stream_events = {
    PW_VERSION_STREAM_EVENTS,
    .param_changed = on_stream_param_changed,
    .process = on_process,
};

/* draw thread: fixed-cadence clock bar, independent of the PipeWire graph
 * clock. raw peak, no smoothing, like main.c */
static void *clock_draw_loop(void *data) {
  struct timespec ts;
  uint64_t frame_ns = 1000000000ULL / DRAW_FPS;

  clock_gettime(CLOCK_MONOTONIC, &ts);
  while (clock_draw_running) {
    ts.tv_nsec += frame_ns;
    while (ts.tv_nsec >= 1000000000L) {
      ts.tv_nsec -= 1000000000L;
      ts.tv_sec++;
    }
    clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &ts, NULL);

    /* frozen in fullscreen: nothing is calculated or resized */
    if (fullscreen_st) {
      clockbar_dynw = 0;
      continue;
    }

    if (notification_center_active()) {
      clockbar_dynw = notify_width;
      continue;
    }

    unsigned int min = clockbar_cw;
    unsigned int maxw = clockbar_cw + CLOCK_ANIM_EXTRA;
    unsigned int new_width =
        min + (unsigned int)(clockbar_peak * (maxw - min));
    if (new_width < min)
      new_width = min;
    if (new_width > maxw)
      new_width = maxw;

    clockbar_dynw = new_width;

    /* Xlib requests are sent by the main thread.  This thread only publishes
     * the desired width, avoiding missed frames while contending for dpy. */
  }
  return NULL;
}

static void updateclockbar(void) {
  static unsigned int last_width;
  unsigned int width;

  if (fullscreen_st || !clockbar_win)
    return;

  width = clockbar_dynw;
  if (!width || width == last_width)
    return;

  /* Request one coordinated redraw after the animation and status updates
   * for this frame.  Resizing alone exposes stale pixels in the bar. */
  bar_dirty = 1;
  last_width = width;
}

static void sound_monitor_disconnect(void) {
  if (sound_stream) {
    pw_stream_destroy(sound_stream);
    sound_stream = NULL;
  }
  if (sound_core) {
    pw_core_disconnect(sound_core);
    pw_core_destroy(sound_core, NULL);
    sound_core = NULL;
  }
  if (sound_context) {
    pw_context_destroy(sound_context);
    sound_context = NULL;
  }
}

static void sound_monitor_connect(void);

static const struct pw_core_events sound_core_events = {
    PW_VERSION_CORE_EVENTS,
};

static void sound_monitor_connect(void) {
  const struct spa_pod *params[1];
  uint8_t buffer[1024];
  struct spa_pod_builder b = SPA_POD_BUILDER_INIT(buffer, sizeof(buffer));
  struct pw_properties *props = NULL;
  struct pw_loop *loop = pw_thread_loop_get_loop(sound_loop);

  if (sound_stream || !loop)
    return;

  if (!(sound_context = pw_context_new(loop, NULL, 0)))
    goto error;
  if (!(sound_core = pw_context_connect(sound_context, NULL, 0)))
    goto error;
  pw_core_add_listener(sound_core, &sound_core_listener, &sound_core_events,
                       NULL);

  props = pw_properties_new(PW_KEY_MEDIA_TYPE, "Audio",
                            PW_KEY_MEDIA_CATEGORY, "Capture",
                            PW_KEY_MEDIA_ROLE, "Music", NULL);
  if (!props)
    goto error;
  if (PW_MONITOR_SINK)
    pw_properties_set(props, PW_KEY_STREAM_CAPTURE_SINK, "true");

  if (!(sound_stream =
            pw_stream_new(sound_core, "dwm-sound-bar", props)))
    goto error;
  props = NULL; /* ownership taken by the stream */
  pw_stream_add_listener(sound_stream, &sound_stream_listener,
                         &sound_stream_events, NULL);

  params[0] = spa_format_audio_raw_build(
      &b, SPA_PARAM_EnumFormat,
      &SPA_AUDIO_INFO_RAW_INIT(.format = SPA_AUDIO_FORMAT_F32));

  if (pw_stream_connect(sound_stream, PW_DIRECTION_INPUT, PW_ID_ANY,
                        PW_STREAM_FLAG_AUTOCONNECT | PW_STREAM_FLAG_MAP_BUFFERS |
                            PW_STREAM_FLAG_RT_PROCESS,
                        params, 1) < 0)
    goto error;
  return;

error:
  pw_properties_free(props);
  sound_monitor_disconnect();
}

static void sound_monitor_start(void) {
  clockanim_running = 1;
  pw_init(NULL, NULL);
  if (!(sound_loop = pw_thread_loop_new("dwm-sound-bar", NULL))) {
    pw_deinit();
    clockanim_running = 0;
    return;
  }
  pw_thread_loop_start(sound_loop);
  sound_monitor_connect();

  clock_draw_running = 1;
  pthread_create(&clock_draw_thread, NULL, clock_draw_loop, NULL);
}

static void sound_monitor_stop(void) {
  if (clock_draw_running) {
    clock_draw_running = 0;
    pthread_join(clock_draw_thread, NULL);
  }
  if (sound_loop) {
    pw_thread_loop_stop(sound_loop);
    sound_monitor_disconnect();
    pw_thread_loop_destroy(sound_loop);
    sound_loop = NULL;
  }
  if (clockanim_running) {
    pw_deinit();
    clockanim_running = 0;
  }
}

void movemouse(const Arg *arg) {
  int x, y, nx, ny;
  int rel_x, rel_y; // offset from window corner to mouse
  int lastw = 0, lasth = 0;
  Client *c;
  Monitor *m;
  XEvent ev;
  int was_tiled = 0;

  if (!(c = selmon->sel))
    return;
  if (c->isfullscreen || c->issticky) /* no support moving fullscreen or sticky windows by mouse */
    return;
  if (!c->isfloating && selmon->lt[selmon->sellt]->arrange) {
    was_tiled = 1;
    togglefloating_noarrange(c);
  }
  restack(selmon);
  XFlush(dpy);
  lastw = c->w;
  lasth = c->h;

  if (XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
                   None, cursor[CurMove]->cursor, last_ev_time) != GrabSuccess)
    return;
  dragclient = c;
  setnoanimation_async(c, 1);
  if (!getrootptr(&x, &y)) {
    XUngrabPointer(dpy, CurrentTime);
    dragclient = NULL;
    setnoanimation_async(c, 0);
    return;
  }
  /* Calculate offset from window top-left to mouse position */
  rel_x = x - c->x;
  rel_y = y - c->y;

  /* Move window so mouse is at same relative position at drag start */
  nx = x - rel_x;
  ny = y - rel_y;
  resize(c, nx, ny, c->w, c->h, 1);
  XFlush(dpy);
  do {
	    if (!drag_next_event(&ev)) {
	      ev.type = -1;
	      continue;
	    }
    switch (ev.type) {
    case KeyPress:
      keypress(&ev);
      break;
    case ConfigureRequest:
    case Expose:
    case MapRequest:
    case UnmapNotify:
      handler[ev.type](&ev);
      break;
    case MotionNotify:
      while (XCheckTypedEvent(dpy, MotionNotify, &ev))
        ;

      // If the window size changed (e.g. due to layout), keep mouse at same
      // relative position
      if (c->w != lastw || c->h != lasth) {
        // Clamp rel_x/rel_y to new window size
        if (rel_x > c->w)
          rel_x = c->w / 2;
        if (rel_y > c->h)
          rel_y = c->h / 2;
        nx = ev.xmotion.x - rel_x;
        ny = ev.xmotion.y - rel_y;
        resize(c, nx, ny, c->w, c->h, 1);
        lastw = c->w;
        lasth = c->h;
        break;
      }

      nx = ev.xmotion.x - rel_x;
      ny = ev.xmotion.y - rel_y;
       m = recttomon(ev.xmotion.x, ev.xmotion.y, 1, 1);
      if (m && m != selmon)
        selmon = m;
      if (abs(selmon->wx - nx) < snap)
        nx = selmon->wx;
      else if (abs((selmon->wx + selmon->ww) - (nx + WIDTH(c))) < snap)
        nx = selmon->wx + selmon->ww - WIDTH(c);
      if (abs(selmon->wy - ny) < snap)
        ny = selmon->wy;
      else if (abs((selmon->wy + selmon->wh) - (ny + HEIGHT(c))) < snap)
        ny = selmon->wy + selmon->wh - HEIGHT(c);
      // Always keep floating while dragging; never toggle floating here
      int neww = c->w, newh = c->h;
      resize(c, nx, ny, neww, newh, 1);
      break;
    }
  } while (ev.type != ButtonRelease);

  XUngrabPointer(dpy, CurrentTime);
  dragclient = NULL;
  XFlush(dpy);
  setnoanimation_sync(c, 0);
  /*
   * Decide the destination monitor from the mouse cursor on release.
   * Check BEFORE arrange to prevent applysizehints() from clamping
   * the window position to the wrong monitor's window area.
   */
  if ((m = recttomon(ev.xmotion.x, ev.xmotion.y, 1, 1)) &&
      m != c->mon) {
    sendmon(c, m);
    selmon = m;
    focus(NULL);
  }

  // If window was originally tiled, return to tiled after drag
  if (was_tiled && c->isfloating) {
    togglefloating(NULL);
  } else {
    arrange(c->mon);
  }
}

Client *nexttiled(Client *c) {
  for (; c && (c == dragclient || c->isfloating || (!ISVISIBLE(c) || HIDDEN(c))); c = c->next)
    ;
  return c;
}

void placemouse(const Arg *arg) {
  int x, y, px, py, ocx, ocy, nx = -9999, ny = -9999, freemove = 0;
  Client *c, *r = NULL, *at, *prevr;
  Monitor *m;
  XEvent ev;
  XWindowAttributes wa;
  int attachmode, prevattachmode;
  attachmode = prevattachmode = -1;

  if (!(c = selmon->sel) ||
      !c->mon->lt[c->mon->sellt]->arrange) /* no support for placemouse when
                                              floating layout is used */
    return;
  if (c->isfullscreen || c->issticky) /* no support placing fullscreen or sticky windows by mouse */
    return;
  restack(selmon);
  prevr = c;
  if (XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
                   None, cursor[CurMove]->cursor, CurrentTime) != GrabSuccess)
    return;
  dragclient = c;
  XFlush(dpy);
  setnoanimation_async(c, 1);

  c->isfloating = 0;
  c->beingmoved = 1;

  XGetWindowAttributes(dpy, c->win, &wa);
  ocx = wa.x;
  ocy = wa.y;

  if (!getrootptr(&x, &y)) {
    XUngrabPointer(dpy, CurrentTime);
    dragclient = NULL;
    c->beingmoved = 0;
    setnoanimation_async(c, 0);
    return;
  }

  XFlush(dpy);
  do {
	    if (!drag_next_event(&ev)) {
	      ev.type = -1;
	      continue;
	    }
    switch (ev.type) {
    case KeyPress:
      keypress(&ev);
      break;
    case ConfigureRequest:
    case Expose:
    case MapRequest:
    case UnmapNotify:
      handler[ev.type](&ev);
      break;
    case MotionNotify:
      while (XCheckTypedEvent(dpy, MotionNotify, &ev))
        ;

      nx = ocx + (ev.xmotion.x - x);
      ny = ocy + (ev.xmotion.y - y);

      if (!freemove && (abs(nx - ocx) > snap || abs(ny - ocy) > snap))
        freemove = 1;

      if (freemove) {
        /* Keep the managed geometry in sync with the temporary drag position.
         * Tag switches call showhide(), which otherwise restores c->x/c->y. */
        c->x = nx;
        c->y = ny;
        XMoveWindow(dpy, c->win, nx, ny);
      }

      if ((m = recttomon(ev.xmotion.x, ev.xmotion.y, 1, 1)) && m != selmon)
        selmon = m;

      if (arg->i ==
          1) { // tiled position is relative to the client window center point
        px = nx + wa.width / 2;
        py = ny + wa.height / 2;
      } else { // tiled position is relative to the mouse cursor
        px = ev.xmotion.x;
        py = ev.xmotion.y;
      }

      r = recttoclient(px, py, 1, 1);

      if (!r || r == c)
        break;

      attachmode = 0; // below
      if (((float)(r->y + r->h - py) / r->h) >
          ((float)(r->x + r->w - px) / r->w)) {
        if (abs(r->y - py) < r->h / 2)
          attachmode = 1; // above
      } else if (abs(r->x - px) < r->w / 2)
        attachmode = 1; // above

      if ((r && r != prevr) || (attachmode != prevattachmode)) {
        detachstack(c);
        detach(c);
        if (c->mon != r->mon) {
          arrangemon(c->mon);
          c->tags = r->mon->tagset[r->mon->seltags];
        }

        c->mon = r->mon;
        r->mon->sel = r;

        if (attachmode) {
          if (r == r->mon->clients)
            attach(c);
          else {
            for (at = r->mon->clients; at->next != r; at = at->next)
              ;
            c->next = at->next;
            at->next = c;
          }
        } else {
          c->next = r->next;
          r->next = c;
        }

        attachstack(c);
        arrangemon(r->mon);
        prevr = r;
        prevattachmode = attachmode;
      }
      break;
    }
  } while (ev.type != ButtonRelease);
  XUngrabPointer(dpy, CurrentTime);
  dragclient = NULL;
  setnoanimation_sync(c, 0);

  if ((m = recttomon(ev.xmotion.x, ev.xmotion.y, 1, 1)) && m != c->mon) {
    detach(c);
    detachstack(c);
    arrangemon(c->mon);
    c->mon = m;
    c->tags = m->tagset[m->seltags];
    attach(c);
    attachstack(c);
    selmon = m;
  }

  focus(c);
  c->beingmoved = 0;

  if (nx != -9999)
    resize(c, nx, ny, c->w, c->h, 0);
  arrangemon(c->mon);
}

void pop(Client *c) {
  detach(c);
  attach(c);
  focus(c);
  arrange(c->mon);
}

void propertynotify(XEvent *e) {
  Client *c;
  Window trans;
  XPropertyEvent *ev = &e->xproperty;

  if ((c = wintosystrayicon(ev->window))) {
    if (ev->atom == XA_WM_NORMAL_HINTS) {
      updatesizehints(c);
      updatesystrayicongeom(c, c->w, c->h);
    } else
      updatesystrayiconstate(c, ev);
    resizebarwin(selmon);
    updatesystray();
  }
  if (ev->state == PropertyDelete &&
            ev->atom != netatom[NetWMBypassCompositor])
    return; /* ignore */
  else if ((c = wintoclient(ev->window))) {
    switch (ev->atom) {
    default:
      break;
    case XA_WM_TRANSIENT_FOR:
      if (XGetTransientForHint(dpy, c->win, &trans)) {
        if ((c->isfloating = (wintoclient(trans)) != NULL))
          c->isontop = DIALOG_ONTOP_PRIORITY;
        arrange(c->mon);
        XRaiseWindow(dpy, c->win);
      }
      break;
    case XA_WM_NORMAL_HINTS:
      c->hintsvalid = 0;
      break;
    case XA_WM_HINTS:
      updatewmhints(c);
      drawbars();
      drawtabs();
      break;
    }
    if (ev->atom == XA_WM_NAME || ev->atom == netatom[NetWMName]) {
      updatetitle(c);
      if (c == c->mon->sel)
        drawbar(c->mon);
      drawtab(c->mon);
    }

    else if (ev->atom == netatom[NetWMIcon]) {
      updateicon(c);
      if (c == c->mon->sel)
        drawbar(c->mon);
    }

    if (ev->atom == netatom[NetWMWindowType]) {
      updatewindowtype(c);
      arrange(c->mon);
      XRaiseWindow(dpy, c->win);
    }
    if (ev->atom == netatom[NetWMBypassCompositor])
      sync_bypass_compositor(c);
  }
}

void restart(const Arg *arg) { running = 0; }

Client *recttoclient(int x, int y, int w, int h) {
  Client *c, *r = NULL;
  int a, area = 0;

  for (c = nexttiled(selmon->clients); c; c = nexttiled(c->next)) {
    if ((a = INTERSECTC(x, y, w, h, c)) > area) {
      area = a;
      r = c;
    }
  }
  return r;
}

Monitor *recttomon(int x, int y, int w, int h) {
  Monitor *m, *r = selmon;
  int a, area = 0;

  for (m = mons; m; m = m->next)
    if ((a = INTERSECT(x, y, w, h, m)) > area) {
      area = a;
      r = m;
    }
  return r;
}

void removesystrayicon(Client *i) {
  Client **ii;

  if (!showsystray || !i)
    return;
  for (ii = &systray->icons; *ii && *ii != i; ii = &(*ii)->next)
    ;
  if (ii)
    *ii = i->next;
  free(i);
}

void resize(Client *c, int x, int y, int w, int h, int interact) {
  if (!c)
    return;

  if (applysizehints(c, &x, &y, &w, &h, interact)) {
     // if (!c->isfloating) {
     //   if (animate_tiled)
     //     resizeclient_animated(c, x, y, w,h); // this function make animation relly play of windows move
     //   else
     //     resizeclient(c, x, y, w, h); // instant for tiled
     // } else
      resizeclient(c, x, y, w, h); // instant for floating
  }
}

void resizebarwin(Monitor *m) {
  unsigned int tw, tlw, cw, kw, rw, stw = 0, stgap = 0;
  int lx, rx, cx, kx, titlex, title_right, span;

  if (showsystray && m == systraytomon(m)) {
    stw = getsystraywidth();
    if (stw)
      stgap = bargap;
  }

  if (!m->showbar) {
    XMoveResizeWindow(dpy, m->barwin, m->wx, m->by, 1, bh);
    if (m->bartitlewin)
      XMoveResizeWindow(dpy, m->bartitlewin, m->wx, m->by, 1, bh);
    if (m->barcenterwin)
      XMoveResizeWindow(dpy, m->barcenterwin, m->wx, m->by, 1, bh);
    if (m->barkbwin)
      XMoveResizeWindow(dpy, m->barkbwin, m->wx, m->by, 1, bh);
    if (m->barrightwin)
      XMoveResizeWindow(dpy, m->barrightwin, m->wx, m->by, 1, bh);
    if (m == selmon)
      clockbar_win = 0;
    return;
  }

	barwidths(m, &tw, &tlw, &cw, &kw, &rw);
	/* X rejects zero width/height ConfigureWindow requests.  A narrow monitor
	 * or a long status string can otherwise collapse one of the bar sections
	 * to zero while the section is still being resized. */
	if (!tw) tw = 1;
	if (!tlw) tlw = 1;
	if (!cw) cw = 1;
	if (!kw) kw = 1;
	if (!rw) rw = 1;
	{
   unsigned int dcw = (notification_center_active() && m == selmon) ? notify_width
                                     : ((clockbar_dynw && !notify_clock_hovered &&
                                         !fullscreen_st && m == selmon)
                                           ? clockbar_dynw : cw);
	   unsigned int fcw = (notification_center_active() && m == selmon) ? notify_width : clockbar_cw;
	   if (!dcw) dcw = 1;
	   if (!fcw) fcw = 1;

    lx = floatbar ? m->wx + m->gappov : m->wx;
    rx = lx + (int)(floatbar ? m->ww - 2 * m->gappov : m->ww) - (int)stw -
         (int)rw - (int)stgap;

    XMoveResizeWindow(dpy, m->barwin, lx, m->by, tw, bh);

    kx = lx + (int)tw + bargap; /* kb sticks to the workspace bar */
    if (m->barkbwin) {
      XMoveResizeWindow(dpy, m->barkbwin, kx, m->by, kw, bh);
      XMapWindow(dpy, m->barkbwin);
    }

    titlex = kx + (int)kw + bargap; /* app name bar after the kb */
    title_right = titlex + (int)tlw;
    if (m->bartitlewin) {
      XMoveResizeWindow(dpy, m->bartitlewin, titlex, m->by, tlw, bh);
      XMapWindow(dpy, m->bartitlewin);
    }

    span = rx - title_right;
    if (span >= (int)fcw + 2 * bargap) {
      cx = title_right + (span - (int)fcw - 2 * bargap) / 2;
      int clock_cx = cx + (int)(fcw + 2 * bargap) / 2;
      /* never let the clock center be left of the monitor's center */
      int monitor_center = m->wx + m->ww / 2;
      if (clock_cx < monitor_center) {
        clock_cx = monitor_center;
        cx = clock_cx - (int)(fcw + 2 * bargap) / 2;
      }
      int center_y = m->by;
       unsigned int center_h = (notification_center_active() && m == selmon) ? notify_height : bh;
      if (m->barcenterwin) {
        XMoveResizeWindow(dpy, m->barcenterwin,
                          cx + (int)(fcw + 2 * bargap) / 2 - (int)dcw / 2,
                          center_y, dcw, center_h);
        XMapWindow(dpy, m->barcenterwin);
        /* Keep the center window above fullscreen clients as soon as the
         * fullscreen transition lays it out.  The visualizer also needs to
         * stay above the neighboring bar sections while it grows. */
          if (!fullscreen_st && (notification_center_active() || clockbar_dynw))
           XRaiseWindow(dpy, m->barcenterwin);
      }
      if (m == selmon) {
        clockbar_win = m->barcenterwin;
        clockbar_cx = clock_cx;
        clockbar_by = center_y;
        clockbar_bh = center_h;
      }
    } else {
      cx = 0;
      if (m->barcenterwin)
        XUnmapWindow(dpy, m->barcenterwin);
      if (m == selmon)
        clockbar_win = 0;
    }
  }

  if (m->barrightwin) {
    XMoveResizeWindow(dpy, m->barrightwin, rx, m->by, rw, bh);
    XMapWindow(dpy, m->barrightwin);
  }
}

void resizeclient(Client *c, int x, int y, int w, int h) {
  XWindowChanges wc;

  c->oldw = c->w;
  c->w = wc.width = w;
  c->oldh = c->h;
  c->h = wc.height = h;
  c->oldx = c->x;
  c->x = wc.x = x;
  c->oldy = c->y;
  c->y = wc.y = y;

  if (c->beingmoved)
    return;

  wc.border_width = c->bw;
  XConfigureWindow(dpy, c->win, CWX | CWY | CWWidth | CWHeight | CWBorderWidth,
                   &wc);
  if (!c->isfullscreen && !c->isontop) {
    Window s = ontopsibling(c->mon, c);
    if (s) {
      XWindowChanges wcs;
      wcs.sibling = s;
      wcs.stack_mode = Below;
      XConfigureWindow(dpy, c->win, CWSibling | CWStackMode, &wcs);
    }
  }
  configure(c);
  XFlush(dpy);
}

static Window ontopsibling(Monitor *m, Client *exclude) {
  Client *c;
  Client *lowest = NULL;
  if (!m)
    return None;
  for (c = m->stack; c; c = c->snext)
    if (c != exclude && c->isontop && !c->issticky && !c->isfullscreen &&
        ISVISIBLE(c))
      if (!lowest || c->isontop < lowest->isontop)
        lowest = c;
  return lowest ? lowest->win : None;
}

void resizemouse(const Arg *arg) {
  Client *c;
  Monitor *m;
  XEvent ev;
  Time lasttime = 0;
  int ocx, ocy, ocw, och, nw, nh;
  int mx, my;
  int last_quadrant = -1;
  int quadrant;

  if (!(c = selmon->sel) || c->isfullscreen || c->issticky)
    return;

  restack(selmon);

  /* original position and size */
  ocx = c->x;
  ocy = c->y;
  ocw = c->w;
  och = c->h;

  if (XGrabPointer(dpy, root, False, MOUSEMASK, GrabModeAsync, GrabModeAsync,
                   None, cursor[CurResize]->cursor, CurrentTime) != GrabSuccess)
    return;
  XFlush(dpy);
  setnoanimation_async(c, 1);

  if (!getrootptr(&mx, &my))
    return;

  XFlush(dpy);
  do {
	    if (!drag_next_event(&ev)) {
	      ev.type = -1;
	      continue;
	    }
     switch (ev.type) {
    case ConfigureRequest:
    case Expose:
    case MapRequest:
    case UnmapNotify:
      handler[ev.type](&ev);
      break;
    case MotionNotify:
      if ((ev.xmotion.time - lasttime) <= (1000 / 60))
        continue;
      lasttime = ev.xmotion.time;

      /* determine resize quadrant based on initial grab point */
      if (mx < ocx + ocw / 2 && my < ocy + och / 2)
        quadrant = CurTopLeft;
      else if (mx >= ocx + ocw / 2 && my < ocy + och / 2)
        quadrant = CurTopRight;
      else if (mx < ocx + ocw / 2 && my >= ocy + och / 2)
        quadrant = CurBottomLeft;
      else
        quadrant = CurBottomRight;

      if (quadrant != last_quadrant) {
        XChangeActivePointerGrab(dpy, MOUSEMASK, cursor[quadrant]->cursor, CurrentTime);
        last_quadrant = quadrant;
      }

      /* width/height based on mouse movement */
      nw = MAX(ocw + (ev.xmotion.x - mx) * (mx < ocx + ocw / 2 ? -1 : 1),
               c->minw);
      nh = MAX(och + (ev.xmotion.y - my) * (my < ocy + och / 2 ? -1 : 1),
               c->minh);

      /* calculate new window position */
      int nx = (mx < ocx + ocw / 2) ? ocx + (ocw - nw) : ocx;
      int ny = (my < ocy + och / 2) ? ocy + (och - nh) : ocy;

      if (!c->isfloating && selmon->lt[selmon->sellt]->arrange &&
          (abs(nw - c->w) > snap || abs(nh - c->h) > snap))
        togglefloating(NULL);

      if (!selmon->lt[selmon->sellt]->arrange || c->isfloating)
        resize(c, nx, ny, nw, nh, 1);

      break;
    }
  } while (ev.type != ButtonRelease);

  XUngrabPointer(dpy, CurrentTime);
  setnoanimation_sync(c, 0);
  while (XCheckMaskEvent(dpy, EnterWindowMask, &ev))
    ;

  if ((m = recttomon(c->x + WIDTH(c) / 2, c->y + HEIGHT(c) / 2, 1, 1)) &&
      m != c->mon) {
    sendmon(c, m);
    selmon = m;
    focus(NULL);
  }
}

void resizerequest(XEvent *e) {
  XResizeRequestEvent *ev = &e->xresizerequest;
  Client *i;

  if ((i = wintosystrayicon(ev->window))) {
    updatesystrayicongeom(i, ev->width, ev->height);
    resizebarwin(selmon);
    updatesystray();
  }
}

void restack(Monitor *m) {
  Client *c;
  XEvent ev;
  XWindowChanges wc;

  drawbar(m);
  drawtab(m);
  drawsidebar(m);

  if (!m)
    return;

  if (stickywin) {
    XLowerWindow(dpy, stickywin->win);
  }

  /* Also lower any other sticky windows just in case */
  for (c = m->stack; c; c = c->snext)
    if (c->issticky && c != stickywin && ISVISIBLE(c))
      XLowerWindow(dpy, c->win);

  if (m->sel && !m->sel->issticky && !m->sel->isontop && (m->sel->isfloating || !m->lt[m->sellt]->arrange))
    XRaiseWindow(dpy, m->sel->win);
  if (m->lt[m->sellt]->arrange) {
    wc.stack_mode = Below;
    wc.sibling = m->barwin;
    for (c = m->stack; c; c = c->snext)
      if (!c->isfloating && !c->issticky && ISVISIBLE(c)) {
        XConfigureWindow(dpy, c->win, CWSibling | CWStackMode, &wc);
        wc.sibling = c->win;
      }
  }
  {
    Client *ontop_clients[256];
    int ontop_count = 0;
    for (c = m->stack; c; c = c->snext)
      if (c->isontop && !c->issticky && !c->isfullscreen && ISVISIBLE(c))
        ontop_clients[ontop_count++] = c;
    for (int i = 1; i < ontop_count; i++) {
      Client *key = ontop_clients[i];
      int j = i - 1;
      while (j >= 0 && ontop_clients[j]->isontop < key->isontop) {
        ontop_clients[j + 1] = ontop_clients[j];
        j--;
      }
      ontop_clients[j + 1] = key;
    }
    Window isontop_sibling = None;
    for (int i = 0; i < ontop_count; i++) {
      c = ontop_clients[i];
      if (isontop_sibling == None) {
        XRaiseWindow(dpy, c->win);
      } else {
        wc.sibling = isontop_sibling;
        wc.stack_mode = Below;
        XConfigureWindow(dpy, c->win, CWSibling | CWStackMode, &wc);
      }
      isontop_sibling = c->win;
    }
  }
  XFlush(dpy);
  while (XCheckMaskEvent(dpy, EnterWindowMask, &ev))
    ;
  if (m && m->sidebarvisible)
    XRaiseWindow(dpy, m->sidebarwin);
}

void checkminimize(void) {
  Monitor *m;
  Client *c;
  time_t now = time(NULL);

  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      if (c != m->sel && !ISVISIBLE(c) && !HIDDEN(c) && !c->issticky &&
          shouldminimize(c) && c->lastvisible > 0)
        if (now - c->lastvisible >= 1) {
          hide(c);
          c->isautominimized = 1;
          c->lastvisible = 0;
        }
}

static time_t next_minimize_deadline(void) {
  Monitor *m;
  Client *c;
  time_t deadline = 0;

  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      if (c != m->sel && !ISVISIBLE(c) && !HIDDEN(c) && !c->issticky &&
          c->lastvisible > 0 && (!deadline || c->lastvisible + 1 < deadline))
        deadline = c->lastvisible + 1;

  return deadline;
}

void prepare_workspace_switch(Monitor *m, unsigned int oldtags, unsigned int newtags) {
  Client *c;
  int changed = 0;

  /* Unmap windows leaving the view; minimizable clients also enter IconicState. */
  for (c = m->clients; c; c = c->next) {
    if (c != dragclient && shouldminimize(c) && (c->tags & oldtags) &&
        !(c->tags & newtags) && !c->issticky && !HIDDEN(c)) {
      xunmapclient(c);
      /* Track tag-hidden windows even when the client cannot minimize. */
      c->isautominimized = 1;
      if (c->lastvisible == 0)
        c->lastvisible = time(NULL);
      changed = 1;
    }
  }

  /* Map windows entering the view; minimizable clients also enter NormalState. */
  for (c = m->clients; c; c = c->next) {
    if (shouldminimize(c) && (c->tags & newtags) && !c->issticky && c->isiconic &&
        c->isautominimized && !c->fshidden) {
      xmapclient(c);
      c->isautominimized = 0;
      c->lastvisible = 0;
      changed = 1;
    }
  }

  if (changed)
    XSync(dpy, False);
}

void run(void) {
  XEvent ev;
  int xfd = ConnectionNumber(dpy);
  int timeout;
  const int clockbar_timeout = 1000 / DRAW_FPS;
  time_t next_clock_update = 0;
  struct pollfd pfd[3] = {{.fd = xfd, .events = POLLIN},
                          {.fd = -1, .events = POLLIN},
                          {.fd = -1, .events = POLLIN}};

  /* main event loop */
  XFlush(dpy);
  updateclock();
  next_clock_update = time(NULL) / 60 * 60 + 60;
  while (running) {
    time_t now = time(NULL);
    time_t minimize_deadline = next_minimize_deadline();
    time_t next_deadline = now - now % 60 + 60;

    if (minimize_deadline && minimize_deadline < next_deadline)
      next_deadline = minimize_deadline;
    timeout = next_deadline > now ? (int)((next_deadline - now) * 1000) : 0;
    if (CLOCK_ANIMATE && timeout > clockbar_timeout)
      timeout = clockbar_timeout;
    if (notify_current && timeout > 100)
      timeout = 100;
    if (notify_transition_pending && timeout > NOTIFY_TRANSITION_MS)
      timeout = NOTIFY_TRANSITION_MS;
    if (notify_history_active &&
        notify_history_scroll != notify_history_scroll_target &&
        timeout > clockbar_timeout)
      timeout = clockbar_timeout;
    if (mpris_active && timeout > clockbar_timeout)
      timeout = clockbar_timeout;
    pfd[1].fd = notify_fd;
    pfd[2].fd = status_event_fd;
    poll(pfd, status_event_fd >= 0 ? 3 : (notify_fd >= 0 ? 2 : 1), timeout);
    if (notify_fd >= 0 && (pfd[1].revents & POLLIN))
      notification_dispatch();
    if (status_event_fd >= 0 && (pfd[2].revents & POLLIN))
      status_consume();
    if (CLOCK_ANIMATE)
      updateclockbar();
    {
      int redraw = bar_dirty;
      bar_dirty = 0;
      if (update_mpris_scroll())
        redraw = 1;
      if (redraw)
      drawbars();
	    }
	    if (!mpris_active) {
			mpris_scroll_clock_valid = 0;
			mpris_scroll_accum_ns = 0;
		}
    while (XPending(dpy)) {
      XNextEvent(dpy, &ev);

      /* Xkb StateNotify for Alt sidebar tracking */
      if (xkb_event_base && ev.type == xkb_event_base) {
        XkbEvent *xkbev = (XkbEvent *)&ev;
        if (xkbev->any.xkb_type == XkbStateNotify) {
          int new_alt = (xkbev->state.mods & Mod1Mask) != 0;
          if (enablesidebar && selmon) {
            if (new_alt && !alt_held)
              showsidbar(selmon);
            else if (!new_alt && alt_held)
              hideosidebar(selmon);
          }
          alt_held = new_alt;
          getkblayout();
          drawbars();
        }
        continue;
      }

      if (handler[ev.type])
        handler[ev.type](&ev); /* call handler */
    }

    /* Keep a fullscreen client above the bar after all requests from the
     * client in this event batch have been processed. */
    if (fullscreen_st && selmon && selmon->sel && selmon->sel->isfullscreen) {
      XRaiseWindow(dpy, selmon->sel->win);
      XFlush(dpy);
    }

    now = time(NULL);
    notification_tick();
    notification_history_tick();
    if (minimize_deadline && now >= minimize_deadline)
      checkminimize();
    if (now >= next_clock_update) {
      updateclock();
      next_clock_update = now - now % 60 + 60;
    }
  }
}

void updateclock(void) {
  time_t t = time(NULL);
  struct tm *tm = localtime(&t);
  char buf[8];

  if (!tm)
    return;
  snprintf(buf, sizeof(buf), "%02d:%02d", tm->tm_hour, tm->tm_min);
  if (strcmp(buf, clockstr) == 0)
    return;
  strcpy(clockstr, buf);
  drawbars();
}

void scan(void) {
  unsigned int i, num;
  Window d1, d2, *wins = NULL;
  XWindowAttributes wa;

  if (XQueryTree(dpy, root, &d1, &d2, &wins, &num)) {
    for (i = 0; i < num; i++) {
      if (!XGetWindowAttributes(dpy, wins[i], &wa) || wa.override_redirect ||
          XGetTransientForHint(dpy, wins[i], &d1))
        continue;
      if (wa.map_state == IsViewable || getstate(wins[i]) == IconicState)
        manage(wins[i], &wa);
    }
    for (i = 0; i < num; i++) { /* now the transients */
      if (!XGetWindowAttributes(dpy, wins[i], &wa))
        continue;
      if (XGetTransientForHint(dpy, wins[i], &d1) &&
          (wa.map_state == IsViewable || getstate(wins[i]) == IconicState))
        manage(wins[i], &wa);
    }
    if (wins)
      XFree(wins);
  }
}

void sendmon(Client *c, Monitor *m) {
  if (c->mon == m)
    return;
  unfocus(c, 1);
  detach(c);
  detachstack(c);
  c->mon = m;
  c->tags = m->tagset[m->seltags]; /* assign tags of target monitor */
  attach(c);
  attachstack(c);
  setclienttagprop(c);
  focus(NULL);
  arrange(NULL);
}

void setclientstate(Client *c, long state) {
  long data[] = {state, None};
  Atom atoms[32];
  int natoms = 0;
  Atom da;
  int di;
  unsigned long nitems, extra;
  unsigned char *p = NULL;

  if (XGetWindowProperty(dpy, c->win, netatom[NetWMState], 0L, 32, False,
                         XA_ATOM, &da, &di, &nitems, &extra,
                         &p) == Success && p) {
    Atom *existing = (Atom *)p;
    for (unsigned long i = 0; i < nitems && natoms < 32; i++)
      if (existing[i] != netatom[NetWMStateHidden])
        atoms[natoms++] = existing[i];
    XFree(p);
  }

  if (state == IconicState)
    atoms[natoms++] = netatom[NetWMStateHidden];

  XChangeProperty(dpy, c->win, netatom[NetWMState], XA_ATOM, 32,
                  PropModeReplace, (unsigned char *)atoms, natoms);

  XChangeProperty(dpy, c->win, wmatom[WMState], wmatom[WMState], 32,
                  PropModeReplace, (unsigned char *)data, 2);
}

void setcurrentdesktop(void) {
  long data[] = {0};
  XChangeProperty(dpy, root, netatom[NetCurrentDesktop], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 1);
}
void setdesktopnames(void) {
  XTextProperty text;
  Xutf8TextListToTextProperty(dpy, tags, TAGSLENGTH, XUTF8StringStyle, &text);
  XSetTextProperty(dpy, root, &text, netatom[NetDesktopNames]);
}

int sendevent(Window w, Atom proto, int mask, long d0, long d1, long d2,
              long d3, long d4) {
  int n;
  Atom *protocols, mt;
  int exists = 0;
  XEvent ev;

  if (proto == wmatom[WMTakeFocus] || proto == wmatom[WMDelete]) {
    mt = wmatom[WMProtocols];
    if (XGetWMProtocols(dpy, w, &protocols, &n)) {
      while (!exists && n--)
        exists = protocols[n] == proto;
      XFree(protocols);
    }
  } else {
    exists = True;
    mt = proto;
  }
  if (exists) {
    ev.type = ClientMessage;
    ev.xclient.window = w;
    ev.xclient.message_type = mt;
    ev.xclient.format = 32;
    ev.xclient.data.l[0] = d0;
    ev.xclient.data.l[1] = d1;
    ev.xclient.data.l[2] = d2;
    ev.xclient.data.l[3] = d3;
    ev.xclient.data.l[4] = d4;
    XSendEvent(dpy, w, False, mask, &ev);
  }
  return exists;
}

void setnumdesktops(void) {
  long data[] = {TAGSLENGTH};
  XChangeProperty(dpy, root, netatom[NetNumberOfDesktops], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 1);
}

/*
 * cgwrite_focused — GPU VRAM boost for focused window via cgroup
 * Mirrors dwm-dmemcg-boost.sh logic: reads /proc/PID/cgroup, enables
 * subtree_control recursively, and writes to dmem.low
 */
#define CGWRITE_BIN "/usr/local/bin/cgwrite"
#define CGWRITE_DRM_SYSFS "/sys/class/drm"
#define CGWRITE_DEFAULT_BOOST_SIZE "4294967296" /* 4 GiB */
#define CGWRITE_DEFAULT_DRM_RESOURCE 0

static int cgwrite_drm_resource = CGWRITE_DEFAULT_DRM_RESOURCE;
static char cgwrite_boost_size[64] = CGWRITE_DEFAULT_BOOST_SIZE;

static int cgwrite_read_uint64_file(const char *path,
                                    unsigned long long *value) {
  FILE *f;
  unsigned long long v;

  if (!path || !value)
    return 0;

  f = fopen(path, "r");
  if (!f)
    return 0;

  if (fscanf(f, "%llu", &v) != 1) {
    fclose(f);
    return 0;
  }

  fclose(f);
  *value = v;
  return 1;
}

static int cgwrite_read_text_file(const char *path, char *buf,
                                  size_t bufsize) {
  FILE *f;

  if (!path || !buf || bufsize == 0)
    return 0;

  f = fopen(path, "r");
  if (!f)
    return 0;

  if (!fgets(buf, bufsize, f)) {
    fclose(f);
    return 0;
  }

  fclose(f);
  return 1;
}

static int cgwrite_parse_card_name(const char *name, int *card,
                                   const char **suffix) {
  const char *p;
  char *end;
  long n;

  if (!name || strncmp(name, "card", 4) != 0 ||
      !isdigit((unsigned char)name[4]))
    return 0;

  p = name + 4;
  errno = 0;
  n = strtol(p, &end, 10);
  if (errno != 0 || n < 0 || n > 255)
    return 0;

  if (card)
    *card = (int)n;
  if (suffix)
    *suffix = end;

  return 1;
}

static int cgwrite_find_connected_display_card(void) {
  DIR *dir;
  struct dirent *ent;
  int best = -1;

  dir = opendir(CGWRITE_DRM_SYSFS);
  if (!dir)
    return -1;

  while ((ent = readdir(dir))) {
    const char *suffix;
    char status_path[512];
    char status[64];
    int card;

    if (!cgwrite_parse_card_name(ent->d_name, &card, &suffix) || !suffix ||
        suffix[0] != '-')
      continue;

    snprintf(status_path, sizeof(status_path), "%s/%s/status",
             CGWRITE_DRM_SYSFS, ent->d_name);
    if (!cgwrite_read_text_file(status_path, status, sizeof(status)))
      continue;

    if (strncmp(status, "connected", strlen("connected")) == 0 &&
        (best < 0 || card < best))
      best = card;
  }

  closedir(dir);
  return best;
}

static int cgwrite_find_boot_vga_card(void) {
  DIR *dir;
  struct dirent *ent;
  int best = -1;

  dir = opendir(CGWRITE_DRM_SYSFS);
  if (!dir)
    return -1;

  while ((ent = readdir(dir))) {
    const char *suffix;
    char boot_vga_path[512];
    unsigned long long boot_vga;
    int card;

    if (!cgwrite_parse_card_name(ent->d_name, &card, &suffix) || !suffix ||
        suffix[0] != '\0')
      continue;

    snprintf(boot_vga_path, sizeof(boot_vga_path), "%s/%s/device/boot_vga",
             CGWRITE_DRM_SYSFS, ent->d_name);
    if (cgwrite_read_uint64_file(boot_vga_path, &boot_vga) && boot_vga == 1 &&
        (best < 0 || card < best))
      best = card;
  }

  closedir(dir);
  return best;
}

static int cgwrite_find_first_card(void) {
  DIR *dir;
  struct dirent *ent;
  int best = -1;

  dir = opendir(CGWRITE_DRM_SYSFS);
  if (!dir)
    return -1;

  while ((ent = readdir(dir))) {
    const char *suffix;
    int card;

    if (!cgwrite_parse_card_name(ent->d_name, &card, &suffix) || !suffix ||
        suffix[0] != '\0')
      continue;

    if (best < 0 || card < best)
      best = card;
  }

  closedir(dir);
  return best;
}

static int cgwrite_read_card_vram_total(int card, unsigned long long *bytes) {
  static const char *files[] = {
      "mem_info_vram_total",
      "mem_info_vis_vram_total",
      "local_memory_size",
  };
  char path[512];
  size_t i;

  if (card < 0 || !bytes)
    return 0;

  for (i = 0; i < LENGTH(files); i++) {
    snprintf(path, sizeof(path), "%s/card%d/device/%s", CGWRITE_DRM_SYSFS,
             card, files[i]);
    if (cgwrite_read_uint64_file(path, bytes) && *bytes > 0)
      return 1;
  }

  return 0;
}

static void cgwrite_detect_drm_boost(void) {
  unsigned long long bytes;
  int card;

  cgwrite_drm_resource = CGWRITE_DEFAULT_DRM_RESOURCE;
  snprintf(cgwrite_boost_size, sizeof(cgwrite_boost_size), "%s",
           CGWRITE_DEFAULT_BOOST_SIZE);

  card = cgwrite_find_connected_display_card();
  if (card < 0)
    card = cgwrite_find_boot_vga_card();
  if (card < 0)
    card = cgwrite_find_first_card();

  if (card < 0)
    return;

  cgwrite_drm_resource = card;
  if (cgwrite_read_card_vram_total(card, &bytes))
    snprintf(cgwrite_boost_size, sizeof(cgwrite_boost_size), "%llu", bytes);
}

pid_t getwindowpid(Window win) {
  Atom atom, type;
  int format;
  unsigned long nitems, bytes;
  unsigned char *prop;
  pid_t pid = -1;

  atom = XInternAtom(dpy, "_NET_WM_PID", False);
  if (atom == None)
    return -1;

  if (XGetWindowProperty(dpy, win, atom, 0L, 1L, False, XA_CARDINAL, &type,
                          &format, &nitems, &bytes, &prop) == Success &&
      prop != NULL) {
    pid = *(pid_t *)prop;
    XFree(prop);
  }
  return pid;
}

static Window get_win_prop(Window w, const char *atom_name) {
  Atom atom, type;
  int format;
  unsigned long nitems, bytes;
  unsigned char *prop;
  Window result = None;

  atom = XInternAtom(dpy, atom_name, False);
  if (atom == None)
    return None;

  if (XGetWindowProperty(dpy, w, atom, 0L, 1L, False, XA_WINDOW, &type,
                          &format, &nitems, &bytes, &prop) == Success &&
      prop != NULL) {
    result = *(Window *)prop;
    XFree(prop);
  }
  return result;
}

static unsigned long get_user_time(Window win) {
  Atom atom, type;
  int format;
  unsigned long nitems, bytes;
  unsigned char *prop;
  unsigned long time_val = 0;

  atom = XInternAtom(dpy, "_NET_WM_USER_TIME", False);
  if (atom == None)
    return 0;

  if (XGetWindowProperty(dpy, win, atom, 0L, 1L, False, XA_CARDINAL, &type,
                          &format, &nitems, &bytes, &prop) == Success &&
      prop != NULL) {
    time_val = *(unsigned long *)prop;
    XFree(prop);
  }
  return time_val;
}

static int is_browser_window(Client *c) {
  if (!c->name[0] || c->name[0] == '\0')
    return 0;
  if (strstr(c->name, "Firefox") || strstr(c->name, "firefox"))
    return 1;
  if (strstr(c->name, "Zen Browser") || strstr(c->name, "zen-browser"))
    return 1;
  if (strstr(c->name, "chrome") || strstr(c->name, "Chrome") ||
      strstr(c->name, "Chromium") || strstr(c->name, "Chromium-browser") ||
      strstr(c->name, "brave") || strstr(c->name, "Microsoft Edge") ||
      strstr(c->name, "microsoft-edge") || strstr(c->name, "edge") ||
      strstr(c->name, "vivaldi") || strstr(c->name, "opera") ||
      strstr(c->name, "waterfox") || strstr(c->name, "librewolf") ||
      strstr(c->name, "pale-moon") || strstr(c->name, "org.mozilla"))
    return 1;
  return 0;
}

Client *find_pipparent(Client *c) {
  if (!c || c->win == None)
    return NULL;

  Monitor *m;
  Client *it;
  unsigned long highest_time = 0;
  Client *best_parent = NULL;

  Window pip_user_time_window = get_win_prop(c->win, "_NET_WM_USER_TIME_WINDOW");
  if (pip_user_time_window != None && pip_user_time_window != root) {
    Window parent = pip_user_time_window;
    Window child;
    int depth = 0;

    while (parent && parent != root && depth < 20) {
      Client *client = wintoclient(parent);
      if (client) {
        pid_t client_pid = getwindowpid(client->win);
        pid_t pip_pid = getwindowpid(c->win);
        if (client_pid == pip_pid && client_pid > 0 && client != c) {
          return client;
        }
      }

      if (XGetTransientForHint(dpy, parent, &child) && child == pip_user_time_window) {
        Window dummy;
        Window *children = NULL;
        unsigned int nchildren = 0;

        if (XQueryTree(dpy, parent, &dummy, &parent, &children, &nchildren)) {
          if (children)
            XFree(children);
          if (!parent || parent == root)
            break;
        } else {
          break;
        }
      } else {
        parent = None;
      }
      depth++;
    }
  }

  pid_t pip_pid = getwindowpid(c->win);
  if (pip_pid <= 0)
    return NULL;

  for (m = mons; m; m = m->next) {
    for (it = m->clients; it; it = it->next) {
      if (!it->win || it == c || it->pipparent)
        continue;

      pid_t client_pid = getwindowpid(it->win);
      if (client_pid != pip_pid)
        continue;

      if (is_browser_window(it)) {

        unsigned long current_time = get_user_time(it->win);

        if (current_time > highest_time) {
          highest_time = current_time;
          best_parent = it;
        }
      }
    }
  }

  return best_parent;
}

void cgwrite_focused(Window win) {
  pid_t pid, child;
  char pid_str[32];
  char drm_resource_str[16];
  char *argv[] = {CGWRITE_BIN, pid_str, drm_resource_str, cgwrite_boost_size,
                  NULL};

  if (!win || win == None)
    return;

  pid = getwindowpid(win);
  if (pid <= 0)
    return;

  snprintf(pid_str, sizeof(pid_str), "%d", (int)pid);
  snprintf(drm_resource_str, sizeof(drm_resource_str), "%d",
           cgwrite_drm_resource);

  child = fork();
  if (child < 0) {
    /* fork failed — nothing we can do without logging infrastructure here */
    return;
  }

  if (child == 0) {
    /* Child: exec the setuid binary */
    execv(CGWRITE_BIN, argv);
    /* execv only returns on failure */
    _exit(1);
  }

  /* Parent: reap child so it doesn't become a zombie */
  waitpid(child, NULL, 0);
}

void setfocus(Client *c) {
  if (!c->neverfocus) {
    XSetInputFocus(dpy, c->win, RevertToPointerRoot, CurrentTime);
    XChangeProperty(dpy, root, netatom[NetActiveWindow], XA_WINDOW, 32,
                    PropModeReplace, (unsigned char *)&(c->win), 1);
  } else {
    /* InputHint false: do not focus the client window, but avoid leaving the
     * previous X focus target so keys still go there while dwm shows sel on
     * the neverfocus window (e.g. after arrange → focusunderpointer). */
    XSetInputFocus(dpy, root, RevertToPointerRoot, CurrentTime);
    XDeleteProperty(dpy, root, netatom[NetActiveWindow]);
  }
  sendevent(c->win, wmatom[WMTakeFocus], NoEventMask, wmatom[WMTakeFocus],
            CurrentTime, 0, 0, 0);

  /* Apply cgroup settings to the focused window. */
  cgwrite_focused(c->win);
}

void setfullscreen(Client *c, int fullscreen) {
  if (fullscreen && !c->isfullscreen) {
    XChangeProperty(dpy, c->win, netatom[NetWMState], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)&netatom[NetWMFullscreen],
                    1);
    c->isfullscreen = 1;
    c->oldstate = c->isfloating;
    c->oldbw = c->bw;
    c->bw = 0;
    c->isfloating = 1;
    resizeclient(c, c->mon->mx, c->mon->my, c->mon->mw, c->mon->mh);
    setwindowopacity(c);
    sync_bypass_compositor(c);
    XRaiseWindow(dpy, c->win);

    /* hide all lower windows; preserve sticky windows if window has transparency */
    int has_transparency = window_has_transparency(c);
    Client *it;
    for (it = c->mon->stack; it; it = it->snext) {
      if (it == c || !ISVISIBLE(it) || HIDDEN(it))
        continue;
      if (has_transparency && stickywin && it->issticky)
        continue;
      xunmapclient(it);
      it->fshidden = 1;
      it->isautominimized = 0;
    }
  } else if (!fullscreen && c->isfullscreen) {
    XChangeProperty(dpy, c->win, netatom[NetWMState], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)0, 0);
    clearwindowopacity(c);
    c->isfullscreen = 0;
    sync_bypass_compositor(c);
    c->isfloating = c->oldstate;
    c->bw = c->oldbw;
    c->x = c->oldx;
    c->y = c->oldy;
    c->w = c->oldw;
    c->h = c->oldh;
    resizeclient(c, c->x, c->y, c->w, c->h);

    /* restore windows hidden by fullscreen */
    Client *it;
    for (it = c->mon->stack; it; it = it->snext) {
      if (it->fshidden) {
        it->fshidden = 0;
        xmapclient(it);
        it->isautominimized = 0;
      }
    }
    arrange(c->mon);
  }

  if (c == selmon->sel || fullscreen_st)
    updatefullscreenstatus(selmon->sel);
  drawbars();

  /* Bar redraws can change the stacking order. Keep the fullscreen client
   * above the bar immediately after the transition. */
  if (fullscreen && c->isfullscreen && c->mon == selmon &&
      c->win) {
    XRaiseWindow(dpy, c->win);
    XFlush(dpy);
  }
}

void setlayout(const Arg *arg) {
  if (!arg || !arg->v || arg->v != selmon->lt[selmon->sellt])
    selmon->sellt = selmon->pertag->sellts[selmon->pertag->curtag] ^= 1;
  if (arg && arg->v)
    selmon->lt[selmon->sellt] =
        selmon->pertag->ltidxs[selmon->pertag->curtag][selmon->sellt] =
            (Layout *)arg->v;
  strncpy(selmon->ltsymbol, selmon->lt[selmon->sellt]->symbol,
          sizeof(selmon->ltsymbol) - 1);
  selmon->ltsymbol[sizeof(selmon->ltsymbol) - 1] = '\0';
  if (selmon->sel)
    arrange(selmon);
  else
    drawbar(selmon);
}

void setcfact(const Arg *arg) {
  float f;
  Client *c;

  c = selmon->sel;

  if (!arg || !c || !selmon->lt[selmon->sellt]->arrange)
    return;
  if (!arg->f)
    f = 1.0;
  else if (arg->f > 4.0) // set fact absolutely
    f = arg->f - 4.0;
  else
    f = arg->f + c->cfact;
  if (f < 0.25)
    f = 0.25;
  else if (f > 4.0)
    f = 4.0;
  Bool prev_animate = animate_tiled;
  animate_tiled = 0;
  animate_tiled = prev_animate;
  c->cfact = f;
  arrange(selmon);
}

/* arg > 1.0 will set mfact absolutely */
void setmfact(const Arg *arg) {
  float f;

  if (!arg || !selmon->lt[selmon->sellt]->arrange)
    return;
  f = arg->f < 1.0 ? arg->f + selmon->mfact : arg->f - 1.0;
  if (f < 0.05 || f > 0.95)
    return;
  Bool prev_animate = animate_tiled;
  animate_tiled = 0;
  selmon->mfact = selmon->pertag->mfacts[selmon->pertag->curtag] = f;
  arrange(selmon);
  animate_tiled = prev_animate;
}

void setup(void) {
  int i;
  XSetWindowAttributes wa;
  Atom utf8string;
  struct sigaction sa;
  /* do not transform children into zombies when they terminate */
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_NOCLDSTOP | SA_NOCLDWAIT | SA_RESTART;
  sa.sa_handler = SIG_IGN;
  sigaction(SIGCHLD, &sa, NULL);

  /* clean up any zombies (inherited from .xinitrc etc) immediately */
  while (waitpid(-1, NULL, WNOHANG) > 0)
    ;

  cgwrite_detect_drm_boost();

  /* init screen */
  screen = DefaultScreen(dpy);
  sw = DisplayWidth(dpy, screen);
  sh = DisplayHeight(dpy, screen);
  root = RootWindow(dpy, screen);
  drw = drw_create(dpy, screen, root, sw, sh);
  if (!drw_fontset_create(drw, fonts, LENGTH(fonts)))
    die("no fonts could be loaded.");
  lrpad = drw->fonts->h;
  bh = drw->fonts->h + 2 + vertpadbar + borderpx * 2;
  th = vertpadtab;
  // bh_n = vertpadtab;
  updategeom();
  /* init atoms */
  utf8string = XInternAtom(dpy, "UTF8_STRING", False);
  wmatom[WMProtocols] = XInternAtom(dpy, "WM_PROTOCOLS", False);
  wmatom[WMDelete] = XInternAtom(dpy, "WM_DELETE_WINDOW", False);
  wmatom[WMState] = XInternAtom(dpy, "WM_STATE", False);
  wmatom[WMTakeFocus] = XInternAtom(dpy, "WM_TAKE_FOCUS", False);
  netatom[NetActiveWindow] = XInternAtom(dpy, "_NET_ACTIVE_WINDOW", False);
  netatom[NetSupported] = XInternAtom(dpy, "_NET_SUPPORTED", False);
  netatom[NetSystemTray] = XInternAtom(dpy, "_NET_SYSTEM_TRAY_S0", False);
  netatom[NetSystemTrayOP] = XInternAtom(dpy, "_NET_SYSTEM_TRAY_OPCODE", False);
  netatom[NetSystemTrayOrientation] =
      XInternAtom(dpy, "_NET_SYSTEM_TRAY_ORIENTATION", False);
  netatom[NetSystemTrayOrientationHorz] =
      XInternAtom(dpy, "_NET_SYSTEM_TRAY_ORIENTATION_HORZ", False);
  netatom[NetWMName] = XInternAtom(dpy, "_NET_WM_NAME", False);
  netatom[NetWMIcon] = XInternAtom(dpy, "_NET_WM_ICON", False);
  netatom[NetWMState] = XInternAtom(dpy, "_NET_WM_STATE", False);
  netatom[NetWMCheck] = XInternAtom(dpy, "_NET_SUPPORTING_WM_CHECK", False);
  netatom[NetWMFullscreen] =
      XInternAtom(dpy, "_NET_WM_STATE_FULLSCREEN", False);
  netatom[NetWMStateHidden] =
      XInternAtom(dpy, "_NET_WM_STATE_HIDDEN", False);
  netatom[NetWMWindowType] = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE", False);
  netatom[NetWMSkipTaskbar] =
      XInternAtom(dpy, "_NET_WM_STATE_SKIP_TASKBAR", False);
  netatom[NetWMWindowTypeDialog] =
      XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_DIALOG", False);
  netatom[NetWMWindowOpacity] =
      XInternAtom(dpy, "_NET_WM_WINDOW_OPACITY", False);
  netatom[NetWMBypassCompositor] =
      XInternAtom(dpy, "_NET_WM_BYPASS_COMPOSITOR", False);
  netatom[NetClientList] = XInternAtom(dpy, "_NET_CLIENT_LIST", False);
  xatom[Manager] = XInternAtom(dpy, "MANAGER", False);
  xatom[Xembed] = XInternAtom(dpy, "_XEMBED", False);
  xatom[XembedInfo] = XInternAtom(dpy, "_XEMBED_INFO", False);
  netatom[NetDesktopViewport] =
      XInternAtom(dpy, "_NET_DESKTOP_VIEWPORT", False);
  netatom[NetNumberOfDesktops] =
      XInternAtom(dpy, "_NET_NUMBER_OF_DESKTOPS", False);
  netatom[NetCurrentDesktop] = XInternAtom(dpy, "_NET_CURRENT_DESKTOP", False);
  netatom[NetDesktopNames] = XInternAtom(dpy, "_NET_DESKTOP_NAMES", False);
  netatom[NetClientInfo] = XInternAtom(dpy, "_NET_CLIENT_INFO", False);
  netatom[NetNoAnimation] = XInternAtom(dpy, "_NO_ANIMATION", False);
  netatom[NetBarLeft] = XInternAtom(dpy, "_BAR_LEFT", False);
  /* init cursors */
  cursor[CurNormal] = drw_cur_create(drw, "left_ptr");
  cursor[CurResize] = drw_cur_create(drw, "sizing");
  cursor[CurMove] = drw_cur_create(drw, "fleur");
  cursor[CurResizeHorzArrow] = drw_cur_create(drw, "sb_h_double_arrow");
  cursor[CurResizeVertArrow] = drw_cur_create(drw, "sb_v_double_arrow");
  cursor[CurTopLeft] = drw_cur_create(drw, "top_left_corner");
  cursor[CurTopRight] = drw_cur_create(drw, "top_right_corner");
  cursor[CurBottomLeft] = drw_cur_create(drw, "bottom_left_corner");
  cursor[CurBottomRight] = drw_cur_create(drw, "bottom_right_corner");
  /* init appearance */
  scheme = ecalloc(LENGTH(colors) + 1, sizeof(Clr *));
  scheme[LENGTH(colors)] = drw_scm_create(drw, colors[0], 3);
  for (i = 0; i < LENGTH(colors); i++)
    scheme[i] = drw_scm_create(drw, colors[i], 3);
  drw_clr_create(drw, &clrborder, col_borderbar);
  drw_clr_create(drw, &mpris_scroll_bg_clr, "#a6da95");
  drw_clr_create(drw, &mpris_progress_clr, "#B8E9B4");
  drw_clr_create(drw, &notify_bg, "#1E1D2D");
  drw_clr_create(drw, &notify_fg, "#FFFFFF");
  drw_clr_create(drw, &notify_body, "#CDD6F4");
  {
    Clr control, control_hover;
    drw_clr_create(drw, &control, "#363449");
    drw_clr_create(drw, &control_hover, "#514B70");
    notify_control_scheme[ColFg] = notify_fg;
    notify_control_scheme[ColBg] = control;
    notify_control_scheme[ColBorder] = control;
    notify_control_hover_scheme[ColFg] = notify_fg;
    notify_control_hover_scheme[ColBg] = control_hover;
    notify_control_hover_scheme[ColBorder] = control_hover;

    notify_action_scheme[ColFg] = control;
    notify_action_scheme[ColBg] = notify_bg;
    notify_action_scheme[ColBorder] = notify_bg;
    notify_action_hover_scheme[ColFg] = notify_fg;
    notify_action_hover_scheme[ColBg] = notify_bg;
    notify_action_hover_scheme[ColBorder] = notify_bg;
  }
  notify_summary_scheme[ColFg] = notify_fg;
  notify_summary_scheme[ColBg] = notify_bg;
  notify_summary_scheme[ColBorder] = notify_bg;
  notify_body_scheme[ColFg] = notify_body;
  notify_body_scheme[ColBg] = notify_bg;
  notify_body_scheme[ColBorder] = notify_bg;
  /* init system tray */
  updatesystray();
  /* init bars */
  updatebars();
  notification_init();
  updatestatus();
  updatebarpos(selmon);
  updatepreview();
  updatenumberofdesktops();
  updatecurrentdesktop(selmon->tagset[selmon->seltags]);
  /* supporting window for NetWMCheck */
  wmcheckwin = XCreateSimpleWindow(dpy, root, 0, 0, 1, 1, 0, 0, 0);
  XChangeProperty(dpy, wmcheckwin, netatom[NetWMCheck], XA_WINDOW, 32,
                  PropModeReplace, (unsigned char *)&wmcheckwin, 1);
  XChangeProperty(dpy, wmcheckwin, netatom[NetWMName], utf8string, 8,
                  PropModeReplace, (unsigned char *)"dwm", 3);
  XChangeProperty(dpy, root, netatom[NetWMCheck], XA_WINDOW, 32,
                  PropModeReplace, (unsigned char *)&wmcheckwin, 1);
  XChangeProperty(dpy, root, netatom[NetWMName], utf8string, 8,
                  PropModeReplace, (unsigned char *)"dwm", 3);
  /* EWMH support per view */
  XChangeProperty(dpy, root, netatom[NetSupported], XA_ATOM, 32,
                  PropModeReplace, (unsigned char *)netatom, NetLast);
  setnumdesktops();
  setcurrentdesktop();
  setdesktopnames();
  setviewport();
  XDeleteProperty(dpy, root, netatom[NetClientList]);
  XDeleteProperty(dpy, root, netatom[NetClientInfo]);
  /* select events */
  wa.cursor = cursor[CurNormal]->cursor;
  wa.event_mask = SubstructureRedirectMask | SubstructureNotifyMask |
                  ButtonPressMask | PointerMotionMask | EnterWindowMask |
                  LeaveWindowMask | StructureNotifyMask | PropertyChangeMask |
                  FocusChangeMask;
  XChangeWindowAttributes(dpy, root, CWEventMask | CWCursor, &wa);
  XSelectInput(dpy, root, wa.event_mask);
  grabkeys();
  /* Xkb StateNotify for Alt sidebar tracking */
  if (XkbQueryExtension(dpy, NULL, &xkb_event_base, NULL, NULL, NULL)) {
    XkbSelectEvents(dpy, XkbUseCoreKbd, XkbStateNotifyMask, XkbStateNotifyMask);
    getkblayout();
  }
  focus(NULL);
}
void setviewport(void) {
  long data[] = {0, 0};
  XChangeProperty(dpy, root, netatom[NetDesktopViewport], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 2);
}

void seturgent(Client *c, int urg) {
  XWMHints *wmh;

  c->isurgent = urg;
  if (!(wmh = XGetWMHints(dpy, c->win)))
    return;
  wmh->flags = urg ? (wmh->flags | XUrgencyHint) : (wmh->flags & ~XUrgencyHint);
  XSetWMHints(dpy, c->win, wmh);
  XFree(wmh);
}

void show(Client *c) {
  if (!c || !HIDDEN(c))
    return;

  xmapclient(c);
  c->isautominimized = 0;
  c->fshidden = 0;
  arrange(c->mon);
}

/* Fullscreen hides clients explicitly. Restore that state when the
 * fullscreen client is no longer visible on the monitor, such as after a
 * workspace or monitor move. */
static void restorefullscreenhidden(Monitor *m) {
  Client *c, *it;
  int fullscreenvisible = 0;

  for (c = m->clients; c; c = c->next)
    if (c->isfullscreen && ISVISIBLE(c)) {
      fullscreenvisible = 1;
      break;
    }

  if (fullscreenvisible)
    return;

  for (it = m->clients; it; it = it->next) {
    if (!it->fshidden)
      continue;
    it->fshidden = 0;
    if (ISVISIBLE(it)) {
      xmapclient(it);
      it->isautominimized = 0;
    } else {
      /* Let showhide map it when its workspace becomes visible. */
      it->isautominimized = 1;
    }
  }
}

void showhide(Client *c) {
  if (!c)
    return;
  if (ISVISIBLE(c)) {
    c->lastvisible = 0;
    /* show clients top down */
    if (HIDDEN(c) && c->isautominimized && !c->fshidden) {
      xmapclient(c);
      c->isautominimized = 0;
    }
    XMoveWindow(dpy, c->win, c->x, c->y);
    if ((!c->mon->lt[c->mon->sellt]->arrange || c->isfloating) &&
        !c->isfullscreen)
      resize(c, c->x, c->y, c->w, c->h, 0);
    showhide(c->snext);
  } else {
    if (c->lastvisible == 0)
      c->lastvisible = time(NULL);
    /* hide clients bottom up */
    showhide(c->snext);
    if (!HIDDEN(c) && shouldminimize(c))
      c->isautominimized = 1;
    if (!HIDDEN(c))
      xunmapclient(c);
    else if (shouldminimize(c))
      setclientstate(c, IconicState);
  }
}

void showtagpreview(int tag) {
  if (!selmon->previewshow || !tag_preview) {
    XUnmapWindow(dpy, selmon->tagwin);
    return;
  }

  if (selmon->tagmap[tag]) {
    XSetWindowBackgroundPixmap(dpy, selmon->tagwin, selmon->tagmap[tag]);
    XCopyArea(dpy, selmon->tagmap[tag], selmon->tagwin, drw->gc, 0, 0,
              selmon->mw / scalepreview, selmon->mh / scalepreview, 0, 0);
     XFlush(dpy);
    XMapWindow(dpy, selmon->tagwin);
  } else
    XUnmapWindow(dpy, selmon->tagwin);
}

void spawn(const Arg *arg) {
  struct sigaction sa;

  if (fork() == 0) {
    if (dpy)
      close(ConnectionNumber(dpy));
    setsid();
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    sa.sa_handler = SIG_DFL;
    sigaction(SIGCHLD, &sa, NULL);
    execvp(((char **)arg->v)[0], (char **)arg->v);
    die("dwm: execvp '%s' failed:", ((char **)arg->v)[0]);
  }
}

void setclienttagprop(Client *c) {
  long data[] = {(long)c->tags, (long)c->mon->num};
  XChangeProperty(dpy, c->win, netatom[NetClientInfo], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 2);
}

static void setworkspaceanimation(Monitor *m, int val) {
  Client *c;
  long data = val;
  for (c = m->clients; c; c = c->next)
    if (ISVISIBLE(c))
      XChangeProperty(dpy, c->win, netatom[NetNoAnimation], XA_CARDINAL, 32,
                      PropModeReplace, (unsigned char *)&data, 1);
}

void switchtag(void) {
  int i;
  unsigned int occ = 0;
  Client *c;
  Imlib_Image image;

  for (c = selmon->clients; c; c = c->next)
    occ |= c->tags;
  for (i = 0; i < LENGTH(tags); i++) {
    if (selmon->tagset[selmon->seltags] & 1 << i) {
      if (selmon->tagmap[i] != 0) {
        XFreePixmap(dpy, selmon->tagmap[i]);
        selmon->tagmap[i] = 0;
      }
      if (occ & 1 << i && tag_preview) {
        image = imlib_create_image(sw, sh);
        if (!image)
          continue;
        imlib_context_set_image(image);
        imlib_context_set_display(dpy);
        imlib_context_set_visual(DefaultVisual(dpy, screen));
        imlib_context_set_drawable(RootWindow(dpy, screen));
        imlib_copy_drawable_to_image(0, selmon->mx, selmon->my, selmon->mw,
                                     selmon->mh, 0, 0, 1);
        selmon->tagmap[i] =
            XCreatePixmap(dpy, selmon->tagwin, selmon->mw / scalepreview,
                          selmon->mh / scalepreview, DefaultDepth(dpy, screen));
        imlib_context_set_drawable(selmon->tagmap[i]);
        imlib_render_image_part_on_drawable_at_size(
            0, 0, selmon->mw, selmon->mh, 0, 0, selmon->mw / scalepreview,
            selmon->mh / scalepreview);
        if (imlib_context_get_image())
          imlib_free_image();
      }
    }
  }
}

void tabmode(const Arg *arg) {
  if (arg && arg->i >= 0)
    selmon->showtab = arg->ui % showtab_nmodes;
  else
    selmon->showtab = (selmon->showtab + 1) % showtab_nmodes;
  arrange(selmon);
}

void tag(const Arg *arg) {
  Client *c;
  if (selmon->sel && arg->ui & TAGMASK) {
    c = selmon->sel;
    selmon->sel->tags = arg->ui & TAGMASK;
    setclienttagprop(c);
    focus(NULL);
    arrange(selmon);
  }
}

void tagmon(const Arg *arg) {
  if (!selmon->sel || !mons->next)
    return;
  sendmon(selmon->sel, dirtomon(arg->i));
}

void togglebar(const Arg *arg) {
  selmon->showbar = selmon->pertag->showbars[selmon->pertag->curtag] =
      !selmon->showbar;
  updatebarpos(selmon);
  resizebarwin(selmon);
  if (showsystray) {
    XWindowChanges wc;
    if (!selmon->showbar)
      wc.y = -bh;
    else if (selmon->showbar) {
      wc.y = selmon->gappoh;
      if (!selmon->topbar)
        wc.y = selmon->mh - bh + selmon->gappoh;
    }
    XConfigureWindow(dpy, systray->win, CWY, &wc);
  }
  arrange(selmon);
}

void togglefloating_noarrange(Client *c) {
  if (!c || c->isfullscreen || c->issticky)
    return;
  c->isfloating = !c->isfloating || c->isfixed;
  if (c->isfloating)
    resize(c, c->x, c->y, c->w, c->h, 0);
}

void togglefloating(const Arg *arg) {
  Client *c = dragclient ? dragclient : selmon->sel;

  if (!c)
    return;
  if (c->isfullscreen || c->issticky) /* no support for fullscreen or sticky windows */
    return;

  c->isfloating = !c->isfloating || c->isfixed;
  if (c->isfloating)
    resize(c, c->x, c->y, c->w, c->h, 0);

  /* Do not tile or reposition the client while a pointer drag is active. */
  if (dragclient)
    return;

  arrange(selmon);
}

void togglefullscr(const Arg *arg) {
  if (!selmon->sel)
    return;

  XEvent e = {0};
  e.type = ClientMessage;
  e.xclient.window = selmon->sel->win;
  e.xclient.message_type = netatom[NetWMState];
  e.xclient.format = 32;
  e.xclient.data.l[0] = 2;  /* _NET_WM_STATE_TOGGLE */
  e.xclient.data.l[1] = netatom[NetWMFullscreen];
  e.xclient.data.l[2] = 0;
  XSendEvent(dpy, root, False, SubstructureRedirectMask, &e);

  /* MAY BE NEXT TIME ( need someone to implement this )
    Add auto close pip when enter fullscreen and reopen when exit fullscreen
    - 1st run close pip if exists when entering fullscreen
      - save piprante to reopen when exiting fullscreen
    - 2nd run reopen pip if it was closed when exiting fullscreen
      - add fake focus to parent to trigger focus event, this will fake browser to allow spawn pip again
  */
}


void toggletag(const Arg *arg) {
  unsigned int newtags;

  if (!selmon->sel)
    return;
  newtags = selmon->sel->tags ^ (arg->ui & TAGMASK);
  if (newtags) {
    selmon->sel->tags = newtags;
    setclienttagprop(selmon->sel);
    focus(NULL);
    updatecurrentdesktop(selmon->tagset[selmon->seltags]);
    arrange(selmon);
  }
}

void toggleview(const Arg *arg) {
  unsigned int newtagset =
      selmon->tagset[selmon->seltags] ^ (arg->ui & TAGMASK);
  int i;

  if (newtagset) {
    prepare_workspace_switch(selmon, selmon->tagset[selmon->seltags], newtagset);
    switchtag();
    selmon->tagset[selmon->seltags] = newtagset;

    if (newtagset == ~0) {
      selmon->pertag->prevtag = selmon->pertag->curtag;
      selmon->pertag->curtag = 0;
    }

    /* test if the user did not select the same tag */
    if (!(newtagset & 1 << (selmon->pertag->curtag - 1))) {
      selmon->pertag->prevtag = selmon->pertag->curtag;
      for (i = 0; !(newtagset & 1 << i); i++)
        ;
      selmon->pertag->curtag = i + 1;
    }

    /* apply settings for this view */
    selmon->nmaster = selmon->pertag->nmasters[selmon->pertag->curtag];
    selmon->mfact = selmon->pertag->mfacts[selmon->pertag->curtag];
    selmon->sellt = selmon->pertag->sellts[selmon->pertag->curtag];
    selmon->lt[selmon->sellt] =
        selmon->pertag->ltidxs[selmon->pertag->curtag][selmon->sellt];
    selmon->lt[selmon->sellt ^ 1] =
        selmon->pertag->ltidxs[selmon->pertag->curtag][selmon->sellt ^ 1];

    if (selmon->showbar != selmon->pertag->showbars[selmon->pertag->curtag])
      togglebar(NULL);

    updatecurrentdesktop(selmon->tagset[selmon->seltags]);
    focus(NULL);
    arrange(selmon);
  }
}

void hidewin(const Arg *arg) {
  if (!selmon->sel)
    return;
  Client *c = (Client *)selmon->sel;
  hide(c);
  hiddenWinStack[++hiddenWinStackTop] = c;
}


void restorewin(const Arg *arg) {
  int i = hiddenWinStackTop;
  while (i > -1) {
    if (HIDDEN(hiddenWinStack[i]) &&
        (hiddenWinStack[i]->tags & selmon->tagset[selmon->seltags])) {
      show(hiddenWinStack[i]);
      focus(hiddenWinStack[i]);
      restack(selmon);
      for (int j = i; j < hiddenWinStackTop; ++j) {
        hiddenWinStack[j] = hiddenWinStack[j + 1];
      }
      --hiddenWinStackTop;
      return;
    }
    --i;
  }
}


void togglewin(const Arg *arg) {
  if (selmon->sel) hidewin(arg);
  else restorewin(arg);
}


void unfocus(Client *c, int setfocus) {
  if (!c)
    return;
  grabbuttons(c, 0);
  XSetWindowBorder(dpy, c->win, scheme[SchemeNorm][ColBorder].pixel);
  if (setfocus) {
    XSetInputFocus(dpy, root, RevertToPointerRoot, CurrentTime);
    XDeleteProperty(dpy, root, netatom[NetActiveWindow]);
  }
}

void unmanage(Client *c, int destroyed) {
  Monitor *m = c->mon;
  XWindowChanges wc;

  if (!destroyed && (c->isfullscreen || c->issticky))
    clearwindowopacity(c);

  if (c == selmon->sel || (c->isfullscreen && fullscreen_st))
    updatefullscreenstatus(NULL);

  /* cleanup sticky metadata if the removed client was sticky */
  if (c == stickywin) {
    stickywin = NULL;
    stick_state = 0;
  }

  detach(c);
  detachstack(c);
  freeicon(c);

  if (!destroyed) {
    wc.border_width = c->oldbw;
    XGrabServer(dpy); /* avoid race conditions */
    XSetErrorHandler(xerrordummy);
    XSelectInput(dpy, c->win, NoEventMask);
    XConfigureWindow(dpy, c->win, CWBorderWidth, &wc); /* restore border */
    XUngrabButton(dpy, AnyButton, AnyModifier, c->win);
    setclientstate(c, WithdrawnState);
   XFlush(dpy);
    XSetErrorHandler(xerror);
    XUngrabServer(dpy);
  }

  /* if the dying window was fullscreen, restore any clients it hid */
  if (c->isfullscreen) {
    Client *it;
    for (it = m->stack; it; it = it->snext) {
      if (it->fshidden) {
        it->fshidden = 0;
        xmapclient(it);
        it->isautominimized = 0;
      }
    }
  }

  if (c->pipparent) {
    c->pipparent->pipparent = NULL;
    c->pipparent = NULL;
  }

  free(c);
  updateclientlist();
  arrange(m);

  /* Focus the client currently under the pointer. */
  {
    Window dummy, pointerwin;
    int pointerx, pointery, pointerxwin, pointerywin;
    unsigned int pointermask;
    Client *pointerc = NULL;

    if (XQueryPointer(dpy, root, &dummy, &pointerwin, &pointerx, &pointery,
                      &pointerxwin, &pointerywin, &pointermask))
      pointerc = wintoclient(pointerwin);
    focus(pointerc);
  }
}

void unmapnotify(XEvent *e) {
  Client *c;
  XUnmapEvent *ev = &e->xunmap;
  XWindowAttributes wa;

  if ((c = wintoclient(ev->window))) {
    if (c->wm_unmapped) {
      c->wm_unmapped = 0;
      return;
    }
    if (ev->send_event)
      setclientstate(c, WithdrawnState);
    else if (ISVISIBLE(c) && !c->isiconic) {
      /* A stale UnmapNotify from our own earlier hide can arrive after we
       * already re-mapped the window. If X still reports the window as
       * viewable, this event does not describe the current state - drop it. */
      if (XGetWindowAttributes(dpy, c->win, &wa) &&
          wa.map_state == IsViewable)
        return;
      unmanage(c, 0);
    }
  } else if ((c = wintosystrayicon(ev->window))) {
    XMapRaised(dpy, c->win);
    updatesystray();
  }
}

void updatebars(void) {
  unsigned int w;
  Monitor *m;
  XSetWindowAttributes wa = {.override_redirect = True,
                             .background_pixmap = ParentRelative,
                             .event_mask = ButtonPressMask | KeyPressMask |
                                           ExposureMask | PointerMotionMask |
                                           EnterWindowMask | LeaveWindowMask};

  XClassHint ch = {"dwm", "dwm"};
  for (m = mons; m; m = m->next) {
    if (m->barwin)
      continue;
    w = m->ww;
    if (showsystray && m == systraytomon(m))
      w -= getsystraywidth();
    m->barwin = XCreateWindow(
        dpy, root, m->wx + m->gappov, m->by, w - 2 * m->gappov, bh, 0,
        DefaultDepth(dpy, screen), CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->barwin, cursor[CurNormal]->cursor);
    XMapRaised(dpy, m->barwin);
    m->bartitlewin = XCreateWindow(
        dpy, root, m->wx, m->by, 1, bh, 0, DefaultDepth(dpy, screen),
        CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->bartitlewin, cursor[CurNormal]->cursor);
    XUnmapWindow(dpy, m->bartitlewin);
    XSetClassHint(dpy, m->bartitlewin, &ch);
    m->barcenterwin = XCreateWindow(
        dpy, root, m->wx, m->by, 1, bh, 0, DefaultDepth(dpy, screen),
        CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->barcenterwin, cursor[CurNormal]->cursor);
    XUnmapWindow(dpy, m->barcenterwin);
    XSetClassHint(dpy, m->barcenterwin, &ch);
    m->barkbwin = XCreateWindow(
        dpy, root, m->wx, m->by, 1, bh, 0, DefaultDepth(dpy, screen),
        CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->barkbwin, cursor[CurNormal]->cursor);
    XUnmapWindow(dpy, m->barkbwin);
    XSetClassHint(dpy, m->barkbwin, &ch);
    m->barrightwin = XCreateWindow(
        dpy, root, m->wx, m->by, 1, bh, 0, DefaultDepth(dpy, screen),
        CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->barrightwin, cursor[CurNormal]->cursor);
    XUnmapWindow(dpy, m->barrightwin);
    XSetClassHint(dpy, m->barrightwin, &ch);
    /* keep the clock above the status bar so the animation can grow over it */
    {
      XWindowChanges wc = {0};
      wc.sibling = m->barrightwin;
      wc.stack_mode = Above;
      XConfigureWindow(dpy, m->barcenterwin, CWSibling | CWStackMode, &wc);
    }
    m->tabwin = XCreateWindow(
        dpy, root, m->wx + m->gappov, m->ty, m->ww - 2 * m->gappov, th, 0,
        DefaultDepth(dpy, screen), CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->tabwin, cursor[CurNormal]->cursor);
    XMapRaised(dpy, m->tabwin);
    /* sidebar window */
    XSetWindowAttributes swa = {.override_redirect = True,
                                .event_mask = ButtonPressMask | EnterWindowMask |
                                              PointerMotionMask};
    m->sidebarwin = XCreateWindow(
        dpy, root, m->mx + m->gappov * 2, m->my + m->mh / 3, SIDEBAR_WIDTH, m->mh / 3, 0,
        DefaultDepth(dpy, screen), CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWEventMask, &swa);
    XChangeProperty(dpy, m->sidebarwin, netatom[NetBarLeft], XA_ATOM, 32,
                    PropModeReplace, (unsigned char *)&netatom[NetBarLeft], 1);
    /* don't map here — only show when apps exist */
    m->sidebarvisible = 0;
    XSetClassHint(dpy, m->sidebarwin, &ch);
    XSetClassHint(dpy, m->barwin, &ch);
  }
}

void updatepreview(void) {
  Monitor *m;

  XSetWindowAttributes wa = {.override_redirect = True,
                             .background_pixmap = ParentRelative,
                             .event_mask = ButtonPressMask | ExposureMask};
  for (m = mons; m; m = m->next) {
    m->tagwin = XCreateWindow(
        dpy, root, m->wx, m->by + bh, m->mw / scalepreview, m->mh / scalepreview, 0,
        DefaultDepth(dpy, screen), CopyFromParent, DefaultVisual(dpy, screen),
        CWOverrideRedirect | CWBackPixmap | CWEventMask, &wa);
    XDefineCursor(dpy, m->tagwin, cursor[CurNormal]->cursor);
    XMapRaised(dpy, m->tagwin);
    XUnmapWindow(dpy, m->tagwin);
  }
}

void updatebarpos(Monitor *m) {
  Client *c;
  int nvis = 0;

  m->wy = m->my;
  m->wh = m->mh;

  for (c = m->clients; c; c = c->next) {
    if (ISVISIBLE(c))
      ++nvis;
  }

  if (m->showtab == showtab_always ||
      ((m->showtab == showtab_auto) && (nvis > 1) &&
       (m->lt[m->sellt]->arrange == monocle))) {
    m->topbar = !toptab;
    m->wh -=
        th + ((m->topbar == toptab && m->showbar) ? 0 : m->gappoh) - m->gappoh;
    m->ty = m->toptab ? m->wy + ((m->topbar && m->showbar) ? 0 : m->gappoh)
                      : m->wy + m->wh - m->gappoh;
    if (m->toptab)
      m->wy += th + ((m->topbar && m->showbar) ? 0 : m->gappoh) - m->gappoh;
  } else {
    m->ty = -th - m->gappoh;
    m->topbar = topbar;
  }
  if (m->showbar) {
    if (floatbar) {
      m->wh = m->wh - m->gappoh - bh;
      m->by = m->topbar ? m->wy + m->gappoh : m->wy + m->wh;
    } else {
      m->wh = m->wh - bh;
      m->by = m->topbar ? m->wy : m->wy + m->wh;
    }
    if (m->topbar) {
      m->wy += floatbar ? bh + m->gappoh : bh;
    }
  } else
    m->by = -bh - m->gappoh;
  /* resize sidebar */
  if (m->sidebarwin) {
    calcsidebar(m);
    int sidebary = m->my + (m->mh - m->sidebarh) / 2;
    XMoveResizeWindow(dpy, m->sidebarwin, m->mx + m->gappov * 2, sidebary, m->sidebarw, m->sidebarh);
  }
}

void updateclientlist() {
  Client *c;
  Monitor *m;

  XDeleteProperty(dpy, root, netatom[NetClientList]);
  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      XChangeProperty(dpy, root, netatom[NetClientList], XA_WINDOW, 32,
                      PropModeAppend, (unsigned char *)&(c->win), 1);
}

void updatenumberofdesktops(void) {
  long data[] = {LENGTH(tags)};
  XChangeProperty(dpy, root, netatom[NetNumberOfDesktops], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 1);
}

void updatecurrentdesktop(unsigned int tagset) {
  long data[] = {0};
  unsigned int i, mask = 1;

  for (i = 0; i < LENGTH(tags); i++, mask <<= 1) {
    if (tagset & mask) {
      data[0] = i;
      break;
    }
  }

  XChangeProperty(dpy, root, netatom[NetCurrentDesktop], XA_CARDINAL, 32,
                  PropModeReplace, (unsigned char *)data, 1);
}

int updategeom(void) {
  int dirty = 0;

#ifdef XINERAMA
  if (XineramaIsActive(dpy)) {
    int i, j, n, nn;
    Client *c;
    Monitor *m;
    XineramaScreenInfo *info = XineramaQueryScreens(dpy, &nn);
    XineramaScreenInfo *unique = NULL;

    for (n = 0, m = mons; m; m = m->next, n++)
      ;
    /* only consider unique geometries as separate screens */
    unique = ecalloc(nn, sizeof(XineramaScreenInfo));
    for (i = 0, j = 0; i < nn; i++)
      if (isuniquegeom(unique, j, &info[i]))
        memcpy(&unique[j++], &info[i], sizeof(XineramaScreenInfo));
    XFree(info);
    nn = j;
    /* new monitors if nn > n */
    for (i = n; i < nn; i++) {
      for (m = mons; m && m->next; m = m->next)
        ;
      if (m)
        m->next = createmon();
      else
        mons = createmon();
    }
    for (i = 0, m = mons; i < nn && m; m = m->next, i++)
      if (i >= n || unique[i].x_org != m->mx || unique[i].y_org != m->my ||
          unique[i].width != m->mw || unique[i].height != m->mh) {
        dirty = 1;
        m->num = i;
        m->mx = m->wx = unique[i].x_org;
        m->my = m->wy = unique[i].y_org;
        m->mw = m->ww = unique[i].width;
        m->mh = m->wh = unique[i].height;
        updatebarpos(m);
      }
    /* removed monitors if n > nn */
    for (i = nn; i < n; i++) {
      for (m = mons; m && m->next; m = m->next)
        ;
      while ((c = m->clients)) {
        dirty = 1;
        m->clients = c->next;
        detachstack(c);
        c->mon = mons;
        attach(c);
        attachstack(c);
      }
      if (m == selmon)
        selmon = mons;
      cleanupmon(m);
    }
    free(unique);
  } else
#endif /* XINERAMA */
  {    /* default monitor setup */
    if (!mons)
      mons = createmon();
    if (mons->mw != sw || mons->mh != sh) {
      dirty = 1;
      mons->mw = mons->ww = sw;
      mons->mh = mons->wh = sh;
      updatebarpos(mons);
    }
  }
  if (dirty) {
    selmon = mons;
    selmon = wintomon(root);
  }
  return dirty;
}

void updatenumlockmask(void) {
  unsigned int i, j;
  XModifierKeymap *modmap;

  numlockmask = 0;
  modmap = XGetModifierMapping(dpy);
  for (i = 0; i < 8; i++)
    for (j = 0; j < modmap->max_keypermod; j++)
      if (modmap->modifiermap[i * modmap->max_keypermod + j] ==
          XKeysymToKeycode(dpy, XK_Num_Lock))
        numlockmask = (1 << i);
  XFreeModifiermap(modmap);
}

void updatesizehints(Client *c) {
  long msize;
  XSizeHints size;

  if (!XGetWMNormalHints(dpy, c->win, &size, &msize))
    /* size is uninitialized, ensure that size.flags aren't used */
    size.flags = PSize;
  if (size.flags & PBaseSize) {
    c->basew = size.base_width;
    c->baseh = size.base_height;
  } else if (size.flags & PMinSize) {
    c->basew = size.min_width;
    c->baseh = size.min_height;
  } else
    c->basew = c->baseh = 0;
  if (size.flags & PResizeInc) {
    c->incw = size.width_inc;
    c->inch = size.height_inc;
  } else
    c->incw = c->inch = 0;
  if (size.flags & PMaxSize) {
    c->maxw = size.max_width;
    c->maxh = size.max_height;
  } else
    c->maxw = c->maxh = 0;
  if (size.flags & PMinSize) {
    c->minw = size.min_width;
    c->minh = size.min_height;
  } else if (size.flags & PBaseSize) {
    c->minw = size.base_width;
    c->minh = size.base_height;
  } else
    c->minw = c->minh = 0;
  if (size.flags & PAspect) {
    c->mina = (float)size.min_aspect.y / size.min_aspect.x;
    c->maxa = (float)size.max_aspect.x / size.max_aspect.y;
  } else
    c->maxa = c->mina = 0.0;
  c->isfixed = (c->maxw && c->maxh && c->maxw == c->minw && c->maxh == c->minh);
  c->hintsvalid = 1;
}

void updatestatus(void) {
  strcpy(stext, "dwm-" VERSION);
  drawbars();
  updatesystray();
}

void updatesystrayicongeom(Client *i, int w, int h) {
  int rh = bh - vertpadbar;
  if (i) {
    i->h = rh;
    if (w == h)
      i->w = rh;
    else if (h == rh)
      i->w = w;
    else
      i->w = (int)((float)rh * ((float)w / (float)h));
    i->y = i->y + vertpadbar / 2;
    applysizehints(i, &(i->x), &(i->y), &(i->w), &(i->h), False);
    /* force icons into the systray dimensions if they don't want to */
    if (i->h > rh) {
      if (i->w == i->h)
        i->w = rh;
      else
        i->w = (int)((float)rh * ((float)i->w / (float)i->h));
      i->h = rh;
    }
  }
}

void updatesystrayiconstate(Client *i, XPropertyEvent *ev) {
  long flags;
  int code = 0;

  if (!showsystray || !i || ev->atom != xatom[XembedInfo] ||
      !(flags = getatomprop(i, xatom[XembedInfo])))
    return;

  if (flags & XEMBED_MAPPED && !i->tags) {
    i->tags = 1;
    code = XEMBED_WINDOW_ACTIVATE;
    XMapRaised(dpy, i->win);
    setclientstate(i, NormalState);
  } else if (!(flags & XEMBED_MAPPED) && i->tags) {
    i->tags = 0;
    code = XEMBED_WINDOW_DEACTIVATE;
    XUnmapWindow(dpy, i->win);
    setclientstate(i, WithdrawnState);
  } else
    return;
  sendevent(i->win, xatom[Xembed], StructureNotifyMask, CurrentTime, code, 0,
            systray->win, XEMBED_EMBEDDED_VERSION);
}

void updatesystray(void) {
  XSetWindowAttributes wa;
  XWindowChanges wc;
  Client *i;
  Monitor *m = systraytomon(NULL);
  unsigned int x = floatbar ? m->mx + m->mw - m->gappov : m->mx + m->mw;
  unsigned int w = 1;

  if (!showsystray)
    return;
  if (!systray) {
    /* init systray */
    if (!(systray = (Systray *)calloc(1, sizeof(Systray))))
      die("fatal: could not malloc() %u bytes\n", sizeof(Systray));
    systray->win = XCreateSimpleWindow(dpy, root, x, m->by, w, bh, 0, 0,
                                       scheme[SchemeSel][ColBg].pixel);
    wa.event_mask = ButtonPressMask | ExposureMask;
    wa.override_redirect = True;
    wa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
    XSelectInput(dpy, systray->win, SubstructureNotifyMask);
    XChangeProperty(dpy, systray->win, netatom[NetSystemTrayOrientation],
                    XA_CARDINAL, 32, PropModeReplace,
                    (unsigned char *)&netatom[NetSystemTrayOrientationHorz], 1);
    XChangeWindowAttributes(
        dpy, systray->win, CWEventMask | CWOverrideRedirect | CWBackPixel, &wa);
    XUnmapWindow(dpy, systray->win);
    XSetSelectionOwner(dpy, netatom[NetSystemTray], systray->win, CurrentTime);
    if (XGetSelectionOwner(dpy, netatom[NetSystemTray]) == systray->win) {
      sendevent(root, xatom[Manager], StructureNotifyMask, CurrentTime,
                netatom[NetSystemTray], systray->win, 0, 0);
      XSync(dpy, False);
    } else {
      fprintf(stderr, "dwm: unable to obtain system tray.\n");
      free(systray);
      systray = NULL;
      return;
    }
  }
  for (w = 0, i = systray->icons; i; i = i->next) {
    /* make sure the background color stays the same */
    wa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
    XChangeWindowAttributes(dpy, i->win, CWBackPixel, &wa);
    XMapRaised(dpy, i->win);
    w += systrayspacing;
    i->x = w;
    XMoveResizeWindow(dpy, i->win, i->x, vertpadbar / 2, i->w, i->h);
    w += i->w;
    if (i->mon != m)
      i->mon = m;
  }
  if (!w) {
    XUnmapWindow(dpy, systray->win);
    return;
  }
  w += systrayspacing;
  x -= w;
  XMoveResizeWindow(dpy, systray->win, x, m->by, w, bh);
  wc.x = x;
  wc.y = m->by;
  wc.width = w;
  wc.height = bh;
  wc.stack_mode = Above;
  wc.sibling = m->barwin;
  XConfigureWindow(dpy, systray->win,
                   CWX | CWY | CWWidth | CWHeight | CWSibling | CWStackMode,
                   &wc);
  XMapWindow(dpy, systray->win);
  XMapSubwindows(dpy, systray->win);
  /* redraw background */
  XSetForeground(dpy, drw->gc, scheme[SchemeNorm][ColBg].pixel);
  XFillRectangle(dpy, systray->win, drw->gc, 0, 0, w, bh);
  XFlush(dpy);
}

void updatetitle(Client *c) {
  if (!gettextprop(c->win, netatom[NetWMName], c->name, sizeof c->name))
    gettextprop(c->win, XA_WM_NAME, c->name, sizeof c->name);
  if (c->name[0] == '\0') /* hack to mark broken clients */
    strcpy(c->name, broken);
}

void updatewindowtype(Client *c) {
  Atom state = getatomprop(c, netatom[NetWMState]);
  Atom wtype = getatomprop(c, netatom[NetWMWindowType]);

  if (state == netatom[NetWMFullscreen])
    setfullscreen(c, 1);
  if (wtype == netatom[NetWMWindowTypeDialog]) {
    c->iscentered = 1;
    c->isfloating = 1;
    c->isontop = DIALOG_ONTOP_PRIORITY;
  }
}

void updatewmhints(Client *c) {
  XWMHints *wmh;

  if ((wmh = XGetWMHints(dpy, c->win))) {
    if (c == selmon->sel && wmh->flags & XUrgencyHint) {
      wmh->flags &= ~XUrgencyHint;
      XSetWMHints(dpy, c->win, wmh);
    } else
      c->isurgent = (wmh->flags & XUrgencyHint) ? 1 : 0;
    if (wmh->flags & InputHint)
      c->neverfocus = !wmh->input;
    else
      c->neverfocus = 0;
    XFree(wmh);
  }
}

void view(const Arg *arg) {
  int i;
  unsigned int tmptag;
  unsigned int newtagset;

  if ((arg->ui & TAGMASK) == selmon->tagset[selmon->seltags])
    return;
  
  newtagset = arg->ui & TAGMASK ? arg->ui & TAGMASK : selmon->pertag->prevtag;
  updatecurrentdesktop(newtagset);
   XFlush(dpy);
  prepare_workspace_switch(selmon, selmon->tagset[selmon->seltags], newtagset);
  switchtag();
  selmon->seltags ^= 1; /* toggle sel tagset */

  if (arg->ui & TAGMASK) {
    selmon->pertag->prevtag = selmon->pertag->curtag;
    selmon->tagset[selmon->seltags] = arg->ui & TAGMASK;

    if (arg->ui == ~0)
      selmon->pertag->curtag = 0;
    else {
      for (i = 0; !(arg->ui & 1 << i); i++)
        ;
      selmon->pertag->curtag = i + 1;
    }
  } else {
    tmptag = selmon->pertag->prevtag;
    selmon->pertag->prevtag = selmon->pertag->curtag;
    selmon->pertag->curtag = tmptag;
  }

  selmon->nmaster = selmon->pertag->nmasters[selmon->pertag->curtag];
  selmon->mfact = selmon->pertag->mfacts[selmon->pertag->curtag];
  selmon->sellt = selmon->pertag->sellts[selmon->pertag->curtag];
  selmon->lt[selmon->sellt] =
      selmon->pertag->ltidxs[selmon->pertag->curtag][selmon->sellt];
  selmon->lt[selmon->sellt ^ 1] =
      selmon->pertag->ltidxs[selmon->pertag->curtag][selmon->sellt ^ 1];

  if (selmon->showbar != selmon->pertag->showbars[selmon->pertag->curtag])
    togglebar(NULL);

  focus(NULL);
  arrange(selmon);
}

Client *wintoclient(Window w) {
  Client *c;
  Monitor *m;

  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      if (c->win == w)
        return c;
  return NULL;
}

Client *wintosystrayicon(Window w) {
  Client *i = NULL;

  if (!showsystray || !w)
    return i;
  for (i = systray->icons; i && i->win != w; i = i->next)
    ;
  return i;
}

Monitor *wintomon(Window w) {
  int x, y;
  Client *c;
  Monitor *m;

  if (w == root && getrootptr(&x, &y))
    return recttomon(x, y, 1, 1);
  for (m = mons; m; m = m->next)
    if (w == m->barwin || w == m->bartitlewin || w == m->barcenterwin ||
        w == m->barkbwin || w == m->barrightwin || w == m->tabwin)
      return m;
  if ((c = wintoclient(w)))
    return c->mon;
  return selmon;
}

/* There's no way to check accesses to destroyed windows, thus those cases are
 * ignored (especially on UnmapNotify's). Other types of errors call Xlibs
 * default error handler, which may call exit. */
int xerror(Display *dpy, XErrorEvent *ee) {
  if (ee->error_code == BadWindow ||
      (ee->request_code == X_SetInputFocus && ee->error_code == BadMatch) ||
      (ee->request_code == X_PolyText8 && ee->error_code == BadDrawable) ||
      (ee->request_code == X_PolyFillRectangle &&
       ee->error_code == BadDrawable) ||
      (ee->request_code == X_PolySegment && ee->error_code == BadDrawable) ||
      (ee->request_code == X_ConfigureWindow && ee->error_code == BadMatch) ||
      (ee->request_code == X_GrabButton && ee->error_code == BadAccess) ||
      (ee->request_code == X_GrabKey && ee->error_code == BadAccess) ||
      (ee->request_code == X_CopyArea && ee->error_code == BadDrawable))
    return 0;
  fprintf(stderr, "dwm: fatal error: request code=%d, error code=%d\n",
          ee->request_code, ee->error_code);
  return xerrorxlib(dpy, ee); /* may call exit */
}

int xerrordummy(Display *dpy, XErrorEvent *ee) { return 0; }

/* Startup Error handler to check if another window manager
 * is already running. */
int xerrorstart(Display *dpy, XErrorEvent *ee) {
  die("dwm: another window manager is already running");
  return -1;
}

Monitor *systraytomon(Monitor *m) {
  Monitor *t;
  int i, n;
  if (!systraypinning) {
    if (!m)
      return selmon;
    return m == selmon ? m : NULL;
  }
  for (n = 1, t = mons; t && t->next; n++, t = t->next)
    ;
  for (i = 1, t = mons; t && t->next && i < systraypinning; i++, t = t->next)
    ;
  if (systraypinningfailfirst && n < systraypinning)
    return mons;
  return t;
}

void zoom(const Arg *arg) {
  Client *c = selmon->sel;

  if (!selmon->lt[selmon->sellt]->arrange || !c || c->isfloating)
    return;
  if (c == nexttiled(selmon->clients) && !(c = nexttiled(c->next)))
    return;
  pop(c);
}

int main(int argc, char *argv[]) {
  XInitThreads();
  if (argc == 2 && !strcmp("-v", argv[1]))
    die("dwm-" VERSION);
  else if (argc != 1)
    die("usage: dwm [-v]");
  if (!setlocale(LC_CTYPE, "") || !XSupportsLocale())
    fputs("warning: no locale support\n", stderr);
  if (!(dpy = XOpenDisplay(NULL)))
    die("dwm: cannot open display");
  checkotherwm();
  setup();
#ifdef __OpenBSD__
  if (pledge("stdio rpath proc exec", NULL) == -1)
    die("pledge");
#endif /* __OpenBSD__ */
  scan();
  status_start();
  if (CLOCK_ANIMATE)
    sound_monitor_start();
  run();
  cleanup();
  XCloseDisplay(dpy);
  return EXIT_SUCCESS;
}
