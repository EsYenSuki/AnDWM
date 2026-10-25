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
#include <sys/stat.h>
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
#include <GL/gl.h>
#include <GL/glx.h>
#include <ft2build.h>
#include FT_FREETYPE_H
#include <hb.h>
#include <hb-ft.h>

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
#define NOTIFY_PADDING   15
#define NOTIFY_IMAGE_MAX_H 60
#define NOTIFY_IMAGE_RADIUS 16
#define NOTIFY_MAX_TEXT  4096
#define NOTIFY_INPUT_ROW_H 24
#define NOTIFY_BUTTON_H 24
#define NOTIFY_BODY_LINE_GAP 0
#define NOTIFY_BODY_MAX_LINES 4
#define NOTIFY_POPUP_BODY_MAX_LINES 2
#define NOTIFY_POPUP_BODY_HOVER_MAX_LINES 4
#define NOTIFY_HISTORY_BODY_MAX_LINES 2
#define NOTIFY_BODY_LINE_BYTES 1024
#define NOTIFY_HISTORY_FPS 100
#define NOTIFY_ACTION_X  12
#define NOTIFY_TEXT_TOP_OFFSET 3
#define NOTIFY_TEXT_BOTTOM_GAP 6
#define NOTIFY_IMAGE_BUTTON_GAP 2
#define NOTIFY_HISTORY_MAX     10
#define NOTIFY_HISTORY_ENTRY_H 70
#define NOTIFY_HISTORY_MAX_H   400
#define FINDER_MAX_APPS 512
#define FINDER_MAX_TEXT 256
#define FINDER_EDGE 15
#define FINDER_ICON_GAP 8
#define FINDER_MARKER_WIDTH 270
#define FINDER_CURSOR_BLINK_MS 500

typedef struct FinderApp FinderApp;
struct FinderApp {
  char name[FINDER_MAX_TEXT];
  char exec[PATH_MAX];
  char file[PATH_MAX];
  char icon_name[FINDER_MAX_TEXT];
  Picture icon;
  int icon_loaded;
  int recent;
  int score;
};
static FinderApp finder_apps[FINDER_MAX_APPS];
static unsigned int finder_app_count;
static unsigned int finder_order[FINDER_MAX_APPS];
static unsigned int finder_visible;
static char finder_query[FINDER_MAX_TEXT];
static char finder_math_result[64];
static int finder_math_active;
static int finder_math_help_active;
static const char *finder_math_help[] = {
  "+ - * / % ^ ! ( )  f(x) f(a,b)",
  "sqrt cbrt abs exp ln log2 log10",
  "pow hypot mod atan2 min max",
  "sin cos tan asin acos atan",
  "floor ceil round trunc",
  "gcd lcm fact",
  "bitor bitand bitxor bitnot",
  "shl shr deg rad",
  "pi e tau phi epsilon",
  "byte_max word_max dword_max",
  "int_max int_min uint_max",
  "kb mb gb tb true false",
};
static uint64_t finder_cursor_base_ms;
static int finder_cursor_visible = 1;
static size_t finder_cursor;
static Fnt *finder_result_font;
static int finder_active;
static int finder_dirty;
static int finder_loading;
static int finder_icons_pending;
static Visual *finder_argb_visual;
static int finder_argb_depth;
static Colormap finder_argb_colormap;
static int finder_argb_create_failed;
static int finder_selected;
static int finder_scroll;
static char finder_recent[10][PATH_MAX];
static unsigned int finder_recent_count;

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
  uint32_t *img_pixels;
  unsigned int img_w, img_h;
  GLuint img_texture;
  int action_used;
  unsigned int body_wrap_width, body_wrap_count, body_wrap_max_lines;
  int body_wrap_valid;
  char body_wrap_lines[NOTIFY_BODY_MAX_LINES][NOTIFY_BODY_LINE_BYTES];
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
static int notify_image_y, notify_text_y;
static int notify_clock_hovered;
static unsigned int notify_width, notify_height;
static unsigned int notify_count;
static unsigned int notify_history_count;
static int notify_history_scroll;
static int notify_history_scroll_target;
static struct timespec notify_history_scroll_started;
static Clr notify_bg, notify_fg, notify_body, finder_text_clr;
static const char finder_text[] = "#B8B5C8";
static Clr notify_summary_scheme[3], notify_body_scheme[3];
static Clr notify_summary_dim_scheme[3], notify_body_dim_scheme[3];
static Clr notify_control_scheme[3], notify_control_hover_scheme[3];
static Clr notify_action_scheme[3], notify_action_hover_scheme[3];
static int notify_action_x[16], notify_action_w[16];
static int notify_action_y;
static int notify_input_x, notify_input_y, notify_input_w, notify_input_h;
static int notify_input_focus;
static Notification *notify_history_input;
static int notify_hovered;
static int notify_hover = -1;
static Notification *notify_history_hover_entry;
static int notify_history_hover_action = -1;
static struct timespec notify_hover_started;
static struct timespec notify_history_hover_started;
static uint64_t notify_render_cache_hash;
static int notify_render_cache_valid;
static Pixmap notify_history_pixmap;
static GC notify_history_gc;
static Picture notify_history_picture;
static Picture notify_history_mask_picture;
static Picture notify_history_dest_picture;
static Picture notify_history_background_picture;
static Pixmap notify_history_mask_pixmap;
static Pixmap notify_history_background_pixmap;
static Window notify_history_dest_window;
static unsigned int notify_history_pixmap_w, notify_history_pixmap_h;
static unsigned int notify_history_mask_w, notify_history_mask_h;

/* OpenGL notification rendering */
static GLXContext notify_gl_ctx = None;
static GLXFBConfig notify_gl_fbconfig;
static GLXPbuffer notify_gl_pbuffer = None;
static unsigned int notify_gl_pbuffer_w, notify_gl_pbuffer_h;
static int notify_gl_initialized = 0;
typedef void (*NotificationGLBlendFuncSeparate)(GLenum, GLenum, GLenum,
                                                GLenum);
static NotificationGLBlendFuncSeparate notify_gl_blend_func_separate;

/* FreeType + OpenGL font rendering */
typedef struct {
  unsigned int tex_id;
  unsigned int face_index;
  unsigned int glyph_index;
  int w, h;
  int bearing_x, bearing_y;
  int advance;
  int loaded;
} GLGlyph;

#define GL_FONT_MAX_FACES 32
#define GL_FONT_MAX_GLYPHS 2048
typedef struct {
  FT_Face face;
  hb_font_t *hb_font;
  char *file;
  int index;
  double pixel_size;
} GLFontFace;

typedef struct {
  GLFontFace faces[GL_FONT_MAX_FACES];
  unsigned int face_count;
  GLGlyph glyphs[GL_FONT_MAX_GLYPHS];
  unsigned int glyph_count;
  int height;
  double pixel_size;
} GLFont;

static FT_Library ft_lib = NULL;
static GLFont *gl_font = NULL;

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
static void buttonrelease(XEvent *e);
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
static void drawrightbar(Monitor *m, unsigned int rw);
static void drawrightbar_only(void);
static void drawbars(void);
static int status_text_visible(const char *text);
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
static void raisefullscreenoverlays(Monitor *m);
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
static int hasurgentclients(void);
static void demandattention(Client *c);
static void updateurgentborders(void);
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
static void finder(const Arg *arg);
static void finder_close(void);
static int finder_pointer_inside(XButtonEvent *ev);
static void finder_motion(XMotionEvent *ev);
static void finder_focus_pointer(void);
static int finder_keypress(XKeyEvent *ev);
static int finder_buttonpress(XButtonPressedEvent *ev);
static void finder_load_apps(void);
static int finder_load_next_icon(void);
static void finder_load_recent(void);
static void finder_save_recent(void);
static void status_start(void);
static void status_stop(void);
static void status_consume(void);
static int update_mpris_scroll(void);
static void mpris_load_art(unsigned int target_w, unsigned int target_h);
static void mpris_panel_button(XButtonPressedEvent *ev);
static void mpris_panel_motion(XMotionEvent *ev);
static void mpris_panel_draw(Monitor *m, unsigned int w, unsigned int h);
static void mpris_collapse_panel(void);
static void mpris_volume_marker(Monitor *m, int x, int y,
                                unsigned int width, unsigned int height);
static void finder_marker(Monitor *m, int row);
static int mpris_pointer_over_marker(Monitor *m);
static int mpris_pointer_over_bar(Monitor *m);
static int drag_next_event(XEvent *ev);
/* These are defined with the other dwm globals below; the MPRIS helpers are
 * kept near the status worker for readability. */
static int bh;
static Display *dpy;
static Drw *drw;
static Clr **scheme;

#define STATUS_SLOTS 3
#define STATUS_SIZE 1024
#define MPRIS_WIDTH 240
#define MPRIS_SCROLL_GAP 32
#define MPRIS_SCROLL_PAD 8
#define MPRIS_SCROLL_INTERVAL_NS 33333333ULL
#define MPRIS_COMPLETE_THRESHOLD 0.995
#define MPRIS_PANEL_MIN_WIDTH 320
#define MPRIS_PANEL_HOVER_H 2
#define MPRIS_VOLUME_CURVE 9.0
#define MPRIS_VOLUME_MARKER_WIDTH 24
#define MPRIS_VOLUME_MARKER_HOVER_WIDTH 32
#define MPRIS_VOLUME_MARKER_HEIGHT 16
#define MPRIS_VOLUME_MARKER_HOVER_HEIGHT 20
enum status_slot_state { STATUS_FREE, STATUS_WRITING, STATUS_PUBLISHED,
                         STATUS_READING };
typedef struct {
	_Atomic int state;
	char text[STATUS_SIZE];
	char mpris[768];
	char mpris_service[128];
	char mpris_art[PATH_MAX];
	double mpris_progress;
	double mpris_volume;
	int mpris_playing;
	int mpris_present;
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
static int mpris_playing;
static int mpris_present;
static unsigned int mpris_scroll_text_width;
static double mpris_progress = -1.0;
static double mpris_volume = 1.0;
static char mpris_service[128];
static char mpris_art_url[PATH_MAX];
static Picture mpris_art;
static int mpris_art_w, mpris_art_h;
static int mpris_hovered;
static int mpris_marker_hovered;
static int mpris_marker_pressed;
static int mpris_volume_drag;
static Clr mpris_scroll_bg_clr;
static Clr mpris_progress_clr;
static Clr mpris_volume_fill_clr;
static Clr mpris_volume_empty_clr;
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

static int status_dbus_property_double(DBusConnection *connection, const char *service,
                                       const char *property, double *out) {
	DBusMessage *message, *reply;
	DBusMessageIter iter, variant;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	double value;

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
	if (dbus_message_iter_get_arg_type(&variant) != DBUS_TYPE_DOUBLE) {
		dbus_message_unref(reply);
		return 0;
	}
	dbus_message_iter_get_basic(&variant, &value);
	*out = value;
	dbus_message_unref(reply);
	return 1;
}

static int mpris_method(const char *method) {
	DBusConnection *connection;
	DBusMessage *message, *reply;
	if (!mpris_service[0]) return 0;
	connection = dbus_bus_get(DBUS_BUS_SESSION, NULL);
	if (!connection) return 0;
	message = dbus_message_new_method_call(mpris_service, "/org/mpris/MediaPlayer2",
	        "org.mpris.MediaPlayer2.Player", method);
	if (!message) {
		dbus_connection_unref(connection);
		return 0;
	}
	reply = dbus_connection_send_with_reply_and_block(connection, message, 300, NULL);
	dbus_message_unref(message);
	if (reply) dbus_message_unref(reply);
	dbus_connection_unref(connection);
	return reply != NULL;
}

static int mpris_set_volume(double volume) {
	DBusConnection *connection;
	DBusMessage *message;
	DBusMessageIter args, variant;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	const char *property = "Volume";
	const char *signature = "d";
	if (!mpris_service[0]) return 0;
	volume = MAX(0.0, MIN(1.0, volume));
	connection = dbus_bus_get(DBUS_BUS_SESSION, NULL);
	if (!connection) return 0;
	message = dbus_message_new_method_call(mpris_service, "/org/mpris/MediaPlayer2",
	        "org.freedesktop.DBus.Properties", "Set");
	if (!message) {
		dbus_connection_unref(connection);
		return 0;
	}
	dbus_message_iter_init_append(message, &args);
	dbus_message_iter_append_basic(&args, DBUS_TYPE_STRING, &interface);
	dbus_message_iter_append_basic(&args, DBUS_TYPE_STRING, &property);
	dbus_message_iter_open_container(&args, DBUS_TYPE_VARIANT, signature, &variant);
	dbus_message_iter_append_basic(&variant, DBUS_TYPE_DOUBLE, &volume);
	dbus_message_iter_close_container(&args, &variant);
	/* Volume is changed from pointer-motion events.  Waiting for a synchronous
	 * reply here can stall the main X event loop when another DBus client (for
	 * example the notification service) is active.  Queue the Set request and
	 * keep the local slider responsive instead. */
	if (!dbus_connection_send(connection, message, NULL)) {
		dbus_message_unref(message);
		dbus_connection_unref(connection);
		return 0;
	}
	dbus_connection_flush(connection);
	dbus_message_unref(message);
	dbus_connection_unref(connection);
	mpris_volume = volume;
	return 1;
}

/* Map the slider's linear position to a more useful, logarithmic volume
 * response.  The inverse is used for drawing so the marker follows the same
 * curve as the value sent to the player. */
static double mpris_slider_volume(double position) {
	position = MAX(0.0, MIN(1.0, position));
	if (position <= 0.0)
		return 0.0;
	return expm1(position * log1p(MPRIS_VOLUME_CURVE)) /
	       MPRIS_VOLUME_CURVE;
}

static double mpris_volume_position(double volume) {
	volume = MAX(0.0, MIN(1.0, volume));
	if (volume <= 0.0)
		return 0.0;
	return log1p(volume * MPRIS_VOLUME_CURVE) /
	       log1p(MPRIS_VOLUME_CURVE);
}

static double mpris_volume_from_x(int x, int slider_x, int slider_w) {
	double position;

	/* The marker starts at the fill endpoint, so subtract half its width:
	 * clicking the marker's center selects the current endpoint. */
	position = (double)(x - slider_x - MPRIS_VOLUME_MARKER_WIDTH / 2) /
	           MAX(1, slider_w);
	return mpris_slider_volume(position);
}

static int status_mpris_metadata(DBusConnection *connection, const char *service,
                                 char *artist, size_t artistlen,
                                 char *title, size_t titlelen,
                                 char *art, size_t artlen,
                                 int64_t *length_us) {
	DBusMessage *message, *reply;
	DBusMessageIter iter, variant, dict;
	const char *interface = "org.mpris.MediaPlayer2.Player";
	const char *property = "Metadata";
	artist[0] = title[0] = art[0] = '\0';
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
		} else if (!strcmp(key, "mpris:artUrl") &&
		           dbus_message_iter_get_arg_type(&value) == DBUS_TYPE_STRING) {
			const char *s;
			dbus_message_iter_get_basic(&value, &s);
			snprintf(art, artlen, "%s", s ? s : "");
		}
next:
		dbus_message_iter_next(&dict);
	}
	dbus_message_unref(reply);
	return *title != '\0';
}

static int status_mpris(char *out, size_t outlen, char *raw, size_t rawlen,
                        char *service_out, size_t service_len,
                        char *art, size_t artlen, double *progress,
                        double *volume, int *playing) {
	DBusConnection *connection;
	DBusMessage *reply;
	DBusMessageIter iter, names;
	char artist[192], title[384], state[32];
	int64_t position_us = 0, length_us = 0;
	char service[128] = "";
	*progress = -1.0;
	if (playing) *playing = 0;
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
			                               state, sizeof state) &&
			    (!strcmp(state, "Playing") || !strcmp(state, "Paused"))) {
				if (playing) *playing = !strcmp(state, "Playing");
				snprintf(service, sizeof service, "%s", name);
				break;
			}
		}
		dbus_message_iter_next(&names);
	}
	dbus_message_unref(reply);
	if (!service[0] || !status_mpris_metadata(connection, service, artist, sizeof artist,
	                                       title, sizeof title, art, artlen, &length_us)) {
		dbus_connection_unref(connection);
		return 0;
	}
	snprintf(service_out, service_len, "%s", service);
	*volume = 1.0;
	(void)status_dbus_property_double(connection, service, "Volume", volume);
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
	/* Keep the player active while paused, but only expose the scrolling
	 * title segment while playback is actually running. */
	if (!playing || *playing) {
		snprintf(out, outlen,
		         "^c#1E1D2D^ ^b#B8E9B4^ 󰎆^c#1E1D2D^^m^ %s^M^^d^^c#96CDFB^",
		         raw && rawlen ? raw : "");
	} else if (out && outlen) {
		out[0] = '\0';
	}
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
                        char *mpris_service_out, size_t mpris_service_len,
                        char *mpris_art_out, size_t mpris_art_len,
                        double *mpris_progress_out, double *mpris_volume_out,
                        int *mpris_playing_out,
                        int *mpris_present_out,
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
	if (mpris_service_out && mpris_service_len) mpris_service_out[0] = '\0';
	if (mpris_art_out && mpris_art_len) mpris_art_out[0] = '\0';
	if (mpris_volume_out) *mpris_volume_out = 1.0;
	if (mpris_playing_out) *mpris_playing_out = 0;
	if (mpris_present_out) *mpris_present_out = 0;
	has_player = status_mpris(player, sizeof player, mpris_out, mpris_len,
	                          mpris_service_out, mpris_service_len,
	                          mpris_art_out, mpris_art_len,
	                          mpris_progress_out, mpris_volume_out,
	                          mpris_playing_out);
	if (mpris_present_out) *mpris_present_out = has_player;
	sav_icon[0] = '\0';
	if (fan[0] || !strcmp(governor, "performance")) {
		snprintf(sav_icon, sizeof sav_icon, "  %s%s%s", fan,
		         fan[0] && !strcmp(governor, "performance") ? " " : "",
		         !strcmp(governor, "performance") ? "" : "");
	}
	/* A paused player remains present for MPRIS interaction, but the
	 * top-right bar should fall back to the regular status layout rather
	 * than showing an empty player segment. */
	if (has_player && (!mpris_playing_out || *mpris_playing_out)) {
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
	char local[STATUS_SIZE], local_mpris[768], local_service[128], local_art[PATH_MAX];
	char last_mpris[768] = "";
	double local_mpris_progress;
	double local_mpris_volume;
	int local_mpris_playing;
	int local_mpris_present;
	double last_mpris_progress = -1.0;
	unsigned long long last_total = 0, last_active = 0;
	(void)arg;
	while (atomic_load_explicit(&status_running, memory_order_acquire)) {
		/* The bar is covered by fullscreen clients.  Keep status alive, but
		 * reduce hardware/DBus/MPRIS polling while it cannot be seen. */
		struct timespec ts = { .tv_sec = fullscreen_st ? 5 : 1, .tv_nsec = 0 };
		status_make(local, sizeof local, local_mpris, sizeof local_mpris,
		            local_service, sizeof local_service, local_art, sizeof local_art,
		            &local_mpris_progress, &local_mpris_volume,
		            &local_mpris_playing,
		            &local_mpris_present,
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
				memcpy(status_slots[i].mpris_service, local_service, sizeof local_service);
				memcpy(status_slots[i].mpris_art, local_art, sizeof local_art);
				status_slots[i].mpris_progress = local_mpris_progress;
				status_slots[i].mpris_volume = local_mpris_volume;
				status_slots[i].mpris_playing = local_mpris_playing;
				status_slots[i].mpris_present = local_mpris_present;
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
			memcpy(mpris_service, status_slots[i].mpris_service, sizeof mpris_service);
			mpris_service[sizeof mpris_service - 1] = '\0';
			if (strcmp(mpris_art_url, status_slots[i].mpris_art)) {
				memcpy(mpris_art_url, status_slots[i].mpris_art, sizeof mpris_art_url);
				mpris_art_url[sizeof mpris_art_url - 1] = '\0';
				/* The artwork is loaded by mpris_panel_draw with the actual
				 * right-bar width.  Do not cache a placeholder-sized picture. */
				if (mpris_art) {
					XRenderFreePicture(dpy, mpris_art);
					mpris_art = None;
				}
				mpris_art_w = mpris_art_h = 0;
			}
			mpris_progress = status_slots[i].mpris_progress;
			mpris_volume = status_slots[i].mpris_volume;
			mpris_playing = status_slots[i].mpris_playing;
			mpris_present = status_slots[i].mpris_present;
			/* Paused players have no scrolling title, but remain available to
			 * keep the expanded panel and its playback controls alive. */
			mpris_active = mpris_present;
			/* A paused player remains active, so keep the expanded panel while
			 * it is hovered.  If the player disappears, collapse immediately
			 * regardless of where the pointer is. */
			if (!mpris_active && (mpris_hovered || mpris_volume_drag ||
			                     mpris_marker_hovered)) {
				mpris_hovered = 0;
				mpris_volume_drag = 0;
				mpris_marker_hovered = 0;
				mpris_marker_pressed = 0;
				mpris_collapse_panel();
			}
			atomic_store_explicit(&status_slots[i].state, STATUS_FREE, memory_order_release);
			/* Fullscreen does not expose the bar, so defer repainting until it
			 * ends while still consuming the newest status snapshot. */
			if (!fullscreen_st)
				bar_dirty = 1;
			break;
		}
	}
}

static void mpris_load_art(unsigned int target_w, unsigned int target_h) {
	Imlib_Image image;
	const char *path = mpris_art_url;
	DATA32 *data;
	int w, h;
	char file_path[PATH_MAX];

	if (mpris_art)
		XRenderFreePicture(dpy, mpris_art);
	mpris_art = None;
	mpris_art_w = mpris_art_h = 0;
	if (!path[0])
		return;
	if (!strncmp(path, "file://", 7)) {
		path += 7;
		if (*path == '/') {
			snprintf(file_path, sizeof file_path, "%s", path);
			path = file_path;
		}
	} else if (path[0] != '/') {
		/* Avoid blocking dwm on remote artwork URLs. */
		return;
	}
	image = imlib_load_image(path);
	if (!image)
		return;
	imlib_context_set_image(image);
	w = imlib_image_get_width();
	h = imlib_image_get_height();
	data = imlib_image_get_data_for_reading_only();
	if (data && w > 0 && h > 0)
		mpris_art = drw_picture_create_cover(drw, (char *)data, w, h,
		                                      target_w, target_h);
	if (mpris_art) {
		mpris_art_w = target_w;
		mpris_art_h = target_h;
	}
	if (imlib_context_get_image())
		imlib_free_image();
}

static void mpris_panel_button(XButtonPressedEvent *ev) {
	int y = ev->y - bh;
	int control_w = 34;
	int slider_x = control_w + 12;
	int slider_w = MAX(1, (int)statuswidth(stext) - slider_x - 120);
	int volume_x = slider_x + slider_w + 6;
	int previous_x = volume_x + 46;
	int next_x = previous_x + control_w;
	int marker_half_width = (mpris_marker_hovered
		? MPRIS_VOLUME_MARKER_HOVER_WIDTH : MPRIS_VOLUME_MARKER_WIDTH) / 2;
	if (!mpris_active || y < 0 || y >= bh)
		return;
	/* Mouse buttons 4 and 5 are wheel-up and wheel-down in X11.  Handle
	 * them independently of the pointer's horizontal position so scrolling
	 * over any part of the expanded player changes volume in 5% steps. */
	if (ev->button == Button4 || ev->button == Button5) {
		mpris_set_volume(mpris_volume + (ev->button == Button4 ? 0.05 : -0.05));
		bar_dirty = 1;
		return;
	}
	if (ev->x < control_w) {
		mpris_method("PlayPause");
	} else if (ev->x >= slider_x - marker_half_width &&
	           ev->x <= slider_x + slider_w + marker_half_width) {
		mpris_volume_drag = 1;
		mpris_set_volume(mpris_volume_from_x(ev->x, slider_x, slider_w));
	} else if (ev->x >= previous_x && ev->x < next_x) {
		mpris_method("Previous");
	} else if (ev->x >= next_x && ev->x < next_x + control_w) {
		mpris_method("Next");
	}
	bar_dirty = 1;
}

static void mpris_panel_motion(XMotionEvent *ev) {
	int slider_x = 34 + 12;
	int slider_w = MAX(1, (int)statuswidth(stext) - slider_x - 120);
	int marker_half_width = (mpris_marker_hovered
		? MPRIS_VOLUME_MARKER_HOVER_WIDTH : MPRIS_VOLUME_MARKER_WIDTH) / 2;
	if (mpris_volume_drag &&
	    ev->x >= slider_x - marker_half_width &&
	    ev->x <= slider_x + slider_w + marker_half_width)
		mpris_set_volume(mpris_volume_from_x(ev->x, slider_x, slider_w));
}

static void mpris_panel_draw(Monitor *m, unsigned int w, unsigned int h) {
	/* Cover the complete expanded bar, including the upper status half. */
	unsigned int art_y = 0;
	unsigned int panel_h = h ? h : 1;
	int control_w = 34;
	int slider_x = control_w + 12;
	int slider_w;
	int volume_x;
	int previous_x;
	int next_x;
	int track_y;
	int fill_w;
	int knob_x;
	int marker_width = mpris_marker_hovered
		? MPRIS_VOLUME_MARKER_HOVER_WIDTH : MPRIS_VOLUME_MARKER_WIDTH;
	int marker_height = mpris_marker_hovered
		? MPRIS_VOLUME_MARKER_HOVER_HEIGHT : MPRIS_VOLUME_MARKER_HEIGHT;
	char volume[16];
	static const char *controls[] = {"", ""};
	const char *playback = mpris_playing ? controls[0] : "";
	(void)m;
	slider_w = MAX(1, (int)w - slider_x - 120);
	volume_x = slider_x + slider_w + 6;
	previous_x = volume_x + 46;
	next_x = previous_x + control_w;
	track_y = bh + bh / 2 - 2;
	fill_w = (int)(slider_w * mpris_volume_position(mpris_volume) + 0.5);
	/* The marker's left edge starts exactly at the filled track's right edge. */
	knob_x = slider_x + fill_w;
	if (knob_x < slider_x)
		knob_x = slider_x;
	if (knob_x > slider_x + slider_w)
		knob_x = slider_x + slider_w;
	/* Keep the marker center fixed while it grows on hover. */
	if (mpris_marker_hovered)
		knob_x -= (MPRIS_VOLUME_MARKER_HOVER_WIDTH -
		           MPRIS_VOLUME_MARKER_WIDTH) / 2;
	/* Always make the cached picture match the actual expanded bar size.  The
	 * status update can load a small placeholder before rw is known; using that
	 * size for the panel would leave the thumbnail narrower than the bar. */
	if (mpris_art_url[0] &&
	    (!mpris_art || mpris_art_w != (int)w || mpris_art_h != (int)panel_h))
		mpris_load_art(w, panel_h);

	XSetForeground(drw->dpy, drw->gc, scheme[SchemeNorm][ColBg].pixel);
	XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, art_y, w, panel_h);
	if (mpris_art)
		drw_pic(drw, 0, art_y, w, panel_h, mpris_art);
	/* Use one continuous gradient instead of stacked strips, which avoids
	 * visible horizontal banding in the artwork. */
	{
		XFixed stops[] = { XDoubleToFixed(0.0), XDoubleToFixed(0.25),
		                  XDoubleToFixed(1.0) };
		XRenderColor colors[] = {
			{ scheme[SchemeNorm][ColBg].color.red,
			  scheme[SchemeNorm][ColBg].color.green,
			  scheme[SchemeNorm][ColBg].color.blue, 0xFFFF },
			{ scheme[SchemeNorm][ColBg].color.red,
			  scheme[SchemeNorm][ColBg].color.green,
			  scheme[SchemeNorm][ColBg].color.blue, 0xFFFF },
			{ scheme[SchemeNorm][ColBg].color.red,
			  scheme[SchemeNorm][ColBg].color.green,
			  scheme[SchemeNorm][ColBg].color.blue, 0x0000 }
		};
		XLinearGradient linear = {
			{ 0, 0 }, { 0, XDoubleToFixed(panel_h) }
		};
		Picture overlay = XRenderCreateLinearGradient(dpy, &linear, stops,
		                                             colors, LENGTH(stops));
		if (overlay) {
			XRenderComposite(dpy, PictOpOver, overlay, None, drw->picture,
			                 0, 0, 0, 0, 0, art_y, w, panel_h);
			XRenderFreePicture(dpy, overlay);
		}
	}

	/* Draw the transport glyphs without clearing their rectangles, so the
	 * artwork remains visible beneath and between the controls. */
	drw_setscheme(drw, scheme[SchemeTitle]);
	drw_text_transparent(drw, 10, bh + 4, 28, MAX(1, bh - 8), 0,
	                     playback);
	drw_text_transparent(drw, previous_x, bh + 4, 28, MAX(1, bh - 8), 0,
	                     controls[1]);
	drw_text_transparent(drw, next_x, bh + 4, 28, MAX(1, bh - 8), 0, "");
	drw_setscheme(drw, scheme[SchemeNorm]);
	XSetForeground(drw->dpy, drw->gc, mpris_volume_empty_clr.pixel);
	XFillRectangle(drw->dpy, drw->drawable, drw->gc, slider_x, track_y,
	               slider_w, 4);
	if (fill_w > 0) {
		XSetForeground(drw->dpy, drw->gc, mpris_volume_fill_clr.pixel);
		XFillRectangle(drw->dpy, drw->drawable, drw->gc, slider_x, track_y,
		               fill_w, 4);
	}
	/* Connect the filled endpoint to the center of the separate marker. */
	XSetForeground(drw->dpy, drw->gc, mpris_volume_fill_clr.pixel);
	XFillRectangle(drw->dpy, drw->drawable, drw->gc,
	               slider_x + fill_w, track_y + 1, marker_width / 2, 2);
	/* Center the marker vertically on the 4-pixel track. */
	mpris_volume_marker(m, knob_x, track_y + 2 - marker_height / 2,
	                    marker_width, marker_height);
	snprintf(volume, sizeof volume, "%d%%", (int)(mpris_volume * 100.0 + 0.5));
	drw_setscheme(drw, scheme[SchemeTitle]);
	drw_text_transparent(drw, volume_x, bh + 4, 38, MAX(1, bh - 8), 0, volume);
}

static void notification_init(void);
static void notification_shutdown(void);
static int notification_gl_init(unsigned int w, unsigned int h);
static GLFont *gl_font_create(void);
static int gl_font_add_face(GLFont *font, const char *file, int index,
                            double pixel_size);
static unsigned int gl_font_text_width(const char *text);
static void notification_dispatch(void);
static void notification_tick(void);
static double notification_elapsed(const struct timespec *started);
static void notification_draw(void);
static void notification_draw_foreground(int history);
static void notification_present_layers(int history);
static int notification_history_background_create(void);
static int notification_history_mask_create(unsigned int w, unsigned int h);
static void map_center_window(Window win, int x, int y, unsigned int w,
                              unsigned int h, int fade);
static int notification_foreground_pass;
static int notification_background_only;
static void notification_advance(void);
static void notification_clear_queue(void);
static void notification_emit_closed(Notification *n, uint32_t reason);
static void notification_emit_action(Notification *n, const char *action);
static void notification_emit_input(Notification *n);
static int notification_buttonpress(XButtonPressedEvent *ev);
static int notification_input_keypress(XKeyEvent *ev);
static void notification_update_layout(Notification *n);
static uint32_t notification_utf8_next(const char **text);
static void notification_motion(XMotionEvent *ev);
static void notification_history_motion(XMotionEvent *ev);
static void notification_history_draw(void);
static void notification_history_layout(void);
static void notification_history_add(Notification *n);
static void notification_history_show(void);
static void notification_history_hide(void);
static int notification_center_active(void);
static void notification_update_wm_class(Window win, int active, int history,
                                         int finder);
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
static int lrpad;  /* sum of left and right  for text */
static int (*xerrorxlib)(Display *, XErrorEvent *);
static unsigned int numlockmask = 0;
static Time last_ev_time;
static void (*handler[LASTEvent])(XEvent *) = {
    [ButtonPress] = buttonpress,
    [ButtonRelease] = buttonrelease,
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
static int urgentflash = 1;
static struct timespec urgentflash_last;
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

static void mpris_collapse_panel(void) {
	if (!selmon)
		return;
	drawbars();
	resizebarwin(selmon);
}

static int update_mpris_scroll(void) {
	struct timespec now_mono;
	unsigned int textw;
	unsigned int cycle;
	uint64_t elapsed_ns = 0;
	uint64_t steps;

  if (fullscreen_st || !mpris_active) {
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
  if (redraw) {
    if (finder_active)
      drawrightbar_only();
    else
      drawbars();
  }
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
  Window mpris_volume_markerwin;
  Window finder_markerwin;
  int finder_marker_mapped;
  int finder_marker_stacked;
  int finder_marker_x;
  int finder_marker_y;
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

/* Keep the volume position as a separate top-level X11 window.  It is placed
 * above the bar for compositors while forwarding its mouse input to the bar. */
static void mpris_volume_marker(Monitor *m, int x, int y,
                                unsigned int width, unsigned int height) {
  Window child;
  int root_x, root_y;
  XWindowChanges wc = {0};
  XClassHint marker_ch = {
    "dwm-mpris-volume-marker",
    mpris_marker_hovered ? "dwm-mpris-volume-marker-larg"
                         : "dwm-mpris-volume-marker"
  };

  if (!m->mpris_volume_markerwin || !mpris_hovered || !mpris_active)
    return;
  XTranslateCoordinates(dpy, m->barrightwin, root, 0, 0,
                        &root_x, &root_y, &child);
  /* Set the compositor-visible class before changing geometry, so a class
   * rule for the previous hover state cannot be applied to the new frame. */
  XSetClassHint(dpy, m->mpris_volume_markerwin, &marker_ch);
  /* Apply the complete geometry in one X request so a resize never becomes
   * visible before its matching position update. */
  wc.x = root_x + x;
  wc.y = root_y + y;
  wc.width = width;
  wc.height = height;
  wc.sibling = m->barrightwin;
  wc.stack_mode = Above;
  XConfigureWindow(dpy, m->mpris_volume_markerwin,
                   CWX | CWY | CWWidth | CWHeight | CWSibling | CWStackMode,
                   &wc);
  {
    XWindowAttributes wa;
    if (XGetWindowAttributes(dpy, m->mpris_volume_markerwin, &wa) &&
        wa.map_state != IsViewable)
      XMapWindow(dpy, m->mpris_volume_markerwin);
  }
}

static void finder_marker(Monitor *m, int row) {
  Window child;
  int root_x, root_y;
  XWindowChanges wc = {0};

  if (!m->finder_markerwin)
    return;
  if (!finder_active || m != selmon || row <= 0) {
    if (m->finder_marker_mapped) {
      XUnmapWindow(dpy, m->finder_markerwin);
      m->finder_marker_mapped = 0;
    }
    m->finder_marker_stacked = 0;
    return;
  }
  XTranslateCoordinates(dpy, m->barcenterwin, root, 0, 0,
                        &root_x, &root_y, &child);
  wc.x = root_x + (finder_width - FINDER_MARKER_WIDTH) / 2;
  wc.y = root_y + row * bh;
  wc.width = FINDER_MARKER_WIDTH;
  wc.height = 38;
  if (!m->finder_marker_mapped || m->finder_marker_x != wc.x ||
      m->finder_marker_y != wc.y) {
    XConfigureWindow(dpy, m->finder_markerwin,
                     CWX | CWY | CWWidth | CWHeight, &wc);
    m->finder_marker_x = wc.x;
    m->finder_marker_y = wc.y;
  }
  if (!m->finder_marker_mapped) {
    /* Raise only on the hidden -> visible transition. Repeatedly raising an
     * opaque root-level sibling on every draw causes visible flashes without
     * a compositor. */
    XMapRaised(dpy, m->finder_markerwin);
    m->finder_marker_mapped = 1;
    m->finder_marker_stacked = 1;
  } else if (!m->finder_marker_stacked) {
    XRaiseWindow(dpy, m->finder_markerwin);
    m->finder_marker_stacked = 1;
  }
}

/* The clock animation normally raises the center bar as it grows.  During
 * the expanded MPRIS panel, keep the right bar above it instead. */
static void
restack_mpris_panel(Monitor *m)
{
	XWindowChanges wc = {0};

	if (!m || m != selmon || !mpris_hovered || !mpris_active ||
	    !m->barrightwin)
		return;
	if (m->barcenterwin) {
		wc.sibling = m->barcenterwin;
		wc.stack_mode = Above;
		XConfigureWindow(dpy, m->barrightwin, CWSibling | CWStackMode, &wc);
	} else {
		XRaiseWindow(dpy, m->barrightwin);
	}
}

static int mpris_pointer_over_marker(Monitor *m) {
  XWindowAttributes wa;
  Window root_return, child_return;
  unsigned int mask;
  int pointer_x, pointer_y, window_x, window_y;

  if (!m->mpris_volume_markerwin ||
      !XGetWindowAttributes(dpy, m->mpris_volume_markerwin, &wa) ||
      wa.map_state != IsViewable)
    return 0;
  if (!XQueryPointer(dpy, root, &root_return, &child_return,
                     &pointer_x, &pointer_y, &window_x, &window_y, &mask))
    return 0;
  XTranslateCoordinates(dpy, m->mpris_volume_markerwin, root, 0, 0,
                        &window_x, &window_y, &child_return);
  return pointer_x >= window_x && pointer_x < window_x + wa.width &&
         pointer_y >= window_y && pointer_y < window_y + wa.height;
}

static int mpris_pointer_over_bar(Monitor *m) {
  XWindowAttributes wa;
  Window root_return, child_return;
  unsigned int mask;
  int pointer_x, pointer_y, window_x, window_y;

  if (!m->barrightwin ||
      !XGetWindowAttributes(dpy, m->barrightwin, &wa) ||
      wa.map_state != IsViewable)
    return 0;
  if (!XQueryPointer(dpy, root, &root_return, &child_return,
                     &pointer_x, &pointer_y, &window_x, &window_y, &mask))
    return 0;
  XTranslateCoordinates(dpy, m->barrightwin, root, 0, 0,
                        &window_x, &window_y, &child_return);
  return pointer_x >= window_x && pointer_x < window_x + wa.width &&
         pointer_y >= window_y && pointer_y < window_y + wa.height;
}

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

static void buttonrelease(XEvent *e) {
  XButtonEvent *ev = &e->xbutton;

  if (mpris_volume_drag || ev->window == selmon->barrightwin ||
      ev->window == selmon->mpris_volume_markerwin)
    mpris_volume_drag = 0;
  if (ev->window == selmon->mpris_volume_markerwin) {
    mpris_marker_pressed = 0;
    if (mpris_pointer_over_marker(selmon)) {
      mpris_marker_hovered = 1;
      drawbars();
    }
  }
  if (!mpris_volume_drag && mpris_hovered &&
      !mpris_pointer_over_bar(selmon) &&
      !mpris_pointer_over_marker(selmon)) {
    mpris_hovered = 0;
    drawbars();
    resizebarwin(selmon);
  }
}

void buttonpress(XEvent *e) {
  unsigned int i, x, click;
  int clientbinding;
  int loop;
  Arg arg = {0};
  Client *c;
  Monitor *m;
  XButtonPressedEvent *ev = &e->xbutton;

  /* Finder is modal.  A click on a client or another bar section must not
   * be handled by the normal click bindings while the Finder is open. */
  if (finder_active) {
    if (ev->window == selmon->barcenterwin) {
      finder_buttonpress(ev);
      return;
    }
    if (finder_pointer_inside(ev)) {
      XButtonPressedEvent inside = *ev;
      XWindowAttributes attr;
      if (XGetWindowAttributes(dpy, selmon->barcenterwin, &attr)) {
        inside.window = selmon->barcenterwin;
        inside.x = ev->x_root - attr.x;
        inside.y = ev->y_root - attr.y;
        finder_buttonpress(&inside);
      }
    } else {
      finder_close();
      finder_focus_pointer();
    }
    return;
  }

  if (ev->window == selmon->mpris_volume_markerwin) {
    /* Keep the marker compact during a click/drag. */
    mpris_marker_pressed = 1;
    if (mpris_marker_hovered) {
      mpris_marker_hovered = 0;
      drawbars();
    }
    XButtonPressedEvent forwarded = *ev;
    Window child;
    XTranslateCoordinates(dpy, root, selmon->barrightwin,
                          ev->x_root, ev->y_root, &forwarded.x,
                          &forwarded.y, &child);
    forwarded.window = selmon->barrightwin;
    mpris_panel_button(&forwarded);
    return;
  }

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
    if (mpris_hovered && mpris_active && ev->y >= bh) {
      mpris_panel_button(ev);
      return;
    }
    click = ClkStatusText;
  } else if (ev->window == selmon->barcenterwin) {
    if (finder_active) {
      finder_buttonpress(ev);
      return;
    }
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
  drw_fontset_free(finder_result_font);
  drw_free(drw);
  if (finder_argb_colormap)
    XFreeColormap(dpy, finder_argb_colormap);
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
  if (mon->mpris_volume_markerwin) {
    XUnmapWindow(dpy, mon->mpris_volume_markerwin);
    XDestroyWindow(dpy, mon->mpris_volume_markerwin);
  }
    if (mon->finder_markerwin) {
      XUnmapWindow(dpy, mon->finder_markerwin);
      mon->finder_marker_mapped = 0;
      mon->finder_marker_stacked = 0;
      XDestroyWindow(dpy, mon->finder_markerwin);
  }
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
    if (c != selmon->sel)
      demandattention(c);
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

	if (mpris_hovered && mpris_active)
		w = MAX(w, MPRIS_PANEL_MIN_WIDTH);
	return w + horizpadbar;
}

static int
status_text_visible(const char *text)
{
	if (!text)
		return 0;
	while (*text == ' ' || *text == '\t')
		text++;
	return *text != '\0';
}

static int
status_next_is_scroll(const char *code)
{
	const char *end = strchr(code, '^');

	return end && end[1] == '^' && end[2] == 'm' && end[3] == '^';
}

int drawstatusbar(Monitor *m, int bh, char *stext) {
  int i, w, x, len;
  int expanded = mpris_hovered && mpris_active;
  int content_h = expanded ? bh / 2 : bh;
  int paired_bg = expanded && !mpris_playing;
  int bg_segment = -1;
  int bg_width;
  int text_bg = 0;
  int joins_scroll = 0;
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

  if (!expanded) {
    XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
    XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, w, content_h);
    drw_setscheme(drw, scheme[LENGTH(colors)]);
    drw->scheme[ColFg] = scheme[SchemeNorm][ColFg];
    drw->scheme[ColBg] = scheme[SchemeNorm][ColBg];
    drw_rect(drw, 0, borderpx, w, content_h, 1, 1);
  } else {
    /* The artwork is already behind this pass.  Do not paint a bar-wide
     * background; only an explicit ^b field gets a background below. */
    drw_setscheme(drw, scheme[LENGTH(colors)]);
    drw->scheme[ColFg] = scheme[SchemeNorm][ColFg];
    drw->scheme[ColBg] = scheme[SchemeNorm][ColBg];
  }

  /* process status text */
  i = -1;
  while (text[++i]) {
    if (text[i] == '^' && !isCode) {
      isCode = 1;

      text[i] = '\0';
      joins_scroll = status_next_is_scroll(text + i + 1);
       w = isScroll ? mpris_field_width(text) : TEXTW(text) - lrpad;
         if (isScroll) {
          double progress = mpris_progress;
          unsigned int progressw = 0;
          if (progress >= 0.0) {
            if (progress > 1.0) progress = 1.0;
            if (progress >= MPRIS_COMPLETE_THRESHOLD) progress = 1.0;
            progressw = (unsigned int)(progress * w + 0.5);
          }
           if (expanded && text_bg && status_text_visible(text)) {
             XSetForeground(drw->dpy, drw->gc, drw->scheme[ColBg].pixel);
              bg_width = MAX(1, w +
                               (paired_bg && !(bg_segment & 1) ? lrpad + 1 : 0) -
                                (expanded && bg_segment >= 0 &&
                                 !isScroll &&
                                 !joins_scroll &&
                                 (!paired_bg || (bg_segment & 1)) ? 2 : 0));
              XFillRectangle(drw->dpy, drw->drawable, drw->gc, x,
                             borderpx + vertpadbar / 2, bg_width,
                             bh - vertpadbar);
            }
            mpris_scroll_text_width = drw_text_scroll_progress(
                drw, x, borderpx + vertpadbar / 2, w,
                 bh - vertpadbar, MPRIS_SCROLL_PAD, text, mpris_scroll_px,
               MPRIS_SCROLL_GAP, 0,
               expanded && (!text_bg || !status_text_visible(text))
                   ? (const Clr *)-1 : &mpris_scroll_bg_clr,
              progress >= 0.0 ? &mpris_progress_clr : NULL,
              progressw);
        }
        else {
          if (expanded && text_bg && status_text_visible(text)) {
            XSetForeground(drw->dpy, drw->gc, drw->scheme[ColBg].pixel);
            bg_width = MAX(1, w +
                             (paired_bg && !(bg_segment & 1) ? lrpad + 1 : 0) -
                              (expanded && bg_segment >= 0 &&
                               !isScroll &&
                               !joins_scroll &&
                               (!paired_bg || (bg_segment & 1)) ? 2 : 0));
            XFillRectangle(drw->dpy, drw->drawable, drw->gc, x,
                            borderpx + vertpadbar / 2, bg_width,
                            bh - vertpadbar);
          }
          if (expanded)
            drw_text_transparent(drw, x, borderpx + vertpadbar / 2, w,
                                 bh - vertpadbar, 0, text);
          else
            drw_text(drw, x, borderpx + vertpadbar / 2, w, bh - vertpadbar,
                     0, text, 0);
        }

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
           text_bg = 1;
           bg_segment++;
           i += 7;
        } else if (text[i] == 'd') {
          drw->scheme[ColFg] = scheme[SchemeNorm][ColFg];
          drw->scheme[ColBg] = scheme[SchemeNorm][ColBg];
          text_bg = 0;
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
      if (expanded && text_bg && status_text_visible(text)) {
        XSetForeground(drw->dpy, drw->gc, drw->scheme[ColBg].pixel);
         bg_width = MAX(1, w +
                          (paired_bg && !(bg_segment & 1) ? lrpad + 1 : 0) -
                          (expanded && bg_segment >= 0 &&
                           (!paired_bg || (bg_segment & 1)) ? 2 : 0));
         XFillRectangle(drw->dpy, drw->drawable, drw->gc, x,
             borderpx + vertpadbar / 2, bg_width,
            bh - vertpadbar);
      }
       mpris_scroll_text_width = drw_text_scroll_progress(
           drw, x, borderpx + vertpadbar / 2, w,
            bh - vertpadbar, MPRIS_SCROLL_PAD, text, mpris_scroll_px,
          MPRIS_SCROLL_GAP, 0,
          expanded && (!text_bg || !status_text_visible(text))
              ? (const Clr *)-1 : &mpris_scroll_bg_clr,
          progress >= 0.0 ? &mpris_progress_clr : NULL,
          progressw);
    }
    else {
      if (expanded && text_bg && status_text_visible(text)) {
        XSetForeground(drw->dpy, drw->gc, drw->scheme[ColBg].pixel);
        XFillRectangle(drw->dpy, drw->drawable, drw->gc, x,
                       borderpx + vertpadbar / 2, w + lrpad + 1,
                       bh - vertpadbar);
      }
      if (expanded)
         drw_text_transparent(drw, x, borderpx + vertpadbar / 2, w,
                              bh - vertpadbar, 0, text);
      else
        drw_text(drw, x, borderpx + vertpadbar / 2, w, bh - vertpadbar, 0,
                 text, 0);
    }
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

static void finder_expand_path(const char *path, char *out, size_t size) {
  const char *home = getenv("HOME");
  if (path[0] == '~' && path[1] == '/' && home)
    snprintf(out, size, "%s/%s", home, path + 2);
  else
    snprintf(out, size, "%s", path);
}

static void finder_math_skip(const char **input) {
  while (isspace((unsigned char)**input))
    (*input)++;
}

static int finder_math_expression(const char **input, double *value);
static int finder_math_unary(const char **input, double *value);

static int finder_math_identifier(const char **input, char *name, size_t size) {
  const char *start = *input;
  size_t len;

  if (!isalpha((unsigned char)**input) && **input != '_')
    return 0;
  (*input)++;
  while (isalnum((unsigned char)**input) || **input == '_')
    (*input)++;
  len = (size_t)(*input - start);
  if (len >= size)
    return 0;
  memcpy(name, start, len);
  name[len] = '\0';
  return 1;
}

/* Parse a parenthesised argument list.  Commas separate arguments, but they
 * are not expression operators, so the normal expression parser stops at the
 * next comma or closing parenthesis. */
static int finder_math_args(const char **input, double *args, int max,
                            int *count) {
  finder_math_skip(input);
  if (**input != '(')
    return 0;
  (*input)++;
  *count = 0;
  finder_math_skip(input);
  if (**input == ')') {
    (*input)++;
    return 1;
  }
  while (*count < max) {
    if (!finder_math_expression(input, &args[*count]))
      return 0;
    (*count)++;
    finder_math_skip(input);
    if (**input == ',') {
      (*input)++;
      continue;
    }
    if (**input == ')') {
      (*input)++;
      return 1;
    }
    return 0;
  }
  return 0;
}

/* Bit operations use exact non-negative integers up to 2^53. */
static int finder_math_u64(double value, unsigned long long *out) {
  if (!isfinite(value) || value < 0.0 || value > 9007199254740992.0 ||
      floor(value) != value)
    return 0;
  *out = (unsigned long long)value;
  return 1;
}

static int finder_math_i64(double value, long long *out) {
  if (!isfinite(value) || value < -9007199254740992.0 ||
      value > 9007199254740992.0 || floor(value) != value)
    return 0;
  *out = (long long)value;
  return 1;
}

static int finder_math_apply(const char *name, const double *args, int count,
                             double *value) {
  double v, a, b;
  int i;

  if (count == 1) {
    v = args[0];
    if (!strcasecmp(name, "sqrt")) {
      if (v < 0.0)
        return 0;
      *value = sqrt(v);
    } else if (!strcasecmp(name, "cbrt")) {
      *value = cbrt(v);
    } else if (!strcasecmp(name, "abs")) {
      *value = fabs(v);
    } else if (!strcasecmp(name, "exp")) {
      *value = exp(v);
    } else if (!strcasecmp(name, "ln") || !strcasecmp(name, "log")) {
      if (v <= 0.0)
        return 0;
      *value = log(v);
    } else if (!strcasecmp(name, "log2")) {
      if (v <= 0.0)
        return 0;
      *value = log2(v);
    } else if (!strcasecmp(name, "log10")) {
      if (v <= 0.0)
        return 0;
      *value = log10(v);
    } else if (!strcasecmp(name, "sin")) {
      *value = sin(v);
    } else if (!strcasecmp(name, "cos")) {
      *value = cos(v);
    } else if (!strcasecmp(name, "tan")) {
      *value = tan(v);
    } else if (!strcasecmp(name, "asin")) {
      if (v < -1.0 || v > 1.0)
        return 0;
      *value = asin(v);
    } else if (!strcasecmp(name, "acos")) {
      if (v < -1.0 || v > 1.0)
        return 0;
      *value = acos(v);
    } else if (!strcasecmp(name, "atan")) {
      *value = atan(v);
    } else if (!strcasecmp(name, "floor")) {
      *value = floor(v);
    } else if (!strcasecmp(name, "ceil")) {
      *value = ceil(v);
    } else if (!strcasecmp(name, "round")) {
      *value = round(v);
    } else if (!strcasecmp(name, "trunc")) {
      *value = trunc(v);
    } else if (!strcasecmp(name, "deg")) {
      *value = v * 180.0 / 3.14159265358979323846;
    } else if (!strcasecmp(name, "rad")) {
      *value = v * 3.14159265358979323846 / 180.0;
    } else if (!strcasecmp(name, "fact")) {
      if (v < 0.0 || v > 170.0 || floor(v) != v)
        return 0;
      *value = 1.0;
      for (i = 2; i <= (int)v; i++)
        *value *= i;
    } else if (!strcasecmp(name, "bitnot")) {
      long long n;
      if (!finder_math_i64(v, &n))
        return 0;
      *value = (double)(~n);
    } else {
      return 0;
    }
    return isfinite(*value);
  }

  if (count != 2)
    return 0;
  a = args[0];
  b = args[1];
  if (!strcasecmp(name, "pow")) {
    *value = pow(a, b);
  } else if (!strcasecmp(name, "hypot")) {
    *value = hypot(a, b);
  } else if (!strcasecmp(name, "mod")) {
    if (b == 0.0)
      return 0;
    *value = fmod(a, b);
  } else if (!strcasecmp(name, "atan2")) {
    *value = atan2(a, b);
  } else if (!strcasecmp(name, "min")) {
    *value = MIN(a, b);
  } else if (!strcasecmp(name, "max")) {
    *value = MAX(a, b);
  } else if (!strcasecmp(name, "gcd")) {
    unsigned long long x, y, t;
    if (!finder_math_u64(a, &x) || !finder_math_u64(b, &y))
      return 0;
    while (y) {
      t = x % y;
      x = y;
      y = t;
    }
    *value = (double)x;
  } else if (!strcasecmp(name, "lcm")) {
    unsigned long long x, y, t, g;
    if (!finder_math_u64(a, &x) || !finder_math_u64(b, &y))
      return 0;
    if (x == 0 || y == 0) {
      *value = 0.0;
      return 1;
    }
    {
      unsigned long long xx = x, yy = y;
      while (yy) {
        t = xx % yy;
        xx = yy;
        yy = t;
      }
      g = xx;
    }
    if ((double)(x / g) * (double)y > 9007199254740992.0)
      return 0;
    *value = (double)((x / g) * y);
  } else if (!strcasecmp(name, "bitor") ||
             !strcasecmp(name, "bitand") ||
             !strcasecmp(name, "bitxor")) {
    long long x, y;
    if (!finder_math_i64(a, &x) || !finder_math_i64(b, &y))
      return 0;
    if (!strcasecmp(name, "bitor"))
      *value = (double)(x | y);
    else if (!strcasecmp(name, "bitand"))
      *value = (double)(x & y);
    else
      *value = (double)(x ^ y);
  } else if (!strcasecmp(name, "shl") || !strcasecmp(name, "shr")) {
    long long x, n;
    if (!finder_math_i64(a, &x) || !finder_math_i64(b, &n) ||
        n < 0 || n > 62)
      return 0;
    if (!strcasecmp(name, "shl"))
      *value = (double)((unsigned long long)x << (unsigned int)n);
    else
      *value = (double)((unsigned long long)x >> (unsigned int)n);
  } else {
    return 0;
  }
  return isfinite(*value);
}

static int finder_math_constant(const char *name, double *value) {
  if (!strcasecmp(name, "pi"))
    *value = 3.14159265358979323846;
  else if (!strcasecmp(name, "e"))
    *value = 2.71828182845904523536;
  else if (!strcasecmp(name, "tau"))
    *value = 6.28318530717958647692;
  else if (!strcasecmp(name, "phi"))
    *value = 1.61803398874989484820;
  else if (!strcasecmp(name, "epsilon"))
    *value = 2.22044604925031308085e-16;
  else if (!strcasecmp(name, "byte_max"))
    *value = 255.0;
  else if (!strcasecmp(name, "word_max"))
    *value = 65535.0;
  else if (!strcasecmp(name, "dword_max"))
    *value = 4294967295.0;
  else if (!strcasecmp(name, "int_max"))
    *value = 2147483647.0;
  else if (!strcasecmp(name, "int_min"))
    *value = -2147483648.0;
  else if (!strcasecmp(name, "uint_max"))
    *value = 4294967295.0;
  else if (!strcasecmp(name, "kb"))
    *value = 1024.0;
  else if (!strcasecmp(name, "mb"))
    *value = 1048576.0;
  else if (!strcasecmp(name, "gb"))
    *value = 1073741824.0;
  else if (!strcasecmp(name, "tb"))
    *value = 1099511627776.0;
  else if (!strcasecmp(name, "true"))
    *value = 1.0;
  else if (!strcasecmp(name, "false"))
    *value = 0.0;
  else
    return 0;
  return 1;
}

static int finder_math_primary(const char **input, double *value) {
  char name[32];
  char *end;
  double number, args[2];
  int count;

  finder_math_skip(input);
  if (**input == '(') {
    (*input)++;
    if (!finder_math_expression(input, value))
      return 0;
    finder_math_skip(input);
    if (**input != ')')
      return 0;
    (*input)++;
    return 1;
  }
  if (isalpha((unsigned char)**input) || **input == '_') {
    if (!finder_math_identifier(input, name, sizeof(name)))
      return 0;
    finder_math_skip(input);
    if (**input == '(') {
      if (!finder_math_args(input, args, (int)LENGTH(args), &count))
        return 0;
      return finder_math_apply(name, args, count, value);
    }
    return finder_math_constant(name, value);
  }
  errno = 0;
  number = strtod(*input, &end);
  if (end == *input || errno == ERANGE || !isfinite(number))
    return 0;
  *input = end;
  *value = number;
  return 1;
}

static int finder_math_postfix(const char **input, double *value) {
  double fact;
  int i;

  if (!finder_math_primary(input, value))
    return 0;
  for (;;) {
    finder_math_skip(input);
    if (**input != '!')
      return 1;
    (*input)++;
    if (!isfinite(*value) || *value < 0.0 || *value > 170.0 ||
        floor(*value) != *value)
      return 0;
    fact = 1.0;
    for (i = 2; i <= (int)*value; i++)
      fact *= i;
    *value = fact;
  }
}

static int finder_math_power(const char **input, double *value) {
  double rhs;

  if (!finder_math_postfix(input, value))
    return 0;
  finder_math_skip(input);
  if (**input == '^') {
    (*input)++;
    if (!finder_math_unary(input, &rhs))
      return 0;
    *value = pow(*value, rhs);
    if (!isfinite(*value))
      return 0;
  }
  return 1;
}

static int finder_math_unary(const char **input, double *value) {
  finder_math_skip(input);
  if (**input == '+') {
    (*input)++;
    return finder_math_unary(input, value);
  }
  if (**input == '-') {
    (*input)++;
    if (!finder_math_unary(input, value))
      return 0;
    *value = -*value;
    return 1;
  }
  return finder_math_power(input, value);
}

static int finder_math_term(const char **input, double *value) {
  double rhs;
  char op;

  if (!finder_math_unary(input, value))
    return 0;
  for (;;) {
    finder_math_skip(input);
    op = **input;
    if (op != '*' && op != '/' && op != '%')
      return 1;
    (*input)++;
    if (!finder_math_unary(input, &rhs))
      return 0;
    if (op == '*') {
      *value *= rhs;
    } else {
      if (rhs == 0.0)
        return 0;
      if (op == '/')
        *value /= rhs;
      else
        *value = fmod(*value, rhs);
    }
    if (!isfinite(*value))
      return 0;
  }
}

static int finder_math_expression(const char **input, double *value) {
  double rhs;
  char op;

  if (!finder_math_term(input, value))
    return 0;
  for (;;) {
    finder_math_skip(input);
    op = **input;
    if (op != '+' && op != '-')
      return 1;
    (*input)++;
    if (!finder_math_term(input, &rhs))
      return 0;
    if (op == '+')
      *value += rhs;
    else
      *value -= rhs;
    if (!isfinite(*value))
      return 0;
  }
}

static void finder_update_math(void) {
  const char *input = finder_query;
  double value;
  int has_operator = strpbrk(finder_query, "+-*/%^!()") != NULL;

  finder_math_active = 0;
  finder_math_help_active = 0;
  finder_math_result[0] = '\0';
  if (!finder_query[0])
    return;
  if (!strcasecmp(finder_query, "math")) {
    finder_math_help_active = 1;
    return;
  }
  if (!has_operator) {
    char name[32];

    finder_math_skip(&input);
    if (finder_math_identifier(&input, name, sizeof(name))) {
      finder_math_skip(&input);
      if (*input == '\0' && finder_math_constant(name, &value)) {
        snprintf(finder_math_result, sizeof(finder_math_result), "%.15g",
                 value);
        finder_math_active = 1;
      }
    }
    return;
  }
  if (!finder_math_expression(&input, &value))
    return;
  finder_math_skip(&input);
  if (*input != '\0')
    return;
  snprintf(finder_math_result, sizeof(finder_math_result), "%.15g", value);
  finder_math_active = 1;
}

static uint64_t finder_monotonic_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)ts.tv_nsec / 1000000ULL;
}

static void finder_cursor_reset(void) {
  finder_cursor_base_ms = finder_monotonic_ms();
  finder_cursor_visible = 1;
}

static int finder_cursor_state(void) {
  uint64_t elapsed = finder_monotonic_ms() - finder_cursor_base_ms;
  return ((elapsed / FINDER_CURSOR_BLINK_MS) & 1ULL) == 0;
}

static size_t finder_cursor_prev(const char *text, size_t pos) {
  if (pos == 0)
    return 0;
  pos--;
  while (pos > 0 && ((unsigned char)text[pos] & 0xc0) == 0x80)
    pos--;
  return pos;
}

static size_t finder_cursor_next(const char *text, size_t pos) {
  size_t len = strlen(text);
  if (pos >= len)
    return len;
  pos++;
  while (pos < len && ((unsigned char)text[pos] & 0xc0) == 0x80)
    pos++;
  return pos;
}

static int finder_matches(const FinderApp *app) {
  if (finder_math_active || finder_math_help_active)
    return 0;
  if (!finder_query[0])
    return 1;
  return strcasestr(app->name, finder_query) ||
         strcasestr(app->exec, finder_query);
}

static int finder_cmp(const void *a, const void *b) {
  const FinderApp *aa = a, *bb = b;
  if (aa->recent != bb->recent)
    return bb->recent - aa->recent;
  return strcasecmp(aa->name, bb->name);
}

/* Rank how closely an application name matches the query.  A complete or
 * prefix match is more relevant than a match at a word boundary, which in
 * turn is more relevant than an arbitrary substring.  Command-only matches
 * stay visible but sort below every name match. */
static int finder_name_score(const char *name) {
  const char *match;
  size_t qlen = strlen(finder_query);
  int score;

  if (strcasecmp(name, finder_query) == 0)
    return 100000;
  if (strncasecmp(name, finder_query, qlen) == 0)
    return 90000;
  match = strcasestr(name, finder_query);
  if (!match)
    return 0;
  score = (match > name && !isalnum((unsigned char)match[-1])) ? 70000 : 50000;
  return score - (int)(match - name) * 10;
}

static int finder_match_score(const FinderApp *app) {
  int score;

  if (!finder_query[0])
    return 0;
  if ((score = finder_name_score(app->name)) != 0)
    return score;
  return strcasestr(app->exec, finder_query) ? 10000 : 0;
}

static int finder_rank_cmp(const void *a, const void *b) {
  const FinderApp *aa = &finder_apps[*(const unsigned int *)a];
  const FinderApp *bb = &finder_apps[*(const unsigned int *)b];

  if (aa->score != bb->score)
    return bb->score - aa->score;
  if (aa->recent != bb->recent)
    return bb->recent - aa->recent;
  return strcasecmp(aa->name, bb->name);
}

/* Build the visible result order.  Without a query this preserves the
 * recents-first list; while searching, textual relevance wins and recency is
 * only used to break ties. */
static void finder_rank(void) {
  finder_visible = 0;
  for (unsigned int i = 0; i < finder_app_count; i++) {
    if (!finder_matches(&finder_apps[i]))
      continue;
    finder_apps[i].score = finder_match_score(&finder_apps[i]);
    finder_order[finder_visible++] = i;
  }
  qsort(finder_order, finder_visible, sizeof(finder_order[0]),
        finder_rank_cmp);
}

static void finder_icon_path(const FinderApp *app, char *out, size_t size) {
  const char *home = getenv("HOME");
  const char *name = app->icon_name;
  static const char *roots[] = {
    "/usr/local/share/icons", "/usr/share/icons", NULL
  };
  static const char *sizes[] = {
    "scalable", "512x512", "384x384", "256x256", "192x192",
    "128x128", "96x96", "64x64", "48x48", "32x32", "24x24",
    "22x22", "16x16", "512", "384", "256", "192", "128", "96",
    "64", "48", "32", "24", "22", "16", NULL
  };
  static const char *extensions[] = {"png", "svg", "xpm", NULL};
  char root[PATH_MAX], candidate[PATH_MAX];
  DIR *dir;
  struct dirent *entry;
  unsigned int i, j;

  out[0] = '\0';
  if (!name[0])
    return;
  if (name[0] == '/') {
    snprintf(out, size, "%s", name);
    return;
  }
  /* An Icon= value may already include an extension, but most desktop files
   * contain a theme icon name without one. */
  if (strchr(name, '.')) {
    if (home) {
      snprintf(candidate, sizeof(candidate), "%s/.local/share/icons/%s", home, name);
      if (access(candidate, R_OK) == 0) {
        snprintf(out, size, "%s", candidate);
        return;
      }
    }
    for (i = 0; roots[i]; i++) {
      snprintf(candidate, sizeof(candidate), "%s/%s", roots[i], name);
      if (access(candidate, R_OK) == 0) {
        snprintf(out, size, "%s", candidate);
        return;
      }
    }
    snprintf(candidate, sizeof(candidate), "/usr/share/pixmaps/%s", name);
    if (access(candidate, R_OK) == 0) {
      snprintf(out, size, "%s", candidate);
      return;
    }
  }

  /* Check every installed icon theme, not only hicolor.  Themes such as
   * Papirus and Breeze commonly store the application icons there. */
  for (i = 0; roots[i] || (home && i == 0); i++) {
    const char *base = roots[i];
    if (i == 0 && home) {
      snprintf(root, sizeof(root), "%s/.local/share/icons", home);
      base = root;
    }
    if (!base)
      continue;
    dir = opendir(base);
    if (!dir)
      continue;
    while ((entry = readdir(dir))) {
      if (entry->d_name[0] == '.')
        continue;
      for (j = 0; sizes[j]; j++) {
        unsigned int k;
        for (k = 0; extensions[k]; k++) {
          snprintf(candidate, sizeof(candidate), "%s/%s/%s/apps/%s.%s",
                   base, entry->d_name, sizes[j], name, extensions[k]);
          if (access(candidate, R_OK) == 0) {
            snprintf(out, size, "%s", candidate);
            closedir(dir);
            return;
          }
        }
      }
    }
    closedir(dir);
  }

  for (i = 0; extensions[i]; i++) {
    snprintf(candidate, sizeof(candidate), "/usr/share/pixmaps/%s.%s",
             name, extensions[i]);
    if (access(candidate, R_OK) == 0) {
      snprintf(out, size, "%s", candidate);
      return;
    }
  }
}

static void finder_load_icon(FinderApp *app) {
  char path[PATH_MAX];
  Imlib_Image image;
  DATA32 *data;
  int w, h;

  finder_icon_path(app, path, sizeof(path));
  if (!path[0] || !(image = imlib_load_image(path)))
    return;
  imlib_context_set_image(image);
  w = imlib_image_get_width();
  h = imlib_image_get_height();
  data = imlib_image_get_data_for_reading_only();
  if (data && w > 0 && h > 0)
    /* Always run icon data through the Imlib2 scaling path.  The fast path in
     * drw_picture_create_resized assumes the source stride/format matches an
     * XImage exactly, which is not true for all PNG/SVG loaders and results
     * in an empty ARGB picture for many desktop icons. */
    app->icon = drw_picture_create_cover(drw, (char *)data, w, h, 22, 22);
  if (image && imlib_context_get_image())
    imlib_free_image();
}

static void finder_free_icons(void) {
  for (unsigned int i = 0; i < finder_app_count; i++)
    if (finder_apps[i].icon) {
      XRenderFreePicture(dpy, finder_apps[i].icon);
      finder_apps[i].icon = None;
    }
}

/* The application list itself is rebuilt from the XDG desktop directories,
 * but the recent order is learned state and should survive restarting dwm or
 * logging in again. */
static int finder_recent_path(char *path, size_t size, int create_dirs) {
  const char *state = getenv("XDG_STATE_HOME");
  const char *home = getenv("HOME");
  char dir[PATH_MAX];

  if (state && state[0] == '/') {
    snprintf(dir, sizeof(dir), "%s/dwm", state);
  } else if (home && home[0]) {
    snprintf(dir, sizeof(dir), "%s/.local/state/dwm", home);
    if (create_dirs) {
      char local[PATH_MAX], state_dir[PATH_MAX];
      snprintf(local, sizeof(local), "%s/.local", home);
      snprintf(state_dir, sizeof(state_dir), "%s/.local/state", home);
      (void)mkdir(local, 0700);
      (void)mkdir(state_dir, 0700);
    }
  } else {
    return 0;
  }
  if (create_dirs)
    (void)mkdir(dir, 0700);
  return snprintf(path, size, "%s/finder-recent", dir) < (int)size;
}

static void finder_load_recent(void) {
  char path[PATH_MAX], line[PATH_MAX];
  FILE *fp;

  finder_recent_count = 0;
  if (!finder_recent_path(path, sizeof(path), 0) ||
      !(fp = fopen(path, "r")))
    return;
  while (finder_recent_count < LENGTH(finder_recent) &&
         fgets(line, sizeof(line), fp)) {
    line[strcspn(line, "\r\n")] = '\0';
    if (!line[0])
      continue;
    snprintf(finder_recent[finder_recent_count],
             sizeof(finder_recent[finder_recent_count]), "%s", line);
    finder_recent_count++;
  }
  fclose(fp);
}

static void finder_save_recent(void) {
  char path[PATH_MAX], temp[PATH_MAX];
  FILE *fp;

  if (!finder_recent_path(path, sizeof(path), 1))
    return;
  if (snprintf(temp, sizeof(temp), "%s.tmp", path) >= (int)sizeof(temp))
    return;
  if (!(fp = fopen(temp, "w")))
    return;
  for (unsigned int i = 0; i < finder_recent_count; i++)
    fprintf(fp, "%s\n", finder_recent[i]);
  if (fclose(fp) == 0)
    (void)rename(temp, path);
  else
    (void)unlink(temp);
}

static void finder_load_apps(void) {
  unsigned int i;
  finder_free_icons();
  finder_app_count = 0;
  for (i = 0; finder_app_dirs[i] && finder_app_count < FINDER_MAX_APPS; i++) {
    char dirpath[PATH_MAX];
    DIR *dir;
    struct dirent *entry;
    finder_expand_path(finder_app_dirs[i], dirpath, sizeof(dirpath));
    if (!(dir = opendir(dirpath)))
      continue;
    while ((entry = readdir(dir)) && finder_app_count < FINDER_MAX_APPS) {
      char path[PATH_MAX], line[PATH_MAX + 32], *value;
      FILE *fp;
      FinderApp *app;
      if (!strstr(entry->d_name, ".desktop"))
        continue;
      snprintf(path, sizeof(path), "%s/%s", dirpath, entry->d_name);
      if (!(fp = fopen(path, "r")))
        continue;
      app = &finder_apps[finder_app_count];
      memset(app, 0, sizeof(*app));
      while (fgets(line, sizeof(line), fp)) {
        if (!strncmp(line, "Name=", 5) && !app->name[0])
          snprintf(app->name, sizeof(app->name), "%s", line + 5);
        else if (!strncmp(line, "Exec=", 5) && !app->exec[0])
          snprintf(app->exec, sizeof(app->exec), "%s", line + 5);
        else if (!strncmp(line, "Icon=", 5) && !app->icon_name[0])
          snprintf(app->icon_name, sizeof(app->icon_name), "%s", line + 5);
        else if (!strncmp(line, "NoDisplay=true", 15) ||
                 !strncmp(line, "Hidden=true", 11))
          app->name[0] = '\0';
      }
      fclose(fp);
      if (!app->name[0] || !app->exec[0])
        continue;
      app->name[strcspn(app->name, "\r\n")] = '\0';
      app->exec[strcspn(app->exec, "\r\n")] = '\0';
      app->icon_name[strcspn(app->icon_name, "\r\n")] = '\0';
      /* Desktop field codes are not useful for a launcher without files. */
      while ((value = strchr(app->exec, '%')))
        memmove(value, value + ((value[1] && strchr("fFuUdiCk", value[1])) ? 2 : 1),
                strlen(value + ((value[1] && strchr("fFuUdiCk", value[1])) ? 2 : 1)) + 1);
      snprintf(app->file, sizeof(app->file), "%s", path);
      for (unsigned int r = 0; r < finder_recent_count; r++)
        if (!strcmp(finder_recent[r], app->file)) {
          app->recent = (int)(finder_recent_count - r);
          break;
        }
       finder_app_count++;
    }
    closedir(dir);
  }
  qsort(finder_apps, finder_app_count, sizeof(*finder_apps), finder_cmp);
  finder_rank();
}

/* Decode at most one visible icon per event-loop pass.  Icon lookup can walk
 * several theme directories and image decoding can be expensive, so neither
 * should delay the first Finder frame or a keypress. */
static int finder_load_next_icon(void) {
  int end = MIN((int)finder_visible, finder_scroll + finder_rows);

  for (int i = finder_scroll; i < end; i++) {
    FinderApp *app = &finder_apps[finder_order[i]];
    if (app->icon_loaded)
      continue;
    app->icon_loaded = 1;
    finder_load_icon(app);
    return 1;
  }
  return 0;
}

static int finder_visible_count(void) {
  return (int)finder_visible;
}

/* One row is always reserved for the query.  The remaining rows follow the
 * number of matching applications, up to the configured maximum. */
static int finder_display_rows(void) {
  if (finder_math_active)
    return 2;
  if (finder_math_help_active)
    return 1 + (int)LENGTH(finder_math_help);
  int rows = finder_visible_count() - finder_scroll;
  int app_rows = MAX(0, MIN(finder_rows, rows));
  return 1 + app_rows;
}

static int finder_set_scroll(int scroll) {
  int maxscroll = MAX(0, finder_visible_count() - finder_rows);

  scroll = MAX(0, MIN(maxscroll, scroll));
  if (scroll == finder_scroll)
    return 0;
  finder_scroll = scroll;
  return 1;
}

static FinderApp *finder_selected_app(void) {
  if (finder_selected < 0 || (unsigned int)finder_selected >= finder_visible)
    return NULL;
  return &finder_apps[finder_order[finder_selected]];
}

static void finder_close(void) {
  finder_active = 0;
  finder_loading = 0;
  finder_icons_pending = 0;
  finder_dirty = 1;
  finder_query[0] = '\0';
  finder_math_active = 0;
  finder_math_help_active = 0;
  finder_math_result[0] = '\0';
  finder_cursor = 0;
  finder_cursor_reset();
  finder_selected = 0;
  finder_scroll = 0;
  finder_visible = 0;
  XUngrabPointer(dpy, CurrentTime);
  XUngrabKeyboard(dpy, CurrentTime);
  XSetInputFocus(dpy, root, RevertToParent, CurrentTime);
  resizebarwin(selmon);
  drawbars();
}

static int finder_pointer_inside(XButtonEvent *ev) {
  XWindowAttributes attr;
  if (!selmon || !selmon->barcenterwin ||
      !XGetWindowAttributes(dpy, selmon->barcenterwin, &attr))
    return 0;
  return ev->x_root >= attr.x && ev->x_root < attr.x + (int)attr.width &&
          ev->y_root >= attr.y && ev->y_root < attr.y + (int)attr.height;
}

static void finder_motion(XMotionEvent *ev) {
  XWindowAttributes attr;
  int row, selected;

  if (!finder_active || finder_math_active || finder_math_help_active ||
      !selmon || !selmon->barcenterwin ||
      !XGetWindowAttributes(dpy, selmon->barcenterwin, &attr) ||
      ev->x_root < attr.x || ev->x_root >= attr.x + (int)attr.width ||
      ev->y_root < attr.y || ev->y_root >= attr.y + (int)attr.height)
    return;

  row = (ev->y_root - attr.y) / MAX(1, bh);
  if (row <= 0 || row >= finder_display_rows())
    return;
  selected = finder_scroll + row - 1;
  if (selected == finder_selected)
    return;
  finder_selected = selected;
  finder_dirty = 1;
  finder_icons_pending = 1;
  drawbars();
}

static void finder_focus_pointer(void) {
  Window root_return, child;
  int root_x, root_y, win_x, win_y;
  unsigned int mask;
  Client *c;

  if (!XQueryPointer(dpy, root, &root_return, &child, &root_x, &root_y,
                     &win_x, &win_y, &mask))
    return;
  if ((c = wintoclient(child))) {
    if (c->mon != selmon)
      selmon = c->mon;
    focus(c);
  }
}

static void finder_launch(void) {
  FinderApp *app = finder_selected_app();
  pid_t pid;
  if (!app)
    return;
  if ((pid = fork()) == 0) {
    setsid();
    execl("/bin/sh", "sh", "-c", app->exec, (char *)NULL);
    _exit(127);
  }
  for (unsigned int i = 0; i < finder_recent_count; i++) {
    if (strcmp(finder_recent[i], app->file))
      continue;
    for (unsigned int j = i; j + 1 < finder_recent_count; j++)
      snprintf(finder_recent[j], sizeof(finder_recent[j]), "%s",
               finder_recent[j + 1]);
    finder_recent_count--;
    break;
  }
  for (unsigned int i = MIN(finder_recent_count, LENGTH(finder_recent) - 1);
       i > 0; i--)
    snprintf(finder_recent[i], sizeof(finder_recent[i]), "%s",
             finder_recent[i - 1]);
  snprintf(finder_recent[0], sizeof(finder_recent[0]), "%s", app->file);
  if (finder_recent_count < LENGTH(finder_recent))
    finder_recent_count++;
  finder_save_recent();
  finder_close();
}

static void finder(const Arg *arg) {
  (void)arg;
  /* Keep the modal Finder off fullscreen clients.  It would otherwise raise
   * itself above the fullscreen window and steal keyboard focus.  Closing an
   * already-open Finder is still allowed. */
  if (!finder_active && (fullscreen_st ||
                         (selmon && selmon->sel && selmon->sel->isfullscreen)))
    return;
  finder_active = !finder_active;
  finder_dirty = 1;
  finder_query[0] = '\0';
  finder_math_active = 0;
  finder_math_help_active = 0;
  finder_math_result[0] = '\0';
  finder_cursor = 0;
  finder_cursor_reset();
  finder_selected = 0;
  finder_scroll = 0;
  if (finder_active) {
    /* Open and paint the query row first.  Desktop metadata and icons are
     * loaded by the event loop after this frame is visible. */
    finder_free_icons();
    finder_app_count = 0;
    finder_visible = 0;
    finder_loading = 1;
    finder_icons_pending = 0;
    /* Keep Escape available even if an application changes focus while the
     * Finder is active. */
    XGrabKeyboard(dpy, selmon->barcenterwin, True, GrabModeAsync,
                  GrabModeAsync, CurrentTime);
    /* Client windows normally consume their own ButtonPress events.  Grab
     * the pointer so outside clicks are delivered to dwm and can close the
     * modal Finder instead of falling through to the application. */
     XGrabPointer(dpy, root, False, ButtonPressMask | PointerMotionMask,
                  GrabModeAsync, GrabModeAsync, None, None, CurrentTime);
    XSetInputFocus(dpy, selmon->barcenterwin, RevertToParent, CurrentTime);
     } else {
    finder_loading = 0;
    finder_icons_pending = 0;
    finder_close();
    return;
  }
  resizebarwin(selmon);
  drawbars();
}

static int finder_keypress(XKeyEvent *ev) {
  KeySym keysym = XLookupKeysym(ev, 0);
  char text[64];
  int len, query_changed = 0, cursor_moved = 0;
  size_t n;

  if (!finder_active)
    return 0;
  n = strlen(finder_query);
  if (finder_cursor > n)
    finder_cursor = n;
  if (keysym == XK_Escape) {
    finder_close();
    return 1;
  } else if (keysym == XK_Return || keysym == XK_KP_Enter) {
    finder_launch();
    return 1;
  } else if (keysym == XK_Up) {
    if (finder_selected > 0) finder_selected--;
  } else if (keysym == XK_Down) {
    if (finder_selected + 1 < finder_visible_count())
      finder_selected++;
  } else if (keysym == XK_Left) {
    size_t prev = finder_cursor_prev(finder_query, finder_cursor);
    if (prev != finder_cursor) {
      finder_cursor = prev;
      cursor_moved = 1;
    }
  } else if (keysym == XK_Right) {
    size_t next = finder_cursor_next(finder_query, finder_cursor);
    if (next != finder_cursor) {
      finder_cursor = next;
      cursor_moved = 1;
    }
  } else if (keysym == XK_Home) {
    if (finder_cursor != 0) {
      finder_cursor = 0;
      cursor_moved = 1;
    }
  } else if (keysym == XK_End) {
    if (finder_cursor != n) {
      finder_cursor = n;
      cursor_moved = 1;
    }
  } else if (keysym == XK_BackSpace) {
    if (finder_cursor > 0) {
      size_t prev = finder_cursor_prev(finder_query, finder_cursor);
      memmove(finder_query + prev, finder_query + finder_cursor,
              n - finder_cursor + 1);
      finder_cursor = prev;
      query_changed = 1;
    }
  } else if (keysym == XK_Delete) {
    if (finder_cursor < n) {
      size_t next = finder_cursor_next(finder_query, finder_cursor);
      memmove(finder_query + finder_cursor, finder_query + next,
              n - next + 1);
      query_changed = 1;
    }
  } else {
    len = XLookupString(ev, text, sizeof(text) - 1, NULL, NULL);
    if (len <= 0)
      return 1;
    text[len] = '\0';
    if (n + (size_t)len < sizeof(finder_query)) {
      memmove(finder_query + finder_cursor + len,
              finder_query + finder_cursor, n - finder_cursor + 1);
      memcpy(finder_query + finder_cursor, text, (size_t)len);
      finder_cursor += (size_t)len;
      query_changed = 1;
    }
  }
  if (query_changed) {
    finder_update_math();
    finder_rank();
    finder_selected = 0;
    finder_set_scroll(0);
  }
  if (query_changed || cursor_moved)
    finder_cursor_reset();
  finder_dirty = 1;
  if (cursor_moved) {
    resizebarwin(selmon);
    drawbars();
    return 1;
  }
  finder_icons_pending = 1;
  if (finder_selected < finder_scroll)
    finder_set_scroll(finder_selected);
  if (finder_selected >= finder_scroll + finder_rows)
    finder_set_scroll(finder_selected - finder_rows + 1);
  resizebarwin(selmon);
  drawbars();
  return 1;
}

static int finder_buttonpress(XButtonPressedEvent *ev) {
  int row;
  if (!finder_active)
    return finder_active;
  if (ev->button == Button4) {
    finder_set_scroll(finder_scroll - 1);
    finder_selected = MAX(finder_scroll, finder_selected - 1);
    finder_dirty = 1;
    finder_icons_pending = 1;
    resizebarwin(selmon);
    drawbars();
    return 1;
  }
  if (ev->button == Button5) {
    finder_set_scroll(finder_scroll + 1);
    finder_selected = MIN(finder_scroll + finder_rows - 1, finder_selected + 1);
    finder_dirty = 1;
    finder_icons_pending = 1;
    resizebarwin(selmon);
    drawbars();
    return 1;
  }
  if (ev->button != Button1)
    return 1;
  row = ev->y / MAX(1, bh);
  if (row > 0 && row < finder_display_rows()) {
    finder_selected = finder_scroll + row - 1;
    finder_launch();
  }
  return 1;
}

static char *notify_strdup(const char *s) {
  return s ? strdup(s) : strdup("");
}

static void notification_image_texture_free(Notification *n) {
  if (!n || !n->img_texture)
    return;
  if (notify_gl_ctx && notify_gl_pbuffer &&
      glXMakeCurrent(dpy, notify_gl_pbuffer, notify_gl_ctx))
    glDeleteTextures(1, &n->img_texture);
  n->img_texture = 0;
}

static void notification_image_texture_create(Notification *n) {
  unsigned int w, h;
  uint32_t *pixels;

  if (!n || n->img_texture || !n->img_pixels || !n->img_w || !n->img_h ||
      !n->image_w || !n->image_h)
    return;
  h = MIN(n->image_h, (unsigned int)NOTIFY_IMAGE_MAX_H);
  w = MAX(1U, (unsigned int)((uint64_t)n->image_w * h / n->image_h));
  if (w > 100) {
    w = 100;
    h = MAX(1U, (unsigned int)((uint64_t)n->image_h * w / n->image_w));
  }
  pixels = calloc((size_t)w * h, sizeof(*pixels));
  if (!pixels)
    return;

  /* Upload only display-sized pixels: notification source images may be
   * thousands of pixels wide, but are rendered at no more than 100x60. */
  for (unsigned int y = 0; y < h; y++)
    for (unsigned int x = 0; x < w; x++) {
      double sx = ((x + 0.5) * n->img_w / w) - 0.5;
      double sy = ((y + 0.5) * n->img_h / h) - 0.5;
      unsigned int x0, x1, y0, y1;
      double fx, fy;
      uint32_t p00, p10, p01, p11, out = 0;

      if (sx < 0) sx = 0;
      if (sy < 0) sy = 0;
      x0 = MIN((unsigned int)sx, n->img_w - 1);
      y0 = MIN((unsigned int)sy, n->img_h - 1);
      x1 = MIN(x0 + 1, n->img_w - 1);
      y1 = MIN(y0 + 1, n->img_h - 1);
      fx = sx - x0;
      fy = sy - y0;
      p00 = n->img_pixels[(size_t)y0 * n->img_w + x0];
      p10 = n->img_pixels[(size_t)y0 * n->img_w + x1];
      p01 = n->img_pixels[(size_t)y1 * n->img_w + x0];
      p11 = n->img_pixels[(size_t)y1 * n->img_w + x1];
      for (unsigned int shift = 0; shift < 32; shift += 8) {
        double top = ((p00 >> shift) & 0xff) * (1.0 - fx) +
                     ((p10 >> shift) & 0xff) * fx;
        double bottom = ((p01 >> shift) & 0xff) * (1.0 - fx) +
                        ((p11 >> shift) & 0xff) * fx;
        unsigned int channel = (unsigned int)lround(top * (1.0 - fy) +
                                                    bottom * fy);
        out |= channel << shift;
      }
      pixels[(size_t)y * w + x] = out;
    }

  glGenTextures(1, &n->img_texture);
  if (n->img_texture) {
    glBindTexture(GL_TEXTURE_2D, n->img_texture);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glPixelStorei(GL_UNPACK_ALIGNMENT, 4);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, w, h, 0, GL_BGRA,
                 GL_UNSIGNED_BYTE, pixels);
  }
  free(pixels);
}

static void notification_free(Notification *n) {
  unsigned int i;
  if (!n)
    return;
  notification_image_texture_free(n);
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
  free(n->img_pixels);
  if (n->image)
    XRenderFreePicture(dpy, n->image);
  free(n);
}

static void notification_free_contents(Notification *n) {
  unsigned int i;
  if (!n)
    return;
  n->body_wrap_valid = 0;
  n->body_wrap_count = 0;
  notification_image_texture_free(n);
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
  free(n->img_pixels);
  n->img_pixels = NULL;
  n->img_w = n->img_h = 0;
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

static void notification_update_wm_class(Window win, int active, int history,
                                         int finder) {
  XClassHint ch;

  if (!win)
    return;
  if (finder) {
    ch.res_name = "finder";
    ch.res_class = "finder";
    XSetClassHint(dpy, win, &ch);
  } else if (active) {
    ch.res_name = history ? "notification-history" : "notification";
    ch.res_class = "notify";
    XSetClassHint(dpy, win, &ch);
  } else {
    /* Restore the normal DWM class when the center returns to clock mode. */
    ch.res_name = "dwm";
    ch.res_class = "dwm";
    XSetClassHint(dpy, win, &ch);
  }
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
  Notification *old, *prev;

  if (!n)
    return;
  n->next = notify_history_head;
  notify_history_head = n;
  if (!notify_history_tail)
    notify_history_tail = n;
  notify_history_count++;
  while (notify_history_count > NOTIFY_HISTORY_MAX) {
    prev = NULL;
    old = notify_history_head;
    while (old && old->next) {
      prev = old;
      old = old->next;
    }
    if (!old)
      break;
    if (prev)
      prev->next = NULL;
    else
      notify_history_head = NULL;
    notify_history_tail = prev;
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

static void notification_round_pixels(uint32_t *pixels, unsigned int w,
                                      unsigned int h, unsigned int draw_w,
                                      unsigned int draw_h) {
  double radius, scale_x, scale_y;

  if (!pixels || !w || !h || !draw_w || !draw_h)
    return;
  radius = MIN(NOTIFY_IMAGE_RADIUS, MIN(draw_w, draw_h) / 2.0);
  if (radius <= 0)
    return;
  scale_x = (double)w / draw_w;
  scale_y = (double)h / draw_h;

  for (unsigned int y = 0; y < h; y++)
    for (unsigned int x = 0; x < w; x++) {
      double px = (x + 0.5) / scale_x;
      double py = (y + 0.5) / scale_y;
      double dx = px < radius ? radius - px
          : px > draw_w - radius ? px - (draw_w - radius) : 0;
      double dy = py < radius ? radius - py
          : py > draw_h - radius ? py - (draw_h - radius) : 0;
      double distance, coverage;
      uint32_t *pixel;
      unsigned int alpha;

      if (!dx || !dy)
        continue;
      distance = sqrt(dx * dx + dy * dy);
      coverage = fmax(0.0, fmin(1.0, radius + 0.5 - distance));
      pixel = &pixels[(size_t)y * w + x];
      alpha = *pixel >> 24;
      *pixel = (*pixel & 0x00ffffffU) |
               ((uint32_t)(alpha * coverage + 0.5) << 24);
    }
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
    notification_fit_size(w, h, NOTIFY_MAX_W - 40, NOTIFY_IMAGE_MAX_H,
                          &dw, &dh);
    n->image = notification_round_picture(
        drw_picture_create_resized(drw, (char *)data, w, h, dw, dh), dw, dh);
    n->image_w = dw;
    n->image_h = dh;

    n->img_pixels = ecalloc((size_t)w * h, sizeof(uint32_t));
    if (n->img_pixels) {
      memcpy(n->img_pixels, data, (size_t)w * h * sizeof(uint32_t));
      n->img_w = w;
      n->img_h = h;
      {
        unsigned int draw_w = dw, draw_h = dh;
        if (draw_w > 100) {
          draw_w = 100;
          draw_h = MAX(1U, (unsigned int)((uint64_t)dh * draw_w / dw));
        }
        notification_round_pixels(n->img_pixels, w, h, draw_w, draw_h);
      }
    }
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
      pixels[y * w + x] = (a << 24) | (p[0] << 16) | (p[1] << 8) | p[2];
    }
  {
    unsigned int dw, dh;
    notification_fit_size(w, h, NOTIFY_MAX_W - 40, NOTIFY_IMAGE_MAX_H,
                          &dw, &dh);
    n->image = notification_round_picture(
        drw_picture_create_resized(drw, (char *)pixels, w, h, dw, dh), dw,
        dh);
    n->image_w = dw;
    n->image_h = dh;

    n->img_pixels = ecalloc((size_t)w * h, sizeof(uint32_t));
    if (n->img_pixels) {
      memcpy(n->img_pixels, pixels, (size_t)w * h * sizeof(uint32_t));
      n->img_w = w;
      n->img_h = h;
      {
        unsigned int draw_w = dw, draw_h = dh;
        if (draw_w > 100) {
          draw_w = 100;
          draw_h = MAX(1U, (unsigned int)((uint64_t)dh * draw_w / dw));
        }
        notification_round_pixels(n->img_pixels, w, h, draw_w, draw_h);
      }
    }
  }
  n->image_hint = 1;
  free(pixels);
}

static unsigned int notification_text_width(const char *text) {
  const char *start, *end;
  char line[1024];
  unsigned int width = 0;

  if (!text || !*text)
    return 0;
  /* Do not resize the pbuffer when measuring during a popup draw.  The
   * current drawable may be the full-size notification surface. */
  if (!gl_font && !notification_gl_init(1, 1))
    return 0;
  if (!gl_font)
    gl_font = gl_font_create();
  if (!gl_font)
    return 0;
  start = text;
  while (*start) {
    size_t len;
    end = strchr(start, '\n');
    len = MIN(end ? (size_t)(end - start) : strlen(start), sizeof(line) - 1);
    memcpy(line, start, len);
    line[len] = '\0';
    width = MAX(width, gl_font_text_width(line));
    start += len;
    if (*start == '\n')
      start++;
    else if (!*start)
      break;
  }
  return width;
}

static unsigned int notification_body_wrap(Notification *n,
                                             unsigned int width,
                                             unsigned int max_lines) {
  const char *p;

  if (!n || !n->body || !*n->body)
    return 0;
  max_lines = MIN(max_lines, NOTIFY_BODY_MAX_LINES);
  if (!max_lines)
    return 0;
  if (n->body_wrap_valid && n->body_wrap_width == width &&
      n->body_wrap_max_lines == max_lines)
    return n->body_wrap_count;

  n->body_wrap_valid = 0;
  n->body_wrap_width = width;
  n->body_wrap_max_lines = max_lines;
  n->body_wrap_count = 0;
  p = n->body;
  while (*p && n->body_wrap_count < max_lines) {
    unsigned int lines = n->body_wrap_count;
    char *line = n->body_wrap_lines[lines];
    size_t used = 0, last_space = 0;
    const char *after_space = NULL;
    int explicit_break = 0;

    line[0] = '\0';
    while (*p && *p != '\n') {
      const char *next = p;
      uint32_t cp = notification_utf8_next(&next);
      size_t bytes = (size_t)(next - p);
      if (used + bytes >= NOTIFY_BODY_LINE_BYTES) {
        p = next;
        break;
      }
      memcpy(line + used, p, bytes);
      line[used + bytes] = '\0';
      if (notification_text_width(line) > width) {
        if (last_space) {
          used = last_space;
          p = after_space;
        } else if (used) {
          p = next == p ? p + 1 : p;
          break;
        } else {
          used += bytes;
          p = next;
        }
        break;
      }
      used += bytes;
      p = next;
      if (cp == ' ' || cp == '\t') {
        last_space = used;
        after_space = p;
      }
    }
    if (*p == '\n') {
      p++;
      explicit_break = 1;
    }
    while (used && (line[used - 1] == ' ' || line[used - 1] == '\t'))
      used--;
    line[used] = '\0';
    n->body_wrap_count++;
    if (!used && !explicit_break && *p)
      p++;
  }
  n->body_wrap_valid = 1;
  return n->body_wrap_count;
}

static unsigned int notification_text_block_height(int has_summary,
                                                    unsigned int body_lines) {
  unsigned int line_h, body_line_h, height;
  int ascender, descender;

  if (!has_summary && !body_lines)
    return 0;
  line_h = (unsigned int)MAX(gl_font ? gl_font->height : drw->fonts->h, 1);
  body_line_h = (unsigned int)MAX(
      (int)ceil(gl_font ? gl_font->pixel_size : drw->fonts->h) +
          NOTIFY_BODY_LINE_GAP,
      1);
  if (gl_font && gl_font->face_count) {
    FT_Size_Metrics metrics = gl_font->faces[0].face->size->metrics;
    ascender = MAX(1, (int)(metrics.ascender >> 6));
    descender = MAX(0, -(int)(metrics.descender >> 6));
  } else {
    ascender = MAX(1, (int)(line_h * 3 / 4));
    descender = MAX(0, (int)line_h - ascender);
  }

  height = (unsigned int)(ascender + descender);
  if (has_summary && body_lines)
    height += line_h + 2U;
  if (body_lines > 1)
    height += (body_lines - 1) * body_line_h;
  return height;
}

static int notification_action_row_y(Notification *n) {
  (void)n;
  return notify_action_y;
}

static unsigned int notification_history_content_height(Notification *n) {
  unsigned int height = 0;
  unsigned int body_width = NOTIFY_MAX_W - 2U * NOTIFY_PADDING;
  unsigned int body_lines = 0, img_w = 0, img_h = 0;
  int has_summary, has_body;

  if (!n)
    return (unsigned int)bh;
  has_summary = n->summary && *n->summary;
  has_body = n->body && *n->body;
  if (n->image && n->image_w && n->image_h) {
    img_h = MIN(n->image_h, (unsigned int)NOTIFY_IMAGE_MAX_H);
    img_w = (unsigned int)((uint64_t)n->image_w * img_h / n->image_h);
    if (img_w > 100) {
      img_w = 100;
      img_h = MAX(1U, (unsigned int)((uint64_t)n->image_h * img_w /
                                     n->image_w));
    }
    body_width = body_width > img_w + 12 ? body_width - img_w - 12 : 1;
  }
  if (has_body) {
    body_lines = notification_body_wrap(n, body_width,
                                        NOTIFY_HISTORY_BODY_MAX_LINES);
  }
  height = notification_text_block_height(has_summary, body_lines);
  return MAX((unsigned int)bh, MAX(height, img_h));
}

static unsigned int notification_history_entry_content_height(Notification *n) {
  unsigned int height;

  if (!n)
    return NOTIFY_HISTORY_ENTRY_H;
  height = notification_history_content_height(n);
  if (n->input_enabled)
    height += NOTIFY_INPUT_ROW_H;
  if (n->action_count >= 4)
    height += NOTIFY_BUTTON_H;
  return height;
}

static unsigned int notification_history_entry_height(Notification *n) {
  unsigned int height = notification_history_entry_content_height(n);

  if (n && n->next)
    height += NOTIFY_PADDING;
  return height;
}

static void notification_history_layout(void) {
  Notification *n;
  unsigned int content_h, viewport_h;
  int max_scroll;

  if (!gl_font && notification_gl_init(1, 1))
    gl_font = gl_font_create();
  notify_width = NOTIFY_MAX_W;
  content_h = 0;
  for (n = notify_history_head; n; n = n->next)
    content_h += notification_history_entry_height(n);
  notify_height = MIN(MAX(content_h + 2U * NOTIFY_PADDING, (unsigned int)bh),
                      (unsigned int)NOTIFY_HISTORY_MAX_H);
  viewport_h = notify_height > 2U * NOTIFY_PADDING
                   ? notify_height - 2U * NOTIFY_PADDING : 0;
  max_scroll = content_h > viewport_h ? (int)(content_h - viewport_h) : 0;
  notify_history_scroll = MAX(0, MIN(notify_history_scroll, max_scroll));
  notify_history_scroll_target = MAX(0, MIN(notify_history_scroll_target,
                                             max_scroll));
  if (!max_scroll)
    notify_history_scroll = 0;
  if (!max_scroll)
    notify_history_scroll_target = 0;
}

static void notification_history_show(void) {
  if (!notify_history_count || notify_active || finder_active)
    return;
  notify_history_active = 1;
  notify_history_input = NULL;
  notify_input_focus = 0;
  notify_history_hover_entry = NULL;
  notify_history_hover_action = -1;
  notify_history_scroll = 0;
  notify_history_scroll_target = 0;
    notify_history_scroll_started.tv_sec = 0;
    notify_history_scroll_started.tv_nsec = 0;
  notification_history_layout();
  drawbars();
  resizebarwin(selmon);
}

static void notification_history_hide(void) {
  if (!notify_history_active)
    return;
  notify_history_active = 0;
  if (notify_input_focus)
    XSetInputFocus(dpy, root, RevertToParent, CurrentTime);
  notify_input_focus = 0;
  notify_history_input = NULL;
  notify_history_hover_entry = NULL;
  notify_history_hover_action = -1;
  notification_history_layout();
  drawbars();
  resizebarwin(selmon);
}

static void notification_update_layout(Notification *n) {
  unsigned int text_w, body_w, content_w, img_w = 0, img_h = 0;
  unsigned int content_h, text_content_h, body_lines = 0;
  int image_y;
  unsigned int actions = 0, visible_actions = 0;
  unsigned int action_w = 0, action_label_w[16] = {0};
  unsigned int control_top;
  const unsigned int pad = NOTIFY_PADDING;

  if (!n)
    return;

  /* Keep image and text alignment based on the baselines actually rendered. */
  if (!gl_font && notification_gl_init(1, 1))
    gl_font = gl_font_create();

  /* The optional image stays at its natural aspect ratio and at most 70px
   * high.  Its width is capped so it cannot consume the whole text column. */
  if (n->image && n->image_w > 0 && n->image_h > 0) {
    img_h = MIN(n->image_h, (unsigned int)NOTIFY_IMAGE_MAX_H);
    img_w = (unsigned int)((double)n->image_w * img_h / n->image_h);
    if (img_w > 100) {
      img_w = 100;
      img_h = MAX(1U, (unsigned int)((double)n->image_h * img_w / n->image_w));
    }
  }

  text_w = MAX(notification_text_width(n->summary),
               notification_text_width(n->body));
  if (n->input_enabled) {
    text_w = MAX(text_w, notification_text_width(n->input_placeholder));
    text_w = MAX(text_w, notification_text_width(n->input_text));
  }
  actions = n->actions
      ? MIN(n->action_count / 2, LENGTH(notify_action_x)) : 0;
  visible_actions = notify_hovered ? actions : 0;
  for (unsigned int i = 0; i < visible_actions; i++) {
    action_label_w[i] = notification_text_width(n->actions[i * 2 + 1]);
    action_w += action_label_w[i];
  }
  if (visible_actions > 1)
    action_w += (visible_actions - 1) * 16;
  text_w = MAX(text_w, action_w);
  if (img_w)
    text_w += img_w + 12;
  content_w = MIN(NOTIFY_MAX_W - 2U * pad, text_w);
  notify_width = MAX(100U, content_w + 2U * pad);

  content_w = notify_width - 2U * pad;
  body_w = MAX(1U, content_w - (img_w ? img_w + 12 : 0));
  if (n->body && *n->body)
    body_lines = notification_body_wrap(n, body_w,
        notify_hovered ? NOTIFY_POPUP_BODY_HOVER_MAX_LINES
                       : NOTIFY_POPUP_BODY_MAX_LINES);
  text_content_h = notification_text_block_height(
      n->summary && *n->summary, body_lines);
  content_h = MAX(text_content_h, img_h);
  notify_text_y = (int)(content_h - text_content_h) / 2;
  image_y = (int)(content_h - img_h) / 2;
  notify_image_y = image_y;

  memset(notify_action_x, 0, sizeof(notify_action_x));
  memset(notify_action_w, 0, sizeof(notify_action_w));
  notify_input_x = (int)pad;
  notify_input_w = (int)content_w;
  notify_input_h = n->input_enabled ? NOTIFY_INPUT_ROW_H : 0;
  control_top = content_h;
  notify_input_y = n->input_enabled ? (int)(pad + control_top) : 0;
  notify_action_y = visible_actions ? (int)(pad + control_top +
      (n->input_enabled ? NOTIFY_INPUT_ROW_H : 0)) : 0;
  if (visible_actions) {
    unsigned int used = 0, weight = MAX(action_w, visible_actions);
    for (unsigned int i = 0; i < visible_actions; i++) {
      unsigned int cell_weight = action_label_w[i] +
          (i + 1 < visible_actions ? 16U : 0U);
      unsigned int cell_w = i + 1 == visible_actions
          ? content_w - used
          : MAX(1U, (unsigned int)(((uint64_t)content_w *
                                    MAX(cell_weight, 1U)) / weight));
      cell_w = MIN(cell_w, content_w - used);
      notify_action_x[i] = (int)(pad + used);
      notify_action_w[i] = (int)cell_w;
      used += cell_w;
    }
  }
  notify_height = MAX(50U, control_top +
      (n->input_enabled ? NOTIFY_INPUT_ROW_H : 0) +
      (visible_actions ? NOTIFY_BUTTON_H : 0) + 2U * pad);
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
      p->img_pixels = n->img_pixels;
      p->img_w = n->img_w;
      p->img_h = n->img_h;
      n->img_pixels = NULL;
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
      p->img_pixels = n->img_pixels;
      p->img_w = n->img_w;
      p->img_h = n->img_h;
      n->img_pixels = NULL;
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
      p->img_pixels = n->img_pixels;
      p->img_w = n->img_w;
      p->img_h = n->img_h;
      n->img_pixels = NULL;
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

/* Initialize FreeType and select the font already configured for the bar. */
static int gl_font_init_ft(void) {
  if (ft_lib)
    return 1;
  if (FT_Init_FreeType(&ft_lib)) {
    fprintf(stderr, "AnDWM: cannot initialize FreeType for notifications\n");
    return 0;
  }
  return 1;
}

static int notification_gl_init(unsigned int w, unsigned int h) {
  int attrs[] = { GLX_X_RENDERABLE, True,
                  GLX_DRAWABLE_TYPE, GLX_PBUFFER_BIT,
                  GLX_RENDER_TYPE, GLX_RGBA_BIT,
                  GLX_RED_SIZE, 8, GLX_GREEN_SIZE, 8,
                  GLX_BLUE_SIZE, 8, GLX_ALPHA_SIZE, 8, None };
  int pbuf_attrs[5];
  int nconfigs = 0;
  GLXFBConfig *configs;

  w = MAX(w, 1U);
  h = MAX(h, 1U);
  if (!notify_gl_initialized) {
    configs = glXChooseFBConfig(dpy, screen, attrs, &nconfigs);
    if (!configs || nconfigs == 0) {
      if (configs) XFree(configs);
      fprintf(stderr, "AnDWM: GLX has no RGBA pbuffer configuration for notifications\n");
      return 0;
    }
    notify_gl_fbconfig = configs[0];
    notify_gl_ctx = glXCreateNewContext(dpy, notify_gl_fbconfig, GLX_RGBA_TYPE,
                                        NULL, True);
    XFree(configs);
    if (!notify_gl_ctx) {
      fprintf(stderr, "AnDWM: cannot create notification GLX context\n");
      return 0;
    }
    notify_gl_initialized = 1;
  }
  if (!notify_gl_pbuffer || notify_gl_pbuffer_w != w ||
      notify_gl_pbuffer_h != h) {
    if (notify_gl_pbuffer) {
      glXMakeCurrent(dpy, None, NULL);
      glXDestroyPbuffer(dpy, notify_gl_pbuffer);
    }
    pbuf_attrs[0] = GLX_PBUFFER_WIDTH;
    pbuf_attrs[1] = (int)w;
    pbuf_attrs[2] = GLX_PBUFFER_HEIGHT;
    pbuf_attrs[3] = (int)h;
    pbuf_attrs[4] = None;
    notify_gl_pbuffer = glXCreatePbuffer(dpy, notify_gl_fbconfig, pbuf_attrs);
    if (!notify_gl_pbuffer) {
      notify_gl_pbuffer_w = notify_gl_pbuffer_h = 0;
      fprintf(stderr, "AnDWM: cannot create notification GLX pbuffer\n");
      return 0;
    }
    notify_gl_pbuffer_w = w;
    notify_gl_pbuffer_h = h;
  }
  if (!glXMakeCurrent(dpy, notify_gl_pbuffer, notify_gl_ctx)) {
    fprintf(stderr, "AnDWM: cannot bind notification GLX pbuffer\n");
    return 0;
  }
  if (!notify_gl_blend_func_separate)
    notify_gl_blend_func_separate = (NotificationGLBlendFuncSeparate)
        glXGetProcAddressARB((const GLubyte *)"glBlendFuncSeparate");
  return 1;
}

static void notification_gl_blend_separate(void) {
  if (notify_gl_blend_func_separate)
    notify_gl_blend_func_separate(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA,
                                  GL_ONE, GL_ONE_MINUS_SRC_ALPHA);
  else
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
}

static GLFont *gl_font_create(void) {
  GLFont *font;
  Fnt *f;
  double pixel_size = drw && drw->fonts ? drw->fonts->h : 14;

  if (!gl_font_init_ft())
    return NULL;
  font = calloc(1, sizeof(*font));
  if (!font)
    return NULL;
  font->pixel_size = pixel_size;

  /* Mirror config.h's fontset for GL text. Xft's resolved pattern provides
   * the actual font file, face index, and configured size for each entry. */
  for (f = drw ? drw->fonts : NULL; f; f = f->next) {
    FcChar8 *file = NULL;
    double face_pixel_size = pixel_size;
    int index = 0;

    if (!f->xfont || !f->xfont->pattern ||
        FcPatternGetString(f->xfont->pattern, FC_FILE, 0, &file) !=
            FcResultMatch)
      continue;
    FcPatternGetDouble(f->xfont->pattern, FC_PIXEL_SIZE, 0,
                       &face_pixel_size);
    FcPatternGetInteger(f->xfont->pattern, FC_INDEX, 0, &index);
    if (!font->face_count)
      font->pixel_size = face_pixel_size;
    gl_font_add_face(font, (const char *)file, index, face_pixel_size);
  }

  /* Keep a local system-font fallback for unusual setups where none of the
   * configured Xft fonts expose a file that FreeType can open. */
  if (!font->face_count) {
    static const char *fallbacks[] = {
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/TTF/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
        NULL};
    for (int i = 0; fallbacks[i]; i++) {
      if (gl_font_add_face(font, fallbacks[i], 0, font->pixel_size) >= 0)
        goto face_loaded;
    }
    fprintf(stderr, "AnDWM: cannot find a FreeType font for notifications\n");
    free(font);
    return NULL;
  }
face_loaded:
  font->height = drw && drw->fonts ? (int)drw->fonts->h
      : (int)(font->faces[0].face->size->metrics.height >> 6);
  if (font->height <= 0)
    font->height = (int)ceil(pixel_size);
  return font;
}

static int gl_font_add_face(GLFont *font, const char *file, int index,
                            double pixel_size) {
  GLFontFace *font_face;
  if (!font || !file)
    return -1;
  if (pixel_size <= 0)
    pixel_size = font->pixel_size > 0 ? font->pixel_size : 14;
  for (unsigned int i = 0; i < font->face_count; i++)
    if (font->faces[i].index == index &&
        font->faces[i].pixel_size == pixel_size &&
        !strcmp(font->faces[i].file, file))
      return (int)i;
  if (font->face_count >= LENGTH(font->faces))
    return -1;
  font_face = &font->faces[font->face_count];
  memset(font_face, 0, sizeof(*font_face));
  font_face->file = strdup(file);
  font_face->index = index;
  font_face->pixel_size = pixel_size;
  if (!font_face->file ||
      FT_New_Face(ft_lib, file, index, &font_face->face) ||
      FT_Set_Char_Size(font_face->face, 0,
                       (FT_F26Dot6)lround(pixel_size * 64.0), 72, 72)) {
    if (font_face->face)
      FT_Done_Face(font_face->face);
    free(font_face->file);
    memset(font_face, 0, sizeof(*font_face));
    return -1;
  }
  font_face->hb_font = hb_ft_font_create_referenced(font_face->face);
  if (!font_face->hb_font) {
    FT_Done_Face(font_face->face);
    free(font_face->file);
    memset(font_face, 0, sizeof(*font_face));
    return -1;
  }
  font->face_count++;
  return (int)(font->face_count - 1);
}

static uint32_t notification_utf8_next(const char **text) {
  const unsigned char *s = (const unsigned char *)*text;
  uint32_t c;
  if (s[0] < 0x80) {
    *text += 1;
    return s[0];
  }
  if (s[0] >= 0xc2 && s[0] <= 0xdf &&
      (s[1] & 0xc0) == 0x80) {
    c = ((uint32_t)(s[0] & 0x1f) << 6) | (s[1] & 0x3f);
    *text += 2;
    return c;
  }
  if (s[0] >= 0xe0 && s[0] <= 0xef &&
      (s[1] & 0xc0) == 0x80 && (s[2] & 0xc0) == 0x80 &&
      !(s[0] == 0xe0 && s[1] < 0xa0) &&
      !(s[0] == 0xed && s[1] >= 0xa0)) {
    c = ((uint32_t)(s[0] & 0x0f) << 12) |
        ((uint32_t)(s[1] & 0x3f) << 6) | (s[2] & 0x3f);
    *text += 3;
    return c;
  }
  if (s[0] >= 0xf0 && s[0] <= 0xf4 &&
      (s[1] & 0xc0) == 0x80 && (s[2] & 0xc0) == 0x80 &&
      (s[3] & 0xc0) == 0x80 &&
      !(s[0] == 0xf0 && s[1] < 0x90) &&
      !(s[0] == 0xf4 && s[1] > 0x8f)) {
    c = ((uint32_t)(s[0] & 7) << 18) | ((uint32_t)(s[1] & 0x3f) << 12) |
        ((uint32_t)(s[2] & 0x3f) << 6) | (s[3] & 0x3f);
    *text += 4;
    return c;
  }
  *text += 1;
  return 0xfffd;
}

static int gl_font_face_for_codepoint(GLFont *font, uint32_t codepoint) {
  FcPattern *pattern = NULL, *match = NULL;
  FcCharSet *charset = NULL;
  FcChar8 *file = NULL;
  FcResult match_result;
  int index = 0, face_index = -1;

  if (!font || !codepoint)
    return 0;
  for (unsigned int i = 0; i < font->face_count; i++)
    if (FT_Get_Char_Index(font->faces[i].face, codepoint))
      return (int)i;

  pattern = FcPatternCreate();
  charset = FcCharSetCreate();
  if (pattern && charset && FcCharSetAddChar(charset, codepoint) &&
      FcPatternAddCharSet(pattern, FC_CHARSET, charset)) {
    FcConfigSubstitute(NULL, pattern, FcMatchPattern);
    FcDefaultSubstitute(pattern);
    match = FcFontMatch(NULL, pattern, &match_result);
  }
  if (match && FcPatternGetString(match, FC_FILE, 0, &file) == FcResultMatch) {
    FcPatternGetInteger(match, FC_INDEX, 0, &index);
    face_index = gl_font_add_face(font, (const char *)file, index,
                                  font->pixel_size);
    if (face_index >= 0 &&
        !FT_Get_Char_Index(font->faces[face_index].face, codepoint))
      face_index = -1;
  }
  if (match)
    FcPatternDestroy(match);
  if (pattern)
    FcPatternDestroy(pattern);
  if (charset)
    FcCharSetDestroy(charset);
  return face_index >= 0 ? face_index : 0;
}

static GLGlyph *gl_font_glyph(GLFont *font, unsigned int face_index,
                              unsigned int glyph_index) {
  GLGlyph *g = NULL;
  FT_Face face;
  FT_GlyphSlot slot;
  unsigned char *bitmap;
  int pitch, x, y;

  if (!font || face_index >= font->face_count)
    return NULL;
  for (unsigned int i = 0; i < font->glyph_count; i++)
    if (font->glyphs[i].face_index == face_index &&
        font->glyphs[i].glyph_index == glyph_index)
      return &font->glyphs[i];
  if (font->glyph_count >= LENGTH(font->glyphs))
    return NULL;

  face = font->faces[face_index].face;
  if (FT_Load_Glyph(face, glyph_index, FT_LOAD_RENDER))
    return NULL;
  slot = face->glyph;
  g = &font->glyphs[font->glyph_count++];
  memset(g, 0, sizeof(*g));
  g->face_index = face_index;
  g->glyph_index = glyph_index;
  g->w = slot->bitmap.width;
  g->h = slot->bitmap.rows;
  g->bearing_x = slot->bitmap_left;
  g->bearing_y = slot->bitmap_top;
  g->advance = slot->advance.x >> 6;
  g->loaded = 1;
  if (!g->w || !g->h)
    return g;

  bitmap = calloc((size_t)g->w * g->h, 1);
  if (!bitmap)
    return g;
  pitch = slot->bitmap.pitch;
  for (y = 0; y < g->h; y++) {
    const unsigned char *row = pitch >= 0
        ? slot->bitmap.buffer + y * pitch
        : slot->bitmap.buffer + (g->h - 1 - y) * -pitch;
    for (x = 0; x < g->w; x++) {
      if (slot->bitmap.pixel_mode == FT_PIXEL_MODE_MONO)
        bitmap[y * g->w + x] = (row[x >> 3] & (0x80 >> (x & 7))) ? 255 : 0;
      else
        bitmap[y * g->w + x] = row[x];
    }
  }
  glGenTextures(1, &g->tex_id);
  glBindTexture(GL_TEXTURE_2D, g->tex_id);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
  glTexImage2D(GL_TEXTURE_2D, 0, GL_ALPHA, g->w, g->h, 0, GL_ALPHA,
               GL_UNSIGNED_BYTE, bitmap);
  free(bitmap);
  return g;
}

static unsigned int gl_font_text_width(const char *text) {
  int64_t width = 0;
  const char *run_start, *p;
  if (!text || !gl_font)
    return 0;
  p = text;
  while (*p) {
    const char *next = p;
    unsigned int face_index;
    hb_buffer_t *buffer;
    hb_glyph_position_t *positions;
    unsigned int count;

    face_index = (unsigned int)gl_font_face_for_codepoint(
        gl_font, notification_utf8_next(&next));
    run_start = p;
    p = next;
    while (*p) {
      next = p;
      if ((unsigned int)gl_font_face_for_codepoint(
              gl_font, notification_utf8_next(&next)) != face_index)
        break;
      p = next;
    }
    buffer = hb_buffer_create();
    if (!buffer)
      continue;
    hb_buffer_add_utf8(buffer, run_start, (int)(p - run_start), 0,
                       (int)(p - run_start));
    hb_buffer_guess_segment_properties(buffer);
    hb_shape(gl_font->faces[face_index].hb_font, buffer, NULL, 0);
    positions = hb_buffer_get_glyph_positions(buffer, &count);
    for (unsigned int i = 0; i < count; i++)
      width += MAX(positions[i].x_advance, 0);
    hb_buffer_destroy(buffer);
  }
  return (unsigned int)MAX((width + 63) / 64, 0);
}

static void gl_font_draw_text(const char *text, int x, int baseline,
                              unsigned int max_width, float r, float g,
                              float b) {
  int64_t pen_x = (int64_t)x * 64;
  const char *p = text;
  if (!text || !gl_font)
    return;
  glEnable(GL_TEXTURE_2D);
  glEnable(GL_BLEND);
  notification_gl_blend_separate();
  glColor4f(r, g, b, 1.0f);
  glTexEnvf(GL_TEXTURE_ENV, GL_TEXTURE_ENV_MODE, GL_MODULATE);
  while (*p) {
    const char *run_start = p, *next = p;
    unsigned int face_index = (unsigned int)gl_font_face_for_codepoint(
        gl_font, notification_utf8_next(&next));
    hb_buffer_t *buffer;
    hb_glyph_info_t *infos;
    hb_glyph_position_t *positions;
    unsigned int count;
    int64_t run_x = pen_x;

    p = next;
    while (*p) {
      next = p;
      if ((unsigned int)gl_font_face_for_codepoint(
              gl_font, notification_utf8_next(&next)) != face_index)
        break;
      p = next;
    }
    buffer = hb_buffer_create();
    if (!buffer)
      continue;
    hb_buffer_add_utf8(buffer, run_start, (int)(p - run_start), 0,
                       (int)(p - run_start));
    hb_buffer_guess_segment_properties(buffer);
    hb_shape(gl_font->faces[face_index].hb_font, buffer, NULL, 0);
    infos = hb_buffer_get_glyph_infos(buffer, &count);
    positions = hb_buffer_get_glyph_positions(buffer, &count);
    for (unsigned int i = 0; i < count; i++) {
      GLGlyph *glyph = gl_font_glyph(gl_font, face_index, infos[i].codepoint);
      float pen = (float)(run_x + positions[i].x_offset) / 64.0f;
      float x1, y1, x2, y2;
      if ((uint64_t)MAX(run_x + positions[i].x_advance -
                            (int64_t)x * 64, 0) >
          (uint64_t)max_width * 64) {
        hb_buffer_destroy(buffer);
        glDisable(GL_BLEND);
        glDisable(GL_TEXTURE_2D);
        return;
      }
      if (glyph && glyph->tex_id && glyph->w > 0 && glyph->h > 0) {
        x1 = pen + glyph->bearing_x;
        y1 = baseline - glyph->bearing_y -
             (float)positions[i].y_offset / 64.0f;
        x2 = x1 + glyph->w;
        y2 = y1 + glyph->h;
        glBindTexture(GL_TEXTURE_2D, glyph->tex_id);
        glBegin(GL_QUADS);
        glTexCoord2f(0, 0); glVertex2f(x1, y1);
        glTexCoord2f(1, 0); glVertex2f(x2, y1);
        glTexCoord2f(1, 1); glVertex2f(x2, y2);
        glTexCoord2f(0, 1); glVertex2f(x1, y2);
        glEnd();
      }
      run_x += positions[i].x_advance;
    }
    pen_x = run_x;
    hb_buffer_destroy(buffer);
    if ((uint64_t)MAX(pen_x - (int64_t)x * 64, 0) >
        (uint64_t)max_width * 64)
      break;
  }
  glDisable(GL_BLEND);
  glDisable(GL_TEXTURE_2D);
}

static void gl_font_free(GLFont *font) {
  if (!font)
    return;
  for (unsigned int i = 0; i < font->glyph_count; i++)
    if (font->glyphs[i].tex_id)
      glDeleteTextures(1, &font->glyphs[i].tex_id);
  for (unsigned int i = 0; i < font->face_count; i++) {
    if (font->faces[i].hb_font)
      hb_font_destroy(font->faces[i].hb_font);
    if (font->faces[i].face)
      FT_Done_Face(font->faces[i].face);
    free(font->faces[i].file);
  }
  free(font);
}

static void notification_gl_draw_body(Notification *n, int x, int *baseline,
                                      int line_h, unsigned int width,
                                      unsigned int max_lines,
                                      float r, float g, float b) {
  unsigned int lines = notification_body_wrap(n, width, max_lines);

  for (unsigned int i = 0; i < lines; i++) {
    gl_font_draw_text(n->body_wrap_lines[i], x, *baseline, width, r, g, b);
    *baseline += line_h;
  }
}

static unsigned long notification_channel_pixel(unsigned long mask,
                                                unsigned char value) {
  unsigned int shift = 0;
  unsigned long max;
  if (!mask)
    return 0;
  while (!(mask & 1)) {
    mask >>= 1;
    shift++;
  }
  max = mask;
  return ((((unsigned long)value * max + 127) / 255) << shift);
}

static unsigned char notification_vertical_alpha(unsigned int y,
                                                 unsigned int h) {
  static const double stops[] = {0.0, 0.0, 0.1, 0.2, 0.3, 0.4,
                                 0.5, 0.6, 0.7, 0.8, 0.9, 1.0};
  /* Finder's accelerating curve, remapped from 100% at the top to 50% at
   * the bottom while retaining the same transition profile. */
  static const unsigned char alpha[] = {
      255, 255, 254, 251, 246, 238, 228, 215, 200, 182, 162, 128};
  double position = h > 1 ? (double)y / (double)(h - 1) : 0.0;

  for (unsigned int i = 1; i < LENGTH(stops); i++) {
    if (position <= stops[i]) {
      double span = stops[i] - stops[i - 1];
      double fraction = span > 0.0 ? (position - stops[i - 1]) / span : 0.0;
      return (unsigned char)lround(alpha[i - 1] +
                                   (alpha[i] - alpha[i - 1]) * fraction);
    }
  }
  return alpha[LENGTH(alpha) - 1];
}

static void notification_present_gl(unsigned int w, unsigned int h,
                                   Drawable target) {
  unsigned char *pixels;
  Visual *visual;
  int depth;
  XImage *image;
  GC gc;
  Pixmap pixmap;
  Picture src = None, dest = None;
  XRenderPictFormat *format, *visual_format;
  unsigned long alpha_mask = 0;

  /* History frames, including their per-pixel alpha, are uploaded directly
   * into the reusable content pixmap. Scrolling then uses XCopyArea. */
  if (target != None || (notify_history_active && selmon &&
                         selmon->barcenterwin)) {
    uint16_t endian_test = 1;
    int native_byte_order = *(unsigned char *)&endian_test
                                ? LSBFirst : MSBFirst;
    unsigned char *row = NULL;
    Drawable dest = target != None ? target : selmon->barcenterwin;

    visual = finder_argb_visual ? finder_argb_visual
                                : DefaultVisual(dpy, screen);
    depth = finder_argb_visual ? finder_argb_depth
                               : DefaultDepth(dpy, screen);
    visual_format = XRenderFindVisualFormat(dpy, visual);
    if (visual_format && visual_format->type == PictTypeDirect)
      alpha_mask = (unsigned long)visual_format->direct.alphaMask
                   << visual_format->direct.alpha;
    image = XCreateImage(dpy, visual, (unsigned int)depth, ZPixmap, 0, NULL,
                         w, h, 32, 0);
    if (image && image->bits_per_pixel == 32 &&
        image->byte_order == native_byte_order &&
        image->bytes_per_line == (int)(w * 4U) &&
        visual->red_mask == 0x00ff0000UL &&
        visual->green_mask == 0x0000ff00UL &&
        visual->blue_mask == 0x000000ffUL &&
        (!alpha_mask || alpha_mask == 0xff000000UL)) {
      image->data = calloc((size_t)image->bytes_per_line, h);
      row = malloc((size_t)image->bytes_per_line);
      if (image->data && row) {
        glPixelStorei(GL_PACK_ALIGNMENT, 4);
        glReadPixels(0, 0, (GLsizei)w, (GLsizei)h, GL_BGRA,
                     GL_UNSIGNED_BYTE, image->data);
        /* Preserve transparent history foreground pixels so text and images
         * can be composited above the separately-gradient-masked background.
         * Popups use the gradient directly as one complete surface. */
        for (unsigned int y = 0; y < h; y++) {
          unsigned char opacity = target != None
              ? 0 : notification_vertical_alpha(h - 1U - y, h);
          for (unsigned int x = 0; x < w; x++) {
            unsigned char *pixel = (unsigned char *)image->data +
                (size_t)y * image->bytes_per_line + (size_t)x * 4U;
            if (target == None)
              pixel[3] = opacity;
          }
        }
        for (unsigned int y = 0; y < h / 2; y++) {
          unsigned char *top = (unsigned char *)image->data +
                               (size_t)y * image->bytes_per_line;
          unsigned char *bottom = (unsigned char *)image->data +
                                  (size_t)(h - 1 - y) * image->bytes_per_line;
          memcpy(row, top, (size_t)image->bytes_per_line);
          memcpy(top, bottom, (size_t)image->bytes_per_line);
          memcpy(bottom, row, (size_t)image->bytes_per_line);
        }
        gc = XCreateGC(dpy, dest, 0, NULL);
        if (gc) {
          XPutImage(dpy, dest, gc, image, 0, 0, 0, 0, w, h);
          XFreeGC(dpy, gc);
          free(row);
          XDestroyImage(image);
          return;
        }
      }
      free(row);
    }
    if (image)
      XDestroyImage(image);
  }

  pixels = calloc((size_t)w * h, 4);
  if (!pixels)
    return;
  glPixelStorei(GL_PACK_ALIGNMENT, 1);
  glReadPixels(0, 0, (GLsizei)w, (GLsizei)h, GL_RGBA, GL_UNSIGNED_BYTE, pixels);
  visual = finder_argb_visual ? finder_argb_visual : DefaultVisual(dpy, screen);
  depth = finder_argb_visual ? finder_argb_depth : DefaultDepth(dpy, screen);
  visual_format = XRenderFindVisualFormat(dpy, visual);
  if (visual_format && visual_format->type == PictTypeDirect)
    alpha_mask = (unsigned long)visual_format->direct.alphaMask
                 << visual_format->direct.alpha;
  image = XCreateImage(dpy, visual, (unsigned int)depth, ZPixmap, 0, NULL,
                       w, h, 32, 0);
  if (!image) {
    free(pixels);
    return;
  }
  image->data = calloc((size_t)image->bytes_per_line, h);
  if (!image->data) {
    image->f.destroy_image(image);
    free(pixels);
    return;
  }
  for (unsigned int py = 0; py < h; py++)
    for (unsigned int px = 0; px < w; px++) {
      size_t src_offset = ((size_t)(h - 1 - py) * w + px) * 4;
      unsigned char r = pixels[src_offset];
      unsigned char g = pixels[src_offset + 1];
      unsigned char b = pixels[src_offset + 2];
      /* Both popup and history pixels remain transparent foreground. The
       * viewport's fixed background gradient is composited separately. */
      unsigned char a = pixels[src_offset + 3];
      unsigned long pixel = notification_channel_pixel(visual->red_mask, r) |
                            notification_channel_pixel(visual->green_mask, g) |
                            notification_channel_pixel(visual->blue_mask, b) |
                            notification_channel_pixel(alpha_mask, a);
      XPutPixel(image, (int)px, (int)py, pixel);
    }
  free(pixels);

  /* The history cache is a pixmap with the same depth as the bar window.
   * Use the generic XImage conversion when the fast BGRA layout above is
   * unavailable, rather than leaving the cache uninitialized. */
  if (target != None) {
    gc = XCreateGC(dpy, target, 0, NULL);
    if (gc) {
      XPutImage(dpy, target, gc, image, 0, 0, 0, 0, w, h);
      XFreeGC(dpy, gc);
    }
    XDestroyImage(image);
    return;
  }

  pixmap = XCreatePixmap(dpy, root, w, h, (unsigned int)depth);
  if (!pixmap) {
    XDestroyImage(image);
    return;
  }
  gc = XCreateGC(dpy, pixmap, 0, NULL);
  if (!gc) {
    XFreePixmap(dpy, pixmap);
    XDestroyImage(image);
    return;
  }
  XPutImage(dpy, pixmap, gc, image, 0, 0, 0, 0, w, h);
  format = XRenderFindStandardFormat(dpy, depth == 32 ? PictStandardARGB32
                                                       : PictStandardRGB24);
  if (format)
    src = XRenderCreatePicture(dpy, pixmap, format, 0, NULL);
  if (finder_argb_visual)
    format = XRenderFindVisualFormat(dpy, finder_argb_visual);
  else
    format = XRenderFindVisualFormat(dpy, visual);
  if (format)
    dest = XRenderCreatePicture(dpy, selmon->barcenterwin, format, 0, NULL);
  if (src && dest && notification_history_background_create() &&
      notification_history_mask_create(w, h)) {
    XRenderColor transparent = {0, 0, 0, 0};
    XRenderFillRectangle(dpy, PictOpSrc, dest, &transparent, 0, 0, w, h);
    XRenderComposite(dpy, PictOpOver, notify_history_background_picture,
                     notify_history_mask_picture, dest,
                     0, 0, 0, 0, 0, 0, w, h);
    XRenderComposite(dpy, PictOpOver, src, None, dest,
                     0, 0, 0, 0, 0, 0, w, h);
  } else if (src && dest) {
    XRenderComposite(dpy, PictOpSrc, src, None, dest,
                     0, 0, 0, 0, 0, 0, w, h);
  }
  if (src) XRenderFreePicture(dpy, src);
  if (dest) XRenderFreePicture(dpy, dest);
  XFreeGC(dpy, gc);
  XFreePixmap(dpy, pixmap);
  XDestroyImage(image);
}

/* Render the complete popup, including its image and text, on a dedicated
 * GLX pbuffer.  It is then copied as one full-height image, never from dwm's
 * bar-sized scratch drawable. */
static uint64_t notification_hash_bytes(uint64_t hash, const void *data,
                                       size_t len) {
  const unsigned char *bytes = data;
  for (size_t i = 0; i < len; i++) {
    hash ^= bytes[i];
    hash *= UINT64_C(1099511628211);
  }
  return hash;
}

static uint64_t notification_hash_string(uint64_t hash, const char *text) {
  static const unsigned char null_marker = 0xff;
  if (!text)
    return notification_hash_bytes(hash, &null_marker, sizeof(null_marker));
  hash = notification_hash_bytes(hash, text, strlen(text));
  return notification_hash_bytes(hash, "\0", 1);
}

static uint64_t notification_hash_item(uint64_t hash, const Notification *n) {
  hash = notification_hash_bytes(hash, &n->id, sizeof(n->id));
  hash = notification_hash_string(hash, n->summary);
  hash = notification_hash_string(hash, n->body);
  hash = notification_hash_string(hash, n->input_text);
  hash = notification_hash_string(hash, n->input_placeholder);
  hash = notification_hash_bytes(hash, &n->img_pixels, sizeof(n->img_pixels));
  hash = notification_hash_bytes(hash, &n->img_w, sizeof(n->img_w));
  hash = notification_hash_bytes(hash, &n->img_h, sizeof(n->img_h));
  hash = notification_hash_bytes(hash, &n->action_count,
                                 sizeof(n->action_count));
  hash = notification_hash_bytes(hash, &n->input_enabled,
                                 sizeof(n->input_enabled));
  hash = notification_hash_bytes(hash, &n->action_used,
                                 sizeof(n->action_used));
  for (unsigned int i = 0; n->actions && i < n->action_count; i++)
    hash = notification_hash_string(hash, n->actions[i]);
  return hash;
}

static uint64_t notification_frame_hash(int history) {
  uint64_t hash = UINT64_C(14695981039346656037);
  Notification *n;
  hash = notification_hash_bytes(hash, &history, sizeof(history));
  hash = notification_hash_bytes(hash, &notify_width, sizeof(notify_width));
  hash = notification_hash_bytes(hash, &notify_height, sizeof(notify_height));
  if (history) {
    hash = notification_hash_bytes(hash, &notify_history_count,
                                   sizeof(notify_history_count));
    hash = notification_hash_bytes(hash, &notify_history_hover_entry,
                                   sizeof(notify_history_hover_entry));
    hash = notification_hash_bytes(hash, &notify_history_hover_action,
                                   sizeof(notify_history_hover_action));
    hash = notification_hash_bytes(hash, &notify_history_input,
                                   sizeof(notify_history_input));
    for (n = notify_history_head; n; n = n->next)
      hash = notification_hash_item(hash, n);
  } else if (notify_current) {
    hash = notification_hash_item(hash, notify_current);
    hash = notification_hash_bytes(hash, &notify_hovered,
                                   sizeof(notify_hovered));
    hash = notification_hash_bytes(hash, &notify_hover, sizeof(notify_hover));
    hash = notification_hash_bytes(hash, &notify_input_focus,
                                   sizeof(notify_input_focus));
    hash = notification_hash_bytes(hash, &notify_text_y, sizeof(notify_text_y));
    hash = notification_hash_bytes(hash, &notify_image_y,
                                   sizeof(notify_image_y));
    hash = notification_hash_bytes(hash, &notify_input_x,
                                   sizeof(notify_input_x));
    hash = notification_hash_bytes(hash, &notify_input_y,
                                   sizeof(notify_input_y));
    hash = notification_hash_bytes(hash, &notify_input_w,
                                   sizeof(notify_input_w));
    hash = notification_hash_bytes(hash, &notify_input_h,
                                   sizeof(notify_input_h));
    hash = notification_hash_bytes(hash, notify_action_x,
                                   sizeof(notify_action_x));
    hash = notification_hash_bytes(hash, notify_action_w,
                                   sizeof(notify_action_w));
    hash = notification_hash_bytes(hash, &notify_action_y,
                                   sizeof(notify_action_y));
  }
  return hash;
}

static int notification_frame_cached(int history) {
  return notify_render_cache_valid &&
         notify_render_cache_hash == notification_frame_hash(history);
}

static void notification_draw(void) {
  Notification *n = notify_current;
  unsigned int w = notify_width, h = notify_height;
  int pad = NOTIFY_PADDING, x = pad, baseline, line_h, ascender;
  int body_line_h;
  int img_w = 0, img_h = 0;
  int text_x, text_width;

  if (!n || !notify_active || !w || !h || !selmon || !selmon->barcenterwin)
    return;
  if (notification_frame_cached(0))
    return;
  if (!notification_gl_init(w, h))
    return;
  if (!gl_font)
    gl_font = gl_font_create();
  if (!gl_font)
    return;
  line_h = MAX(gl_font->height, 1);
  body_line_h = MAX((int)ceil(gl_font->pixel_size) +
                        NOTIFY_BODY_LINE_GAP,
                    1);
  ascender = MAX(1, (int)(gl_font->faces[0].face->size->metrics.ascender >> 6));
  if (n->image && n->image_w && n->image_h) {
    img_h = MIN((int)n->image_h, NOTIFY_IMAGE_MAX_H);
    img_w = (int)((double)n->image_w * img_h / n->image_h);
    if (img_w > 100) {
      img_w = 100;
      img_h = MAX(1, (int)((double)n->image_h * img_w / n->image_w));
    }
  }
  text_x = pad + (img_w ? img_w + 12 : 0);
  text_width = MAX(1, (int)w - text_x - pad);
  baseline = pad + notify_text_y + ascender;

  glViewport(0, 0, (GLsizei)w, (GLsizei)h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  glOrtho(0, w, h, 0, -1, 1);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
  glDisable(GL_DEPTH_TEST);
  glDisable(GL_SCISSOR_TEST);
  glClearColor(0, 0, 0, 0);
  glClear(GL_COLOR_BUFFER_BIT);
  glDisable(GL_TEXTURE_2D);

  if (img_w > 0 && n->img_pixels && n->img_w > 0 && n->img_h > 0) {
    notification_image_texture_create(n);
    if (n->img_texture)
      glBindTexture(GL_TEXTURE_2D, n->img_texture);
    if (n->img_texture) {
      glEnable(GL_TEXTURE_2D);
      glEnable(GL_BLEND);
      glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
      glColor4f(1, 1, 1, 1);
      glBegin(GL_QUADS);
      glTexCoord2f(0, 0); glVertex2f(x, pad + notify_image_y);
      glTexCoord2f(1, 0); glVertex2f(x + img_w, pad + notify_image_y);
      glTexCoord2f(1, 1); glVertex2f(x + img_w, pad + notify_image_y + img_h);
      glTexCoord2f(0, 1); glVertex2f(x, pad + notify_image_y + img_h);
      glEnd();
      glDisable(GL_BLEND);
      glDisable(GL_TEXTURE_2D);
    }
  }

  if (n->summary && *n->summary) {
    gl_font_draw_text(n->summary, text_x, baseline, text_width,
                      1.0f, 1.0f, 1.0f);
    baseline += line_h + 2;
  }
  if (n->body && *n->body)
    notification_gl_draw_body(n, text_x, &baseline, body_line_h,
                              text_width,
                              notify_hovered
                                  ? NOTIFY_POPUP_BODY_HOVER_MAX_LINES
                                  : NOTIFY_POPUP_BODY_MAX_LINES,
                              0.82f, 0.85f, 0.9f);

  /* Controls are intentionally just text: their rows have hitboxes but no
   * filled rectangles, borders, or other button/input backgrounds. */
  if (n->input_enabled) {
    const char *value = n->input_text && *n->input_text
        ? n->input_text : n->input_placeholder;
    const char *visible = value;
    unsigned int max_width = (unsigned int)MAX(1, notify_input_w);
    if (!value)
      value = "";
    visible = value;
    if (n->input_text && *n->input_text) {
      visible = n->input_text;
      while (*visible && gl_font_text_width(visible) +
             (notify_input_focus ? gl_font_text_width("|") : 0U) > max_width)
        notification_utf8_next(&visible);
    }
    if (notify_input_focus) {
      const char *typed = n->input_text && *n->input_text ? visible : "";
      size_t len = strlen(typed);
      char *with_cursor = malloc(len + 2);
      if (with_cursor) {
        memcpy(with_cursor, typed, len);
        with_cursor[len] = '|';
        with_cursor[len + 1] = '\0';
        gl_font_draw_text(with_cursor, notify_input_x,
                          notify_input_y + MAX(0, (NOTIFY_INPUT_ROW_H - line_h) / 2) + ascender,
                          max_width,
                          1.0f, 1.0f, 1.0f);
        if (!len && value && *value) {
          unsigned int cursor_w = notification_text_width("|");
          gl_font_draw_text(value, notify_input_x + cursor_w,
                            notify_input_y + MAX(0, (NOTIFY_INPUT_ROW_H - line_h) / 2) + ascender,
                            max_width > cursor_w ? max_width - cursor_w : 0,
                            0.58f, 0.61f, 0.66f);
        }
        free(with_cursor);
      }
    } else {
      float r = n->input_text && *n->input_text ? 0.92f : 0.58f;
      float g = n->input_text && *n->input_text ? 0.93f : 0.61f;
      float b = n->input_text && *n->input_text ? 0.96f : 0.66f;
      gl_font_draw_text(visible, notify_input_x,
                        notify_input_y + MAX(0, (NOTIFY_INPUT_ROW_H - line_h) / 2) + ascender,
                        max_width, r, g, b);
    }
  }
  for (unsigned int i = 0; notify_hovered && n->actions &&
       i < MIN(n->action_count / 2, LENGTH(notify_action_x)); i++) {
    const char *label = n->actions[i * 2 + 1];
    unsigned int cell_w = (unsigned int)MAX(1, notify_action_w[i]);
    unsigned int label_w = notification_text_width(label);
    int label_x = notify_action_x[i] +
        (int)(cell_w - MIN(label_w, cell_w));
    int hovered = notify_hover == (int)i;
    float r = hovered ? 1.0f : 0.82f;
    float g = hovered ? 1.0f : 0.85f;
    float b = hovered ? 1.0f : 0.9f;
    gl_font_draw_text(label, label_x,
                      notify_action_y + MAX(0, (NOTIFY_BUTTON_H - line_h) / 2) + ascender,
                      cell_w, r, g, b);
  }

  notification_present_gl(w, h, None);
  notify_render_cache_hash = notification_frame_hash(0);
  notify_render_cache_valid = 1;
}

static unsigned int notification_history_surface_height(void) {
  Notification *n;
  unsigned int height = 2U * NOTIFY_PADDING;

  for (n = notify_history_head; n; n = n->next)
    height += notification_history_entry_height(n);
  return MAX(height, notify_height);
}

static int notification_history_mask_create(unsigned int w,
                                            unsigned int h) {
  XRenderPictFormat *format;
  Pixmap pixmap;
  Picture picture;

  if (notify_history_mask_picture && notify_history_mask_w == w &&
      notify_history_mask_h == h)
    return 1;
  if (notify_history_mask_picture)
    XRenderFreePicture(dpy, notify_history_mask_picture);
  if (notify_history_mask_pixmap)
    XFreePixmap(dpy, notify_history_mask_pixmap);
  notify_history_mask_picture = None;
  notify_history_mask_pixmap = None;
  notify_history_mask_w = notify_history_mask_h = 0;

  format = XRenderFindStandardFormat(dpy, PictStandardA8);
  if (!format)
    return 0;
  pixmap = XCreatePixmap(dpy, root, w, h, 8);
  if (!pixmap)
    return 0;
  picture = XRenderCreatePicture(dpy, pixmap, format, 0, NULL);
  if (!picture) {
    XFreePixmap(dpy, pixmap);
    return 0;
  }
  for (unsigned int y = 0; y < h; y++) {
    unsigned char opacity = notification_vertical_alpha(y, h);
    XRenderColor color = {0, 0, 0, (unsigned short)(opacity * 257U)};
    XRenderFillRectangle(dpy, PictOpSrc, picture, &color, 0, (int)y, w, 1);
  }
  notify_history_mask_pixmap = pixmap;
  notify_history_mask_picture = picture;
  notify_history_mask_w = w;
  notify_history_mask_h = h;
  return 1;
}

static int notification_history_background_create(void) {
  XRenderPictFormat *format;
  XRenderPictureAttributes attributes = {0};
  XRenderColor color = {7864, 8519, 11141, 65535};
  Pixmap pixmap;
  Picture picture;

  if (notify_history_background_picture)
    return 1;
  format = XRenderFindStandardFormat(dpy, PictStandardARGB32);
  if (!format)
    return 0;
  pixmap = XCreatePixmap(dpy, root, 1, 1, 32);
  if (!pixmap)
    return 0;
  attributes.repeat = True;
  picture = XRenderCreatePicture(dpy, pixmap, format, CPRepeat, &attributes);
  if (!picture) {
    XFreePixmap(dpy, pixmap);
    return 0;
  }
  XRenderFillRectangle(dpy, PictOpSrc, picture, &color, 0, 0, 1, 1);
  notify_history_background_pixmap = pixmap;
  notify_history_background_picture = picture;
  return 1;
}

static int notification_history_cache_create(unsigned int w,
                                             unsigned int h) {
  XWindowAttributes attr;
  Pixmap pixmap;
  GC gc;
  XRenderPictFormat *format;

  if (!selmon || !selmon->barcenterwin || !w || !h ||
      !XGetWindowAttributes(dpy, selmon->barcenterwin, &attr))
    return 0;
  pixmap = XCreatePixmap(dpy, selmon->barcenterwin, w, h,
                         (unsigned int)attr.depth);
  if (!pixmap)
    return 0;
  gc = XCreateGC(dpy, pixmap, 0, NULL);
  if (!gc) {
    XFreePixmap(dpy, pixmap);
    return 0;
  }
  if (notify_history_gc)
    XFreeGC(dpy, notify_history_gc);
  if (notify_history_picture)
    XRenderFreePicture(dpy, notify_history_picture);
  if (notify_history_pixmap)
    XFreePixmap(dpy, notify_history_pixmap);
  notify_history_pixmap = pixmap;
  notify_history_gc = gc;
  format = XRenderFindStandardFormat(dpy, attr.depth == 32
      ? PictStandardARGB32 : PictStandardRGB24);
  notify_history_picture = format
      ? XRenderCreatePicture(dpy, pixmap, format, 0, NULL) : None;
  notify_history_pixmap_w = w;
  notify_history_pixmap_h = h;
  notify_render_cache_valid = 0;
  return 1;
}

static void notification_history_present(void) {
  unsigned int pad, content_h, content_src_y;
  XWindowAttributes attr;
  XRenderPictFormat *dest_format;

  if (!notify_history_active || !notify_history_pixmap ||
      !notify_history_gc || !selmon || !selmon->barcenterwin)
    return;
  if (notify_width > notify_history_pixmap_w ||
      notify_history_scroll < 0)
    return;

  /* Keep the viewport padding fixed while only scrolling the content region.
   * The old GL path used a scissor rectangle for exactly this clipping. */
  pad = MIN((unsigned int)NOTIFY_PADDING, notify_height / 2U);
  content_h = notify_height - 2U * pad;
  content_src_y = pad + (unsigned int)notify_history_scroll;
  if (notify_history_pixmap_h < content_src_y)
    return;
  content_h = MIN(content_h, notify_history_pixmap_h - content_src_y);
  if (notify_history_dest_window != selmon->barcenterwin) {
    if (notify_history_dest_picture)
      XRenderFreePicture(dpy, notify_history_dest_picture);
    notify_history_dest_picture = None;
    notify_history_dest_window = selmon->barcenterwin;
  }
  if (notify_history_picture &&
      notification_history_background_create() &&
      notification_history_mask_create(notify_width, notify_height) &&
      (notify_history_dest_picture ||
       (XGetWindowAttributes(dpy, selmon->barcenterwin, &attr) &&
        (dest_format = XRenderFindVisualFormat(dpy, attr.visual)) &&
        (notify_history_dest_picture = XRenderCreatePicture(
             dpy, selmon->barcenterwin, dest_format, 0, NULL))))) {
    XRenderComposite(dpy, PictOpSrc, notify_history_background_picture,
                     notify_history_mask_picture, notify_history_dest_picture,
                     0, 0, 0, 0, 0, 0, notify_width, notify_height);
    if (content_h)
      XRenderComposite(dpy, PictOpOver, notify_history_picture, None,
                       notify_history_dest_picture,
                       0, (int)content_src_y, 0, (int)pad, 0, (int)pad,
                       notify_width, content_h);
    XFlush(dpy);
    return;
  }
  if (pad) {
    XCopyArea(dpy, notify_history_pixmap, selmon->barcenterwin,
              notify_history_gc, 0, 0, notify_width, pad, 0, 0);
    XCopyArea(dpy, notify_history_pixmap, selmon->barcenterwin,
              notify_history_gc, 0, 0, notify_width, pad, 0,
              (int)(notify_height - pad));
  }
  if (content_h)
    XCopyArea(dpy, notify_history_pixmap, selmon->barcenterwin,
              notify_history_gc, 0, (int)content_src_y, notify_width,
              content_h, 0, (int)pad);
  XFlush(dpy);
}

static void notification_history_draw(void) {
  Notification *n;
  unsigned int w = notify_width, h = notification_history_surface_height();
  unsigned int pad = NOTIFY_PADDING, content_w;
  int line_h, body_line_h, ascender, y;

  if (!notify_history_active || !notify_history_count || !w || !h ||
      !selmon || !selmon->barcenterwin)
    return;
  if ((notify_history_pixmap_w != w || notify_history_pixmap_h != h ||
       !notify_history_pixmap || !notify_history_gc) &&
      !notification_history_cache_create(w, h))
    return;
  if (notification_frame_cached(1)) {
    notification_history_present();
    return;
  }
  if (!notification_gl_init(w, h))
    return;
  if (!gl_font)
    gl_font = gl_font_create();
  if (!gl_font)
    return;
  content_w = w > 2U * pad ? w - 2U * pad : 1U;
  line_h = MAX(gl_font->height, 1);
  body_line_h = MAX((int)ceil(gl_font->pixel_size) +
                        NOTIFY_BODY_LINE_GAP,
                    1);
  ascender = MAX(1, (int)(gl_font->faces[0].face->size->metrics.ascender >> 6));

  glViewport(0, 0, (GLsizei)w, (GLsizei)h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  glOrtho(0, w, h, 0, -1, 1);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
  glDisable(GL_DEPTH_TEST);
  glDisable(GL_SCISSOR_TEST);
  glClearColor(0.0f, 0.0f, 0.0f, 0.0f);
  glClear(GL_COLOR_BUFFER_BIT);
  glDisable(GL_TEXTURE_2D);
  glEnable(GL_SCISSOR_TEST);
  glScissor((GLint)pad, (GLint)pad, (GLsizei)content_w,
            (GLsizei)(h - 2U * pad));

  y = (int)pad;
  for (n = notify_history_head; n; n = n->next) {
    unsigned int entry_h = notification_history_entry_height(n);
    unsigned int content_h = notification_history_content_height(n);
    unsigned int img_w = 0, img_h = 0, body_w = content_w;
    unsigned int body_lines = 0, text_h;
    int has_summary = n->summary && *n->summary;
    int has_body = n->body && *n->body;
    int dimmed = n->action_used ||
                 (n->action_count < 2 && !n->input_enabled);
    int text_y, baseline, controls_y;

    if (y + (int)entry_h <= (int)pad) {
      y += (int)entry_h;
      continue;
    }
    if (y >= (int)(h - pad))
      break;

    if (n->image && n->image_w && n->image_h) {
      img_h = MIN(n->image_h, (unsigned int)NOTIFY_IMAGE_MAX_H);
      img_w = (unsigned int)((uint64_t)n->image_w * img_h / n->image_h);
      if (img_w > 100) {
        img_w = 100;
        img_h = MAX(1U, (unsigned int)((uint64_t)n->image_h * img_w /
                                       n->image_w));
      }
      body_w = body_w > img_w + 12 ? body_w - img_w - 12 : 1;
    }
    if (has_body)
      body_lines = notification_body_wrap(n, body_w,
                                          NOTIFY_HISTORY_BODY_MAX_LINES);
    text_h = notification_text_block_height(has_summary, body_lines);
    text_y = y + MAX(0, ((int)content_h - (int)text_h) / 2);
    baseline = text_y + ascender;

    if (img_w && n->img_pixels && n->img_w && n->img_h) {
      notification_image_texture_create(n);
      if (n->img_texture)
        glBindTexture(GL_TEXTURE_2D, n->img_texture);
      if (n->img_texture) {
        glEnable(GL_TEXTURE_2D);
        glEnable(GL_BLEND);
        notification_gl_blend_separate();
        glColor4f(dimmed ? 0.68f : 1.0f,
                  dimmed ? 0.70f : 1.0f,
                  dimmed ? 0.73f : 1.0f, 1.0f);
        glBegin(GL_QUADS);
        glTexCoord2f(0, 0); glVertex2f((float)pad, (float)y + (content_h - img_h) / 2.0f);
        glTexCoord2f(1, 0); glVertex2f((float)pad + img_w, (float)y + (content_h - img_h) / 2.0f);
        glTexCoord2f(1, 1); glVertex2f((float)pad + img_w, (float)y + (content_h + img_h) / 2.0f);
        glTexCoord2f(0, 1); glVertex2f((float)pad, (float)y + (content_h + img_h) / 2.0f);
        glEnd();
        glDisable(GL_BLEND);
        glDisable(GL_TEXTURE_2D);
      }
    }
    if (has_summary) {
      gl_font_draw_text(n->summary, (int)pad + (img_w ? (int)img_w + 12 : 0), baseline,
                        body_w, dimmed ? 0.84f : 1.0f,
                        dimmed ? 0.86f : 1.0f,
                        dimmed ? 0.90f : 1.0f);
      baseline += line_h + 2;
    }
    if (has_body)
      notification_gl_draw_body(n,
                                (int)pad + (img_w ? (int)img_w + 12 : 0),
                                &baseline, body_line_h, body_w,
                                NOTIFY_HISTORY_BODY_MAX_LINES,
                                dimmed ? 0.56f : 0.82f,
                                dimmed ? 0.58f : 0.85f,
                                dimmed ? 0.61f : 0.9f);

    controls_y = y + (int)content_h;
    if (n->input_enabled) {
      const char *value = n->input_text && *n->input_text
          ? n->input_text : n->input_placeholder;
      float r = n->input_text && *n->input_text ? 0.92f : 0.58f;
      float g = n->input_text && *n->input_text ? 0.93f : 0.61f;
      float b = n->input_text && *n->input_text ? 0.96f : 0.66f;
      gl_font_draw_text(value ? value : "", (int)pad,
                        controls_y + MAX(0, (NOTIFY_INPUT_ROW_H - line_h) / 2) + ascender,
                        content_w, r, g, b);
      controls_y += NOTIFY_INPUT_ROW_H;
    }
    if (n->action_count >= 4) {
      unsigned int actions = MIN(n->action_count / 2, 16U);
      unsigned int cell_w = actions ? content_w / actions : content_w;
      for (unsigned int i = 0; i < actions; i++) {
        const char *label = n->actions[i * 2 + 1];
        unsigned int label_w = notification_text_width(label);
        int label_x = (int)pad +
                      (int)((i + 1 == actions ? content_w : (i + 1) * cell_w)) -
                      (int)MIN(label_w, cell_w);
        int hovered = notify_history_hover_action == (int)i;
        gl_font_draw_text(label, label_x,
                          controls_y + MAX(0, (NOTIFY_BUTTON_H - line_h) / 2) + ascender,
                          cell_w, hovered ? 1.0f : 0.82f,
                          hovered ? 1.0f : 0.85f,
                          hovered ? 1.0f : 0.9f);
      }
    }

    y += (int)entry_h;
  }
  glDisable(GL_SCISSOR_TEST);
  notification_present_gl(w, h, notify_history_pixmap);
  notify_render_cache_hash = notification_frame_hash(1);
  notify_render_cache_valid = 1;
  notification_history_present();
}

static void notification_draw_foreground(int history) {
  if (history)
    notification_history_draw();
  else
    notification_draw();
}

static void notification_present_layers(int history) {
  notification_draw_foreground(history);
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
          ev->x < notify_action_x[i] + notify_action_w[i]) {
        int button_y = notification_action_row_y(n);
        if (ev->y >= button_y && ev->y < button_y + NOTIFY_BUTTON_H) {
          hover = (int)i;
          break;
        }
      }
  }
  if (hover != notify_hover) {
    notify_hover = hover;
    drawbars();
  }
}

static void notification_history_motion(XMotionEvent *ev) {
  Notification *n, *hovered = NULL;
  int entry_y = NOTIFY_PADDING - notify_history_scroll;
  int local_y = 0, action = -1;
  unsigned int content_w = notify_width > 2U * NOTIFY_PADDING
                               ? notify_width - 2U * NOTIFY_PADDING : 1U;

  if (!notify_history_active)
    return;
  for (n = notify_history_head;
       ev->y >= (int)NOTIFY_PADDING &&
       ev->y < (int)(notify_height - NOTIFY_PADDING) && n; n = n->next) {
    unsigned int entry_h = notification_history_entry_height(n);
    if (ev->y >= entry_y &&
        ev->y < entry_y + (int)notification_history_entry_content_height(n)) {
      hovered = n;
      local_y = ev->y - entry_y;
      break;
    }
    entry_y += (int)entry_h;
  }

  if (hovered && hovered->action_count >= 4 &&
      ev->x >= NOTIFY_PADDING && ev->x < (int)(NOTIFY_PADDING + content_w) &&
      local_y >= (int)notification_history_content_height(hovered) +
                     (hovered->input_enabled ? NOTIFY_INPUT_ROW_H : 0) &&
      local_y < (int)notification_history_entry_height(hovered)) {
    unsigned int count = MIN(hovered->action_count / 2, 16U);
    unsigned int cell_w = count ? content_w / count : content_w;
    action = MIN((int)((ev->x - (int)NOTIFY_PADDING) / MAX(cell_w, 1U)),
                 (int)count - 1);
  }
  if (notify_history_hover_entry != hovered ||
      notify_history_hover_action != action) {
    notify_history_hover_entry = hovered;
    notify_history_hover_action = action;
    if (hovered)
      clock_gettime(CLOCK_MONOTONIC, &notify_history_hover_started);
    /* Hover only changes action-label color; history geometry is unchanged. */
    drawbars();
  }
}

static int notification_history_buttonpress(XButtonPressedEvent *ev) {
  Notification *n;
  int entry_y = NOTIFY_PADDING - notify_history_scroll;
  unsigned int content_w = notify_width > 2U * NOTIFY_PADDING
                               ? notify_width - 2U * NOTIFY_PADDING : 1U;

  if (!notify_history_active)
    return 0;
  if (ev->button == Button4 || ev->button == Button5) {
    int max_scroll = 0, old_target = notify_history_scroll_target;
    int was_animating =
        notify_history_scroll != notify_history_scroll_target;
    int base_scroll = was_animating ? notify_history_scroll_target
                                    : notify_history_scroll;
    unsigned int total = 0;
    unsigned int viewport_h = notify_height > 2U * NOTIFY_PADDING
                                 ? notify_height - 2U * NOTIFY_PADDING : 0;
    for (n = notify_history_head; n; n = n->next)
      total += notification_history_entry_height(n);
    if (total > viewport_h)
      max_scroll = (int)(total - viewport_h);
    notify_history_scroll_target = MAX(0, MIN(max_scroll,
        base_scroll + (ev->button == Button4 ? -60 : 60)));
    if (notify_history_scroll_target == old_target)
      return 1;
    if (!was_animating)
      clock_gettime(CLOCK_MONOTONIC, &notify_history_scroll_started);
    drawbars();
    return 1;
  }
  if (ev->button != Button1)
    return 1;
  if (ev->x < (int)NOTIFY_PADDING ||
      ev->x >= (int)(NOTIFY_PADDING + content_w) ||
      ev->y < (int)NOTIFY_PADDING ||
      ev->y >= (int)(notify_height - NOTIFY_PADDING))
    return 1;

  for (n = notify_history_head; n; n = n->next) {
    unsigned int entry_h = notification_history_entry_height(n);
    int local_y = ev->y - entry_y;
    int controls_y = (int)notification_history_content_height(n);
    if (ev->y >= entry_y && ev->y < entry_y + (int)entry_h) {
      if (local_y >= (int)notification_history_entry_content_height(n))
        return 1;
      if (n->input_enabled && local_y >= controls_y &&
          local_y < controls_y + NOTIFY_INPUT_ROW_H) {
        notify_history_input = n;
        notify_input_focus = 1;
        XSetInputFocus(dpy, selmon->barcenterwin, RevertToParent, CurrentTime);
        drawbars();
        return 1;
      }
      controls_y += n->input_enabled ? NOTIFY_INPUT_ROW_H : 0;
      if (n->action_count >= 4 && local_y >= controls_y &&
          local_y < controls_y + NOTIFY_BUTTON_H) {
        unsigned int count = MIN(n->action_count / 2, 16U);
        unsigned int cell_w = count ? MAX(content_w / count, 1U) : content_w;
        unsigned int index = MIN((unsigned int)(ev->x - (int)NOTIFY_PADDING) /
                                     cell_w,
                                 count ? count - 1 : 0);
        notification_emit_action(n, n->actions[index * 2]);
        notification_emit_closed(n, 2);
        notification_history_clear_controls(n);
        if (notify_history_input == n)
          notify_history_input = NULL;
        notify_input_focus = 0;
        notification_history_layout();
        drawbars();
        resizebarwin(selmon);
        return 1;
      }
      if (n->action_count >= 2) {
        notification_emit_action(n, n->actions[0]);
        notification_emit_closed(n, 2);
        notification_history_clear_controls(n);
        notification_history_layout();
        drawbars();
        resizebarwin(selmon);
      }
      return 1;
    }
    entry_y += (int)entry_h;
  }
  return 1;
}

static int notification_history_tick(void) {
  struct timespec now;
  double elapsed, fraction;
  int delta, step;

  if (!notify_history_active ||
      notify_history_scroll == notify_history_scroll_target)
    return 0;

  /* Mouse/event traffic can keep poll() returning immediately.  Rate-limit
   * actual scroll frames here as well as bounding the idle poll timeout. */
  if (notification_elapsed(&notify_history_scroll_started) <
      1.0 / NOTIFY_HISTORY_FPS)
    return 1;

  clock_gettime(CLOCK_MONOTONIC, &now);
  elapsed = (double)(now.tv_sec - notify_history_scroll_started.tv_sec) +
            (double)(now.tv_nsec - notify_history_scroll_started.tv_nsec) /
            1000000000.0;
  notify_history_scroll_started = now;
  fraction = 1.0 - exp(-MAX(0.0, elapsed) / 0.055);
  delta = notify_history_scroll_target - notify_history_scroll;
  step = (int)lround(delta * fraction);
  if (!step && delta)
    step = delta > 0 ? 1 : -1;
  if (abs(delta) <= 1)
    notify_history_scroll = notify_history_scroll_target;
  else
    notify_history_scroll += step;
  notification_history_present();
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
  if (n)
    n->action_used = 1;
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
  if (n)
    n->action_used = 1;
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
      drawbars();
    }
    return 1;
  }
  for (i = 0; i < LENGTH(notify_action_x); i++) {
    if (notify_action_w[i] && ev->x >= notify_action_x[i] &&
        ev->x < notify_action_x[i] + notify_action_w[i]) {
      int button_y = notification_action_row_y(n);
      if (ev->y >= button_y && ev->y < button_y + NOTIFY_BUTTON_H) {
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
      resizebarwin(selmon);
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
      resizebarwin(selmon);
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
      do {
        length--;
      } while (length &&
               (((unsigned char)n->input_text[length] & 0xc0) == 0x80));
      n->input_text[length] = '\0';
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
  if (notify_history_gc) {
    XFreeGC(dpy, notify_history_gc);
    notify_history_gc = None;
  }
  if (notify_history_picture) {
    XRenderFreePicture(dpy, notify_history_picture);
    notify_history_picture = None;
  }
  if (notify_history_mask_picture) {
    XRenderFreePicture(dpy, notify_history_mask_picture);
    notify_history_mask_picture = None;
  }
  if (notify_history_dest_picture) {
    XRenderFreePicture(dpy, notify_history_dest_picture);
    notify_history_dest_picture = None;
  }
  if (notify_history_background_picture) {
    XRenderFreePicture(dpy, notify_history_background_picture);
    notify_history_background_picture = None;
  }
  if (notify_history_mask_pixmap) {
    XFreePixmap(dpy, notify_history_mask_pixmap);
    notify_history_mask_pixmap = None;
  }
  if (notify_history_background_pixmap) {
    XFreePixmap(dpy, notify_history_background_pixmap);
    notify_history_background_pixmap = None;
  }
  notify_history_mask_w = notify_history_mask_h = 0;
  notify_history_dest_window = None;
  if (notify_history_pixmap) {
    XFreePixmap(dpy, notify_history_pixmap);
    notify_history_pixmap = None;
  }
  notify_history_pixmap_w = notify_history_pixmap_h = 0;
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

  /* Cleanup OpenGL font while the notification context is current. */
  if (notify_gl_ctx != None && notify_gl_pbuffer != None)
    glXMakeCurrent(dpy, notify_gl_pbuffer, notify_gl_ctx);
  if (gl_font) {
    gl_font_free(gl_font);
    gl_font = NULL;
  }

  /* Cleanup FreeType */
  if (ft_lib) {
    FT_Done_FreeType(ft_lib);
    ft_lib = NULL;
  }

  /* Cleanup OpenGL resources. */
  if (notify_gl_ctx != None) {
    glXMakeCurrent(dpy, None, NULL);
    glXDestroyContext(dpy, notify_gl_ctx);
    notify_gl_ctx = None;
  }
  if (notify_gl_pbuffer != None) {
    glXDestroyPbuffer(dpy, notify_gl_pbuffer);
    notify_gl_pbuffer = None;
  }
  notify_gl_pbuffer_w = notify_gl_pbuffer_h = 0;
  notify_gl_initialized = 0;
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
  *cw = finder_active && m == selmon ? finder_width :
        ((notification_center_active() && m == selmon) ? notify_width : clockbar_cw);
  *kw = kblayoutwidth();
  *tw = tagsbarwidth(m);
  avail = (barW > *tw + *rw + *cw + *kw + 4 * bargap + stgap)
              ? barW - *tw - *rw - *cw - *kw - 4 * bargap - stgap
              : 0;
  *tlw = borderpx + bartitlewidth(m, avail > borderpx ? avail - borderpx : 0);
  if (*tlw > avail)
    *tlw = avail;
}

static void map_center_window(Window win, int x, int y, unsigned int w,
                              unsigned int h, int fade) {
  if (finder_argb_visual)
    if (fade == 4)
      drw_map_alpha_background(drw, win, finder_argb_visual, x, y, w, h,
                               notify_bg.pixel);
    else if (fade == 2)
      drw_map_alpha_notification(drw, win, finder_argb_visual, x, y, w, h,
                                 0);
    else
      drw_map_alpha(drw, win, finder_argb_visual, x, y, w, h, fade);
  else
    drw_map(drw, win, x, y, w, h);
}

static void finder_window_text_at(Window win, int x, int y, unsigned int w,
                                  unsigned int h, const char *text, Clr *color,
                                  Fnt *font, int centered) {
  XftDraw *draw;
  XGlyphInfo ext;
  int tx, baseline;
  if (!finder_argb_visual || !text || !*text || !font)
    return;
  draw = XftDrawCreate(dpy, win, finder_argb_visual, finder_argb_colormap);
  if (!draw)
    return;
  XftTextExtentsUtf8(dpy, font->xfont, (const FcChar8 *)text,
                     strlen(text), &ext);
  tx = x + (centered && w > ext.xOff ? (int)(w - ext.xOff) / 2 : 0);
  baseline = y + ((int)h - font->xfont->ascent - font->xfont->descent) / 2
             + font->xfont->ascent;
  XftDrawStringUtf8(draw, color, font->xfont, tx, baseline,
                    (const FcChar8 *)text, strlen(text));
  XftDrawDestroy(draw);
}

static void finder_window_text(Window win, int x, int y, unsigned int w,
                               unsigned int h, const char *text, Clr *color,
                               Fnt *font) {
  finder_window_text_at(win, x, y, w, h, text, color, font, 1);
}

/* Draw the query centred like finder_window_text(), then append a blinking
 * cursor after the text.  The text stays centred whether the cursor is shown
 * or hidden, so it does not jitter on every blink. */
static void finder_window_query(Window win, int x, int y, unsigned int w,
                                unsigned int h, const char *text, Clr *color,
                                Fnt *font, int cursor, size_t cursor_pos) {
  XftDraw *draw;
  XGlyphInfo ext, cursor_ext;
  size_t len;
  int tx, baseline, cursor_h, cursor_x;

  if (!finder_argb_visual || !text || !*text || !font)
    return;
  draw = XftDrawCreate(dpy, win, finder_argb_visual, finder_argb_colormap);
  if (!draw)
    return;
  len = strlen(text);
  if (cursor_pos > len)
    cursor_pos = len;
  XftTextExtentsUtf8(dpy, font->xfont, (const FcChar8 *)text, len, &ext);
  tx = x + (w > ext.xOff ? (int)(w - ext.xOff) / 2 : 0);
  baseline = y + ((int)h - font->xfont->ascent - font->xfont->descent) / 2
             + font->xfont->ascent;
  XftDrawStringUtf8(draw, color, font->xfont, tx, baseline,
                    (const FcChar8 *)text, len);
  if (cursor) {
    memset(&cursor_ext, 0, sizeof(cursor_ext));
    if (cursor_pos > 0)
      XftTextExtentsUtf8(dpy, font->xfont, (const FcChar8 *)text, cursor_pos,
                         &cursor_ext);
    cursor_x = tx + (int)cursor_ext.xOff + (cursor_pos == len ? 2 : 1);
    cursor_h = (int)font->h;
    if (cursor_h > (int)h)
      cursor_h = (int)h;
    if (cursor_h < 2)
      cursor_h = 2;
    XftDrawRect(draw, color, cursor_x,
                y + ((int)h - cursor_h) / 2, 2, (unsigned int)cursor_h);
  }
  XftDrawDestroy(draw);
}

static void finder_window_icon(Window win, int x, int y, unsigned int w,
                               unsigned int h, Picture icon) {
  XRenderPictFormat *format;
  Picture dest;
  if (!finder_argb_visual || !icon)
    return;
  format = XRenderFindVisualFormat(dpy, finder_argb_visual);
  dest = format ? XRenderCreatePicture(dpy, win, format, 0, NULL) : None;
  if (dest) {
    XRenderComposite(dpy, PictOpOver, icon, None, dest, 0, 0, 0, 0,
                     x, y, w, h);
    XRenderFreePicture(dpy, dest);
  }
}

static int finder_argb_error(Display *display, XErrorEvent *event) {
  (void)display;
  if (event->request_code == 1)
    finder_argb_create_failed = 1;
  return 0;
}

void drawbar(Monitor *m) {
  int y = borderpx;
  int bh_n = bh - borderpx * 2;
  int boxs = drw->fonts->h / 9;
  int boxw = drw->fonts->h / 6 + 2;
  int x, w;
  unsigned int i, occ = 0;
  unsigned int tw, tlw, cw, kw, rw;
  Client *c;

  if (!m->showbar) {
    if (m == selmon)
      clockbar_win = 0;
    return;
  }

  for (c = m->clients; c; c = c->next) {
    occ |= (c->issticky ? c->oldtags : c->tags);
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
    drw_text(drw, x, y, w, bh_n, lrpad / 2, tags[i], 0);
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
   notification_update_wm_class(m->barcenterwin,
                                 m == selmon && (notification_center_active() || finder_active),
                                 notify_history_active && !notify_active,
                                 m == selmon && finder_active);
   /* Finder must override a notification that was already open. */
   unsigned int dcw = (finder_active && m == selmon) ? finder_width
                                      : ((notification_center_active() && m == selmon) ? notify_width
                                       : ((clockbar_dynw && !notify_clock_hovered &&
                                          m == selmon)
                                             ? clockbar_dynw : cw));
   unsigned int tcw = clockbar_cw;
   XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
   /* Finder owns several bar rows.  Clear the complete backing-surface area
    * before drawing it; clearing only the normal bar height leaves stale
    * pixels in the lower rows when the pointer is not generating expose
    * events for the center window. */
      XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, dcw,
                    (finder_active && m == selmon)
                        ? bh * finder_display_rows() + FINDER_EDGE : bh);
      if (finder_active && m == selmon && finder_dirty) {
         int row = 1;
         Clr finder_row_scheme[3];
         const char *query_display = finder_query[0] ? finder_query : clockstr;
         unsigned int query_width = drw_fontset_getwidth(drw, query_display);
         unsigned int query_pad = query_width < dcw - 2 * FINDER_EDGE
                                      ? (dcw - 2 * FINDER_EDGE - query_width) / 2
                                      : 0;
          /* First map only opaque background rectangles.  Applying the
           * gradient to the complete drw surface also fades glyphs and
           * icons, so Finder's foreground is rendered directly into the
           * ARGB window after this pass. */
          if (finder_argb_visual) {
            XSetForeground(drw->dpy, drw->gc, scheme[SchemeTitle][ColBg].pixel);
            XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, dcw, bh);
            XSetForeground(drw->dpy, drw->gc, scheme[SchemeNorm][ColBg].pixel);
            XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, bh, dcw,
                           bh * (finder_display_rows() - 1) + FINDER_EDGE);
            map_center_window(m->barcenterwin, 0, 0, dcw,
                              bh * finder_display_rows() + FINDER_EDGE, 3);
            finder_window_query(m->barcenterwin, FINDER_EDGE, 0,
                                dcw - 2 * FINDER_EDGE, bh, query_display,
                                &scheme[SchemeTitle][ColFg], drw->fonts,
                                finder_query[0] && finder_cursor_visible,
                                finder_cursor);
            if (finder_math_active) {
              finder_window_text(m->barcenterwin, FINDER_EDGE, bh,
                                 dcw - 2 * FINDER_EDGE, bh,
                                 finder_math_result,
                                 &scheme[SchemeTitle][ColFg],
                                 finder_result_font ? finder_result_font : drw->fonts);
            }
            if (finder_math_help_active) {
              for (i = 0; i < LENGTH(finder_math_help) &&
                          row < finder_display_rows(); i++, row++)
                finder_window_text_at(m->barcenterwin, FINDER_EDGE, row * bh,
                                      dcw - 2 * FINDER_EDGE, bh,
                                      finder_math_help[i], &finder_text_clr,
                                      drw->fonts, 0);
            }
            for (i = (unsigned int)finder_scroll;
                 !finder_math_active && !finder_math_help_active &&
                 i < finder_visible && row < finder_display_rows();
                 i++) {
              FinderApp *app = &finder_apps[finder_order[i]];
              finder_window_text_at(m->barcenterwin,
                                     FINDER_EDGE + clockpad / 2 + 22 + FINDER_ICON_GAP,
                                     row * bh, dcw, bh, app->name,
                                      ((int)i == finder_selected)
                                        ? &scheme[SchemeTitle][ColFg]
                                        : &finder_text_clr,
                                     drw->fonts, 0);
              if (app->icon)
                finder_window_icon(m->barcenterwin, FINDER_EDGE + clockpad / 2,
                                   row * bh + (bh - 22) / 2, 22, 22,
                                   app->icon);
              row++;
            }
          } else {
            drw_setscheme(drw, scheme[SchemeTitle]);
            drw_text(drw, FINDER_EDGE, 0, dcw - 2 * FINDER_EDGE, bh,
                     query_pad, query_display, 0);
            if (finder_query[0] && finder_cursor_visible) {
              XGlyphInfo cursor_ext;
              size_t query_len = strlen(finder_query);
              size_t cursor_pos = MIN(finder_cursor, query_len);
              int cursor_h = (int)drw->fonts->h;
              int cursor_x;

              memset(&cursor_ext, 0, sizeof(cursor_ext));
              if (cursor_pos > 0)
                XftTextExtentsUtf8(dpy, drw->fonts->xfont,
                                   (const FcChar8 *)finder_query, cursor_pos,
                                   &cursor_ext);
              cursor_x = FINDER_EDGE + (int)query_pad +
                         (int)cursor_ext.xOff +
                         (cursor_pos == query_len ? 2 : 1);
              if (cursor_h > bh - 4)
                cursor_h = bh - 4;
              if (cursor_h < 2)
                cursor_h = 2;
              if (cursor_x + 2 <= (int)dcw - FINDER_EDGE)
                drw_rect(drw, cursor_x, (bh - cursor_h) / 2, 2,
                         (unsigned int)cursor_h, 1, 0);
            }
            if (finder_math_active) {
              Fnt *saved_fonts = drw->fonts;
              unsigned int result_width;
              drw->fonts = finder_result_font ? finder_result_font : saved_fonts;
              result_width = drw_fontset_getwidth(drw, finder_math_result);
              unsigned int result_pad = result_width < dcw - 2 * FINDER_EDGE
                                          ? (dcw - 2 * FINDER_EDGE - result_width) / 2
                                          : 0;
              drw_setscheme(drw, scheme[SchemeTitle]);
              drw_text(drw, FINDER_EDGE, bh, dcw - 2 * FINDER_EDGE, bh,
                       result_pad, finder_math_result, 0);
              drw->fonts = saved_fonts;
            }
            if (finder_math_help_active) {
              finder_row_scheme[ColFg] = finder_text_clr;
              finder_row_scheme[ColBg] = scheme[SchemeNorm][ColBg];
              finder_row_scheme[ColBorder] = scheme[SchemeNorm][ColBorder];
              drw_setscheme(drw, finder_row_scheme);
              for (i = 0; i < LENGTH(finder_math_help) &&
                          row < finder_display_rows(); i++, row++)
                drw_text(drw, 0, row * bh, dcw, bh, FINDER_EDGE,
                         finder_math_help[i], 0);
            }
            for (i = (unsigned int)finder_scroll;
                 !finder_math_active && !finder_math_help_active &&
                 i < finder_visible && row < finder_display_rows();
                 i++) {
              FinderApp *app = &finder_apps[finder_order[i]];
              finder_row_scheme[ColFg] = finder_text_clr;
              finder_row_scheme[ColBg] = scheme[SchemeNorm][ColBg];
              finder_row_scheme[ColBorder] = scheme[SchemeNorm][ColBorder];
              if ((int)i == finder_selected)
                finder_row_scheme[ColFg] = scheme[SchemeTitle][ColFg];
              drw_setscheme(drw, finder_row_scheme);
              drw_text(drw, 0, row * bh, dcw, bh,
                       FINDER_EDGE + clockpad / 2 + 22 + FINDER_ICON_GAP,
                       app->name, 0);
              if (app->icon)
                drw_pic(drw, FINDER_EDGE + clockpad / 2,
                        row * bh + (bh - 22) / 2, 22, 22,
                        app->icon);
              row++;
            }
            map_center_window(m->barcenterwin, 0, 0, dcw,
                              bh * finder_display_rows() + FINDER_EDGE, 3);
          }
          finder_marker(m, finder_visible_count() > finder_scroll &&
                           finder_selected >= finder_scroll &&
                           finder_selected < finder_scroll + finder_rows
                             ? finder_selected - finder_scroll + 1 : 0);
          finder_dirty = 0;
      } else if (finder_active && m == selmon) {
        notify_render_cache_valid = 0;
        /* The Finder surface is already current. Keep its marker and backing
        * window untouched while the other bar sections continue updating. */
         finder_marker(m, finder_visible_count() > finder_scroll &&
                         finder_selected >= finder_scroll &&
                        finder_selected < finder_scroll + finder_rows
                           ? finder_selected - finder_scroll + 1 : 0);
         } else if (notify_active && m == selmon) {
          finder_marker(m, 0);
          notification_present_layers(0);
         } else if (notify_history_active && m == selmon) {
         finder_marker(m, 0);
         notification_present_layers(1);
    } else {
      if (m == selmon)
        notify_render_cache_valid = 0;
      finder_marker(m, 0);
    drw_setscheme(drw, scheme[m == selmon ? SchemeTitle : SchemeNorm]);
    drw_rect(drw, 0, borderpx, dcw, bh_n, 1, 1);
    drw_text(drw, dcw > tcw ? (int)((dcw - tcw) / 2) : 0,
             borderpx + vertpadbar / 2, tcw, bh - vertpadbar, clockpad, clockstr,
             0);
    map_center_window(m->barcenterwin, 0, 0, dcw, bh, 0);
  }

  /* center bar: keyboard layout */
  XSetForeground(drw->dpy, drw->gc, clrborder.pixel);
  XFillRectangle(drw->dpy, drw->drawable, drw->gc, 0, 0, kw, bh);
  drw_setscheme(drw, scheme[m == selmon ? SchemeTitle : SchemeNorm]);
  drw_rect(drw, 0, borderpx, kw, bh_n, 1, 1);
  drw_text(drw, 0, borderpx + vertpadbar / 2, kw, bh - vertpadbar, kblayoutpad,
           kbstr, 0);
  drw_map(drw, m->barkbwin, 0, 0, kw, bh);

  drawrightbar(m, rw);
}

static void drawrightbar(Monitor *m, unsigned int rw) {
  /* Keep the right/status surface independent from Finder's center surface.
   * This lets status and MPRIS updates continue while Finder is open without
   * redrawing or restacking the Finder. */
  if (m == selmon && mpris_hovered && mpris_active) {
    mpris_panel_draw(m, rw, bh * MPRIS_PANEL_HOVER_H);
    /* Draw the normal status once, above the artwork.  Drawing it before
     * the panel as well leaves stale glyphs visible through transparent
     * gaps between ^b status segments. */
    drawstatusbar(m, bh - borderpx * 2, stext);
    drw_map(drw, m->barrightwin, 0, 0, rw, bh * MPRIS_PANEL_HOVER_H);
  } else {
    if (m->mpris_volume_markerwin)
      XUnmapWindow(dpy, m->mpris_volume_markerwin);
    drawstatusbar(m, bh - borderpx * 2, stext);
    drw_map(drw, m->barrightwin, 0, 0, rw, bh);
  }
}

static void drawrightbar_only(void) {
  if (!selmon || !selmon->barrightwin)
    return;
  /* Recompute the right-bar geometry for status strings whose width changed,
   * but leave Finder's center surface and marker untouched. */
  resizebarwin(selmon);
  drawrightbar(selmon, statuswidth(stext));
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

  if (ev->window == selmon->mpris_volume_markerwin) {
    if (!mpris_marker_pressed && !mpris_marker_hovered) {
      mpris_marker_hovered = 1;
      drawbars();
    }
    return;
  }

  if (ev->window == selmon->barrightwin) {
    if (mpris_active && !mpris_hovered) {
      mpris_hovered = 1;
		  drawbars();
      resizebarwin(selmon);
    }
    return;
  }

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

  if (ev->window == selmon->mpris_volume_markerwin) {
    mpris_marker_pressed = 0;
    mpris_marker_hovered = 0;
    if (mpris_pointer_over_bar(selmon))
      return;
    if (mpris_volume_drag)
      return;
    mpris_volume_drag = 0;
    if (mpris_hovered) {
      mpris_hovered = 0;
      drawbars();
      resizebarwin(selmon);
    }
    return;
  }

  if (ev->window == selmon->barrightwin) {
    if (mpris_active && mpris_pointer_over_marker(selmon))
      return;
    if (mpris_volume_drag)
      return;
    mpris_volume_drag = 0;
    if (mpris_hovered) {
      mpris_hovered = 0;
      drawbars();
      resizebarwin(selmon);
    }
    return;
  }

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
    if (m == selmon && ev->window == m->barcenterwin &&
        (notify_active || notify_history_active))
      notify_render_cache_valid = 0;
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
  if (finder_keypress(ev))
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

  if (finder_active) {
    finder_motion(ev);
    return;
  }

  if (ev->window == selmon->mpris_volume_markerwin) {
    XMotionEvent forwarded = *ev;
    Window child;
    XTranslateCoordinates(dpy, root, selmon->barrightwin,
                          ev->x_root, ev->y_root, &forwarded.x,
                          &forwarded.y, &child);
    forwarded.window = selmon->barrightwin;
    if (mpris_hovered && mpris_active)
      mpris_panel_motion(&forwarded);
    return;
  }

  if (ev->window == selmon->barrightwin) {
    if (mpris_hovered && mpris_active && ev->y >= bh)
      mpris_panel_motion(ev);
    return;
  }

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
      if (fullscreen_st || notification_center_active() || finder_active) {
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
    if (finder_active) {
      clockbar_dynw = 0;
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
    if (m->mpris_volume_markerwin)
      XUnmapWindow(dpy, m->mpris_volume_markerwin);
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
   unsigned int dcw = (finder_active && m == selmon) ? finder_width :
                                      ((notification_center_active() && m == selmon) ? notify_width
                                       : ((clockbar_dynw && !notify_clock_hovered &&
                                          !fullscreen_st && m == selmon)
                                            ? clockbar_dynw : cw));
   unsigned int fcw = (finder_active && m == selmon) ? finder_width :
                      ((notification_center_active() && m == selmon) ? notify_width : clockbar_cw);
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
        unsigned int center_h = (finder_active && m == selmon) ? bh * finder_display_rows() + FINDER_EDGE :
                               ((notification_center_active() && m == selmon) ? notify_height : bh);
      if (m->barcenterwin) {
        XMoveResizeWindow(dpy, m->barcenterwin,
                          cx + (int)(fcw + 2 * bargap) / 2 - (int)dcw / 2,
                          center_y, dcw, center_h);
        XMapWindow(dpy, m->barcenterwin);
        /* Keep the center window above fullscreen clients as soon as the
         * fullscreen transition lays it out.  The visualizer also needs to
         * stay above the neighboring bar sections while it grows. */
             if ((finder_active && m == selmon && finder_dirty) ||
                (notification_center_active() &&
                 !(m == selmon && mpris_hovered && mpris_active)) ||
               (clockbar_dynw && !fullscreen_st &&
                !(m == selmon && mpris_hovered && mpris_active)))
             XRaiseWindow(dpy, m->barcenterwin);
           else if (fullscreen_st && m == selmon && m->sel &&
                    m->sel->isfullscreen) {
             /* The notification center uses this same X window and is raised
              * above fullscreen.  Put it back below the fullscreen client
              * when the notification times out and the clock is restored. */
             XWindowChanges wc = {0};
             wc.sibling = m->sel->win;
             wc.stack_mode = Below;
             XConfigureWindow(dpy, m->barcenterwin,
                              CWSibling | CWStackMode, &wc);
           }
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
    XMoveResizeWindow(dpy, m->barrightwin, rx, m->by, rw,
                      (m == selmon && mpris_hovered && mpris_active)
                           ? bh * MPRIS_PANEL_HOVER_H : bh);
    XMapWindow(dpy, m->barrightwin);
    restack_mpris_panel(m);
  }

  /* Mapping the neighboring bar windows can put them above a center window
   * which was just opened.  Finder must remain above those windows even when
   * the pointer is elsewhere, so do the final raise after all bar sections
   * have been mapped. */
   if (m->barcenterwin && finder_active && m == selmon && finder_dirty) {
    XRaiseWindow(dpy, m->barcenterwin);
    if (m->finder_markerwin && m->finder_marker_mapped) {
      /* The center window was just raised, so restore the marker's position
       * once. Do not restack it during ordinary Finder redraws. */
      XRaiseWindow(dpy, m->finder_markerwin);
      m->finder_marker_stacked = 1;
    }
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

/* Fullscreen clients should cover normal windows, but not dialogs and
 * compositor/WM-owned overlays.  Keep these above fullscreen after a client
 * or the WM changes the stacking order. */
static void raisefullscreenoverlays(Monitor *m) {
  Client *c;

  if (!m)
    return;
  for (c = m->stack; c; c = c->snext)
    if (c->isontop && !c->isfullscreen && ISVISIBLE(c) && !HIDDEN(c))
      XRaiseWindow(dpy, c->win);
  if (m->sidebarvisible)
    XRaiseWindow(dpy, m->sidebarwin);
  if (m == selmon && notification_center_active() && m->barcenterwin)
    XRaiseWindow(dpy, m->barcenterwin);
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
  int timeout, pending_events;
  const int clockbar_timeout = 1000 / DRAW_FPS;
  const int history_scroll_timeout = 1000 / NOTIFY_HISTORY_FPS;
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

    if (finder_active && finder_loading) {
      finder_load_apps();
      finder_loading = 0;
      finder_icons_pending = 1;
      finder_dirty = 1;
    } else if (finder_active && finder_icons_pending) {
      if (!finder_load_next_icon())
        finder_icons_pending = 0;
      else
        finder_dirty = 1;
    }

    if (minimize_deadline && minimize_deadline < next_deadline)
      next_deadline = minimize_deadline;
    timeout = next_deadline > now ? (int)((next_deadline - now) * 1000) : 0;
    if (CLOCK_ANIMATE && !fullscreen_st && timeout > clockbar_timeout)
      timeout = clockbar_timeout;
    if (notify_current && timeout > 100)
      timeout = 100;
    if (notify_transition_pending && timeout > NOTIFY_TRANSITION_MS)
      timeout = NOTIFY_TRANSITION_MS;
    if (notify_history_active &&
        notify_history_scroll != notify_history_scroll_target &&
        timeout > history_scroll_timeout)
      timeout = history_scroll_timeout;
    if (mpris_active && !fullscreen_st && timeout > clockbar_timeout)
      timeout = clockbar_timeout;
    if (hasurgentclients() && timeout > 300)
      timeout = 300;
    if (finder_active && (finder_loading || finder_icons_pending))
      timeout = 0;
    if (finder_active && finder_query[0]) {
      uint64_t elapsed = finder_monotonic_ms() - finder_cursor_base_ms;
      uint64_t wait = FINDER_CURSOR_BLINK_MS -
                      elapsed % FINDER_CURSOR_BLINK_MS;
      if (timeout > (int)wait)
        timeout = (int)wait;
    }
    pfd[1].fd = notify_fd;
    pfd[2].fd = status_event_fd;
    poll(pfd, status_event_fd >= 0 ? 3 : (notify_fd >= 0 ? 2 : 1), timeout);
    if (notify_fd >= 0 && (pfd[1].revents & POLLIN))
      notification_dispatch();
    if (status_event_fd >= 0 && (pfd[2].revents & POLLIN))
      status_consume();
    {
      struct timespec now_mono;
      int urgent_redraw = 0;

      clock_gettime(CLOCK_MONOTONIC, &now_mono);
      if (hasurgentclients()) {
        long elapsed_ms = (now_mono.tv_sec - urgentflash_last.tv_sec) * 1000L +
                          (now_mono.tv_nsec - urgentflash_last.tv_nsec) / 1000000L;
        if (!urgentflash_last.tv_sec || elapsed_ms >= 300) {
          urgentflash = !urgentflash;
          urgentflash_last = now_mono;
          updateurgentborders();
          urgent_redraw = 1;
        }
      } else {
        urgentflash = 1;
        urgentflash_last.tv_sec = 0;
        urgentflash_last.tv_nsec = 0;
      }
      if (urgent_redraw)
        bar_dirty = 1;
    }
    if (CLOCK_ANIMATE)
      updateclockbar();
    if (finder_active && finder_query[0]) {
      int visible = finder_cursor_state();
      if (visible != finder_cursor_visible) {
        finder_cursor_visible = visible;
        finder_dirty = 1;
      }
    }
    {
      int redraw = bar_dirty;
      bar_dirty = 0;
      if (update_mpris_scroll())
        redraw = 1;
      /* Lazy icon decoding marks Finder dirty without touching bar_dirty.  A
       * full draw is required to show the newly decoded icon; only status or
       * MPRIS-only updates may use the right-bar fast path. */
      if (finder_active && finder_dirty)
        redraw = 1;
      if (redraw) {
        if (finder_active && !finder_dirty)
          drawrightbar_only();
        else
          drawbars();
      }
	    }
	    if (!mpris_active) {
			mpris_scroll_clock_valid = 0;
			mpris_scroll_accum_ns = 0;
		}
    /* Do not let a sustained stream of pointer events starve animation ticks.
     * Any remaining events stay queued and make the next poll return at once. */
    pending_events = 0;
    while (pending_events < 64 && XPending(dpy)) {
      XNextEvent(dpy, &ev);
      pending_events++;

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

    if (fullscreen_st && selmon && selmon->sel && selmon->sel->isfullscreen)
      raisefullscreenoverlays(selmon);

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
      /* Keep overlay clients mapped so dialogs and other always-on-top
       * windows can still appear over a fullscreen client.  Ordinary
       * clients are hidden below it as before. */
      if (it->isontop || (has_transparency && stickywin && it->issticky))
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
    raisefullscreenoverlays(c->mon);
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
  {
    XVisualInfo template = {0}, *visuals;
    int nvisuals, i;
    template.screen = screen;
    template.depth = 32;
    template.class = TrueColor;
    visuals = XGetVisualInfo(dpy, VisualScreenMask | VisualDepthMask |
                             VisualClassMask, &template, &nvisuals);
    for (i = 0; visuals && i < nvisuals; i++) {
      XRenderPictFormat *format = XRenderFindVisualFormat(dpy,
                                                           visuals[i].visual);
      if (format && format->type == PictTypeDirect &&
          format->direct.alphaMask) {
        finder_argb_visual = visuals[i].visual;
        finder_argb_depth = visuals[i].depth;
        finder_argb_colormap = XCreateColormap(dpy, root,
                                               finder_argb_visual, AllocNone);
        break;
      }
    }
    if (visuals)
      XFree(visuals);
  }
  drw = drw_create(dpy, screen, root, sw, sh);
  if (!drw_fontset_create(drw, fonts, LENGTH(fonts)))
    die("no fonts could be loaded.");
  {
    Fnt *normal_fonts = drw->fonts;
    const char *result_fonts[] = {
      "Iosevka Medium:style:medium:size=16"
    };
    finder_result_font = drw_fontset_create(drw, result_fonts,
                                            LENGTH(result_fonts));
    drw->fonts = normal_fonts;
  }
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
     /* Keep the unplayed portion darker than the light-green progress fill. */
     drw_clr_create(drw, &mpris_scroll_bg_clr, "#A6DA95");
   drw_clr_create(drw, &mpris_progress_clr, "#B8E9B4");
   drw_clr_create(drw, &mpris_volume_fill_clr, "#FFFFFF");
   drw_clr_create(drw, &mpris_volume_empty_clr, "#777777");
   drw_clr_create(drw, &notify_bg, "#1E1D2D");
    drw_clr_create(drw, &notify_fg, "#FFFFFF");
    drw_clr_create(drw, &notify_body, "#CDD6F4");
    drw_clr_create(drw, &finder_text_clr, finder_text);
  {
    Clr control, control_hover, action_text;
    drw_clr_create(drw, &control, "#363449");
    drw_clr_create(drw, &control_hover, "#514B70");
    /* Action labels sit between the body text and the dark notification
     * background; hovering them raises the contrast without changing the
     * button background. */
    drw_clr_create(drw, &action_text, "#AEB8D6");
    notify_control_scheme[ColFg] = notify_fg;
    notify_control_scheme[ColBg] = control;
    notify_control_scheme[ColBorder] = control;
    notify_control_hover_scheme[ColFg] = notify_fg;
    notify_control_hover_scheme[ColBg] = control_hover;
    notify_control_hover_scheme[ColBorder] = control_hover;

    notify_action_scheme[ColFg] = action_text;
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
  drw_clr_create(drw, &notify_summary_dim_scheme[ColFg], "#B0B9D2");
  drw_clr_create(drw, &notify_summary_dim_scheme[ColBg], "#1E1D2D");
  drw_clr_create(drw, &notify_summary_dim_scheme[ColBorder], "#1E1D2D");
  drw_clr_create(drw, &notify_body_dim_scheme[ColFg], "#929CB8");
  drw_clr_create(drw, &notify_body_dim_scheme[ColBg], "#1E1D2D");
  drw_clr_create(drw, &notify_body_dim_scheme[ColBorder], "#1E1D2D");
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

static int hasurgentclients(void) {
  Monitor *m;
  Client *c;

  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      if (c->isurgent)
        return 1;
  return 0;
}

static void demandattention(Client *c) {
  Arg a;

  if (!c)
    return;
  if (!c->isurgent)
    seturgent(c, 1);

  XSetWindowBorder(dpy, c->win,
                   urgentflash ? scheme[SchemeSel][ColBorder].pixel
                               : scheme[SchemeNorm][ColBorder].pixel);

  /* Show the client's tag(s), but deliberately leave the focused client
   * unchanged.  The user can focus the requesting client when ready. */
  a.ui = c->tags & TAGMASK;
  if (a.ui)
    view(&a);
  drawbars();
}

static void updateurgentborders(void) {
  Monitor *m;
  Client *c;

  for (m = mons; m; m = m->next)
    for (c = m->clients; c; c = c->next)
      if (c->isurgent)
        XSetWindowBorder(dpy, c->win,
                         urgentflash ? scheme[SchemeSel][ColBorder].pixel
                                     : scheme[SchemeNorm][ColBorder].pixel);
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
                              ExposureMask | PointerMotionMask | ButtonReleaseMask |
                                           EnterWindowMask | LeaveWindowMask};

  XClassHint ch = {"dwm", "dwm"};
  XClassHint marker_ch = {"dwm-mpris-volume-marker",
                          "dwm-mpris-volume-marker"};
  XClassHint finder_marker_ch = {"dwm-finder-marker", "dwm-finder-marker"};
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
    {
      XSetWindowAttributes cwa = {0};
      unsigned long cmask = CWOverrideRedirect | CWEventMask;
      int depth = DefaultDepth(dpy, screen);
      Visual *visual = DefaultVisual(dpy, screen);
      if (finder_argb_visual) {
        cwa.background_pixel = 0;
        cwa.border_pixel = 0;
        cwa.colormap = finder_argb_colormap;
        cmask |= CWColormap | CWBackPixel | CWBorderPixel;
        depth = finder_argb_depth;
        visual = finder_argb_visual;
      } else {
        cwa.background_pixmap = ParentRelative;
        cmask |= CWBackPixmap;
      }
      cwa.override_redirect = True;
      cwa.event_mask = wa.event_mask;
      if (finder_argb_visual)
        finder_argb_create_failed = 0;
      if (finder_argb_visual)
        XSetErrorHandler(finder_argb_error);
      m->barcenterwin = XCreateWindow(dpy, root, m->wx, m->by, 1, bh, 0,
                                      depth, InputOutput, visual, cmask,
                                      &cwa);
      XSync(dpy, False);
      if (finder_argb_visual)
        XSetErrorHandler(xerror);
      if (finder_argb_create_failed && finder_argb_visual) {
        finder_argb_visual = NULL;
        finder_argb_depth = 0;
        if (finder_argb_colormap) {
          XFreeColormap(dpy, finder_argb_colormap);
          finder_argb_colormap = None;
        }
        cwa = wa;
        cmask = CWOverrideRedirect | CWBackPixmap | CWEventMask;
        m->barcenterwin = XCreateWindow(dpy, root, m->wx, m->by, 1, bh, 0,
                                        DefaultDepth(dpy, screen), InputOutput,
                                        DefaultVisual(dpy, screen), cmask, &cwa);
      }
    }
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
    {
      XSetWindowAttributes mwa = {
        .override_redirect = True,
        .background_pixel = mpris_volume_fill_clr.pixel,
        .border_pixel = 0,
        .event_mask = ButtonPressMask | ButtonReleaseMask |
                      PointerMotionMask | EnterWindowMask | LeaveWindowMask
      };
      m->mpris_volume_markerwin = XCreateWindow(
          dpy, root, 0, 0, 24, 16, 0, DefaultDepth(dpy, screen),
          CopyFromParent, DefaultVisual(dpy, screen),
          CWOverrideRedirect | CWBackPixel | CWBorderPixel | CWEventMask,
          &mwa);
      XSetClassHint(dpy, m->mpris_volume_markerwin, &marker_ch);
      XStoreName(dpy, m->mpris_volume_markerwin, "dwm-mpris-volume-marker");
      XUnmapWindow(dpy, m->mpris_volume_markerwin);
    }
    /* Keep Finder's selection indicator in its own fixed native X11 window.
     * It is 300x38 pixels and pointer motion never changes the selection. */
    {
      XSetWindowAttributes fwa = {
        .override_redirect = True,
        .background_pixel = scheme[SchemeTitle][ColFg].pixel,
        .border_pixel = 0,
        .event_mask = 0
      };
      m->finder_markerwin = XCreateWindow(
          dpy, root, 0, 0, 300, 38, 0, DefaultDepth(dpy, screen),
          CopyFromParent, DefaultVisual(dpy, screen),
          CWOverrideRedirect | CWBackPixel | CWBorderPixel | CWEventMask,
          &fwa);
      XSetClassHint(dpy, m->finder_markerwin, &finder_marker_ch);
      XStoreName(dpy, m->finder_markerwin, "dwm-finder-marker");
      XUnmapWindow(dpy, m->finder_markerwin);
    }
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
  finder_load_recent();
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
