/* See LICENSE file for copyright and license details. */

#include <X11/XF86keysym.h>

/* appearance */
static const unsigned int borderpx  = 2;        /* border pixel of windows */
static const unsigned int default_border = 0;   /* to switch back to default border after dynamic border resizing via keybinds */
static const unsigned int snap      = 14;       /* snap pixel */
static const unsigned int gappih    = 14;       /* horiz inner gap between windows */
static const unsigned int gappiv    = 14;       /* vert inner gap between windows */
static const unsigned int gappoh    = 14;       /* horiz outer gap between windows and screen edge */
static const unsigned int gappov    = 14;       /* vert outer gap between windows and screen edge */
static const int smartgaps          = 0;        /* 1 means no outer gap when there is only one window */
static const unsigned int systraypinning = 0;   /* 0: sloppy systray follows selected monitor, >0: pin systray to monitor X */
static const unsigned int systrayspacing = 6;   /* systray spacing */
static const int systraypinningfailfirst = 1;   /* 1: if pinning fails,display systray on the 1st monitor,False: display systray on last monitor*/
static const int showsystray        = 1;        /* 0 means no systray */
static const int showbar            = 1;        /* 0 means no bar */
static const int showtab            = showtab_auto;
static const int toptab             = 1;        /* 0 means bottom tab */
static const int floatbar           = 1;        /* 1 means the bar will float(don't have padding),0 means the bar have padding */
static const int topbar             = 1;        /* 0 means bottom bar */
static const int horizpadbar        = 6;
static const int vertpadbar         = 12;
static const int bargap             = 10;   /* space between the bars */
static const int clockpad           = 24;   /* space before/after the clock text */
static const int finder_width       = 300;  /* center finder width */
static const int finder_rows        = 10;   /* number of applications shown */
static const char *finder_app_dirs[] = {
    "~/.local/share/applications",
    "/usr/local/share/applications",
    "/usr/share/applications",
    "~/.local/share/flatpak/exports/share/applications",
    "/var/lib/flatpak/exports/share/applications",
    NULL,
};
static const int notification_gl    = 1;   /* 1: use OpenGL GPU acceleration for notification and history, 0: use XRender fallback */
static const char *notification_ignore_apps[] = {
    NULL,
};
static const char *notification_ignore_summaries[] = {
    NULL,
};
static const char *notification_ignore_bodies[] = {
    "You have unseen notifications.",
    NULL,
};
static const int kblayoutpad        = 17;   /* padding inside the keyboard layout bar */
static const int vertpadtab         = 35;
static const int horizpadtabi       = 16;
static const int horizpadtabo       = 16;
static const int scalepreview       = 7;
static const int tag_preview        = 1;        /* 1 means enable, 0 is off */
static const int tag_preview_x_offset = 15;
static const int tag_preview_y_offset = 15;
static const int colorfultag        = 1;        /* 0 means use SchemeSel for selected non vacant tag */
static const char buttonbar[]       = "";
static const char *upvol[]   = { "/usr/bin/pactl", "set-sink-volume", "0", "+5%",     NULL };
static const char *downvol[] = { "/usr/bin/pactl", "set-sink-volume", "0", "-5%",     NULL };
static const char *mutevol[] = { "/usr/bin/pactl", "set-sink-mute",   "0", "toggle",  NULL };
static const char *light_up[] = {"/usr/bin/light", "-A", "5", NULL};
static const char *light_down[] = {"/usr/bin/light", "-U", "5", NULL};
static const int new_window_attach_on_end = 0; /*  1 means the new window will attach on the end; 0 means the new window will attach on the front,default is front */
#define ICONSIZE 19   /* icon size */
#define ICONSPACING 8 /* space between icon and title */

/* sidebar app list */
static const int enablesidebar = 1;       /* 1 = enabled, 0 = disabled */
static const int sidebaretrigger = 4;     /* px from left edge to auto-show */

static const char *fonts[] = {
    "Iosevka Medium:style:medium:size=11.5",                      // Latin / main compact font
    "Hack Nerd Font Mono:style:Bold:size=19",
    "Sarasa Gothic SC:style:Regular:size=10",
    "Sarasa Gothic TC:style:Regular:size=10",           // Chinese Traditional
    "Sarasa Gothic J:style:Regular:size=10",           // Japanese
    "Sarasa Gothic K:style:Regular:size=10",           // Korean
    "Noto Sans Thai:style:Regular:size=11.5",            // Thai
    "Noto Sans Arabic:style:Regular:size=11.5",          // Arabic
    "Noto Sans Devanagari:style:Regular:size=11.5",       // Hindi/Indic
};

static const char *togglekb[]  = { "setxkbmap", "-layout", "us,th", "-option", "grp:win_space_toggle", NULL };

// theme
#include "themes/catppuccin.h"

static const char *colors[][3]      = {
    /*                     fg       bg      border */
    [SchemeNorm]       = { gray3,   black,  gray2 },
    [SchemeSel]        = { gray4,   blue,   blue  },
    [SchemeTitle]      = { white,   black,  black }, // active window title
    [TabSel]           = { blue,    gray2,  black },
    [TabNorm]          = { gray3,   black,  black },
    [SchemeTag]        = { gray3,   black,  black },
    [SchemeTag1]       = { blue,    black,  black },
    [SchemeTag2]       = { red,     black,  black },
    [SchemeTag3]       = { orange,  black,  black },
    [SchemeTag4]       = { green,   black,  black },
    [SchemeTag5]       = { pink,    black,  black },
    [SchemeTag6]       = { purple,  black,  black },
    [SchemeTag7]       = { brown,   black,  black },
    [SchemeTag8]       = { cyan,    black,  black },
    [SchemeLayout]     = { green,   black,  black },
    [SchemeBtnPrev]    = { green,   black,  black },
    [SchemeBtnNext]    = { yellow,  black,  black },
    [SchemeBtnClose]   = { red,     black,  black },
};

/* tagging */
/* static char *tags[] = {"", "", "", "", ""}; */
static char *tags[] = {"", "", "", "", ""};

static const char* eww[] = { "eww", "open" , "eww", NULL };

static const Launcher launchers[] = {
    /* command     name to display */
    { eww,         "" },
};

static const int tagschemes[] = {
    SchemeTag1, SchemeTag2, SchemeTag3, SchemeTag4, SchemeTag5,
    SchemeTag6, SchemeTag7, SchemeTag8
};

static const unsigned int ulinepad      = 5; /* horizontal padding between the underline and tag */
static const unsigned int ulinestroke   = 2; /* thickness / height of the underline */
static const unsigned int ulinevoffset  = 0; /* how far above the bottom of the bar the line should appear */
static const int ulineall               = 0; /* 1 to show underline on all tags, 0 for just the active ones */

static const Rule rules[] = {
    /* xprop(1):
     *	WM_CLASS(STRING) = instance, class
     *	WM_NAME(STRING) = title
     */
    /* class      instance    title       tags mask     iscentered   isfloating   isontop   monitor */
    { "Gimp",     NULL,       NULL,       0,            0,           1,           0,        -1 },
    { "Firefox",  NULL,       NULL,       1 << 8,       0,           0,           0,        -1 },
    { "eww",      NULL,       NULL,       0,            0,           1,           0,        -1 },
    { "spectacle",NULL,       NULL,       0,            1,           1,           10,       -1 },
    { "wired",    NULL,       NULL,       0,            0,           1,           10,       -1 },
    { "highlight-pointer",    NULL,       NULL,       0,            0,           1,           99,       -1 },
    { "mpv",      NULL,       NULL,       0,            1,           1,           1,        -1 },
    { "MainKt",      NULL,       NULL,       1,            1,           1,           1,        -1 }

};

/* layout(s) */
static const float mfact     = 0.50; /* factor of master area size [0.05..0.95] */
static const int nmaster     = 1;    /* number of clients in master area */
static const int resizehints = 0;    /* 1 means respect size hints in tiled resizals */
static const int lockfullscreen = 1; /* 1 will force focus on the fullscreen window */

static const char *const transparent_fullscreen_classes[] = {
    "kitty",
    "mpv",
    NULL,  /* sentinel */
};

#define FORCE_VSPLIT 1  /* nrowgrid layout: force two clients to always split vertically */
#include "functions.h"


static const Layout layouts[] = {
    /* symbol     arrange function */
    { "[]=",      spiral },    /* first entry is default */    
    { ":::",      gaplessgrid },
    { "[\\]",     dwindle },
    { "[M]",      monocle },
    { "[@]",      tile },
    { "H[]",      deck },
    { "TTT",      bstack },
    { "===",      bstackhoriz },
    { "HHH",      grid },
    { "###",      nrowgrid },
    { "---",      horizgrid },
    { "|M|",      centeredmaster },
    { ">M>",      centeredfloatingmaster },
    { "><>",      NULL },    /* no layout function means floating behavior */
    { NULL,       NULL },
};

/* key definitions */
#define MODKEY Mod4Mask
#define TAGKEYS(KEY,TAG) \
    { MODKEY,                       KEY,      view,           {.ui = 1 << TAG} }, \
    { MODKEY|ControlMask,           KEY,      toggleview,     {.ui = 1 << TAG} }, \
    { MODKEY|ShiftMask,             KEY,      tag,            {.ui = 1 << TAG} }, \
    { MODKEY|ControlMask|ShiftMask, KEY,      toggletag,      {.ui = 1 << TAG} },

/* helper for spawning shell commands in the pre dwm-5.0 fashion */
#define SHCMD(cmd) { .v = (const char*[]){ "/bin/sh", "-c", cmd, NULL } }

/* commands */

static const Key keys[] = {
    /* modifier                         key         function        argument */

    // brightness and audio 
    {0,             XF86XK_AudioLowerVolume,    spawn, {.v = downvol}},
	{0,             XF86XK_AudioMute,           spawn,    {.v = mutevol }},
	{0,             XF86XK_AudioRaiseVolume,    spawn, {.v = upvol}},
	{0,				XF86XK_MonBrightnessUp,     spawn,	{.v = light_up}},
	{0,				XF86XK_MonBrightnessDown,   spawn,	{.v = light_down}},

    // screenshot fullscreen and cropped
    { MODKEY|ShiftMask,     		    XK_s,       spawn,          SHCMD("/home/Hi/.config/AnDWM/scripts/bin/znap") },
    { MODKEY,                           XK_s,       finder_ocr,     {0} },
    { MODKEY,                           XK_a,       finder,         {0} },
    { MODKEY,                           XK_Return,  spawn,          SHCMD("kitty") },
    { MODKEY,                           XK_e,       spawn,          SHCMD("nemo") },
    { MODKEY,                           XK_b,       spawn,          SHCMD("MOZ_X11_EGL=1 MOZ_USE_XINPUT2=1 zen-browser") },
    { MODKEY,                           XK_v,       spawn,          SHCMD("/home/Hi/.config/AnDWM/scripts/bin/clyp") },
    { MODKEY,                           XK_period,  spawn,          SHCMD("rofi -modi \"emoji:rofimoji --action copy --hidden-descriptions\" -show emoji -theme /home/Hi/.config/AnDWM/rofi/moji.rasi") },
    { MODKEY|ShiftMask,                 XK_c,       spawn,          SHCMD("picom cursor toggle") },

    // zoom keybind
    { MODKEY,                           XK_equal,   spawn,          SHCMD("picom-zoom +0.2") },
    { MODKEY,                           XK_minus,   spawn,          SHCMD("picom-zoom -0.2") },
    { MODKEY,                           XK_BackSpace,   spawn,      SHCMD("picom-zoom 1") },
    // extra zoom
    { MODKEY|ControlMask,               XK_equal,   spawn,          SHCMD("picom-zoom +0.4") },
    { MODKEY|ControlMask,               XK_minus,   spawn,          SHCMD("picom-zoom -0.4") },


    // toggle stuff
    { MODKEY,                           XK_space,   spawn,          {.v = togglekb } },
    { MODKEY|ControlMask,               XK_b,       togglebar,      {0} },
    { MODKEY|ControlMask,               XK_t,       togglegaps,     {0} },
    { MODKEY,                           XK_w,       togglefloating, {0} },
    { MODKEY,                           XK_f,       togglefullscr,  {0} },
    { MODKEY|ShiftMask,                 XK_b,       togglestickyclient,   {0} },

    { MODKEY|ShiftMask,                 XK_w,       tabmode,        { -1 } },
    { MODKEY,                           XK_j,       focusstack,     {.i = +1 } },
    { MODKEY,                           XK_k,       focusstack,     {.i = -1 } },
    { MODKEY,                           XK_i,       incnmaster,     {.i = +1 } },
    { MODKEY,                           XK_d,       incnmaster,     {.i = -1 } },

    // shift view
    { MODKEY,                           XK_Left,    shiftview,      {.i = -1 } },
    { MODKEY,                           XK_Right,   shiftview,      {.i = +1 } },

    // change m,cfact sizes 
    { MODKEY,                           XK_o,       setmfact,       {.f = -0.05} },
    { MODKEY,                           XK_p,       setmfact,       {.f = +0.05} },
    { MODKEY|ShiftMask,                 XK_o,       setcfact,       {.f = +0.25} },
    { MODKEY|ShiftMask,                 XK_p,       setcfact,       {.f = -0.25} },


    { MODKEY|ShiftMask,                 XK_j,       movestack,      {.i = +1 } },
    { MODKEY|ShiftMask,                 XK_k,       movestack,      {.i = -1 } },
    { MODKEY|ShiftMask,                 XK_Return,  zoom,           {0} },
    { MODKEY,                           XK_Tab,     view,           {0} },

    // overall gaps
    { MODKEY|ControlMask,               XK_i,       incrgaps,       {.i = +1 } },
    { MODKEY|ControlMask,               XK_d,       incrgaps,       {.i = -1 } },

    // inner gaps
    { MODKEY|ShiftMask,                 XK_i,       incrigaps,      {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_i,       incrigaps,      {.i = -1 } },

    // outer gaps
    { MODKEY|ControlMask,               XK_o,       incrogaps,      {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_o,       incrogaps,      {.i = -1 } },

    // inner+outer hori, vert gaps 
    { MODKEY|ControlMask,               XK_6,       incrihgaps,     {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_6,       incrihgaps,     {.i = -1 } },
    { MODKEY|ControlMask,               XK_7,       incrivgaps,     {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_7,       incrivgaps,     {.i = -1 } },
    { MODKEY|ControlMask,               XK_8,       incrohgaps,     {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_8,       incrohgaps,     {.i = -1 } },
    { MODKEY|ControlMask,               XK_9,       incrovgaps,     {.i = +1 } },
    { MODKEY|ControlMask|ShiftMask,     XK_9,       incrovgaps,     {.i = -1 } },

    { MODKEY|ControlMask|ShiftMask,     XK_d,       defaultgaps,    {0} },

    // layout
    { MODKEY,                           XK_t,       setlayout,      {.v = &layouts[0]} },
    { MODKEY|ShiftMask,                 XK_f,       setlayout,      {.v = &layouts[1]} },
    { MODKEY,                           XK_m,       setlayout,      {.v = &layouts[2]} },
    { MODKEY|ControlMask,               XK_g,       setlayout,      {.v = &layouts[10]} },
    { MODKEY|ControlMask|ShiftMask,     XK_t,       setlayout,      {.v = &layouts[13]} },
    { MODKEY|ShiftMask,                 XK_space,   setlayout,      {0} },
    { MODKEY|ControlMask,               XK_comma,   cyclelayout,    {.i = -1 } },
    { MODKEY|ControlMask,               XK_period,  cyclelayout,    {.i = +1 } },
    { MODKEY,                           XK_0,       view,           {.ui = ~0 } },
    { MODKEY|ShiftMask,                 XK_0,       tag,            {.ui = ~0 } },
    { MODKEY,                           XK_comma,   focusmon,       {.i = -1 } },
    { MODKEY,                           XK_period,  focusmon,       {.i = +1 } },
    { MODKEY|ShiftMask,                 XK_comma,   tagmon,         {.i = -1 } },
    { MODKEY|ShiftMask,                 XK_period,  tagmon,         {.i = +1 } },


    // kill window
    { MODKEY,                           XK_q,       killclient,     {0} },
    { MODKEY|ShiftMask,                 XK_q,       forcekillclient, {0} },


    // restart
    { MODKEY|ShiftMask,                 XK_r,       restart,           {0} },

    // hide & restore windows
    { MODKEY,                           XK_h,       togglewin,      {0} },
    { MODKEY|ShiftMask,                 XK_h,       restorewin,     {0} },


    { Mod1Mask,                         XK_Tab,     focusstack,     {.i = +1 } },
    { Mod1Mask|ShiftMask,               XK_Tab,     focusstack,     {.i = -1 } },


    TAGKEYS(                            XK_1,                       0)
    TAGKEYS(                            XK_2,                       1)
    TAGKEYS(                            XK_3,                       2)
    TAGKEYS(                            XK_4,                       3)
    TAGKEYS(                            XK_5,                       4)
    TAGKEYS(                            XK_6,                       5)
    TAGKEYS(                            XK_7,                       6)
    TAGKEYS(                            XK_8,                       7)
    TAGKEYS(                            XK_9,                       8)
};

/* button definitions */
/* click can be ClkTagBar, ClkLtSymbol, ClkStatusText, ClkWinTitle, ClkClientWin, or ClkRootWin */
static const Button buttons[] = {
    /* click                event mask      button          function        argument */
    { ClkLtSymbol,          0,              Button1,        setlayout,      {0} },
    { ClkLtSymbol,          0,              Button3,        setlayout,      {.v = &layouts[2]} },
    { ClkWinTitle,          0,              Button2,        zoom,           {0} },
    { ClkStatusText,        0,              Button2,        spawn,          SHCMD("st") },

    /* Keep movemouse? */
    /* { ClkClientWin,         MODKEY,         Button1,        movemouse,      {0} }, */

    /* placemouse options, choose which feels more natural:
    *    0 - tiled position is relative to mouse cursor
    *    1 - tiled position is relative to window center
    *    2 - mouse pointer warps to window center
    *
    * The moveorplace uses movemouse or placemouse depending on the floating state
    * of the selected client. Set up individual keybindings for the two if you want
    * to control these separately (i.e. to retain the feature to move a tiled window
    * into a floating position).
    */
    { ClkClientWin,         MODKEY,         Button1,        moveorplace,    {.i = 0} },
    { ClkClientWin,         MODKEY,         Button2,        togglefloating, {0} },
    { ClkClientWin,         MODKEY,         Button3,        resizemouse,    {0} },
    { ClkClientWin,         ControlMask,    Button1,        dragmfact,      {0} },
    { ClkClientWin,         ControlMask,    Button3,        dragcfact,      {0} },
    { ClkTagBar,            0,              Button1,        view,           {0} },
    { ClkTagBar,            0,              Button3,        toggleview,     {0} },
    { ClkTagBar,            MODKEY,         Button1,        tag,            {0} },
    { ClkTagBar,            MODKEY,         Button3,        toggletag,      {0} },
    { ClkTabBar,            0,              Button1,        focuswin,       {0} },
    { ClkTabBar,            0,              Button1,        focuswin,       {0} },
    { ClkTabPrev,           0,              Button1,        movestack,      { .i = -1 } },
    { ClkTabNext,           0,              Button1,        movestack,      { .i = +1 } },
    { ClkTabClose,          0,              Button1,        killclient,     {0} },
};
