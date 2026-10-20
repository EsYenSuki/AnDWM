#!/bin/sh
export XDG_SESSION_TYPE=x11
export DESKTOP_SESSION=dwm
export XDG_CURRENT_DESKTOP=dwm

systemctl --user import-environment DISPLAY XAUTHORITY
dbus-update-activation-environment --systemd DISPLAY XAUTHORITY

xrdb merge ~/.Xresources


########## FOR MULTI MONITOR IN VERTICAL SETUP ############
##
##xrandr \
##  --output HDMI-1 --mode 1920x1080 --rate 100 --rotate inverted --pos 0x768 \
##  --output eDP-1 --mode 1366x768 --pos 277x0 --primary
###########################################################

########## LIVE WALLPAPER ############
#xwinwrap -ni -ov -fs -s -- \
#sh -c 'mpv --wid=$1 --loop=inf --no-audio --no-border --hwdec=auto wallpaper.mp4' _ WID
######################################

########## COMMENT THIS IF USE LIVE WALLPAPER ############
feh --bg-fill ~/.config/AnDWM/Wallpaper/Miku_plant.png
###########################################################

xset r rate 200 20 &

# Compositor
picom --config ~/.config/AnDWM/scripts/picom.conf &

# ClipBoard
greenclip daemon &

# Language Layout switch key
setxkbmap -layout us,th -option grp:win_space_toggle &

# User Authentication prompt
/usr/lib/polkit-gnome/polkit-gnome-authentication-agent-1 &

# XDG autostart (Steam, Discord, etc.)
dex -a -s ~/.config/autostart >/dev/null 2>&1 &

#taskset -c 0
taskset -c 0 ionice -c3 nice -n 19 cpulimit -l 1 -- bash -c '~/.config/AnDWM/scripts/bin/bat' > /dev/null 2>&1 &

#sudo ~/.config/AnDWM/scripts/sh/asusprofile.sh &
taskset -c 0 ionice -c3 nice -n 19 cpulimit -l 5 -- bash -c 'sudo ~/.config/AnDWM/scripts/sh/asusprofile.sh' > /dev/null 2>&1 &

# Start actual WM
exec AnDWM
