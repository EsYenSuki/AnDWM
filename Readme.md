# AnDWM

AnDWM is my customized dwm setup. It includes the dwm source, helper scripts,
rofi themes, wallpaper, compositor config, status bar utilities, and an
optional Ly display manager setup.

https://github.com/user-attachments/assets/a37d4c88-ccac-45ad-9f32-568b6a9bbbf5

## Supported Install

The included installer is written for Arch Linux and Arch-based systems. It uses
`pacman`, installs `yay` when needed, installs required packages, copies the
config to `~/.config/AnDWM`, builds helper utilities, installs the window
manager, and creates an XSession entry named `AnDWM`.

Read `install.sh` before running it. The script uses `sudo`, installs packages,
creates files under `/usr/share`, and can optionally install and enable Ly.

**To make workspace transition animation work** - you must install my [PICOM](https://github.com/AN-ASZ/picom) patch

## Requirements

Core requirements:

* Arch Linux or an Arch-based distro
* `sudo`
* `git`
* `base-devel`
* `xorg-server`
* `xorg-xinit`
* X11 development libraries
* `imlib2`
* `libx11`
* `libxft`
* `libxinerama`
* `libxrender`
* `libxfixes`
* `libxdamage`
* `libxcomposite`
* `fontconfig`

Runtime tools used by this config:

* `kitty`
* `picom`
* `feh`
* `rofi`
* `rofi-greenclip`
* `wired`
* `dex`
* `playerctl`
* `polkit-gnome`
* `xorg-xsetroot`
* `xorg-xrandr`
* `fish`
* `starship`
* Nerd fonts, including Iosevka or Hack

The installer handles these packages for Arch-based systems.

## Install

Clone this repository and run the installer:

```sh
git clone https://github.com/AN-ASZ/AnDWM.git
cd AnDWM
chmod +x install.sh
./install.sh
```

During installation, you can choose whether to install Ly and disable other
display managers.

After installation, reboot and select `AnDWM` from your display manager.

## What The Installer Does

`install.sh` performs these steps:

* Updates the system with `pacman -Syu`
* Installs `yay` if it is missing
* Installs required `pacman` and AUR packages
* Copies `AnDWM` to `~/.config/AnDWM`
* Installs fonts and refreshes the font cache
* Optionally installs and enables Ly
* Builds helper utilities in `~/.config/AnDWM/scripts/bin`
* Builds and installs dwm as `/usr/local/bin/AnDWM`
* Installs `cgwrite` as `/usr/local/bin/cgwrite`
* Creates `/usr/share/xsessions/AnDWM.desktop`

## Run With A Display Manager

The installer creates this XSession entry:

```ini
[Desktop Entry]
Name=AnDWM
Comment=Modern ChadWM fork
Exec=/home/YOUR_USER/.config/AnDWM/scripts/sh/run.sh
Type=Application
```

Select `AnDWM` at your login screen.

## Run With startx

You can also start the session manually:

```sh
startx ~/.config/AnDWM/scripts/sh/run.sh
```

## Manual Build

If you only want to build and install the window manager:

```sh
cd AnDWM/AnDWM
sudo make clean
sudo make install
```

This installs:

* `/usr/local/bin/AnDWM`
* `/usr/local/bin/cgwrite`
* `/usr/local/share/man/man1/dwm.1`

## Recompile After Changes

Recompile after changing the dwm source or `config.h`:

```sh
cd ~/.config/AnDWM/AnDWM
sudo make clean
sudo make install
```

Then restart the session.

## Session Startup

The session script is:

```sh
~/.config/AnDWM/scripts/sh/run.sh
```

It loads `.Xresources`, sets the wallpaper with `feh`, starts `wired`, starts
the custom bar, starts `picom`, starts `greenclip`, configures keyboard layouts,
starts the polkit agent, runs XDG autostart entries, and finally executes
`AnDWM`.

## Customization

Useful files:

* DWM config: `~/.config/AnDWM/AnDWM/config.h`
* DWM source: `~/.config/AnDWM/AnDWM/dwm.c`
* Build settings: `~/.config/AnDWM/AnDWM/config.mk`
* Startup script: `~/.config/AnDWM/scripts/sh/run.sh`
* Picom config: `~/.config/AnDWM/scripts/picom.conf`
* Rofi config: `~/.config/AnDWM/rofi/config.rasi`
* Wallpapers: `~/.config/AnDWM/Wallpaper`
* Bar themes: `~/.config/AnDWM/scripts/bar_themes`

## Notification History

AnDWM includes notification history in the center clock bar. Notifications are
kept in newest-first order, with up to ten entries retained and five entries
visible at a time. Use the mouse wheel over the history to scroll through older
notifications; scrolling uses a smooth 500 ms eased animation.

Active notifications retain their normal timeout and interaction behavior:

* Left-click notification content to activate its first action
* Right-click notification content to dismiss the current notification
* Middle-click notification content to clear active and queued notifications
  while keeping them in history

Action buttons and input fields are excluded from these content-click actions.

## Uninstall

Remove the installed binaries:

```sh
cd ~/.config/AnDWM/AnDWM
sudo make uninstall
```

Optional cleanup:

```sh
rm -rf ~/.config/AnDWM
sudo rm -f /usr/share/xsessions/AnDWM.desktop
```

## Credits

This setup is based on chadwm and dwm.

Original chadwm repository:

https://github.com/siduck/chadwm.git

Thanks to the original patch authors and maintainers of dwm, chadwm, and the
tools used by this setup.
