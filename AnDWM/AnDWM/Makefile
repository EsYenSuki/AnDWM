# dwm - dynamic window manager
# See LICENSE file for copyright and license details.
include config.mk

SRC = drw.c dwm.c util.c
OBJ = ${SRC:.c=.o}

all: dwm cgwrite

.c.o:
	${CC} -c ${CFLAGS} $<

${OBJ}: config.h config.mk

config.h:
	cp config.def.h $@

dwm: ${OBJ}
	${CC} -o $@ ${OBJ} ${LDFLAGS}

cgwrite: cgwrite.c
	$(CC) $(CFLAGS) -o cgwrite cgwrite.c

clean:
	rm -f dwm cgwrite cgwrite.o ${OBJ} dwm-${VERSION}.tar.gz config.h

dist: clean
	mkdir -p dwm-${VERSION}
	cp -R LICENSE Makefile README config.def.h config.mk\
		dwm.1 drw.h util.h ${SRC} dwm.png transient.c dwm-${VERSION}
	tar -cf dwm-${VERSION}.tar dwm-${VERSION}
	gzip dwm-${VERSION}.tar
	rm -rf dwm-${VERSION}

install: all
	mkdir -p ${DESTDIR}${PREFIX}/bin
	cp -f dwm ${DESTDIR}${PREFIX}/bin/AnDWM
	chmod 755 ${DESTDIR}${PREFIX}/bin/AnDWM
	cp -f cgwrite ${DESTDIR}${PREFIX}/bin/cgwrite
	chown root:root ${DESTDIR}${PREFIX}/bin/cgwrite
	chmod 4755 ${DESTDIR}${PREFIX}/bin/cgwrite
	mkdir -p ${DESTDIR}${MANPREFIX}/man1
	sed "s/VERSION/${VERSION}/g" < dwm.1 > ${DESTDIR}${MANPREFIX}/man1/dwm.1
	chmod 644 ${DESTDIR}${MANPREFIX}/man1/dwm.1

uninstall:
	rm -f ${DESTDIR}${PREFIX}/bin/AnDWM\
		${DESTDIR}${PREFIX}/bin/cgwrite\
		${DESTDIR}${MANPREFIX}/man1/dwm.1

# bridge: pipn native messaging host
BRIDGE_SRC  = ../scripts/pipn_bridge.c
BRIDGE_OUT  = $(HOME)/.config/AnDWM/scripts/bin/pipn-nativemessage
NATIVEMSG   = $(HOME)/Projects/lib-native-messaging
NATIVEMSG_H = $(NATIVEMSG)/include

pipn-bridge: $(BRIDGE_OUT)

$(BRIDGE_OUT): $(BRIDGE_SRC)
	$(CC) -o $@ $(BRIDGE_SRC) $(NATIVEMSG)/src/nativemsg.c \
		-lpthread -I$(NATIVEMSG_H) $(CFLAGS)

.PHONY: all clean dist install uninstall pipn-bridge
