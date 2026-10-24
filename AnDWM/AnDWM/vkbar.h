/* Vulkan bar renderer backend.  The Xlib/Xft/XRender renderer remains in
 * drw.c; this interface is deliberately independent so both backends can
 * coexist during the migration. */
#ifndef VKBAR_H
#define VKBAR_H

#include <X11/Xlib.h>
#include <vulkan/vulkan.h>

typedef struct VkBar VkBar;

typedef struct {
  unsigned int width;
  unsigned int height;
  unsigned int frames_in_flight;
} VkBarConfig;

VkBar *vkbar_create(Display *display, Window window, const VkBarConfig *config);
void vkbar_destroy(VkBar *bar);
int vkbar_resize(VkBar *bar, unsigned int width, unsigned int height);
int vkbar_begin_frame(VkBar *bar, VkCommandBuffer *command_buffer);
int vkbar_end_frame(VkBar *bar, VkCommandBuffer command_buffer);

#endif
