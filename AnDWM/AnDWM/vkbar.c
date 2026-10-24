#define VK_USE_PLATFORM_XLIB_KHR

#include "vkbar.h"

#include <stdlib.h>
#include <string.h>

struct VkBar {
  Display *display;
  Window window;
  VkInstance instance;
  VkSurfaceKHR surface;
  VkPhysicalDevice physical_device;
  VkDevice device;
  VkQueue queue;
  uint32_t queue_family;
  VkCommandPool command_pool;
  VkCommandBuffer command_buffer;
  VkSemaphore image_available;
  VkSemaphore render_finished;
  VkFence in_flight;
  VkBarConfig config;
  int ready;
};

static void vkbar_destroy_handles(VkBar *bar)
{
  if (!bar)
    return;
  if (bar->device != VK_NULL_HANDLE)
    vkDeviceWaitIdle(bar->device);
  if (bar->in_flight != VK_NULL_HANDLE)
    vkDestroyFence(bar->device, bar->in_flight, NULL);
  if (bar->render_finished != VK_NULL_HANDLE)
    vkDestroySemaphore(bar->device, bar->render_finished, NULL);
  if (bar->image_available != VK_NULL_HANDLE)
    vkDestroySemaphore(bar->device, bar->image_available, NULL);
  if (bar->command_pool != VK_NULL_HANDLE)
    vkDestroyCommandPool(bar->device, bar->command_pool, NULL);
  if (bar->device != VK_NULL_HANDLE)
    vkDestroyDevice(bar->device, NULL);
  if (bar->surface != VK_NULL_HANDLE)
    vkDestroySurfaceKHR(bar->instance, bar->surface, NULL);
  if (bar->instance != VK_NULL_HANDLE)
    vkDestroyInstance(bar->instance, NULL);
}

static int vkbar_pick_device(VkBar *bar)
{
  uint32_t count = 0;
  VkPhysicalDevice *devices;

  if (vkEnumeratePhysicalDevices(bar->instance, &count, NULL) != VK_SUCCESS ||
      !count)
    return 0;
  devices = calloc(count, sizeof(*devices));
  if (!devices)
    return 0;
  if (vkEnumeratePhysicalDevices(bar->instance, &count, devices) != VK_SUCCESS) {
    free(devices);
    return 0;
  }
  for (uint32_t i = 0; i < count; i++) {
    uint32_t families = 0;
    vkGetPhysicalDeviceQueueFamilyProperties(devices[i], &families, NULL);
    if (!families)
      continue;
    VkQueueFamilyProperties *props = calloc(families, sizeof(*props));
    if (!props)
      continue;
    vkGetPhysicalDeviceQueueFamilyProperties(devices[i], &families, props);
    for (uint32_t q = 0; q < families; q++) {
      VkBool32 present = VK_FALSE;
      vkGetPhysicalDeviceSurfaceSupportKHR(devices[i], q, bar->surface,
                                           &present);
      if ((props[q].queueFlags & VK_QUEUE_GRAPHICS_BIT) && present) {
        bar->physical_device = devices[i];
        bar->queue_family = q;
        free(props);
        free(devices);
        return 1;
      }
    }
    free(props);
  }
  free(devices);
  return 0;
}

VkBar *vkbar_create(Display *display, Window window, const VkBarConfig *config)
{
  VkBar *bar;
  VkApplicationInfo app = {
    .sType = VK_STRUCTURE_TYPE_APPLICATION_INFO,
    .pApplicationName = "AnDWM Vulkan bar",
    .applicationVersion = VK_MAKE_VERSION(1, 0, 0),
    .pEngineName = "AnDWM",
    .engineVersion = VK_MAKE_VERSION(1, 0, 0),
    .apiVersion = VK_API_VERSION_1_0,
  };
  const char *extensions[] = {
    VK_KHR_SURFACE_EXTENSION_NAME,
    VK_KHR_XLIB_SURFACE_EXTENSION_NAME,
  };
  VkInstanceCreateInfo instance_info = {
    .sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO,
    .pApplicationInfo = &app,
    .enabledExtensionCount = 2,
    .ppEnabledExtensionNames = extensions,
  };

  if (!display || !window)
    return NULL;
  bar = calloc(1, sizeof(*bar));
  if (!bar)
    return NULL;
  bar->display = display;
  bar->window = window;
  bar->config = config ? *config : (VkBarConfig){ 1, 1, 2 };
  if (vkCreateInstance(&instance_info, NULL, &bar->instance) != VK_SUCCESS)
    goto fail;
  VkXlibSurfaceCreateInfoKHR surface_info = {
    .sType = VK_STRUCTURE_TYPE_XLIB_SURFACE_CREATE_INFO_KHR,
    .dpy = display,
    .window = window,
  };
  if (vkCreateXlibSurfaceKHR(bar->instance, &surface_info, NULL,
                             &bar->surface) != VK_SUCCESS)
    goto fail;
  if (!vkbar_pick_device(bar))
    goto fail;

  float priority = 1.0f;
  VkDeviceQueueCreateInfo queue_info = {
    .sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO,
    .queueFamilyIndex = bar->queue_family,
    .queueCount = 1,
    .pQueuePriorities = &priority,
  };
  const char *device_extensions[] = { VK_KHR_SWAPCHAIN_EXTENSION_NAME };
  VkDeviceCreateInfo device_info = {
    .sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO,
    .queueCreateInfoCount = 1,
    .pQueueCreateInfos = &queue_info,
    .enabledExtensionCount = 1,
    .ppEnabledExtensionNames = device_extensions,
  };
  if (vkCreateDevice(bar->physical_device, &device_info, NULL,
                     &bar->device) != VK_SUCCESS)
    goto fail;
  vkGetDeviceQueue(bar->device, bar->queue_family, 0, &bar->queue);

  VkCommandPoolCreateInfo pool_info = {
    .sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO,
    .flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT,
    .queueFamilyIndex = bar->queue_family,
  };
  if (vkCreateCommandPool(bar->device, &pool_info, NULL,
                          &bar->command_pool) != VK_SUCCESS)
    goto fail;
  VkCommandBufferAllocateInfo buffer_info = {
    .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO,
    .commandPool = bar->command_pool,
    .level = VK_COMMAND_BUFFER_LEVEL_PRIMARY,
    .commandBufferCount = 1,
  };
  if (vkAllocateCommandBuffers(bar->device, &buffer_info,
                               &bar->command_buffer) != VK_SUCCESS)
    goto fail;
  VkSemaphoreCreateInfo semaphore_info = {
    .sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO,
  };
  if (vkCreateSemaphore(bar->device, &semaphore_info, NULL,
                        &bar->image_available) != VK_SUCCESS ||
      vkCreateSemaphore(bar->device, &semaphore_info, NULL,
                        &bar->render_finished) != VK_SUCCESS)
    goto fail;
  VkFenceCreateInfo fence_info = {
    .sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO,
    .flags = VK_FENCE_CREATE_SIGNALED_BIT,
  };
  if (vkCreateFence(bar->device, &fence_info, NULL, &bar->in_flight) != VK_SUCCESS)
    goto fail;
  bar->ready = 1;
  return bar;

fail:
  vkbar_destroy_handles(bar);
  free(bar);
  return NULL;
}

void vkbar_destroy(VkBar *bar)
{
  if (!bar)
    return;
  vkbar_destroy_handles(bar);
  free(bar);
}

int vkbar_resize(VkBar *bar, unsigned int width, unsigned int height)
{
  if (!bar || !bar->ready || !width || !height)
    return 0;
  bar->config.width = width;
  bar->config.height = height;
  /* Swapchain creation/recreation is intentionally isolated for the next
   * migration step; the legacy XRender path remains the visible fallback. */
  return 1;
}

int vkbar_begin_frame(VkBar *bar, VkCommandBuffer *command_buffer)
{
  VkCommandBufferBeginInfo begin = {
    .sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO,
    .flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT,
  };
  if (!bar || !bar->ready || !command_buffer ||
      vkWaitForFences(bar->device, 1, &bar->in_flight, VK_TRUE, UINT64_MAX) != VK_SUCCESS ||
      vkResetFences(bar->device, 1, &bar->in_flight) != VK_SUCCESS ||
      vkResetCommandBuffer(bar->command_buffer, 0) != VK_SUCCESS ||
      vkBeginCommandBuffer(bar->command_buffer, &begin) != VK_SUCCESS)
    return 0;
  *command_buffer = bar->command_buffer;
  return 1;
}

int vkbar_end_frame(VkBar *bar, VkCommandBuffer command_buffer)
{
  VkSubmitInfo submit = {
    .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO,
    .commandBufferCount = 1,
    .pCommandBuffers = &command_buffer,
  };
  if (!bar || !bar->ready || command_buffer != bar->command_buffer ||
      vkEndCommandBuffer(command_buffer) != VK_SUCCESS ||
      vkQueueSubmit(bar->queue, 1, &submit, bar->in_flight) != VK_SUCCESS)
    return 0;
  return 1;
}
