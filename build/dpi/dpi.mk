MODELSIM_PATH=$(dir $(shell which vsim))..

DPI_MAKEFILE_PATH := $(dir $(lastword $(MAKEFILE_LIST)))

DPI_TOOL_CFLAGS = -fPIC -DDPI_TOOL_NAME=$(TARGET) -fvisibility=hidden $(EXTRA_CFLAGS)
CLEAN_TARGETS = clean_dpi

INCLUDE=$(MODELSIM_PATH)/include

FLAGS=-std=c99 -fvisibility=hidden -c -g -fPIC
#FLAGS=-std=gnu99 -fvisibility=hidden -c -g -fPIC -DDPI_VERIFICATION
DLL_FLAGS=-shared -fvisibility=hidden
DLL_SUFFIX=so
QUOTE="

PLATFORM=`uname`

.PHONY: dpi_library
dpi_library: lib$(TARGET).$(DLL_SUFFIX)

$(DPI_TOOL_OBJS):
	make -C $(DPI_TOOL_DIR) EXTRA_CFLAGS="$(DPI_TOOL_CFLAGS)" OBJDIR=$(OBJDIR) $@

dpi.o: $(DPI_MAKEFILE_PATH)dpi.c
	$(CC) $(DPI_TOOL_CFLAGS) -c -o $@ $<

lib$(TARGET).$(DLL_SUFFIX): $(DPI_TOOL_OBJS) dpi.o
	$(LD) -init __dpiregisterself $(DLL_FLAGS) -o $@ $^

clean_dpi:
	rm -fR dpi.o *.$(DLL_SUFFIX)
