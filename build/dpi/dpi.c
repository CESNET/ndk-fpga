#define DPI_STR_HELPER(x) #x
#define DPI_STR(x) DPI_STR_HELPER(x)

#include <stdio.h>

void dpiregister(const char *name, int (*main)(int argc, char *argv[]));

int main(int argc, char *argv[]);
static const char *dpi_tool_name = DPI_STR(DPI_TOOL_NAME);

__attribute__((visibility("default"))) int DPI_TOOL_NAME(int argc, char *argv[])
{
    return main(argc, argv);
}

__attribute__((constructor)) __attribute__((visibility("default"))) void __dpiregisterself() {
    dpiregister(dpi_tool_name, DPI_TOOL_NAME);
}

void __init() {
    dpiregister(dpi_tool_name, DPI_TOOL_NAME);
}
