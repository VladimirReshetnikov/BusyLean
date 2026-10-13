#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/* Lean 4.19 uses /proc/<getpid()>/exe.  In this container getpid() uses
 * the local PID namespace while the mounted procfs uses the host namespace.
 * Resolve only the current process's executable through /proc/self/exe.
 * No compiler, elaborator, kernel, file contents, or other path is modified.
 */
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char current[64];
    snprintf(current, sizeof current, "/proc/%d/exe", (int)getpid());
    return original(strcmp(path, current) == 0 ? "/proc/self/exe" : path,
                    buf, size);
}
