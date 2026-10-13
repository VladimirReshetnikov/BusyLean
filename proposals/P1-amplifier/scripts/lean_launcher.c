/*
 * Lean 4.19 application-path compatibility launcher.
 * This environment does not expose /proc/<pid>/exe. Instead of querying that
 * interface, the launcher resolves its own argv[0] and supplies that known path
 * to Lean's IO.appPath. No Lean kernel, elaborator, or runtime library is edited.
 */
#include <lean/lean.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

static const char *launcher_app_path;

/* The release library binds its IO.appPath implementation internally, so the
 * adapter supplies the stored argv[0] at its libc path-query boundary. This
 * resolves only the current application's already-known pathname, and does not
 * obtain any information from protected /proc entries. Other reads use the
 * ordinary kernel interface and retain its access checks. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
    char own_path[80];
    snprintf(own_path, sizeof own_path, "/proc/%ld/exe", (long)getpid());
    if (launcher_app_path && strcmp(path, own_path) == 0) {
        size_t n = strlen(launcher_app_path);
        if (n > size) n = size;
        memcpy(buffer, launcher_app_path, n);
        return (ssize_t)n;
    }
    return syscall(SYS_readlink, path, buffer, size);
}

LEAN_EXPORT lean_obj_res lean_io_app_path(void) {
    return lean_io_result_mk_ok(lean_mk_string(launcher_app_path));
}

extern int lean_main(int argc, char **argv);

int main(int argc, char **argv) {
    static char resolved[PATH_MAX];
    if (!realpath(argv[0], resolved)) {
        perror("resolving Lean launcher path");
        return 1;
    }
    launcher_app_path = resolved;
    return lean_main(argc, argv);
}
