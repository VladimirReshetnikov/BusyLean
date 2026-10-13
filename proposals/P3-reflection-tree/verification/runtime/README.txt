Lean runtime and verification provenance
========================================

Compiler used for the recorded checks:
  Lean 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release
Official distribution:
  https://github.com/leanprover/lean4/releases/tag/v4.19.0
  https://github.com/leanprover/lean4/releases/download/v4.19.0/lean-4.19.0-linux.tar.zst

The original compiler and kernel libraries were not modified. The normal
proof modules need only the pinned standard Init library. External compiled
dependency auditing additionally uses Lean.Environment and Lean.Util.FoldConsts,
both included in a normal Lean installation. No Mathlib download is needed.

The source archive contains no compiler or helper binaries.
runtime_metadata.json records original executable/shared-library SHA-256
hashes, compiler version, platform details, and preliminary smoke checks.
The authoritative final package checks are in ../results.json.

Container-only compatibility helper
-----------------------------------
The checking container exposes an outer procfs inside a local PID namespace.
Lean 4.19 locates itself through /proc/<getpid()>/exe, which then refers to the
wrong process. proc_self_compat.c redirects exactly this own-process pathname
to /proc/self/exe and leaves all other libc readlink operations unchanged.
It changes executable-location discovery only, not proof elaboration or kernel
checking. The recorded checks inherited this helper through LD_PRELOAD.

An ordinary Lean installation does not need the helper. From the package root:
  python3 verification/verify.py --lean /path/to/lean

Only if this particular Linux PID/procfs mismatch occurs, build and use it:
  gcc -shared -fPIC -O2 -Wall -Wextra -o /tmp/proc_self_compat.so \
    verification/runtime/proc_self_compat.c -ldl
  LD_PRELOAD=/tmp/proc_self_compat.so \
    python3 verification/verify.py --lean /path/to/lean

The verifier inherits the caller's environment but never installs, requires,
or enables the helper itself. Its fresh temporary object directory prevents
reuse of previous project builds. Source files are hashed before checking and
checked for changes after the run.

All timings are measurements on this machine and depend on hardware and load.
The verifier enforces the adapted 15-second total definition budget and the
60-second total proof/check/audit budget on each rerun. It never evaluates
either contender; executable baseline samples stop at depth 4.
