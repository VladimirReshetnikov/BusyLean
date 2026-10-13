# Validation runtime note

The mathematical sources require an ordinary Lean **4.19.0** installation and
its standard library. They do not require Mathlib, a modified kernel, or the
compatibility launcher included in this directory.

The validation host did not expose the running application's executable path
through `/proc/<pid>/exe`, which the release launcher normally uses to locate
the Lean installation. For this host, `lean_launcher.c` supplies the already
known executable path obtained from `argv[0]` and calls the release library's
`lean_main`. It was linked against the unmodified Lean 4.19.0 release libraries.
No elaborator, kernel, mathematical definition, or runtime library was edited.
Other path reads retain the normal operating-system access checks.

The source is included to make this environment adaptation reviewable. It is
not part of the contest entry or of the Lean dependency graph, and ordinary
Lean installations should use their normal executable. The measured version
was:

```
Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)
```

See `validation/build_report.json` for the observed platform, individual module
timings, source hashes, axiom audit, dependency audit, and independent finite
source-semantics regression results. Timings use a fresh temporary project
with every delivered mathematical source rebuilt; the installed Lean standard
library is reused in its normal compiled form.
