#!/usr/bin/env bash
# Optional Linux compatibility adapter for this execution environment only.
# Normal Lean installations do not need this script.
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 /absolute/path/to/lean-4.19.0-linux" >&2
  exit 2
fi

toolchain_dir=$(cd "$1" && pwd)
script_dir=$(cd "$(dirname "$0")" && pwd)
gcc -O2 -I"$toolchain_dir/include" "$script_dir/lean_launcher.c" \
  -L"$toolchain_dir/lib/lean" -Wl,-rpath,'$ORIGIN/../lib/lean' \
  -Wl,--export-dynamic -lleanshared -o "$toolchain_dir/bin/lean-compat"
"$toolchain_dir/bin/lean-compat" --version
