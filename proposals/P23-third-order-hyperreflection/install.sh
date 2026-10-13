#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 [--force] /path/to/BusyLean" >&2
  exit 2
}

force=0
if [[ ${1:-} == "--force" ]]; then
  force=1
  shift
fi
[[ $# -eq 1 ]] || usage

package_dir=$(cd "$(dirname "$0")" && pwd)
target=$(cd "$1" && pwd)
expected_head=64d31a0cf6f1aa4477a088be5554957de6e87a61
expected_toolchain=leanprover/lean4:v4.34.0

[[ -f "$target/BusyLean/Contender19.lean" ]] || {
  echo "error: target is not the expected BusyLean checkout" >&2
  exit 1
}
[[ -f "$target/BusyLean.lean" ]] || {
  echo "error: BusyLean.lean is missing" >&2
  exit 1
}
actual_toolchain=$(tr -d '\r\n' < "$target/lean-toolchain")
[[ "$actual_toolchain" == "$expected_toolchain" ]] || {
  echo "error: expected $expected_toolchain, found $actual_toolchain" >&2
  exit 1
}

if git -C "$target" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  actual_head=$(git -C "$target" rev-parse HEAD)
  if [[ "$actual_head" != "$expected_head" ]]; then
    echo "warning: package targets $expected_head but checkout is $actual_head" >&2
  fi
fi

files=(
  BusyLean/SuperReflection.lean
  BusyLean/SuperReflectionFacts.lean
  BusyLean/Contender20.lean
  BusyLean/Comparison20.lean
  test/Audit20.lean
  scripts/check20.py
)

for rel in "${files[@]}"; do
  src="$package_dir/overlay/$rel"
  dst="$target/$rel"
  if [[ -e "$dst" && $force -ne 1 ]]; then
    echo "error: $dst already exists; use --force to replace it" >&2
    exit 1
  fi
  mkdir -p "$(dirname "$dst")"
  cp "$src" "$dst"
done
chmod +x "$target/scripts/check20.py"

python3 - "$target/BusyLean.lean" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
text = p.read_text(encoding="utf-8")
imports = [
    "import BusyLean.SuperReflection",
    "import BusyLean.SuperReflectionFacts",
    "import BusyLean.Contender20",
    "import BusyLean.Comparison20",
]
missing = [line for line in imports if line not in text]
if missing:
    if text and not text.endswith("\n"):
        text += "\n"
    text += "\n".join(missing) + "\n"
    p.write_text(text, encoding="utf-8")
PY

echo "Installed Contender 20 overlay into $target"
echo "Next: cd '$target' && python3 scripts/check20.py"
