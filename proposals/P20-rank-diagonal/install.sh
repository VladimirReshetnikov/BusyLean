#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./install.sh [--force] /path/to/BusyLean

Copies the Contender 14 overlay into a BusyLean checkout and appends the
required imports to BusyLean.lean.  Existing nonidentical overlay files are
left untouched unless --force is supplied.
USAGE
}

force=0
if [[ ${1:-} == "--force" ]]; then
  force=1
  shift
fi
if [[ $# -ne 1 ]]; then
  usage >&2
  exit 2
fi

target=$(cd "$1" && pwd)
root=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

if [[ ! -f "$target/BusyLean.lean" || ! -d "$target/BusyLean" ]]; then
  echo "error: $target does not look like the BusyLean repository root" >&2
  exit 1
fi

expected=1ee50c7d97bbed57a60709f661453c3e213f4db3
if command -v git >/dev/null 2>&1 && git -C "$target" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  actual=$(git -C "$target" rev-parse HEAD)
  if [[ $actual != "$expected" ]]; then
    echo "warning: overlay was audited against $expected" >&2
    echo "warning: target checkout is at $actual; review the current contender first" >&2
  fi
fi

copy_one() {
  local src=$1 dst=$2
  mkdir -p "$(dirname "$dst")"
  if [[ -e "$dst" ]] && ! cmp -s "$src" "$dst"; then
    if [[ $force -ne 1 ]]; then
      echo "error: refusing to overwrite nonidentical $dst (use --force)" >&2
      exit 1
    fi
    cp -p "$dst" "$dst.pre-contender14.bak"
    echo "backup: $dst.pre-contender14.bak"
  fi
  install -m "$(stat -c '%a' "$src")" "$src" "$dst"
  echo "installed: ${dst#$target/}"
}

copy_one "$root/overlay/BusyLean/HyperReflection.lean" "$target/BusyLean/HyperReflection.lean"
copy_one "$root/overlay/BusyLean/Contender14.lean" "$target/BusyLean/Contender14.lean"
copy_one "$root/overlay/BusyLean/Comparison14.lean" "$target/BusyLean/Comparison14.lean"
copy_one "$root/overlay/test/Audit14.lean" "$target/test/Audit14.lean"
copy_one "$root/overlay/scripts/check14.py" "$target/scripts/check14.py"

for line in \
  'import BusyLean.HyperReflection' \
  'import BusyLean.Contender14' \
  'import BusyLean.Comparison14'; do
  if ! grep -qxF "$line" "$target/BusyLean.lean"; then
    printf '%s\n' "$line" >> "$target/BusyLean.lean"
    echo "appended to BusyLean.lean: $line"
  fi
done

echo
echo "Next step:"
echo "  cd '$target' && python3 scripts/check14.py"
