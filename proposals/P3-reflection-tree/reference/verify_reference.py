#!/usr/bin/env python3
"""Verify pinned reference snapshots without network access or Git."""

from pathlib import Path
import hashlib
import json


def main() -> None:
    directory = Path(__file__).resolve().parent
    manifest = json.loads((directory / "SOURCE_PROVENANCE.json").read_text())
    for entry in manifest["files"]:
        data = (directory / entry["path"]).read_bytes()
        blob_header = b"blob " + str(len(data)).encode("ascii") + b"\0"
        observed = {
            "bytes": len(data),
            "git_blob_sha1": hashlib.sha1(blob_header + data).hexdigest(),
            "sha256": hashlib.sha256(data).hexdigest(),
        }
        for field, actual in observed.items():
            if actual != entry[field]:
                raise SystemExit(f"FAIL: {entry['path']} {field}")
    print(f"Verified {len(manifest['files'])} pinned upstream files.")
    print(f"Commit: {manifest['commit']}")


if __name__ == "__main__":
    main()
