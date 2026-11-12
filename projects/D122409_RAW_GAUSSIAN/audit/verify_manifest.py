#!/usr/bin/env python3
"""Verify the published Lean source and execution-evidence hashes."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "audit" / "source_manifest.json"


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    failed = []
    for rel, expected in manifest["sha256"].items():
        path = ROOT / rel
        if not path.is_file():
            failed.append(f"missing source: {rel}")
        elif digest(path) != expected:
            failed.append(f"source hash mismatch: {rel}")
    for rel, expected in manifest["evidence_sha256"].items():
        path = ROOT / "audit" / rel
        if not path.is_file():
            failed.append(f"missing evidence: audit/{rel}")
        elif digest(path) != expected:
            failed.append(f"evidence hash mismatch: audit/{rel}")
    if failed:
        for item in failed:
            print(f"FAIL: {item}", file=sys.stderr)
        return 1
    print(f"PASS: {len(manifest['sha256'])} source/config hashes and {len(manifest['evidence_sha256'])} evidence hashes")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except Exception as exc:
        print(f"VERIFY ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
