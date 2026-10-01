#!/usr/bin/env python3
"""Freeze named unchanged BP dependencies, then run the real-source diagnostic.

This does not bootstrap ACL2, build an image, issue refs or install a provider.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = [
    ("6b2fbf3f09bdf4976c1e1edeeab7acbd71d3e161", "books/bp-wire-primary-cursor.lisp", "6b072d05c727deb65902238f7213b19470f8d6b774e910052cdf37379a3433e3"),
    ("963f9cfb8b4b15bdc3e2e67b0f381f1dfa82ed23", "books/bp-wire-canonical-cursor.lisp", "f4c00c50dcd37986a1ba3f29f7358061351439a9ba94a56d99794105c7717600"),
    ("bdc21cf3be8ac3d0ce68daeb0300480194747db6", "books/bp-segmented-wire-job.lisp", "1aa15656903d4232ffed9e294905a7655d02e0782f0ae2947b62b2eb5dea9ddc"),
    ("6b88b5b752b87fbe376c36f9f2ec6767adefb8df", "books/tcpcl-segment-source-cursor.lisp", "9ae2f150a94767d3c9df7cb3b4ad708230eec339f0b1de595450d4c9a74970ed"),
]

def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: bpsec_source_observation.py /absolute/path/to/sbcl")
    destination = ROOT / "build/bpsec-source-observation"
    destination.mkdir(parents=True, exist_ok=True)
    manifest = []
    for revision, path, digest in DEPENDENCIES:
        source = subprocess.check_output(["git", "show", f"{revision}:{path}"], cwd=ROOT)
        if hashlib.sha256(source).hexdigest() != digest:
            raise SystemExit(f"dependency hash mismatch: {path}")
        (destination / Path(path).name).write_bytes(source)
        manifest.append(dict(revision=revision, path=path, sha256=digest))
    (destination / "dependencies.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return subprocess.call([sys.argv[1], "--script", "tests/native_bpsec_source_observation.lisp"], cwd=ROOT)

if __name__ == "__main__":
    raise SystemExit(main())
