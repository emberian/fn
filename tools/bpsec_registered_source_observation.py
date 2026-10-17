#!/usr/bin/env python3
"""Freeze exact BP raw recording source and run receiver composition.

Unchanged dependency copies stay in build/. No issuer/native/proof promotion.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from commit_map import resolve

ROOT = Path(__file__).resolve().parents[1]
REVISION = "640f482a1"
PATHS = [
    "books/cbor.lisp", "books/tcpcl-records.lisp", "books/tcpcl-octets.lisp",
    "books/clock.lisp", "books/tcpcl-session.lisp", "books/tcpcl-received-source.lisp",
    "books/page-read-resources.lisp", "books/page-read-ledger.lisp",
    "books/tcpcl-segment-source-cursor.lisp", "books/bp-received-byte-storage.lisp",
    "books/bp-received-raw-source.lisp", "books/bp-received-raw-registry.lisp",
    "tests/bp_received_raw_registry_recording.lisp",
]
# The framing sources, leased frozen from their last trees (they were
# tools/bpsec_source_observation.py's, retired with its only subject,
# tests/native_bpsec_source_observation.lisp, on 2026-10-16).
DEPENDENCIES = [
    ("6b2fbf3f09bdf4976c1e1edeeab7acbd71d3e161", "books/bp-wire-primary-cursor.lisp", "6b072d05c727deb65902238f7213b19470f8d6b774e910052cdf37379a3433e3"),
    ("963f9cfb8b4b15bdc3e2e67b0f381f1dfa82ed23", "books/bp-wire-canonical-cursor.lisp", "f4c00c50dcd37986a1ba3f29f7358061351439a9ba94a56d99794105c7717600"),
    ("bdc21cf3be8ac3d0ce68daeb0300480194747db6", "books/bp-segmented-wire-job.lisp", "1aa15656903d4232ffed9e294905a7655d02e0782f0ae2947b62b2eb5dea9ddc"),
    ("6b88b5b752b87fbe376c36f9f2ec6767adefb8df", "books/tcpcl-segment-source-cursor.lisp", "9ae2f150a94767d3c9df7cb3b4ad708230eec339f0b1de595450d4c9a74970ed"),
]
OWNED_HASHES = {
    "books/bp-received-raw-source.lisp": "451aaaf835c84eb916fd3f1619d5a0dab90e403990079822466f3c45af6860d6",
    "books/bp-received-raw-registry.lisp": "ef033c2ffa47809e35adc048215273742e9f07112849780d8961555d211988c2",
    "tests/bp_received_raw_registry_recording.lisp": "861dd80d90d13625beefeb8377f8ae4f5e8348d32843e022a3411ce16817b0de",
}

def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: bpsec_registered_source_observation.py /absolute/path/to/sbcl")
    destination = ROOT / "build/bpsec-registered-source-observation"
    destination.mkdir(parents=True, exist_ok=True)
    full_revision = resolve(REVISION, ROOT)
    manifest = []
    for path in PATHS:
        body = subprocess.check_output(["git", "show", f"{full_revision}:{path}"], cwd=ROOT)
        digest = hashlib.sha256(body).hexdigest()
        if path in OWNED_HASHES and digest != OWNED_HASHES[path]:
            raise SystemExit(f"BP lease source mismatch: {path}")
        output = destination / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(body)
        manifest.append(dict(revision=REVISION, path=path, sha256=digest))
    # Use only the frozen trusted recording loader, not its original scenarios.
    # Path adjustment is an owned test adapter; production bodies are unchanged.
    prefix = (destination / PATHS[-1]).read_text().split("; Complete raw transfer", 1)[0]
    prefix = prefix.replace("(catalog-file path)",
                            '(catalog-file (concatenate \'string "build/bpsec-registered-source-observation/" path))')
    (destination / "recording-loader.lisp").write_text(prefix)
    manifest.append(dict(path="recording-loader.lisp", sha256=hashlib.sha256(prefix.encode()).hexdigest(),
                         scope="Owned test path adapter of frozen trusted mutable stobj loader; no original scenario rerun"))
    (destination / "dependencies.json").write_text(json.dumps(manifest, indent=2) + "\n")
    # The framing source copies are the previously leased frozen component.
    framing = ROOT / "build/bpsec-source-observation"
    framing.mkdir(parents=True, exist_ok=True)
    for revision, path, digest in DEPENDENCIES:
        body = subprocess.check_output(["git", "show", f"{resolve(revision, ROOT)}:{path}"], cwd=ROOT)
        if hashlib.sha256(body).hexdigest() != digest:
            raise SystemExit(f"framing source mismatch: {path}")
        (framing / Path(path).name).write_bytes(body)
    return subprocess.call([sys.argv[1], "--script", "tests/native_bpsec_registered_source_observation.lisp"], cwd=ROOT)

if __name__ == "__main__":
    raise SystemExit(main())
