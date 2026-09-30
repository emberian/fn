#!/usr/bin/env python3
"""Bind a saved extraction world to selected source, variant and image bytes.

Created only after world_image.sh loads and saves that world successfully.
An old or externally supplied image without this binding remains unknown.
"""
import hashlib
import json
import sys
from pathlib import Path


def digest_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def binding(image, key, variant):
    if variant not in ("default", "dtn"):
        raise ValueError("unsupported extraction variant")
    image = Path(image)
    return {"schema": 1, "world_key": key, "variant": variant,
            "launcher_sha256": digest_file(image),
            "core_sha256": digest_file(str(image) + ".core")}


def record(image):
    return Path(str(image) + ".binding.json")


def check(image, key, variant):
    expected = binding(image, key, variant)
    actual = json.loads(record(image).read_text())
    if actual != expected:
        raise ValueError("saved world source/variant/image binding differs")


def main():
    try:
        action, image, key, variant = sys.argv[1:]
        if action == "create":
            record(image).write_text(json.dumps(binding(image, key, variant), sort_keys=True) + "\n")
        elif action == "check":
            check(image, key, variant)
        else:
            raise ValueError("expected create or check")
    except (OSError, ValueError) as error:
        print("world_binding: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
