#!/usr/bin/env python3
"""Run the real CLI with a test-only evidence hook in its selected image script."""
import builtins
import os
from pathlib import Path
import sys
import tempfile
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_admin


def instrument(source, device_effects=False):
    marker = b"(sb-ext:exit :code (fn2-nserve-main))"
    if source.count(marker) != 1:
        raise ValueError("selected image main changed; review evidence insertion")
    hook = b'(load "tests/native-control-capture.lsp")\n'
    if device_effects:
        adapter = b'(load "host/adapter.lisp")'
        if source.count(adapter) != 1 or source.index(adapter) > source.index(marker):
            raise ValueError("selected adapter must load before device evidence hook")
        hook += b'(load "tests/native-device-effects-capture.lsp")\n'
    return source.replace(marker, hook + marker)


def main():
    selected = ROOT / "tools/image-node.lsp"
    source = instrument(selected.read_bytes(), bool(os.environ.get("FN2_TEST_DEVICE_EFFECTS")))
    original = builtins.open

    def evidence_script(path, mode="r", *args, **kwargs):
        if Path(path) == selected and mode == "rb":
            stream = tempfile.TemporaryFile()
            stream.write(source)
            stream.seek(0)
            return stream
        return original(path, mode, *args, **kwargs)

    with mock.patch("builtins.open", evidence_script):
        return fn_admin.main(root=ROOT)


if __name__ == "__main__":
    raise SystemExit(main())
