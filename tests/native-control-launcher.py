#!/usr/bin/env python3
"""Run the real CLI with a test-only evidence hook in its selected image script."""
import builtins
from pathlib import Path
import sys
import tempfile
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import fn_admin


def instrument(source):
    marker = b"(sb-ext:exit :code (fn2-nserve-main))"
    if source.count(marker) != 1:
        raise ValueError("selected image main changed; review evidence insertion")
    return source.replace(marker, b'(load "tests/native-control-capture.lsp")\n' + marker)


def main():
    selected = ROOT / "tools/image-node.lsp"
    source = instrument(selected.read_bytes())
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
