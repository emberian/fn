#!/usr/bin/env python3
"""Test-only stdin loader hook; executes the explicitly selected real launcher."""
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def observed_script(source):
    needle = b'(sb-ext:exit :code (fn2-nserve-main))'
    if source.count(needle) != 1:
        raise ValueError('expected exactly one actual native entry')
    return source.replace(needle, b'(load "tests/native-upload-reset-capture.lsp")\n' + needle)


def main():
    real = Path(os.environ['FN2_TEST_REAL_ACL2']).resolve(strict=True)
    if real == Path(__file__).resolve():
        raise ValueError('recursive test launcher')
    source = sys.stdin.buffer.read()
    if source != (ROOT / 'tools/image-node.lsp').read_bytes():
        raise ValueError('test hook requires exact current image-node input')
    with tempfile.TemporaryFile() as script:
        script.write(observed_script(source))
        script.seek(0)
        os.dup2(script.fileno(), 0)
        os.execve(real, [str(real), *sys.argv[1:]], os.environ.copy())


if __name__ == '__main__':
    main()
