#!/usr/bin/env python3
"""Prepare the exact current native startup with test capture inserted.

Does not run ACL2, open a socket, or substitute a host implementation. Use the
normal qualified launcher and allocated scope for the resulting stdin file.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import proof_repl


def instrument(source, capture_path="tests/native-device-cut-capture.lsp"):
    spans = proof_repl.spans(source)
    final = source[slice(*spans[-1])]
    if final != '(sb-ext:exit :code (fn2-nserve-main))':
        raise ValueError('Current startup does not end at the actual native main')
    capture = f'(load "{capture_path}")\n'
    return source[:spans[-1][0]] + capture + source[spans[-1][0]:]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    source = (ROOT / 'tools/image-node.lsp').read_text()
    with args.output.open('x') as out:
        out.write(instrument(source))
