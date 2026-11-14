#!/usr/bin/env python3
"""Make isolated ACL2 fixtures declare their B* syntax dependency explicitly."""
from __future__ import annotations
import argparse
from pathlib import Path
import lisp_rewrite as lr

IMPORT = '(include-book "std/util/bstar" :dir :system)'

def rewrite(text: str) -> str:
    parsed = lr.parse(text)
    if not lr.match('_', parsed.forms, head='b*'):
        return text
    if lr.match(IMPORT, parsed.forms, deep=False):
        return text
    packages = lr.match('(in-package ?name)', parsed.forms, deep=False)
    if len(packages) != 1:
        raise ValueError('expected exactly one top-level IN-PACKAGE')
    at = packages[0].end
    return lr.write(text, [(at, at, '\n' + IMPORT)])

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write', action='store_true')
    ap.add_argument('files', nargs='+', type=Path)
    args = ap.parse_args()
    missing = []
    for path in args.files:
        original = path.read_text()
        updated = rewrite(original)
        if original != updated:
            missing.append(str(path))
            if args.write:
                path.write_text(updated)
    print(('updated' if args.write else 'missing explicit B* import') + ': ' + str(len(missing)))
    for name in missing:
        print(name)
    return 0 if args.write or not missing else 1

if __name__ == '__main__':
    raise SystemExit(main())
