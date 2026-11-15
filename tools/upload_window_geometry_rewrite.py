#!/usr/bin/env python3
"""Move the actual protocol constants and bind byte-based upload ranges."""
from pathlib import Path
import argparse
import hashlib
import json
import lisp_rewrite as lr

def transform(root):
 moves = [('books/upload-scan.lisp', '*fn2-upload-header-octets*'), ('books/upload-kind.lisp', '*fn2-upload-digest-octets*'), ('books/ordered.lisp', '*fn2-overview-octets-max*')]
 forms = []
 receipt = []
 for name, symbol in moves:
     p = root / name
     old = p.read_text()
     parsed = lr.parse(old)
     m = lr.match('(defconst ' + symbol + ' ?value)', parsed.forms)
     assert len(m) == 1
     m = m[0]
     text = old[m.start:m.end]
     forms.append(text)
     receipt.append({'source': name, 'symbol': symbol, 'sha256': hashlib.sha256(text.encode()).hexdigest()})
     pkg = lr.match('(in-package "ACL2")', parsed.forms)[0]
     p.write_text(lr.write(old, [(m.start, m.end, ''), (pkg.end, pkg.end, '\n(include-book "upload-window-geometry")')]))
 (root / 'books/upload-window-geometry.lisp').write_text('; Shared protocol workspace sizes consumed by actual upload TAKE and service admission.\n(in-package "ACL2")\n(include-book "commit-geometry")\n(fn2-book-layer :b)\n\n' + '\n'.join(forms) + '\n\n; Header references and the eventual digest/overview scratch survive body reuse.\n(defconst *fn2-upload-header-workspace-bytes*\n (+ *fn2-upload-header-octets* *fn2-upload-digest-octets* *fn2-overview-octets-max*))\n(defconst *fn2-upload-body-window-bytes* *fn2-commit-unit-bytes*)\n')
 (root / 'docs/design/receipts').mkdir(parents=True, exist_ok=True)
 (root / 'docs/design/receipts/upload-window-geometry-source.json').write_text(json.dumps({'scope': 'exact source-form moves; no ACL2/guard or rolling progress claim', 'forms': receipt}, indent=2) + '\n')
 p = root / 'books/upload-kind.lisp'
 s = p.read_text()
 old = '(:chunk-window :slot c0-slot :gen c0-gen :class 1)\n                  (:chunk-window :slot c1-slot :gen c1-gen :class 1)'
 new = '(:chunk-window :slot c0-slot :gen c0-gen :class (:bytes *fn2-upload-header-workspace-bytes*))\n                  (:chunk-window :slot c1-slot :gen c1-gen :class (:bytes *fn2-upload-body-window-bytes*))'
 assert old in s
 s = s.replace(old, new)
 a = s.index(';; The pool class of a chunk')
 b = s.index(';; Large-upload windows', a)
 s = s[:a] + ' ; Header and body windows use shared byte requirements at actual TAKE,\n; resolved by the existing pool class resolver for the configured profile.\n' + s[b:]
 p.write_text(s)
 p = root / 'books/upload-kind.lisp'
 s = p.read_text()
 anchor = '; resolved by the existing pool class resolver for the configured profile.\n'
 assert anchor in s
 s = s.replace(anchor, anchor + '; The input-profile/constructor fixture class baseline remains unchanged;\n; actual upload TAKE uses the byte requirements below.\n(defconst *fn2-upload-chunk-class* 1)\n', 1)
 p.write_text(s)

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('root',type=Path)
 transform(p.parse_args().root)
