#!/usr/bin/env python3
"""Emit a post-admission hook for the actual native whole-effect theorem.

Run as TOP-LEVEL events, not in a new encapsulate (which hides external proof
supporters). Run only after admitting the unchanged whole consumer book with proofs and the
shared extractor. Including the consumer certificate cannot satisfy this hook.
This does not launch ACL2, change certificates, or discharge the crypto premise.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import certs
import ledger

BOOK = 'books/native-b3-correspondence'
SUBJECT = 'FN2-NATIVE-MK-NODE-WHOLE-EFFECT'
SUPPORT = 'FN2-A-CRYPTO-NATIVE-CORRESPONDENCE'
ASSUMPTION = 'FN2-A-CRYPTO-NATIVE'


def identity(root):
    path = root / (BOOK + '.lisp')
    raw = path.read_bytes()
    forms = ledger.read_forms(raw.decode('latin-1'))
    found = [f for f in forms if ledger.head(f) == 'defthm' and str(f[1]).upper() == SUBJECT]
    if len(found) != 1:
        raise ValueError('expected one actual top-level whole-effect theorem')
    return [BOOK, hashlib.sha256(raw).hexdigest(), certs.closure_key(root, BOOK)[0],
            ledger.Sym(SUBJECT.lower()), ledger.Sym(SUPPORT.lower()), ledger.Sym(ASSUMPTION.lower()),
            certs.closure_key(root, 'books/assurance-proof-support')[0],
            hashlib.sha256(Path(__file__).read_bytes()).hexdigest()], found[0][2]


def hook(root, output):
    ident, formula = identity(root)
    expected = ledger.source_text(formula)
    return f'''(in-package "ACL2")
; Source identity check only: no alternate theorem/model is proved here.
(make-event
 (let ((actual (getpropc '{SUBJECT} 'theorem nil (w state))))
  (if actual
      (value (list 'defun-nx 'fn2-native-support-source-form (all-vars actual)
                   '{expected}))
    (er soft 'native-proof-support "Actual consumer theorem is absent."))))
(make-event
 (let* ((world (w state))
        (actual (getpropc '{SUBJECT} 'theorem nil world))
        (body (getpropc 'fn2-native-support-source-form 'unnormalized-body nil world))
        (translated (if (eq (car body) 'return-last) (cadddr body) body))
        (node (fn2-proof-support-node '{SUBJECT} '({ASSUMPTION}) world))
        (contexts (fn2-proof-assumption-contexts
                   '{SUPPORT} (getpropc '{SUPPORT} 'theorem nil world)
                   '({ASSUMPTION}) world)))
  (if (and actual (equal actual translated)
           (member-eq '{SUPPORT} (cadr (assoc-keyword :supporters node)))
           (eq (cadr (assoc-keyword :status (car contexts)))
               :exact-live-constraint-theorem))
      (value (list 'defconst '*fn2-native-proof-support-capture*
                   (list 'quote
                    (list :kind :source-admitted-proof-support
                          :identity '{ledger.source_text(ident)}
                          :report (fn2-proof-support-report
                                   '({SUBJECT}) '({ASSUMPTION}) 128 world)))))
    (er soft 'native-proof-support "Source formula, actual proof support, or constraint binding differs."))))
; Ordinary post-admission I/O: forbidden inside MAKE-EVENT or a book.
(mv-let (channel state) (open-output-channel {ledger.source_text(str(output))} :object state)
 (if (not channel)
     (prog2$ (er hard 'native-proof-support "Cannot open capture output.") state)
   (let ((state (print-object$ *fn2-native-proof-support-capture* channel state)))
     (close-output-channel channel state))))
'''


def validate_capture(root, path):
    forms = ledger.read_forms(path.read_text(encoding='latin-1'))
    if len(forms) != 1 or not isinstance(forms[0], list):
        raise ValueError('expected one source-admission capture')
    row = forms[0]
    if len(row) != 6 or [str(k).upper() for k in row[::2]] != [':KIND', ':IDENTITY', ':REPORT']:
        raise ValueError('unsupported source-admission capture fields')
    if str(row[1]).upper() != ':SOURCE-ADMITTED-PROOF-SUPPORT':
        raise ValueError('unsupported source-admission capture kind')
    current, _ = identity(root)
    if ledger.source_text(row[3]) != ledger.source_text(current):
        raise ValueError('consumer source, closure key, theorem or assumption identity differs')
    report = row[5]
    def plist(value):
        if not isinstance(value, list) or len(value) % 2:
            raise ValueError('malformed proof-support plist')
        keys = [str(k).upper() for k in value[::2]]
        if len(keys) != len(set(keys)):
            raise ValueError('duplicate proof-support fields')
        return dict(zip(keys, value[1::2]))
    fields = plist(report)
    if fields.get(':ROOTS') != [ledger.Sym(SUBJECT.lower())] or fields.get(':NAMED-ASSUMPTION-SUBJECTS') != [ledger.Sym(ASSUMPTION.lower())]:
        raise ValueError('nested report names different consumer/assumption')
    nodes = fields.get(':NODES')
    if not isinstance(nodes, list):
        raise ValueError('missing captured graph')
    selected = [plist(n) for n in nodes if isinstance(n, list) and ':NAME' in [str(k).upper() for k in n[::2]]]
    by_name = {str(n[':NAME']).upper(): n for n in selected}
    if len(by_name) != len(selected):
        raise ValueError('duplicate support nodes')
    subject = by_name.get(SUBJECT, {})
    if ledger.Sym(SUPPORT.lower()) not in subject.get(':SUPPORTERS', []):
        raise ValueError('actual support edge absent')
    if str(subject.get(':SUPPORT-STATE')).upper() != ':RECORDED-EVENT-SUPPORT':
        raise ValueError('support was not captured during admission')
    support = by_name.get(SUPPORT, {})
    contexts = support.get(':CONSTRAINT-CONTEXTS', [])
    matching = []
    for context in contexts:
        c = plist(context)
        if c.get(':SUBJECT') != ledger.Sym(ASSUMPTION.lower()):
            continue
        terms, origins = c.get(':CONSTRAINTS'), c.get(':ORIGINS')
        if not isinstance(terms, list) or not isinstance(origins, list) or len(terms) != len(origins):
            continue
        if (str(c.get(':STATUS')).upper() == ':EXACT-LIVE-CONSTRAINT-THEOREM' and
            any(term == support.get(':THEOREM') and origin == [ledger.Sym('theorem'), ledger.Sym(SUPPORT.lower())]
                for term, origin in zip(terms, origins))):
            matching.append(c)
    if len(matching) != 1:
        raise ValueError('exact live constraint name/formula binding absent')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--capture', type=Path, required=True)
    args = p.parse_args()
    args.output.write_text(hook(args.root, args.capture))
    print(json.dumps({'hook': str(args.output), 'capture': str(args.capture),
                      'identity': identity(args.root)[0],
                      'status': 'source-only; requires actual live admission'}, indent=2))

if __name__ == '__main__':
    main()
