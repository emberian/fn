#!/usr/bin/env python3
"""Split the FNCT request-layout declaration using the owning generator."""
import argparse
from pathlib import Path
import lisp_rewrite as lr

MACRO = '''(defmacro fn2-fnct-deflayout (word)
  `(make-event
    (let ((row (fn2-fnct-word-row ',word *fn2-fnct-codes*)))
      (if (not row)
          (er soft 'fn2-fnct-deflayout "Unknown request schema ~x0." ',word)
        (let ((form (car (fn2-fnct-deflayout-forms (list row)))))
          (if (assoc-eq (cadr form) (table-alist 'fn2-layouts (w state)))
              (er soft 'fn2-fnct-deflayout "Duplicate request schema ~x0." ',word)
            (value form)))))))
(defun fn2-fnct-layouts-presentp (rows layouts)
  (declare (xargs :verify-guards nil))
  (if (atom rows) t
    (let* ((form (car (fn2-fnct-deflayout-forms (list (car rows)))))
           (entry (cdr (assoc-eq (cadr form) layouts))))
      (and (equal (fn2-decl-get :layout entry) (cadr (caddr form)))
           (fn2-fnct-layouts-presentp (cdr rows) layouts)))))'''
CHECK = '''(assert-event
  (and (no-duplicatesp-eq (strip-cars (strip-cdrs *fn2-fnct-codes*)))
       (fn2-fnct-layouts-presentp *fn2-fnct-codes*
                                 (table-alist 'fn2-layouts (w state)))))'''


def head(node):
    return node.items[0].low if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom) else None


def transform(text):
    forms = lr.parse(text).forms
    tables = [n for n in forms if head(n) == 'defconst' and n.items[1].low == '*fn2-fnct-codes*']
    if len(tables) != 1 or not isinstance(tables[0].items[2], lr.Pre):
        raise ValueError('one literal FNCT request schema table required')
    rows = tables[0].items[2].node.items
    words = [row.items[1].low for row in rows]
    if not words or any(not word.startswith(':') for word in words) or len(set(words)) != len(words):
        raise ValueError('request schemas require distinct literal word names')
    aggregates = [n for n in forms if head(n) == 'make-event'
                  and 'fn2-fnct-deflayout-forms' in text[n.start:n.end]
                  and '*fn2-fnct-codes*' in text[n.start:n.end]]
    calls = [n for n in forms if head(n) == 'fn2-fnct-deflayout']
    if not aggregates:
        if [n.items[1].low for n in calls] != words or MACRO not in text or CHECK not in text:
            raise ValueError('decomposed declaration inventory is incomplete or changed')
        return text
    if len(aggregates) != 1 or calls:
        raise ValueError('expected one aggregate and no existing per-schema declarations')
    lookup = [n for n in forms if head(n) == 'defun' and n.items[1].low == 'fn2-fnct-word-row']
    if len(lookup) != 1:
        raise ValueError('existing schema lookup must be unique')
    declarations = '\n'.join('(fn2-fnct-deflayout ' + word + ')' for word in words)
    replacement = (text[lookup[0].start:lookup[0].end] + '\n' + MACRO + '\n'
                   + declarations + '\n' + CHECK)
    return lr.write(text, [(lookup[0].start, lookup[0].end, ''),
                           (aggregates[0].start, aggregates[0].end, replacement)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = transform(args.source.read_text())
    if args.write:
        args.source.write_text(result)
    else:
        print(result, end='')
