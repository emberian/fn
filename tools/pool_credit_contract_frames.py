#!/usr/bin/env python3
"""Requested ROWS contracts from actual credit configuration resizers."""
from pathlib import Path
import argparse
import re
import lisp_rewrite

START = '; Configuration resizer ROWS contracts generated from actual API calls.\n'
END = '; End configuration resizer ROWS contracts.\n'

def generate(api, declaration):
    parsed = lisp_rewrite.parse(api)
    writer = next(api[n.start:n.end] for n in parsed.forms
                  if api[n.start:n.end].startswith('(defun fn2-pool-credit-configure'))
    names = list(dict.fromkeys(re.findall(r'resize-fn2-pool-credit-[a-z-]+', writer)))
    assert names
    events = []
    for name in names:
        assert '(' + name[len('resize-'):] + ' :type (array ' in declaration
        events.append('(fn2-pool-preserves ' + name + ' (n fn2-pool)\n'
            ' :specs (("-PUBLIC-ROWS" fn2-pool-rows nil :frame fn2-pool)) :disable nil\n'
            ' :hints (("Goal" :in-theory (enable fn2-pool-rows ' + name + '))))')
    return START + '\n'.join(events) + '\n' + END

def rewrite(source, api, declaration):
    begin = source.index(START)
    end = source.index(END, begin) + len(END)
    return lisp_rewrite.write(source, [(begin, end, generate(api, declaration))])

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = Path('books/pool-credit-contracts.lisp')
    source = path.read_text()
    updated = rewrite(source, Path('books/pool-credit.lisp').read_text(),
                      Path('books/pool.lisp').read_text())
    if args.check:
        assert updated == source
    else:
        path.write_text(updated)
