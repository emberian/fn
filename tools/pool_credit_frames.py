#!/usr/bin/env python3
"""Regenerate leaf proof frames from the actual group writer's extra setters."""
from pathlib import Path
import argparse
import re
import lisp_rewrite

START = '; Public frame class generated from the six actual group-array setters.\n'
END = '(defun fn2-pool-credit-store-groups'

def generate(source, declaration):
    parsed = lisp_rewrite.parse(source)
    writer = next(source[n.start:n.end] for n in parsed.forms
                  if source[n.start:n.end].startswith(END))
    names = list(dict.fromkeys(re.findall(r'update-fn2-pool-credit-([a-z-]+)i\b', writer)))
    assert names
    result = []
    for name in names:
        assert '(fn2-pool-credit-' + name + ' :type (array ' in declaration
        setter = 'update-fn2-pool-credit-' + name + 'i'
        getters = ['fn2-pool-nclasses'] + ['fn2-pool-credit-' + other + '-length'
                                         for other in names if other != name]
        equations = ['(equal (' + getter + ' (' + setter + ' i value fn2-pool)) ('
                     + getter + ' fn2-pool))' for getter in getters]
        result.append('(defthm fn2-pool-credit-' + name + '-keeps-group-geometry\n (and '
                      + '\n      '.join(equations) + ')\n :hints (("Goal" :in-theory (enable '
                      + ' '.join(getters + [setter]) + '))))')
    return START + '\n'.join(result) + '\n\n'

def generate_resizers(source, declaration):
    parsed = lisp_rewrite.parse(source)
    writer = next(source[n.start:n.end] for n in parsed.forms
                  if source[n.start:n.end].startswith('(defun fn2-pool-credit-configure'))
    ops = list(dict.fromkeys(re.findall(r'resize-fn2-pool-credit-[a-z-]+', writer)))
    result = ['; Public scalar frames for the actual configuration resizers.\n']
    for op in ops:
        field = op[len('resize-'):]
        assert '(' + field + ' :type (array ' in declaration
        result.append('(defthm ' + op + '-keeps-nclasses\n'
                      ' (equal (fn2-pool-nclasses (' + op + ' n fn2-pool)) (fn2-pool-nclasses fn2-pool))\n'
                      ' :hints (("Goal" :in-theory (enable fn2-pool-nclasses ' + op + '))))\n')
    return ''.join(result)

def rewrite(source, declaration):
    begin = source.index(START)
    end = source.index(END, begin)
    resize_start = source.index('; Public scalar frames for the actual configuration resizers.')
    resize_end = source.index('(defun fn2-pool-credit-configure', resize_start)
    return lisp_rewrite.write(source, [(begin, end, generate(source, declaration)),
        (resize_start, resize_end, generate_resizers(source, declaration))])

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = Path('books/pool-credit.lisp')
    source = path.read_text()
    updated = rewrite(source, Path('books/pool.lisp').read_text())
    if args.check:
        assert updated == source, 'run tools/pool_credit_frames.py to regenerate'
    else:
        path.write_text(updated)
