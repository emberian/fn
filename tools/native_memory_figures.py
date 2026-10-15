#!/usr/bin/env python3
"""Regenerate tests/native_memory_figures.json by evaluating source-exact ACL2.

Only the constant/function dependency slice of fn-cbud-conn-octets is loaded.
This is evaluation, not a certificate. Python never computes the Lisp charge.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as L

SOURCES = ('books/connection-budget.lisp', 'books/connection-read-quantum.lisp',
           'books/heap-figure.lisp')
GENERATOR = 'tools/native_memory_figures.py'


def source_digests():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES}


def source_slice():
    definitions = {}
    for name in SOURCES:
        parsed = L.parse(ROOT / name)
        for node in parsed.forms:
            if (isinstance(node, L.Lst) and len(node.items) > 2
                    and isinstance(node.items[0], L.Atom)
                    and node.items[0].low in ('defun', 'defconst')):
                definitions[node.items[1].low] = (parsed, node)
    emitted, visiting, forms = set(), set(), []
    def atoms(node):
        if isinstance(node, L.Atom):
            yield node.low
        elif isinstance(node, L.Lst):
            for child in node.items:
                yield from atoms(child)
    def visit(name):
        if name in emitted:
            return
        if name in visiting:
            raise ValueError('recursive cost slice: ' + name)
        visiting.add(name)
        parsed, node = definitions[name]
        for dependency in sorted(set(atoms(node)) - {name}):
            if dependency in definitions:
                visit(dependency)
            elif dependency.startswith(('fn-', '*fn-')):
                raise ValueError('cost dependency needs a source in ' + GENERATOR + ': ' + dependency)
        forms.append(parsed.text[node.start:node.end])
        visiting.remove(name)
        emitted.add(name)
    visit('fn-cbud-conn-octets')
    return '\n\n'.join(forms)


def main():
    before = source_digests()
    work = ROOT / 'build/native-memory-figures'
    work.mkdir(parents=True, exist_ok=True)
    source = work / 'source.lisp'
    source.write_text('(in-package "ACL2")\n' + source_slice() + '''
(value-triple
 (cw "FN_NATIVE_MEMORY_FIGURES ~x0 ~x1~%"
     (fn-cbud-conn-octets 0 nil) (fn-cbud-conn-octets 0 t)))
''')
    driver = work / 'driver.lsp'
    driver.write_text('(ld ' + json.dumps(str(source)) +
                      ' :ld-error-action :return)\n(quit)\n')
    log = work / 'acl2.log'
    with driver.open('r') as inp, log.open('w') as out:
        job = subprocess.Popen([str(ROOT / 'tools/acl2'), '--timeout', '60',
                                '--label', 'native-memory-figures'],
                               cwd=ROOT, stdin=inp, stdout=out, stderr=subprocess.STDOUT)
        (work / 'job.pid').write_text(str(job.pid) + '\n')
        code = job.wait()
    if code:
        raise SystemExit(f'{GENERATOR}: ACL2 exit {code}; see {log}')
    text = log.read_text()
    match = re.search(r'FN_NATIVE_MEMORY_FIGURES\s+(\d+)\s+(\d+)', text)
    if not match:
        raise SystemExit(f'{GENERATOR}: cost slice did not evaluate; see {log}')
    if source_digests() != before:
        raise SystemExit(f'{GENERATOR}: input changed during generation; run again')
    data = {'generated_by': GENERATOR,
            'connection_fixed_without_tls': int(match[1]),
            'connection_fixed_with_tls': int(match[2]),
            'source_sha256': before}
    target = ROOT / 'tests/native_memory_figures.json'
    target.write_text(json.dumps(data, indent=2) + '\n')
    print(f'{GENERATOR}: regenerated {target.relative_to(ROOT)} from ACL2')


if __name__ == '__main__':
    main()
