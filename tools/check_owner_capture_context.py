#!/usr/bin/env python3
"""Run the actual program-mode owner capture constructor in a warm ACL2 world.

The selected source definitions are extracted verbatim; the warm world must
already contain owner-config/owner dependencies. This is a composition fixture,
not full owner qualification or a new semantic implementation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from datetime import datetime, timezone
import sys

import proof_repl

SELECTED = {
    'books/owner-config-selector.lisp': ['fn-ocfg-config'],
    'books/owner-config.lisp': ['fn-ocfg-owner', 'fn-ocfg-pins', 'fn-ocfg-staged',
        'fn-ocfg-make', 'fn-ocfg-with-owner'],
    'books/owner-state-accessors.lisp': ['fn-owner-ocfg'],
    'books/owner-reader-view.lisp': ['fn-ocv-reader-view', 'fn-own-with-view',
        'fn-ocfg-with-view', 'fn-ocfg-at-reader-view'],
    'books/owner-tls-prefix.lisp': ['fn-own-tls-served-conn'],
    'books/catalog-root-incarnation.lisp': ['fn-cri-tokenp', 'fn-cri-reserve'],
    'books/owner-connection-state.lisp': ['fn-owner-reader-views'],
    'host/owner-host.lisp': ['fn-owner-catalog-root-reserve',
        'fn-owner-catalog-root-current', 'fn-owner-catalog-capture-context'],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('session')
    parser.add_argument('--source-tree', type=Path, default=Path('.'))
    args = parser.parse_args()
    output = Path('build/runtime-tests/owner-capture-context')
    output.mkdir(parents=True, exist_ok=True)
    selected = []
    provenance = []
    for relative, names in SELECTED.items():
        path = args.source_tree / relative
        text = path.read_text()
        definitions = {proof_repl.head_and_name(form)[1]: form
            for form in proof_repl.forms(text)
            if proof_repl.head_and_name(form)[0] == 'defun'}
        for name in names:
            form = definitions[name]
            selected.append(form)
            provenance.append({'path': relative, 'name': name,
                'sha256': hashlib.sha256(form.encode()).hexdigest()})
    fixture = Path('tests/owner_capture_context_fixture.lisp').read_text()
    source = output / 'selected-source.lisp'
    source.write_text('(in-package "ACL2")\n' + '\n\n'.join(selected) + '\n' + fixture)
    (output / 'source.json').write_text(json.dumps({
        'source_tree': str(args.source_tree.resolve()),
        'source_revision': subprocess.check_output(['git', '-C', str(args.source_tree),
            'rev-parse', 'HEAD'], text=True).strip(),
        'definitions': provenance,
        'fixture_sha256': hashlib.sha256(fixture.encode()).hexdigest(),
        'scope': 'actual selected program constructor; no full owner or image qualification'
    }, indent=2) + '\n')
    result = subprocess.run([sys.executable, 'tools/proof_repl.py', 'send-file',
        args.session, str(source)], text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT)
    (output / 'result.log').write_text(result.stdout)
    print(result.stdout, end='')
    (output / 'result.json').write_text(json.dumps({
        'session': args.session, 'exit_code': result.returncode,
        'finished_utc': datetime.now(timezone.utc).isoformat(),
        'source_manifest_sha256': hashlib.sha256((output / 'source.json').read_bytes()).hexdigest(),
        'log_sha256': hashlib.sha256(result.stdout.encode()).hexdigest()
    }, indent=2) + '\n')
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
