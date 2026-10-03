#!/usr/bin/env python3
"""Prepare a fresh ACL2/native process entry, preserving build attachment order.

This executes admitted source and trusted native loads; it never saves an image
or treats a loaded definition as a certificate. The bootstrap world and each
selected source event have separate coordinates in the companion manifest.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from proof_repl import forms


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def literal(value: str) -> str:
    return '"' + value.replace('\\', '\\\\').replace('"', '\\"') + '"'


def prefix(text: str, overlays: list[str]) -> str:
    result = []
    inserted = False
    for form in forms(text):
        lower = form.lower()
        if lower == ':q' or lower.startswith('(save-exec '):
            break
        if (lower.startswith('(load "host/native/strip-world.lisp"')
                or lower.startswith('(fnn-save-world-flavor ')):
            continue
        if lower.startswith('(defttag :fn-native-host'):
            if overlays:
                result.append("(set-ld-redef-action '(:warn . :overwrite) state)")
                result.extend(overlays)
                result.append("(set-ld-redef-action nil state)")
            inserted = True
        result.append(form)
    if not inserted:
        raise ValueError('build has no normal-to-native boundary')
    # Every logical event/load above uses the ordinary ACL2 error path. Native
    # entry occurs only after the complete ordered bootstrap has returned.
    result.append('(defttag :fn-source-native-entry)')
    result.append('(progn! (set-raw-mode t) (fn-native-entry state))')
    return '\n\n'.join(result) + '\n'


def prepare(args) -> Path:
    world = Path(args.world_root).resolve()
    source = Path(args.source_root).resolve()
    out = Path(args.output).resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    build = world / args.build
    hashes = {str(build): digest(build)}
    # Verify source inputs at every launch; admitted forms remain embedded in
    # the bootstrap and have their own hashes in the event coordinates.
    for pattern in ('books/*.lisp', 'host/**/*.lisp', 'lib/*.so', 'lib/*.dylib'):
        for path in world.glob(pattern):
            if path.is_file():
                hashes[str(path)] = digest(path)
    selected = []
    coordinates = []
    for selector in args.event:
        name, symbol = selector.rsplit(':', 1)
        path = source / name
        found = [f for f in forms(path.read_text())
                 if re.match(r'\(defun\s+' + re.escape(symbol) + r'\s', f, re.I)]
        if len(found) != 1:
            raise ValueError(f'{selector}: expected one actual defun')
        selected.append(found[0])
        hashes[str(path)] = digest(path)
        coordinates.append({'file': str(path), 'symbol': symbol,
                            'form_sha256': hashlib.sha256(found[0].encode()).hexdigest(),
                            'file_sha256': digest(path)})
    bootstrap = out.with_suffix('.bootstrap.lisp')
    bootstrap.write_text('(in-package "ACL2")\n(set-cbd ' + literal(str(world) + '/')
                         + ')\n' + prefix(build.read_text(), selected))
    hashes[str(bootstrap)] = digest(bootstrap)
    manifest = out.with_suffix('.json')
    data = {'schema': 'fn-native-source-runner-v1', 'world_root': str(world),
            'world_revision': args.world_revision, 'source_root': str(source),
            'source_revision': args.source_revision or subprocess.check_output(
                ['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip(),
            'bootstrap': str(bootstrap), 'sha256': hashes, 'events': coordinates,
            'sbcl': str(Path(args.sbcl).resolve()), 'core': str(Path(args.core).resolve()),
            'profile': args.profile, 'kind': 'fresh source execution; not certification or packaging'}
    manifest.write_text(json.dumps(data, indent=2) + '\n')
    script = Path(__file__).resolve()
    out.write_text('#!/usr/bin/env python3\nimport os,sys\n'
                   + f'os.execv({sys.executable!r}, [{sys.executable!r}, {str(script)!r}, '
                   + f'"run", {str(manifest)!r}, "--", *sys.argv[1:]])\n')
    out.chmod(0o755)
    return manifest


def run(manifest: Path, argv: list[str]) -> None:
    data = json.loads(manifest.read_text())
    for name, expected in data['sha256'].items():
        if digest(Path(name)) != expected:
            raise ValueError(f'source runner input changed: {name}')
    if sys.platform == 'darwin':
        raise ValueError('source native runner currently requires the governed hbox execution route')
    if argv[:1] == ['--fn']:
        argv = argv[1:]
    os.chdir(data['world_root'])
    env = dict(os.environ)
    env['ACL2_BOOK_HASH_ALISTP'] = 'NIL'
    env.pop('ACL2_SYSTEM_BOOKS', None)
    env['ACL2_CUSTOMIZATION'] = data['bootstrap']
    env.pop('ACL2_CUSTOMIZATION_QUIET', None)
    env['FN_NATIVE_PROFILE'] = data['profile']
    env['FN_NATIVE_WORLD'] = 'full'
    # ACL2's output channels initialize from these Lisp streams. The native
    # entry opens fd1 separately for protocol output. exec preserves stdin and
    # makes the native owner the signalled/killed process, with no relay PID.
    command = [data['sbcl'], '--tls-limit', '65536', '--dynamic-space-size', '12000',
               '--control-stack-size', '64', '--core', data['core'],
               '--noinform', '--disable-debugger', '--no-userinit',
               '--eval', '(setf *standard-output* *error-output* *trace-output* *error-output*)',
               '--eval', '(acl2::sbcl-restart)', '--end-toplevel-options', '--fn', *argv]
    os.execve(command[0], command, env)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    p = commands.add_parser('prepare')
    for name in ('world-root', 'world-revision', 'source-root', 'output', 'sbcl', 'core'):
        p.add_argument('--' + name, required=True)
    p.add_argument('--source-revision', help='explicit immutable source archive revision')
    p.add_argument('--build', default='host/native/build.lisp')
    p.add_argument('--profile', choices=('developer', 'production'), default='developer')
    p.add_argument('--event', action='append', default=[])
    p = commands.add_parser('run')
    p.add_argument('manifest', type=Path)
    p.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    try:
        if args.action == 'prepare':
            print(prepare(args))
        else:
            run(args.manifest, args.argv[1:] if args.argv[:1] == ['--'] else args.argv)
    except (OSError, ValueError) as error:
        print(f'native source runner refused: {error}', file=sys.stderr)
        return 5
    return 0


if __name__ == '__main__':
    sys.exit(main())
