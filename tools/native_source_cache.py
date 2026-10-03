#!/usr/bin/env python3
"""Checkpoint an initialized source world before any native owner/Store exists.

This is an internal execution cache, not certification or a qualified image.
The ordinary source runner admits the complete prefix and selected events first.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import native_source_runner as runner

ENTRY = '(progn! (set-raw-mode t) (fn-native-entry state))'


def prepare(manifest, output):
    data = json.loads(manifest.read_text())
    for path, expected in data['sha256'].items():
        if runner.digest(Path(path)) != expected:
            raise ValueError('source cache input changed: ' + path)
    output = output.resolve()
    if output.exists() or Path(str(output) + '.core').exists():
        raise ValueError('checkpoint output already exists; choose a fresh cache coordinate')
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists() or Path(str(output) + '.core').exists():
        raise ValueError('execution cache output already exists; prepare a fresh coordinate')
    original = Path(data['bootstrap']).read_text()
    if original.count(ENTRY) != 1 or not original.rstrip().endswith(ENTRY):
        raise ValueError('expected one terminal source entry, before any Store/owner')
    checkpoint = ':q'
    after = '(acl2::save-exec ' + runner.literal(str(output)) + ' "internal source execution cache" :return-from-lp \'(acl2::fn-native-entry acl2::state) :inert-args t :host-lisp-args "--noinform" :toplevel-args "--disable-debugger")'
    bootstrap = output.with_suffix('.checkpoint.lisp')
    bootstrap.write_text(original.replace(ENTRY, checkpoint))
    data['bootstrap'] = str(bootstrap)
    data['sha256'][str(bootstrap)] = runner.digest(bootstrap)
    data['cache_output'] = str(output)
    data['after_acl2_loop'] = after
    data['kind'] = 'initialized source execution cache; no Store/owner, certification or qualification claim'
    target = output.with_suffix('.checkpoint.json')
    target.write_text(json.dumps(data, indent=2) + '\n')
    return target


def seal(manifest, raw_overlays=(), logical_files=()):
    data = json.loads(manifest.read_text())
    output = Path(data['cache_output'])
    core = Path(str(output) + '.core')
    if not output.is_file() or not core.is_file():
        raise ValueError('source checkpoint did not produce both launcher and core')
    for path, expected in data['sha256'].items():
        if runner.digest(Path(path)) != expected:
            raise ValueError('checkpoint input changed: ' + path)
    data['sha256'][str(core)] = runner.digest(core)
    data['sha256'][str(output)] = runner.digest(output)
    for field in ('sbcl', 'core'):
        path = Path(data[field]).resolve()
        data['sha256'][str(path)] = runner.digest(path)
    data['execution_core'] = str(core)
    data['raw_overlays'] = [str(path.resolve()) for path in raw_overlays]
    data['logical_files'] = [str(path.resolve()) for path in logical_files]
    source_loader = Path(__file__).resolve().parents[1] / 'host/native/source-load.lisp'
    if logical_files:
        data['source_loader'] = str(source_loader)
    # The initialized core contains these compiled sources. Rehash the actual
    # execution inputs on restart, rather than rereading unused source files.
    execution = {str(core): data['sha256'][str(core)],
                 str(output): data['sha256'][str(output)],
                 str(Path(data['sbcl']).resolve()): runner.digest(Path(data['sbcl']))}
    for path in (*logical_files, *raw_overlays):
        execution[str(path.resolve())] = runner.digest(path)
    if logical_files:
        execution[str(source_loader)] = runner.digest(source_loader)
    for name in ('FN_MLDSA_LIBRARY', 'FN_DEFLATE_LIBRARY', 'FN_BLAKE3_LIBRARY'):
        if os.environ.get(name):
            path = Path(os.environ[name]).resolve()
            execution[str(path)] = runner.digest(path)
    data['execution_sha256'] = execution
    target = output.with_suffix('.execution.json')
    target.write_text(json.dumps(data, indent=2) + '\n')
    return target


def execute(manifest, argv):
    data = json.loads(manifest.read_text())
    for path, expected in data['execution_sha256'].items():
        if runner.digest(Path(path)) != expected:
            raise ValueError('initialized source input changed: ' + path)
    if sys.platform == 'darwin':
        raise ValueError('source execution cache requires the governed hbox route')
    if argv[:1] == ['--fn']:
        argv = argv[1:]
    os.chdir(data['world_root'])
    env = dict(os.environ, ACL2_CUSTOMIZATION='NONE')
    env.pop('ACL2_SYSTEM_BOOKS', None)
    env['FN_NATIVE_PROFILE'] = data['profile']
    logical = []
    if data.get('logical_files'):
        logical = ['--eval', '(load ' + runner.literal(data['source_loader']) + ')',
                   '--eval', '(acl2::fnn-source-admit-files (quote (' +
                   ' '.join(runner.literal(path) for path in data['logical_files']) + ')))']
    command = [data['sbcl'], '--tls-limit', '65536', '--dynamic-space-size', '12000',
               '--control-stack-size', '64', '--core', data['execution_core'],
               '--noinform', '--disable-debugger', '--no-userinit',
               *logical,
               *[word for path in data.get('raw_overlays', ())
                 for word in ('--eval', '(load ' + runner.literal(path) + ')')],
               '--eval', '(acl2::sbcl-restart)', '--end-toplevel-options', '--fn', *argv]
    os.execve(command[0], command, env)


def initialize(manifest):
    data = json.loads(manifest.read_text())
    for path, expected in data['sha256'].items():
        if runner.digest(Path(path)) != expected:
            raise ValueError('checkpoint input changed: ' + path)
    if sys.platform == 'darwin':
        raise ValueError('source execution cache requires the governed hbox route')
    os.chdir(data['world_root'])
    env = dict(os.environ, ACL2_CUSTOMIZATION='NONE', ACL2_BOOK_HASH_ALISTP='NIL',
               FN_NATIVE_PROFILE=data['profile'], FN_NATIVE_WORLD='full')
    env.pop('ACL2_CUSTOMIZATION_QUIET', None)
    env.pop('ACL2_SYSTEM_BOOKS', None)
    command = [data['sbcl'], '--tls-limit', '65536', '--dynamic-space-size', '12000',
               '--control-stack-size', '64', '--core', data['core'], '--noinform',
               '--disable-debugger', '--no-userinit',
               '--eval', '(setf *standard-output* *error-output* *trace-output* *error-output*)',
               '--eval', '(with-open-file (input ' + runner.literal(data['bootstrap'])
               + ') (let ((*standard-input* input) (*terminal-io* (make-two-way-stream input *error-output*))) (acl2::sbcl-restart)))',
               '--eval', data['after_acl2_loop']]
    os.execve(command[0], command, env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('prepare'); p.add_argument('manifest', type=Path); p.add_argument('output', type=Path)
    p = sub.add_parser('seal'); p.add_argument('manifest', type=Path); p.add_argument('--raw-overlay', action='append', type=Path, default=[]); p.add_argument('--logical-file', action='append', type=Path, default=[])
    p = sub.add_parser('initialize'); p.add_argument('manifest', type=Path)
    p = sub.add_parser('run'); p.add_argument('manifest', type=Path); p.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        if args.command == 'prepare': print(prepare(args.manifest, args.output))
        elif args.command == 'seal': print(seal(args.manifest, args.raw_overlay, args.logical_file))
        elif args.command == 'initialize': initialize(args.manifest)
        else: execute(args.manifest, args.argv[1:] if args.argv[:1] == ['--'] else args.argv)
    except (OSError, ValueError) as error:
        print('source execution cache refused: ' + str(error), file=sys.stderr)
        return 5
    return 0

if __name__ == '__main__':
    sys.exit(main())
