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
    output.parent.mkdir(parents=True, exist_ok=True)
    original = Path(data['bootstrap']).read_text()
    if original.count(ENTRY) != 1 or not original.rstrip().endswith(ENTRY):
        raise ValueError('expected one terminal source entry, before any Store/owner')
    checkpoint = '(progn! (set-raw-mode t) (save-exec ' + runner.literal(str(output)) + ' "internal source execution cache" :return-from-lp \'(fn-native-entry state) :inert-args t :host-lisp-args "--noinform" :toplevel-args "--disable-debugger"))'
    bootstrap = output.with_suffix('.checkpoint.lisp')
    bootstrap.write_text(original.replace(ENTRY, checkpoint))
    data['bootstrap'] = str(bootstrap)
    data['sha256'][str(bootstrap)] = runner.digest(bootstrap)
    data['cache_output'] = str(output)
    data['kind'] = 'initialized source execution cache; no Store/owner, certification or qualification claim'
    target = output.with_suffix('.checkpoint.json')
    target.write_text(json.dumps(data, indent=2) + '\n')
    return target


def seal(manifest):
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
    data['execution_core'] = str(core)
    target = output.with_suffix('.execution.json')
    target.write_text(json.dumps(data, indent=2) + '\n')
    return target


def execute(manifest, argv):
    data = json.loads(manifest.read_text())
    for path, expected in data['sha256'].items():
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
    command = [data['sbcl'], '--tls-limit', '65536', '--dynamic-space-size', '12000',
               '--control-stack-size', '64', '--core', data['execution_core'],
               '--noinform', '--disable-debugger', '--no-userinit',
               '--eval', '(acl2::sbcl-restart)', '--end-toplevel-options', '--fn', *argv]
    os.execve(command[0], command, env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('prepare'); p.add_argument('manifest', type=Path); p.add_argument('output', type=Path)
    p = sub.add_parser('seal'); p.add_argument('manifest', type=Path)
    p = sub.add_parser('run'); p.add_argument('manifest', type=Path); p.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        if args.command == 'prepare': print(prepare(args.manifest, args.output))
        elif args.command == 'seal': print(seal(args.manifest))
        else: execute(args.manifest, args.argv[1:] if args.argv[:1] == ['--'] else args.argv)
    except (OSError, ValueError) as error:
        print('source execution cache refused: ' + str(error), file=sys.stderr)
        return 5
    return 0

if __name__ == '__main__':
    sys.exit(main())
