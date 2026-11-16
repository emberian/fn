"""One source-bound leaf lifecycle for proof_repl; allocation stays with its caller.

No remote scheduling, queue, retries, parent authoring, or deadline renewal.
The caller runs this inside its already granted externally timed cgroup.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

import acl2_slots
import acl2_toolchain
import certs


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_sources(root, plan, book):
    with certs.closure_scope():
        closure = certs.closure(root, book)
        for name in closure:
            expected = plan['books'][name]
            if (digest(root / (name + '.lisp')) != expected['sha256'] or
                    certs.closure_key(root, name)[0] != expected['key']):
                raise ValueError('source/key changed: ' + name)
    return set(closure)


def check_cache(root, plan, names, cache, toolchain):
    found = {}
    for name in sorted(names):
        key = plan['books'][name]['key']
        entries = certs.cached_entries(cache, key, lambda meta:
            meta.get('toolchain_identity') == toolchain and
            bool(meta.get('fasl_sha256')) and certs.usable_origin(meta, str(root)))
        chosen = certs.choose_entry(entries, str(root))
        if not chosen:
            raise ValueError('unqualified parent/root (no cold replay): ' + name)
        directory, meta = chosen
        for kind in ('cert', 'fasl', 'port'):
            expected = meta.get(kind + '_sha256')
            if kind != 'port' or expected:
                if not expected or digest(directory / ('book.' + kind)) != expected:
                    raise ValueError('cache payload changed: ' + name + ':' + kind)
        found[name] = {'entry': str(directory), 'key': key}
    return found


def checked_scope(memory_bytes):
    relative = Path('/proc/self/cgroup').read_text().strip().split('::', 1)[1]
    path = Path('/sys/fs/cgroup' + relative)
    if ((path / 'memory.max').read_text().strip() != str(memory_bytes) or
            (path / 'memory.swap.max').read_text().strip() != '0'):
        raise ValueError('effective cgroup does not match granted memory/swap0')
    return str(path)


def session_handles(state, cgroup):
    handles = []
    for field in ('pid', 'acl2_pgid'):
        pid = state[field]
        proc = Path('/proc') / str(pid)
        actual = proc.joinpath('cgroup').read_text().strip().split('::', 1)[1]
        if '/sys/fs/cgroup' + actual != cgroup:
            raise ValueError('session escaped allocated cgroup')
        ticks = proc.joinpath('stat').read_text().rsplit(')', 1)[1].split()[19]
        handles.append({'pid': pid, 'start_ticks': ticks})
    return handles


def require_stopped(handles):
    for handle in handles:
        stat = Path('/proc') / str(handle['pid']) / 'stat'
        if stat.exists() and stat.read_text().rsplit(')', 1)[1].split()[19] == handle['start_ticks']:
            raise ValueError('owned session still live after stop: ' + str(handle['pid']))


def verify_record(root, output, book, toolchain):
    lines = (output / 'record.log').read_text().splitlines()
    paths = [line.split(': ', 1)[1] for line in lines
             if line.startswith('Certification run: ')]
    if len(paths) != 1:
        raise ValueError('record did not identify exactly one manifest')
    path = root / paths[0] / 'manifest.json'
    manifest = json.loads(path.read_text())
    if (manifest['status'] != 'passed' or not manifest['runner_unchanged'] or
            manifest['source_digests_sha256'] != manifest['source_digests_sha256_after'] or
            manifest['acl2_toolchain_identity'] != toolchain or manifest['roots'] != [book]):
        raise ValueError('record manifest changed source, runner, toolchain, or root')
    return str(path)


class Commands:
    def __init__(self, root, output, deadline, receipt, save):
        self.root, self.output, self.deadline = root, output, deadline
        self.receipt, self.save = receipt, save

    def run(self, label, arguments, cleanup=False):
        remaining = self.deadline - time.time()
        if not cleanup and remaining <= 0:
            raise TimeoutError('fixed campaign deadline expired')
        with (self.output / (label + '.log')).open('wb') as log:
            child = subprocess.Popen([sys.executable, *arguments], cwd=self.root,
                                     stdout=log, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            row = {'label': label, 'pid': child.pid, 'argv': arguments}
            self.receipt['commands'].append(row)
            self.save()
            try:
                row['returncode'] = child.wait(timeout=20 if cleanup else remaining)
            finally:
                if child.poll() is None:
                    # Only the group created by this exact Popen, never a name match.
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    child.wait(timeout=10)
                row['returncode'] = child.returncode
                self.save()
        if row['returncode']:
            raise RuntimeError(label + ' refused; see ' + str(self.output / (label + '.log')))


def qualify(args, repl):
    root = repl.ROOT.resolve()
    book = repl.normalize_book(args.book)
    plan = json.loads(args.plan.read_text())
    output = args.output.resolve()
    # Refuse reused output/session ownership; a failed run is never overwritten.
    output.mkdir(parents=True, exist_ok=False)
    name = 'leaf_' + str(os.getpid()) + '_' + uuid.uuid4().hex[:12]
    receipt = {'book': book, 'source': plan['source'], 'session': name,
               'deadline': args.deadline, 'commands': [], 'status': 'preflight'}
    def save():
        (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    commands = Commands(root, output, args.deadline, receipt, save)
    if args.memory_bytes <= 0 or args.event_steps <= 0 or args.event_seconds <= 0:
        raise ValueError('positive memory and original-event limits required')
    previous_handlers = {}
    def interrupted(signum, frame):
        raise RuntimeError('interrupted by signal ' + str(signum))
    for signum in (signal.SIGTERM, signal.SIGINT):
        previous_handlers[signum] = signal.signal(signum, interrupted)
    attempted = False
    stopped = False
    try:
        if time.time() >= args.deadline:
            raise TimeoutError('fixed campaign deadline expired')
        receipt['cgroup'] = checked_scope(args.memory_bytes)
        os.environ.update(acl2_slots.acl2_environment(root=root))
        os.environ['FN_REPL_STEP_LIMIT'] = str(args.event_steps)
        os.environ['FN_CERT_IMAGES'] = 'off'
        identity = acl2_toolchain.fingerprint(Path(os.environ['FN_ACL2']))
        expected = plan.get('toolchain', plan.get('toolchain_identity'))
        if not expected or not identity.qualified or identity.identity != expected:
            raise ValueError('launcher toolchain does not match source plan')
        cache = Path(os.environ['FN_CERT_CACHE'])
        closure = check_sources(root, plan, book)
        parents = closure - {book}
        receipt['parents'] = check_cache(root, plan, parents, cache, expected)
        imports, exports = repl.warm_entry_books(root, sorted(parents))
        if set(exports) != parents:
            raise ValueError('ENTRY exports differ from actual qualified parents')
        entry = root / 'build' / (name + '.lisp')
        entry.parent.mkdir(exist_ok=True)
        entry.write_text('(in-package "ACL2")\n' + ''.join(
            '(include-book "../' + parent + '")\n' for parent in imports))
        receipt['entry'] = {'path': str(entry), 'imports': imports, 'exports': sorted(exports)}
        if repl.read_state(name) or repl.lock_holder(name).get('pid'):
            raise ValueError('session already owned')
        attempted = True
        commands.run('start', ['tools/proof_repl.py', 'start', name,
            str(entry.relative_to(root).with_suffix('')), '--cached-only',
            '--load-limit', str(args.event_seconds), '--limit', str(args.event_seconds),
            '--load-timeout', '120', '--idle-timeout', '5'])
        receipt['session_handles'] = session_handles(repl.read_state(name), receipt['cgroup'])
        save()
        commands.run('author', ['tools/proof_repl.py', 'send-range', name, book,
            '--skip-includes', '--ld-local', '--per-event-steps', str(args.event_steps),
            '--limit', str(args.event_seconds)])
        commands.run('stop', ['tools/proof_repl.py', 'stop', name], cleanup=True)
        require_stopped(receipt['session_handles'])
        stopped = True
        check_sources(root, plan, book)
        check_cache(root, plan, parents, cache, expected)
        receipt['status'] = 'author-ready'
        save()
        commands.run('record', ['tools/certify_books.py', book, '--incremental',
            '--cached-parents', '--jobs', '1', '--origin-kind', 'run', '--timeout-seconds',
            str(max(1, int(args.deadline - time.time())))])
        check_sources(root, plan, book)
        receipt['manifest'] = verify_record(root, output, book, expected)
        receipt['qualified'] = check_cache(root, plan, closure, cache, expected)
        receipt['status'] = 'qualified'
        return 0
    except (OSError, ValueError, KeyError, RuntimeError, TimeoutError, subprocess.TimeoutExpired) as error:
        receipt['status'] = 'refused'
        receipt['error'] = str(error)
        print(error, file=sys.stderr)
        return 1
    finally:
        if attempted and not stopped:
            try:
                commands.run('cleanup', ['tools/proof_repl.py', 'stop', name], cleanup=True)
            except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
                receipt['cleanup_error'] = str(error)
        save()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)
