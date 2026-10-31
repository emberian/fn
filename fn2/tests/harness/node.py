"""The one Node adapter. See the generated layer-D requirements below."""
import functools
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import time
import threading
from typing import Protocol

import tests.native_harness as fn1
from . import inventory

ROOT = Path(__file__).resolve().parents[3]
INVENTORY = inventory.load()
ORIGINAL_NODE = fn1.Node

__doc__ = 'What layer D must provide (top 40 inventory requirements by modules):\n' + '\n'.join(
    f"{r['modules']:3} modules | {r['kind']} | {r['value']}"
    for r in sorted(INVENTORY['aggregates']['host_requirements'],
                    key=lambda r: (-r['modules'], r['kind'], r['value']))[:40])

# Explicit dispositions of the inventory's config_keys union. 'dynamic' is
# an unresolved inventory expression, not an accepted TOML key. No inferred
# config defaults or host policy: these are fixture name translations only.
CONFIG_KEYS = {
    'store.path': 'keep', 'listener.host': 'keep', 'listener.port': 'keep',
    'control.path': 'keep', 'auth.protected_only': 'keep',
    'listener.tls_cert': 'keep', 'listener.tls_key': 'keep', 'dynamic': 'keep',
    'auth.required': 'keep', 'log.path': 'keep', 'auth.path': 'keep',
    'listener.tls_port': 'keep', 'web.port': 'keep', 'web.site': 'keep',
    'resources.cold_descriptors': 'replace(profile.cold_descriptors)',
    'resources.cold_file_ids': 'replace(profile.cold_file_ids)',
    'resources.cold_heap_octets': 'replace(profile.cold_heap_octets)',
    'resources.cold_read_ids': 'replace(profile.cold_read_ids)',
    'resources.cold_workers': 'replace(profile.cold_workers)',
    'resources.output_heap_octets': 'replace(profile.output_heap_octets)',
    'resources.output_quantum_heap_octets': 'replace(profile.output_quantum_heap_octets)',
    'resources.reclaim_live': 'replace(profile.reclaim_live)',
    'tls.key_exchange': 'keep', 'web.domain': 'keep',
}


class NodeInterface(Protocol):
    """Structural interface; concrete backends also retain fn1's full surface.

    Counts are module unions over all 120 inventory modules, not assertions.
    """
    def start(self, **options):
        """120 modules: fn1 Node.start / launch, operator CONFIG run."""
        ...

    def stop(self, expect=fn1.EXIT.OK, **options):
        """120 modules: fn1 Node.stop(expect), SIGTERM, reap, exit class."""
        ...

    @property
    def config(self) -> Path:
        """119 modules: fn1 Node.config / write_config, inventoried fn.toml keys."""
        ...

    @property
    def socket(self):
        """110 modules: fn1 port, tls_port and session() -> Client (this node)."""
        ...

    @property
    def control(self):
        """120 modules: fn1 control path; operator/store/invoke/init/post verbs."""
        ...

    def kill_at(self, cut, **options):
        """49 modules: start(env={FN_NATIVE_CONTROL_FAULT: cut}), death_cut/died_at."""
        ...

    def observe(self):
        """120 modules: process stdout/stderr, LISTENING/-WEB, CONTROL, exit class."""
        ...


_ids = itertools.count()
_emit_lock = threading.Lock()
_ports = {}


def unique_id():
    return f'{os.getpid()}:{next(_ids)}'


def node_fields(node):
    fields = dict(node=str(node.root), control=str(node.control) if node.control else None)
    for port in (node.port, node.tls_port):
        if port is not None:
            _ports[port] = fields
    return fields


def snapshots(words):
    files = {}
    for word in words:
        try:
            path = Path(word)
            if not path.is_file():
                continue
            with path.open('rb') as stream:
                data = stream.read(65537)
                if len(data) <= 65536:
                    files[word] = data.hex()
                else:
                    digest, size = hashlib.sha256(data), len(data)
                    for chunk in iter(lambda: stream.read(65536), b''):
                        digest.update(chunk)
                        size += len(chunk)
                    files[word] = dict(sha256=digest.hexdigest(), length=size)
        except (OSError, ValueError):
            continue
    return files


def sent(octets):
    if len(octets) <= 1 << 20:
        return dict(sent_hex=octets.hex())
    return dict(sent_hex=octets[:65536].hex(), sent_len=len(octets),
                sent_sha256=hashlib.sha256(octets).hexdigest())


def emit(kind, phase, **fields):
    directory = os.environ.get('FN2_OBSERVE_DIR')
    if not directory:
        return
    test = os.environ.get('FN2_TEST_ID') or fn1.current_test_id() or 'fixture'
    path = Path(directory) / (re.sub(r'[^A-Za-z0-9_.-]', '_', test) + '.jsonl')
    path.parent.mkdir(parents=True, exist_ok=True)
    with _emit_lock, path.open('a', encoding='utf-8') as output:
        output.write(json.dumps(dict(t=time.monotonic_ns(), test=test, kind=kind,
                                     phase=phase, **fields)) + '\n')


def observed(kind, fields=lambda *a, **k: {}, result=lambda value: {}):
    """No extra reads or transformations when observation is disabled."""
    def decorate(call):
        @functools.wraps(call)
        def wrapped(*args, **kwargs):
            if not os.environ.get('FN2_OBSERVE_DIR'):
                return call(*args, **kwargs)
            before = dict(call=unique_id()) | fields(*args, **kwargs)
            if args and isinstance(args[0], ORIGINAL_NODE):
                before.update(node_fields(args[0]))
            elif kind.startswith('client.'):
                before.update(args[0]._observation)
            words = before.get('words') if kind in {'invoke', 'operator', 'store'} else None
            if words is not None:
                before['files_before'] = snapshots(words)
            emit(kind, 'invoke', **before)
            try:
                value = call(*args, **kwargs)
            except BaseException as error:
                if kind in {'node.start', 'node.try_start', 'node.start_store_owner'}:
                    args[0]._watch_process(args[0].process, kwargs)
                if words is not None:
                    before['files_after'] = snapshots(words)
                emit(kind, 'info', **before, exception=str(error))
                raise
            after = {'files_after': snapshots(words)} if words is not None else {}
            after.update(result(value))
            emit(kind, 'fail' if after.get('exit_code', 0) not in (0, None) else 'ok',
                 **(before | after))
            return value
        return wrapped
    return decorate


def completed(result):
    def prefix(value):
        octets = value.encode('utf-8') if isinstance(value, str) else value or b''
        return octets[:4096].decode('utf-8', 'replace')
    return dict(exit_code=result.returncode, exit_class=fn1.outcome_name(result.returncode),
                stdout=prefix(result.stdout), stderr=prefix(result.stderr))


def process_fields(process):
    if process is None:
        return dict(pid=None, argv=[], exit_class=None)
    status = process.poll()
    return dict(pid=process.pid, argv=list(map(str, process.process.args)), exit_code=status,
                exit_class=fn1.outcome_name(status) if status is not None else None,
                stdout=process.stdout.since(0).decode('utf-8', 'replace'),
                stderr=process.stderr.since(0).decode('utf-8', 'replace'))


class Fn1Backend(ORIGINAL_NODE):
    """The real fn1 Node, with optional observation and structural aliases."""
    @functools.wraps(ORIGINAL_NODE.__init__)
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        if os.environ.get('FN2_OBSERVE_DIR'):
            node_fields(self)

    def _start_fields(self, options):
        env = self.environment(options.get('env'))
        cut = options.get('death_cut')
        return dict(env_selectors={k: v for k, v in env.items() if k.startswith('FN_NATIVE_')
                    and any(s in k for s in ('FAULT', 'CUT', 'DEATH', 'TEST'))},
                    **({'death_cut': [cut[0], cut[1].decode('ascii')]} if cut else {}))

    def _watch_process(self, process, options):
        if not isinstance(process, fn1.NativeProcess) or getattr(process, '_fn2_watched', False):
            return
        process._fn2_watched = True
        context = node_fields(self) | self._start_fields(options)
        original_signal = process.signal
        def signal(number):
            if os.environ.get('FN2_OBSERVE_DIR'):
                context['signal'] = int(number)
            return original_signal(number)
        process.signal = observed('node.signal', lambda number: context | dict(signal=int(number))
                                  | process_fields(process), lambda _: process_fields(process))(signal)
        process.finish = observed('node.exit', lambda: context | process_fields(process),
                                 lambda _: context | process_fields(process))(process.finish)

    @property
    def socket(self):
        return self

    def kill_at(self, cut, **options):
        env = dict(options.pop('env', {}) or {})
        env['FN_NATIVE_CONTROL_FAULT'] = cut
        return self.start(env=env, **options)

    def observe(self):
        return process_fields(self.process)

    def session(self, **options):
        if os.environ.get('FN2_OBSERVE_DIR'):
            node_fields(self)
        return super().session(**options)

    @observed('node.start', lambda self, **kw: dict(
        pid=None, argv=list(map(str, self.argv(kw.get('image'),
                         ('operator', self.config, *kw.get('verb', ('run',)))))),
        exit_class=None) | self._start_fields(kw), process_fields)
    def start(self, **options):
        process = super().start(**options)
        if os.environ.get('FN2_OBSERVE_DIR'):
            self._watch_process(process, options)
        return process

    @observed('node.try_start', lambda self, **kw: dict(
        argv=list(map(str, self.argv(kw.get('image'), ('operator', self.config, 'run')))),
        pid=None, exit_class=None) | self._start_fields(kw), lambda answer: process_fields(answer[0]))
    def try_start(self, **options):
        answer = super().try_start(**options)
        if os.environ.get('FN2_OBSERVE_DIR'):
            self._watch_process(answer[0], options)
        return answer

    @observed('node.start_store_owner', lambda self, **kw: dict(
        argv=list(map(str, self.argv(kw.get('image'), ('owner', 'run', self.store_path)))),
        pid=None, exit_class=None), lambda answer: process_fields(answer[0]))
    def start_store_owner(self, **options):
        answer = super().start_store_owner(**options)
        if os.environ.get('FN2_OBSERVE_DIR'):
            self._watch_process(answer[0], options)
            _ports[answer[1]] = node_fields(self)
        return answer

    @observed('node.stop', lambda self, *a, **kw: dict(requested_signal=15) | process_fields(
        (a[1] if len(a) > 1 else kw.get('process')) or self.process),
              lambda status: dict(exit_code=status, exit_class=fn1.outcome_name(status),
                                  signal=-status if status is not None and status < 0 else None))
    def stop(self, *args, **options):
        return super().stop(*args, **options)

    @observed('invoke', lambda self, *words, **kw: dict(words=list(map(str, words))), completed)
    def invoke(self, *words, **options):
        return super().invoke(*words, **options)

    @observed('operator', lambda self, *words, **kw: dict(words=list(map(str, words))), completed)
    def operator(self, *words, **options):
        return super().operator(*words, **options)

    @observed('store', lambda self, *words, **kw: dict(words=list(map(str, words))), completed)
    def store(self, *words, **options):
        return super().store(*words, **options)


def unavailable(operation, requirement, **fields):
    if os.environ.get('FN2_OBSERVE_DIR'):
        fields['call'] = unique_id()
    emit(operation, 'invoke', requirement=requirement, **fields)
    try:
        fn1.node_dead(f'fn2 layer D not yet serving: {operation} needs {requirement}')
    except fn1.NodeDead as error:
        emit(operation, 'info', exception=str(error), **fields)
        raise


# The served fn2 node (A5r, f794c78f3): `tools/acl2 < fn2/tests/native-serve.lsp` with the listener in the
# environment; `LISTENING <port>` once bound; SIGTERM/SIGINT to its process group ends it with `STOPPED <reason>`
# and exit 0; `REFUSED <word>` and exit 2 for a refused configuration. Its profile is D's served profile: the
# fixture's fn.toml supplies only the listener, so a key the served node would not read is a named requirement.
NATIVE_SERVE = ROOT / 'fn2' / 'tests' / 'native-serve.lsp'
SERVED_KEYS = {('store', 'path'), ('listener', 'host'), ('listener', 'port'), ('control', 'path')}


class Fn2Process(fn1.NativeProcess):
    """The served node's session: tools/acl2 is a wrapper whose child is SBCL, so a signal goes to the group
    whose leader this process is (started with start_new_session), never to the wrapper's PID alone."""
    def signal(self, number):
        if self.process.poll() is None:
            try:
                os.killpg(self.pid, number)
            except ProcessLookupError:
                pass


class Fn2Backend(Fn1Backend):
    """The served fn2 node on a configured listener (start/stop/session); every other execution entry names
    the missing host contract.

    Inherits fn1's exact constructor, scratch cleanup, and nonexecution helpers.
    """
    def write_config(self, *, listener=True, tls=None, extra='', protected_only=False):
        super().write_config(listener=listener, tls=tls, extra=extra,
                             protected_only=protected_only)
        # Preserve the fixture text byte-for-byte except the table name.
        text = self.config.read_text(encoding='utf-8')
        self.config.write_text(re.sub(r'(?m)^\[resources\](?=\s*(?:#.*)?$)',
                                      '[profile]', text), encoding='utf-8')

    def launch(self, image, words, env):
        return self.argv(image, words), self.environment(env)

    def _served_listener(self, options):
        """The listener the served node takes from this fixture, or the named requirement it cannot meet."""
        import tomllib
        config = tomllib.loads(self.config.read_text(encoding='utf-8'))
        unread = sorted(f'{table}.{key}' for table, values in config.items()
                        for key in (values if isinstance(values, dict) else {'': values})
                        if (table, key) not in SERVED_KEYS)
        refusals = [
            (tuple(options.get('verb', ('run',))) != ('run',),
             'operator CONFIG ' + ' '.join(map(str, options.get('verb') or ()))),
            (options.get('death_cut') is not None or 'FN_NATIVE_CONTROL_FAULT' in (options.get('env') or {}),
             'a process-death cut (FN_NATIVE_CONTROL_FAULT, death_cut)'),
            (options.get('intent', 'serve') != 'serve', f"start intent {options.get('intent')}"),
            (self.port is None, 'a node without a plain listener'),
            (self.tls_port is not None, 'an implicit-TLS listener (listener.tls_port)'),
            (bool(unread), 'fn.toml keys the served profile does not read: ' + ', '.join(unread)),
            (config.get('listener', {}).get('host', '127.0.0.1') != '127.0.0.1', 'a listener host other than 127.0.0.1'),
        ]
        for refused, requirement in refusals:
            if refused:
                unavailable('start', requirement, pid=None, exit_class=None,
                            argv=['tools/acl2', '<', str(NATIVE_SERVE)])
        return dict(FN2_LISTENER_PORT=str(self.port), FN2_LISTENER_ADDRESS='127.0.0.1')

    def start(self, **options):
        """`tools/acl2 < fn2/tests/native-serve.lsp` on this node's port, in its own session; one PID file
        per start (ROOT/fn2-node-N.pid, the session leader) beside the fixture; returned at `LISTENING`."""
        return self._serve(self._served_listener(options), **options)

    @observed('node.start', lambda self, listener, **kw: dict(pid=None, argv=['tools/acl2', '<', str(NATIVE_SERVE)],
                                                              exit_class=None), process_fields)
    def _serve(self, listener, *, ready=b'LISTENING ', timeout=180, limit=fn1.DEFAULT_LIMIT, **options):
        env = dict(os.environ, **{k: str(v) for k, v in (options.get('env') or {}).items() if v is not None},
                   **listener)
        argv = [str(ROOT / 'tools' / 'acl2')]
        with NATIVE_SERVE.open('rb') as script:
            popen = subprocess.Popen(argv, cwd=ROOT, env=env, stdin=script, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, bufsize=0, start_new_session=True)
        process = Fn2Process(popen, limit=limit)
        (self.root / f'fn2-node-{len(self.processes)}.pid').write_text(f'{popen.pid}\n')
        fn1._register(argv + ['native-serve'], process)
        self.processes.append(process)
        self.process = process
        try:
            line = process.announcement(ready, timeout=timeout)
            if ready == b'LISTENING ':
                self.case.assertEqual(line, f'LISTENING {self.port}\n'.encode(),
                                      f'{self.name} announced {line!r}')
        except AssertionError as error:
            fn1.node_dead(error)
        fn1.require_node_greeting(process, self.port, config=self.config)
        if os.environ.get('FN2_OBSERVE_DIR'):
            self._watch_process(process, options)
        return process

    def try_start(self, **options):
        unavailable('try_start', 'operator CONFIG run; LISTENING or a named startup refusal')

    def invoke(self, *words, **options):
        unavailable('invoke', 'fn --fn ' + ' '.join(map(str, words)), words=list(map(str, words)))

    def operator(self, *words, **options):
        unavailable('operator', 'operator CONFIG ' + ' '.join(map(str, words)) + '; FNCT control socket',
                    words=list(map(str, words)))

    def store(self, *words, **options):
        unavailable('store', 'store STORE ' + ' '.join(map(str, words)), words=list(map(str, words)))

    def init(self, *groups, **options):
        unavailable('init', 'operator CONFIG init [--profile P] GROUP...: the served profile carries no '
                    'groups until D6 (GROUP answers the interim 503)')

    def post(self, *args, **options):
        unavailable('post', 'operator CONFIG post --message-id ID --payload PATH --group GROUP')

    def start_store_owner(self, **options):
        unavailable('start_store_owner', 'owner run STORE 0 ONCE N [FAULT]; LISTENING PORT')

    def kill_at(self, cut, **options):
        unavailable('kill_at', f'FN_NATIVE_CONTROL_FAULT={cut}; death_cut status/marker and died_at')

    def session(self, **options):
        if self.process is None or self.process.poll() is not None:
            unavailable('socket', 'a started served node: NNTP 200/201 greeting on listener.port')
        return super().session(**options)


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Node adapter contract')
    parser.add_argument('--requirements', action='store_true', required=True)
    parser.parse_args()
    print(__doc__)
