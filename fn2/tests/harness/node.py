"""The one Node adapter. See the generated layer-D requirements below."""
import functools
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import time
from typing import Protocol

ROOT = Path(__file__).resolve().parents[3]
INVENTORY = json.loads(Path(__file__).with_name('natives-inventory.json').read_text())


def load_fn1():
    """Load the original file once, independently of the installed import shim."""
    name = 'fn1_native_harness'
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, ROOT / 'tests/native_harness.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    return sys.modules[name]


fn1 = load_fn1()
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


def emit(kind, phase, **fields):
    directory = os.environ.get('FN2_OBSERVE_DIR')
    if not directory:
        return
    test = os.environ.get('FN2_TEST_ID') or fn1.current_test_id() or 'fixture'
    path = Path(directory) / (re.sub(r'[^A-Za-z0-9_.-]', '_', test) + '.jsonl')
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a', encoding='utf-8') as output:
        output.write(json.dumps(dict(t=time.monotonic_ns(), test=test, kind=kind,
                                     phase=phase, **fields)) + '\n')


def observed(kind, fields=lambda *a, **k: {}, result=lambda value: {}):
    """No extra reads or transformations when observation is disabled."""
    def decorate(call):
        @functools.wraps(call)
        def wrapped(*args, **kwargs):
            if not os.environ.get('FN2_OBSERVE_DIR'):
                return call(*args, **kwargs)
            before = fields(*args, **kwargs)
            emit(kind, 'invoke', **before)
            try:
                value = call(*args, **kwargs)
            except BaseException as error:
                emit(kind, 'info', **before, exception=str(error))
                raise
            after = result(value)
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
    return dict(pid=process.pid, argv=list(map(str, process.process.args)),
                exit_class=fn1.outcome_name(process.poll()) if process.poll() is not None else None,
                stdout=process.stdout.since(0).decode('utf-8', 'replace'),
                stderr=process.stderr.since(0).decode('utf-8', 'replace'))


class Fn1Backend(fn1.Node):
    """The real fn1 Node, with optional observation and structural aliases."""
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
        # fn1.Node.session closes over its original module's Client.
        from .shim import Client
        return Client(self.port, **options)

    @observed('node.start', lambda self, **kw: dict(
        pid=None, argv=list(map(str, self.argv(kw.get('image'),
                         ('operator', self.config, *kw.get('verb', ('run',)))))),
        exit_class=None), process_fields)
    def start(self, **options):
        return super().start(**options)

    @observed('node.try_start', lambda self, **kw: dict(
        argv=list(map(str, self.argv(kw.get('image'), ('operator', self.config, 'run')))),
        pid=None, exit_class=None), lambda answer: process_fields(answer[0]))
    def try_start(self, **options):
        return super().try_start(**options)

    @observed('node.start_store_owner', lambda self, **kw: dict(
        argv=list(map(str, self.argv(kw.get('image'), ('owner', 'run', self.store_path)))),
        pid=None, exit_class=None), lambda answer: process_fields(answer[0]))
    def start_store_owner(self, **options):
        return super().start_store_owner(**options)

    @observed('node.stop', lambda self, *a, **kw: process_fields(kw.get('process') or self.process),
              lambda status: dict(exit_code=status, exit_class=fn1.outcome_name(status)))
    def stop(self, *args, **options):
        return super().stop(*args, **options)

    def stop_all(self):
        if not os.environ.get('FN2_OBSERVE_DIR'):
            return super().stop_all()
        for process in self.processes:
            emit('node.stop', 'invoke', **process_fields(process))
        try:
            super().stop_all()
        except BaseException as error:
            emit('node.stop', 'info', exception=str(error))
            raise
        for process in self.processes:
            emit('node.stop', 'ok' if process.returncode == 0 else 'fail',
                 **process_fields(process))

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
    emit(operation, 'invoke', requirement=requirement, **fields)
    try:
        fn1.node_dead(f'fn2 layer D not yet serving: {operation} needs {requirement}')
    except fn1.NodeDead as error:
        emit(operation, 'info', exception=str(error), **fields)
        raise


class Fn2Backend(Fn1Backend):
    """Scratch fixtures only; every execution entry names the missing host contract.

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

    def start(self, **options):
        unavailable('start', 'fn --fn operator CONFIG run; CONTROL path, LISTENING PORT / '
                    'LISTENING-WEB PORT and an NNTP/control/HTTP greeting; '
                    f"selectors={options.get('env', {})}, death_cut={options.get('death_cut')}",
                    pid=None, exit_class=None, argv=list(map(str, self.argv(options.get('image'),
                        ('operator', self.config, *options.get('verb', ('run',)))))))

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
        unavailable('init', 'operator CONFIG init [--profile P] GROUP...')

    def post(self, *args, **options):
        unavailable('post', 'operator CONFIG post --message-id ID --payload PATH --group GROUP')

    def start_store_owner(self, **options):
        unavailable('start_store_owner', 'owner run STORE 0 ONCE N [FAULT]; LISTENING PORT')

    def kill_at(self, cut, **options):
        unavailable('kill_at', f'FN_NATIVE_CONTROL_FAULT={cut}; death_cut status/marker and died_at')

    def session(self, **options):
        unavailable('socket', 'NNTP 200/201 greeting on listener.port / listener.tls_port')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description='Node adapter contract')
    parser.add_argument('--requirements', action='store_true', required=True)
    parser.parse_args()
    print(__doc__)
