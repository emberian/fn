"""Explicit, reversible adapters on the real tests.native_harness module."""
import functools
import os
from pathlib import Path
import unittest

import tests.native_harness as native_harness
from . import node

ORIGINAL_CLIENT = native_harness.Client


class Client(ORIGINAL_CLIENT):
    """fn1's exact constructor and protocol, with optional exchange records."""
    @functools.wraps(ORIGINAL_CLIENT.__init__)
    def __init__(self, port, **options):
        if not os.environ.get('FN2_OBSERVE_DIR'):
            super().__init__(port, **options)
            return
        self._observation = dict(conn=node.unique_id(),
            **node._ports.get(port, dict(node=f'port:{port}', control=None)))
        self._connect(port, **options)

    _connect = node.observed('client.connect')(ORIGINAL_CLIENT.__init__)
    send = node.observed('client.send', lambda self, octets: node.sent(octets))(ORIGINAL_CLIENT.send)
    post = node.observed('client.post', result=lambda reply: dict(
        replies_hex=[r.hex() if r is not None else None for r in reply]))(ORIGINAL_CLIENT.post)
    multiline = node.observed('client.multiline', result=lambda reply: dict(
        replies_hex=[r.hex() for r in reply]))(ORIGINAL_CLIENT.multiline)
    starttls = node.observed('client.starttls', result=lambda reply: dict(
        reply_hex=reply.hex()))(ORIGINAL_CLIENT.starttls)
    close = node.observed('client.close')(ORIGINAL_CLIENT.close)

    @node.observed('client.command', lambda self, text: dict(
        command_hex=(text.encode('utf-8') if isinstance(text, str) else text).hex()),
        lambda reply: dict(reply_hex=reply.hex()))
    def command(self, text):
        return super().command(text)

    @node.observed('client.line', result=lambda reply: dict(reply_hex=reply.hex()))
    def line(self, limit=None):
        return super().line(limit=limit)

    @node.observed('client.block', result=lambda reply: dict(reply_hex=reply.hex()))
    def block(self):
        return super().block()


def _host():
    return Path(os.environ.get('FN2_HOST', str(node.ROOT / 'fn2/host/fn')))


def _native_image(variable, default=None):
    return _host()


def _executable(image):
    return Path(image).resolve() == _host().resolve() or ORIGINALS['executable'](image)


def _requires(*images):
    absent = [str(image) for image in images if not _executable(image)]
    return unittest.skipUnless(not absent, 'native image required: ' + ', '.join(absent))


def _run(argv, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        node.unavailable('invoke', ' '.join(map(str, argv)))
    return ORIGINALS['run'](argv, **options)


def _start(argv, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        node.unavailable('start', ' '.join(map(str, argv)) + '; LISTENING and first response')
    return ORIGINALS['start'](argv, **options)


def _start_filed(argv, log_path, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        node.unavailable('start_filed', ' '.join(map(str, argv)) + '; drained announcements')
    return ORIGINALS['start_filed'](argv, log_path, **options)


def _installed_launcher(image):
    return _host()


# Every mutation of fn1's module is declared here. Helpers stay original on fn1.
PATCH_POINTS = {
    'Node': {'fn1': node.Fn1Backend, 'fn2': node.Fn2Backend},
    'Client': {'fn1': Client, 'fn2': Client},
    'native_image': {'fn2': _native_image},
    'executable': {'fn2': _executable},
    'requires': {'fn2': _requires},
    'run': {'fn2': _run},
    'start': {'fn2': _start},
    'start_filed': {'fn2': _start_filed},
    'installed_launcher': {'fn2': _installed_launcher},
}
ORIGINALS = {name: getattr(native_harness, name) for name in PATCH_POINTS}
_installed_originals = {}


def install(backend):
    """Apply one backend; runners own the matching uninstall in a finally block."""
    if backend not in ('fn1', 'fn2'):
        raise ValueError('unknown Node backend: ' + backend)
    uninstall()
    for name, replacements in PATCH_POINTS.items():
        if backend in replacements:
            _installed_originals[name] = getattr(native_harness, name)
            setattr(native_harness, name, replacements[backend])
    return native_harness


def uninstall():
    """Restore exactly the values present before the current installation."""
    for name, original in _installed_originals.items():
        setattr(native_harness, name, original)
    _installed_originals.clear()
