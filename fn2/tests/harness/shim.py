"""Installed as tests.native_harness before any carried native module imports."""
import importlib as _importlib
import os as _os
import sys as _sys
from . import node as _node

_fn1 = _node.load_fn1()
globals().update({name: value for name, value in vars(_fn1).items() if not name.startswith('_')})


class Client(_fn1.Client):
    """fn1's exact constructor and protocol, with optional exchange records."""
    @_node.observed('client.command', lambda self, text: dict(
        command_hex=(text.encode('utf-8') if isinstance(text, str) else text).hex()),
        lambda reply: dict(reply_hex=reply.hex()))
    def command(self, text):
        return super().command(text)

    @_node.observed('client.line', result=lambda reply: dict(reply_hex=reply.hex()))
    def line(self, limit=None):
        return super().line(limit=limit)

    @_node.observed('client.block', result=lambda reply: dict(reply_hex=reply.hex()))
    def block(self):
        return super().block()


def __getattr__(name):
    # Some carried modules explicitly import private parser/drain helpers.
    # Preserve those imports without copying the original module metadata.
    return getattr(_fn1, name)


def _host():
    return Path(_os.environ.get('FN2_HOST', str(_node.ROOT / 'fn2/host/fn')))


def _native_image(variable, default=None):
    return _host()


def _executable(image):
    return Path(image).resolve() == _host().resolve() or _fn1.executable(image)


def _requires(*images):
    import unittest
    absent = [str(image) for image in images if not _executable(image)]
    return unittest.skipUnless(not absent, 'native image required: ' + ', '.join(absent))


def _run(argv, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        _node.unavailable('invoke', ' '.join(map(str, argv)))
    return _fn1.run(argv, **options)


def _start(argv, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        _node.unavailable('start', ' '.join(map(str, argv)) + '; LISTENING and first response')
    return _fn1.start(argv, **options)


def _start_filed(argv, log_path, **options):
    if argv and Path(argv[0]).resolve() == _host().resolve():
        _node.unavailable('start_filed', ' '.join(map(str, argv)) + '; drained announcements')
    return _fn1.start_filed(argv, log_path, **options)


def install(backend=None):
    """Both import spellings must resolve to this same module object."""
    backend = backend or _os.environ.get('FN2_NODE_BACKEND', 'fn1')
    if backend not in ('fn1', 'fn2'):
        raise ValueError('unknown Node backend: ' + backend)
    replacements = dict(Node=_node.Fn1Backend, native_image=_fn1.native_image,
                        executable=_fn1.executable, requires=_fn1.requires,
                        run=_fn1.run, start=_fn1.start, start_filed=_fn1.start_filed,
                        installed_launcher=_fn1.installed_launcher)
    if backend == 'fn2':
        replacements.update(Node=_node.Fn2Backend, native_image=_native_image,
                            executable=_executable, requires=_requires, run=_run,
                            start=_start, start_filed=_start_filed,
                            installed_launcher=lambda image: _host())
    globals().update(replacements)
    package = _importlib.import_module('tests')
    module = _sys.modules[__name__]
    _sys.modules['tests.native_harness'] = module
    package.native_harness = module
    return module


install()
