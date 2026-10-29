"""Preserve the first live observation before Hypothesis tries to replay it.

Adapters must call record_failure before raising their assertion. The outer
context only adds a pointer: it cannot reconstruct a lost observation. The four
live machines (nntp, consumer, tls_auth, config_limits) call it.
Fake tests can use the same hooks without writing artifacts (a plain TestCase
has no ``evidence`` attribute).
"""
from contextlib import contextmanager
from dataclasses import fields, is_dataclass
from functools import wraps
import json
import os
import unittest
from pathlib import Path


def json_value(value):
    """Snapshot bytes and model records without retaining live resource owners."""
    if isinstance(value, bytes):
        return {'hex': value.hex()}
    if is_dataclass(value) and not isinstance(value, type):
        return {field.name: json_value(getattr(value, field.name)) for field in fields(value)}
    if isinstance(value, dict):
        return {str(key): json_value(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [json_value(item) for item in value]
    if isinstance(value, (set, frozenset)):
        return sorted((json_value(item) for item in value), key=repr)
    if isinstance(value, Path):
        return str(value)
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    raise TypeError('live evidence must be data, not ' + type(value).__name__)


def record_failure(case, family, *, rule, request, reply, verdict, trace):
    """Write the first failure now; later examples and replay cannot replace it."""
    evidence = getattr(case, 'evidence', None)
    if evidence is None or 's_failure' in evidence:
        return
    from fn2.tests.surface import RUN, output
    path = Path(RUN.get('out', os.environ.get('FN2_SURFACE_OUT', 'build/surface'))) / family / 's-failure.json'
    record = json_value(dict(schema_version=1, family=family, test=case.id(),
                             rule=rule, request=request, reply=reply,
                             model_verdict=verdict, trace=trace))
    # Save the in-memory copy first, so even an output failure cannot erase it.
    evidence['s_failure'] = record
    evidence['s_failure_path'] = str(path)
    try:
        path = output(family) / 's-failure.json'
        evidence['s_failure_path'] = str(path)
        # The runner requires a fresh output directory. Exclusive creation also
        # protects an earlier sibling's first failure if several S tests fail.
        with path.open('x', encoding='utf-8') as stream:
            json.dump(record, stream, indent=2, sort_keys=True)
            stream.write('\n')
    except FileExistsError:
        evidence['s_failure_file_note'] = 'family file already contains an earlier failure; this test is in s_failure'
    except OSError as exc:
        evidence['s_failure_write_error'] = str(exc)


def capture_step(case, family, *, request=None):
    """Capture an operation exception when no precise model check did so.

    Apply inside Hypothesis's @rule/@invariant decorators, so the registered
    function is this wrapper. Request extractors are explicit data adapters;
    neither exception frames nor Hypothesis internals are inspected.
    """
    def decorate(call):
        @wraps(call)
        def wrapped(machine, *args, **kwargs):
            command = request(machine, *args, **kwargs) if request else None
            try:
                return call(machine, *args, **kwargs)
            except unittest.SkipTest:
                raise
            except Exception as exc:
                verdict = dict(ok=False, evaluated=False, exception=type(exc).__name__, detail=str(exc))
                trace = list(getattr(machine, 'trace', ()))
                trace.append(dict(rule=call.__name__, request=command, reply=None, model_verdict=verdict))
                owner = case if case is not None else machine.case
                record_failure(owner, family, rule=call.__name__, request=command,
                               reply=None, verdict=verdict, trace=trace)
                raise
        return wrapped
    return decorate


@contextmanager
def failure_context(case, family):
    """Keep Hypothesis's error type and traceback, including replay divergence."""
    try:
        yield
    except BaseException as exc:
        evidence = getattr(case, 'evidence', {})
        if 's_failure' in evidence:
            pointer = evidence.get('s_failure_path', family + '/s-failure.json')
            note = 'First live S failure: ' + pointer + ' (also test evidence.s_failure)'
            if 's_failure_file_note' in evidence:
                note += '; ' + evidence['s_failure_file_note']
            if 's_failure_write_error' in evidence:
                note += '; artifact write failed: ' + evidence['s_failure_write_error']
            if note not in getattr(exc, '__notes__', ()):
                exc.add_note(note)
        raise


def run_live_machine(case, family, factory, *, settings=None):
    """Run the public stateful API; its final replay remains enabled internally."""
    from hypothesis.stateful import run_state_machine_as_test
    from fn2.tests.surface import live_model_settings
    with failure_context(case, family):
        run_state_machine_as_test(factory, settings=settings or live_model_settings(family))
