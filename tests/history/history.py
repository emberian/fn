"""JSONL observations and crash-aware, per-process operation pairing."""
from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict, dataclass
import json
from pathlib import Path

FUNCTIONS = {'register', 'poll', 'wait', 'ack', 'position', 'rebase',
             'unregister', 'post', 'read', 'crash', 'recover', 'withdraw', 'transfer'}


class HistoryError(ValueError):
    def __init__(self, kind, index, explanation):
        self.kind, self.index = kind, index
        super().__init__(f'{kind} at {index}: {explanation}')


@dataclass(frozen=True)
class Record:
    process: str
    type: str
    f: str
    value: dict
    time: int
    index: int

    def __post_init__(self):
        object.__setattr__(self, 'value', deepcopy(self.value))

    def to_dict(self):
        return asdict(self)


@dataclass(frozen=True)
class Operation:
    invoke: Record
    completion: Record

    @property
    def f(self):
        return self.invoke.f

    @property
    def type(self):
        return self.completion.type

    @property
    def value(self):
        return self.invoke.value | self.completion.value

    @property
    def node(self):
        return self.value.get('node', 'default')


@dataclass(frozen=True)
class Anomaly:
    kind: str
    ops: tuple[int, ...]
    explanation: str


def anomaly(kind, explanation, *ops):
    return Anomaly(kind, tuple(dict.fromkeys(i for op in ops for i in
                   (op.invoke.index, op.completion.index))), explanation)


def records(history):
    result = []
    last_index = last_time = -1
    for raw in history:
        try:
            r = raw if isinstance(raw, Record) else Record(**raw)
        except (TypeError, ValueError) as error:
            raise HistoryError('record-shape', len(result), str(error)) from error
        if (not isinstance(r.process, str) or not r.process or r.f not in FUNCTIONS
                or r.type not in {'invoke', 'ok', 'fail', 'info'}
                or not isinstance(r.value, dict)):
            raise HistoryError('record-shape', r.index, 'invalid process/type/f/value')
        if type(r.index) is not int or r.index < 0 or r.index <= last_index:
            raise HistoryError('index-order', r.index, 'indices must strictly increase')
        if type(r.time) is not int or r.time < 0 or r.time < last_time:
            raise HistoryError('time-backwards', r.index, 'monotonic ns required')
        last_index, last_time = r.index, r.time
        result.append(r)
    return result


def pair(history):
    """Validate and pair; only an observed crash permits a missing completion."""
    pending, result = {}, []
    for r in records(history):
        if r.type == 'invoke':
            if r.process in pending:
                raise HistoryError('two-invokes', r.index, r.process)
            pending[r.process] = r
            continue
        if r.process not in pending:
            raise HistoryError('completion-without-invoke', r.index, r.process)
        start = pending.pop(r.process)
        if start.f != r.f:
            raise HistoryError('function-mismatch', r.index, start.f)
        for field in ('node', 'consumer', 'epoch', 'scope', 'cursor', 'message_id'):
            if field in start.value and field in r.value and start.value[field] != r.value[field]:
                raise HistoryError('request-changed', r.index, field)
        if start.f == 'ack' and ('position' in r.value and
                                r.value['position'] != start.value.get('position')):
            raise HistoryError('request-changed', r.index, 'ack target')
        op = Operation(start, r)
        result.append(op)
        if r.f == 'crash' and r.type == 'ok':
            for process, invocation in list(pending.items()):
                if invocation.value.get('node', 'default') == op.node:
                    result.append(Operation(invocation, Record(process, 'info', invocation.f,
                        {'reason': 'crash-before-reply'}, r.time, r.index)))
                    del pending[process]
    if pending:
        first = next(iter(pending.values()))
        raise HistoryError('incomplete-without-crash', first.index, first.process)
    return sorted(result, key=lambda op: (op.completion.index, op.invoke.index))


def read_jsonl(source):
    """Read a path or text stream; validate before returning records."""
    if hasattr(source, 'read'):
        lines = source.read().splitlines()
    else:
        lines = Path(source).read_text(encoding='utf-8').splitlines()
    data = []
    for line_no, line in enumerate(lines, 1):
        try:
            data.append(json.loads(line))
        except (ValueError, TypeError) as error:
            raise HistoryError('invalid-json', line_no, str(error)) from error
    result = records(data)
    pair(result)
    return result


def write_jsonl(history, destination):
    data = records(history)
    pair(data)
    text = ''.join(json.dumps(r.to_dict(), sort_keys=True) + '\n' for r in data)
    if hasattr(destination, 'write'):
        destination.write(text)
    else:
        Path(destination).write_text(text, encoding='utf-8')
