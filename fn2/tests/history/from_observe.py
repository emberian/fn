"""Translate native observer evidence, retaining explicit coverage failures."""
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re

from .history import Record, pair, write_jsonl


@dataclass
class Adapted:
    history: list[Record]
    unmapped: list[dict]

    @property
    def counts(self):
        return dict(Counter(item['key'] for item in self.unmapped))


def cursor(hex_bytes):
    """Decode a captured v1 cursor as specified in consumer-progress L43-49."""
    data, offset, ids = bytes.fromhex(hex_bytes), 5, []
    if data[:5] != b'fncu\x01':
        raise ValueError('not a v1 cursor')
    for _ in range(5):
        if offset >= len(data):
            raise ValueError('short cursor')
        size = data[offset]
        offset += 1
        if not 1 <= size <= 64 or offset + size > len(data):
            raise ValueError('invalid cursor ID length')
        ids.append(data[offset:offset + size].decode('latin-1'))
        offset += size
    if len(data) != offset + 16:
        raise ValueError('invalid cursor length')
    qv, vv, epoch, position = [int.from_bytes(data[n:n + 4], 'big')
                             for n in range(offset, offset + 16, 4)]
    return {'consumer': ids[2], 'epoch': epoch, 'position': position,
            'scope': dict(zip(('history', 'incarnation', 'principal', 'query',
                              'query_version', 'view_version'),
                             (ids[0], ids[1], ids[3], ids[4], qv, vv)))}


def _body_digest(block):
    if b'\r\n\r\n' not in block:
        raise ValueError('ARTICLE has no header/body separator')
    return hashlib.sha256(block.split(b'\r\n\r\n', 1)[1]).hexdigest()


def adapt(records):
    """No execution, file-path dereferences, or reconstruction of missing facts.

    Optional files={path: hex} and history_value={} are explicit future observer
    enrichments. Existing H1b emits neither. All incompleteness is counted.
    """
    raw = list(records)
    missing, used, calls, pending = {}, set(), [], defaultdict(deque)

    def miss(i, why):
        r = raw[i]
        words = r.get('words', [])
        first = words[0] if words else ''
        if not first and r.get('command_hex'):
            first = bytes.fromhex(r['command_hex']).decode('ascii', 'replace').split()[0]
        label = r.get('kind', '?') + ':' + first
        missing.setdefault(i, {'index': i, 'key': label, 'reason': why})

    last_t = -1
    for i, r in enumerate(raw):
        if type(r.get('t')) is not int or r['t'] < last_t:
            raise ValueError(f'observe-time-backwards at {i}')
        last_t = r['t']
        signature = (r.get('test'), r.get('process'), r.get('kind'),
                     tuple(r.get('words', [])), r.get('command_hex'),
                     r.get('pid') if r.get('kind') == 'node.stop' else None)
        if r.get('phase') == 'invoke':
            if pending[signature]:
                miss(i, 'ambiguous overlapping calls without unique call ID')
                for old in pending[signature]:
                    miss(old, 'ambiguous overlapping calls without unique call ID')
            pending[signature].append(i)
        elif r.get('phase') in {'ok', 'fail', 'info'} and pending[signature]:
            start = pending[signature].popleft()
            if start in missing:
                miss(i, 'ambiguous call completion')
            else:
                calls.append((start, i))
        else:
            miss(i, 'completion without identifiable invocation')
    for starts in pending.values():
        for i in starts:
            miss(i, 'incomplete native call; no correlated completion')
    calls.sort()
    events, claimed = [], set()

    def emit(start, end, f, value, outcome='ok', response=None):
        a, b = raw[start], raw[end]
        process = f"native:{a.get('test', 'fixture')}:{start}"
        # Per-call observer IDs represent independent CLI/connection operations.
        request = {k: v for k, v in value.items() if k not in
                   {'code', 'reason', 'events', 'more', 'report', 'posture'}
                   and (k != 'position' or f == 'ack')
                   and (k != 'digest' or f == 'post')}
        events.extend([(start, 0, process, 'invoke', f, request),
                       (end, 1, process, outcome, f, value | (response or {}))])
        used.update((start, end))
        claimed.add(start)

    state = {}  # Only explicitly observed or definitely acknowledged positions.
    for start, end in calls:
        if start in claimed:
            continue
        a, b = raw[start], raw[end]
        kind, words = a.get('kind'), list(a.get('words', []))
        extra = a.get('history_value', {}) | b.get('history_value', {})
        node = a.get('node', b.get('node', 'default'))
        value = {'node': node} | extra
        if kind in {'node.start', 'node.try_start', 'node.start_store_owner'}:
            if b['phase'] == 'ok' and b.get('exit_class') in {None, 'OK'}:
                value['posture'] = 'ready'
                emit(start, end, 'recover', value)
                if a.get('env', {}).get('FN_NATIVE_CONTROL_FAULT'):
                    miss(start, 'fault armed; no crash observed until stop')
            else:
                emit(start, end, 'recover', value | {'posture': 'uncertain'}, 'info')
            continue
        if kind == 'node.stop':
            if b.get('exit_class') not in {None, 'OK'}:
                emit(start, end, 'crash', value | {'cut': extra.get('cut', 'unknown')})
            else:
                miss(start, 'clean stop is not a crash cut')
                miss(end, 'clean stop is not a crash cut')
            continue
        if kind in {'invoke', 'operator', 'store'} and words[:1] == ['consumer']:
            args = [w for w in words[1:] if w != '--json']
            if len(args) < 2:
                continue
            verb, control, *params = args
            f = verb.removeprefix('bound-')
            if f not in {'register', 'poll', 'wait', 'ack', 'position', 'rebase', 'unregister', 'status'}:
                continue
            if 'node' not in extra and 'node' not in a:
                value['node'] = control
                miss(start, 'control path known; node start/stop correlation unavailable')
            if params and f != 'ack':
                value['consumer'] = params[0]
            said = b.get('stdout', '').strip()
            parsed = {}
            try:
                parsed = json.loads(said.splitlines()[-1])
                if not isinstance(parsed, dict):
                    parsed = {}
            except (ValueError, IndexError):
                pass
            match = re.search(r'consumer(?: status)? (accepted|refused|uncertain)(?: ([\w-]+))?', said)
            outcome = parsed.get('outcome', match[1] if match else None)
            phase = {'accepted': 'ok', 'refused': 'fail', 'uncertain': 'info'}.get(outcome, 'info')
            if b['phase'] == 'info':
                phase = 'info'
            value['reason'] = parsed.get('reason', match[2] if match and outcome != 'accepted' else None)
            files = a.get('files', {}) | b.get('files', {})
            path = None
            if f == 'ack' and params:
                path = params[0]
            elif f in {'register', 'rebase'} and len(params) >= 3:
                path = params[2]
            elif f in {'position', 'poll', 'wait'} and len(params) >= 2:
                n = 2 if verb.startswith('bound-') else 1
                path = params[n] if len(params) > n else None
            if path in files:
                try:
                    value.update(cursor(files[path]))
                except (ValueError, UnicodeError) as error:
                    miss(end, f'captured cursor: {error}')
            if f == 'status':
                f = 'position'
                count = re.search(r'committed-ack=(\d+)', said)
                if 'committed_ack' in parsed or count:
                    value['position'] = parsed.get('committed_ack', int(count[1]) if count else None)
            state_key = (value['node'], value.get('consumer'))
            if f in {'poll', 'wait'}:
                baseline = state.get(state_key)
                if baseline and baseline.get('scope') == value.get('scope') and baseline.get('epoch') == value.get('epoch'):
                    value.setdefault('cursor', baseline['position'])
                report = parsed.get('report')
                report_index = 3 if verb.startswith('bound-') else 2
                report_path = params[report_index] if len(params) > report_index else None
                report_bytes = bytes.fromhex(files[report_path]) if report_path in files else None
                mid = parsed.get('message_id')
                if report_bytes is not None:
                    if not report_bytes:
                        report = 'empty'
                    elif report_bytes.startswith(b'FNWD\x01'):
                        report, mid = 'withdrawn', report_bytes[5:].decode('ascii')
                if report == 'empty':
                    value.setdefault('events', [])
                elif mid and 'position' in value:
                    value.setdefault('events', [[value['position'], mid]])
                if report:
                    value['report'] = report
                # Native single-item output lacks the pinned frontier/more bit.
                if f == 'wait' and '--timeout' in params:
                    value['deadline'] = a['t'] + int(params[params.index('--timeout') + 1]) * 10**9
            required = {'consumer', 'epoch', 'scope'}
            if f in {'ack', 'register', 'rebase', 'position'}:
                required.add('position')
            if f in {'poll', 'wait'}:
                required.update(('cursor', 'position', 'events', 'more'))
            if f == 'wait':
                required.add('deadline')
            if required - value.keys():
                value['observed_only'] = True
                miss(end, 'missing consumer evidence: ' + ', '.join(sorted(required - value.keys())))
            if phase == 'ok' and f in {'register', 'rebase', 'position', 'ack'} and not value.get('observed_only'):
                state[state_key] = value.copy()
            elif f in {'ack', 'register', 'rebase', 'unregister'} and phase != 'fail':
                state.pop(state_key, None)
            emit(start, end, f, value, phase)
            continue
        if kind != 'client.command':
            continue
        command = bytes.fromhex(a.get('command_hex', '')).decode('ascii', 'replace').split()
        if not command:
            continue
        verb = command[0].upper()
        reply = bytes.fromhex(b.get('reply_hex', '')).decode('ascii', 'replace')
        code = int(reply[:3]) if reply[:3].isdigit() else None
        stream = (a.get('test'), a.get('process'))
        following = [(s, e) for s, e in calls if s > end and
                     (raw[s].get('test'), raw[s].get('process')) == stream]
        stop = next((s for s, e in following if raw[s]['kind'] == 'client.command'), len(raw))
        if verb == 'POST':
            final_end = end
            if code == 340:
                final = next(((s, e) for s, e in following if s < stop
                              and raw[s]['kind'] == 'client.line'
                              and (raw[e]['phase'] == 'info' or
                                   bytes.fromhex(raw[e].get('reply_hex', ''))[:3] in
                                   {b'240', b'441', b'440', b'480'})), None)
                if final:
                    s, final_end = final
                    reply = bytes.fromhex(raw[final_end].get('reply_hex', '')).decode('ascii', 'replace')
                    code = int(reply[:3]) if reply[:3].isdigit() else None
                    used.update((s, final_end))
                    claimed.add(s)
            phase = 'ok' if code == 240 else 'fail' if code in {440, 480, 441} else 'info'
            if 'uncertain' in reply.lower() or b['phase'] == 'info':
                phase = 'info'
            reason = reply[4:].strip()
            if 'already stored' in reason:
                reason = 'duplicate'
            elif 'different article with this Message-ID' in reason:
                reason = 'conflict'
            value.update(code=code, reason=reason)
            if not {'message_id', 'digest'} <= value.keys():
                value['observed_only'] = True
                miss(end, 'POST send/body/Message-ID not observed')
            emit(start, final_end, 'post', value, phase)
            used.add(end)
        elif verb in {'ARTICLE', 'HEAD', 'STAT'} and len(command) == 2 and command[1].startswith('<'):
            value.update(message_id=command[1], code=code)
            final_end = end
            read_phase = 'info' if code is None or b['phase'] == 'info' else 'ok'
            if code in {220, 221}:
                block = next(((s, e) for s, e in following if s < stop and raw[s]['kind'] == 'client.block'), None)
                if block:
                    s, final_end = block
                    used.update((s, final_end))
                    claimed.add(s)
                    if raw[final_end]['phase'] != 'ok':
                        read_phase = 'info'
                    if verb == 'ARTICLE':
                        try:
                            value['digest'] = _body_digest(bytes.fromhex(raw[final_end]['reply_hex']))
                        except (KeyError, ValueError) as error:
                            miss(final_end, str(error))
                else:
                    miss(end, 'missing read block')
                    read_phase = 'info'
            if 'digest' not in value and code in {220, 221, 223}:
                miss(end, 'read presence only; no payload digest')
            emit(start, final_end, 'read', value, read_phase)
            used.add(end)
    for i in range(len(raw)):
        if i not in used:
            miss(i, 'unmapped record or nested transport detail')
    events.sort(key=lambda e: (e[0], e[1]))
    history, inflight, crashed = [], {}, set()
    for source, _, process, phase, f, v in events:
        if phase != 'invoke' and process in crashed:
            miss(source, 'late reply after observed crash; operation remains info')
            continue
        history.append(Record(process, phase, f, v, raw[source]['t'], len(history)))
        if phase == 'invoke':
            inflight[process] = v.get('node', 'default')
        else:
            inflight.pop(process, None)
        if f == 'crash' and phase == 'ok':
            for client, target in list(inflight.items()):
                if target == v.get('node', 'default'):
                    crashed.add(client)
                    del inflight[client]
    pair(history)
    return Adapted(history, [missing[i] for i in sorted(missing)])


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = adapt(json.loads(line) for line in args.source.read_text().splitlines())
    write_jsonl(result.history, args.output)
    print(json.dumps({'counts': result.counts, 'unmapped': result.unmapped}, sort_keys=True))


if __name__ == '__main__':
    main()
