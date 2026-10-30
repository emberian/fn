"""Translate native observer evidence, retaining explicit coverage failures."""
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
import base64
import binascii
import hashlib
import json
from pathlib import Path
import re
from email.parser import BytesHeaderParser

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


def _cancel_target(headers):
    """Only an unambiguous Control field names a cancellation target."""
    fields = headers.get_all('Control', [])
    if len(fields) != 1:
        return None
    match = re.fullmatch(r'cancel\s+(<[^<>\s]+>)', fields[0].strip(), re.I)
    return match[1] if match else None


def _sasl_account(mechanism, token):
    """Recover an observed SASL identity, never infer one from success alone."""
    try:
        data = base64.b64decode(token, validate=True).decode('utf-8')
        if mechanism == 'PLAIN':
            authorization, authentication, _ = data.split('\0')
            return authorization or authentication or None
        if mechanism in {'SCRAM-SHA-256', 'SCRAM-SHA-256-PLUS'}:
            flag, authorization, first = data.split(',', 2)
            if flag not in {'n', 'y', 'p=tls-exporter', 'p=tls-unique'}:
                return None
            account = authorization[2:] if authorization.startswith('a=') else next(
                (field[2:] for field in first.split(',') if field.startswith('n=')), '')
            return account.replace('=2C', ',').replace('=3D', '=') or None
    except (ValueError, UnicodeError, binascii.Error):
        pass
    return None


def _key_authority(cause_headers, target_headers):
    """RFC 8315: hash the base64 key STRING, not the decoded secret bytes."""
    if cause_headers is None or target_headers is None:
        return None
    def tokens(headers, name):
        values = []
        for field in headers.get_all(name, []):
            text, depth, escaped = [], 0, False
            for char in str(field):
                if depth:
                    if escaped:
                        escaped = False
                    elif char == '\\':
                        escaped = True
                    elif char == '(':
                        depth += 1
                    elif char == ')':
                        depth -= 1
                elif char == '(':
                    depth = 1
                    text.append(' ')
                else:
                    text.append(char)
            if depth:
                continue
            for token in ''.join(text).split():
                if re.fullmatch(r'sha256:[A-Za-z0-9+/]+={0,2}', token, re.I):
                    values.append(token.split(':', 1)[1])
        return values
    keys, locks = tokens(cause_headers, 'Cancel-Key'), tokens(target_headers, 'Cancel-Lock')
    if not keys or not locks:
        return None
    for key in keys:
        try:
            digest = base64.b64encode(hashlib.sha256(key.encode('ascii')).digest()).decode('ascii')
        except UnicodeError:
            continue
        if digest in locks:
            return True
    return False


def adapt(records):
    """No execution, file-path dereferences, or reconstruction of missing facts.

    files_before/files_after are immutable captures; legacy files and explicit
    history_value enrichments remain accepted. All incompleteness is counted.
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
        if 'call' in r:
            signature = ('call', r['call'])
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

    def emit(start, end, f, value, outcome='ok', response=None, suffix=''):
        a, b = raw[start], raw[end]
        process = f"native:{a.get('test', 'fixture')}:{start}{suffix}"
        # Per-call observer IDs represent independent CLI/connection operations.
        request = {k: v for k, v in value.items() if k not in
                   {'code', 'reason', 'events', 'more', 'report', 'posture'}
                   and (k != 'position' or f == 'ack')
                   and (k != 'digest' or f in ('post', 'transfer'))}
        events.extend([(start, 0, process, 'invoke', f, request),
                       (end, 1, process, outcome, f, value | (response or {}))])
        used.update((start, end))
        claimed.add(start)

    state, exits, cuts, cancels = {}, set(), {}, {}
    accounts, users, sasl, posters, article_headers = {}, {}, {}, {}, {}

    def withdraw(start, end, node, target, cause_call, cause_mid=None, phase='ok'):
        value = dict(node=node, message_id=target, cause_call=cause_call)
        if cause_mid:
            value['cause_message_id'] = cause_mid
        if phase == 'ok':
            value['authorized'] = True
        emit(start, end, 'withdraw', value, phase, suffix=':withdraw')

    def stream(r):
        return (r.get('test'), r.get('node'), r.get('conn', r.get('process')))

    def authority(cause, node):
        if node == cause['origin']:
            return cause['authorized']
        if cause['authorized'] is True:
            return True
        return _key_authority(cause['headers'], article_headers.get((node, cause['target'])))

    def observed_cancel(start, end, node, cause, phase='ok'):
        allowed = authority(cause, node)
        outcome = phase if phase != 'ok' else ('ok' if allowed is True else
                                             'fail' if allowed is False else 'info')
        withdraw(start, end, node, cause['target'], cause['call'], cause['mid'], outcome)

    def transport(start, end):
        # Only positively correlated new-format nested transport is redundant.
        for s, e in calls:
            if (start <= s <= e <= end and 'conn' in raw[s]
                    and stream(raw[s]) == stream(raw[start])
                    and raw[s]['kind'] in {'client.send', 'client.line', 'client.block'}):
                used.update((s, e))
                claimed.add(s)

    for start, end in calls:
        if start in claimed:
            continue
        a, b = raw[start], raw[end]
        kind, words = a.get('kind'), list(a.get('words', []))
        extra = a.get('history_value', {}) | b.get('history_value', {})
        node = a.get('node', b.get('node', 'default'))
        value = {'node': node} | extra
        if kind == 'operator' and words[:2] == ['article', 'withdraw'] and len(words) >= 3:
            phase = ('info' if b['phase'] == 'info' or b.get('exit_code') is None else
                     'ok' if b.get('exit_code') == 0 else 'fail')
            withdraw(start, end, node, words[2], a.get('call', start), phase=phase)
            continue
        if kind == 'node.signal':
            used.update((start, end))  # signal request alone does not establish death
            continue
        if kind in {'node.start', 'node.try_start', 'node.start_store_owner'}:
            cuts[node] = a.get('death_cut')
            if 'env_selectors' in a:
                value['env_selectors'] = a['env_selectors']
            if b['phase'] == 'ok' and b.get('exit_class') in {None, 'OK'}:
                value['posture'] = 'ready'
                emit(start, end, 'recover', value)
            else:
                emit(start, end, 'recover', value | {'posture': 'uncertain'}, 'info')
            continue
        if kind in {'node.stop', 'node.exit'}:
            identity = (node, b.get('pid'), b.get('exit_code'))
            if 'call' in a and (identity in exits or b.get('exit_class') == 'OK'):
                used.update((start, end))
                continue
            if b.get('exit_class') not in {None, 'OK'}:
                cut = b.get('death_cut', cuts.get(node))
                # A selector arms a fault; only matching exit + marker proves its cut.
                reached = (isinstance(cut, list) and len(cut) == 2 and
                           b.get('exit_code') == cut[0] and
                           cut[1] in b.get('stdout', '') + b.get('stderr', ''))
                emit(start, end, 'crash', value | {'cut': extra.get('cut', cut[1] if reached else 'unknown')})
                exits.add(identity)
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
            files = b.get('files_after', a.get('files', {}) | b.get('files', {}))
            if f == 'ack':
                files = a.get('files_before', files)
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
                    if not isinstance(files[path], str):
                        raise ValueError('snapshot has hash/length only')
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
                report_bytes = (bytes.fromhex(files[report_path]) if
                                isinstance(files.get(report_path), str) else None)
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
                if type(parsed.get('more')) is bool:
                    value['more'] = parsed['more']
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
        if kind in {'client.connect', 'client.close', 'client.starttls'} and 'conn' in a:
            for table in (accounts, users, sasl):
                table.pop(stream(a), None)
            used.update((start, end))
            transport(start, end)
            if kind == 'client.starttls':
                used.update(i for s, e in calls if start < s < e < end
                            and stream(raw[s]) == stream(a) for i in (s, e))
            continue
        # Some clients send SASL continuations with send/line, not command.
        connection = stream(a)
        if connection in sasl and kind in {'client.send', 'client.line'}:
            negotiation = sasl[connection]
            if kind == 'client.send':
                token = bytes.fromhex(a.get('sent_hex', '')).strip()
                account = _sasl_account(negotiation['mechanism'], token)
                if account is not None:
                    negotiation['account'] = account
            else:
                status = bytes.fromhex(b.get('reply_hex', ''))[:3]
                if status in {b'281', b'283'} and b['phase'] == 'ok':
                    accounts[connection] = negotiation['account']
                if status != b'383':
                    sasl.pop(connection)
            used.update((start, end))
            continue
        if kind != 'client.command':
            continue
        command = bytes.fromhex(a.get('command_hex', '')).decode('ascii', 'replace').split()
        if not command:
            continue
        verb = command[0].upper()
        reply = bytes.fromhex(b.get('reply_hex', '')).decode('ascii', 'replace')
        code = int(reply[:3]) if reply[:3].isdigit() else None
        if verb == 'AUTHINFO' or connection in sasl:
            if verb == 'AUTHINFO' and len(command) >= 2:
                method = command[1].upper()
                if method == 'USER' and len(command) == 3 and code == 381 and b['phase'] == 'ok':
                    users[connection] = command[2] if '\ufffd' not in command[2] else None
                elif method == 'PASS' and code == 281 and b['phase'] == 'ok':
                    accounts[connection] = users.pop(connection, None)
                elif method == 'SASL' and len(command) >= 3:
                    mechanism = command[2].upper()
                    sasl[connection] = dict(mechanism=mechanism, account=_sasl_account(
                        mechanism, command[3].encode() if len(command) > 3 else b''))
            elif connection in sasl:
                account = _sasl_account(sasl[connection]['mechanism'], command[0].encode())
                if account is not None:
                    sasl[connection]['account'] = account
            if connection in sasl:
                if code in {281, 283} and b['phase'] == 'ok':
                    accounts[connection] = sasl[connection]['account']
                if code != 383:
                    sasl.pop(connection)
            used.update((start, end))
            transport(start, end)
            continue
        following = [(s, e) for s, e in calls if s > end and
                     stream(raw[s]) == stream(a)]
        stop = next((s for s, e in following if raw[s]['kind'] == 'client.command'), len(raw))
        if verb in {'POST', 'IHAVE'}:
            final_end = end
            if code == (340 if verb == 'POST' else 335):
                final = next(((s, e) for s, e in following if s < stop
                              and raw[s]['kind'] == 'client.line'
                              and (raw[e]['phase'] == 'info' or
                                   bytes.fromhex(raw[e].get('reply_hex', ''))[:3] in
                                   {b'240', b'441', b'440', b'480', b'235', b'436', b'437'})), None)
                if final:
                    s, final_end = final
                    reply = bytes.fromhex(raw[final_end].get('reply_hex', '')).decode('ascii', 'replace')
                    code = int(reply[:3]) if reply[:3].isdigit() else None
                    used.update((s, final_end))
                    claimed.add(s)
            phase = ('ok' if code == (240 if verb == 'POST' else 235) else
                     'fail' if code in {440, 480, 441, 435, 436, 437} else 'info')
            if ('uncertain' in reply.lower() or b['phase'] == 'info'
                    or raw[final_end]['phase'] == 'info'):
                phase = 'info'
            reason = reply[4:].strip()
            if 'already stored' in reason:
                reason = 'duplicate'
            elif 'different article with this Message-ID' in reason:
                reason = 'conflict'
            value.update(code=code, reason=reason)
            target, headers = None, None
            sends = [raw[s] for s, e in following if e <= final_end and raw[s]['kind'] == 'client.send']
            if sends and not any('sent_sha256' in r for r in sends):
                wire = b''.join(bytes.fromhex(r.get('sent_hex', '')) for r in sends)
                if wire.endswith(b'\r\n.\r\n'):
                    article = b'\r\n'.join(line[1:] if line.startswith(b'..') else line
                                            for line in wire[:-3].split(b'\r\n'))
                    headers = BytesHeaderParser().parsebytes(article)
                    target = _cancel_target(headers)
                    mid = headers.get('Message-ID')
                    if mid:
                        try:
                            value.update(message_id=mid.strip(), digest=_body_digest(article))
                        except ValueError:
                            pass
            mid = value.get('message_id')
            if phase == 'ok' and mid and headers is not None:
                article_headers.setdefault((node, mid), headers)
                if verb == 'POST':
                    posters.setdefault((node, mid), accounts.get(connection) if 'conn' in a else None)
            cause = None
            if target:
                poster = posters.get((node, target))
                author = accounts.get(connection) if 'conn' in a else None
                local = poster == author if poster is not None and author is not None else None
                prior = cancels.get(mid)
                cause = (prior if verb == 'IHAVE' and prior else
                         dict(target=target, call=a.get('call', start), mid=mid,
                              origin=node if verb == 'POST' else None,
                              authorized=local if verb == 'POST' else None, headers=headers))
            if verb == 'IHAVE':
                # A transfer is observation on this peer, never evidence of
                # simultaneous delivery on any other node: it is its own op
                # (`transfer`, H7: the convergence checker's), outside the
                # POST durability vocabulary.
                if target:
                    observed_cancel(start, final_end, node, cause, phase)
                    if phase == 'ok' and mid:
                        cancels.setdefault(mid, cause)
                if {'message_id', 'digest'} <= value.keys():
                    emit(start, final_end, 'transfer', value, phase, suffix=':transfer')
                else:
                    miss(end, 'IHAVE send/body/Message-ID not observed')
                used.add(end)
                transport(start, final_end)
                continue
            if not {'message_id', 'digest'} <= value.keys():
                value['observed_only'] = True
                miss(end, 'POST send/body/Message-ID not observed')
            emit(start, final_end, 'post', value, phase)
            if target:
                observed_cancel(start, final_end, node, cause, phase)
                if phase == 'ok' and mid:
                    cancels.setdefault(mid, cause)
            used.add(end)
            transport(start, final_end)
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
                    elif 'reply_hex' in raw[final_end]:
                        headers = BytesHeaderParser().parsebytes(bytes.fromhex(raw[final_end]['reply_hex']))
                        article_headers[(node, command[1])] = headers
                        target = _cancel_target(headers)
                        if target:
                            cancels.setdefault(command[1], dict(target=target, call=a.get('call', start),
                                mid=command[1], origin=None, authorized=None, headers=headers))
                        if command[1] in cancels:
                            cancels[command[1]]['headers'] = headers
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
            cause = cancels.get(command[1])
            if (cause and read_phase == 'ok'
                    and code in {220, 221, 223}):
                # The cause first becomes observed here at read completion.
                observed_cancel(final_end, final_end, node, cause)
            used.add(end)
            transport(start, final_end)
    for start, end in calls:
        if raw[start].get('kind') in {'client.post', 'client.multiline'} and 'conn' in raw[start]:
            children = [(s, e) for s, e in calls if start < s < e < end
                        and stream(raw[s]) == stream(raw[start])]
            if children and all(s in used and e in used for s, e in children):
                used.update((start, end))
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
