"""Process-death fault cells and their external NNTP oracle (no host decisions).

The store filesystem's fdatasync durability is an assumption, not established
by killing a process. Histories describe client observations, never acceptance
inferred from a successful send. SHA256 here is only a test byte comparator.
"""
from __future__ import annotations

import collections
import hashlib
import json
import socket
import threading
import time

from tests.test_native_peer_catchup import without_path_and_xref

PROPERTIES = {
    "P1-DURABLE": "Every POST with a read 240 survives restart byte-identically, Path/Xref excepted.",
    "P2-IDENTITY": "Only attempted articles exist; each Message-ID has exactly its attempted octets; uncertain POSTs are whole or absent.",
    "P5-RECOVERY": "After each process death, including recovery death, LISTENING and a productive POST occur within the stated bound.",
    "P8-CLIENTS": "Client bytes cannot kill the owner, exceed other clients' deadlines or grow RSS without bound; misuse is refused by name.",
    "P4-RECLAIM": "A held ARTICLE across publication/checkpoint/reclaim returns accepted octets or a named refusal, never another article's bytes.",
}
OUTCOMES = ("not-attempted", "attempted-uncertain", "completed")


def digest(octets):
    return hashlib.sha256(without_path_and_xref(octets)).hexdigest()


class History:
    def __init__(self):
        self.ops = []
        self.lock = threading.Lock()

    def plan(self, kind, args):
        with self.lock:
            op = {"op_id": len(self.ops), "kind": kind, "args": args,
                  "args_digest": hashlib.sha256(json.dumps(args, sort_keys=True).encode()).hexdigest(),
                  "send_time": None, "outcome": "not-attempted", "reply_line": None}
            self.ops.append(op)
            return op

    def sent(self, op):
        # Mark before send: a sendall exception cannot tell how many bytes reached the peer.
        op.update(send_time=time.monotonic(), outcome="attempted-uncertain")

    def complete(self, op, line):
        if not line.endswith(b"\r\n"):
            raise EOFError("incomplete reply line")
        op.update(outcome="completed", reply_line=line.decode("latin-1"), complete_time=time.monotonic())

    def counts(self):
        c = collections.Counter(op["outcome"] for op in self.ops)
        return {k: c[k] for k in OUTCOMES}


def verify(history, present):
    """P1/P2 against a COMPLETE inventory: Message-ID -> normalized octet digest.

    The inventory must include unexpected IDs, not merely probe known POSTs.
    A completed refusal is not accepted; an earlier 240 pins the identity even
    if a later attempted POST offers different octets under that Message-ID.
    """
    findings = []
    posts = [o for o in history if o["kind"] == "POST"]
    accepted, possible = {}, collections.defaultdict(set)
    for op in posts:
        a = op["args"]
        if op["outcome"] == "attempted-uncertain" or (op["outcome"] == "completed" and (op["reply_line"] or "").startswith("240 ")):
            possible[a["msgid"]].add(a["sha256"])
        if op["outcome"] == "completed" and (op["reply_line"] or "").startswith("240 "):
            old = accepted.setdefault(a["msgid"], a["sha256"])
            if old != a["sha256"]:
                findings.append(("P2-IDENTITY", "conflicting acceptances: " + a["msgid"]))
            if present.get(a["msgid"]) != a["sha256"]:
                findings.append(("P1-DURABLE", "missing or changed: " + a["msgid"]))
    for mid, value in present.items():
        allowed = {accepted[mid]} if mid in accepted else possible[mid]
        if value not in allowed:
            findings.append(("P2-IDENTITY", "unattempted or changed: " + mid))
    return findings


def shrink(history, fails, budget=32):
    """Bounded ddmin: re-run prefixes, suffixes and chunk deletions.

    Retains original op IDs. Reports budget exhaustion; never claims global
    shortest when the budget (or non-monotonic failure) prevents that claim.
    """
    best, calls, granularity = list(history), 0, 2
    while best and calls < budget:
        width = max(1, (len(best) + granularity - 1) // granularity)
        changed = False
        for start in range(0, len(best), width):
            candidate = best[:start] + best[start + width:]
            calls += 1
            if fails(candidate):
                best, changed = candidate, True
                granularity = max(2, granularity - 1)
                break
            if calls >= budget:
                break
        if not changed:
            if width == 1:
                return best, {"runs": calls, "budget": budget, "minimal": "one-deletion"}
            granularity = min(len(best), granularity * 2)
    return best, {"runs": calls, "budget": budget, "minimal": "empty" if not best else "budget-exhausted"}


def report(history, findings, checked, replay=None, budget=32):
    violations = []
    tagged = any(o.get('replayable') or o.get('transcript') or 'replay_key' in o for o in history.ops)
    variable = [o for o in history.ops if not tagged or o.get('replayable') or o.get('transcript') or 'replay_key' in o]
    variable_ids = {o['op_id'] for o in variable}
    fixed = [o for o in history.ops if o['op_id'] not in variable_ids]
    for prop, detail in sorted(set(findings)):
        errors = []
        def fails(candidate):
            try:
                return replay(candidate, prop, detail)
            except Exception as exc:
                # A replay setup failure is not reproduction of this property.
                errors.append(type(exc).__name__ + ': ' + str(exc))
                return False
        short, info = (shrink(variable, fails, budget) if replay else
                       (variable, {"runs": 0, "minimal": "not-replayed"}))
        info.update(fixed_operations=len(fixed), replay_errors=errors)
        violations.append({"property": prop, "detail": detail, "history_len": len(history.ops),
                           "shrunk_history": short, "fixed_history": fixed, "shrink": info})
    return {"violations": violations, "outcomes": history.counts(), "checked": checked,
            "history": history.ops}


class Client:
    """All commands, including probes, recorded; completion includes dot body.

    No implicit QUIT on close. One absolute command deadline covers all reads.
    """
    def __init__(self, port, history, deadline=10, rcvbuf=None):
        self.history, self.deadline = history, deadline
        self.sock = socket.socket()
        self.sock.settimeout(deadline)
        if rcvbuf:
            self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, rcvbuf)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.sock.connect(("127.0.0.1", port))
        self.buffer = bytearray()
        self.recv_size = 65536
        self.end = time.monotonic() + deadline
        if self.line()[:3] not in (b"200", b"201"):
            self.close()
            raise ConnectionError("greeting refused")

    def line(self):
        if time.monotonic() >= self.end:
            raise TimeoutError("command-deadline")
        while b"\r\n" not in self.buffer:
            left = self.end - time.monotonic()
            if left <= 0:
                raise TimeoutError("command-deadline")
            self.sock.settimeout(left)
            chunk = self.sock.recv(self.recv_size)
            if not chunk:
                raise EOFError("partial reply")
            self.buffer.extend(chunk)
        end = self.buffer.index(b"\r\n") + 2
        line = bytes(self.buffer[:end])
        del self.buffer[:end]
        return line

    def begin(self, kind, args, wire, op=None):
        self.end = time.monotonic() + self.deadline
        op = op if op is not None else self.history.plan(kind, args)
        self.history.sent(op)
        self.sock.sendall(wire)
        return op

    def finish(self, op):
        line = self.line()
        body = bytearray()
        if line[:3] in (b"220", b"221", b"222", b"211", b"215", b"224") and (
                op["kind"] != "GROUP"):
            while True:
                row = self.line()
                if row == b".\r\n":
                    break
                body.extend(row[1:] if row.startswith(b"..") else row)
        self.history.complete(op, line)
        return line, bytes(body)

    def command(self, text):
        op = self.begin(text.split()[0], {"command": text}, text.encode() + b"\r\n")
        return self.finish(op)

    def post(self, i, octets=2048, op=None):
        from tools import rep_measure, msgid_measure
        article = rep_measure.article(i, octets)
        args = {"i": i, "octets": octets, "msgid": msgid_measure.msgid(i), "sha256": digest(article)}
        op = self.begin("POST", args, b"POST\r\n", op)
        line = self.line()
        if line.startswith(b"340 "):
            self.sock.sendall(article + b".\r\n")
            line = self.line()
        self.history.complete(op, line)
        return line

    def close(self):
        self.sock.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


def inventory(port, history, deadline=10):
    """Enumerate every group/article, checking both number and Message-ID routes."""
    present = {}
    with Client(port, history, deadline) as c:
        status, groups = c.command("LIST ACTIVE")
        if not status.startswith(b"215 "):
            raise RuntimeError("LIST ACTIVE refused: " + repr(status))
        for group in groups.splitlines():
            status, numbers = c.command("LISTGROUP " + group.split()[0].decode())
            if not status.startswith(b"211 "):
                raise RuntimeError("LISTGROUP refused: " + repr(status))
            for number in numbers.splitlines():
                status, article = c.command("ARTICLE " + number.decode())
                if not status.startswith(b"220 "):
                    raise RuntimeError("enumerated ARTICLE refused: " + repr(status))
                mid = next(row.split(b":", 1)[1].strip().decode() for row in article.split(b"\r\n\r\n")[0].splitlines()
                           if row.lower().startswith(b"message-id:"))
                value = digest(article)
                if mid in present and present[mid] != value:
                    raise ValueError("P2-IDENTITY: conflicting enumerated Message-ID " + mid)
                present[mid] = value
                reply, by_id = c.command("ARTICLE " + mid)
                if not reply.startswith(b"220 ") or digest(by_id) != value:
                    raise ValueError("P2-IDENTITY: number/Message-ID mismatch " + mid)
    return present


def metrics(faults):
    return {"faults.%s.violations" % p: sum(v["property"] == p for v in faults["violations"])
            for p in set(faults["checked"]) | {v["property"] for v in faults["violations"]}}


BOUNDARIES = (
    'fnn-durable-barrier', 'fnn-log-fdatasync', 'fnn-checkpoint-yield',
    'fnn-checkpoint-write-arena-steps', 'fnn-checkpoint-write-steps',
    'fnn-state-checkpoint-install', 'fnn-owner-publish-captured',
)


def sample_points(n, budget):
    if n <= budget:
        return list(range(1, n + 1))
    if budget < 3:
        raise ValueError('sampling needs at least first/middle/last')
    return sorted({1 + round(i * (n - 1) / (budget - 1)) for i in range(budget)})


class Campaign:
    """Fresh, private stores per replay; never rewind or mutate another run."""
    def __init__(self, run, ph):
        self.run, self.ph, self.serial = run, ph, 0
        self.deadline = ph.get('command_deadline_s', 10)
        self.recovery = ph.get('recovery_s', 60)

    def node(self, hook=False, reclaim=False):
        from pathlib import Path
        parent = self.run.node
        self.serial += 1
        work = parent.work / ('fault-%04d' % self.serial)
        work.mkdir()
        hooks = [Path(__file__).resolve().parents[2] / 'planning/evidence/load/hooks/f2-crash.lisp'] if hook else []
        node = type(parent)(parent.target, work, parent.flags, parent.groups,
                            parent.env['SBCL_USER_ARGS'], hooks, work / 'gc.log', {}, 1,
                            parent.heap_mode)
        # The environment of the driving shell must not accidentally arm init/heap/control.
        node.env = {k: v for k, v in node.env.items() if not k.startswith('FN_LOAD_CRASH_')}
        node.init()
        if reclaim:
            with node.config.open('a') as f:
                f.write('\n[resources]\nreclaim_live = true\n')
        if node.heap_mode == 'decided':
            node.decide_heap()
            node.heap_mode = 'fixed'  # never run a heap probe with a crash hook armed
        return node

    def control(self, node, h, *words, op=None):
        import subprocess
        op = op if op is not None else h.plan('CONTROL', {'words': list(words)})
        h.sent(op)
        env = {k: v for k, v in node.env.items() if not k.startswith('FN_LOAD_CRASH_')}
        p = subprocess.run(node.argv(*words), env=env, capture_output=True, timeout=self.recovery)
        reply = (p.stdout + p.stderr).decode('utf-8', 'replace').strip()
        h.complete(op, (reply + '\r\n').encode())
        op['rc'] = p.returncode
        return p.returncode, reply

    def start(self, node):
        elapsed = node.start(timeout=self.recovery)
        (node.work / 'owner.pid').write_text(str(node.pid) + '\n')
        return elapsed

    def post_plan(self, h, count):
        from tools import rep_measure, msgid_measure
        return [h.plan('POST', {'i': i, 'octets': 2048, 'msgid': msgid_measure.msgid(i),
                                'sha256': digest(rep_measure.article(i, 2048))}) for i in range(count)]

    def crash_trial(self, selected=None, recipe=None):
        import subprocess
        node, h, findings, notes = self.node(hook=True), History(), [], {}
        count_path, go = node.work / 'counts', node.work / 'go'
        witness = node.work / 'crash'
        witness.touch()  # same pre-existing inode survives abort; hook fsyncs contents
        node.env.update(FN_LOAD_CRASH_GO=str(go), FN_LOAD_CRASH_RECORD=str(witness))
        if selected:
            node.env['FN_LOAD_CRASH_AT'] = selected
        else:
            node.env['FN_LOAD_CRASH_COUNT'] = str(count_path)
        try:
            self.start(node)
            ops = self.post_plan(h, self.ph.get('posts', 100)) if recipe is None else [
                h.plan(o['kind'], o['args']) for o in recipe if o['kind'] in ('POST', 'CONTROL')
                and o['args'].get('i') != 1000000]
            if recipe is None:
                control = h.plan('CONTROL', {'words': ['store', 'checkpoint']})
                ops.insert(len(ops) // 2, control)
            for op in ops:
                op["replayable"] = True
            go.touch()
            start, posted = time.monotonic(), 0
            for op in ops:
                if node.proc.poll() is not None:
                    break
                try:
                    if op['kind'] == 'CONTROL':
                        # Reuse the planned operation, not a second synthetic completion.
                        self.control(node, h, *op['args']['words'], op=op)
                    else:
                        time.sleep(max(0, start + posted / 20 - time.monotonic()))
                        with Client(node.port, h, self.deadline) as c:
                            c.post(op['args']['i'], op['args']['octets'], op)
                        posted += 1
                except (OSError, EOFError, subprocess.TimeoutExpired):
                    if not selected:
                        raise
                    break
            if not selected:
                # Require publication completion, not merely a queued control reply.
                wait_log(node, 'CHECKPOINT auto sequence=', self.recovery)
                notes['counts'] = {name: 0 for name in BOUNDARIES}
                for row in count_path.read_text().splitlines():
                    name, n = row.split()
                    notes['counts'][name] = int(n)
            else:
                try:
                    node.proc.wait(self.recovery)
                except subprocess.TimeoutExpired:
                    notes['not_measured'] = 'selected boundary was not reached'
                    return h, findings, notes
                if not witness.read_text().strip():
                    findings.append(('P5-RECOVERY', 'owner died without armed-boundary witness'))
                    return h, findings, notes
                notes['crash'] = witness.read_text().strip()
                node.stop()
                second = node.work / 'recovery-crash'
                second.touch()
                node.env.pop('FN_LOAD_CRASH_GO', None)
                node.env.update(FN_LOAD_CRASH_AT='*:1', FN_LOAD_CRASH_RECORD=str(second))
                try:
                    self.start(node)
                except Exception:
                    pass  # expected only when the fsynced hook witness below exists
                if not second.read_text().strip():
                    notes['not_measured'] = 'no recovery boundary hit before LISTENING/deadline'
                    return h, findings, notes
                node.stop()
                notes['recovery_crash'] = second.read_text().strip()
                node.env = {k: v for k, v in node.env.items() if not k.startswith('FN_LOAD_CRASH_')}
                try:
                    t0 = time.monotonic()
                    self.start(node)
                    with Client(node.port, h, min(self.deadline, max(.01, self.recovery - (time.monotonic() - t0)))) as c:
                        reply = c.post(1000000, 2048)
                    if not reply.startswith(b'240 ') or time.monotonic() - t0 > self.recovery:
                        findings.append(('P5-RECOVERY', 'restart was not productive within bound'))
                except Exception as exc:
                    findings.append(('P5-RECOVERY', 'clean restart: ' + str(exc)))
                    return h, findings, notes
                try:
                    findings += verify(h.ops, inventory(node.port, h, self.deadline))
                except ValueError as exc:
                    findings.append(('P2-IDENTITY', str(exc)))
            return h, findings, notes
        finally:
            node.stop()


def wait_log(node, marker, seconds, offset=0):
    path = node.work / ('owner.%d.err' % node.err_n)
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        lines = [s for s in path.read_bytes()[offset:].decode('utf-8', 'replace').splitlines() if marker in s]
        if lines:
            return lines[-1]
        if node.proc.poll() is not None:
            raise EOFError('owner died awaiting ' + marker)
        time.sleep(.05)
    raise TimeoutError('no ' + marker + ' within bound')


def merge_reports(reports):
    checked = sorted(set.intersection(*(set(r['checked']) for r in reports))) if reports else []
    return {'checked': checked, 'violations': [v for r in reports for v in r['violations']],
            'outcomes': {k: sum(r['outcomes'][k] for r in reports) for k in OUTCOMES},
            'histories': [r['history'] for r in reports]}


def crash_boundary(run, ph):
    campaign = Campaign(run, ph)
    reference, _, counts = campaign.crash_trial()
    reports, trials = [report(reference, [], [])], []
    checked = ['P1-DURABLE', 'P2-IDENTITY', 'P5-RECOVERY']
    for function in BOUNDARIES:
        n = counts['counts'][function]
        if not n:
            trials.append({'boundary': function, 'not_measured': 'zero calls in reference'})
        for k in sample_points(n, ph.get('samples_per_boundary', 3)):
            selected = '%s:%d' % (function, k)
            h, findings, notes = campaign.crash_trial(selected)
            def replay(recipe, prop, detail):
                _, fs, _ = campaign.crash_trial(selected, recipe)
                return (prop, detail) in fs
            reports.append(report(h, findings, checked if 'not_measured' not in notes else [],
                                  replay, ph.get('shrink_runs', 16)))
            trials.append(dict(notes, boundary=selected))
    # Reference is a control, not a fault-property measurement.
    out = merge_reports(reports[1:])
    out['outcomes'] = {k: out['outcomes'][k] + reference.counts()[k] for k in OUTCOMES}
    if any('not_measured' in t for t in trials):
        out['checked'] = []  # incomplete corpus must not pass with a vacuous zero
    return {'faults': out, 'reference_counts': counts['counts'], 'trials': trials,
            'recovery_bound_s': campaign.recovery,
            'status': 'not-measured' if not out['checked'] else 'ok'}


def transcript():
    from tools import msgid_measure
    return [('GROUP', {'command': 'GROUP fn.test'}),
            ('ARTICLE', {'command': 'ARTICLE ' + msgid_measure.msgid(0)}),
            ('HEAD', {'command': 'HEAD ' + msgid_measure.msgid(0)}),
            ('STAT', {'command': 'STAT ' + msgid_measure.msgid(0)}),
            ('POST', {'i': 1, 'octets': 2048}),
            ('MISUSE', {'command': 'LOAD-INVALID-COMMAND'})]


def wire_operations(recipe, history):
    from tools import rep_measure, msgid_measure
    wire, ranges = bytearray(), []
    for kind, raw_args in recipe:
        args = dict(raw_args)
        if kind == 'POST':
            body = rep_measure.article(args['i'], args['octets'])
            args.update(msgid=msgid_measure.msgid(args['i']), sha256=digest(body))
            data = b'POST\r\n' + body + b'.\r\n'
        else:
            data = args['command'].encode() + b'\r\n'
        op = history.plan(kind, args)
        op["transcript"] = True
        ranges.append((len(wire), len(wire) + len(data), op))
        wire.extend(data)
    return bytes(wire), ranges


def read_body(c, line, kind):
    body = bytearray()
    if kind in ('ARTICLE', 'HEAD') and line[:3] in (b'220', b'221'):
        while True:
            row = c.line()
            if row == b'.\r\n':
                break
            body.extend(row[1:] if row.startswith(b'..') else row)
    return bytes(body)


def framing_trial(campaign, recipe, split=None, policy=False):
    from .driver import proc_snapshot
    node, h, findings, sequence = campaign.node(), History(), [], []
    sender = None
    try:
        campaign.start(node)
        with Client(node.port, h, campaign.deadline) as seed:
            if not seed.post(0).startswith(b'240 '):
                raise RuntimeError('F6 seed refused')
        rss0 = (proc_snapshot(node.pid) or {}).get('vmrss')
        with Client(node.port, h, campaign.deadline) as c:
            wire, ranges = wire_operations(recipe, h)
            sender_errors = []
            def send():
                try:
                    cuts = [0, len(wire)] if split is None else sorted({0, min(split, len(wire)), len(wire)})
                    for lo, hi in zip(cuts, cuts[1:]):
                        for begin, end, op in ranges:
                            if begin < hi and end > lo and op['outcome'] == 'not-attempted':
                                h.sent(op)
                        c.sock.sendall(wire[lo:hi])
                        if hi != len(wire):
                            time.sleep(campaign.ph.get('fragment_pause_s', .002))
                except OSError as exc:
                    sender_errors.append(str(exc))
            sender = threading.Thread(target=send, daemon=True)
            sender.start()
            changed = False
            for _, _, op in ranges:
                c.end = time.monotonic() + campaign.deadline
                line = c.line()
                intermediate = None
                if op['kind'] == 'POST' and line.startswith(b'340 '):
                    intermediate, line = line, c.line()
                if policy and op['kind'] == 'ARTICLE' and line.startswith(b'220 ') and not changed:
                    rc, reply = campaign.control(node, h, 'policy', 'set', 'exposure-connections', '32')
                    if rc:
                        raise RuntimeError('policy change refused: ' + reply)
                    changed = True
                body = read_body(c, line, op['kind'])
                h.complete(op, line)
                if op['kind'] == 'MISUSE' and not (line[:1] in (b'4', b'5') and len(line.split()) > 1):
                    findings.append(('P8-CLIENTS', 'misuse lacked named refusal'))
                normalized = without_path_and_xref(body) if body else b''
                sequence.append([line.decode('latin-1'), hashlib.sha256(normalized).hexdigest(),
                                 intermediate.decode('latin-1') if intermediate else None])
                # A separate client must stay productive within the command deadline.
                with Client(node.port, h, campaign.deadline) as fast:
                    if not fast.command('STAT <t17-000000@example.invalid>')[0].startswith(b'223 '):
                        findings.append(('P8-CLIENTS', 'other client STAT refused'))
            sender.join(campaign.deadline)
            if sender.is_alive() or sender_errors:
                findings.append(('P8-CLIENTS', 'fragment sender did not finish: ' + repr(sender_errors)))
        rss1 = (proc_snapshot(node.pid) or {}).get('vmrss')
        if node.proc.poll() is not None:
            findings.append(('P8-CLIENTS', 'owner died'))
        return h, findings, sequence, {'rss_before_kib': rss0, 'rss_after_kib': rss1}
    except (OSError, EOFError, TimeoutError) as exc:
        findings.append(('P8-CLIENTS', 'client deadline/connection failure: ' + str(exc)))
        return h, findings, sequence, {}
    finally:
        if sender:
            sender.join(campaign.deadline)
        node.stop()


def framing(run, ph):
    campaign, recipe = Campaign(run, ph), transcript()
    reference, base_findings, sequence, base_mem = framing_trial(campaign, recipe)
    reports = [report(reference, base_findings, ['P8-CLIENTS'])]
    wire, _ = wire_operations(recipe, History())
    points = sample_points(len(wire) - 1, ph.get('split_budget', 64))
    trials = []
    for split, policy in [(p, False) for p in points] + [(None, True)]:
        h, findings, actual, mem = framing_trial(campaign, recipe, split, policy)
        if actual != sequence:
            findings.append(('P8-CLIENTS', 'reply-sequence differs from unfragmented reference'))
        if mem.get('rss_after_kib') is not None and base_mem.get('rss_after_kib') is not None:
            if mem['rss_after_kib'] - base_mem['rss_after_kib'] > ph.get('rss_slack_kib', 16384):
                findings.append(('P8-CLIENTS', 'framing RSS exceeds reference envelope'))
        def replay(ops, prop, detail):
            # Rerun BOTH controls with the reduced operation history; seed/probes are fixtures.
            reduced = [(o['kind'], o['args']) for o in ops if o.get('transcript')]
            _, f0, expected, _ = framing_trial(campaign, reduced)
            _, fs, observed, _ = framing_trial(campaign, reduced, split, policy)
            return bool(fs) or (not f0 and observed != expected)
        reports.append(report(h, findings, ['P8-CLIENTS'], replay, ph.get('shrink_runs', 16)))
        trials.append(dict(mem, split=split, policy_change=policy))
    return {'faults': merge_reports(reports), 'split_points': points,
            'transcript_octets': len(wire), 'sampled': len(points) < len(wire) - 1,
            'reference_sequence': sequence, 'trials': trials, 'command_deadline_s': campaign.deadline}


def slow_trial(campaign, selected=None):
    """The solo control and stressed window use the same four fast clients.

    `selected` is a reduced history: only its tagged client operations are
    replayed, in each client's original order. Setup/solo control stay fixed.
    """
    import re
    from .driver import proc_snapshot
    from .result import lat_stats
    node, h, findings = campaign.node(), History(), []
    duration = campaign.ph.get('duration_s', 40)
    slow_sleep = campaign.ph.get('recv_sleep_s', .01)
    stopped = threading.Event()
    threads, sockets, rss = [], [], []
    lock = threading.Lock()
    selected_keys = None if selected is None else {tuple(o['replay_key']) for o in selected if 'replay_key' in o}
    def allowed(role, n):
        return selected_keys is None or (role, n) in selected_keys
    def more(role, n):
        return selected_keys is None or any(r == role and k >= n for r, k in selected_keys)
    def fast_worker(role, end, lat, stress):
        try:
            with Client(node.port, h, campaign.deadline) as c:
                n = 0
                while time.monotonic() < end and not stopped.is_set() and (not stress or more(role, n)):
                    for text in ('GROUP fn.test', 'STAT <t17-000000@example.invalid>', 'ARTICLE <t17-000000@example.invalid>'):
                        if not stress or allowed(role, n):
                            op = h.plan(text.split()[0], {'command': text})
                            if stress:
                                op['replay_key'] = [role, n]
                            start = time.monotonic()
                            c.begin(op['kind'], op['args'], text.encode() + b'\r\n', op)
                            reply, _ = c.finish(op)
                            lat[op['kind']].append(time.monotonic() - start)
                            if reply[:3] not in (b'211', b'223', b'220'):
                                with lock:
                                    findings.append(('P8-CLIENTS', 'fast client refused: ' + repr(reply)))
                        n += 1
        except (OSError, EOFError) as exc:
            with lock:
                findings.append(('P8-CLIENTS', 'fast client missed command deadline: ' + str(exc)))

    def slow_worker(k, end):
        role = 'slow-%d' % k
        try:
            with Client(node.port, h, campaign.deadline, rcvbuf=4096) as c:
                sockets.append(c.sock)
                c.recv_size = 1
                pending = []
                # Multiple replies ensure the socket's kernel queue cannot hide
                # the backpressure of a 512 KiB response on common Linux defaults.
                for j in range(campaign.ph.get('pipeline', 8)):
                    if allowed(role, j):
                        text = 'ARTICLE <t17-%06d@example.invalid>' % (k + 1)
                        op = h.plan('ARTICLE', {'command': text})
                        op['replay_key'] = [role, j]
                        c.begin('ARTICLE', op['args'], text.encode() + b'\r\n', op)
                        pending.append(op)
                for op in pending:
                    c.end = end
                    line = c.line()
                    if not line.startswith(b'220 '):
                        h.complete(op, line)
                        if line[:1] not in (b'4', b'5') or len(line.split()) < 2:
                            findings.append(('P8-CLIENTS', 'slow reader lacked named refusal'))
                        continue
                    tail = bytearray()
                    while time.monotonic() < end and not stopped.is_set():
                        c.sock.settimeout(max(.01, end - time.monotonic()))
                        octet = c.sock.recv(1)
                        if not octet:
                            return  # uncertain; named send refusal is checked in owner log
                        tail.extend(octet)
                        if tail.endswith(b'\r\n.\r\n'):
                            h.complete(op, line)
                            break
                        if len(tail) > 5:
                            del tail[:-5]
                        time.sleep(slow_sleep)
        except (OSError, EOFError):
            pass  # incomplete slow reply is legal only with the named deadline witness below

    def poster(end):
        try:
            with Client(node.port, h, campaign.deadline) as c:
                start, n = time.monotonic(), 0
                while time.monotonic() < end and not stopped.is_set() and more('poster', n):
                    if allowed('poster', n):
                        from tools import rep_measure, msgid_measure
                        i = 100 + n
                        op = h.plan('POST', {'i': i, 'octets': 2048, 'msgid': msgid_measure.msgid(i),
                                             'sha256': digest(rep_measure.article(i, 2048))})
                        op['replay_key'] = ['poster', n]
                        if not c.post(i, op=op).startswith(b'240 '):
                            findings.append(('P8-CLIENTS', '5/s poster refused'))
                    n += 1
                    stopped.wait(max(0, start + n / 5 - time.monotonic()))
        except (OSError, EOFError) as exc:
            findings.append(('P8-CLIENTS', 'poster deadline: ' + str(exc)))

    try:
        campaign.start(node)
        with Client(node.port, h, campaign.deadline) as c:
            for i in range(5):
                if not c.post(i, 2048 if i == 0 else 512 * 1024).startswith(b'240 '):
                    raise RuntimeError('F5 seed refused')
        node.stop()
        campaign.start(node)  # cold owner cache, without dropping the machine's caches
        solo, loaded = collections.defaultdict(list), collections.defaultdict(list)
        end = time.monotonic() + campaign.ph.get('solo_s', 10)
        threads = [threading.Thread(target=fast_worker, args=('fast-%d' % k, end, solo, False), daemon=True) for k in range(4)]
        for t in threads:
            t.start()
        for t in threads:
            t.join(campaign.ph.get('solo_s', 10) + campaign.deadline)
        baseline = (proc_snapshot(node.pid) or {}).get('vmrss')
        end = time.monotonic() + duration
        threads = [threading.Thread(target=slow_worker, args=(k, end), daemon=True) for k in range(4)]
        threads += [threading.Thread(target=fast_worker, args=('fast-%d' % k, end, loaded, True), daemon=True) for k in range(4)]
        threads.append(threading.Thread(target=poster, args=(end,), daemon=True))
        for t in threads:
            t.start()
        while time.monotonic() < end:
            snap = proc_snapshot(node.pid)
            if snap and snap.get('vmrss') is not None:
                rss.append(snap['vmrss'])
            if node.proc.poll() is not None:
                findings.append(('P8-CLIENTS', 'owner died under slow readers'))
                break
            time.sleep(.05)
        stopped.set()
        for t in threads:
            t.join(campaign.deadline + 1)
        if any(t.is_alive() for t in threads):
            findings.append(('P8-CLIENTS', 'client thread outlived command deadline'))
        solo_stats = {k: lat_stats(v) for k, v in solo.items()}
        loaded_stats = {k: lat_stats(v) for k, v in loaded.items()}
        measured = True
        for op in ('GROUP', 'STAT', 'ARTICLE'):
            a, b = solo_stats.get(op, {}).get('p99_ms'), loaded_stats.get(op, {}).get('p99_ms')
            if a is None or b is None:
                measured = False
            elif b > 2 * a:
                findings.append(('P8-CLIENTS', op + ' p99 exceeds 2x solo'))
        growth = max(rss) - baseline if rss and baseline is not None else None
        if growth is None:
            measured = False
        elif growth > 4 * 512:
            findings.append(('P8-CLIENTS', 'owner RSS growth exceeds readers x reply size (2048 KiB)'))
        log = (node.work / ('owner.%d.err' % node.err_n)).read_text(errors='replace')
        refusals = re.findall(r'send refused reason=([^ ]+) cid=([^ ]+) op=([^\n]+)', log)
        refusals = [r for r in refusals if r[0] in ('send-stalled', 'reader-too-slow')]
        if len({r[1] for r in refusals}) < 4 :
            findings.append(('P8-CLIENTS', 'fewer than four named send deadline refusals within stress bound'))
        return h, findings, {'solo': solo_stats, 'loaded': loaded_stats, 'rss_growth_kib': growth,
                             'rss_bound_kib': 2048, 'send_refusals': refusals, 'measured': measured}
    finally:
        stopped.set()
        for sock in sockets:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
        for t in threads:
            t.join(campaign.deadline + 1)
        node.stop()


def slow_reader(run, ph):
    campaign = Campaign(run, ph)
    h, findings, stats = slow_trial(campaign)
    def replay(ops, prop, detail):
        _, fs, _ = slow_trial(campaign, ops)
        # Keep the same failure detail, so a removed slow client cannot turn a
        # latency finding into a missing-deadline-witness finding while shrinking.
        return (prop, detail) in fs
    return {'faults': report(h, findings, ['P8-CLIENTS'] if stats['measured'] else [],
                             replay, ph.get('shrink_runs', 8)), **stats,
            'status': 'ok' if stats['measured'] else 'not-measured',
            'cold_scope': 'owner cache after restart; filesystem cache untouched'}


def held_trial(campaign, selected=None):
    import re
    from tools import rep_measure, msgid_measure
    node, h, findings, held, notes = campaign.node(reclaim=True), History(), [], [], {}
    keys = None if selected is None else {tuple(o['replay_key']) for o in selected if 'replay_key' in o}
    def enabled(key):
        return keys is None or key in keys
    try:
        campaign.start(node)
        with Client(node.port, h, campaign.deadline) as c:
            for i in range(campaign.ph.get('readers', 4)):
                body = rep_measure.article(i, 512 * 1024).replace(b'\r\n\r\n', b'\r\nExpires: Mon, 01 Jan 2024 00:00:00 +0000\r\n\r\n', 1)
                args = {'i': i, 'octets': 512 * 1024, 'expires': '2024-01-01',
                        'msgid': msgid_measure.msgid(i), 'sha256': digest(body)}
                op = c.begin('POST', args, b'POST\r\n')
                line = c.line()
                if line.startswith(b'340 '):
                    c.sock.sendall(body + b'.\r\n')
                    line = c.line()
                h.complete(op, line)
                if not line.startswith(b'240 '):
                    raise RuntimeError('F3 seed refused: ' + repr(line))
        node.stop()
        campaign.start(node)
        for i in range(campaign.ph.get('readers', 4)):
            if not enabled(('hold', i)):
                continue
            c = Client(node.port, h, campaign.deadline, rcvbuf=4096)
            # Single-byte reads through the status and first body line prevent
            # the test client from consuming the response before maintenance.
            c.recv_size = 1
            text = 'ARTICLE ' + msgid_measure.msgid(i)
            op = c.begin('ARTICLE', {'command': text}, text.encode() + b'\r\n')
            op['replay_key'] = ['hold', i]
            line = c.line()
            if not line.startswith(b'220 '):
                h.complete(op, line)
                c.close()
                if line[:1] not in (b'4', b'5') or len(line.split()) < 2:
                    findings.append(('P4-RECLAIM', 'initial ARTICLE lacked named refusal'))
                continue
            prefix = c.line()  # stall mid-body (inside ARTICLE's header block)
            held.append((c, op, line, prefix, i))
        notes['pins_before'] = campaign.control(node, h, 'pins')[1]
        if enabled(('checkpoint', 0)):
            err = node.work / ('owner.%d.err' % node.err_n)
            offset = err.stat().st_size
            rc, reply = campaign.control(node, h, 'store', 'checkpoint')
            if rc:
                raise RuntimeError('checkpoint refused: ' + reply)
            notes['publication'] = wait_log(node, 'CHECKPOINT auto sequence=', campaign.recovery, offset)
        if enabled(('reclaim', 0)):
            rc, reply = campaign.control(node, h, 'retention', 'expire', 'fn.test', 'purge', '30')
            if rc:
                raise RuntimeError('expiry policy refused: ' + reply)
            err = node.work / ('owner.%d.err' % node.err_n)
            offset = err.stat().st_size
            end = time.monotonic() + campaign.recovery
            while True:
                rc, reply = campaign.control(node, h, 'store', 'reclaim')
                if not rc or not any(w in reply for w in ('queued', 'in-flight')) or time.monotonic() >= end:
                    break
                time.sleep(.1)
            if rc:
                raise RuntimeError('reclaim refused: ' + reply)
            notes['reclaim'] = wait_log(node, 'RECLAIM installed records=', campaign.recovery, offset)
            match = re.search(r'reclaimed=(\d+)', notes['reclaim'])
            if not match or int(match[1]) == 0:
                raise RuntimeError('reclaim installed without reclaiming any test article')
        # Put different bytes into the post-reclaim store before releasing readers.
        if enabled(('replacement', 0)):
            with Client(node.port, h, campaign.deadline) as c:
                if not c.post(999, 512 * 1024).startswith(b'240 '):
                    raise RuntimeError('replacement POST refused')
                h.ops[-1]['replay_key'] = ['replacement', 0]
        truncated = 0
        for c, op, line, prefix, i in held:
            c.recv_size = 65536
            c.end = time.monotonic() + campaign.deadline
            body = bytearray(prefix)
            try:
                while True:
                    row = c.line()
                    if row == b'.\r\n':
                        break
                    body.extend(row[1:] if row.startswith(b'..') else row)
                h.complete(op, line)
                expected = next(o['args']['sha256'] for o in h.ops if o['kind'] == 'POST' and o['args'].get('i') == i)
                if digest(bytes(body)) != expected:
                    findings.append(('P4-RECLAIM', 'resumed ARTICLE changed accepted bytes: ' + str(i)))
            except (OSError, EOFError):
                truncated += 1
        log = (node.work / ('owner.%d.err' % node.err_n)).read_text(errors='replace')
        named = set(re.findall(r'send refused reason=(?:send-stalled|reader-too-slow) cid=([^ ]+) op=(?:article|tail)', log))
        notes['named_refusal_clients'] = sorted(named)
        if truncated > len(named):
            findings.append(('P4-RECLAIM', 'truncated held replies without distinct named refusals'))
        # Record maintenance operations as replayable units; control helpers keep
        # their complete reply/status observations in the same history.
        for op in h.ops:
            if op['kind'] == 'CONTROL':
                words = op['args']['words']
                if words == ['store', 'checkpoint']:
                    op['replay_key'] = ['checkpoint', 0]
                elif words[:2] in (['store', 'reclaim'], ['retention', 'expire']):
                    op['replay_key'] = ['reclaim', 0]
        return h, findings, notes
    except (OSError, EOFError, TimeoutError) as exc:
        findings.append(('P4-RECLAIM', 'held-reader connection/deadline failure: ' + str(exc)))
        return h, findings, notes
    finally:
        for c, *_ in held:
            c.close()
        node.stop()


def held_reader(run, ph):
    campaign = Campaign(run, ph)
    h, findings, notes = held_trial(campaign)
    def replay(ops, prop, detail):
        _, fs, _ = held_trial(campaign, ops)
        return (prop, detail) in fs
    return {'faults': report(h, findings, ['P4-RECLAIM'], replay, ph.get('shrink_runs', 8)), **notes}
