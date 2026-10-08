"""Process-death fault cells and their external NNTP oracle (no host decisions).

The store filesystem's fdatasync durability is an assumption, not established
by killing a process. Histories describe client observations, never acceptance
inferred from a successful send. SHA256 here is only a test byte comparator.
"""
from __future__ import annotations

import collections
import hashlib
import contextlib
import json
import os
import socket
import threading
import time
from pathlib import Path

from .peers import without_path_and_xref

PROPERTIES = {
    "P1-DURABLE": "Every POST with a read 240 survives restart byte-identically, Path/Xref excepted.",
    "P2-IDENTITY": "Only attempted articles exist; each Message-ID has exactly its attempted octets; uncertain POSTs are whole or absent.",
    "P5-RECOVERY": "After each process death, including recovery death, LISTENING and a productive POST occur within the stated bound.",
    "P8-CLIENTS": "Client bytes cannot kill the owner, exceed other clients' deadlines or grow RSS without bound; misuse is refused by name.",
    "P4-RECLAIM": "A held ARTICLE across publication/checkpoint/reclaim returns accepted octets or a named refusal, never another article's bytes.",
}
OUTCOMES = ("not-attempted", "attempted-uncertain", "completed")


INJECTED = (b"path:", b"xref:", b"injection-info:", b"injection-date:")


def accepted_form(octets):
    """The octets a client POSTed, as the server stores them minus the headers the injecting
    agent adds (RFC 5537 3.5: Path, Injection-Info, Injection-Date; and Xref for the serving
    agent).  The served article of a POST carries `Injection-Info: <host>` and the first F2
    survey flagged every article as changed until this was dropped too."""
    head, _, body = octets.partition(b"\r\n\r\n")
    kept = [l for l in head.split(b"\r\n") if not l.lower().startswith(INJECTED)]
    return b"\r\n".join(kept) + b"\r\n\r\n" + body


def digest(octets):
    return hashlib.sha256(accepted_form(octets)).hexdigest()


TRACE_SCHEMA = 1


class TraceRecorder:
    """The wire order a run actually produced, as steps (schema 1, for replay).

    Appended under one lock by Client and Campaign, so the list is the order the
    run's threads reached the socket, not a reconstruction. `sequential` is read
    off the steps: a send on one connection while another connection still owes
    the rest of a reply, or two sends on different connections with no read step
    between them, make the trace interleaved. Inside `inventory()` only the one
    inventory step is recorded.
    """
    def __init__(self):
        self.lock = threading.RLock()
        self.steps, self.interleaved = [], False
        self.started, self.next_conn, self.fixed = False, 0, None
        self.incomplete, self.last_send = set(), None

    def _add(self, step):
        self.steps.append(step)
        return len(self.steps) - 1

    def _send_check(self, who):
        if (self.incomplete - {who}) or (self.last_send not in (None, who)):
            self.interleaved = True
        self.last_send = who

    def start(self, crash=None):
        with self.lock:
            idx = self._add({"t": "restart" if self.started else "start"})
            self.started = True
            if crash is not None:
                self._add({"t": "crash", "boundary": crash[0], "hit": int(crash[1])})
            return idx

    def conn(self):
        with self.lock:
            if self.fixed is not None:
                return -1
            cid, self.next_conn = self.next_conn, self.next_conn + 1
            self._add({"t": "conn", "c": cid})
            return cid

    def send(self, cid, octets):
        with self.lock:
            if self.fixed is not None:
                return self.fixed
            self._send_check(cid)
            return self._add({"t": "send", "c": cid, "hex": bytes(octets).hex()})

    def read(self, cid, until):
        with self.lock:
            if self.fixed is not None:
                return self.fixed
            self.last_send = None
            self.incomplete.add(cid)
            return self._add({"t": "read", "c": cid, "until": until})

    def upgrade(self, idx, until):
        with self.lock:
            if self.fixed is None and self.steps[idx]["t"] == "read":
                self.steps[idx]["until"] = until

    def done(self, cid):
        with self.lock:
            self.incomplete.discard(cid)

    def close(self, cid):
        with self.lock:
            self.incomplete.discard(cid)
            if self.fixed is None:
                self._add({"t": "close", "c": cid})

    def control(self, words):
        # An operator verb has no schema step of its own; recorded as an extension.
        with self.lock:
            self._send_check("control")
            self.last_send = None
            return self._add({"t": "control", "words": list(words)})

    @contextlib.contextmanager
    def inventory(self):
        with self.lock:
            self._send_check("inventory")
            self.last_send = None
            self.fixed = self._add({"t": "inventory"})
        try:
            yield self.fixed
        finally:
            with self.lock:
                self.fixed = None

    def snapshot(self, ops):
        with self.lock:
            return {"steps": [dict(x) for x in self.steps], "sequential": not self.interleaved,
                    "ops": [dict(o, step=o.get("step")) for o in ops]}


class History:
    def __init__(self):
        self.ops = []
        self.lock = threading.Lock()
        self.recorder = TraceRecorder()

    def plan(self, kind, args):
        with self.lock:
            op = {"op_id": len(self.ops), "kind": kind, "args": args,
                  "args_digest": hashlib.sha256(json.dumps(args, sort_keys=True).encode()).hexdigest(),
                  "send_time": None, "outcome": "not-attempted", "reply_line": None, "step": None}
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


def report(history, findings, checked, replay=None, budget=32, tracer=None):
    violations = []
    tagged = any(o.get('replayable') or o.get('transcript') or 'replay_key' in o for o in history.ops)
    variable = [o for o in history.ops if not tagged or o.get('replayable') or o.get('transcript') or 'replay_key' in o]
    variable_ids = {o['op_id'] for o in variable}
    fixed = [o for o in history.ops if o['op_id'] not in variable_ids]
    # One shrink per property: a trial can carry one finding per article (say, 50 lost POSTs),
    # and shrinking each detail separately exhausted a 2 h cell on one boundary (f2b-g41).
    # The first detail is shrunk; the rest are listed beside it.
    by_prop = {}
    for prop, detail in sorted(set(findings)):
        by_prop.setdefault(prop, []).append(detail)
    for prop, details in by_prop.items():
        detail = details[0]
        errors = []
        replayed = {}
        def fails(candidate):
            try:
                hit = replay(candidate, prop, detail)
                if hit and tracer is not None:
                    replayed['trace'] = tracer.snapshot(tracer.last_history)
                return hit
            except Exception as exc:
                # A replay setup failure is not reproduction of this property.
                errors.append(type(exc).__name__ + ': ' + str(exc))
                return False
        short, info = (shrink(variable, fails, budget) if replay else
                       (variable, {"runs": 0, "minimal": "not-replayed"}))
        info.update(fixed_operations=len(fixed), replay_errors=errors)
        violation = {"property": prop, "detail": detail, "details": details, "history_len": len(history.ops),
                     "shrunk_history": short, "fixed_history": fixed, "shrink": info}
        if tracer is not None:
            # The last successful replay is the shrunk history's run; with no
            # reduction the original run is its own replay.
            violation["trace"] = tracer.emit(replayed.get("trace") or tracer.snapshot(history),
                                             "violation-%d-%s" % (len(violations), prop))
        violations.append(violation)
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
        self.rec, self.closed = history.recorder, False
        self.cid = self.rec.conn()
        self.buffer = bytearray()
        self.recv_size = 65536
        self.end = time.monotonic() + deadline
        self.mark_read("line")
        greeting = self.line()
        self.read_done()
        if greeting[:3] not in (b"200", b"201"):
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

    def send_raw(self, wire):
        """Record then write exactly these octets; returns the trace step index."""
        idx = self.rec.send(self.cid, wire)
        self.sock.sendall(wire)
        return idx

    def mark_read(self, until):
        self.last_read = self.rec.read(self.cid, until)
        return self.last_read

    def read_done(self):
        self.rec.done(self.cid)

    def begin(self, kind, args, wire, op=None):
        self.end = time.monotonic() + self.deadline
        op = op if op is not None else self.history.plan(kind, args)
        self.history.sent(op)
        op["step"] = self.send_raw(wire)
        return op

    def finish(self, op):
        self.mark_read("line")
        line = self.line()
        body = bytearray()
        if line[:3] in (b"220", b"221", b"222", b"211", b"215", b"224") and (
                op["kind"] != "GROUP"):
            self.rec.upgrade(self.last_read, "dot")
            while True:
                row = self.line()
                if row == b".\r\n":
                    break
                body.extend(row[1:] if row.startswith(b"..") else row)
        self.history.complete(op, line)
        self.read_done()
        return line, bytes(body)

    def command(self, text):
        op = self.begin(text.split()[0], {"command": text}, text.encode() + b"\r\n")
        return self.finish(op)

    def post(self, i, octets=2048, op=None):
        from tools import rep_measure, msgid_measure
        article = rep_measure.article(i, octets)
        args = {"i": i, "octets": octets, "msgid": msgid_measure.msgid(i), "sha256": digest(article)}
        return self.post_article(article, args, op)

    def post_article(self, article, args, op=None):
        op = self.begin("POST", args, b"POST\r\n", op)
        self.mark_read("line")
        line = self.line()
        if line.startswith(b"340 "):
            self.send_raw(article + b".\r\n")
            self.mark_read("line")
            line = self.line()
        self.history.complete(op, line)
        self.read_done()
        return line

    def close(self):
        if not self.closed:
            self.closed = True
            self.rec.close(self.cid)
        self.sock.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


def inventory(port, history, deadline=10):
    """Enumerate every group/article, checking both number and Message-ID routes."""
    present = {}
    with history.recorder.inventory() as step, Client(port, history, deadline) as c:
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
        self.traces, self.trace_serial, self.last_history, self.meta = [], 0, None, {}
        self.deadline = ph.get('command_deadline_s', 10)
        self.recovery = ph.get('recovery_s', 60)

    def history(self):
        self.last_history = History()
        return self.last_history

    def snapshot(self, history):
        return dict(self.meta, **history.recorder.snapshot(history.ops))

    def emit(self, trace, tag):
        """Write one replayable trace; returns its path. FN_LOAD_TRACE_DIR overrides the default directory."""
        from pathlib import Path
        from .driver import BOX_BASE
        cell = getattr(self.run, 'cell_id', None) or 'F'
        label = getattr(self.run, 'label', None) or cell
        self.trace_serial += 1
        ident = '%s-%s-%03d' % (cell, tag, self.trace_serial)
        directory = Path(os.environ.get('FN_LOAD_TRACE_DIR') or os.path.join(BOX_BASE, 'fault-traces', cell))
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / ('%s-%s.json' % (label, ident))
        body = dict(trace, schema=TRACE_SCHEMA, cell=cell, id=ident)
        path.write_text(json.dumps(body))
        self.traces.append(str(path))
        return str(path)

    def node(self, hook=False, reclaim=False):
        from pathlib import Path
        parent = self.run.node
        self.serial += 1
        work = parent.work / ('fault-%04d' % self.serial)
        work.mkdir()
        hook_name = 'f2-crash.lisp' if hook is True else hook
        hooks = [Path(__file__).resolve().parents[2] / 'planning/evidence/load/hooks' / hook_name] if hook else []
        node = type(parent)(parent.target, work, parent.flags, parent.groups,
                            parent.env['SBCL_USER_ARGS'], hooks, work / 'gc.log', {}, 1,
                            parent.heap_mode)
        # The environment of the driving shell must not accidentally arm init/heap/control.
        node.env = fault_environment(node.env)
        node.init()
        self.meta = {'schema': TRACE_SCHEMA, 'cell': getattr(self.run, 'cell_id', None),
                     'store': {'init_flags': list(node.flags), 'groups': list(node.groups), 'fixture': None},
                     'sbcl_user_args': node.env['SBCL_USER_ARGS']}
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
        op['step'] = h.recorder.control(words)
        env = fault_environment(node.env)
        p = subprocess.run(node.argv(*words), env=env, capture_output=True, timeout=self.recovery)
        reply = (p.stdout + p.stderr).decode('utf-8', 'replace').strip()
        h.complete(op, (reply + '\r\n').encode())
        op['rc'] = p.returncode
        return p.returncode, reply

    def start(self, node, h, crash=None):
        """`crash` is (boundary, hit), the cut armed for this start; recorded after its start/restart step."""
        h.recorder.start(crash)
        elapsed = node.start(timeout=self.recovery)
        (node.work / 'owner.pid').write_text(str(node.pid) + '\n')
        return elapsed

    def post_plan(self, h, count):
        from tools import rep_measure, msgid_measure
        return [h.plan('POST', {'i': i, 'octets': 2048, 'msgid': msgid_measure.msgid(i),
                                'sha256': digest(rep_measure.article(i, 2048))}) for i in range(count)]

    def crash_trial(self, selected=None, recipe=None):
        import subprocess
        node, h, findings, notes = self.node(hook=True), self.history(), [], {}
        count_path, go = node.work / 'counts', node.work / 'go'
        witness = node.work / 'crash'
        witness.touch()  # same pre-existing inode survives abort; hook fsyncs contents
        node.env.update(FN_LOAD_CRASH_GO=str(go), FN_LOAD_CRASH_RECORD=str(witness))
        if selected:
            node.env['FN_LOAD_CRASH_AT'] = selected
        else:
            node.env['FN_LOAD_CRASH_COUNT'] = str(count_path)
        try:
            self.start(node, h, tuple(selected.rsplit(':', 1)) if selected else None)
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
                    self.start(node, h, ('*', 1))
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
                    self.start(node, h)
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


def partial(run, row):
    """One line per finished trial in the run's output dir, so a cell killed by its timeout keeps its findings."""
    try:
        out = Path(run.args.out) if getattr(getattr(run, "args", None), "out", None) else None
        if out is not None:
            out.mkdir(parents=True, exist_ok=True)
            with open(out / ("%s-trials.jsonl" % getattr(run, "label", "fault")), "a") as f:
                f.write(json.dumps(row, default=str) + "\n")
    except OSError:
        pass


def crash_boundary(run, ph):
    campaign = Campaign(run, ph)
    reference, _, counts = campaign.crash_trial()
    campaign.emit(campaign.snapshot(reference), 'reference')
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
                                  replay, ph.get('shrink_runs', 16), campaign))
            trials.append(dict(notes, boundary=selected))
            partial(run, {'boundary': selected, 'notes': notes,
                          'findings': sorted({(p, str(d)) for p, d in findings})})
    # Reference is a control, not a fault-property measurement.
    out = merge_reports(reports[1:])
    out['outcomes'] = {k: out['outcomes'][k] + reference.counts()[k] for k in OUTCOMES}
    if any('not_measured' in t for t in trials):
        out['checked'] = []  # incomplete corpus must not pass with a vacuous zero
    out['traces'] = campaign.traces
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
        c.rec.upgrade(c.last_read, 'dot')
        while True:
            row = c.line()
            if row == b'.\r\n':
                break
            body.extend(row[1:] if row.startswith(b'..') else row)
    return bytes(body)


def framing_trial(campaign, recipe, split=None, policy=False):
    from .driver import proc_snapshot
    node, h, findings, sequence = campaign.node(), campaign.history(), [], []
    sender = None
    try:
        campaign.start(node, h)
        with Client(node.port, h, campaign.deadline) as seed:
            if not seed.post(0).startswith(b'240 '):
                raise RuntimeError('F6 seed refused')
        rss0 = (proc_snapshot(node.pid) or {}).get('vmrss')
        with Client(node.port, h, campaign.deadline) as c:
            wire, ranges = wire_operations(recipe, h)
            sender_errors = []
            def send():
                try:
                    if split == 'all':      # every octet its own write: every boundary at once
                        cuts = list(range(len(wire) + 1))
                    else:
                        cuts = [0, len(wire)] if split is None else sorted({0, min(split, len(wire)), len(wire)})
                    for lo, hi in zip(cuts, cuts[1:]):
                        for begin, end, op in ranges:
                            if begin < hi and end > lo and op['outcome'] == 'not-attempted':
                                h.sent(op)
                        step = c.send_raw(wire[lo:hi])
                        for begin, end, op in ranges:
                            if begin < hi and end > lo and op['step'] is None:
                                op['step'] = step
                        if hi != len(wire):
                            time.sleep(campaign.ph.get('fragment_pause_s', .002))
                except OSError as exc:
                    sender_errors.append(str(exc))
            sender = threading.Thread(target=send, daemon=True)
            sender.start()
            changed = False
            for _, _, op in ranges:
                c.end = time.monotonic() + campaign.deadline
                c.mark_read('line')
                line = c.line()
                intermediate = None
                if op['kind'] == 'POST' and line.startswith(b'340 '):
                    c.mark_read('line')
                    intermediate, line = line, c.line()
                if policy and op['kind'] == 'ARTICLE' and line.startswith(b'220 ') and not changed:
                    rc, reply = campaign.control(node, h, 'policy', 'set', 'exposure-connections', '32')
                    if rc:
                        raise RuntimeError('policy change refused: ' + reply)
                    changed = True
                body = read_body(c, line, op['kind'])
                h.complete(op, line)
                c.read_done()
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
    campaign.emit(campaign.snapshot(reference), 'reference')
    reports = [report(reference, base_findings, ['P8-CLIENTS'], tracer=campaign)]
    wire, _ = wire_operations(recipe, History())
    points = sample_points(len(wire) - 1, ph.get('split_budget', 64))
    trials = []
    for split, policy in [(p, False) for p in points] + [(None, True), ('all', False), ('all', True)]:
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
        reports.append(report(h, findings, ['P8-CLIENTS'], replay, ph.get('shrink_runs', 16), campaign))
        trials.append(dict(mem, split=split, policy_change=policy))
    return {'faults': dict(merge_reports(reports), traces=campaign.traces), 'split_points': points,
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
    node, h, findings = campaign.node(), campaign.history(), []
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
                    c.mark_read('line')
                    line = c.line()
                    if not line.startswith(b'220 '):
                        h.complete(op, line)
                        c.read_done()
                        if line[:1] not in (b'4', b'5') or len(line.split()) < 2:
                            findings.append(('P8-CLIENTS', 'slow reader lacked named refusal'))
                        continue
                    c.mark_read('dot')  # stays owed (interleaved) unless the 1-byte reader reaches the dot
                    tail = bytearray()
                    while time.monotonic() < end and not stopped.is_set():
                        c.sock.settimeout(max(.01, end - time.monotonic()))
                        octet = c.sock.recv(1)
                        if not octet:
                            return  # uncertain; named send refusal is checked in owner log
                        tail.extend(octet)
                        if tail.endswith(b'\r\n.\r\n'):
                            h.complete(op, line)
                            c.read_done()
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
        campaign.start(node, h)
        with Client(node.port, h, campaign.deadline) as c:
            for i in range(5):
                if not c.post(i, 2048 if i == 0 else 512 * 1024).startswith(b'240 '):
                    raise RuntimeError('F5 seed refused')
        node.stop()
        campaign.start(node, h)  # cold owner cache, without dropping the machine's caches
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
    campaign.emit(campaign.snapshot(h), 'reference')
    faults_out = report(h, findings, ['P8-CLIENTS'] if stats['measured'] else [],
                        replay, ph.get('shrink_runs', 8), campaign)
    faults_out['traces'] = campaign.traces
    return {'faults': faults_out, **stats,
            'status': 'ok' if stats['measured'] else 'not-measured',
            'cold_scope': 'owner cache after restart; filesystem cache untouched'}


def held_trial(campaign, selected=None):
    import re
    from tools import rep_measure, msgid_measure
    node, h, findings, held, notes = campaign.node(reclaim=True), campaign.history(), [], [], {}
    keys = None if selected is None else {tuple(o['replay_key']) for o in selected if 'replay_key' in o}
    def enabled(key):
        return keys is None or key in keys
    try:
        campaign.start(node, h)
        with Client(node.port, h, campaign.deadline) as c:
            for i in range(campaign.ph.get('readers', 4)):
                body = rep_measure.article(i, 512 * 1024).replace(b'\r\n\r\n', b'\r\nExpires: Mon, 01 Jan 2024 00:00:00 +0000\r\n\r\n', 1)
                args = {'i': i, 'octets': 512 * 1024, 'expires': '2024-01-01',
                        'msgid': msgid_measure.msgid(i), 'sha256': digest(body)}
                op = c.begin('POST', args, b'POST\r\n')
                c.mark_read('line')
                line = c.line()
                if line.startswith(b'340 '):
                    c.send_raw(body + b'.\r\n')
                    c.mark_read('line')
                    line = c.line()
                h.complete(op, line)
                c.read_done()
                if not line.startswith(b'240 '):
                    raise RuntimeError('F3 seed refused: ' + repr(line))
        node.stop()
        campaign.start(node, h)
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
            c.mark_read('line')
            line = c.line()
            if not line.startswith(b'220 '):
                h.complete(op, line)
                c.read_done()
                c.close()
                if line[:1] not in (b'4', b'5') or len(line.split()) < 2:
                    findings.append(('P4-RECLAIM', 'initial ARTICLE lacked named refusal'))
                continue
            c.mark_read('line')  # stays owed: the reply is held mid-body
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
                c.mark_read('dot')
                while True:
                    row = c.line()
                    if row == b'.\r\n':
                        break
                    body.extend(row[1:] if row.startswith(b'..') else row)
                h.complete(op, line)
                c.read_done()
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
    campaign.emit(campaign.snapshot(h), 'reference')
    faults_out = report(h, findings, ['P4-RECLAIM'], replay, ph.get('shrink_runs', 8), campaign)
    faults_out['traces'] = campaign.traces
    return {'faults': faults_out, **notes}


def fault_environment(env):
    """Fault selectors belong only to the explicitly armed owner process."""
    return {k: v for k, v in env.items()
            if not k.startswith(('FN_LOAD_CRASH_', 'FN_LOAD_F1_', 'FN_LOAD_F4_'))}


def collision_search(candidates, tag, count, bits=8, bucket=0):
    """Finite candidate search; TAG is an oracle, never a Python MAC reimplementation.

    Return fewer than count on exhaustion. The caller must not call that a
    saturated trial. Low-bit collisions alone do not establish saturation.
    """
    if count < 1 or not 1 <= bits <= 60 or not 0 <= bucket < (1 << bits):
        raise ValueError('invalid collision search geometry')
    result, seen = [], set()
    for mid in candidates:
        if mid not in seen and tag(mid) & ((1 << bits) - 1) == bucket:
            seen.add(mid)
            result.append(mid)
            if len(result) == count:
                break
    return result


def named_refusal(line):
    words = (line or '').strip().split(maxsplit=1)
    return len(words) == 2 and len(words[0]) == 3 and words[0].isdigit() and words[0][0] in '45'


def verify_slot_reuse(history, evidence):
    """F1 external oracle, with coverage independent of any discovered violation."""
    findings = []
    reads = [o for o in history if o.get('probe') == 'F1'
             and o.get('route') == evidence.get('route')]
    accepted = {}
    for op in history:
        if (op['kind'] == 'POST' and op['outcome'] == 'completed'
                and (op['reply_line'] or '').startswith('240 ')):
            accepted.setdefault(op['args']['msgid'], op['args']['sha256'])
    for op in reads:
        mid, line = op['args']['msgid'], op.get('reply_line') or ''
        if op['outcome'] != 'completed':
            # A timeout is neither accepted bytes nor a named refusal.
            findings.append(('P4-RECLAIM', 'incomplete F1 reply: ' + mid))
        elif line.startswith('220 '):
            if mid not in accepted or op.get('body_sha256') != accepted[mid]:
                findings.extend((p, 'F1 returned changed bytes: ' + mid)
                                for p in ('P4-RECLAIM', 'P2-IDENTITY'))
        elif not named_refusal(line):
            findings.append(('P4-RECLAIM', 'F1 reply lacked named refusal: ' + mid))
    measured = bool(reads and any(o.get('held') for o in reads)
                    and evidence.get('held') and evidence.get('released')
                    and evidence.get('publication') and evidence.get('drop_calls', 0) > 0
                    and evidence.get('installs', 0) > 0
                    and evidence.get('evictions', 0) > 0 and evidence.get('reuses', 0) > 0
                    and (evidence.get('route') != 'W' or evidence.get('funded_pool'))
                    and evidence.get('complete'))
    return findings, ['P4-RECLAIM', 'P2-IDENTITY'] if measured else []


def verify_index_saturation(history, health, existing, absent):
    """F4: both lookup routes, both epochs, original bytes and duplicate refusal."""
    findings, complete = [], bool(existing and absent)
    accepted = {}
    duplicates = collections.Counter()
    for op in history:
        if op['kind'] != 'POST':
            continue
        mid = op['args']['msgid']
        line = op.get('reply_line') or ''
        if op['args'].get('duplicate'):
            duplicates[mid, op['args']['duplicate']] += 1
            if op['outcome'] != 'completed':
                complete = False
            elif line.startswith('240 '):
                findings.append(('P2-IDENTITY', 'duplicate accepted: ' + mid))
            elif not named_refusal(line):
                findings.append(('P2-IDENTITY', 'duplicate lacked named refusal: ' + mid))
        elif op['outcome'] == 'completed' and line.startswith('240 '):
            accepted.setdefault(mid, op['args']['sha256'])
    for mid, value in existing.items():
        if accepted.get(mid) != value or any(duplicates[mid, kind] != 1 for kind in ('same', 'different')):
            complete = False
    probes = {(o.get('epoch'), o['kind'], o['args'].get('msgid')): o
              for o in history if o.get('probe') == 'F4'}
    for epoch in ('before', 'after'):
        for mid in list(existing) + list(absent):
            for kind, code in (('STAT', '223 '), ('ARTICLE', '220 ')):
                op = probes.get((epoch, kind, mid))
                if op is None or op['outcome'] != 'completed':
                    complete = False
                    continue
                line = op.get('reply_line') or ''
                if mid in existing:
                    if (not line.startswith(code) or mid not in line.split()
                            or (kind == 'ARTICLE' and op.get('body_sha256') != existing[mid])):
                        findings.append(('P2-IDENTITY', epoch + ' changed/missing ' + kind + ': ' + mid))
                elif not line.startswith('430 ') or not named_refusal(line):
                    findings.append(('P2-IDENTITY', epoch + ' absent ID not absent: ' + mid))
    # Saturation (unplaced > 0) is reported beside the verdict, not required for it: on train 45
    # 2,104 IDs with 8-bit tag collisions left the linear-hash table at unplaced 0 (it split), and
    # full-tag collisions (60 bits) are not constructible. The verdict's scope says which.
    return findings, ['P2-IDENTITY'] if complete else []


def index_saturated(health):
    return all(len(health.get(epoch, [])) == 4 and health[epoch][2] > 0 for epoch in ('before', 'after'))


def fault_probe(c, mid, cell, epoch=None, held=False, route=None):
    text = 'ARTICLE ' + mid
    op = c.begin('ARTICLE', {'command': text, 'msgid': mid}, text.encode() + b'\r\n')
    op.update(probe=cell, epoch=epoch, held=held, route=route)
    line, body = c.finish(op)
    if line.startswith(b'220 '):
        op['body_sha256'] = digest(body)
    return op


def wait_file(path, seconds, predicate=lambda text: bool(text)):
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        text = path.read_text() if path.exists() else ''
        if predicate(text):
            return text
        time.sleep(.05)
    raise TimeoutError('hook witness missing: ' + str(path))


F1_FUNCTIONS = {'E': 'fnn-extent-cache-store', 'W': 'fnn-extent-window-release'}
F1_POOL = ('Default startup: fnn-owner-page-read-startup -> '
           'fn-owner-page-read-install-default -> fn-owner-page-read-install-baseline. '
           'No external enable switch: [resources] cold_heap_octets/cold_workers/'
           'cold_descriptors/cold_read_ids/cold_file_ids are parsed but '
           'fn-prstartup-default-plan refuses explicit cold policy as '
           ':unpriced-complete-cold-profile; leave them absent.')


def f1_evidence(text, route='E'):
    """Match the route/function; partial, malformed and timeout rows cannot pass."""
    function = F1_FUNCTIONS[route]
    out = dict(route=route, held=False, held_function=function, witness=text,
               installs=0, drop_calls=0, evictions=0, reuses=0)
    for row in text.splitlines(keepends=True):
        if not row.endswith('\n'):
            continue
        fields = row.split()
        if fields == ['pool', route, 'funded']:
            out['funded_pool'] = True
        if fields == ['pool', route, 'unfunded']:
            out['funded_pool'] = False
        if fields[1:3] != [route, function]:
            continue
        if len(fields) == 4 and fields[0] == 'held' and fields[3].isdigit() and int(fields[3]) > 0:
            out.update(held=True, held_call=int(fields[3]))
        if (len(fields) == 7 and fields[0] in ('released', 'timeout')
                and out.get('held') and all(v.isdigit() for v in fields[3:])):
            out.update(zip(('installs', 'drop_calls', 'evictions', 'reuses'), map(int, fields[3:])))
            out[fields[0]] = True
    if out.get('timeout'):
        out.pop('released', None)
    return out


def fault_result(campaign, h, findings, checked, notes, required):
    # Wire traces omit file-trigger timing. Do not advertise them as replayable
    # or shrink them against an unhooked node (a different experiment).
    trace = campaign.snapshot(h)
    trace.update(sequential=False, hook_protocol=notes)
    campaign.emit(trace, 'reference')
    out = report(h, findings, checked)
    out['traces'] = campaign.traces
    out['not_measured'] = {'faults.%s.violations' % p: notes.get('reason', 'required hook evidence incomplete')
                           for p in required if p not in checked}
    result = {'faults': out, **notes}
    if not checked:
        result.update(status='not-measured', reason=notes.get('reason', 'required hook evidence incomplete'))
    return result


def f1_route(campaign, h, ph, route):
    from tools import msgid_measure
    node = release = witness = None
    notes, workers, errors = dict(route=route, pool_configuration=F1_POOL), [], []
    released = threading.Event()
    def launch(action):
        def guarded():
            try:
                action()
            except Exception as exc:
                errors.append(type(exc).__name__ + ': ' + str(exc))
        worker = threading.Thread(target=guarded, daemon=True)
        workers.append(worker)
        worker.start()
        return worker
    try:
        node = campaign.node(hook='f1-delay.lisp')
        notes['work'] = str(node.work)
        go, release, witness = (node.work / n for n in ('f1-arm', 'f1-release', 'f1-witness'))
        campaign.start(node, h)
        with Client(node.port, h, campaign.deadline) as c:
            for i in range(ph.get('cold_reads', 24) + 1):
                if not c.post(i, 524288).startswith(b'240 '):
                    raise RuntimeError('F1 seed refused')
        # Persist extents before making the owner's read cache cold.
        offset = (node.work / ('owner.%d.err' % node.err_n)).stat().st_size
        rc, reply = campaign.control(node, h, 'store', 'checkpoint')
        if rc:
            raise RuntimeError('F1 seed checkpoint: ' + reply)
        wait_log(node, 'CHECKPOINT auto sequence=', campaign.recovery, offset)
        node.stop()
        node.env.update(FN_LOAD_F1_ARM=str(go), FN_LOAD_F1_RELEASE=str(release),
                        FN_LOAD_F1_WITNESS=str(witness), FN_LOAD_F1_N=str(ph.get('hold_n', 1)),
                        FN_LOAD_F1_ROUTE=route,
                        FN_LOAD_F1_SECONDS=str(campaign.recovery * 3),
                        FN_LOAD_F1_CACHE=str(ph.get('cache_entries', 1)))
        campaign.start(node, h)
        go.touch()
        def cold():
            with Client(node.port, h, campaign.recovery * 3) as c:
                fault_probe(c, msgid_measure.msgid(0), 'F1', held=True, route=route)
        launch(cold)
        wait_file(witness, campaign.recovery, lambda s: f1_evidence(s, route).get('held'))
        offset = (node.work / ('owner.%d.err' % node.err_n)).stat().st_size
        def publish():
            rc, reply = campaign.control(node, h, 'store', 'checkpoint')
            if rc:
                raise RuntimeError('F1 checkpoint during hold: ' + reply)
            line = wait_log(node, 'CHECKPOINT auto sequence=', campaign.recovery, offset)
            if not released.is_set():
                notes['publication'] = line
        def churn():
            with Client(node.port, h, campaign.recovery * 3) as c:
                for i in range(1, ph.get('cold_reads', 24) + 1):
                    fault_probe(c, msgid_measure.msgid(i), 'F1', route=route)
        # A blocked publication must not prevent dispatch of the competing reads.
        competing = [launch(publish), launch(churn)]
        end = time.monotonic() + campaign.recovery
        for worker in competing:
            worker.join(max(0, end - time.monotonic()))
        released.set()
        release.touch()
        wait_file(witness, campaign.recovery, lambda s: f1_evidence(s, route).get('released'))
    except Exception as exc:
        notes['reason'] = type(exc).__name__ + ': ' + str(exc)
    finally:
        released.set()
        if release is not None:
            release.touch()  # Unblock our hook before asking our owner to stop.
        for worker in workers:
            worker.join(campaign.recovery)
        if node is not None:
            node.stop()
        for worker in workers:
            worker.join(5)
    notes.update(f1_evidence(witness.read_text() if witness and witness.exists() else '', route))
    reads = [o for o in h.ops if o.get('probe') == 'F1' and o.get('route') == route]
    notes['complete'] = (len(reads) == ph.get('cold_reads', 24) + 1
                         and not any(w.is_alive() for w in workers) and not errors)
    notes['client_errors'] = errors
    findings, checked = verify_slot_reuse(h.ops, notes)
    notes['checked'] = checked
    notes['status'] = 'measured' if checked else 'not-measured'
    if not checked:
        if route == 'W' and not notes.get('funded_pool'):
            notes['reason'] = 'Funded pool not observed in the running image. ' + F1_POOL + ' ' + notes.get('reason', '')
        else:
            notes.setdefault('reason', 'hold, publication and actual cache eviction/reuse not witnessed; '
                             'the hook preserves owner and extent mutexes')
    return notes, [(p, route + ': ' + detail) for p, detail in findings], checked


def slot_reuse(run, ph):
    campaign = Campaign(run, ph)
    h, routes, findings = campaign.history(), {}, []
    required = ['P4-RECLAIM', 'P2-IDENTITY']
    checked = set(required)
    for route in F1_FUNCTIONS:
        notes, fs, measured = f1_route(campaign, h, ph, route)
        routes[route] = notes
        findings.extend(fs)
        checked.intersection_update(measured)
    notes = {'routes': routes}
    if not checked:
        notes['reason'] = '; '.join(r + ': ' + n['reason'] for r, n in routes.items()
                                   if n['status'] == 'not-measured')
    return fault_result(campaign, h, findings, sorted(checked), notes, required)


def f4_mid(i):
    return '<f4-%d@fn.test>' % i


def f4_request(node, h, campaign, command):
    request, response = node.work / 'f4-request', node.work / 'f4-response'
    # Numbered responses prevent a restart or earlier probe satisfying this one.
    serial = sum(o['kind'] == 'HOOK' for o in h.ops) + 1
    op = h.plan('HOOK', {'command': command, 'serial': serial})
    request.write_text('%d %s\n' % (serial, command))
    h.sent(op)
    with Client(node.port, h, campaign.recovery) as c:
        c.command('STAT <f4-hook-probe@fn.test>')
    text = wait_file(response, campaign.recovery,
                     lambda s: s.startswith('%d\n' % serial) and s.endswith('done\n'))
    h.complete(op, b'200 hook complete\r\n')
    op['response'] = text
    return text.splitlines()[1:-1]


def index_saturation(run, ph):
    from tools import rep_measure, msgid_measure
    campaign = Campaign(run, ph)
    node, h = campaign.node(hook='f4-index.lisp'), campaign.history()
    notes, existing, absent, health = {}, {}, [], {}
    try:
        node.env.update(FN_LOAD_F4_REQUEST=str(node.work / 'f4-request'),
                        FN_LOAD_F4_RESPONSE=str(node.work / 'f4-response'))
        campaign.start(node, h)
        health['initial'] = list(map(int, f4_request(node, h, campaign, 'health')[0].split()))
        count, absent_count = ph.get('colliding_ids', 2304), ph.get('absent_ids', 32)
        selected, scanned = [], 0
        batch = ph.get('tag_batch', 4096)
        if not 1 <= batch <= 4096 or count < 1 or absent_count < 1:
            raise ValueError('F4 needs positive ID counts and a tag batch in 1..4096')
        while len(selected) < count + absent_count and scanned < ph.get('candidate_budget', 1048576):
            size = min(batch, ph.get('candidate_budget', 1048576) - scanned)
            rows = f4_request(node, h, campaign, 'tags %d %d' % (scanned, size))
            tags = {f4_mid(int(i)): int(tag) for i, tag in (r.split() for r in rows)}
            if len(tags) != size or set(tags) != {f4_mid(i) for i in range(scanned, scanned + size)}:
                raise RuntimeError('incomplete hook tag batch')
            selected.extend(collision_search(tags, tags.__getitem__, count + absent_count - len(selected),
                                             ph.get('collision_bits', 8)))
            scanned += size
        notes.update(candidates_scanned=scanned, collisions=len(selected), collision_bits=ph.get('collision_bits', 8))
        if len(selected) != count + absent_count:
            raise RuntimeError('collision search exhausted its finite candidate budget')
        absent = selected[count:]
        prefix = 'p' * ph.get('prefix_octets', 128)
        mids = selected[:count] + ['<%s%c-%d@fn.test>' % (prefix, ch, i)
                                  for i, ch in enumerate('ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789')]
        with Client(node.port, h, campaign.deadline) as c:
            for i, mid in enumerate(mids):
                body = rep_measure.article(i, 2048).replace(msgid_measure.msgid(i).encode(), mid.encode())
                args = {'msgid': mid, 'sha256': digest(body)}
                line = c.post_article(body, args)
                if line.startswith(b'240 '):
                    existing[mid] = digest(body)
                    for label, duplicate in (('same', body), ('different', body + b'different octets\r\n')):
                        c.post_article(duplicate, dict(args, sha256=digest(duplicate), duplicate=label))
                elif named_refusal(line.decode('latin-1')):
                    absent.append(mid)
                else:
                    raise RuntimeError('F4 seed reply: ' + repr(line))
        for epoch in ('before', 'after'):
            if epoch == 'after':
                node.stop()
                try:
                    campaign.start(node, h)
                except Exception as exc:  # a store accepted under this budget must reopen under it (ADMISSION-RESERVES-NOT-REOPEN)
                    notes['restart_refused'] = str(exc)[-200:]
                    raise
            health[epoch] = list(map(int, f4_request(node, h, campaign, 'health')[0].split()))
            with Client(node.port, h, campaign.deadline) as c:
                for mid in list(existing) + absent:
                    text = 'STAT ' + mid
                    op = c.begin('STAT', {'command': text, 'msgid': mid}, text.encode() + b'\r\n')
                    op.update(probe='F4', epoch=epoch)
                    c.finish(op)
                    fault_probe(c, mid, 'F4', epoch)
        notes['accepted_collisions'] = sum(mid in existing for mid in selected[:count])
        notes['accepted_fanout'] = sum(mid in existing for mid in mids[count:])
        notes['complete'] = notes['accepted_collisions'] > 0 and notes['accepted_fanout'] > 1
        if not notes['complete']:
            notes['reason'] = 'both colliding IDs and shared-prefix fan-out were not accepted'
    except Exception as exc:
        notes['reason'] = type(exc).__name__ + ': ' + str(exc)
    finally:
        node.stop()
    notes.update(health=health, existing=len(existing), absent=len(absent))
    findings, checked = verify_index_saturation(h.ops, health, existing, absent)
    notes['saturated'] = index_saturated(health)
    if not notes.get('complete'):
        checked = []
    if 'before' in health:
        # The restart arm was reached: a refused restart is a P5 finding whatever else completed.
        checked = list(checked) + ['P5-RECOVERY']
        if notes.get('restart_refused'):
            findings = list(findings) + [('P5-RECOVERY', 'restart after a refusal-free run refused: '
                                          + notes['restart_refused'])]
    if not checked:
        notes.setdefault('reason', 'complete identity probes before and after restart not witnessed')
    return fault_result(campaign, h, findings, checked, notes, ['P2-IDENTITY', 'P5-RECOVERY'])
