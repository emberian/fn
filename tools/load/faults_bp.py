"""F8: two private BP owners, process death and external TCPCL faults.

Run on the build box, never against a deployed store. The DTN developer image
owns BP and fixture encoding; --developer-image supplies NNTP POST/inventory.
SHA256 compares test bytes only. A transport ACK is never an article receipt.
The incarnation experiment is the native test's different-boot fence/restore,
not a claim that an old journal can migrate to a new boot automatically.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import socket
import tempfile
import time
import traceback
from types import SimpleNamespace

from .faults import (Campaign, Client, History, digest, inventory, merge_reports,
                     report, verify)

PROPERTIES = ['P1-DURABLE', 'P2-IDENTITY', 'P5-RECOVERY']
FAULTS = {'drop-receipt', 'duplicate', 'death-A', 'death-B',
          'different-boot', 'stale-ack'}
CUTS = {
    'kind7': ('FN_BP_NODE_TEST_PAUSE_AFTER_KIND_SEVEN', b'BP NODE KIND7 DURABLE'),
    'decision': ('FN_BP_APP_TEST_PAUSE_AFTER_DECISION', b'BP APP DECISION DURABLE'),
}
ROOT = Path(__file__).resolve().parents[2]
# Client transaction identity, not a boot/incarnation counter. The automatic
# receipt constructor fn-bprl-receipt-auto-record always uses generation 0
# (books/bp-workflow-constructors.lisp). fn-bp-prepare-enqueue forbids reuse of
# the PAIR (txid, generation), including across restart. Keep this fixture's
# explicit enqueues in generation 1; never guess ACL2's next receipt txid.
ENQUEUE_GENERATION = 1
ENQUEUE_PREFLIGHT_REFUSAL = b'ACL2 rejected application journal enqueue before publication'


def generate(seed):
    """Stable recipe IDs survive ddmin; every full seed exercises every fault.

    Shuffle the three fault-bearing articles, placing the boot change and ACK
    replay between them. A final productive exchange witnesses recovery.
    """
    rng = random.Random(seed)
    modes = ['drop', 'kind7', 'decision']
    rng.shuffle(modes)
    recipe = []
    def add(action, **args):
        recipe.append({'step': len(recipe), 'action': action, **args})
    for i, mode in enumerate(modes):
        add('post', i=i, octets=rng.choice([512, 1024, 2048]))
        add('transfer', i=i, mode=mode)
        add('duplicate', i=i)
        if i == 0:
            add('restart', node='A')
            add('boot', node='B')
            add('stale', i=i)
    add('post', i=3, octets=512)
    add('transfer', i=3, mode='clean')
    return recipe


def check(history, observations):
    """Complete inventories plus physical article counts, not a set-only oracle.

    Crossposts may appear in several groups; counts are the image's replayed
    Store article count, and duplicates are repeated IDs within ONE group.
    Missing observations are findings and cannot make a passing zero bar.
    """
    findings = []
    for name in ('A', 'B'):
        obs = observations.get(name)
        if not complete_observation(obs):
            findings.append(('P5-RECOVERY', name + ': complete inventory missing'))
            continue
        articles = obs['articles']
        findings.extend((prop, name + ': ' + detail) for prop, detail in verify(history, articles))
        if obs['article_count'] != len(articles) or obs.get('duplicates'):
            findings.append(('P2-IDENTITY', name + ': duplicate or unenumerated article'))
    if all(complete_observation(observations.get(n)) for n in ('A', 'B')):
        if observations['A']['articles'] != observations['B']['articles']:
            findings.append(('P2-IDENTITY', 'divergence is nonzero'))
    return findings


def complete_observation(obs):
    return (isinstance(obs, dict) and obs.get('complete') is True
            and isinstance(obs.get('articles'), dict)
            and isinstance(obs.get('article_count'), int))


class TransferRefused(Exception):
    """An observed XFER_REFUSE for this session's transfer, not a lost ACK."""
    def __init__(self, frame):
        self.frame = frame
        super().__init__('XFER_REFUSE ' + frame.hex())


class WirePeer:
    """Small synchronous raw TCPCL peer, like NativeBpNodeTests.RawTcpclPeer.

    Retain exact XFER_ACK frames for replay on a later connection. All reads
    share an absolute deadline; byte lengths are fixture observations only.
    """
    def __init__(self, port, timeout, node_id=b'dtn://sender/', *, recorder=None, node=None):
        self.end = time.monotonic() + timeout
        self.recorder, self.node = recorder, node
        self.cid = None
        self.closed = False
        self.keepalive = False
        self.sock = socket.create_connection(('127.0.0.1', port), timeout)
        try:
            if recorder is not None:
                idx = len(recorder.steps)
                self.cid = recorder.conn()
                self.annotate(idx, protocol='tcpcl', node=node)
            self.send(b'dtn!\x04\x00')
            if self.exact(6) != b'dtn!\x04\x00':
                raise ValueError('unexpected TCPCL contact header')
            peer = node_id
            self.send(b'\x07\x00\x01' + (65536).to_bytes(8, 'big')
                             + (1048576).to_bytes(8, 'big') + len(peer).to_bytes(2, 'big')
                             + peer + b'\x00\x00\x00\x00')
            self.keepalive = True
            init = self.frame()
            if init[0] != 7:
                raise ValueError('missing SESS_INIT')
            # The peer's receive limits, not the limits we just advertised.
            # bp-node currently advertises a 1024-byte segment MRU. Sending a
            # whole 2 KiB bundle as one segment causes MSG_REJECT 060201.
            self.segment_mru = int.from_bytes(init[3:11], 'big')
            self.transfer_mru = int.from_bytes(init[11:19], 'big')
            if not self.segment_mru or not self.transfer_mru:
                raise ValueError('peer advertises a zero MRU')
        except BaseException:
            self.abort()
            raise

    def annotate(self, idx, **fields):
        if self.recorder is not None:
            with self.recorder.lock:
                self.recorder.steps[idx].update(fields)

    def send(self, data):
        idx = None
        if self.recorder is not None:
            idx = self.recorder.send(self.cid, data)
        self.sock.sendall(data)
        return idx

    def exact(self, n):
        data = bytearray()
        idx = None
        if self.recorder is not None:
            # Explicit binary-read extension; never label TCPCL as an NNTP
            # line. The shared recorder still owns wire order and completion.
            idx = self.recorder.read(self.cid, 'octets')
            self.annotate(idx, count=n, protocol='tcpcl', node=self.node)
        while len(data) < n:
            left = self.end - time.monotonic()
            if left <= 0:
                raise TimeoutError('TCPCL deadline')
            self.sock.settimeout(min(left, 0.5))
            try:
                chunk = self.sock.recv(n - len(data))
            except socket.timeout:
                if self.keepalive:
                    self.send(b'\x04')  # RawTcpclPeer's one-second keepalive.
                continue
            if not chunk:
                raise EOFError('incomplete TCPCL frame')
            data.extend(chunk)
        if self.recorder is not None:
            self.annotate(idx, received_hex=bytes(data).hex())
            self.recorder.done(self.cid)
        return bytes(data)

    def frame(self):
        kind = self.exact(1)
        if kind == b'\x07':
            body = self.exact(18)
            size = self.exact(2)
            body += size + self.exact(int.from_bytes(size, 'big'))
            size = self.exact(4)
            return kind + body + size + self.exact(int.from_bytes(size, 'big'))
        sizes = {2: 17, 3: 9, 4: 0, 5: 2, 6: 2}
        if kind[0] not in sizes:
            raise ValueError('unexpected TCPCL frame type %d' % kind[0])
        return kind + self.exact(sizes[kind[0]])

    def transfer(self, bundle):
        if not bundle or len(bundle) > self.transfer_mru:
            raise ValueError('bundle outside peer transfer MRU')
        # Match RawTcpclPeer.segment exactly, with START/extensions only on
        # the first segment and END only on the last (RFC 9174 section 5.2).
        for offset in range(0, len(bundle), self.segment_mru):
            data = bundle[offset:offset + self.segment_mru]
            end = offset + len(data)
            flags = (2 if offset == 0 else 0) | (1 if end == len(bundle) else 0)
            self.send(b'\x01' + bytes([flags]) + (0).to_bytes(8, 'big')
                      + (b'\x00' * 4 if offset == 0 else b'')
                      + len(data).to_bytes(8, 'big') + data)
            while True:
                frame = self.frame()
                if frame[0] != 4:
                    break
            if frame[0] == 3 and int.from_bytes(frame[2:10], 'big') == 0:
                raise TransferRefused(frame)
            if (frame[0] != 2 or frame[1] != flags
                    or int.from_bytes(frame[2:10], 'big') != 0
                    or int.from_bytes(frame[10:18], 'big') != end):
                raise ValueError('transfer did not get exact XFER_ACK at %d/%d: %s'
                                 % (end, len(bundle), frame.hex()))
        return frame

    def replay(self, ack):
        self.send(ack)
        while True:
            frame = self.frame()
            if frame[0] == 4:
                continue
            if frame[0] not in (5, 6):
                raise ValueError('stale ACK not rejected: ' + frame.hex())
            return frame

    def close(self, graceful=False):
        try:
            self.send(b'\x05\x00\x00')
            if graceful:
                while True:
                    frame = self.frame()
                    if frame[0] == 4:
                        continue
                    if frame[0] != 5:
                        raise ValueError('SESS_TERM reply missing: ' + frame.hex())
                    if not frame[1] & 1:
                        self.send(b'\x05\x01' + frame[2:3])
                    break
        except OSError:
            if graceful:
                raise
        finally:
            self.abort()

    def abort(self):
        if not self.closed:
            self.closed = True
            if self.recorder is not None and self.cid is not None:
                self.recorder.close(self.cid)
            self.sock.close()


class BpCampaign(Campaign):
    """Compose two ordinary Campaign nodes and reuse its start/control path."""
    def __init__(self, run, ph, image, developer_image):
        super().__init__(run, ph)
        self.image = Path(image).resolve()
        self.developer_image = Path(developer_image).resolve()

    def trial(self, recipe):
        h, findings, observations, witnessed = self.history(), [], {}, set()
        # The owners and relay run concurrently, including native traffic
        # invisible to the raw peer. Do not claim a sequential NNTP replay.
        h.recorder.interleaved = True
        notes = {'steps': [{'recipe': dict(step), 'outcome': 'not-attempted'} for step in recipe],
                 'failing_step': None, 'exception': None, 'cleanup_exceptions': [],
                 'inventory_exceptions': [],
                 'nodes': {}, 'commands': [], 'refusals': [], 'recipe': list(recipe)}
        h.trial_notes = notes
        pair = None
        current = {'phase': 'setup'}
        step_log = None

        def record_refusal(refused, context):
            notes['refusals'].append(dict(refused, **context))
            findings.append(('P5-RECOVERY', refused.get('operation', 'workflow-enqueue')
                             + ' refused by ' + refused['decision'] + ': '
                             + refused['reply_line'].strip()))

        try:
            pair = Pair(self, h)
            for step, step_log in zip(recipe, notes['steps']):
                current = {'phase': 'recipe', **step}
                # The original recipe, not the observed reply, is replayed.
                op = h.plan('F8', step)
                op['replayable'] = True
                op['step'] = h.recorder.control(['F8', json.dumps(step, sort_keys=True)])
                h.sent(op)
                step_log.update(op_id=op['op_id'], send_time=op['send_time'], outcome=op['outcome'])
                refused = pair.execute(step, witnessed)
                if refused is not None:
                    # Explicit refusals complete the attempt without making
                    # its intended effect or fault witness true.
                    record_refusal(refused, {'recipe': dict(step)})
                    h.complete(op, refused['reply_line'].encode('utf-8'))
                    op['rc'] = refused['rc']
                    step_log['refusal'] = refused
                else:
                    h.complete(op, b'F8 step observed\r\n')
                step_log.update(outcome=op['outcome'], complete_time=op['complete_time'])
            step_log = None
            current = {'phase': 'converge'}
            for refused in pair.converge(witnessed) or []:
                record_refusal(refused, {'phase': 'converge'})
        except Exception as exc:
            notes['failing_step'] = current
            notes['exception'] = exception_details(exc)
            if step_log is not None:
                step_log['exception'] = notes['exception']
            findings.append(('P5-RECOVERY', 'required observation failed: ' + type(exc).__name__ + ': ' + str(exc)))
        finally:
            if pair is not None:
                # Inventories remain required evidence even after an earlier
                # refusal or exception. Keep the original failure diagnostics.
                try:
                    observations = pair.observe()
                except Exception as exc:
                    details = exception_details(exc)
                    notes['inventory_exceptions'].append(details)
                    if notes['failing_step'] is None:
                        notes.update(failing_step={'phase': 'inventory'}, exception=details)
                    findings.append(('P5-RECOVERY', 'inventory failed: ' + str(exc)))
                try:
                    pair.close()
                except Exception as exc:
                    notes['cleanup_exceptions'].append(exception_details(exc))
                    findings.append(('P5-RECOVERY', 'cleanup failed: ' + str(exc)))
        findings.extend(check(h.ops, observations))
        notes.update(observations=observations, witnessed=sorted(witnessed))
        return h, findings, notes

    def snapshot(self, history):
        # Campaign.meta is mutable across shrink trials; use this history's
        # own node paths and recipe, not the most recently allocated pair.
        nodes = history.trial_notes['nodes']
        first = nodes.get('A', {})
        return dict(history.recorder.snapshot(history.ops), cell='F8',
                    store={'init_flags': first.get('init_flags', []),
                           'groups': first.get('groups', []), 'fixture': None},
                    sbcl_user_args=first.get('sbcl_user_args', ''),
                    extensions=['F8', 'multi-node', 'tcpcl-octets'],
                    trial=history.trial_notes)


def exception_details(exc):
    return {'type': type(exc).__name__, 'message': str(exc),
            'traceback_tail': ''.join(traceback.format_exception(type(exc), exc, exc.__traceback__)).splitlines()[-40:]}


class Pair:
    def __init__(self, campaign, history):
        from tests.native_harness import environment
        from tests.test_bp_contact_relay_native import ByteRelay
        self.c, self.h = campaign, history
        self.notes = history.trial_notes
        self.nodes, self.processes, self.active = {}, [], {}
        self.bundles, self.acks, self.posted, self.requests = {}, {}, {}, {}
        self.offered = set()
        self.sequence = 0
        self.relay = ByteRelay()
        self.cut_events = []
        try:
            for name in ('A', 'B'):
                # Campaign.node allocates a new private store on EVERY replay.
                op = self.h.plan('INIT', {'node': name})
                self.h.sent(op)
                node = self.c.node()
                self.nodes[name] = node
                self.notes['nodes'][name] = {'work': str(node.work), 'stderr': [], 'stdout': [],
                                             'init_flags': list(node.flags), 'groups': list(node.groups),
                                             'sbcl_user_args': node.env['SBCL_USER_ARGS']}
                node.env = environment({'SBCL_USER_ARGS': node.env['SBCL_USER_ARGS']})
                self.h.complete(op, b'private store initialized\r\n')
                self.must_control(node, 'policy', 'set', 'path-identity', self.path(name))
            self.invoke('app-journal', 'workflow-init', self.nodes['A'].store,
                        self.workflow('A'), self.eid('A'), self.eid('B'),
                        'native-policy', self.eid('B'), 3600000, 'origin-native', 'wire-auth')
        except BaseException:
            self.close()
            raise

    @staticmethod
    def eid(name):
        return 'dtn://sender/' if name == 'A' else 'dtn://receiver/'

    @staticmethod
    def path(name):
        return 'sender.bp.gate.invalid' if name == 'A' else 'receiver.bp.gate.invalid'

    def file(self, name, suffix):
        return self.nodes[name].work / suffix

    def journal(self, name):
        return self.file(name, 'fnbs')

    def workflow(self, name):
        return self.file(name, 'fnwf')

    def invoke(self, *words, expected=0):
        from tests.native_harness import environment, run
        op = self.h.plan('CONTROL', {'argv': [str(x) for x in words]})
        op['step'] = self.h.recorder.control(['--fn', *[str(x) for x in words]])
        self.h.sent(op)
        p = run([self.c.image, '--fn', *words], cwd=ROOT, env=environment(), timeout=self.c.recovery)
        self.h.complete(op, p.stdout + p.stderr + b'\r\n')
        op['rc'] = p.returncode
        stem = self.c.run.node.work / ('command-%d-%d' % (self.c.serial, op['op_id']))
        stdout, stderr = str(stem) + '.stdout', str(stem) + '.stderr'
        Path(stdout).write_bytes(p.stdout)
        Path(stderr).write_bytes(p.stderr)
        self.notes['commands'].append({'op_id': op['op_id'], 'stdout': stdout, 'stderr': stderr, 'rc': p.returncode})
        if expected is not None and p.returncode != expected:
            raise RuntimeError('command exit %s: %s' % (p.returncode, (p.stdout + p.stderr).decode(errors='replace')))
        return p

    def must_control(self, node, *words):
        rc, output = self.c.control(node, self.h, *[str(w) for w in words])
        if rc:
            raise RuntimeError('operator exit %s: %s' % (rc, output))

    def start_reader(self, name):
        node = self.nodes[name]
        op = self.h.plan('START-NNTP', {'node': name})
        self.h.sent(op)
        self.notes['nodes'][name]['stderr'].append(str(node.work / ('owner.%d.err' % (node.err_n + 1))))
        op['step'] = len(self.h.recorder.steps)
        self.c.start(node, self.h)
        with self.h.recorder.lock:
            self.h.recorder.steps[op['step']].update(node=name, protocol='nntp')
        self.h.complete(op, b'LISTENING\r\n')

    def stop_reader(self, name):
        node = self.nodes[name]
        if node.proc is not None:
            op = self.h.plan('STOP-NNTP', {'node': name, 'pid': node.pid})
            op['step'] = self.h.recorder.control(['F8', 'stop-nntp', name])
            self.h.sent(op)
            rc = node.stop(grace=5)
            self.h.complete(op, ('exit %s\r\n' % rc).encode())
            op['rc'] = rc

    def stop_bp(self, name, kill=False):
        pair = self.active.pop(name, None)
        if pair:
            process, _ = pair
            op = self.h.plan('KILL' if kill else 'STOP-BP', {'node': name, 'pid': process.pid})
            op['step'] = self.h.recorder.control(['F8', 'kill-bp' if kill else 'stop-bp', name])
            self.h.sent(op)
            if kill:
                if process.poll() is not None:
                    raise RuntimeError('intended death found an already exited process')
                process.kill()  # Only our recorded child PID, never a name match.
                process.wait(timeout=15)
            rc = process.stop(grace=5)
            self.h.complete(op, ('exit %s\r\n' % rc).encode())
            op['rc'] = rc

    def bp_args(self, name, verb, port=None, once=False):
        other = 'B' if name == 'A' else 'A'
        args = ['bp-node', verb]
        if verb == 'serve':
            args.append(str(port))
        args += [str(self.journal(name)), str(self.nodes[name].store), str(self.file(name, 'fnrj')),
                 str(self.workflow(name)), self.eid(name), self.eid(other), self.eid(name),
                 'native-policy', self.eid(name), '127.0.0.1', str(self.relay.port),
                 '1' if once else '0', '3600000', '2', '32', '1048576', '0', '0']
        if verb == 'dispatch':
            args.append('0')
        return args

    def start_bp(self, name, *, mode='clean', once=False):
        from tests.native_harness import environment, free_port, start
        port, other = free_port(), 'B' if name == 'A' else 'A'
        self.must_control(self.nodes[name], 'bp-boundary', 'add', other + '-boundary',
                          self.path(other), self.eid(other), port, 'fn.test', '32768', '16',
                          'contact', self.relay.port)
        self.must_control(self.nodes[name], 'bp-route', 'add', self.eid(other) + '*', other + '-boundary')
        args = self.bp_args(name, 'serve', port, once)
        extra = {CUTS[mode][0]: '1'} if mode in CUTS else {}
        op = self.h.plan('START-BP', {'node': name, 'argv': args, 'env': extra})
        op['step'] = self.h.recorder.control(['--fn', *args])
        self.h.sent(op)
        process = start([self.c.image, '--fn', *args], cwd=ROOT, env=environment(extra), limit=None)
        self.processes.append((name, process, op))
        self.notes['nodes'][name]['stderr'].append(str(self.file(name, 'bp-%d.stderr' % process.pid)))
        self.notes['nodes'][name]['stdout'].append(str(self.file(name, 'bp-%d.stdout' % process.pid)))
        self.active[name] = process, port
        self.file(name, 'bp-%d.pid' % process.pid).write_text(str(process.pid) + '\n')
        line = process.announcement(b'BP NODE LISTENING ', timeout=self.c.recovery)
        self.h.complete(op, line.rstrip(b'\r\n') + b'\r\n')
        return process, int(line.rsplit(b' ', 1)[1])

    def dispatch(self, name='B', expected=0):
        return self.invoke(*self.bp_args(name, 'dispatch', once=True), expected=expected)

    def post(self, step):
        from tools import msgid_measure, rep_measure
        i, octets = step['i'], step['octets']
        self.stop_bp('A')
        self.start_reader('A')
        op = self.h.plan('POST', {'i': i, 'octets': octets, 'msgid': msgid_measure.msgid(i),
                                  'sha256': digest(rep_measure.article(i, octets))})
        try:
            with Client(self.nodes['A'].port, self.h, self.c.deadline) as client:
                line = client.post(i, octets, op)
            if not line.startswith(b'240 '):
                raise RuntimeError('productive POST refused: ' + repr(line))
        finally:
            self.stop_reader('A')
        article = self.invoke('store', self.nodes['A'].store, 'inspect', msgid_measure.msgid(i)).stdout
        self.posted[i] = article
        refused = self.enqueue(i, msgid_measure.msgid(i))
        if refused is None:
            self.invoke('bp-obligation', 'undertake', self.nodes['A'].store, self.workflow('A'), 'f8-work-%d' % i, 3)
            self.requests[i] = self.author_request(i, article)
        # Even a known enqueue refusal leaves the earlier works available to
        # the remaining recipe. No request/undertaking is invented for it.
        _, port = self.start_bp('A')
        self.relay.route(port)
        return refused

    def enqueue(self, i, msgid):
        from tests.native_harness import EXIT
        self.sequence += 1
        work = 'f8-work-%d' % i
        p = self.invoke('app-journal', 'workflow-enqueue', self.nodes['A'].store, self.workflow('A'),
                        self.sequence, ENQUEUE_GENERATION, work, msgid, 'f8-forward-%d' % i,
                        self.eid('B'), 'native-policy', 'terms-native', expected=None)
        if p.returncode == EXIT.OK:
            return None
        reply = p.stdout + p.stderr
        if p.returncode == EXIT.REFUSED and ENQUEUE_PREFLIGHT_REFUSAL in reply:
            # fnn-app-publish refuses here BEFORE fnn-app-authorized-publish:
            # no enqueue record was published. Other errors/uncertainty must
            # still stop the trial; they could leave a pending durable intent.
            return {'rc': p.returncode, 'reply_line': reply.decode('utf-8', 'replace').rstrip() + '\r\n',
                    'decision': 'fn-workflow-preflight-record',
                    'txid': self.sequence, 'generation': ENQUEUE_GENERATION, 'article': i}
        raise RuntimeError('workflow-enqueue exit %s: %s' % (p.returncode, reply.decode('utf-8', 'replace')))

    def author_request(self, i, article):
        from tests.native_harness import Acl2Session
        op = self.h.plan('FIXTURE', {'i': i, 'article_sha256': hashlib.sha256(article).hexdigest()})
        self.h.sent(op)
        with Acl2Session(self.c.image, timeout=self.c.recovery) as bridge:
            fields = [('f8-work-%d' % i).encode(), bridge.subject(b'', article),
                      self.eid('A').encode(), self.eid('B').encode(), b'native-policy',
                      b'origin-native', b'wire-auth', b'terms-native']
            adu = bridge.bp_request(fields, article)
        self.h.complete(op, b'ACL2 fixture encoded\r\n')
        self.file('A', 'request-%d.adu' % i).write_bytes(adu)
        return adu

    def capture_bundle(self, i):
        """Recover the actual received bundle with the image's frame codec.

        Same kind-5 decoder as NativeBpNodeTests.acl2_lifecycle_payloads;
        Python neither authors a new bundle identity nor decodes Store bytes.
        """
        from tests.native_harness import Acl2Session, acl2_octets
        op = self.h.plan('CAPTURE-BUNDLE', {'i': i})
        self.h.sent(op)
        found = []
        with Acl2Session(self.c.image, timeout=self.c.recovery) as bridge:
            for path in sorted((self.journal('B') / 'lifecycle').glob('*.fnb')):
                bundle = acl2_octets(bridge.call(
                    "(let* ((record (fn-bpnf-stored-record-unframe '"
                    + bridge.literal(path.read_bytes()) + ')) '
                    + '(bundle (and record (fn-bpnf-held-bundle (fn-bpn-nth 3 record))))) '
                    + "(and record (equal (fn-bpb-payload bundle) '"
                    + bridge.literal(self.requests[i]) + ') (fn-bpb-encode bundle)))'))
                if bundle:
                    found.append(bundle)
        if len(found) != 1:
            raise RuntimeError('expected exactly one held request bundle, got %d' % len(found))
        self.bundles[i] = found[0]
        op['bundle_sha256'] = hashlib.sha256(found[0]).hexdigest()
        self.h.complete(op, b'one actual held bundle captured\r\n')
        self.file('A', 'bundle-%d.bp' % i).write_bytes(found[0])

    def transfer(self, i, mode, witnessed):
        from tests.native_harness import EXIT
        if i not in self.requests or (mode == 'duplicate' and i not in self.bundles):
            return  # Deleted producer in a shrink candidate: explicit dependency no-op.
        sender, sender_port = self.active['A']
        offset = len(self.cut_events)
        self.relay.route(sender_port, cut_after=80 if mode == 'drop' else None,
                         observer=lambda **event: self.cut_events.append(event))
        receiver, port = self.start_bp('B', mode=mode, once=True)
        op = self.h.plan('BP-EXCHANGE', {'i': i, 'mode': mode})
        op['step'] = self.h.recorder.control(['F8', 'exchange', str(i), mode])
        self.h.sent(op)
        refused = None
        if mode == 'duplicate':
            op['bundle_sha256'] = hashlib.sha256(self.bundles[i]).hexdigest()
            peer = WirePeer(port, self.c.recovery, recorder=self.h.recorder, node='B')
            try:
                ack = peer.transfer(self.bundles[i])
                self.acks[i] = ack
                op['ack_hex'] = ack.hex()
                peer.close(graceful=True)
            except TransferRefused as exc:
                peer.close()
                refused = {'rc': EXIT.REFUSED, 'reply_line': str(exc) + '\r\n',
                           'wire_hex': exc.frame.hex(), 'reason': exc.frame[1]}
            except BaseException:
                peer.abort()
                raise
        else:
            # A's listening node holds FNBS; the request uses a separate
            # outbound journal of the same identity, as the native receipt
            # test does. Reuse it across ALL requests and retries: a fresh
            # journal resets fn-bpn-sequence-recover to 0, colliding with the
            # earlier (source, creation-time=0, sequence=0) bundle identity.
            # fnn-command-bp-service-run owns allocation/reuse, not Python.
            work = 'f8-carrier-%d' % i
            result = self.invoke('bp-service', 'run', '127.0.0.1', port,
                        self.file('A', 'request-%d.adu' % i), self.file('A', 'request-fnbs'),
                        self.eid('A'), self.eid('B'), work, work + '-attempt', 0,
                        3600000, 2, 32, 1048576, 0, 0, expected=None)
            reply = result.stdout + result.stderr
            if result.returncode != EXIT.OK:
                reasons = re.findall(rb'^TCPCL [^\r\n]+ refused outbound xfer=([0-9]+) reason=([0-9]+)\r?$',
                                     reply, re.MULTILINE)
                if (result.returncode != EXIT.REFUSED or not reasons
                        or b'BP forwarding retained reason=refused' not in reply):
                    raise RuntimeError('bp-service run exit %s: %s'
                                       % (result.returncode, reply.decode(errors='replace')))
                refused = {'rc': result.returncode,
                           'reply_line': reply.decode(errors='replace').rstrip() + '\r\n',
                           'wire_refusals': [{'xfer': int(x), 'reason': int(r)} for x, r in reasons]}
        if refused is not None:
            refused.update(operation='BP-EXCHANGE', article=i, mode=mode,
                           decision='fn-tcl-delivery-refuse-reason (books/tcpcl-delivery.lisp:52)')
            self.h.complete(op, refused['reply_line'].encode())
            op.update(rc=refused['rc'], refusal=refused)
            # A refused reception has no new custody. Do not await kind7,
            # receipt delivery or a lost-receipt cut that it never reached.
            self.stop_bp('B')
            out, err = receiver.communicate(timeout=self.c.recovery)
            refused['receiver_reply'] = (out + err).decode(errors='replace')
            op['owner_exit'] = receiver.returncode
            self.relay.route(sender_port)
            return refused
        if mode in CUTS:
            marker = receiver.output_until(CUTS[mode][1], timeout=self.c.recovery)
            op['cut_marker'] = marker.decode(errors='replace')
            self.stop_bp('B', kill=True)
            witnessed.add('death-B')
        else:
            out, err = receiver.communicate(timeout=self.c.recovery)
            op['owner_exit'] = receiver.returncode
            if receiver.returncode:
                raise RuntimeError('receiver exit: ' + (out + err).decode(errors='replace'))
            self.stop_bp('B')
            if mode == 'drop':
                if not self.cut_events[offset:] or b'BP forwarding retained reason=uncertain' not in out:
                    raise RuntimeError('lost receipt cut not observed')
                op['receipt_cut'] = self.cut_events[offset:]
                witnessed.add('drop-receipt')
        self.relay.route(sender_port)
        self.dispatch()
        # A consumed receipt is an application observation, not XFER_ACK.
        if mode != 'duplicate':
            sender.output_until(b'BP node delivery receipt-accepted', timeout=self.c.recovery)
            self.capture_bundle(i)
            self.offered.add(i)
        else:
            witnessed.add('duplicate')
        self.h.complete(op, b'BP exchange observed\r\n')

    def other_boot(self, witnessed):
        from tests.native_harness import Acl2Session, EXIT, acl2_octets
        domain = self.journal('B') / 'clock-domain.fnb'
        if not domain.exists():
            return  # No transfer remains in this shrink candidate.
        boot = Path('/proc/sys/kernel/random/boot_id').read_text().strip()
        other = boot[:-1] + ('0' if boot[-1] != '0' else '1')
        saved = domain.read_bytes()
        lifecycle = self.journal('B') / 'lifecycle'
        before = {p.name: p.read_bytes() for p in lifecycle.iterdir()}
        with Acl2Session(self.c.image, timeout=self.c.recovery) as bridge:
            frame = acl2_octets(bridge.call("(fn-bpcd-frame '" + bridge.literal(other.encode()) + ')'))
        op = self.h.plan('BOOT-DOMAIN', {'node': 'B',
                                        'original_sha256': hashlib.sha256(saved).hexdigest(),
                                        'other_sha256': hashlib.sha256(frame).hexdigest()})
        self.h.sent(op)
        try:
            domain.write_bytes(frame)
            fenced = self.dispatch(expected=EXIT.UNCERTAIN)
            if b'restart fenced: clock domain different-boot' not in fenced.stderr:
                raise RuntimeError('different-boot fence missing')
            if before != {p.name: p.read_bytes() for p in lifecycle.iterdir()}:
                raise RuntimeError('different-boot fence changed held lifecycle')
        finally:
            domain.write_bytes(saved)
        # fn-bpnf-clock-domain-plan returns :same after restoration, exactly
        # as test_restart_in_another_boot_fences_and_keeps_rows requires.
        recovered = self.dispatch()
        if b'BP FNBS recovered held=' not in recovered.stdout:
            raise RuntimeError('original boot-domain recovery observation missing')
        self.h.complete(op, b'different-boot fenced; unchanged lifecycle; original domain recovered\r\n')
        witnessed.add('different-boot')

    def execute(self, step, witnessed):
        action = step['action']
        if action == 'post':
            return self.post(step)
        elif action in ('transfer', 'duplicate'):
            return self.transfer(step['i'], step.get('mode', 'duplicate'), witnessed)
        elif action == 'restart' and 'A' in self.active:
            # Named external cut: after a completed article/receipt exchange.
            self.stop_bp('A', kill=True)
            _, port = self.start_bp('A')
            self.relay.route(port)
            witnessed.add('death-A')
        elif action == 'boot':
            self.other_boot(witnessed)
        elif action == 'stale' and step['i'] in self.acks:
            # Replay B's ACK to its original logical recipient A, now on a
            # fresh connection after A's process restart. There is no pending
            # transfer on this connection; the stale transfer id must not bind.
            sender, port = self.active['A']
            op = self.h.plan('TCPCL-STALE-ACK', {'ack_hex': self.acks[step['i']].hex(), 'node': 'A'})
            self.h.sent(op)
            peer = WirePeer(port, self.c.recovery, node_id=self.eid('B').encode(),
                            recorder=self.h.recorder, node='A')
            try:
                reply = peer.replay(self.acks[step['i']])
                self.h.complete(op, ('TCPCL rejection ' + reply.hex() + '\r\n').encode())
            finally:
                peer.close()
            if sender.poll() is not None:
                raise RuntimeError('stale ACK stopped the shared sender owner')
            witnessed.add('stale-ack')

    def converge(self, witnessed):
        # Shrinking must not manufacture loss merely by deleting an explicit
        # transfer step. POST creates an obligation; the fixed final drain
        # offers every remaining request that has not had a completed exchange.
        refusals = []
        for i in sorted(self.requests.keys() - self.offered):
            refused = self.transfer(i, 'clean', witnessed)
            if refused is not None:
                refusals.append(refused)
        return refusals

    def observe(self):
        observations = {}
        for name in ('A', 'B'):
            try:
                observations[name] = self.observe_node(name)
            except Exception as exc:
                # One unavailable node must not discard the other's inventory.
                self.notes['inventory_exceptions'].append(dict(exception_details(exc), node=name))
        return observations

    def observe_node(self, name):
        self.stop_bp(name)
        node = self.nodes[name]
        self.start_reader(name)
        try:
            articles = inventory(node.port, self.h, self.c.deadline)
            duplicates = []
            with Client(node.port, self.h, self.c.deadline) as client:
                status, numbers = client.command('LISTGROUP fn.test')
                if not status.startswith(b'211 '):
                    raise RuntimeError('duplicate observation refused')
                seen = set()
                for number in numbers.splitlines():
                    status, article = client.command('ARTICLE ' + number.decode())
                    if not status.startswith(b'220 '):
                        raise RuntimeError('duplicate observation ARTICLE refused')
                    mid = next(row.split(b':', 1)[1].strip().decode() for row in article.split(b'\r\n\r\n')[0].splitlines()
                               if row.lower().startswith(b'message-id:'))
                    if mid in seen:
                        duplicates.append(mid)
                    seen.add(mid)
        finally:
            self.stop_reader(name)
        status = self.invoke('store', node.store, 'status', '--replay').stdout
        counts = re.findall(rb'^transactions=[0-9]+ articles=([0-9]+) ', status, re.MULTILINE)
        if len(counts) != 1:
            raise RuntimeError('replayed article count missing')
        return {'articles': articles, 'article_count': int(counts[0]),
                'duplicates': duplicates, 'complete': True}

    def close(self):
        errors = []
        for name in list(self.active):
            try:
                self.stop_bp(name)
            except Exception as exc:
                errors.append('%s BP stop: %s' % (name, exc))
        for name in self.nodes:
            try:
                self.stop_reader(name)
            except Exception as exc:
                errors.append('%s reader stop: %s' % (name, exc))
        for name, process, op in self.processes:
            try:
                process.stop(grace=5)
            except Exception as exc:
                errors.append('%s PID %s stop: %s' % (name, process.pid, exc))
            finally:
                op['rc'] = process.returncode
                for stream in ('stdout', 'stderr'):
                    try:
                        self.file(name, 'bp-%d.%s' % (process.pid, stream)).write_bytes(getattr(process, stream).since(0))
                    except Exception as exc:
                        errors.append('%s PID %s %s: %s' % (name, process.pid, stream, exc))
        self.relay.close()
        if errors:
            raise RuntimeError('; '.join(errors))


def run_campaign(campaign, seed=1, histories=1, budget=16):
    reports, trials = [], []
    for index in range(histories):
        recipe = generate(seed + index)
        h, findings, notes = campaign.trial(recipe)
        notes['trace'] = campaign.emit(campaign.snapshot(h), 'history-%d' % index)
        missing = FAULTS - set(notes['witnessed'])
        if missing:
            findings.append(('P5-RECOVERY', 'missing fault witnesses: ' + ', '.join(sorted(missing))))
        def replay(candidate, prop, detail):
            _, fs, _ = campaign.trial([op['args'] for op in candidate])
            return (prop, detail) in fs
        complete = all(complete_observation(notes['observations'].get(n)) for n in ('A', 'B'))
        notes['divergence'] = (len(set(notes['observations']['A']['articles'].items())
                                  ^ set(notes['observations']['B']['articles'].items())) if complete else None)
        reports.append(report(h, findings, PROPERTIES if complete and not missing else [], replay, budget, campaign))
        trials.append(dict(notes, seed=seed + index))
    out = merge_reports(reports)
    out['traces'] = campaign.traces
    return {'faults': out, 'trials': trials,
            'status': 'not-measured' if not out['checked'] else ('failed' if out['violations'] else 'ok')}


def bp_disruption(run, ph):
    """Driver entry; F8 registration is supplied separately for lane L."""
    developer = ph.get('developer_image') or os.environ.get('FN_NATIVE_DEVELOPER_HOST')
    if not developer:
        raise ValueError('F8 needs FN_NATIVE_DEVELOPER_HOST (NNTP-capable developer image)')
    return run_standalone(run.node.target.path, developer, run.node.work,
                          ph.get('seed', 1), ph.get('histories', 1), ph.get('shrink_runs', 16), ph)


def run_standalone(image, developer, work, seed, histories, budget, ph=None):
    from .driver import Node, Target
    from tests.native_harness import environment
    if histories < 1 or budget < 0:
        raise ValueError('histories must be positive; shrink budget nonnegative')
    work = Path(work).resolve()
    work.mkdir(parents=True, exist_ok=True)
    # No rmtree, store reuse, or overwriting another campaign's scratch.
    root = Path(tempfile.mkdtemp(prefix='f8-', dir=work))
    env = environment()
    parent = Node(Target('image', developer), root, ['--profile', 'default'], ['fn.test'],
                  env.get('SBCL_USER_ARGS', ''), [], root / 'gc.log', env, 1, 'fixed')
    campaign = BpCampaign(SimpleNamespace(node=parent, cell_id='F8', label=root.name),
                          ph or {'recovery_s': 120}, image, developer)
    result = run_campaign(campaign, seed, histories, budget)
    result['work'] = str(root)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--image', required=True)
    parser.add_argument('--developer-image', required=True)
    parser.add_argument('--work', required=True)
    parser.add_argument('--out', required=True)
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--histories', type=int, default=1)
    parser.add_argument('--shrink-runs', type=int, default=16)
    args = parser.parse_args(argv)
    result = run_standalone(args.image, args.developer_image, args.work, args.seed,
                            args.histories, args.shrink_runs)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + '\n')
    return 0 if result['status'] == 'ok' else 1


if __name__ == '__main__':
    raise SystemExit(main())
