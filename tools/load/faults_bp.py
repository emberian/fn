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


class WirePeer:
    """Small synchronous raw TCPCL peer, like NativeBpNodeTests.RawTcpclPeer.

    Retain exact XFER_ACK frames for replay on a later connection. All reads
    share an absolute deadline; byte lengths are fixture observations only.
    """
    def __init__(self, port, timeout, node_id=b'dtn://sender/'):
        self.end = time.monotonic() + timeout
        self.sock = socket.create_connection(('127.0.0.1', port), timeout)
        try:
            self.sock.sendall(b'dtn!\x04\x00')
            if self.exact(6) != b'dtn!\x04\x00':
                raise ValueError('unexpected TCPCL contact header')
            peer = node_id
            self.sock.sendall(b'\x07\x00\x00' + (65536).to_bytes(8, 'big')
                             + (1048576).to_bytes(8, 'big') + len(peer).to_bytes(2, 'big')
                             + peer + b'\x00\x00\x00\x00')
            if self.frame()[0] != 7:
                raise ValueError('missing SESS_INIT')
        except BaseException:
            self.sock.close()
            raise

    def exact(self, n):
        data = bytearray()
        while len(data) < n:
            left = self.end - time.monotonic()
            if left <= 0:
                raise TimeoutError('TCPCL deadline')
            self.sock.settimeout(left)
            chunk = self.sock.recv(n - len(data))
            if not chunk:
                raise EOFError('incomplete TCPCL frame')
            data.extend(chunk)
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
        self.sock.sendall(b'\x01\x03' + (1).to_bytes(8, 'big') + b'\x00' * 4
                         + len(bundle).to_bytes(8, 'big') + bundle)
        while True:
            frame = self.frame()
            if frame[0] == 4:
                continue
            if (frame[0] != 2 or frame[1] != 3
                    or int.from_bytes(frame[2:10], 'big') != 1
                    or int.from_bytes(frame[10:18], 'big') != len(bundle)):
                raise ValueError('transfer did not get exact final XFER_ACK: ' + frame.hex())
            return frame

    def replay(self, ack):
        self.sock.sendall(ack)
        while True:
            frame = self.frame()
            if frame[0] == 4:
                continue
            if frame[0] not in (5, 6):
                raise ValueError('stale ACK not rejected: ' + frame.hex())
            return frame

    def close(self, graceful=False):
        try:
            self.sock.sendall(b'\x05\x00\x00')
            if graceful:
                while True:
                    frame = self.frame()
                    if frame[0] == 4:
                        continue
                    if frame[0] != 5:
                        raise ValueError('SESS_TERM reply missing: ' + frame.hex())
                    if not frame[1] & 1:
                        self.sock.sendall(b'\x05\x01' + frame[2:3])
                    break
        except OSError:
            if graceful:
                raise
        finally:
            self.sock.close()


class BpCampaign(Campaign):
    """Compose two ordinary Campaign nodes and reuse its start/control path."""
    def __init__(self, run, ph, image, developer_image):
        super().__init__(run, ph)
        self.image = Path(image).resolve()
        self.developer_image = Path(developer_image).resolve()

    def trial(self, recipe):
        h, findings, observations, witnessed = History(), [], {}, set()
        pair = None
        try:
            pair = Pair(self, h)
            for step in recipe:
                # The original recipe, not the observed reply, is replayed.
                op = h.plan('F8', step)
                op['replayable'] = True
                h.sent(op)
                pair.execute(step, witnessed)
                h.complete(op, b'F8 step observed\r\n')
            pair.converge(witnessed)
            observations = pair.observe()
        except Exception as exc:
            findings.append(('P5-RECOVERY', 'required observation failed: ' + type(exc).__name__ + ': ' + str(exc)))
        finally:
            if pair is not None:
                try:
                    pair.close()
                except Exception as exc:
                    findings.append(('P5-RECOVERY', 'cleanup failed: ' + str(exc)))
        findings.extend(check(h.ops, observations))
        return h, findings, {'observations': observations, 'witnessed': sorted(witnessed)}


class Pair:
    def __init__(self, campaign, history):
        from tests.native_harness import environment
        from tests.test_bp_contact_relay_native import ByteRelay
        self.c, self.h = campaign, history
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
        self.h.sent(op)
        p = run([self.c.image, '--fn', *words], cwd=ROOT, env=environment(), timeout=self.c.recovery)
        self.h.complete(op, p.stdout + p.stderr + b'\r\n')
        op['rc'] = p.returncode
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
        self.c.start(node)
        self.h.complete(op, b'LISTENING\r\n')

    def stop_reader(self, name):
        node = self.nodes[name]
        if node.proc is not None:
            op = self.h.plan('STOP-NNTP', {'node': name, 'pid': node.pid})
            self.h.sent(op)
            rc = node.stop(grace=5)
            self.h.complete(op, ('exit %s\r\n' % rc).encode())
            op['rc'] = rc

    def stop_bp(self, name, kill=False):
        pair = self.active.pop(name, None)
        if pair:
            process, _ = pair
            op = self.h.plan('KILL' if kill else 'STOP-BP', {'node': name, 'pid': process.pid})
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
        self.h.sent(op)
        process = start([self.c.image, '--fn', *args], cwd=ROOT, env=environment(extra), limit=None)
        self.processes.append((name, process, op))
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
        self.sequence += 1
        work = 'f8-work-%d' % i
        self.invoke('app-journal', 'workflow-enqueue', self.nodes['A'].store, self.workflow('A'),
                    self.sequence, 0, work, msgid_measure.msgid(i), 'f8-forward-%d' % i,
                    self.eid('B'), 'native-policy', 'terms-native')
        self.invoke('bp-obligation', 'undertake', self.nodes['A'].store, self.workflow('A'), work, 3)
        self.requests[i] = self.author_request(i, article)
        _, port = self.start_bp('A')
        self.relay.route(port)

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
        if i not in self.requests or (mode == 'duplicate' and i not in self.bundles):
            return  # Deleted producer in a shrink candidate: explicit dependency no-op.
        sender, sender_port = self.active['A']
        offset = len(self.cut_events)
        self.relay.route(sender_port, cut_after=80 if mode == 'drop' else None,
                         observer=lambda **event: self.cut_events.append(event))
        receiver, port = self.start_bp('B', mode=mode, once=True)
        op = self.h.plan('BP-EXCHANGE', {'i': i, 'mode': mode})
        self.h.sent(op)
        if mode == 'duplicate':
            op['bundle_sha256'] = hashlib.sha256(self.bundles[i]).hexdigest()
            peer = WirePeer(port, self.c.recovery)
            try:
                ack = peer.transfer(self.bundles[i])
                self.acks[i] = ack
                op['ack_hex'] = ack.hex()
                peer.close(graceful=True)
            except BaseException:
                peer.sock.close()
                raise
        else:
            # A's listening node holds FNBS; the request uses a separate
            # outbound journal of the same identity, exactly as the native
            # dropped-receipt test does. bp-service owns bundle creation.
            work = 'f8-carrier-%d' % i
            self.invoke('bp-service', 'run', '127.0.0.1', port,
                        self.file('A', 'request-%d.adu' % i), self.file('A', 'request-fnbs-%d' % i),
                        self.eid('A'), self.eid('B'), work, work + '-attempt', 0,
                        3600000, 2, 32, 1048576, 0, 0)
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
        self.dispatch()
        self.h.complete(op, b'different-boot fenced; unchanged lifecycle; original domain recovered\r\n')
        witnessed.add('different-boot')

    def execute(self, step, witnessed):
        action = step['action']
        if action == 'post':
            self.post(step)
        elif action in ('transfer', 'duplicate'):
            self.transfer(step['i'], step.get('mode', 'duplicate'), witnessed)
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
            peer = WirePeer(port, self.c.recovery, node_id=self.eid('B').encode())
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
        for i in sorted(self.requests.keys() - self.offered):
            self.transfer(i, 'clean', witnessed)

    def observe(self):
        observations = {}
        for name in ('A', 'B'):
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
            observations[name] = {'articles': articles, 'article_count': int(counts[0]),
                                  'duplicates': duplicates, 'complete': True}
        return observations

    def close(self):
        for name in list(self.active):
            self.stop_bp(name)
        for name in self.nodes:
            self.stop_reader(name)
        for name, process, op in self.processes:
            process.stop(grace=5)
            op['rc'] = process.returncode
            self.file(name, 'bp-%d.stdout' % process.pid).write_bytes(process.stdout.since(0))
            self.file(name, 'bp-%d.stderr' % process.pid).write_bytes(process.stderr.since(0))
        self.relay.close()


def run_campaign(campaign, seed=1, histories=1, budget=16):
    reports, trials = [], []
    for index in range(histories):
        recipe = generate(seed + index)
        h, findings, notes = campaign.trial(recipe)
        missing = FAULTS - set(notes['witnessed'])
        if missing:
            findings.append(('P5-RECOVERY', 'missing fault witnesses: ' + ', '.join(sorted(missing))))
        def replay(candidate, prop, detail):
            _, fs, _ = campaign.trial([op['args'] for op in candidate])
            return (prop, detail) in fs
        complete = all(complete_observation(notes['observations'].get(n)) for n in ('A', 'B'))
        notes['divergence'] = (len(set(notes['observations']['A']['articles'].items())
                                  ^ set(notes['observations']['B']['articles'].items())) if complete else None)
        reports.append(report(h, findings, PROPERTIES if complete and not missing else [], replay, budget))
        trials.append(dict(notes, seed=seed + index))
    out = merge_reports(reports)
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
    campaign = BpCampaign(SimpleNamespace(node=parent), ph or {'recovery_s': 120}, image, developer)
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
