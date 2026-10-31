"""Form S for fn2 under the simulator (milestone M1a): the served verbs judged by H2's model, the interim
replies named.

The machine opens connections through SimTarget (layer D's session: fn2_sim_session.py over
fn2/tests/sim-session.lsp; one simulated node per test, one connection per example) and sends commands in
random chunkings, so every reply is also a fragmentation case. Two kinds of command:

  served   (fn2_conn_interim.json "served_verbs", and STARTTLS, which D3 answers exactly as the model does
           for a node without TLS: 580): NntpModel judges the reply, under the profile D3 serves (posting
           off, no TLS, no credentials, no SASL mechanism, no AUTHINFO label until E2: `d3` policy below)
  interim  (the table's "interim" commands): the reply must be the table's code; each is counted as OWED with
           the quest that replaces it, never a pass and never a red. A different code is a disagreement. A line
           whose verb has left the table is judged by the model as a served one.

The gate (M1a): zero disagreements on served verbs and every interim reply named. Every connection's WIRE
verdict is asserted at the end (sim_target.SimTarget).
"""
import json
from pathlib import Path

from fn2.tests.surface.live_evidence import capture_step, record_failure

INTERIM = json.loads((Path(__file__).resolve().parents[1] / 'fn2_conn_interim.json').read_text())
# D3's profile, stated where the model reads it: posting off (greeting 201, MODE READER 201), no TLS (STARTTLS
# 580, no STARTTLS label), no credential store and no SASL mechanism (AUTHINFO USER 381, PASS 481/482,
# SASL 503), and no AUTHINFO/SASL capability lines until E2 renders them.
# The sessions' profile has no read rows, so the node serves no archive: the cursor's verbs, once out of the
# interim table, answer *fn2-answer-unread* (503; NEXT and LAST 412), which the model states as archive False.
# A session profile with read rows and a published group turns this to True with the model's groups set to it.
D3_POLICY = {'posting': False, 'starttls': False, 'sasl_mechanisms': [], 'advertise_authinfo': False,
             'clock': 'unknown', 'archive': False}


def machine(case, target, owed, served=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, rule
    from fn2.tests.model.nntp_model import NntpModel

    served_lines = st.sampled_from([
        b'CAPABILITIES', b'CAPABILITIES AUTOUPDATE', b'CAPABILITIES x', b'HELP', b'HELP x', b'DATE', b'DATE x',
        b'MODE READER', b'MODE STREAM', b'MODE x', b'MODE', b'LIST OVERVIEW.FMT', b'LIST HEADERS', b'LIST MOTD',
        b'LIST DISTRIBUTIONS', b'LIST DISTRIB.PATS', b'AUTHINFO USER hu-reader', b'AUTHINFO PASS secret',
        b'AUTHINFO SASL SCRAM-SHA-256', b'AUTHINFO SASL PLAIN', b'AUTHINFO USER', b'AUTHINFO x',
        b'XREDEEM 0123456789abcdef0123456789abcdef hu-friend', b'XREDEEM PASS secret', b'XREDEEM x',
        b'STARTTLS', b'NOSUCHCOMMAND', b'GROUP', b'ARTICLE <a@b> extra', b'COMPRESS DEFLATE',
        b'IHAVE <t@x>', b'CHECK <t@x>', b'TAKETHIS <t@x>', b'QUIT'])
    interim_lines = st.sampled_from([
        b'GROUP surface.test', b'LISTGROUP', b'ARTICLE <a@b>', b'HEAD 1', b'BODY', b'STAT <x@y>', b'NEXT', b'LAST',
        b'OVER 1-', b'XOVER 1-', b'HDR subject 1-', b'XHDR subject 1-', b'LIST ACTIVE', b'LIST NEWSGROUPS',
        b'NEWGROUPS 20260101 000000', b'NEWNEWS * 20260101 000000', b'POST', b'XPAT subject 1- *x*',
        b'XFN-ZARTICLE <a@b> ' + b'0' * 64])

    class SimNntp(RuleBasedStateMachine):
        @capture_step(case, 'nntp')
        def __init__(self):
            super().__init__()
            self.case, self.trace = case, []
            self.model = NntpModel({'surface.test': {}}, [], {}, dict(D3_POLICY))
            self.connect()

        def connect(self):
            self.conn = self.model.connect(tls=False, implicit_tls=False)
            self.client = target.connect()
            self.check(self.conn.greeting(), self.client.greeting, command=b'greeting')

        def check(self, expected, status, body=None, *, command):
            verdict = expected.check(status, body)
            self.trace.append(dict(rule=verdict.rule, request=command, reply=dict(status=status, body=body),
                                   model_verdict=verdict))
            if not verdict.ok:
                record_failure(case, 'nntp', rule=verdict.rule, request=command,
                               reply=dict(status=status, body=body), verdict=verdict, trace=self.trace)
            case.assertTrue(verdict.ok, f'{verdict.rule}: {verdict.detail}; {command!r} -> {status!r}')
            expected.update(status, body)

        def exchange(self, line, chunks):
            self.client.send(line + b'\r\n', chunks)
            return self.client.line()

        @rule(line=served_lines, cut=st.integers(min_value=0, max_value=40))
        @capture_step(case, 'nntp', request=lambda self, line, cut: line)
        def served(self, line, cut):
            if self.conn.quit:
                return self.reconnect()
            self.judge(line, cut)

        def judge(self, line, cut):
            expected = self.conn.send(line + b'\r\n')
            chunks = [cut, len(line) + 2 - cut] if cut and 0 < cut < len(line) + 2 else None
            status = self.exchange(line, chunks)
            body = None
            if expected.multiline_for(status):
                rows = []
                while True:
                    row = self.client.line()
                    rows.append(row)
                    if row == b'.\r\n':
                        break
                body = b''.join(rows)
            self.check(expected, status, body, command=line)
            if served is not None:
                verb = line.split()[0].decode()
                served[verb] = served.get(verb, 0) + 1
            if self.conn.quit:
                self.reconnect()

        @rule(line=interim_lines)
        @capture_step(case, 'nntp', request=lambda self, line: line)
        def interim(self, line):
            if self.conn.quit:
                return self.reconnect()
            verb = line.split()[0].decode()
            if verb not in INTERIM['interim']:
                # The verb left the interim table (its quest landed): the model judges it as served.
                return self.judge(line, None)
            entry = INTERIM['interim'][verb]
            status = self.exchange(line, None)
            owed[verb] = owed.get(verb, dict(quest=entry['quest'], code=entry['code'], replies=0))
            owed[verb]['replies'] += 1
            ok = status[:3] == str(entry['code']).encode()
            self.trace.append(dict(rule='interim', request=line, reply=dict(status=status),
                                   model_verdict=dict(ok=ok, detail=f"interim {entry['code']} ({entry['quest']})")))
            if not ok:
                record_failure(case, 'nntp', rule='interim', request=line, reply=dict(status=status),
                               verdict=dict(ok=False, detail=f"interim table says {entry['code']}"), trace=self.trace)
            case.assertTrue(ok, f"{line!r}: interim table says {entry['code']} ({entry['quest']}), got {status!r}")

        @rule()
        def reconnect(self):
            if not self.conn.quit:
                expected = self.conn.send(b'QUIT\r\n')
                self.check(expected, self.exchange(b'QUIT', None), command=b'QUIT')
            self.client.close(quit=False)
            self.connect()

        def teardown(self):
            self.client.close(quit=False)

    return SimNntp
