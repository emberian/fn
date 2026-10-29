"""HZ store maintenance oracle, composed with the single NNTP model.

SPEC-MAP (lines at 287655a40)
===========================
Decision / effect                       Source
accepted 0; refused 1, unchanged;        docs/operator.md:1232-1242 (usage 5).
 usage extra arguments                  Extra-argument reason `usage` is provisional:
                                        exit table defines the class, not each verb.
export: history, archive-exists          docs/operator.md:819-837; storage.md:1810-1839.
export --status live / no-owner          docs/operator.md:834-837; stopped no-owner
                                        provisional; native_maintenance_live:146-148
                                        supplies command shape, not adjudication.
import preserves IDs/numbers/body;       docs/install.md:322-371; specs/storage.md:
 overrides, manifest-mismatch, profile,  1840-1848,1920-1933. `manifest-mismatch` word
 archive-incomplete, store-exists        provisional: normative text says mismatch by
                                        name; native_store_export:119-151 names it.
bless: marker, own open, secret;          docs/operator.md:774-803. snapshot-incomplete
 snapshot-incomplete / no-node-secret    and no-node-secret reason words provisional
                                        (native_snapshot_bless:56-87).
compact/checkpoint preserve state        docs/operator.md:1173-1190; specs/storage.md:
                                        602-608,637-649,668-700. Literal success
                                        text may differ live/offline; require a
                                        checkpoint/compaction outcome, exit 0.
inspect ID accepted / absent             docs/operator.md:1078-1095 (absent exit 1
                                        provisional; native_maintenance_live:53-59).
inspect group exact count/numbers/IDs;   docs/operator.md:1097-1110 (unknown-group 1).
 unknown-group                          Numbers are checked by NntpModel as well.
recover live/stopped preserves POSTs     docs/operator.md:938-946,974-979;
                                        specs/storage.md:460-470.
status live exact transaction count;     docs/install.md:271-289; stopped conservative
 stopped conservative bound             header bound, not invented exact replay count.
wire BODY/STAT/GROUP/LISTGROUP            NntpModel SPEC-MAP; no second wire oracle.

Scope: RELEASE-PLAN rows 73-75 and row 84's status/checkpoint/export/import/
bless-snapshot/inspect/recover subset. Next slice: reclaim (reclaim_live and
RSS measurement), rebind-filesystem, node-secret, repair-control, provenance,
probe, digest, journal, retention/compression, repair truncation and crash cuts.
Exports need no blessing: SNAPSHOT applies to full stopped-store copies, not
MANIFEST archives. No unblessed-export refusal is invented. Authentication and
node keys are copied separately when importing, as install.md requires.

Profile: one group, <=8 tiny authenticated articles, serialized CLI requests,
no cancellations or concurrent writes. Stored-article projection uses the posted
headers solely to supply NntpModel's authenticated POST seam; reads compare BODY,
STAT and group membership, never claim generated Injection-Info bytes. Nominal
one example ~30 seconds: two fixed posts, at most 20 generated steps, CLI timeout
3 seconds (init/start/import/export 10), <=19 wire commands/observation (two per article plus GROUP/LISTGROUP/absent-ID). These are work
bounds, not a wall guarantee; the surface child has its independent timeout.

Design note for Astra: retain a model per store plus immutable export captures,
not an oracle reset from observed inspect output. Switching the same stopped
Node to a fresh imported path saves port leases while preserving an independent
expected round trip. A full snapshot producer is not tested: the completion
marker is an explicit fixture observation, just as the carried native does.
"""
from copy import deepcopy
from dataclasses import dataclass
import re

from .nntp_model import NntpModel
from .limits_model import STORE_INIT

GROUP = 'surface.test'
LOGIN = 'hz-store-poster'
PASSWORD = 'hz-store-fixture-password'  # FAKE-SECRET
ADJUDICATIONS = ()  # Seat adds only rows backed by a recorded fn1 reply.


def article(serial):
    ident = f'<hz-store-{serial}@surface.invalid>'
    data = (f'From: hz@surface.invalid\r\nNewsgroups: {GROUP}\r\n'
            f'Subject: HZ {serial}\r\nMessage-ID: {ident}\r\n'
            f'Date: Thu, 29 Oct 2026 12:00:00 +0000\r\n\r\nHZ body {serial}\r\n').encode()
    return ident, data


def wire_model():
    return NntpModel({GROUP: {}}, [], {LOGIN: {'password': PASSWORD, 'posting': True}},
                     {'posting': True, 'stored_articles': {}})


def named_reason(reply):
    """Exact reason token, never substring/prefix matching an adjudication."""
    text = reply.get('text', '')
    reasons = re.findall(r'\breason=([A-Za-z0-9-]+)', text)
    if reasons:
        return reasons[0].lower() if len(reasons) == 1 else None
    found = re.search(r'\b(?:refused\s+)([A-Za-z0-9-]+)', text)
    if found:
        return found[1].lower()
    return 'usage' if re.search(r'(?im)^usage:', text) else 'absent' if re.search(r'(?m)^absent ', text) else None


@dataclass(frozen=True)
class Request:
    verb: str
    argument: str = ''
    destination: str = ''
    override: tuple = ()
    direct: bool = False
    malformed: bool = False


class Expect:
    def __init__(self, model, request):
        self.model, self.request = model, request
        self.exit, self.reason, self.argument_class = model.classify(request)

    def check(self, reply):
        if reply.get('exit') != self.exit:
            return f'{self.request.verb}: expected exit {self.exit}'
        if self.reason and named_reason(reply) != self.reason:
            return 'named refusal: expected ' + self.reason
        if self.request.verb == 'import':
            exists = self.exit == 0 or self.request.destination in self.model.stores
            if reply.get('destination_exists') is not exists:
                return 'import destination presence differs (refusal must publish nothing)'
        if self.exit:
            if self.request.verb == 'export' and reply.get('archive_before') != reply.get('archive_after'):
                return 'refused export changed existing archive'
            return None
        m, r, text = self.model, self.request, reply.get('text', '')
        count = len(m.wire.articles)
        if r.verb == 'inspect-group':
            rows = text.splitlines()
            expected = [f'inspect group={r.argument} members={count}'] + [
                f'{number} {ident}' for number, ident in m.wire.groups[GROUP]]
            if rows[:len(expected)] != expected:
                return 'inspect group count/number/identity differs'
            # A spurious extra membership must not be hidden after the prefix.
            if any(re.match(r'^\d+ <', row) for row in rows[len(expected):]):
                return 'inspect extra membership'
        elif r.verb == 'inspect':
            if not re.search(r'(?m)^accepted ' + re.escape(r.argument) + r'(?: |$)', text):
                return 'inspect accepted identity missing'
        elif r.verb == 'status':
            live = re.search(r'(?m)^transactions=(\d+)(?: |$)', text)
            stopped = re.search(r'(?m)^stopped checkpoint=(?:none|\d+) journal-octets=\d+ transactions-at-most=(\d+)$', text)
            if m.running:
                if not live or int(live[1]) != count:
                    return 'status live transaction count differs'
            elif not stopped or int(stopped[1]) < count:
                # Direct `store STORE status` replays and reports exact count.
                if not (r.direct and live and int(live[1]) == count):
                    return 'status stopped bound below model or missing'
            if m.overrides.get('max-transactions'):
                if not re.search(r'max-transactions[= ]+' + str(m.overrides['max-transactions']) + r'\b', text):
                    return 'import profile override missing from status'
        elif r.verb == 'recover':
            token = 'recover accepted owner=serving' if m.running else 'recovered'
            if token not in text:
                return 'recover outcome missing'
        elif r.verb in ('compact', 'checkpoint'):
            if not re.search(r'checkpoint|compact', text):
                return 'maintenance outcome missing'
        elif r.verb == 'export':
            if not re.search(r'exported (?:records=|archive=)', text):
                return 'export completion missing'
        elif r.verb == 'export-status':
            if not re.search(r'export(?:ed| .*state=| idle| status)', text):
                return 'export status outcome missing'
        elif r.verb == 'import':
            n = len(m.archives[r.argument]['wire'].articles)
            if not re.search(r'imported records=' + str(n) + r'(?: |$)', text):
                return 'import record count differs'
        elif r.verb == 'bless-snapshot':
            n = len(m.archives[r.argument]['wire'].articles)
            if not re.search(r'blessed snapshot=.*transactions=' + str(n) + r'\b', text):
                return 'blessed snapshot transaction count differs'
        return None

    def recorded_difference(self, reply, target='fake'):
        if (target not in ('fn1', 'fn2') or self.check(reply) is None
                or self.exit != 1 or reply.get('exit') not in (1, 5)
                or self.reason is None or named_reason(reply) is None):
            return None
        if self.request.verb == 'import' and reply.get('destination_exists') is not (
                self.request.destination in self.model.stores):
            return None
        if self.request.verb == 'export' and reply.get('archive_before') != reply.get('archive_after'):
            return None
        for row in ADJUDICATIONS:
            if target == 'fn2' and row['class'] != 'spec-ambiguity':
                continue
            observed = row['fn1_reply']
            if (row['verb'] == self.request.verb and row['argument_class'] == self.argument_class
                    and observed['exit'] == reply.get('exit')
                    and observed['reason'] == named_reason(reply)):
                return dict(deepcopy(row), target=target, observed_reply=deepcopy(reply))
        return None

    def update(self, reply, target='fake'):
        recorded = self.recorded_difference(reply, target)
        if not recorded and self.check(reply):
            raise AssertionError(self.check(reply))
        m, r = self.model, self.request
        if self.exit:
            return recorded
        if r.verb == 'export':
            m.archives[r.argument] = {'kind': 'export', 'wire': deepcopy(m.wire), 'valid': True}
            m.last_export = r.argument
        elif r.verb == 'import':
            m.stores[r.destination] = deepcopy(m.archives[r.argument]['wire'])
            m.store_overrides[r.destination] = dict(r.override)
        return recorded


class StoreOpsModel:
    def __init__(self):
        self.stores = {'source': wire_model()}
        self.store_overrides = {'source': {}}
        self.current, self.running, self.last_export = 'source', True, None
        self.archives = {'nonempty': {'kind': 'nonempty', 'valid': False}}

    @property
    def wire(self):
        return self.stores[self.current]

    @property
    def overrides(self):
        return self.store_overrides[self.current]

    def rule(self, verb, argument='', **kwargs):
        return Expect(self, Request(verb, argument, **kwargs))

    def classify(self, r):
        if r.malformed:
            return 5, 'usage', 'extra-argument'
        if r.verb == 'export' and r.argument in self.archives:
            return 1, 'archive-exists', 'existing-archive'
        if r.verb == 'export-status' and not self.running:
            return 1, 'no-owner', 'stopped-owner'
        if r.verb == 'import':
            if r.destination in self.stores:
                return 1, 'store-exists', 'existing-store'
            archive = self.archives[r.argument]
            if not archive.get('valid'):
                reason = 'manifest-mismatch' if archive['kind'] == 'tampered' else 'archive-incomplete'
                return 1, reason, archive['kind']
            if r.override and dict(r.override).get('max-history-octets', STORE_INIT['max-history-octets']) < STORE_INIT['max-record-octets']:
                return 1, 'profile', 'inconsistent-profile'
        if r.verb == 'bless-snapshot':
            archive = self.archives[r.argument]
            if not archive.get('marker'):
                return 1, 'snapshot-incomplete', 'unmarked-copy'
            if not archive.get('secret'):
                return 1, 'no-node-secret', 'copy-without-secret'
        if r.verb == 'inspect' and r.argument not in self.wire.articles:
            return 1, 'absent', 'absent-id'
        if r.verb == 'inspect-group' and r.argument != GROUP:
            return 1, 'unknown-group', 'unknown-group'
        return 0, None, 'valid-' + ('live' if self.running else 'stopped')
