"""Check promoted-host death-cut inventory and storage handoff ordering.

The model coordinate is the simulator's crash transition, which lands pending
writes before restarting the core. The declared host coordinates are intervals
around simulator take, physical I/O and terminal posting. This is a
source audit of those coordinates and ordering, NOT a proof of host refinement,
OS durability, runtime branch selection, or certification of the model books.
Native crash campaigns and ACL2 certification are separate gates.
"""
from collections import Counter
from pathlib import Path

import ledger
from served_host_check import inspect, walk

ROOT = Path(__file__).resolve().parents[1]
MODEL_PATHS = ['sim/sim.lisp', 'sim/sim-adapter-base.lisp', 'sim/check-own.lisp',
               'books/host-boundary.lisp', 'books/host-ops.lisp']
# Every literal injection site, including the two distinct network syscall sites.
# Values name the surrounding model transition, not a native syscall guarantee.
CUTS = {
    ('fn2-n-tls-ready', 'tls-start'): 'fn2-sim-physical',
    ('fn2-n-tls-ready', 'tls-handshake'): 'fn2-sim-physical',
    ('fn2-n-tls-ready', 'tls-record'): 'fn2-sim-physical',
    ('fn2-native-tls-flush', 'tls-send'): 'fn2-sim-physical',
    ('fn2-native-tls-fill', 'tls-receive'): 'fn2-sim-physical',
    ('fn2-n-start-ready', 'syscall'): 'fn2-sim-physical',
    ('fn2-n-start-now', 'syscall'): 'fn2-sim-physical',
    ('fn2-n-storage-submit', 'device-submit'): 'fn2-sim-take-one',
    ('fn2-n-storage-completions', 'device-return'): 'fn2-sim-complete-result',
    ('fn2-n-take', 'take'): 'fn2-sim-take-one',
    ('fn2-n-take', 'ack'): 'fn2-sim-take-one',
    ('fn2-n-post-completions', 'post'): 'fn2-sim-terminal-post',
    ('fn2-device-worker', 'device-syscall'): 'fn2-sim-physical',
    ('fn2-device-worker', 'device-syscall-return'): 'fn2-sim-complete-result',
}
ORDERS = {
    'fn2-native-tls-flush': ['fn2-tls-%drain', '@tls-send', 'fn2-native-send'],
    'fn2-native-tls-fill': ['@tls-receive', 'fn2-native-recv', 'fn2-tls-%feed'],
    'fn2-n-take': ['fn2-host-outbox-peek', 'fn2-host-action', 'fn2-host-op-span',
                  '@take', 'fn2-host-outbox-ack', '@ack', 'fn2-n-start-now'],
    'fn2-n-storage-submit': ['fn2-device-request', '@device-submit', 'fn2-device-submit'],
    'fn2-device-worker': ['@device-syscall', 'fn2-device-perform', '@device-syscall-return'],
    'fn2-n-storage-completions': ['fn2-device-take-completion', '@device-return',
                                'fn2-device-io-observation', 'fn2-n-complete'],
    'fn2-n-post-completions': ['fn2-host-post-accept-result', 'fn2-host-post-result', '@post'],
    'fn2-sim-take-one': ['fn2-outbox-peek', 'fn2-sim-register', 'fn2-outbox-ack'],
    'fn2-sim-crash': ['fn2-sim-crash-flight-writes', 'fn2-sim-crash-state',
                      'fn2-own-restart', 'fn2-core-init'],
    'fn2-sim-crash-state': ['fn2-sim-crash-units', 'fn2-storage-crash-reset',
                           'fn2-network-restart', 'fn2-sim-clear-flights'],
}
# These source contracts inspect arguments and result threading, not just names.
# They deliberately do not substitute for a host/simulator state relation proof.
CONTRACTS = {
    'fn2-native-tls-flush': [
        '(fn2-native-send fd (sb-sys:sap+ (sb-sys:vector-sap buffer) off) remaining)',
        '(incf (fn2-native-tls-output-offset tls) n)'],
    'fn2-native-tls-fill': [
        '(room (min (length buffer) (fn2-tls-%input-room (fn2-native-tls-handle tls))))',
        '(fn2-native-recv fd (sb-sys:vector-sap buffer) room)',
        '(= n (fn2-tls-%feed (fn2-native-tls-handle tls) (sb-sys:vector-sap buffer) n))'],
    'fn2-n-tls-ready': [
        '(fn2-native-tls-open (fn2-nhost-tls-config host) (fn2-nhost-tls-window host) (fn2-nhost-tls-quantum host))',
        '(and (fn2-nop-tls-finished op) (fn2-native-tls-output-empty-p tls))',
        '(incf (fn2-nop-tls-seed-offset op) fed)'],
    'fn2-n-take': [
        '(fn2-host-outbox-ack 1 core)',
        '(make-fn2-nop :state +fn2-n-waiting+ :gen gen :kind kind :cap cap :nonce nonce '
        ':address address :len span-len :target cslot :target-gen cgen :offset storage-offset :fua fua)'],
    'fn2-n-storage-submit': [
        '(fn2-device-request (fn2-n-storage-kind (fn2-nop-kind op)) (fn2-nop-fua op) '
        '(fn2-device-backend (fn2-nhost-storage host)))',
        '(make-fn2-device-job :slot slot :gen (fn2-nop-gen op) '
        ':kind (fn2-n-storage-kind (fn2-nop-kind op)) :bytes (fn2-nhost-bytes host) '
        ':address (fn2-nop-address op) :length (fn2-nop-len op) :offset (fn2-nop-offset op))'],
    'fn2-device-perform': [
        '(ecase (fn2-device-job-kind job) '
        '(:read (%fn2-device-pread (fn2-device-fd device) sap (fn2-device-job-length job) (fn2-device-job-offset job))) '
        '(:write (%fn2-device-pwrite (fn2-device-fd device) sap (fn2-device-job-length job) (fn2-device-job-offset job))) '
        '(:fence (fn2-device-fence (fn2-device-fd device))))',
        '(setf (fn2-device-job-result job) n '
        '(fn2-device-job-errno job) (if (minusp n) (fn2-native-errno) 0))',
        '(sb-sys:sap+ (sb-sys:vector-sap bytes) (fn2-device-job-address job))'],
    'fn2-n-storage-completions': [
        '(fn2-device-io-observation (fn2-device-job-result job) (fn2-device-job-errno job))',
        '(fn2-n-complete host (fn2-device-job-slot job) code count 0 nil '
        '(and (eq (fn2-device-job-kind job) :read) '
        '(fn2-n-octets host (fn2-device-job-address job) count)))',
        '(assert (= (fn2-nop-gen op) (fn2-device-job-gen job)))'],
    'fn2-n-complete': [
        '(fn2-host-result (fn2-nop-kind op) code count aux (fn2-nop-len op) cancelled)'],
    'fn2-host-result': [
        '(fn2-sim-terminal-values kind code count aux len nil cancelled)'],
    'fn2-sim-complete-result': [
        '(fn2-sim-terminal-values kind code physical-count aux len release cancelled)',
        '(fn2-sim-terminal-post slot gen event outcome reason count aux0 aux1 '
        'fault word now release early fn2-core fn2-sim fn2-own)'],
    'fn2-n-post-completions': [
        '(fn2-host-post-result 0 slot (fn2-nop-gen op) event (fn2-nop-outcome op) (fn2-nop-reason op) '
        '(fn2-nop-count op) (fn2-nop-aux0 op) (fn2-nop-aux1 op) core)'],
    'fn2-own-post-result': [
        '(fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops)'],
    'fn2-sim-advance-with-clients': [
        '((when (equal fault *fn2-fault-crash*)) '
        '(let ((profile (fn2-sim-profile fn2-sim))) '
        '(mv-let (fn2-core fn2-sim fn2-own) (fn2-sim-crash profile fn2-core fn2-sim fn2-own) '
        '(mv t fn2-core fn2-sim fn2-own))))'],
    'fn2-sim-crash': [
        '(b* (((mv fn2-core fn2-sim fn2-own) '
        '(fn2-sim-crash-flight-writes (fn2-sim-rows fn2-sim) fn2-core fn2-sim fn2-own)) '
        '(fn2-sim (fn2-sim-crash-state fn2-sim)) '
        '(fn2-sim (fn2-sim-land *fn2-fault-crash* fn2-sim)) '
        '(fn2-own (fn2-own-restart fn2-own)) '
        '(fn2-core (fn2-core-init profile fn2-core))) (mv fn2-core fn2-sim fn2-own))'],
}


def boundary(call):
    h = ledger.head(call)
    if h == 'fn2-n-boundary' or (h == 'funcall' and len(call) > 1
                                and ledger.head(call[1]) == 'fn2-device-boundary'):
        if len(call) != 3:
            return '<malformed>'
        label = call[2]
        return label if isinstance(label, str) and not isinstance(label, ledger.Sym) else '<dynamic>'
    return None


def check(root=ROOT):
    root = Path(root)
    _, paths, findings = inspect(root)
    defs, sites, bridges = {}, [], []
    source_forms = {}
    for path in paths + MODEL_PATHS:
        source_forms[path] = ledger.read_forms((root / path).read_text())
        for form in source_forms[path]:
            if ledger.head(form) != 'defun':
                continue
            name = str(form[1])
            if name in defs:
                findings.append(f'duplicate function {name}')
            defs[name] = form
            if not path.startswith('host/'):
                continue
            for call in walk(form):
                label = boundary(call)
                if label == '<dynamic>':
                    bridges.append((name, call))
                elif label is not None:
                    sites.append((name, label))
    expected = Counter(CUTS.keys())
    actual = Counter(sites)
    for site in sorted(actual.keys() | expected.keys()):
        if actual[site] != expected[site]:
            findings.append(f'cut inventory {site}: expected {expected[site]}, found {actual[site]}')
    bridge = ledger.read_forms('(fn2-n-boundary host label)')[0]
    if bridges != [('fn2-n-open-host', bridge)]:
        findings.append('device callback must have exactly one known host-boundary bridge')
    for name in set(CUTS.values()) | {'fn2-sim-crash'}:
        if name not in defs:
            findings.append(f'missing model coordinate {name}')
    for name, contracts in CONTRACTS.items():
        nodes = list(walk(defs.get(name, [])))
        for contract in contracts:
            if nodes.count(ledger.read_forms(contract)[0]) != 1:
                findings.append(f'{name}: missing/duplicated argument or result-flow contract: {contract}')
    for source in [
        '(fn2-host-ops-code-update fn2-host-outbox-ack fn2-outbox-ack (n))',
        '(fn2-host-ops-update fn2-host-post-result fn2-post-result '
        '(cell slot gen evkind outcome reason count aux0 aux1))',
        '(defmacro fn2-host-ops-update (name target args) '
        '`(defun ,name (,@args fn2-core) '
        '(declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))) '
        '(stobj-let ((fn2-ops (fn2-core-ops fn2-core))) '
        '(fn2-ops) (,target ,@args fn2-ops) fn2-core)))',
        '(defmacro fn2-host-ops-code-update (name target args) '
        '`(defun ,name (,@args fn2-core) '
        '(declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core))) '
        '(if (fn2-core-stopped-p fn2-core) (mv :stopped fn2-core) '
        '(stobj-let ((fn2-ops (fn2-core-ops fn2-core))) '
        '(code fn2-ops) (,target ,@args fn2-ops) (mv code fn2-core)))))',
    ]:
        if source_forms['books/host-ops.lisp'].count(ledger.read_forms(source)[0]) != 1:
            findings.append('host ops wrapper no longer forwards the declared ACL2 arguments/results')
    # Normalized completion values must be retained for the later terminal post.
    writes = []
    for node in walk(defs.get('fn2-n-complete', [])):
        if ledger.head(node) == 'setf':
            writes.extend(zip(node[1::2], node[2::2]))
    for field in ('outcome', 'reason', 'count', 'aux0', 'aux1'):
        pair = (ledger.read_forms(f'(fn2-nop-{field} op)')[0], ledger.Sym(field))
        if writes.count(pair) != 1:
            findings.append(f'normalized completion {field} not retained exactly once')
    for name, expected_order in ORDERS.items():
        form = defs.get(name, [])
        observed = []
        for call in walk(form):
            label = boundary(call)
            item = '@' + label if label is not None else ledger.head(call)
            if item in expected_order:
                observed.append(item)
        if observed != expected_order:
            findings.append(f'{name}: handoff order {observed!r}, expected {expected_order!r}')
    # The worker performs one physical operation, preserving short/EINTR results;
    # no hidden write retry or successful fence may be substituted for it.
    perform = defs.get('fn2-device-perform', [])
    for primitive in ('%fn2-device-pread', '%fn2-device-pwrite', 'fn2-device-fence'):
        if sum(ledger.head(c) == primitive for c in walk(perform)) != 1:
            findings.append(f'device performer must call {primitive} at exactly one source site')
    if ledger.calls(perform) & {'loop', 'do', 'dotimes', 'dolist', 'fn2-device-perform'}:
        findings.append('device performer has a retry/iteration form requiring a new model program')
    branches = [c for c in walk(perform) if ledger.head(c) == 'ecase']
    expected_branches = {':read': '%fn2-device-pread', ':write': '%fn2-device-pwrite',
                         ':fence': 'fn2-device-fence'}
    if len(branches) != 1:
        findings.append('device performer must have one explicit operation dispatch')
    else:
        observed = {str(c[0]): ledger.head(c[1]) for c in branches[0][2:]
                    if isinstance(c, list) and len(c) == 2}
        if observed != expected_branches or len(branches[0][2:]) != 3:
            findings.append(f'device primitive mapping changed: {observed!r}')
    for name in ('fn2-native-tls-fill', 'fn2-native-tls-flush', 'fn2-n-tls-ready'):
        if ledger.calls(defs.get(name, [])) & {'loop', 'do', 'dotimes', 'dolist', name}:
            findings.append(f'{name}: TLS transport turn contains an unbounded retry/iteration')
    advance_calls = ledger.calls(defs.get('fn2-sim-advance-with-clients', []))
    if 'fn2-sim-crash' not in advance_calls:
        findings.append('simulator advance no longer reaches the crash transition')
    return {'scope': 'served source cut inventory, ABI contracts and AST order; not control-flow/refinement proof',
            'cuts': len(sites), 'model_crash': 'fn2-sim-crash', 'findings': findings,
            'audit_ok': not findings, 'correspondence_status': 'unproved'}
