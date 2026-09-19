# Design summary: the node functionality and its refinement (wave 4)

Full design: [`specs/node-functionality.md`](../../specs/node-functionality.md).
Base `9321344`. No book was written or certified; every ACL2 form in the
design is a statement to be proved, using existing names exactly.

## The one object

F_node is an ACL2 state machine whose state is the relay state
(`fn-relay-invp`: store under `fn-snt-relation`, sender `fn-bp-binding-statep`,
receiver `fn-bpr-statep`, terms, undertakings) plus configuration,
connections (`fn-wire-statep` × `fn-nntp-sessionp` × a pinned committed
version) and the clock observation. Committed history and generation are
`fn-sf-records`/`fn-sf-frontier` of the store, never separate fields. Its
step dispatches each port's event to the existing machine: `fn-wire-drive`
then `fn-nntp-step` per framed command against the pinned replay; `fn-snrt-step`
for store events; `fn-bp-step`, `fn-relay-accept`, `fn-bpi-ingress-prepare`
for the BP ports. Every subsystem is therefore a projection, stated as
commuting-square equalities with `fn-ideal-statep` as the only hypothesis.

## The claim

The running system trace-refines F_node with the identity simulator. This is
a legitimate UC instance in the F_auth-hybrid model: authority is the
constrained function `fn-assume-policy-authorizedp` that both worlds call,
so nothing is abstracted away. A nontrivial simulator enters at exactly two
argument positions (`policy-authorizedp` of `fn-bp-prepare-receipt`,
`authorized` of `fn-bpr-accept-request`) when signatures arrive, and would
enter at `fn-frame-digest` if identity were compared by digest; OBJ-001's
quarantine keeps the digest a semantic branch instead. The host is a byte
pump under A-HOST; crash cuts are `(:store (:crash ...))`/`(:reopen ...)`
events under `fn-sf-crash-imagep`, which is where A-DURABILITY is applied.

## Server robustness, five theorems over `fn-ideal-serve`

Totality: guard `t` verified and a guard-closure `assert-event` over the
world, mirrored as a `ledger.py --check` rule. Work: an instrumented twin
bounded linearly by input length and configuration. Memory: reachable
states bounded by configuration, which requires `posp` charges. Refusals: a
closed enumeration, refusals leave the committed history unchanged,
uncertain iff fenced. Semantics: the reply stream is partition-independent
(lifting `fn-wire-drive-partition-independence`) and equals `fn-nntp-step`
per command on the pinned archive; connection isolation follows from the w2
owner keystones.

## The gap the design names

`fn-reader-chunk` is `:mode :program` and the `while pending:` loop is
Python; together they compute `fn-wire-drive` but no theorem says so. That
is the wire `pending_subject`. Packet P1 writes the loop once in logic mode
and proves it equal to the ideal octets step.

## Strawman audit

Branch-of-definition refusal theorems (flagged and the unflagged
recognizer-hypothesis siblings) prove nothing about the system: rename
`-by-definition`, extend the detector, drop from the registry. Teeth whose
witness fails only a shape clause (`*forged*`, `*untyped*`) prove nothing:
add shape recognizers and a shape `assert-event` beside every such witness
or retire it. Reachability witnesses are not teeth; relabel. The clock,
codec, watermark, evolving-store, release, relay and `assumptions-tests`
cases are legitimate teeth and stay.

## Composition with BP

F_dtn is an unauthenticated adversarially scheduled channel (withhold,
choose any in-flight bundle, deliver again, drop, inject; no fabrication;
expiry decided by the receiver's clock). F_node × F_dtn is a map from
endpoint to node plus one channel. The end-to-end theorem: an obligation
pinned at A is released only against a receipt that is authorized, grounded
in a committed record at a system node, and leaves A's archive pin, under
every schedule; duplicate delivery is idempotent on state. Progress stays
PRF-018 under A-FAIRNESS.

## Packets

P0 F_node books (core lane) → P1 served path in logic mode (service
integrator) → P2 guard closure and ledger rule (assurance tooling); then in
parallel P3 cost and size, P4 typed refusals, P7 strawman retirements; P5
F_dtn, composition and assumptions applied (after P0 and w2 owner); P6
crypto seam entry with the substrate lane. Acceptance criteria are in the
design's section 6.
