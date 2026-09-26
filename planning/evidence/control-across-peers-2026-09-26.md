# control-across-peers (wave 4, lane 11), 2026-09-26

Lane `lane/control-across-peers` from dev `17ff24aa`; brief
`build/coordinator/queue/done/w4-control-across-peers.txt` (PKT-210, PKT-147,
PKT-208, PKT-154; ids PRF-170, NNT-037, SCN-100, PKT-443, PKT-444).

## Summary

- **PKT-210, the two-node matrix: no disagreement.** 48 node observations
  (2 bases x 3 grant placements x 2 orders x 2 kill modes x 2 receivers),
  each the D29 answer, with pinned readers on both nodes and a revoke plus
  SIGKILL that changes no decision.
- **PKT-147: named.** A signed article naming a group the node does not
  serve answers `refused hybrid-author UNKNOWN-GROUP` (exit 1); every other
  refusing arm of the signed-author ingress names its word. PRF-170.
- **PKT-208:** `:control-signed` removed from both reason tables. The
  nil-group-index view is **reachable** (two cancels naming each other) and
  still answers the plain `430 no article with that message-id`: PKT-443.
- **PKT-154:** the BP v3 path files natively; a pre-C1 signed control does
  **not** replay (a fault at open); the repair path is PKT-444.

## 1. The matrix (PKT-210)

`tests/test_native_control_across_peers.py`. Three loopback nodes: H
authors every target and cancel (signed through `hybrid-author`, unsigned
through POST) and the harness fetches their octets before relaying, so it
controls the order in which A and B receive each pair over IHAVE (Path
prefixed with the configured peer's name). P and Q are enrolled on all
three; Q holds `cancel` over `fn.ga.*` on A only, `fn.gb.*` on B only and
`fn.gab.*` on both. Per basis, the twelve cases are {target in fn.ga.t,
fn.gb.t, fn.gab.t} x {target then cancel, cancel then target} x {no kill,
both receivers SIGKILLed and restarted between the two arrivals}. Readers
are opened on A and on B after every first arrival; after the second
arrivals they read every target-first target again, then POST (their 240
re-pins them) and read again. Then every grant is revoked on both nodes and
both are SIGKILLed and restarted.

| Basis | Target group | A (both orders, both kill modes) | B (same) | after revoke + SIGKILL |
| --- | --- | --- | --- | --- |
| author (P cancels P's signed target) | fn.ga.t / fn.gb.t / fn.gab.t | 430 withdrawn | 430 withdrawn | unchanged |
| authority (Q cancels unsigned) | fn.ga.t (grant on A) | 430 withdrawn | 220 | unchanged |
| authority | fn.gb.t (grant on B) | 220 | 430 withdrawn | unchanged |
| authority | fn.gab.t (grant on both) | 430 withdrawn | 430 withdrawn | unchanged |

Pinned readers, both bases, both nodes: 220 for every target seen before
the second arrivals, still 220 after them; after their own POST (240) the
fresh answer. Every relay `335 / 235`. Disagreements: **none**.

The theorems these cases witness are cited, not restated (the host line is
the one C3 names, `fn-own-refresh` through `fn-own-read`):
`fn-ctl-visible-is-arrival-order-independent` (the two orders),
`fn-ctl-cancel-executes-only-for-author-or-authority` (grant placement),
`fn-ctl-pinned-view-keeps-its-archive` (the pinned readers),
`fn-ctl-replay-is-the-fold` and `fn-ctl-revoke-changes-decisions-not-records`
(the kill and the revoke), books/control-authority.lisp.

Two further cases in the module: a cancel naming its own Message-ID is
declined (`(:decline :self-target)`, books/control-authority.lisp
`fn-ctl-withdrawal-plan`): 220 before and after a SIGKILL; and the empty
view (section 3), an expected failure.

Assurance chain: native entry `hybrid-author` / POST / IHAVE -> ACL2 filing
(`fn-owner-control-filing` -> `fn-pa-filing-plan`) and the Store acceptance
-> `fn-own-refresh`'s withdrawal decision under the configuration at the
cancel's txid (`fn-ctl-refresh-withdrawals`, the journal) -> the owner
relation carrying the visible list -> `fn-own-read`'s served answer
(`fn-nntp-withdrawn-article-answers-430-withdrawn`) -> observed 430
withdrawn / 220. Recovery (`fn-cpo-open-observed`, the refresh after
reopen) re-establishes the relation; every refresh preserves it.

## 2. PKT-147: the unserved group, named (PRF-170)

Cause found: the spike's refusal was the **carrier arm** of
`fnn-hybrid-control-author` (host/native/hybrid-control.lisp), whose
`fn-hsig-injected-carrier-octets` runs the injecting agent
(`fn-hsig-injected-carrier-plan` -> `fn-inj-decide`), which refuses
`:unknown-group` for a Newsgroups name outside the configuration's served
groups; the arm returned a bare `:refused`. The inferred fault at the group
code lookup is not reached for an unserved group (the carrier arm refuses
first, before any bound submission). The owner of the decision is therefore
the injection decision, not `fn-own-control-decision`, which is unchanged.

- `fn-hsig-injected-carrier-reason` (books/hybrid-store-injected.lisp): the
  plan's reason; the host calls it when the octets are nil.
- `fn-inj-decide-served-groups-choose-only-unknown-group`: a source admitted
  under a served list G1 is, under G2 (same agent, bound and clock), the
  identical decision when every group it names is in G2, else
  `(fn-inj-refuse :unknown-group)`.
- KEYSTONE `fn-hsig-injected-carrier-unserved-group-is-refused-by-name`
  (`:rule-classes nil`), over the host-called pair: same octets and no
  reason when served; nil octets and `:unknown-group` otherwise. Host line:
  hybrid-control.lisp `fnn-hybrid-control-author`, the `(unless received`
  arm.
- `fn-nhc-author-refusal (arm reason)` (books/native-hybrid-control.lisp):
  the word of each refusing arm (`author-not-enrolled`, `source-malformed`,
  `unknown-group`, `carrier-refused`, `article-exceeds-profile-bound`,
  `control-not-filed`, `control-malformed`, `signed-event-not-formed`);
  `fn-nhc-author-refusal-is-a-named-refusal` (every word a control status,
  class `:refused`, exit 1) and `fn-nhc-author-refusal-names-an-unserved-group`.
  The seven new words are appended to `*fn-nctrl-statuses*` (every earlier
  status keeps its octet). The operator post's words are unchanged.

Teeth: tests/acl2/hybrid-store-tests.lisp (a reachable witness of each
branch with both hypotheses asserted; without the first, posting
disallowed: the reason is `:posting-disallowed` and the `:unknown-group`
assertion must-fail; without the second, a non-name in G2: `:config-invalid`,
must-fail), tests/acl2/native-hybrid-control-tests.lisp (every arm's word,
the reply round trip with codec-attach, two must-fails).

Native (hbox, developer image `f10414e9` at `f9b91cde`):
`test_unserved_group_and_every_refusal_are_named` ok: fn.unserved only,
fn.test,fn.unserved and a cancel naming fn.unserved each `refused
hybrid-author UNKNOWN-GROUP`; fn.test `accepted`; generation 7
`AUTHOR-NOT-ENROLLED`; a damaged ML-DSA signature `SIGNED-EVENT-NOT-FORMED`
(log native-m2-manual-h1.log; its second test errored on the harness's
missing FN_ACL2 and was rerun as manual-bp2).

## 3. PKT-208

`:control-signed` removed from `*fn-pa-served-reasons*`,
`fn-post-store-refusalp`'s list and `fn-post-store-refusal-text` (nothing
produces it since c3, b94f1015; no book depends on the constants' shape);
`fn-post-outcome-store-refusal-kinds-are-distinct` still holds; teeth in
control-tests and nntp-post-tests (it is no longer a served reason; the two
filing words are).

The nil-group-index view: **reachable**. `fn-own-refresh` builds the group
index as `fn-gidx-build` of the visible list, nil when nothing is visible;
`fn-served-conn-pinned-index` then pins the bare trie without the control
pin. A self-cancel does not reach it (declined), but two signed cancels by
one author naming each other withdraw each other, leaving nothing visible:
both answer `430 no article with that message-id` (fresh and after a
SIGKILL; `GROUP control.cancel` 211 0 3 2). Classified: implementation (the
served answer), not fixed here: the fix changes books/served.lisp's pin
shape and what GROUP answers over nil buckets, a served-closure change with
a reader-visible decision; PKT-443 (1). The native case stays with the
served guarantee as its expectation, marked expected failure.

## 4. PKT-154

Reach: `fn-owner-app-plan-install-legacy` is called only from
`fn-owner-app-plan-install` when the recovered request intent is the old
`:request-intent` form, which no current node writes; the lab and every
fresh node take the v3 path (`fn-bpaj-transit-plan` ->
`fnn-owner-attempt-transit`). Run natively on the v3 path:
`test_control_article_over_bp_is_filed_in_its_control_group` ok: without
control.cancel the receiver refuses (exit 1) and nothing is stored; with it,
the article is in control.cancel (211 1) and not in fn.test (211 0). Finding:
the refusal line reads `reason=none` (PKT-443 (2); expected-failure case
`test_bp_filing_refusal_names_its_reason`). Log native-m2-manual-bp2.log.

Pre-C1 replay: the pre-C1 developer image (`19cf7397`, 9ffef4ac's first
parent; image `f358dbac`, core `2a5ddae2`) authored a signed target and a
signed cancel (Newsgroups fn.test) into a fresh store: both stored in
fn.test, control.cancel empty. The current image (`f10414e9`) refuses to
open a copy: `fault operator run ACL2 replay rejected committed transaction
history or configuration history`. Control: the same procedure without the
cancel opens and serves the target. So the clause does not retire: the
refusal is a generic fault; PKT-444 names the repair path (a named refusal,
a migration, or declared unsupported). Script prec1_replay.py (`0f96f871`;
the control-article run used the version before its `ordinary-only`
switch, `5991ec3e`), logs prec1-replay-control.log, prec1-replay-ordinary.log.
The live node was not touched.

## Certification

persvati `run-20260926T102038Z-baf2`, manifest
`planning/evidence/manifests/certify-20260926T102113Z-288651.json`:
`--affected-by` control-authority, control-served, peer-authored-accept,
nntp-post, native-control, native-hybrid-control, hybrid-store-injected;
329 certified, 0 failed, 291 from the cache. This lane's books: hybrid-store-
injected 2.0 s, native-hybrid-control 2.1 s, native-control 2.1 s, nntp-post
4.6 s, peer-authored-accept 9.9 s, their test books 1.2 to 1.7 s. Over ten
seconds, not this lane's books (recertified because nntp-post is below
them): owner-invariants 15.3 s (10.9 s at the last merge certification,
under load both times), public-exposure 10.9 s. The REPL on persvati
(control-across-peers-repl) loaded each changed book and its test book first.

`make check-lane`: every step green except tools/proof_cost.py, on books
this lane did not change (recertified only because nntp-post and
native-control are below them). r1 measured owner-invariants 15.3 s
(baseline 10.3 s + 25% = 12.9 s; load average about 15 on persvati).
The re-measure r3 (`run-20260926T103546Z-cce3`, `--recertify
books/owner-invariants`, 110 passed, load average about 7; manifest left
uncommitted at build/acl2/certify-20260926T103616Z-456454) put
owner-invariants at 12.0 s (within tolerance) and three books not in the
baseline over ten seconds: public-exposure 12.4 s, byte-store-k0-step-bridge
11.4 s, config-owner-live 11.1 s (config-owner-live was 12.1 s at
control-c3b, public-exposure 10.9 s in r1). Classified: environment
(contention on a shared box), not a regression of these bytes; a quiet-box
measurement is the deputy's merge certification. The lane is at its run
budget (r1, r2 a no-op, r3).

## Native runs and SHA-256

- m1 (dev `17ff24aa`, developer image `aee18e71`, core `3c49c5b2`):
  native-m1-across-peers.log `193dda9c...` (2 tests OK, 25.2 s).
- m2 (`f9b91cde`, developer `f10414e9`, core `8ed4ede6`; production
  `f36b5732`, core `c8048830`): SHA256SUMS in native-m2-SHA256SUMS;
  native-m2-test-tests.test_native_control_across_peers.log `53710d0d...`
  (the self-cancel probe before it became the mutual one: failed, 220);
  native-m2-manual-ev2.log `57e3625f...` (the mutual-cancel view);
  native-m2-manual-m3-across-peers.log `434436f2...` (the module as
  committed: 4 tests, OK, 1 expected failure, 31.1 s);
  native-m2-manual-h1.log `56646c4e...`; native-m2-manual-bp2.log
  `ef1c2748...`.
- prec1: prec1-replay-control.log `1c7b10de...`,
  prec1-replay-ordinary.log `56d8a925...`.

The manual runs used the m2 tree's images with the test files copied in
(tests only; the images are the commit's).

## Not done

- PKT-443: the empty-view answer; the BP refusal reason; the pull side.
- PKT-444: the pre-C1 replay repair (ember's choice among a/b/c).
- A signed control through BP (the BP case above is unsigned; C1 filing is
  by the Control field alone).

## Continuation: the pre-C1 open (control-across-peers-2)

Lane `lane/control-across-peers-2` from dev `273cd980`; brief
`build/coordinator/queue/done/w4-control-across-peers-2.txt` (PKT-444's first
half; ids: events of PRF-170, SCN-100 extended, PKT-457).

### 1. The fault's site

The witness store (hbox `/tank/fn/scratch/control-across-peers/replay-work/store`,
written by the pre-C1 developer image `f358dbac`; committed as
`tests/fixtures/pre-c1-control-store/witness` with `SHA256SUMS`) was decoded
and replayed in ACL2 on persvati (a REPL over dev's certified books; the
records through `fn-frame-store-decode` and `fn-store-event-decode-exact`,
the configuration through `fn-cfg-decode-exact`). Three records: 0 the
keyring snapshot, 1 the signed target, 2 the signed cancel. The
configuration fold (`fn-cpr-replay`'s resumable form) is `:ok`. The identity
fold stops at record 2: `(:fault next=2 :composite-binding)`.

Classification: implementation (a generic fault where an open must succeed
or refuse by name). The function that produced it: `books/replay.lisp`
`fn-replay-identity-step`, its `fn-stxa-p` arm. Record 2 is a schema-1
composite at keyring generation 1, so neither the carried nor the revoked
arm binds and the snapshot arm's `fn-hsig-article-event-snapshot-bindsp-v1`
fails in `fn-hsig-carried-record-metadatap`: the record lists `("fn.test")`
(its Newsgroups, what the pre-C1 image filed) while
`fn-hsig-source-filed-groups` of its signed source is `("control.cancel")`
(C1's classifier: `(:control "cancel" ...)`). `fn-sco-finalize` then answers
`(:error :identity)`, `host/store-node-host.lisp` `fn-store-sn-open-extended`
`:fault`, and `host/native/io.lisp` `fnn-recover-full-replay` printed
`ACL2 replay rejected committed transaction history or configuration
history` (exit 4).

### 2. The decision (books/store-open-pre-c1.lisp; PRF-170 events)

`books/replay.lisp` and `books/control-classify.lisp` are unchanged (so no
closure above replay.lisp moved; the brief's `--affected-by` of those two was
not needed). A new leaf book:

- `fn-sopc-pre-c1-control-record-p (event)`: a schema-1 kind-4 composite whose
  signed source classifies `:control`, whose record lists exactly the
  source's Newsgroups, and not `fn-hsig-source-filed-groups`.
- `fn-sopc-open-refusal (e)`: over the extended capture E the host opens from,
  when the identity fold did not finish `:ok`, the record at its cursor, if it
  is such a record at its own sequence: `(:refused :pre-c1-control-record TXID
  MSGID)`; else nil.
- `fn-sopc-classified-open (e configs frontier)`: the refusal, else
  `fn-sco-store-open` (the pair the host used before). HOST LINE:
  `host/store-node-host.lisp` `fn-store-sn-open-extended`, which every native
  open reaches (`fn-store-sn-recover`, `fn-store-sn-recover-from-checkpoint`;
  from `fnn-recover`: store recover/inspect/checkpoint/status, the owner's
  start in `operator run`, offline `health`).
- `fn-sopc-refusal-text`: `pre-C1 control record (txid N, MSGID): run store
  repair-control`.

Theorems:

- KEYSTONE `fn-replay-identity-step-never-admits-a-pre-c1-control-record`: for
  a pre-C1 control record, `fn-replay-identity-step` from any context answers
  a context whose kind is not `:ok`, at the same cursor (the site above,
  stated over the step the fold runs).
- KEYSTONE `fn-replay-never-faults-on-a-pre-c1-control-record`: if the
  identity fold of PREFIX is `:ok`, EVENT is a pre-C1 control record and its
  sequence is `(len prefix)`, then `fn-sopc-classified-open` of the full open
  of `(append prefix (cons event rest))` (E = `fn-sco-extend` of the capture
  of no prefix, as `fn-store-sn-recover` builds it) is exactly
  `(:refused :pre-c1-control-record TXID MSGID)` of EVENT: never a fault, for
  any REST.
- `fn-sopc-checkpoint-open-names-what-the-full-open-names`: from a checkpoint
  capture of any store-event prefix extended over the suffix, the classified
  open is the full open's.
- KEYSTONE (refinement) `fn-sopc-classified-open-is-the-open-without-a-pre-c1-record`:
  when no record of E's history is a pre-C1 control record, the classified
  open IS `fn-sco-store-open` (for the full open, `fn-cpr-replay` and
  `fn-cpo-open-observed`): the change is invisible to every such history.

Teeth (`tests/acl2/store-open-pre-c1-tests.lisp`, the witness store's four
files as octet constants decoded by the host's codecs, never `ld`-ed): the
witness decodes and the pre-book open was `(:error :identity)` at cursor 2
`:composite-binding`; the step keystone reachable (cancel after the snapshot
and target) and without its hypothesis (the target advances: must-fail); the
open keystone reachable (the witness opens to `(:refused
:pre-c1-control-record 2 "<prec1-cancel@example.invalid>")` and the line),
without H1 (MUTATION, labelled: the target regrouped to fn.other stops the
fold at 1: not the refusal, must-fail), without H2 (the target: it opens,
must-fail on `:refused`), without H3 (the cancel at position 1: stops on the
sequence, nothing named, must-fail); the checkpoint form; the refinement
reachable (the store without the cancel: equal and `:ok`), a post-C1 filing
of the same cancel (MUTATION, labelled: groups `("control.cancel")`: free,
equal, opens; `:refused` must-fail), without its hypothesis (the witness:
must-fail); CORRUPTED STATE (labelled): the cancel regrouped to `("fn.test"
"control.cancel")` is not named and stays `(:error :identity)`.

The checkpoint prefix: no image before P3 (42deb1d2, after C1) writes a
checkpoint, and every image since refuses (before: faults) to open a history
holding such a record, so no checkpoint covers one; the theorem above makes
the checkpoint open name what the full open names in any case.

### 3. The host

`host/native/io.lisp`: a new condition `fnn-store-open-refusal` (a
`fnn-store-error`: exit 1 through `fn-outcome-host-condition-exit-code`, the
outcome-algebra table), raised by `fnn-recover-full-replay` with ACL2's line
(`fn-store-open-refusal-text` of the refusal `fn-store-sn-open-extended`
keeps in the global `fn-store-open-refusal`) and passed through `fnn-recover`
unchanged (the store is fenced, never rewritten into the generic
"cannot reconstruct" fault). The checkpoint path's refusal falls back to the
full replay, which refuses by name. `store ROOT repair-control` exists and
refuses `repair semantics undecided (PKT-444)` (exit 1) without touching the
store. Health reports the store refused by name (`refused operator health
...`, exit 1), not fenced (3). docs/operator.md "Recover after a crash" has
the sentence.

The line appears after each family's word, as every refusal does:
`store: pre-C1 control record (txid 2, <...>): run store repair-control`,
`refused operator run pre-C1 control record (...)...`; the brief's
`refused: ...` form is not a family's grammar.

### 4. Native (hbox, never /tank/fn/node)

`tools/hbox_native.sh --label n1 2e25e21b tests.test_native_pre_c1_open`
(/tank/fn/scratch/control-across-peers-2/native-n1; developer image
`fn-host-developer` c31eb24c..., core a5ea6074...): OK, 3 tests. Log
`planning/evidence/control-across-peers-2-2026-09-26/native-n1-test_native_pre_c1_open.log`
`6f3a8be7ea7459ed79446da038f904d842df2533c69a87b673738ee0d7d0236b`;
SHA256SUMS `native-n1-SHA256SUMS` (53b59540...). Observed: store recover,
inspect, checkpoint: `store: pre-C1 control record (txid 2,
<prec1-cancel@example.invalid>): run store repair-control`, exit 1; operator
run and health: `refused operator run|health pre-C1 control record ...`,
exit 1; the transactions unchanged; `store repair-control`: `store: repair
semantics undecided (PKT-444)`, exit 1; the ordinary store recovers 2
transactions and its status exits 0. The fixtures were copied per case,
never modified in place.

Assurance chain: native entry (`fnn-dispatch` -> `fnn-open-live-store` ->
`fnn-recover`) -> `fnn-bridge-recover` -> `fn-store-sn-recover` ->
`fn-store-sn-open-extended` -> the executed subject `fn-sopc-classified-open`
over the octets decoded by the ACL2 codecs -> the keystones above -> the
observed exit 1 and line. No maintained relation is new: the open
establishes the Store's relations exactly as before on every history the
refusal does not name (the refinement keystone).

### 5. Certification

persvati `run-20260926T114951Z-18bc`, manifest
`planning/evidence/manifests/certify-20260926T115014Z-1323843.json`:
`--affected-by books/store-open-pre-c1.lisp`: 2 certified (store-open-pre-c1
1.0 s, its tests 1.6 s), 92 from the cache, 0 failed. Both were loaded in the
REPL first. `make check-lane` green (warn only: the new book ends with no
theory withdrawal, as store-checkpoint-open does).

### 6. The repair's semantics: ember's packet (PKT-444)

Trace: section 1. Constraints: never replay a pre-C1 record silently at open;
no last-writer-wins; the record's octets are durable history. Options: (a)
replay the record as filed-under-Newsgroups history, what it meant when
written: an explicit, logged, one-way migration on a snapshot in the
two-step pattern (copy, migrate the copy, verify it opens, swap), which
rewrites nothing in the original; (b) re-file it under its filing group if the
operator created control.<verb>, else as refused evidence (changes what the
old store serves); (c) declare pre-C1 control records unsupported (the
refusal stays the answer). THE COORDINATOR'S RECOMMENDATION: (a). Affected:
the store format's replay rule for schema-1 composites, a new migration verb
(its proof: every other record replays unchanged), `store repair-control`'s
body. What continues without it: every post-C1 store (the live node's
included) opens as before; a pre-C1 store is refused by name.

### Not done (PKT-457)

- A pre-C1 MALFORMED control record (classified `:malformed`) still faults
  generically; this lane names only `:control` records.
- A schema-0 composite has no stored source to classify (not examined on a
  store).
- tools/run_store.py (the Python host) has no line for the refusal.
