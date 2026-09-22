# Handoff to Codex, 2026-09-23

Draft written by the fn root coordinator (Claude) while the last four lanes
of the night finish; the "State" section is updated when they land. Read
[how we work](how-we-work.md) and `AGENTS.md` first: they are the rules,
this file is the work. Everything here is briefed from
[the trajectory plan](plan-2026-09-22-trajectory.md) §3 and, for DTN,
[the BP node-machine contract](../specs/bp-node-machine.md) §11; where this
file and those disagree, those win and this file is wrong.

## State (at handoff)

- `dev` is the integration branch; every commit on it is pushed; `make check`
  is green at every commit. The deployed node is hbox at 192.168.50.39:1119
  from the `dabebb84` image ([page](../docs/nodes/hbox.md),
  [record](evidence/node-hbox-dabebb84-2026-09-22.md)). Its image predates
  everything landed since 22:00Z on 2026-09-22; the next freeze carries it.
- The image closure of 165 books certified at `dabebb84`. Books red at their
  current digest on `dev` are listed by `python3 tools/green_check.py --table`;
  the ones inside the image closure are the ones a freeze must fix. Two are
  known and owned: `byte-store-keystones` (PRF-041, the T5-sweep lane) and
  whatever the codec seam's cluster conversion leaves.
- Live lanes at the time of writing, and the books they own (do not edit
  these until their branches land on `dev`): `t1/codec-seam` (the seam books
  `records-seam`, `records-shape`, `records-attach`, `codec-attach`, and the
  store cluster `store-files*`, `store-node*`, `store-observed*`,
  `store-prepare-correspondence`, `replay`, `config-records`, `node-config`,
  `checkpoint*`); `t6b/profile` (`native-config`, `injection-invariants`,
  `owner-agent`); `t13/conform` (`injection`, `peer-inbound`,
  `native-operator`, the operator post entry in `host/native/io.lisp`);
  `t5/sweep` (`store-sweep`, `store-files`, `byte-store-programs`,
  `byte-store-keystones`, the sweep in `host/native/io.lisp`).

## The loop, in one paragraph

A package is DONE or NOT; there are no partial rows. State the property
first as theorem statements over the function the host calls (say the host
line), with one reachable witness and one `must-fail` per hypothesis in the
test book; iterate with `python3 tools/proof_repl.py` (a live ACL2 over a
book, seconds to a red form; `docs/proofs.md`); certify your books, their
test books and their closure on the farm before you report
(`python3 tools/farm.py submit <box> <books> --closure --jobs 4
--timeout-seconds 1800 --remote-root /home/ember/fn-gates/<lane> --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache` on persvati; hbox uses
`/tank/fn/gates/<lane>`, `/tank/fn/toolchains/w28/acl2-literal-4g`,
`/tank/fn/certcache`; then `farm.py wait`; `git add -f` the manifest); for a
whole-closure picture use one provisional wave (`python3 tools/triage.py`,
every independent red at once, publishes nothing); regenerate the ledger
(`python3 tools/ledger.py --write`); `make check` exits 0; commit named
files with prose messages; one worktree per lane under `build/lanes/`,
removed when the lane lands. No `skip-proofs`, `defaxiom`, trust tags, new
`:verify-guards nil` beyond a book's documented posture, deleted or
weakened theorems, or codec opened at the top of a book. Never `git stash`.
On hbox, builds under `swarm-build`; never `pkill -f` a pattern in your own
command line; the node at `/tank/fn/node` is root's; the matrix stores
`/home/hbox/fn-native-matrix/{a,b}` are the matrix's.

## Packages ready now

Each is independent of the live lanes' books.

### C1. Fragment lemmas, the fast reassembler and the limits table

The contract's T4 group and §7 (`specs/bp-node-machine.md`): the whole-parent
theorem, the re-fragmentation theorem composing offsets, the fast
reassembler proved equal to the reference over ALL inputs
(`fn-bpf-reassemble-fast-is-reassemble`, `fn-bpf-fragment-fast-is-fragment`),
an offset-zero coherence witness, and the limits table
(`fn-bpn-limits-compose` in a new `bp-limits`) with the reassembly limit
raised to the ADU maximum only together with every limit it composes with.
Books: `bp-fragment`, `bp-fragment-invariants`, new `bp-fragment-fast`, new
`bp-limits`, their test books. Touches no machine book. Traces N09, N10 from
the counterexample suite (§11.1) are its teeth. Box: persvati. 2 to 3
lane-days. Defects D19 and D20 in §13 are its subject.

### D1a. The status-report codec

`bp-status-report` (new): the corrected report grammar of the contract's
§7.4 (each assertion an array of a Boolean and an optional time; fragment
offset and payload length separate fields; the subject's flag governs
reported times), a bounded decoder and canonical encoder with round trip,
canonicality and the concrete conformance vectors of the grammar; reports
are labelled remote observations, never release authority (§9). Box:
local, persvati for the closure. 1 to 2 lane-days. D1b (minimal generation
and consumption in the machine) is slice B's first batch and is not this
package.

### T9a. The feed's K5

Plan row T9 (a): PRF-029 cited with teeth, and K5
`fn-feed-replay-is-the-live-feed-modulo-inflight` proved, or replaced by a
K5 theorem over `fn-feed-tick-step` and the FNFD journal the host writes,
with the open row retired. Books: `feed*`, `feed-connection*` (the T9c
lane landed the protected-channel keystones there on 2026-09-22; read
`planning/evidence/feed-tls-teeth-2026-09-22.md` and do not restate them).
Host: `host/native/feed-service.lisp`. Box: persvati. 2 to 3 lane-days.

### DTN selectors gated

The selectors lane (landed `bb0affe6`) gated every `FN_NATIVE_*` developer
selector behind one startup check on the production image. Still ungated,
because the DTN image has no developer profile: `FN_BP_*`,
`FN_TCPCL_TEST_*`, `FN_CHECKPOINT_TEST_*`, `FN_APP_JOURNAL_TEST_*`,
`FN_IMMUTABLE_PUBLISH_TEST_FAIL`. Give the DTN image a developer profile
(the shape `fnn-select-image-profile` in `host/native/io.lisp` already has),
put those selectors in the same table, and extend
`tests/native_developer_selectors_raw.lisp` and the source checks in
`tests/test_native_control.py`. Host only; `docs/operator.md` "Developer
selectors" says what is admitted. 1 lane-day.

### A1. The BP node machine and the two-process round trip

The largest package and the head of the DTN chain: the contract's §11
slice A1, briefed entirely from `specs/bp-node-machine.md` (§1 to §9 are the
contract; §5 the statements; §11.1 the counterexample suite, whose rows for
T1, T2, T3, T6 and the loop are A1's first commit). Books: the four
`bp-node-machine*` books, `tcpcl-session` (the final-END refusal), the
machine host files, `host/native/bp-service.lisp`, `host/native/tcpcl.lisp`,
the new loop book, the new teeth book and the round-trip test. Gate: two
native processes on one box exchanging one article and its application
receipt through FNBS, verified on the real owner Store and pins with a
second control work whose pin must remain, and a `kill -9` at each named
crash cut. The receive path does not merge before A2's replay theorems
certify, so A2 (records and the replay and recovery theorems, T6 group;
3 to 4 lane-days) is briefed together with A1 and starts after A1's schema
batch. Box: hbox. 7 to 9 lane-days for A1. Decisions D-1 to D-16 in §12 are
taken; the eight questions after them carry recommendations that are the
defaults, and a different answer from ember changes the section each names.

## Packages ready after a named lane lands

- **T1 clusters** (after `t1/codec-seam`): the BP-receiver cluster, the
  stx/identity/lace cluster, and the frame/anchor/transfer-journal cluster
  converted to include the seam books instead of the codecs, each with the
  three controls the T1 row demands (golden vectors byte-equal before and
  after; the certify wall of a named invariants book before and after with
  `uptime` beside it; `theory_check --table` counts). The seam's constraint
  names come from the T1 lane's report and
  `planning/evidence/codec-seam-2026-09-22.md`. Three lanes on disjoint
  books; persvati and hbox. 2 to 3 lane-days each.
- **T2a, the acceptance stamp** (after T1): `specs/acceptance-stamp.md` §2.1
  to §2.5 and §6, the four callers the design found, the seam exporting the
  magic and the schema octet. Books in the plan's T2a row. 5 to 7 lane-days;
  the plan says Fable, and a Codex lane that takes it reports the
  measurement, not a feeling. T2b (NEWNEWS over the stamp) follows it.
- **T3 and T4** (after T1 and, for T4, T2a): the article match into
  `books/store-node` with its four host lines, and `fn-sn-finish` proved per
  arm with the retention and identity arms stated positively and
  `fn-sn-finish-preserves-indexedp` unconditional. T4's brief also reads the
  eight Store event-order commits on `w25/bp-obligation-vertical` against
  the commutative contract in the BP spec's §10 and marks each integrated
  or unnecessary by name (nothing is marked until then).
- **T16a** (after `t5/sweep`): K0 `fn-bs-program-step-preserves-relation`
  over the frontier, record, finish and recover programs, then K5, K6, K8,
  with the campaign rerun on the developer image (the served owner is armed
  since `bb0affe6`; the driver is
  `tests/campaign/native_operator_campaign.py`).
- **T8b** (after T2a and T4): the live node adopts a new domain and
  capacity, so a group created live is served before any restart;
  `V0-CFG-LIVE` is the row that measures it.
- **T9b** (after `t13/conform`, which edits `peer-inbound`): inbound
  octets and the peer-row round trip.
- **T10a** (after the stx cluster conversion): signatures the node side.

## What root keeps

Merging every batch behind the lane's own certification and
`green_check --changed-since`; one provisional wave every two or three
batches; the freeze, the image, the deploy on hbox, the probe, the matrix,
the campaign and the INN lab on each image; the node's page; the plan and
the registries' hygiene; the dialogue with gpt-6 on the BP contract
(`design-dialogue-2026-09-23-bp-2.md` is the open one).
