# Handoff: w12/bp-sequence — durable BP creation-sequence frontier

Commits `f3807ae`, `84e857e`, `d2daed1`, `b11d24c`, and `5241c22`, based on
`8b474e2`.

`bp send` and reply authoring no longer accept an operator sequence.  The
native host takes the exclusive `sequence/frontier.lock`, asks ACL2 to recover
and reserve, writes ACL2's FNBS frame for `(:bpn-sequence successor)` through
a staged replacement, fsyncs the sequence directory, and only then calls
`fn-bpn-host-send` with the reserved value.  W12 proves the local reservation
successor transition and exercises the native ordering; it does not yet prove
nonreuse over persistence and crash traces.

## Public W12 boundary

`books/bp-node-records.lisp` owns one FNBS v1 kind, code 1: `:sequence` with
one `:nat` field (the next frontier).  Its public model calls are:

* `fn-bpn-sequence-recover(octets presentp freshp)` returning `(:ready n)` or
  a distinct `(:fault reason)`;
* `fn-bpn-sequence-reserve(frontier)` returning `(:reserved n
  (:bpn-sequence n+1))` or `(:refused :sequence-exhausted)`;
* ACL2 framing/unframing and `fn-bpn-sequence-frame-limit`.

The matching `fn-bpn-host-sequence-*` wrappers are the only sequence calls in
`host/native/bp.lisp`.  The allocation domain is both `fn-bpp-timep` and the
FNBS `:nat` domain; `fn-bpn-sequence-reserve-advances-frontier` is the proven
transition for every frontier below `*fn-bpc-max-uint*`.

An absent file means a zero frontier only when `freshp` says the sequence
namespace was just created and parent-published.  BP explicitly fsyncs the
journal root's parent and the sequence directory's parent on every path,
including recovery of already existing directories; it does not rely on
`fnn-safe-directory`'s creation-only parent barrier.  Once that
namespace existed, an absent frontier is `:sequence-frontier-missing`; a
malformed present file is `:sequence-frontier`; each becomes native
indeterminate.  This relies on the filesystem's documented file-and-directory
barrier behavior and on configuration authority treating a newly published
journal root as a new node.  It does not prove a storage device's power-loss
semantics or distinguish external destructive deletion from a new configured
node.

## FNBS extension reservation

Codes 2, 3 and 4 are reserved for W13's lifecycle `:queued`, `:attempting`
and `:result` records; 5 is reserved for a future checkpoint.  They must add
ACL2 schemas and computed bounds before any host writes them.  W12's sequence
record carries no queue, contact, attempt, receipt or lifecycle state.

## Evidence

Local ACL2 8.7: `FN_ACL2=/opt/homebrew/bin/acl2 python3
tools/certify_books.py --jobs 1 books/bp-node-records
tests/acl2/bp-node-records-tests` passed, evidence
`certify-20260921T063641Z-88877`.

Persvati `/home/ember/fn-lanes/w12-bp-sequence`, jobs 4:

* `run-20260921T063659Z-7e21`, `--closure books/frame-journal
  books/bp-node-records tests/acl2/bp-node-records-tests`: exit 0, evidence
`certify-20260921T063702Z-478487`.
* `run-20260921T063925Z-a7f1`, `--closure books/bp-node
  books/bp-node-records`: exit 0, retained for the native image prerequisite.

The certified DTN image build initially correctly refused unrelated uncertified direct
dependencies.  The artifact-set packet then supplied the declared `dtn`
runtime union: persvati run `run-20260921T065324Z-17f8`, jobs 4, exit 0;
`tools/proof_artifacts.py acquire --profile dtn` selected one 103-book set
(`b0f61318acac7c2f`) and ACL2 load-checked it.  The resulting certified
`build/fn-host-dtn` is a 259M core.

The source-pinned native transcript is
[`bp-sequence-native-2026-09-21.md`](../evidence/bp-sequence-native-2026-09-21.md).
It records the root-parent failure injection, retry, sequence progression and
corrupt-frontier recovery.  Its scope is native ordering under the stated
filesystem barrier assumption.

## Persistence-cut trace packet

`books/bp-sequence-persistence.lisp` is a separate executable ACL2 model of
the host cuts between an ACL2 successor decision and authoring: journal-root
parent barrier, sequence-parent barrier, staged record, final-name publication,
sequence-directory barrier, and authoring.  `:process-restart` and
`:power-loss` are distinct observations.  Both discard unbarriered state; a
stage/name cut fences, while a directory-barriered successor retains its
advanced frontier and abandons the pending author.  The latter power-loss
projection assumes the filesystem honours the file and directory fsync
barriers.

The keystone `fn-bpn-sp-trace-authored-sequences-unique` proves that every
finite event trace from the initial state has distinct authored sequence
values.  Its test book has reachable author-before-barrier failures, a failed
root-parent barrier/retry witness, and process/power restart witnesses.  The
native map is deliberately narrow: `fnn-bp-journal-dir` supplies the root
parent barrier; `fnn-bp-sequence-dir` supplies the sequence parent barrier;
`fnn-write-staged`, `fnn-replace`, and `fnn-fsync-dir` supply stage, name, and
directory cuts; reservation return is the only point that may author.  The
fault environment `FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER=1` is the failed root
barrier witness.  W13 lifecycle persistence has its own kinds and still needs
the explicit composition correspondence; this theorem does not establish
nonreuse for queue/lifecycle records, destructive deletion, or storage
hardware outside the stated fsync assumption.

Local ACL2 8.7 passed:

```sh
FN_ACL2=/opt/homebrew/bin/acl2 python3 tools/certify_books.py --jobs 1 \
  books/bp-sequence-persistence tests/acl2/bp-sequence-persistence-tests
```

with source-pinned manifest `certify-20260921T073850Z-38156.json`.  Persvati
then passed the declared closure at `/home/ember/fn-lanes/w12-bp-sequence`:

```sh
python3 tools/farm.py submit persvati --jobs 4 --closure \
  --remote-root /home/ember/fn-lanes/w12-bp-sequence \
  books/bp-sequence-persistence tests/acl2/bp-sequence-persistence-tests
```

Farm run `run-20260921T073923Z-0cb4` exited 0; its source-pinned closure
manifest is `certify-20260921T073927Z-1075245.json`.
