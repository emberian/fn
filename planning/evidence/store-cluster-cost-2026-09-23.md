# Why the store cluster took 727 s, and the repair (lane COST-store, 2026-09-23)

Branch `cost/store` from `dev` 549c750a. The diagnosis below was read from
existing certify logs. No slow form was rerun on the farm. The repairs were
found in `tools/proof_repl.py` sessions on the Mac. The sessions included the
books below the cluster from `~/.cache/fn-certs`. `store-files`,
`store-files-invariants`, `replay` and `hybrid-store` had no cached pair at
these digests, so the sessions loaded them uncertified, and the cluster's own
books were loaded from source. The one exception is `store-node`'s
`verify-guards fn-sn-finish`: it was loaded once unchanged before the
repair, and that measurement is in the table below.

## The logs

| log (persvati) | book | book time |
|---|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260923T000250Z-1473169/books--store-node.certify.log` | store-node | 306.6 s |
| same run, `books--store-node-invariants.certify.log` | store-node-invariants | 311.3 s |
| same run, `books--store-node-traces.certify.log` | store-node-traces | 109.0 s |
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/books--store-node.certify.log` | store-node, `dev` head | 372.7 s |
| same run, `books--store-node-invariants.certify.log` | store-node-invariants, `dev` head | 307.6 s |

The `dev`-head run did not reach store-node-traces. The seam run is the
manifest `certify-20260923T000250Z-1473169`. The event times below come
from its logs. In the `dev`-head logs the same events have the same step
counts, so the proofs are the same and only the wall time differs.

## The slow events

| book | event | time | prover steps | subgoals | share of book |
|---|---|---|---|---|---|
| store-node | `(verify-guards fn-sn-finish)` | 304.9 s | 23 446 180 | 5 744, split at `Goal'` | 99.5% |
| store-node-invariants | `fn-sn-finish-preserves-indexedp` | 118.8 s | 50 771 771 | 13 734; `Goal''` split 5 249 ways, deepest `Subgoal 4667.101.81` | 38% |
| store-node-invariants | `fn-snt-prepare-that-stages-advances-by-one` | 95.4 s | 31 114 442 | 672; `Goal'` split 336 ways | 31% |
| store-node-invariants | `fn-snt-prepared-durable-is-idle-at-successor` | 60.3 s | 21 228 400 | 8; `Goal''` split 4 ways | 19% |
| store-node-invariants | `fn-snt-prepared-abort-is-frontier-advance` | 29.3 s | 9 966 577 | 3 | 9% |
| store-node-traces | `fn-snt-prepare-retention-preserves-relation` | 50.6 s | 38 544 678 | 12 | 46% |
| store-node-traces | `fn-snt-record-directory-preserves-relation` | 34.2 s | 20 181 660 | 9 110; `Goal''` split 286 ways | 31% |
| store-node-traces | `fn-snt-prepare-identity-preserves-relation` | 10.9 s | 10 772 447 | 115 | 10% |
| store-node-traces | `fn-snt-prepare-preserves-relation` | 4.6 s | 3 928 114 | 19 | 4% |

In store-node-invariants the four named theorems take 303.8 s of 311.3 s
(97.6%). None of these proofs used induction (no `*1/` subgoal names). None
had a forcing round, and no subgoal name repeats, so there was no rewrite
loop. Each cost comes from one case split, and the log's splitter note
names the definitions that caused it.

## What each proof opened

**`(verify-guards fn-sn-finish)`** (store-node). The guard conjecture asks
for type facts only: `fn-node-statep` of the node, `true-listp` of the
completion record on the identity arm, `fn-sf-statep` of the kernel step,
`fn-lace-p` of the delta, and `fn-prin-keyringp` of the keyring. Each of
these follows from `fn-sn-statep`, from a forward-chaining shape rule, or
from `fn-sf-core-completion-preserves-state`. But the hypothesis
`fn-sn-completion-enabledp` is enabled at this point of the book, and so
are `fn-sn-record-bindsp`, the store-transaction recognizers and both
record vocabularies (enabled at the top of the book, line 19). The prover
unfolded the hypothesis into the whole completion gate and split 5 744 ways
at `Goal'`. The splitter names `fn-record-ascii-stringp`, `-groupsp`,
`-metadata-bytes-p`, `-msgidp`, `-nonempty-at-mostp`, `-octet-stringp`,
`fn-record-p`, `-payloadp`, `-shapep` and `-uint32p`, together with
`fn-replay-apply-retention-event`, `fn-retain-matching-releasep`,
`fn-sn-identity-context`, `fn-sn-record-bindsp`, `fn-stxa-p`, `fn-stxe-p`,
`fn-stxk-p` and `natp`. The `Rules:` list opens 47 definitions. None of the
facts the conjecture needs is inside the record codec.

**`fn-sn-finish-preserves-indexedp`** (store-node-invariants). This is the
cause the resolution study named. The hint enabled
`fn-sn-completion-enabledp` and `fn-sn-record-bindsp`, and `fn-sn-finish`
is enabled book-wide. The goal therefore dispatched on the finish arm with
the gate, the replay steps and the stx recognizers all open. The first
splitter note, at `Goal''` (5 249 subgoals), names
`fn-record-result-okp`, `fn-replay-apply-record`,
`fn-replay-composite-record`, `fn-sn-completion-enabledp`, `fn-sn-finish`,
`fn-sn-identity-context`, `fn-sn-record-bindsp`, `fn-stxa-p`, `fn-stxe-p`
and `fn-stxk-p`. Each identity case then split again, 54 to 108 ways, on
`fn-replay-identity-step`, `fn-sn-finish-identity`,
`fn-sn-composite-delta` and `fn-sn-keyring-snapshot-listp`. The `Rules:`
list opens 50 definitions, 17 of them from the record codec. The proof
needs three fields of the result on each arm: index, keyring, and the store
of the node.

**The three `fn-snt-prepare*` lemmas** (store-node-invariants). Each hint
enabled `fn-node-statep`, `fn-statep` and `fn-snx-core-definitions` (the
whole node-state recognizer and the acceptance core). The conclusions are
about one field (`next-txid`), or about four fields plus `fn-node-statep`,
and that last fact comes in by `:use` of
`fn-node-complete-preserves-state`. The prover rewrote the full recognizer
in every case: `fn-node-statep`, `fn-statep`, `fn-retain-statep`,
`fn-retain-admissiblep`, `fn-selection-validp`, `fn-fencedp`, and in the
durable lemma also `fn-article-listp`, `fn-node-binding-listp` and
`fn-retain-obligation-listp`. The durable lemma opens 54 definitions and
the abort lemma 30. Only 3 to 8 cases arose, but each cost 3 to 5 million
steps. The stages lemma split into 336 cases on the recognizer's `if`s. The
bodies of `fn-node-prepare`, `fn-accept-prepare` and `fn-accept-complete`
test `fn-statep` of the acceptance, so the recognizer does have to be
answered. It is answered by a single field fact, not by unfolding the
recognizer.

**store-node-traces.** The four slow theorems each state that one
transition preserves `fn-snt-relation`. They open the transition on
purpose. Their cost is per case (12 cases at 3.2 million steps each for the
retention arm), not a codec split. The log does not name the expensive
rules. The one instrumented run this lane allowed itself
(`accumulated-persistence` on a renamed copy of
`fn-snt-prepare-retention-preserves-relation`) did not reproduce the
original proof. The copy had to disable the original rule and the tau
system to avoid proving itself, and without tau it failed in 1.8 s. Its
frames therefore do not describe the certified proof. For what they show,
the largest useless consumers were `fn-sf-crash-imagep` (247 956 frames),
the two admissible-crash-image rewrites and
`fn-snt-replayed-node-idle-and-frontier`. This lane did not change these
proofs, and they remain open (see below).

## The repair

No theorem statement changed. No hypothesis was added, and nothing was
skipped.

1. **`books/store-node`: guard hints for `fn-sn-finish`.** The hint now
   also closes `fn-sn-completion-enabledp`, `fn-sn-record-bindsp`,
   `fn-sn-identity-context`, `fn-replay-identity-step`,
   `fn-replay-apply-retention-event`, `fn-replay-apply-record`,
   `fn-store-retention-event-p`, the three stx recognizers and both record
   vocabularies. The shape comes from the recognizers' `-forward-shape`
   rules. What was proved did not change: `verify-guards` computes the same
   conjecture, and only the path to it changed.
2. **`books/store-node`: the export disable** now also withdraws
   `fn-sn-prepare-retention`, `fn-sn-prepare-identity` and
   `fn-sn-identity-context`. These definitions postdate the list. Left
   enabled, they opened in every goal that dispatched on a store event (see
   the resolution study).
3. **`books/store-node-invariants`: a field lemma**,
   `fn-snx-node-state-acceptance-is-state` (local): `(fn-node-statep s)`
   implies `(fn-statep (fn-node-acceptance s))`. The three prepare lemmas
   now keep `fn-node-statep`, `fn-statep`, `fn-retain-admissiblep`,
   `fn-retain-admit` and `fn-selection-validp` closed. Their hints open the
   steps themselves (`fn-node-prepare`, `fn-accept-prepare`,
   `fn-node-complete`, `fn-accept-complete`, and `fn-clear-pending` or
   `fn-install-pending`) and instantiate the field lemma at the prepared
   node. `fn-state-pending` is no longer enabled in the two prepared-*
   hints. Opened, it becomes `(car (cddddr ...))`, and
   `fn-state-pending-of-fn-make-state` no longer matches.
4. **`books/store-node-invariants`: one lemma per finish arm** (local,
   `defthmd`, enabled only in the theorem's hint). The disabled branch
   needs no new lemma: `fn-sn-finish-disabled-is-no-op` (`:rule-classes
   nil`, already in the book) comes in by `:use`.
   `fn-sn-finish-retention-arm-keeps-the-store-and-index` and
   `fn-sn-finish-identity-arm-keeps-the-store-and-index` give index,
   keyring and node store unchanged on those arms.
   `fn-sn-finish-acceptance-arm-fields` gives the acceptance arm's index,
   keyring and node, and the `fn-node-pending-matchesp` fact that
   `fn-stx-durable-completion-is-an-acceptance` needs. Each arm lemma opens
   `fn-sn-finish` and `fn-sn-completion-enabledp` with the replay steps and
   the recognizers closed. `fn-sn-finish-preserves-indexedp` is then a
   `:cases` on the arm with `fn-sn-finish` closed. Its `:use` list is
   unchanged.
5. **What the export change costs downstream.** Hints that relied on the
   withdrawn definitions being enabled now name them.
   `fn-sn-finish-preserves-state` (invariants) enables
   `fn-sn-identity-context`, because the identity arm's snapshot list is
   read through it. In store-node-traces, the two `-preserves-state` and
   two `-preserves-relation` theorems of the deferred preparations enable
   the arm they are about. store-node-traces also puts
   `fn-sn-identity-context` back into its own book-local enable list. Its
   io-step proofs (the first to fail was
   `fn-snt-record-file-preserves-relation`) carry the context across
   `fn-sn-make-v2` by reading its two fields. This book's theory is
   therefore what it was before for that one definition.

## Session times (proof_repl, Mac)

| event | before (seam log, persvati) | after (session) |
|---|---|---|
| `(verify-guards fn-sn-finish)` | 304.9 s, 23 446 180 steps, 5 744 subgoals (298.1 s in the session before the change) | 0.02 s, 1 861 steps, 3 subgoals |
| `fn-sn-finish-preserves-indexedp` | 118.8 s, 50 771 771 steps, 13 734 subgoals | 0.04 s, 13 790 steps |
| `fn-snt-prepare-that-stages-advances-by-one` | 95.4 s, 31 114 442 steps | 0.01 s, 4 353 steps |
| `fn-snt-prepared-durable-is-idle-at-successor` | 60.3 s, 21 228 400 steps | 0.05 s, 44 147 steps |
| `fn-snt-prepared-abort-is-frontier-advance` | 29.3 s, 9 966 577 steps | 0.04 s, 33 065 steps |
| the four new lemmas together | none | under 0.1 s |
| store-node, every event | 306.6 s | 2.3 s (the largest event is the 1.5 s `include-book`) |
| store-node-invariants, every event | 311.3 s | 7.4 s (the largest single event is 1.5 s, an `include-book`) |
| store-node-traces, every event | 109.0 s | 82.2 s (unchanged proofs: the four slow theorems have the same step counts as the seam log) |
| store-node-resolution, every event | 886.2 s on the seam log, before T4's repair | 3.5 s |

A session admission is not a certificate. Certification is in the next
section.

## What this recertifies

The export change is in `books/store-node`, so every book that includes it
certifies again. That covers the whole store cluster (store-node-invariants,
-traces, -resolution, store-prepare-correspondence, store-observed and the
host books above them), and root's treewide run does that anyway. In sessions
against this branch, every form of each of the following books was admitted:
store-node-resolution, store-observed, store-sweep,
store-prepare-correspondence, checkpoint and byte-store-native-correspondence,
and the test books store-node-tests, store-node-index-tests and
store-node-traces-tests. Books further up were not checked here: the host
books, and `bp-ingress` and `bp-receiver-evolving-history-invariants`, which
belong to other lanes. None of them names the three withdrawn definitions
except `host/store-node-host.lisp`, which calls `fn-sn-prepare-retention` in
a function body. They are left to the treewide run.

## Certification

Submitted to persvati from this branch; the run id is recorded in the commit that follows.
