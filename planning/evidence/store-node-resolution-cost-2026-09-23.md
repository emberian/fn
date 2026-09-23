# Why `store-node-resolution` took 1748 s, and the repair (lane T4-snr, 2026-09-23)

Branch `t4/snr` from `dev` 9a659682. The diagnosis was read from existing
certify logs; the slow forms were not rerun. The repair was tried in one
`tools/proof_repl.py` session on the Mac against the cached closure at `dev`'s
digests (49 books installed from `~/.cache/fn-certs`, none missing).

## The logs

| log (persvati) | what it is |
|---|---|
| `/home/ember/fn-gates/t1-seam/build/acl2/certify-20260922T232746Z-1148619/books--store-node-resolution.certify.log` | seam branch, complete run: book 886.2 s |
| `/home/ember/fn-gates/t13-conform/build/acl2/certify-20260922T225718Z-866045/books--store-node-resolution.certify.log` | `dev` content at jobs 4: the first slow theorem alone took 900.1 s; the copy ends inside the second one's subgoal list |
| `/home/ember/fn-gates/t13-conform/build/acl2/certify-20260922T225718Z-866045/books--store-node-invariants.certify.log` | neighbour, book 376.4 s |

## Event times, seam log (book total 886.2 s over 55 events)

| event | time | prover steps | subgoals |
|---|---|---|---|
| `fn-snrt-step-success-history-monotone` | 466.0 s | 30 536 557 | 21 394 split at `Goal` |
| `fn-snrt-step-records-prefix` | 415.8 s | 38 751 844 | 21 393 split at `Goal''` |
| `fn-sn-known-abort-preserves-relation` | 1.9 s | | |
| `fn-sn-refuse-reservation-preserves-relation` | 1.1 s | | |
| the other 51 events | under 0.8 s together | | |

The two theorems account for 881.8 s of 886.2 s (99.5%). In the `dev` run
at jobs 4 the first of them took 900.1 s by itself, so the 1748 s figure
is the same two proofs slowed by contention.

## What the prover did

Both proofs have the same shape. The subgoal names are flat (`Subgoal 21394`
down to `Subgoal 1`, some with one prime). No `*1/` names appear, so there
was no induction. No subgoal name repeats, so there was no rewrite loop.
There were no forcing rounds. The whole cost is one case split at the top
of the proof, and the log's splitter note names the rules that caused it:

```
Splitter note (see :DOC splitter) for Goal (21394 subgoals).
  if-intro: FN-RECORD-ASCII-STRINGP FN-RECORD-MSGIDP FN-RECORD-NONEMPTY-AT-MOSTP
            FN-RECORD-RESULT-OKP FN-RECORD-UINT32P FN-REPLAY-APPLY-IDENTITY-NEUTRAL
            FN-REPLAY-APPLY-RECORD FN-REPLAY-APPLY-RETENTION-EVENT
            FN-REPLAY-COMPOSITE-RECORD FN-RETAIN-MATCHING-RELEASEP
            FN-SN-IDENTITY-CONTEXT FN-SN-PREPARE-IDENTITY FN-SN-PREPARE-RETENTION
            FN-SNRT-STEP FN-STXA-P FN-STXE-P FN-STXK-P NATP
```

The `Rules:` summary of each theorem opens 45 definitions. They fall into four groups:

- **Record codec:** `fn-record-ascii-stringp`, `-msgidp`, `-nonempty-at-mostp`,
  `-result-okp`, `-result-record`, `-uint32p`, `-string-octets`, and the
  accessors `-txid`, `-generation`, `-msgid`, `-payload`, `-groups`,
  `-charge`, `-content-subject`, `-obligation-id`, `-release-evidence`, and
  `fn-cbor-ag-car`.
- **Replay steps:** `fn-replay-apply-record`,
  `-apply-retention-event`, `-apply-identity-neutral`, `-composite-record`,
  `-complete-retention`, `-identity-advance`, `-identity-step`, and
  `-node-with-retention`.
- **Store-transaction recognizers and context:** `fn-stxa-p`, `fn-stxe-p`,
  `fn-stxk-p`, and `fn-stxk-context-*`.
- **The two deferred preparations:** `fn-sn-prepare-retention`,
  `fn-sn-prepare-identity`, and `fn-sn-identity-context`.

The rewrite rules that settled each proof were the footprint lemmas:
`fn-sn-{refuse-reservation,known-abort}-cannot-acknowledge`,
`fn-snt-step-success-history-monotone` and `fn-sf-prefixp-reflexive`, or
for records `fn-snrt-{refuse,known-abort}-keeps-records` and
`fn-sf-records-of-prepare-record`. The prepare arms' own footprint lemmas
never fired. `fn-sn-prepare-{retention,identity}-cannot-acknowledge` are
proved earlier in this book and enabled, but they are missing from the
`Rules:` list.

## Cause

`fn-snrt-step` dispatches on `(car event)`. The two arms that `6ab2c783` and
`4bb7bb3d` added, `:prepare-retention` and `:prepare-identity`, call
`fn-sn-prepare-retention` and `fn-sn-prepare-identity`. Both definitions are
still **enabled** at this point. `books/store-node`'s export `in-theory
(disable ...)` (line 768) closes the older sibling `fn-sn-prepare` but was
never extended to these two. ACL2 rewrites inside out. It therefore expands
`(fn-sn-prepare-retention s (cadr event))` before the outer
`(fn-sf-successes (fn-sn-files ...))` term could match the arm's
`-cannot-acknowledge` rule. The expansion carries the whole entry gate of
the arm:

- `fn-store-retention-event-p`;
- `(consp (fn-replay-apply-retention-event ...))`;
- `fn-stxe-p`, `fn-stxk-p` and `fn-stxa-p`;
- `(consp (fn-replay-apply-record ...))`;
- `fn-replay-identity-step` over `fn-sn-identity-context`.

The record codec is also open, because line 6 enables
`fn-record-codec-vocabulary` book-wide (the pattern of review F3). The
recognizers therefore unfold to their fields, and every `if` among them
becomes a case. The goal only needed to know which arm it was in and that
the arm leaves successes and records alone. Instead the prover split on the
inside of the codec, about 21 000 times, and then proved each case by the
same footprint rewrite it could have applied once. This is the shape named
in the brief: a kind-dispatch goal that carries a whole codec and whole
recognizers open. It matches none of the other candidate causes: no
induction on the wrong measure, no loop, no free-variable `:use`, no
forcing.

## Repair

The shape fact each proof needs already exists as its own lemma, so nothing
new is proved:

- `fn-sn-prepare-retention-cannot-acknowledge` and
  `fn-sn-prepare-identity-cannot-acknowledge` (this book) state that the arm
  leaves `fn-sf-successes` equal.
- `fn-snt-prepare-retention-keeps-records` and
  `fn-snt-prepare-identity-keeps-records` (books/store-node-traces, withdrawn
  on export under `fn-store-node-traces-vocabulary`) state that the arm
  leaves `fn-sf-records` equal.

The change, all below the includes:

1. The section-level `local` disable that opens the mixed-trace section now
   also closes `fn-sn-prepare-retention` and `fn-sn-prepare-identity`, with
   a comment giving the reason. The other theorems in the section already
   disabled both by hand: `fn-snrt-step-preserves-relation` and
   `fn-snrt-new-success-is-actual-matching-durable-completion`.
2. The hint of `fn-snrt-step-records-prefix` enables the two withdrawn
   `-keeps-records` lemmas. The success-history theorem's hint is unchanged.

No theorem statement changed. No hypothesis was added. Nothing was skipped.
The proofs still consider all five arms. Each now closes by the arm's
footprint lemma instead of by unfolding the arm.

## Session times (proof_repl, Mac, cached closure)

| event | before (seam log) | after (session) |
|---|---|---|
| `fn-snrt-step-success-history-monotone` | 466.0 s, 30 536 557 steps, 21 394 subgoals | 0.01 s, 537 steps, 5 subgoals |
| `fn-snrt-step-records-prefix` | 415.8 s, 38 751 844 steps, 21 393 subgoals | 0.01 s, 823 steps |
| every event of the book, loaded through `fn-snrt-mixed-trace-records-prefix` | 886.2 s | 7.6 s (the largest single event: 1.4 s, an `include-book`) |

After the fix the `Rules:` list of each theorem is `fn-snrt-step`, `not`,
the four or five footprint rewrites, `fn-sf-prefixp-reflexive` and two type
prescriptions. The splitter names only `fn-snrt-step`.

## The neighbours (from the t13 `store-node-invariants` log; not changed here)

| theorem | time | steps | split | opened |
|---|---|---|---|---|
| `fn-sn-finish-preserves-indexedp` | 144.7 s | 49 289 939 | 12 852 subgoals, `Goal''` split 4808 ways, deepest `Subgoal 4226.101.81` | 48 defs, if-intro `fn-replay-apply-record`, `-composite-record`, `-identity-step`, `fn-sn-finish`, `-finish-identity`, `-identity-context`, `fn-stxa-p`/`-e-p`/`-k-p`, `fn-sn-record-bindsp`, `fn-sn-completion-enabledp` |
| `fn-snt-prepare-that-stages-advances-by-one` | 112.8 s | 31 071 451 | 336 cases at `Goal'` | its hint enables `fn-node-statep`, `fn-statep`, `fn-snx-core-definitions`; if-intro `fn-node-statep`, `fn-statep`, `fn-retain-statep`, `fn-retain-admissiblep`, `fn-selection-validp`, `fn-fencedp` |
| `fn-snt-prepared-durable-is-idle-at-successor` | 74.7 s | 21 228 309 | 4 cases | 54 defs, including the whole node recognizer: `fn-node-statep`, `fn-statep`, `fn-retain-statep`, `fn-article-listp`, `fn-node-binding-listp`, `fn-retain-obligation-listp`, ... |
| `fn-snt-prepared-abort-is-frontier-advance` | 36.4 s | 9 966 551 | 3 cases | 30 defs, same recognizer family |

- **`fn-sn-finish-preserves-indexedp`** has the same cause as this book in
  a different place. The goal dispatches on the finish arm (article,
  retention or identity). The hint opens `fn-sn-record-bindsp` and
  `fn-sn-completion-enabledp`, and the codec and replay steps come open with
  them, so the arm split multiplies through the replay step's case
  structure. The repair would be one lemma per arm: the finish result on
  each arm, stated with `fn-replay-apply-record` and the stx recognizers
  closed. The theorem would then be a `:cases` on the arm with each case
  closed by its lemma.
- **The three `fn-snt-prepare*` / `fn-snt-prepared-*` lemmas** have a
  related cause but not the same one. Each hint explicitly enables
  `fn-node-statep` and `fn-statep`, the whole-node-state recognizers,
  together with `fn-snx-core-definitions`. The conclusion is about one or
  two fields: `next-txid`, `stage`, `pending`, `fenced`. The case count is
  small (3 to 336), but each case rewrites the full recognizer (10 to 31
  million steps). The repair would be to state the field facts of
  `fn-node-prepare` and `fn-node-complete` as lemmas: next-txid after
  prepare, and stage, pending and fenced after complete. The recognizer
  would stay closed, reached through `fn-node-complete-preserves-state`.
  Only `prepared-durable-is-idle-at-successor` concludes `fn-node-statep`,
  and it already `:use`s that lemma.

These theorems are in `store-node-invariants`, not this book, so they are
left for a lane that owns that book. The same root fact would help all of
them: `books/store-node`'s export disable should close
`fn-sn-prepare-retention`, `fn-sn-prepare-identity` and
`fn-sn-identity-context` as it closes `fn-sn-prepare`. That change is low in
the graph and recertifies the whole store cluster, so it belongs to root's
treewide run rather than to a lane.

## Certification: not submitted

The farm refused the lane run before ACL2 started. `farm.py submit persvati`
with plain roots (`books/store-node-resolution`,
`tests/acl2/store-node-resolution-tests`,
`tests/acl2/store-node-resolution-traces-tests`, `--jobs 4
--timeout-seconds 1800 --remote-root /home/ember/fn-gates/t4-snr --acl2
/home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache`) answered "no origin/toolchain-coherent certificate
set ... Re-run with --closure". 24 books of this book's closure have no pair
in `/home/ember/fn-certcache` at `dev` 9a659682's digests:

- `principal`, `provenance`, `records`, `records-invariants`, `replay`,
  `retention`, `retention-invariants`, `statement`, `statement-invariants`;
- `store-events`, `store-files`, `store-files-invariants`,
  `store-files-traces`, `store-node`, `store-node-invariants`,
  `store-node-traces`;
- `stx-accept-records`, `stx-carrier`, `stx-evidence-records`, `stx-index`,
  `stx-keyring-records`, `stx-lace`, `stx-verify`, `wildmat`.

Under `planning/how-we-work.md`, "Certification cost", a lane does not
`--closure`, so this lane stopped there. The run waits on root's treewide
certification of `dev`'s head on persvati. After that, the plain-roots
submit above is the whole gate.

`--affected-by books/store-node-resolution` fails separately, in the cache
preflight. It expands to `host/native-auth-host`,
`host/native-auth-admin-host` and `host/native-operator-host`, and
`certify_books.py` refuses those names ("book names must be
repository-relative paths below books/ or tests/acl2/"). That is a
`tools/farm.py` defect, and it is not repaired here.
