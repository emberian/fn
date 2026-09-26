# Consolidation: the catalog, the byte owner, the checkpoint schema, and the wave-5 briefs (2026-09-26)

Lane `lane/consolidation-design` (Fable), from dev `265d3242`, under D33 to D36
(`planning/decisions.md`, pending ember's confirmation) and gpt-6's
consolidation review (`planning/review-2026-09-26-gpt6-consolidation.md`).
Brief: `build/coordinator/queue/w5-consolidation-design.txt`. Registry: no
ids; a design, a prototype (`books/proto-catalog*.lisp`, section 3) and the
wave-5 briefs (`planning/briefs-wave5/w5-*.txt`, section 5). Ground truth
read from the tree at that revision: the books and host lines named below
are cited by name; `tools/current_view.py` finds the line.

**What this design decides.** One executable interface, the *committed event
catalog* over the *byte owner*, with the invariants the fourteen-field Store
tuple and the owner's view now carry as separate fields and re-establish by
comparison; one *PreparedCommit* that completes by token instead of a history
search; one *committed delta* that every projection consumes instead of two
worlds to compare; one *checkpoint storage schema* written by one resumable
pipeline that decides its resources before it allocates; and a *deletion map*
per abstraction, so that each wave-5 lane removes the path it replaces. The
logical model stays what it is (octet lists, histories, article collections);
each concrete representation enters through an abstract stobj whose
obligations are proved once (D27, D30). The prototype (section 3) settles
whether ACL2 8.7's `attach-stobj` lets the tree keep one interface with
several executable implementations without recertifying the interface's
dependents; the catalog slice is briefed on its answer.

**What it does not decide.** Nothing here is implemented beyond the
prototype. PKT-293 and PKT-167 (the records freeze: two views, the shared
transition) are still ember's; the catalog slice's brief assumes gpt-6's
answer (`planning/review-2026-09-26-gpt6-answers.md` section 1) and stops if
she overrules. D36's certificate and storage tier are hers (section 5.8).

## 0. The measured reasons, in one table

Every row is from `planning/performance-2026-09-26.md` (the ledger) or the
record named; the abstraction column is this design's.

| Cost the user or operator pays | Cause in the code | Abstraction that removes it |
| --- | --- | --- |
| POST 10.2 ms at N = 10,000, 2.25 MB consed; `fn-retain-known-id-scanp`, `fn-find-article`, `fn-acceptedp` walk the pins and articles (50 % of CPU) | the Message-ID decision is re-derived from the article list | catalog: Message-ID binding is a column (section 1.1) |
| completion walks the history from sequence 0 (`fn-ccar-seek`, books/owner-commit-carried.lisp) | the finish looks for the record that is completing | PreparedCommit: completion by token (1.3) |
| `fn-own-refresh` compares two article lists (`fn-gidx-refresh`, `fn-midx-refresh`, `fn-ctl-refresh-*`); `fn-served-make-conn-group-indexed` is 15.6 % of a POST's bytes (PKT-558) | derived state rediscovers the change | the committed delta (1.4) |
| OVER 40 rows 320 ms, 2,000 rows 17.7 s at 10,000 (`fn-gidx-find-number-entry` per number) | the group-number projection is a bucket list walked per lookup | catalog: group-number projection is an array (1.1) |
| sixteen bytes per retained octet; 5.55 GB live at 10,000 x 32 KiB; ARTICLE 3 MiB conses 571 MB; POST 3 MiB 1.94 GB | payloads are cons lists in the record, the acceptance state, the reply | the byte owner (1.2; the arena of rep-wave-d, behind the catalog) |
| checkpoint file 670 MB for 320 MB of payload (PKT-307, PKT-314); reopen from it 132 s at 19.3 GB; capture 54 s at N = 40,000 and linear in N (checkpoint-capture-stream section 5) | the file serializes the folds' accumulators (the records twice) as one encoded tree | the checkpoint schema (2.1) and the resumable pipeline (2.2) |
| the automatic capture held the whole file in the publication buffer (315 MB at 40,000, one byte per octet) | the plan encodes the whole tree before a segment is written | bounded batches and chunks (2.2) |
| `fnn-owner-name-list` splits LF-joined names; the feed flush fetches frames by index against a separate peer list; about thirty `f-put-global` mailboxes in host/owner-host.lisp | an interface shaped for an external bridge | typed results (section 4, adapter retirement) |

## 1. The interface: the committed event catalog over the byte owner

### 1.1 The catalog, `fn-cat`

**What it is.** One abstract stobj, `fn-cat`, whose *logical value* is the
committed history as the theorems already know it, and whose *executable* is
the indexed tables gpt-6 section 6 names. The logical value is a true list of
*held* records oldest first (sequence = position): a held record is today's
`fn-record-shapep` tuple with the payload field a handle into the byte owner
and the byte-derived facts beside it (gpt-6's answer, section 1: "a retained
record, containing a payload reference and byte-derived metadata"). The
abstraction relation `fn-cat$corr` states every cross-field invariant the
tables must keep against that list; it is established by the creator and
preserved by every export, which is what `defabsstobj` proves once and what
no served path executes (no whole-state revalidation on a served path,
AGENTS.md).

The held record (the retained view of PKT-293's two views; the wire record
`fn-record-p` is unchanged and remains the codec's domain):

```lisp
; books/catalog-record.lisp (new; the shape only)
(defun fn-held-p (h)                 ; the retained record
  ; the tuple of fn-record-shapep with
  ;   payload  = a natural (a handle into fn-arena), never an octet list;
  ;   facts    = (body-start body-lines control-target source-digest class)
  ;              computed once from the immutable bytes at intern;
  ;   context  = (verdict keyring-generation policy-generation)
  ;              the context-dependent facts, carried WITH their context.
  ...)
(defun fn-held-wire (h fn-arena)     ; materialize: the wire record
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-held-p h) (< (fn-held-payload h) (fn-arena-count fn-arena)))))
  (fn-record-with-payload h (fn-arena-payload (fn-held-payload h) fn-arena)))
```

The catalog's exports (logic over the held list `C`; exec over the tables
of `fn-cat$c`). Each line is `(name args) => value` with its `:logic` body;
the `:exec` names the table read.

```lisp
; books/catalog.lisp (new)
(defabsstobj fn-cat
  :foundation fn-cat$c
  :recognizer (fn-cat-p   :logic fn-cat$ap   :exec fn-cat$cp)     ; fn-cat$ap: a true list of fn-held-p
  :creator    (create-fn-cat :logic create-fn-cat$a :exec create-fn-cat$c)  ; nil
  :corr-fn fn-cat$corr
  :exports
  ((fn-cat-count        :logic (len C)                                :exec the count cell)
   (fn-cat-at seq       :logic (nth seq C)                            :exec the row: kind, txid, msgid, groups,
                                                                             handle, facts, context, provenance)
   (fn-cat-msgid-seqs msgid
                        :logic (fn-cat-seqs-for msgid C 0)            :exec a hash-table cell (equal) msgid -> seqs
                        ; the spec is fn-cei-article-records-for restated over sequences, history order
   (fn-cat-group-number group n
                        :logic (fn-cat-number-seq group n C)          :exec the group's number array
                        ; the spec is the fold fn-gidx-build's binding of local numbers
   (fn-cat-visible-at seq version
                        :logic (fn-cat-visible-fold seq version C)    :exec two cells: withdrawn-at, withdrawn-by
                        ; the spec is fn-ctl-refresh-visible's decision, as a versioned fact
   (fn-cat-verdict seq  :logic (fn-held-context (nth seq C))          :exec the context columns
   (fn-cat-total-octets :logic (fn-cat-octets-fold C)                 :exec one scalar
   (fn-cat-group-count group
                        :logic (fn-cat-group-fold group C)            :exec one scalar per group
   (fn-cat-commit h     :logic (append C (list h))                    :exec append the row, put the msgid,
                                                                             assign the numbers, advance the totals,
                                                                             decide initial visibility  :protect t)
   (fn-cat-withdraw target by
                        :logic (fn-cat-mark-withdrawn target by C)    :exec two cell writes                :protect t)
   (fn-cat-redecide seq verdict generation
                        :logic (fn-cat-with-context seq ... C)        :exec the context columns            :protect t)
   (fn-cat-clear        :logic nil                                    :exec counts := 0                    :protect t)
   (fn-cat-load-row ... :logic (append C (list h))                    :exec as commit, from the checkpoint  :protect t))
  :attachable t)
```

`fn-cat$corr`, the maintained cross-field invariant, is the conjunction the
Store tuple's derived fields carry today as separate relations, stated once:
the count is `(len C)`; row `seq` is `(nth seq C)`; the Message-ID table maps
each Message-ID to exactly the sequences of the article records with it, in
order (`fn-cei-correspondencep`'s content); each group's number array binds
the numbers `fn-gidx-build` would bind (the numbers are assigned at commit
and never reassigned, so the array is append-only); the visibility cells
agree with the fold of withdrawals over `C` (`fn-ctl-refresh-visible`,
`fn-ctl-refresh-withdrawals` as the reference); the scalars are the folds.
The existing relations `fn-ceis-indexedp` (books/consumer-event-index-store-
invariants.lisp), `fn-midx-correspondencep` and `fn-gidx-refresh-is-build`
are its ancestors and are retired by it (section 4).

**A signed composite keeps its outer binding atomic.** A kind-4 composite
(`fn-stxa-p`) commits ONE row: the composite event with its carried article's
Message-ID bound and its verdict in the context columns; `fn-cei-event-article`
today decodes the carried record once at put. The row's handle is the
composite's bytes; the carried article's facts are the row's facts.
`fn-cat-msgid-seqs` answers the composite's sequence; nothing splits it.

**Visibility and verdict are versioned facts.** A view is a *version*, the
catalog count at the moment the view was taken (`fn-own-conn-version` is
already that number): a pinned reader at version `v` sees rows `seq < v` and
a row withdrawn at `w` as visible when `v <= w`. No per-connection copy of the
article list; the pinned archive `fn-own-conn-archive` becomes the version.
Verdicts carry the generation they were decided under; `fn-cat-redecide`
(`keys redecide`, PRF-166) writes a new context without touching the row's
bytes or its binding.

### 1.2 The byte owner beneath it

The byte owner is the arena, `fn-arena` (books/payload-arena.lisp, PRF-118),
behind the catalog: no book above the catalog names it, and the catalog's
rows refer to it by handle. Its guarantees are the arena's keystones, cited
not restated: a sealed handle is immutable under every later seal
(`fn-arena-seals-keep-sealed`), a handle is never reused
(`fn-arena-seal-new-handle`, `fn-arena-seal-count`), nothing removes a
payload, and the relation with a history is the same after a commit's seal
and after an open's seals (`fn-arn-store-corr-of-commit`, `-of-open`).

What the design adds to it, each an interface obligation on the catalog
slice (section 5.2), none a change to the arena's logical value:

- **Immutable byte objects with identity, extent and lifetime.** A handle
  `h` denotes `(fn-arena-payload h)`, extent `(fn-arena-payload-len h)`; its
  lifetime is the process's: from its seal to the next open. A reference
  handed to a reader (a pinned view's rows) stays valid through publication,
  withdrawal, checkpointing and reclamation because none of them removes a
  payload; reclamation (D13) seals the tombstone as a new handle and
  rewrites the row's handle under the mutex; the old bytes are reclaimed at
  the next open, which rebuilds the arena from the retained rows
  (`fn-arn-store-corr-of-open`). A process-local handle is not a portable
  identity: a checkpoint carries file-local references (2.1) and a peer is
  told a Message-ID, never a handle.
- **Parsed byte facts** are decided at intern, once, from the immutable
  bytes: header/body boundary, body line count (OVER's `fn-nov-body-line-count`
  walks the whole body today), control target, source digest, representation
  class. They are byte-derived and carry no context.
- **Context-bound decisions** name their key or policy snapshot: the
  statement verdict `fn-stx-verdict-of-octets` is decided at intern under
  keyring generation `g` and stored as `(verdict . g)`; the theorem the
  slice owes is that between intern (the prepare) and the finish no
  transition changes the keyring (the phase gate: no other transaction
  between a prepare and its finish, `fn-sn-completion-enabledp`), or the
  finish re-decides under the finish's generation and stores that. An
  interned control target is sound; "this control may execute" is not
  cached without its authority context (`fn-owner-control-filing` decides
  at submit under the live configuration, and stays a decision, not a fact).
- **Local projections refer to the object**: numbers, visibility,
  obligations and indexes are catalog columns keyed by sequence, and the
  sequence names the handle. Nothing holds a second copy of the bytes.
- **Explicit lifetimes and bounded growth.** Pinned references are versions
  (1.1); the arena's chunked backing is the interface's business (a seal of
  a payload of any length is one range; the doubling array is amortized,
  not a latency bound: a paged arena is a later implementation behind the
  same `fn-arena$a-*` logic, which is what section 3's mechanism buys);
  eventual reclamation is the open's rebuild, never in place.
- **A checkpoint reference is interpreted within its checkpoint** (2.1).

The host boundary is unchanged in kind: the served POST fills the octet
buffer under the mutex (`fnn-owner-attempt`, host/native/owner.lisp; A-HOST),
the prepare reads it in place, and the finish seals it
(`fn-arena-seal-buffer`, the export with no caller today). The served
ARTICLE writes from the handle (`(:write-payload h kind)` as a reference
effect; the host copies the range into the socket, dot-stuffing decided by
ACL2 by index: egress-span's interface).

### 1.3 PreparedCommit, and completion by token

Today the in-flight submission is `fn-own-inflight` (`fn-own-sub-make id
version mark decision`, books/owner.lisp), the Store's pending record is
`fn-sf-record-candidate` and its completion pair `fn-sf-completion`
(sequence . txid); the finish `fn-ccar-own-finish` (host line:
host/owner-host.lisp `fn-owner-finish-submission`, called by
host/native/owner.lisp `fnn-owner-finish-submission` as the store's finish
callback) finds the record by walking `(car pair)` conses (`fn-ccar-seek`).
The catalog replaces that with one value the live execution state holds:

```lisp
; books/catalog-commit.lisp (new)
(defun fn-pc-make (token expected event plan delta reservation) ...)   ; PreparedCommit
;   token                the operation token: (txid . expected), unique per attempt
;                        (fn-owner-next-txid is consumed even on a known abort today)
;   expected             the expected predecessor: the catalog count at prepare; the
;                        record's sequence if it commits
;   event                the event reference: the held record h WITHOUT its handle yet
;                        (the payload is the octet buffer's range until the finish seals it),
;                        with its parsed facts and its intern-time context
;   plan                 the publication plan: the record file's frame as a buffer range
;                        (fn-owner-pending-octets today), the feed frames per peer
;                        (FeedPublication, section 4)
;   delta                the semantic delta the commit will emit (1.4), computed at prepare
;                        from expected and the catalog: the numbers, the binding, the
;                        initial visibility, the scalar deltas
;   reservation          the resource reservation: the charge and capacity vector reserved
;                        (fn-cvec, fn-smr, already made at prepare)

(defun fn-cat-prepare (wire fn-octets fn-arena fn-cat) => (mv prepared fn-cat)
  ; interns the wire record from the buffer: the facts from the bytes, the context under
  ; the current generation; reserves; records PREPARED as the one pending commit (the
  ; phase gate: at most one).  The catalog's logical value is unchanged.
(defun fn-cat-complete (token fn-octets fn-arena fn-cat) => (mv delta fn-arena fn-cat)
  ; TOKEN names the pending PreparedCommit or the call is refused by name (:stale-token);
  ; seals the buffer (fn-arena-seal-buffer), binds the handle into the event, appends the
  ; row at EXPECTED (fn-cat-commit), emits DELTA.  No search.
(defun fn-cat-abandon (token fn-cat) => fn-cat
  ; a known abort: releases the reservation, clears the pending commit; the buffer is
  ; garbage; nothing was sealed.
```

The host's contract (the adapter-retirement brief, section 5.3): the store
callback that today calls `fnn-owner-finish-submission` with no argument
carries the token the prepare returned; a stale callback (a retried attempt
whose token is not the pending one) cannot complete another operation.
Recovery still reconstructs from durable evidence: at open, a record file
present without its success marker is resolved as today
(`fn-sn-resolution`, `fn-store-sn-recover`), and its row is interned by the
open, not by a token. The normal path does not search history:
`fn-ccar-seek`, `fn-sn-find-record` and `fn-sn-completion-record` leave the
served path (section 4).

### 1.4 The committed delta, and what consumes it

`fn-cat-complete` emits the delta; every projection consumes it, and the
reference definition of what a projection is (the fold over the history) is
what the delta's application is proved equal to:

```lisp
; books/catalog-delta.lisp (new)
(defun fn-delta-p (d) ...)      ; (:article seq msgid groups+numbers handle initial-visibility verdict octets)
                                ; (:withdraw target by)               a cancel after its target
                                ; (:withdraw-pending msgid by)        a cancel before its target: the target's
                                ;                                     initial visibility will be withdrawn
                                ; (:redecide seq verdict generation)  a verdict under a new generation
                                ; (:policy generation from to)        a policy change touching rows [from, to):
                                ;                                     RESUMABLE, applied in bounded batches
                                ; (:retention ...) (:identity ...) (:consumer ...) (:topic ...) the other kinds
(defun fn-view-apply (view d) ...)               ; applyViewDelta for the owner's served view
(defun fn-view-apply-step (view d cursor quantum) => (mv view cursor done))   ; the resumable form
```

The theorem (the owner's view is the reference: `fn-own-view` of
`fn-own-refresh`, books/owner.lisp):

```lisp
(defthm fn-view-apply-is-refresh
  (implies (and (fn-cat-owner-relation o fn-cat fn-arena)               ; R, section 1.5
                (fn-own-store-idlep (fn-own-store o)))
           (equal (fn-view-apply (fn-own-view o) (fn-cat-delta-of (fn-own-store o) h))
                  (fn-own-view (fn-own-refresh (fn-own-with-store o (fn-sn-finish-held ...)))))))
```

The consumers, each one theorem of the same shape: the served view (above);
the group and Message-ID projections (they ARE catalog columns, so their
"consumption" is `fn-cat-commit`'s own correspondence); the consumer
projection (`fn-cpe-projection-step` on the row, not on the record list);
capacity accounting (`fn-cvec-debt-extend`: the octets delta); carriage
usage; the feed's obligation targets (`fn-own-submission-targets` reads the
prepared plan); configuration replay (the `:policy` delta with its range).

**The pinned view advances between commands** (the coordinator's input from
the NNTP inventory: a reader connection today keeps the view it opened with,
and only a poster's own connection advances after its post, so a long-lived
pan or Thunderbird session never sees a peer's new article until it
reconnects). A connection's view is its version `v` (1.1); GROUP and
LISTGROUP, between commands, advance the connection to the current count,
which is `fn-view-apply` over the deltas from `v` to the count (or, since
the view is a version, the assignment `v := count` and the theorem that the
rows a version sees are the fold's). C3's pinned-reader semantics are kept:
within a command the version is fixed, so a multi-line response is
consistent; it advances only at those two commands, never mid-response.
The cancel-after-target case is what makes this visible: an article the
reader listed at `v` and a cancel committed at `w > v` leave the article
visible to that reader until it advances past `w`.

### 1.5 The maintained relation R(C, S), its entries, and what preserves it

```lisp
; books/catalog-relation.lisp (new)
(defun-nx fn-cat-owner-relation (o fn-cat fn-arena)
  ; R(C, S): alpha(C, A) = the old logical Store S of the owner O, i.e.
  (and (fn-cat-p fn-cat) (fn-arena-p fn-arena)
       (fn-arn-store-corr fn-arena (fn-sf-records (fn-sn-files (fn-own-store o))))   ; the arena is the payloads
       (equal (fn-held-wire-all fn-cat fn-arena)                                     ; each row materialized
              (fn-sf-records (fn-sn-files (fn-own-store o))))                        ; is the history
       (fn-own-relation o)))                                                         ; the owner's own
```

The step obligation, per export that mutates, in the form gpt-6 section 3
gives: `R(C,S) ∧ step_c(C,e) = (C',E_c) ⟹ R(C',S') ∧ ⟦E_c⟧ = ⟦E_s⟧`, where
`step_s` is the reference transition (`fn-sn-finish`, `fn-own-step` on the
event) and `⟦E_c⟧` is the delta's meaning (1.4) against the reference's
effects (`fn-own-refresh`'s view, the served reply octets):

| Export (step_c) | Reference (step_s) | The effect equation |
| --- | --- | --- |
| `fn-cat-complete` | `fn-sn-finish` then `fn-own-complete` | `fn-view-apply-is-refresh` (1.4) |
| `fn-cat-withdraw` | `fn-ctl-refresh-withdrawals` at the first publish of the cancel | the same theorem, `:withdraw` case |
| `fn-cat-redecide` | `fn-owner-key-statement-redecide-*` (PRF-166) | the served `HDR :fn-verified` reads the new context |
| `fn-cat-prepare`, `-abandon` | `fn-sn-prepare`, `fn-sn-refuse`/known abort | the logical value is unchanged; the reservation equals the Store's |
| the served read (ARTICLE, OVER, HEAD by number or Message-ID) | `fn-scar-ocfg-read-tls-prefix` (the reference effect) | the bytes written from the handle equal `fn-served-reply-octets` of the reference effects (egress-span's keystone shape) |

**Where R is established (every actual entry).**

1. *Fresh install* (`init`, host/native/io.lisp `fnn-command-init`): the
   creator; `create-fn-cat{correspondence}` and the empty arena;
   `fn-arn-store-corr` of nil. No migration exists (D34): this is the only
   fresh entry.
2. *Open from the journal* (`fnn-recover` → `fn-store-sn-recover`, the
   K0 recovery program `fn-bs-recover-program`): each record decoded from
   its file is interned and `fn-cat-load-row`'d in order; the theorem is
   `fn-arn-store-corr-of-open`'s shape over rows: the fold of loads from the
   empty catalog over the decoded history satisfies R against the replayed
   Store (`fn-sn-recover`'s result).
3. *Open from a checkpoint* (`fnn-recover-from-state-checkpoint` →
   `fnn-state-checkpoint-load` → `fn-store-sco-decode`): section 2.3's
   theorem: loading the file's tables yields (C, A) with alpha(C, A) equal
   to the capture's Store, then the suffix is loaded as in 2.
4. *Recovery after a cut* (the same two entries; `fn-bs-recover-program-keeps-relation-at-every-cut`
   for the byte store, and the resolution of a pending record): the row is
   interned at open; R does not depend on the pending commit.

**Which exported operations preserve it.** Every `:protect t` export of
`fn-cat` (its `{correspondence}` and `{preserved}` obligations), composed
with the transition it stands for by the table above; the arena's seals
(`fn-arn-store-corr-of-commit`). The reads preserve it trivially. The
checkpoint capture (2.2) reads only. Reclamation seals the tombstone and
rewrites the handle: `fn-arn-store-corr` is restated for a history whose
payload is the tombstone (the reclaim kernel's `fn-rcl-tombstone-of` reads
the bytes by handle once; the digest is a parsed fact after this design).

### 1.6 What remains as the reference model only

Kept, as specification: `fn-sf-records` (the history as a list),
`fn-record-p` over the wire record and the codec seam (unchanged, it is the
codec's domain), `fn-cei-article-records-for` and `fn-cei-build` (the
Message-ID binding's specification), `fn-gidx-build` (the local numbers'),
`fn-ctl-refresh-visible` and `fn-ctl-refresh-withdrawals` (visibility's),
`fn-own-refresh` (the delta's meaning), `fn-sn-finish` over wire records
(the reference transition), `fn-sn-find-record` (the completion's meaning),
`fn-sco-capture` (what the checkpoint tables mean, section 2.3). Removed
from execution, with their `-carried` twins once the catalog serves the
path: section 4.

## 2. The checkpoint schema, and the one resumable pipeline

### 2.1 The schema: tables, not a serialized tree

Today's file (`store-checkpoint.fnsc`, schema 2, books/store-checkpoint-
codec.lisp) is one postfix program over the checkpoint VALUE, the 7-tuple
`(fn-sco-make records cpr identity consumer topic event-index)` frozen by
`fn-sco-freeze`: the folds' accumulators, which hold every payload twice
(the configuration fold's node and the event index: PKT-307, PKT-314; 670 MB
for 320 MB of payload). The schema replaces the value with four tables, each
its own run of segments in the same FNSC frame (header 37 octets: magic,
schema **3**, index, count, length, sequence; chunk; trailer sealed over the
previous trailer, header and chunk; `fn-scc-decode-segments`'s refusals of
reorder, truncation, splice and corruption are kept) so that the reader's
admission per segment (`fn-sccr-admit-segment`, PRF-135) and the crash
program (2.4) are unchanged:

| Table | One row per | Columns | Written from |
| --- | --- | --- | --- |
| **P**, immutable payload extents | payload object | file-local index `p`, extent (offset, length) into the P byte run, the bytes | the arena's byte array, range by range, in handle order; a payload appears ONCE, whichever rows refer to it (a composite and its carried article share none today; a reclaimed tombstone is its own object) |
| **E**, committed event metadata | committed event (sequence) | kind, txid, generation, stamp, provenance, charge, Message-ID, groups and their local numbers, the payload reference as a file-local `p` (never a process's handle), the parsed facts, the context (verdict, generation), visibility (withdrawn-at, withdrawn-by) | the catalog's rows, in sequence order; a non-article event is its metadata row with no `p` |
| **R**, projection roots | fold | the configuration fold paused at S (`fn-sco-cpr-prefix`'s pause WITHOUT the node's record list: the node's article entries are (sequence . p) references into E and P), the identity context (`fn-stxk-*`), the consumer projection cursor, the topic prefix state, the per-group counts and the scalar totals, the group-number arrays' lengths | the folds' accumulators as today, with every record list replaced by a sequence range |
| **F**, provenance and frontier | file | schema 3, the store identity, S (the count covered), the frontier txid, the keyring generation and the policy generation in force at S, the profile generation, the writer's source revision, the count of segments per table, the digest chain's genesis | the owner's carried state |

**Reopening equals the intended replay.** The reader loads P into the arena
(one copy, `fn-arena-seal-*` per extent, in index order, so file-local `p`
becomes handle `p` in the fresh arena: the translation is the identity on a
fresh arena and is stated as such, never assumed for a live one), E into the
catalog (`fn-cat-load-row` per row, the handle translated), R and F into
the owner's carried state; then the suffix is replayed from the journal as
today. Shared objects are represented once; no semantic history is
compacted (every event of S is a row; the file removes no record, as
STO-011 says).

**Sizing without serializing.** Each E row's encoded size is a column
advanced at commit (`encodedSize_v(r)` as a stored number, gpt-6 section 6),
so the file's length is a sum of scalars the catalog already carries plus
the arena's fill: the estimate is O(1), where `fn-ockb-file-len` walks the
whole tree at each publication (54 s at N = 40,000, linear in N).

### 2.2 The pipeline: one, resumable, for the automatic publication and the verb

```
capture a stable root  →  enumerate bounded batches  →  encode bounded chunks
       →  publish and validate  →  install / select  →  release the pins
```

1. **Capture a stable root** (under the mutex, O(1)): the count S, the
   arena fill at S, the roots R and the frontier F, and a *pin* on S (the
   catalog is append-only and the arena is append-only, so rows `< S` and
   bytes below the fill are immutable while the capture runs; the pin
   records that a publication is in progress for the operator and for the
   stop). Today `fn-owner-sco-capture` hands the publication thread the
   live record LIST (shared, not copied) and the thread extends and freezes
   a tree; under the schema it hands four numbers.
2. **Enumerate bounded batches**: rows `[i, i + B)` of E, and for P the
   extents those rows reference; B from the profile (a work bound per
   step, D27), so a batch's rows and bytes are bounded by B and B x R.
3. **Encode bounded chunks**: a batch into the publication buffer
   (`fn-octets-pub`, the congruent stobj of checkpoint-capture-stream), at
   most SEG octets per segment; P's bytes copied range by range from the
   arena into the buffer (a new export, `fn-octets-append-arena-range`, or
   the host's `fnn-octets-append-vector` at the same A-HOST boundary). The
   buffer's residency is SEG, never the file: today `fn-sccb-plan` encodes
   the WHOLE file into the buffer before the first write (315 MB at
   N = 40,000).
4. **Publish and validate**: each segment written through the staged file
   (`fnn-write-staged-at`, between the `created` and `written` cuts), its
   trailer chained; validation is the reader's admission of the segment
   just written (`fn-sccr-admit-segment` over its header and the running
   total) before the next batch: a file the open would refuse is never
   completed.
5. **Install / select**: the rename over the name and the root fsync
   (`fn-bs-scp-program`'s last two steps), then `fn-sco-select` at the next
   open decides as today (S at most the count, suffix at most K).
6. **Release the pins**: `fn-owner-sco-publication-done` under the mutex,
   as today; a deferred or failed publication releases the same way.

**The resource decision, before allocation.** Before step 3 allocates
anything: the estimate (2.1, O(1)) against (a) the profile's checkpoint
budget (`fn-ock-capture-budget`, STO-024, kept), (b) the execution-memory
budget of the publication buffer, which is SEG (one segment) and so a
constant of the profile, not of N, and (c) the space the staged file needs
plus the maintenance reserve (`fn-smr`, `statvfs` through the capacity
vector's assumption). When it cannot proceed the owner retains the prior
checkpoint and the journal, reports by name (`CHECKPOINT deferred
reason=exceeds-budget|exceeds-space estimate=E budget=B`, `status` carries
it: STO-024's words, one more reason), and applies the **recovery-resource
contract's backpressure**: the profile declares H (max-history-octets), K
(max-open-suffix) and R (max-record-octets); a deferred publication means
the next open replays at most the suffix since the last durable checkpoint,
which the profile bounds by H, and the owner's due path stays blocked until
the budget covers the estimate (`fn-ock-publication-blockedp`, kept). A
temporary budget is never a semantic maximum: no article is refused for it;
the fatal heap ceiling of the 32,000 MiB launcher (PKT-016) is not reached
by a publication whose residency is SEG.

**Resumable.** A batch is a step: between batches the publication thread
yields (it holds no lock), and the verb (`store checkpoint`, the same
pipeline over the same functions, in a fresh process with the store lock)
does the same. A stop during a capture leaves a staged file the next open's
`fn-bs-recover-stage-cleanup-program` sweeps; a resume is a new capture
(the pins say nothing durable), which is the honest form until a partial
file is worth keeping.

### 2.3 The theorem: reopening equals the intended replay

The existing keystone chain is kept and re-targeted: `fn-sccb-plan-is-file-
octets` (PRF-133) and `fn-sccr-decode-of-plan` (PRF-135) become theorems
about the table codec (`fn-sct-*`, new): the plan of the four tables over
the buffer, per batch, concatenated, is the file the table codec specifies,
and the reader's decode of it is the tables. The new keystone:

```lisp
(defthm fn-sct-load-of-publish-is-the-capture
  (implies (fn-cat-owner-relation o fn-cat fn-arena)                          ; R at the capture
           (let ((loaded (fn-sct-load (fn-sct-file fn-cat fn-arena roots frontier batch seg))))
             (equal (fn-sco-capture-of-loaded loaded)                          ; the value the open installs
                    (fn-sco-capture configs (fn-sf-records (fn-sn-files (fn-own-store o))))))))
```

so `fn-sn-recover-from-checkpoint-equals-full-recover` (checkpoint-cost) and
`fn-sco-open`'s theorems transfer unchanged: the loaded tables ARE the
capture of the committed prefix, and the open over the suffix is the full
open. `fn-sco-capture` stays as the specification of what the tables mean
(1.6); `fn-sco-freeze`/`-thaw` and `fn-sco-index-records` go (section 4).

### 2.4 The crash points, mapped

The file write is `fn-bs-scp-program` (books/byte-store-state-checkpoint-
program.lisp: create, cut `state-checkpoint-created`, write-all, cut
`-written`, fsync, cut `-staged-durable`, rename, cut `-replaced`, fsync-dir,
cut `-durable`; keystone `fn-bs-scp-program-crash-is-old-or-new`;
`tests/campaign/native_cuts.py` STATE_CHECKPOINT_CUTS old/old/old/either/new;
`tools/native_program_check.py` over six programs). The pipeline writes many
segments between the `created` and `written` cuts, as the host already does
(`fnn-plan-write-all` loops inside `fnn-write-staged-at`, checkpoint-capture-
stream section 1), and the model's `:write-all` is the host's loop of writes
torn at unit granularity (byte-store crash model v2). So: **no new program
and no new cut.** The brief for the pipeline (5.1) requires
`native_program_check` PASS with the same six programs and
`verify_state_checkpoint_cut_map` unchanged, and one new native case: a kill
between two segments reopens with the OLD checkpoint (the `created` cut's
verdict) and the staged file is swept. The verb's five cuts through both
entries (`tests.test_native_state_checkpoint`) stay the module for the batch.

## 3. The attach-stobj prototype: what worked, what the tooling needed, what it saves

**The mechanism** (ACL2 8.7, the tree's `w25/acl2-literal` and the laptop's
Homebrew 8.7_6; `:DOC attach-stobj`, `:DOC attachable-stobjs`, and the
distribution's `books/demos/attach-stobj/` and `books/system/tests/
attachable-stobjs/`, read): an abstract stobj introduced with `:attachable
t` is a *generic*; `(attach-stobj gen impl)`, evaluated after `impl` (an
abstract stobj with the same :logic functions positionally, and the same
recognizer and creator logic) and before `gen` is introduced, makes `gen`'s
foundation and every export's executable `impl`'s. There is no indirection
in raw Lisp (each primitive macroexpands to the attachment's :exec); a
function defined at `include-book` time that calls a generic's primitive is
compiled then instead of loaded from the book's compiled file. The
logical world is identical with or without the attachment, so a theorem
proved over the generic is proved for every implementation.

**The prototype** (`books/proto-catalog.lisp`, `proto-catalog-fold.lisp`,
`proto-catalog-arena.lisp`, `tests/acl2/proto-catalog-tests.lisp`;
`docs/prefixes.md` `fn-pcat-`):

- `fn-pcat` is the generic: its :logic side is the ARENA's, verbatim
  (`fn-arena$ap`, `create-fn-arena$a`, the seven `fn-arena$a-*`), so that
  `fn-arena` (books/payload-arena.lisp, the byte array with an offset and a
  size per handle) is a legal attachment; its own foundation `fn-pcat$c`
  is one field holding the payload list, every export a list operation.
  Its obligations (`{correspondence}`, `{preserved}`, `{guard-thm}` per
  export, as `defabsstobj-missing-events` prints them) are the trivial
  ones of "the field is the value"; the opened view restates the arena's
  (`fn-pcat-seal-list-is-append`, ...).
- `proto-catalog-fold` is the consumer, the shape of every book above the
  catalog: `fn-pcat-seal-many` (a seal per record: the open) and
  `fn-pcat-total` (the octets below a handle: a scalar), with
  `fn-pcat-seal-many-keeps-sealed` (a pinned handle reads the same after
  the fold; the arena's keystone over the generic's names) and
  `fn-pcat-total-of-seal-is-delta` (the total after a seal is the old
  total plus the delta, without a walk), both hypothesis-free but for the
  handle's bounds. Guard-verified; the test book runs the exec path on a
  live local generic and gives each theorem its witness and its
  `must-fail` per hypothesis.
- `proto-catalog-arena` is the attachment: `(include-book "payload-arena")`,
  `(attach-stobj fn-pcat fn-arena)`, `(include-book "proto-catalog")`,
  `(include-book "proto-catalog-fold")`, then at certification time
  `fn-pcat-smoke` over the live generic (three seals, the total, two
  reads), which printed `(3 5 (4 5) 3)` and is asserted.

**What worked.** Everything the mechanism promises, measured on the
certification logs (laptop, `tools/certify_books.py` under the pool; then
persvati farm run `run-20260926T181951Z-fa12`, ACL2 8.7, 2 jobs, 300 s:
passed 4, failed 0, 5 installed from the cache, no book over 10 s; manifest
`planning/evidence/manifests/certify-20260926T182020Z-744871.json`):

1. `fn-pcat`'s `defabsstobj ... :attachable t` over another book's :logic
   functions was admitted with its obligations (0.1 s).
2. The fold book was certified ONCE, against the generic (its certificate
   is the generic's world).
3. `proto-catalog-arena`'s `(include-book "proto-catalog-fold")` under the
   attachment was accepted from that certificate in 0.01 s: **no
   recertification of the interface's dependents**; the fold's functions
   were recompiled at include time (silently, as the manual says) and ran
   over the arena's foundation, giving the same value.
4. The attachment book's own certificate (5.7 KB) records the fold as a
   dependency; the fold's certificate is byte-identical before and after
   the attachment book existed.
5. The developer and production images (hbox, `tools/hbox_native.sh
   --images developer,production`, build.lisp including
   `books/proto-catalog-arena`) built: `fn-host-developer.core`
   `02aecbde060b1c33…`, `fn-host.core` `8fd89db7a64dcdde…` (the first run,
   whose module failed on two harness faults: the smoke verb's argument
   protocol and a source test that matched the comment; both repaired; the
   second run's line is below).
6. The second run (hbox `native-proto2`, the tree at `7ff27724`; developer
   core `030b3c3dd8299617…`, production core `6bff486d5f4c1b31…`; log
   `test-tests.test_native_proto_catalog.log` `023e1ca87928c2c0…`, both
   under `/tank/fn/scratch/consolidation-design/native-proto2/`):
   `tests.test_native_proto_catalog` OK, 3 ran, 0 skipped. The developer
   image's `fn proto-catalog smoke` prints
   `proto-catalog count=3 total=5 payload1=(4 5) get02=3 foundation=arena fields=5`:
   the values are ACL2's (`fn-pcat-smoke`), and the live `fn-pcat` object
   is the arena's concrete stobj (five fields: buf, off, size, count,
   fill), not the generic's own (one field). The production image does
   not register the verb (exit 5, nothing printed).

**What the certificate tooling needed.** Nothing new: the four books are
ordinary Makefile roots; `tools/certify_books.py` and `farm.py` certified
them with the cache installing `payload-arena` and its closure; the cache
key is the include closure, and the fold's closure does not contain the
attachment book, so its cached pair is reused under the attachment. Two
findings for the catalog slice: `assert-event` over a live stobj needs
`:stobjs-out '(nil st)` and a form returning `(mv bool st)`; and a
registered developer verb takes `(command rest)` with two words required
(`fn proto-catalog smoke`).

**Whether the substitution avoided recertifying the interface's
dependents.** Yes: point 3. The rule the tree gains (packet P-B, section
6): a representation is an implementation ATTACHED to a generic whose
:logic side is the model; the books above the generic are certified once;
choosing the implementation is one `attach-stobj` event in the image's
include order (host/native/build.lisp), and a second implementation (a
paged arena, a hash-table Message-ID index, the list-backed reference for
a test book) costs its own obligations and no recertification above it.
This is the form the catalog (`fn-cat`, section 1.1) and the byte owner
take. What it does not buy: the books that thread the stobj as a formal
still name it (the catalog's own books do; nothing above them must), and
`:protect` and `:congruent-to` come from the attachment (the generic's
declarations are overridden: state the intended ones on the
implementation).

## 4. The deletion map

gpt-6 section 10: a deletion map per abstraction, so that each lane removes
what it replaces. Host lines are function names in the file named
(`tools/current_view.py` finds the line; a number never goes into a book).
"Measurements" are the figures that prove the whole path improved, each
taken under matched conditions on the same box and image pair, before and
after, over the whole lifetime: load, sustained posting, repeated
checkpointing, reopen, reclamation (the ledger's harness,
`planning/evidence/perf-ledger-2026-09-26/perf.py`, and `tools/rep_measure.py`).

### 4.1 The catalog `fn-cat` (1.1)

| Replaces | Callers that move (host line) | Old execution paths removed | Reference definitions kept (spec only) |
| --- | --- | --- | --- |
| the Store's derived event index `fn-sn-event-index` (the triple SEQUENCE-TRIE, MSGID-TRIE, COUNT; `fn-cei-*`) and its relation `fn-ceis-indexedp`; the owner view's `fn-own-view-index` (`fn-midx-*` trie), `fn-own-view-group-index` (`fn-gidx-*` buckets), `fn-own-view-withdrawals`, `-withdrawn`, `-raw`, `-verdicts`; the Store tuple's fields 6 (index), 8 (verdicts), 9 (snapshots) | `fn-owner-prepare-buffer`, `fn-owner-existing-action-buffer`, `fn-owner-finish-submission`, `fn-owner-recover`, `-recover-from-checkpoint`, `-recover-extended`, `fn-owner-sco-capture`, `fn-owner-article-count` (host/owner-host.lisp); `fn-store-sn-recover`, `fn-store-sco-decode` (host/store-node-host.lisp); the served reads under `fn-owner-chunk` (`fn-scar-*` → `fn-gidx-entry-number-article`, `fn-nntp-msgid-retrieval-indexed`) | `fn-retain-known-id-scanp`, `fn-rclb-existing-action`'s `fn-find-article`, `fn-acceptedp` on POST (ledger row 5); `fn-gidx-find-number-entry` and `fn-nntp-index-entry-available` per OVER row (row 1, 7); `fn-served-make-conn-group-indexed` per POST (PKT-558); `fn-sbud-count`'s `len` of the history; the `fn-ceis-*` preservation books (31 theorems) once `fn-cat$corr` carries their content | `fn-sf-records`; `fn-cei-article-records-for`, `fn-cei-build`; `fn-gidx-build`; `fn-ctl-refresh-visible`, `-withdrawals`; `fn-sn-finish` over wire records |

Measurements: records visited per POST (N to 1), per OVER row (N to 1),
per completion (seq to 0); allocated bytes per POST (2.25 MB at 10,000 to
the row's size); OVER 40 rows (320 ms) and 2,000 rows (17.7 s) at 10,000
and 20,000 to O(rows); proof fan-out: the books that include
consumer-event-index* and msgid-index* (count by `make affected`) become
includers of catalog*.

### 4.2 The byte owner (1.2; the arena of rep-wave-d)

| Replaces | Callers that move | Removed | Kept |
| --- | --- | --- | --- |
| the octet-list payload in the record (`fn-record-payload` of the held record), the acceptance state's `fn-article-payload` and `fn-pending-payload`, the in-flight `fn-own-sub-octets`, the served reply as a list (`fn-nntp-crlf-lines-aux`, `fn-ag-rev-onto`), the frame's payload copy (`fn-frame-protected`) | `fnn-owner-attempt` (host/native/owner.lisp: the fill, unchanged) and the finish (the seal); `fnn-owner-handle-chunk`'s reply write (the range from the handle: egress-span's seam); `fn-store-sn-recover` (decode then intern); the checkpoint reader (2.1); `fn-rcl-tombstone-of` (reclaim, by handle); later `fn-owner-feed-sealed-frame` and `bp-service` (the feed and BP read by handle when they build a bundle) | `fnn-octet-list` per payload call; `fn-record-payloadp`'s per-octet walk on the served path (the held record's payload is `natp`); `fn-nov-body-line-count`'s walk per OVER (a parsed fact); the tree codec's payload copies; `fn-arena-payload` as an escape hatch once no caller needs the list | `fn-record-p` over the wire record; the codec seam (`fn-record-encode`/`-decode-exact`, unchanged); the arena's own logical value |

Measurements: retained bytes per octet (16 to 1: 5.55 GB live at
10,000 x 32 KiB to about 0.6 GB); transient peak of a 3 MiB ARTICLE (571 MB
consed to O(1) beyond the socket copy) and POST (1.94 GB); lock-hold time
per ARTICLE (0.9 s owner CPU at 3 MiB to the copy); reopen from the journal
(164 s, 22.5 GB at 10,000 x 32 KiB); the heap census after a full GC on the
loaded owner (`heap.lisp`).

### 4.3 PreparedCommit and completion by token (1.3)

| Replaces | Callers that move | Removed | Kept |
| --- | --- | --- | --- |
| `fn-own-inflight` + `fn-sf-record-candidate` + `fn-sf-completion`'s (sequence . txid) pair as the way the finish finds its record; the store callback pair `*fnn-finish-callback*`/`fnn-owner-finish-submission` with no argument | `fn-owner-finish-submission`, `fn-owner-refuse-reservation`, `fn-owner-known-abort`, `fn-owner-pending-octets`, `fn-owner-pending-sequence` (host/owner-host.lisp); `fnn-owner-attempt`, `fnn-owner-finish-submission` (host/native/owner.lisp): the token threads through the attempt | `fn-ccar-seek`, `fn-sn-completion-record`, `fn-sn-find-record` on the served path; the `fn-ccar-*` and `fn-pcar-*` equality chains once the catalog serves the path (each was a twin of one lookup) | `fn-sn-find-record` as the meaning of "the completing record"; `fn-sf-*`'s kernel and its K0 programs (the record file's program is unchanged) |

Measurements: records visited per completion (the sequence's conses to
0); owner CPU per commit at N = 10,000 and 20,000 (the ledger's POST row).

### 4.4 The committed delta (1.4)

| Replaces | Callers that move | Removed | Kept |
| --- | --- | --- | --- |
| `fn-own-refresh` and its two-list comparisons `fn-gidx-refresh`, `fn-midx-refresh`, `fn-ctl-refresh-withdrawals`, `-visible`, `-withdrawn`; the per-connection pinned archive copy `fn-own-conn-archive` | `fn-own-complete`, `fn-own-store-step` (books/owner.lisp: the view applies the delta the commit returns); `fn-own-open` and the greeting (the view is a version); GROUP and LISTGROUP (`fn-nntp-*` group selection: the version advances between commands, C3 kept) | the refresh's rediscovery; the greeting's view copy; `fn-served-make-conn-group-indexed` | `fn-own-refresh` as the meaning of the delta (`fn-view-apply-is-refresh`) |

Measurements: bytes consed per POST from the refresh (1.4 % now) and
from the per-connection index (15.6 %); a long-lived reader session sees a
peer's article after its next GROUP (the inventory's finding), measured as
the number of commands to visibility (unbounded to 1).

### 4.5 The checkpoint schema and pipeline (2)

| Replaces | Callers that move | Removed | Kept |
| --- | --- | --- | --- |
| the 7-tuple checkpoint value (`fn-sco-make`), `fn-sco-freeze`/`-thaw`, `fn-sco-index-records`; the tree codec `fn-scc-*` (postfix program over an ACL2 tree), `fn-sccb-plan`'s whole-file encode and `fn-sccr-*`'s tree decode; `fn-ockb-file-len`'s walk; `fn-ock-publication` (the list entry, already superseded) | `fnn-owner-publish-captured`, `fnn-owner-maybe-publish` (host/native/owner.lisp); `fnn-command-state-checkpoint`, `fnn-state-checkpoint-plan`, `-load`, `fnn-recover-from-state-checkpoint` (host/native/io.lisp); `fn-store-sco-publish-plan`, `-decode`, `-segment-admit`, `fn-owner-sco-capture`, `-publication-done` (the host wrappers) | the records twice in the file (PKT-307, PKT-314); the whole-tree walks per publication (three, each linear in N); the whole-file buffer residency; the decode's second copy at open | `fn-sco-capture` as what the tables mean; `fn-sco-open`, `fn-sn-recover-from-checkpoint-equals-full-recover`; `fn-bs-scp-program` and its five cuts; the FNSC frame and the reader's admission per segment |

Measurements: file octets per payload octet (670 MB for 320 MB to about
1.05); capture wall and its growth with N (2.6 s at 2,131 to 54 s at
39,996, linear, to O(N) rows of metadata plus one memcpy per extent, so
seconds); VmHWM across nineteen captures (5.55 GB at 40,000 x 2 KiB);
reopen from the checkpoint (132 s, 19.3 GB at 10,000 x 32 KiB); the
publication buffer's residency (315 MB to SEG); the verb's wall at the
ledger's points.

### 4.6 Adapter retirement (gpt-6 section 7)

| Replaces | Callers that move | Removed | Kept |
| --- | --- | --- | --- |
| `fnn-owner-name-list` (LF-joined names split in raw Lisp); the feed flush's frame-by-index fetch against a separate peer list (`fnn-owner-feed-flush`: `fn-owner-feed-record-peers` then `fn-owner-feed-sealed-frame index`); the `f-put-global` mailboxes of host/owner-host.lisp (`fn-owner-output`, `-closep`, `-starttlsp`, `-submittedp`, `-effects`, `-submit-id/-msgid/-octets/-groups/-intent/-transitp/-peer`, `-feed-records/-frames/-command/-command-status/-peer`, `-sco-base/-durable/-attempted/-deferred`, `-config-octets/-reason`, `-log-line`, `-record-octets/-debt`, `-carried-usage`, about thirty) read back by `fnn-global`; `fn-owner-config-names` | every `fnn-owner-*-global` and `fnn-global` reader in host/native/owner.lisp, feed-service.lisp, pull-service.lisp; `fnn-owner-drain-one`, `fnn-owner-complete-bound-submission`, `fnn-owner-feed-flush`, `fnn-owner-publish-captured`, `fnn-owner-serve-client` | the name-list grammar; the by-index fetch; the mailbox reads; `fnn-owner-octets-global`; history-search completion (4.3); refresh-by-rediscovery (4.4) | ACL2 constructs every value; the adapter executes it |

The typed results (ACL2 values the wrapper returns, one per step, each a
`fn-*-p` shape with a recognizer the host checks once): `FeedPublication
{peer_reference, sealed_frame_plan, completion_token}`; `SubmissionTaken
{id, msgid, octets-range, groups, intent, transitp, peer}`; `ServedStep
{reply-range, closep, starttlsp, submittedp, log-line}`; `Capture {count,
fill, roots, frontier, budget}`; `ConfigResult {octets, reason}`. Text is
rendered at the CLI and log boundaries only; bytes are encoded at the wire
and storage boundaries only; no global result mailboxes.

Measurements: allocation per POST from the join/split; the mutex-held time
per feed flush and per served step (the served step's I/O runs outside the
critical section where the contract permits: gpt-6 section 7's second
paragraph: one mutation owner, bounded semantic steps, immutable read
plans against pinned versions, I/O consuming plans).

### 4.7 D34, D35, D36 (the non-catalog lanes)

| Abstraction | Replaces | Removed | Kept |
| --- | --- | --- | --- |
| one store format, fresh deploys (D34) | the format-7 translation `fn-bs-profile-from-format-7` and `*fn-bs-meta-format-7-*` (books/byte-store-frame.lisp), `upgrade-profile`'s upgrade relation (`fn-profile-upgrade-verdict`, books/store-profile-upgrade.lisp; `fnn-command-upgrade-profile`, `fnn-upgrade-profile-write`, host/native/io.lisp), `rollback-check` and `rollback-snapshot` (`fnn-command-rollback-check`, `-rollback-snapshot`; `fn-native-operator-history-*`), `needs-upgrade`, the versioned release directories and `packaging/upgrade-native.sh`, docs/operator.md "Upgrade, and what a rollback loses" | the two format-7 presets as store frames; `tests.test_native_profile_upgrade`, `test_native_rollback_history`, `test_native_stamp_migration`, `test_native_newnews_migration`, `test_native_history_required`'s migrate arm, `PROFILE_CUTS` (byte-store-profile-program) | `store export` / `store import` (new: the exact committed records and the profile, as a portable archive the codec seam defines; the import is an `init` plus a replay); the profile fields and their validation |
| the release is the product (D35) | the developer's checkout as the deployment; Python on the node | `tools/*.py` from the runpath (a check: `tools/runpath_check.py`, lane release-openbsd) | `packaging/release-tarball.sh` per platform; `packaging/install-native.sh` |
| a public node (D36) | the LAN-only node | | the exposure limits (PRF-161), the certificate and tier from ember |

## 5. The wave-5 briefs

Eight briefs, in gpt-6's order, in `planning/briefs-wave5/` (the coordinator
copies them to `build/coordinator/queue/`). Each names its model, its
user-visible result, its base, what to read, its ordered task, its
maintained relation with its entries, its witnesses, the native modules for
the batch, its fixtures, its envelope, the id blocks it needs, and its
deletion map (section 4's row). Their seams:

| # | Brief | Model | Owns | Waits on | Seam |
| --- | --- | --- | --- | --- | --- |
| 1 | `w5-checkpoint-pipeline` | Fable | books/store-checkpoint-tables*, the pipeline over `fn-octets-pub`, the resource decision; host: the four checkpoint entries | nothing (the schema over today's record shape: P holds the list payloads' bytes, E rows reference them; the catalog slice re-targets E's loader) | hands the catalog slice `fn-sct-load` over rows; hands egress/ingress nothing |
| 2 | `w5-catalog-slice` | Fable | books/catalog*, catalog-record, catalog-commit, catalog-delta, catalog-relation; the arena behind them; host: prepare, finish, existing-action, recover, the served reads by number and Message-ID | ember's D33 and PKT-293 (gpt-6's answer assumed); brief 1 merged (the loader) | absorbs `w3-rep-wave-d-4`; egress-span's reply range reads the handle; ingress-span's span is the buffer range the prepare interns |
| 3 | `w5-adapter-retirement` | Opus | host/native/owner.lisp, feed-service, pull-service; host/owner-host.lisp's wrappers; books/owner-results (the typed shapes) | brief 2's token and delta (or lands first with the shapes over today's values: the brief says which) | keeps the mutex discipline; egress-span's writer |
| 4 | `w5-bp-catalog` | Opus | the BP receipt/obligation rows as catalog kinds; bp-native-app's reads by handle | brief 2 | bp-lifecycle's records |
| 5 | `w5-config-consumer-catalog` | Opus | the configuration checkpoint (PKT-510) as roots; the consumer projection as a delta consumer | brief 1 (roots), brief 2 (delta) | caps-to-profile-2's PRF-186 folds |
| 6 | `w5-migration-removal` | Opus | D34's removals; `store export/import` | ember's D34 | release-product's tarball |
| 7 | `w5-release-product` | Opus | D35: the tarballs, the runpath check, docs for a stranger | lane release-openbsd's findings | migration-removal (no upgrade verb in the docs) |
| 8 | `w5-public-node` | Opus | D36: fn.fg-goose.online | ember's certificate and tier | release-product's tarball; the exposure limits |

## 6. The assurance chain, and what needs ember

**The chain for the slice** (BRIEF-COMMON's form), as the briefs state it:
native entry (`fnn-owner-attempt`, `fnn-owner-finish-submission`,
`fnn-recover`, `fnn-owner-publish-captured`, `fnn-owner-handle-chunk`) →
executed ACL2 subject over the representation (`fn-cat-prepare`,
`fn-cat-complete`, `fn-cat-load-row`, `fn-sct-file`, the served read from
the handle) → refinement (`fn-cat$corr` and `fn-arena$corr`, proved once
per export; `fn-held-wire` as alpha) → maintained relation
(`fn-cat-owner-relation`, established at the four entries of 1.5, preserved
by the `:protect` exports) → behavioural theorems (`fn-view-apply-is-refresh`,
`fn-sct-load-of-publish-is-the-capture`, the served bytes' equation) →
observed result (the native modules per brief, the ledger's rows re-measured).

**Decisions for ember** (packets the deputy numbers at merge; each with
trace, constraints, default, rejected alternative, what continues without
it):

- **P-A, D33's confirmation and PKT-293 with it.** Default: gpt-6's answer
  (two views, shared transition, intern-time facts in two classes); the
  catalog slice is briefed on it and stops if overruled. Rejected: the
  global `natp` freeze (rep-wave-d-2 section 1's finding). Without it: the
  pipeline lane (1) still lands over today's record shape.
- **P-B, the attach-stobj mechanism as the tree's rule for representations**
  (section 3's finding). Default: adopt; a representation is an
  implementation attached to a generic whose logical side is the model,
  and the tree's books above the generic never recertify for a new
  implementation. Rejected: the hundred-book arena-threading approach
  (rep-wave-d section 2 (c)); the `mbe` freeze per leaf (a recertification
  of the closure per representation). Without it: the catalog slice threads
  `fn-cat` as a formal through its own new books only, which is what it
  does anyway; the saving is on the NEXT implementation (a paged arena, a
  hash-table Message-ID index).
- **P-C, the delta log versus versions for pinned views.** Default:
  versions (1.1: a view is a count; withdrawals and verdicts are versioned
  facts), no per-connection copy and no delta log to bound. Rejected: a
  bounded delta log per connection (a data bound). Without it: the served
  view keeps its copy and `fn-own-refresh` stays until the slice's second
  step.
- **P-D, one store format until v1 (D34): `store export/import`'s scope.**
  Default: the exact committed records and the profile; identity and
  consumer state come with them because they are records; feed journals
  and BP spools are not exported (a reinstall re-peers). Rejected: an
  in-place format bump with a reader for both. Without it: the node keeps
  `upgrade-profile` and the rollback verbs, and the release carries the
  upgrade docs.
- **P-E, D36's certificate and storage tier**: hers; the brief lists what
  the node needs from her (5.8).
