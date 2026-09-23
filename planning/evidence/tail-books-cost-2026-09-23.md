# The unowned tail: nntp-auth, byte-store-relation, tcpcl-invariants and feed-events' export (lane COST-tail, 2026-09-23)

Branch `cost/tail` from `dev` a432b7c2. The diagnosis comes from certify
logs already on persvati. The repairs were tried in `tools/proof_repl.py`
sessions on the Mac against the cached closure, one session per book. Every
fix is a hint, a disable, or a local lemma. No theorem statement changed and
no theorem was removed. Session times are the Mac's and certify-log times are
persvati's at 16 jobs, so compare the two columns within a row and not across
rows. The farm run named at the end is the certification.

## The logs

| log (persvati) | books |
|---|---|
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T015321Z-2477288/` (manifest `planning/evidence/manifests/certify-20260923T015321Z-2477288.json`, the second incremental run of dev's head) | `books--nntp-auth`, `books--byte-store-relation`, `books--feed-events`, and for the export `books--feed-totality`, `books--owner-feed-port`, `books--feed-correspondence` |
| `/home/ember/fn-gates/dev-head/build/acl2/certify-20260923T003741Z-1790068/` (the stopped treewide run; the incremental run installed this book from the cache and did not recertify it) | `books--tcpcl-invariants` |

For each event, the tables give the `Summary` time, the prover steps, the
subgoals printed, the largest splitter note and the `:DEFINITION` runes from
`Rules:`. No forcing round appears in any of the four books.

## books/byte-store-relation: 12.3 s, now 2.2 s in the session

| event | log | steps | subgoals | defs | splitters |
|---|---|---|---|---|---|
| `include-book "byte-store-scan"` | 2.80 s | | | | |
| `fn-bs-first-frontier-program-preserves-relation` | 5.99 s | 3.08 M | 32 | 56 | `fn-bs-run`, `fn-bs-run-relatedp`, `fn-bs-step`, `fn-bs-write` |
| `fn-bs-first-frontier-program-rejects-old-frontier-bytes` | 2.78 s | 1.53 M | 14 | 51 | the same |
| 22 other events | 0.65 s | | | | |

Both theorems symbolically run the frontier program. A computed hint
(`fn-bs-k0-unroll-hint`) expands one `fn-bs-run` call each time the clause is
stable, and `fn-bs-run-relatedp` holds the relation at every state of the run.
The rate is 500 k steps/s, so the time is in the rewriter. The log does not
say which rule wastes the steps, so I made one instrumented run of the
preserves theorem (`accumulated-persistence`, 4.82 s in the session):

| rune | tries | useless tries | useless frames |
|---|---|---|---|
| `(:definition fn-bs-run-relatedp)` | 121 | 92 | 291 k of 430 k |
| `(:definition fn-bs-store-relation)` | 121 | 92 | 401 k of 424 k |
| `fn-bs-authority-fencedp`, `-authority-inode-list`, `-authority-knownp`, `fn-sf-statep`, `-pending-entry-targets`, `-all-fencedp`, `-pending-matches-phase` | 212 to 2162 each | nearly all | 50 k to 107 k each |

**Cause.** The relation is opened on every partly unrolled prefix of the run,
while the rest of the run is still an unexpanded `fn-bs-run` call. The
relation cannot be decided on such a term, so 92 of its 121 openings fail,
and each failure first walks the authority, fencing and pending checks. The
relation is a fact about the states of the finished run, so it only needs to
be opened once the unrolling is complete.

**Repair.** There is a local theory, `fn-bs-k0-unroll-theory`, which is the
frontier theory without `fn-bs-run-relatedp` and `fn-bs-store-relation`. There
is also a local computed hint, `fn-bs-k0-staged-hint`. It expands the next
`fn-bs-run` call while one remains. Once none remains, it switches to the full
frontier theory, which opens the relation, and then it removes itself. Both
relation theorems use the staged hint and start in the unroll theory. The
completion theorem and the initial-image theorem do not use the relation and
are unchanged.

| event | session before | session after |
|---|---|---|
| preserves-relation | 4.82 s | 0.18 s |
| rejects-old-frontier-bytes | 2.19 s | 0.10 s |
| book, sum of every event | about 9.2 s | **2.2 s** (1.46 s of it is `include-book "byte-store-scan"`) |

## books/tcpcl-invariants: 11.0 s, now 2.7 s in the session

| event | log | steps | subgoals | largest split | defs |
|---|---|---|---|---|---|
| `fn-tcl-final-ack-means-every-segment` | 3.12 s | 0.97 M | 2391 | 177 | 12; splitters `fn-tcl-settle`, `fn-tcl-step`, `fn-tcl-transferringp`, `fn-tcl-member-equal-append` |
| `fn-tcl-live-inbound-ends-in-exactly-one-outcome` | 2.50 s | 0.41 M | 446 | 114 | 39: every arm of `fn-tcl-step` and `fn-tcl-settle`, `fn-tcl-messagep`, `fn-tcl-negotiate`, `fn-tcl-own-contact`, `fn-cbor-octetp`, `min` |
| `fn-tcl-step-emits-at-most-one-inbound-outcome` | 1.63 s | 0.27 M | 371 | 108 | the same 39 |
| `fn-tcl-drive-partition-independence` | 1.27 s | 0.86 M | 18 | 3 | an induction |
| `fn-tcl-inbound-is-created-only-by-start` | 0.64 s | 0.17 M | 344 | 174 | 18 |
| 57 other events | 1.9 s | | | | |

**Cause.** There are two, and every one of the four step theorems has at
least one of them. First, `fn-tcl-settle` is enabled under `fn-tcl-step`.
Settle is an `if` over the result of whichever arm ran, so it doubles every
arm, and it is the first splitter named for final-ack. What the step
theorems read from it is that it keeps the inbound record, keeps every event,
and adds at most a `(:close)`. Second, the two C3 theorems enabled the message
recognizer and every arm (`fn-tcl-recv-segment`, `-recv-init`, and through
the default theory `-recv-contact`, `-recv-ack`, `-recv-refuse`, `-recv-term`,
`-unexpected`) all at once. The goal was then a product of the step's
dispatch and each arm's own branches. What C3 needs from an arm is its
outcome count, and for the segment arm, that a live transfer the arm ends is
ended by exactly one outcome. The feed lane's probe, which closed only the
handshake handlers, could not move this, because the settle doubling and the
segment arm stayed open.

**Repair** (`books/tcpcl-invariants.lisp`; every new lemma is local):

1. `fn-tcl-settle-keeps-inbound` and `fn-tcl-settle-member-events` (the
   events after settle are the events before it, plus `(:close)` when settle
   fires), placed before C2. Final-ack and created-only-by-start now close
   `fn-tcl-settle`.
2. `fn-tcl-settle-keeps-outcome-count`. For each of the seven arms,
   `fn-tcl-<arm>-at-most-one-outcome` (linear: the arm emits at most one
   outcome for any id). `fn-tcl-recv-segment-ends-a-live-inbound-once`, whose
   hypotheses are a session, a live inbound record and that record's id. A
   first attempt without `fn-tcl-sessionp` failed at a broken-stream branch
   with a nil transfer id, and the recognizer's forward-chaining field facts
   supply that the id is a number. The two C3 theorems then open only
   `fn-tcl-step`, with `fn-tcl-c2-closed`, `fn-tcl-recv-segment`,
   `fn-tcl-settle` and `fn-tcl-ext-decision` closed. The C2 lemmas already in
   the book (`-creates-no-inbound`, `-keeps-inbound`) do the rest.

| event | session before | session after |
|---|---|---|
| final-ack-means-every-segment | 2.57 s | 0.30 s |
| live-inbound-ends-in-exactly-one-outcome | 2.02 s | 0.06 s |
| step-emits-at-most-one-inbound-outcome | 1.33 s | under 0.04 s (the lemmas it uses are 0.01 to 0.05 s each) |
| inbound-is-created-only-by-start | 1.73 s (measured with the new lemmas loaded; 0.64 s in the log) | 0.11 s |
| drive-partition-independence (not changed) | | 0.81 s |
| book, sum of every event | 7.5 s (the feed lane's session) | **2.72 s** |

The one event I left alone is `fn-tcl-drive-partition-independence`. It is
C1's fold induction, 0.81 s in the session, and it has no case explosion
(18 subgoals).

## books/nntp-auth: 23.8 s, now 4.2 s in the session

| event | log | steps | subgoals | largest split | defs, splitters |
|---|---|---|---|---|---|
| `include-book "peer-inbound"` | 3.14 s | | | | |
| `fn-auth-step-binds-a-peer-role-only-by-a-principal-login` | 4.03 s | 0.99 M | 589 | 155 | step, command, `fn-auth-tls-eventp`, `fn-auth-token-argp` |
| `fn-auth-step-preserves-the-config` | 2.38 s | 0.40 M | 321 | 180 | 17: every arm, the binding, the clearing and `fn-auth-principal-match` |
| `fn-auth-submission-is-the-delegated-submission` | 2.24 s | 0.53 M | 306 | 221 | 28: every arm, and the capability lines under CAPABILITIES |
| `fn-auth-authinfo-preserves-consistentp` | 1.74 s | 0.50 M | 190 | 78 | `fn-auth-principal-match`, `-principal-peer-count` |
| `fn-auth-authinfo-accepted-pass-binds-the-match` | 1.72 s | 0.44 M | 130 | 48 | the same, because the hint enabled the match |
| `fn-auth-command-preserves-consistentp` | 1.66 s | 0.24 M | 630 | 318 | `fn-auth-access-capability-lines`, `fn-peer-capability-lines`, `fn-nntp-capability-lines` |
| `fn-auth-step-starttls-clears-a-principal-role` | 1.43 s | 0.51 M | 387 | 210 | step, command, `fn-auth-tls-eventp` |
| `fn-auth-effectsp-of-append-auth` | 0.85 s | 0.35 M | 6 | | an induction |
| `fn-auth-authinfo-binds-only-on-an-accepted-pass` | 0.52 s | 0.18 M | 122 | 46 | |
| 213 other events | 3.85 s | | | | |

The nntp lane read this book as "the proof's subject, not a recognizer or
codec left open". For four of the events that is not so. Two instrumented
runs named the other cost. The log lists only the definitions the proofs
used; it does not show the rules that were tried and failed.

- `fn-auth-effectsp-of-append-auth` (0.87 s in the session). 277 k useless
  frames sat under the book's own exported rule
  `fn-auth-nntp-effects-are-auth-effects`. It is tried on every
  `fn-auth-effectsp` term of the induction, and relieving its hypothesis
  opens `fn-nntp-effectsp`, `fn-nntp-effectp`, the article-id grammar and
  the response-text scan, all of it useless.
- `fn-auth-step-binds-a-peer-role-only-by-a-principal-login` (2.30 s in the
  session). The top of the profile is `fn-nntp-article-idp-is-consp`
  (books/nntp-invariants: 31 548 tries, 560 k useless frames, opening
  `fn-nntp-article-idp` and `fn-nntp-message-id-tokenp`) and
  `fn-nntp-response-text-true-listp` (books/nntp-effects: 175 k useless
  frames, opening `fn-nntp-response-textp` and `true-listp`). Both are
  exported rules of the form "recognizer implies shape". With the NNTP
  syntax vocabulary the book opens at its top, each of them fires on every
  `consp` and `true-listp` term of the dispatch, including the tokenizer's
  results. No proof in this book reads an article identifier.

The rest is what the brief suspected, arms opened together:

- **Config and submission.** Each arm rebuilds the session from the config
  it was given, and each arm this book answers returns a nil submission.
  Opening all the arms at once gave the 180- and 221-way splits.
- **Consistency.** AUTHINFO opened `fn-auth-principal-match`, and with it the
  row count, the name scan and the record lookup, under every branch. The
  consistency proof needs two facts about a match: that it is a string, and
  that it came out of a checked configuration, so the node the binding tests
  is present. COMMAND opened the three capability-line functions under the
  CAPABILITIES arm, which returns the session unchanged.

**Repair** (`books/nntp-auth.lisp`; everything new is local):

1. After the top-of-book enables, a local disable of
   `fn-nntp-article-idp-is-consp` and `fn-nntp-response-text-true-listp`,
   with the reason. All 230 forms of the book load without them.
2. `fn-auth-effectsp-of-append-auth` closes
   `fn-auth-nntp-effects-are-auth-effects` in its hint.
3. `fn-auth-principal-match-is-a-string` (type prescription) and
   `fn-auth-principal-match-means-a-configuration` (forward-chaining to
   `fn-cfgp`). `fn-auth-authinfo-preserves-consistentp` and
   `fn-auth-authinfo-accepted-pass-binds-the-match` keep the match closed.
   I also tried closing it in `-binds-only-on-an-accepted-pass`, where the
   conclusion reads `fn-auth-principal-rolep` and so needs the matched
   record's auth kind. That failed at 1.15 s against 0.35 s open, so that
   theorem is unchanged.
4. `fn-auth-command-preserves-consistentp` closes
   `fn-auth-capability-lines-for-peer` and `fn-auth-peer-record`.
5. Four per-arm config lemmas: `fn-auth-authinfo-`, `-starttls-`,
   `-command-` and `-delegate-keeps-the-config`. The config keystone opens
   only the step, the TLS test and the re-entry.
6. Three per-arm submission lemmas: `fn-auth-authinfo-`, `-starttls-` and
   `-command-has-no-submission`. The submission theorem opens the step, the
   delegate and the re-entry, and it no longer expands `fn-auth-command`.

| event | session before | session after |
|---|---|---|
| binds-a-peer-role-only-by-a-principal-login | 2.30 s | 0.35 s |
| starttls-clears-a-principal-role | 0.95 s | 0.26 s |
| effectsp-of-append-auth | 0.87 s | 0.01 s |
| step-preserves-the-config | (2.38 s in the log) | 0.01 s, plus 0.04 s of lemmas |
| submission-is-the-delegated-submission | (2.24 s in the log) | 0.07 s, plus 0.03 s of lemmas |
| authinfo-preserves-consistentp | (1.74 s in the log) | 0.12 s |
| accepted-pass-binds-the-match | (1.72 s in the log) | 0.10 s |
| command-preserves-consistentp | (1.66 s in the log) | 0.01 s |
| book, sum of every event | 12.7 s (the nntp lane's session) | **4.22 s**, of which 1.80 s is `include-book "peer-inbound"` and the largest event is 0.35 s |

## books/feed-events: the export

`books/feed-events` has no theorems and, until now, no export theory. It left
every definition enabled for every book that includes it. The feed lane
measured 35 s in feed-totality and owner-feed-port from bridges over
`fn-feed-live-port-step` that opened the dispatchers under it. It then closed
them by hand in each of those hints.

**Change.** A new theory, `fn-feed-events-vocabulary`, holds the definitions
of `fn-feed-live-next`, `fn-feed-live-records`, `fn-feed-live-effects`,
`fn-feed-records-portp` and `fn-feed-record-portp`, and it is disabled at the
end of the book. `fn-feed-record-portp` runs the real FNFD encoder. The
per-kind record emitters (`fn-feed-enqueue-records`, `-tick-records`,
`-lost-records`, `-observe-records` and `-restart-records`) stay enabled, and
this is deliberate. `books/owner-feed` defines its own record functions on
top of them, and `books/owner-invariants` opens those functions by name
(`fn-own-feed-intent-records`), so closing the emitters could change a proof
in a book another lane owns. None of the five closed functions appears in any
book above the feed cluster except the three below.

**What includes it and was checked.** Every book or test that names one of
the five functions is one of these: `feed-correspondence`, `feed-totality`,
`owner-feed-port` and their tests. Each of the three books enables the
dispatcher it reasons about by name, and the tests evaluate ground terms. I
loaded each book in a session against the changed export. All forms of
`feed-correspondence` (32), `feed-totality` (13), `owner-feed-port` (16) and
`owner-feed` (174) were admitted. `owner-feed` does not name the five
functions; it calls `fn-feed-live-port-step` only inside a definition. The
books that include `owner-feed` (`feed-connection`, `owner` and everything
above them) were not loaded. None of them names the five functions. The
incremental run recertifies what includes feed-events.

## Book totals

| book | log | session before | session after |
|---|---|---|---|
| `books/nntp-auth` | 23.8 s (16 jobs) | 12.7 s | 4.2 s |
| `books/byte-store-relation` | 12.3 s | about 9.2 s | 2.2 s |
| `books/tcpcl-invariants` | 11.0 s | 7.5 s | 2.7 s |
| `books/feed-events` | 2.0 s | | not changed in cost; its includers lose the open dispatchers |

## Not verified

- These are session loads, not certificates. Some sessions included books
  that had no cached pair at this branch's digests from source without
  certifying them: `peer-feed-invariants` for the feed sessions, and
  `feed-events` and `owner-feed` below `owner-feed-port`. A session include
  of a book like that does not replay its proofs. `owner-feed`'s proofs were
  checked in its own session.
- `owner`, `owner-invariants`, `feed-connection`, `feed-connection-invariants`
  and the rest of the owner cluster were not loaded against the changed
  feed-events export. They are left to the farm run.
- The session's before and after times are the Mac's; the certify-log
  numbers are persvati's at 16 jobs. Each book's number under certification
  is the manifest's.
