# Lane dump: `nntp-served-path`

Branch `lane/nntp-served-path`, worktree `/Users/ember/dev/fn/build/lanes/nntp-served-path`,
branched from `0bd0b5c`. This is a **WIP handoff**, written because the session's
usage ended mid-certification. Nothing here is certified evidence except where
this file says a book certified; read the "In progress" section before trusting
any theorem name.

## The packet as I understood it

1. **D3, the served-path denial of service.** `books/nntp.lisp:1115-1116` re-ran
   `fn-nntp-projectionp` inside every `fn-nntp-step`; that recognizer required
   every committed article to be projectable, and `fn-articlep` admits articles
   that are not. One such article answered 503 to every command including
   CAPABILITIES and QUIT, and every command cost work quadratic in article
   count. Required: (a) carry projectability as session state with a
   preservation theorem; (b) make an unprojectable article degrade only itself
   with an explicit distinct error and exclusion from ranges; (c) remove the
   per-command quadratic recognizers or state the remaining per-command cost as
   a function of the command's own range. Update `host/reader-host.lisp:65-70`,
   calling only proved functions.
2. **Real effect typing.** `fn-nntp-effectp` accepted `(:reply (65))`.
   Strengthen it to a three-digit status followed by SP or CRLF, an initial line
   of at most 512 octets including CRLF, and a dot-stuffed block terminated by
   `.\r\n`; re-prove `fn-nntp-command-effects-well-formed` and
   `fn-nntp-step-effects-well-formed`. Bound group names so the 549-octet
   LISTGROUP 211 line cannot occur, and prove it.
3. **Session invariant with content.** The old invariant admitted a NIL cursor
   unconditionally. Add the RFC conjuncts (cursor after GROUP/LISTGROUP;
   NEXT/LAST move only to valid numbers; Message-ID retrieval unchanged), prove
   preservation over the real `fn-nntp-step` and finite traces, and add
   must-fail teeth per conjunct.
4. **Keep and re-verify the existing precedence** (412 > 420/423, 430, 501) and
   record in `specs/nntp-audit.md` per RFC clause what is proved vs tested vs
   open. Do not advertise READER; say why.

Owned: `books/nntp.lisp`, `books/nntp-invariants.lisp`, `books/nntp-effects.lisp`,
`tests/acl2/nntp-tests.lisp`, `host/reader-host.lisp`, `specs/nntp.md`,
`specs/nntp-audit.md`, `specs/reader-partition-matrix.md`.
Not owned: `books/acceptance.lisp`, `books/wire.lisp`, `tools/run_reader.py`.

## State at handoff

| Root | State |
| --- | --- |
| `books/nntp` | **certifies** (`books/nntp.cert` present, produced by `build/acl2/certify-20260919T053253Z-94153`) |
| `books/nntp-invariants` | **does not certify yet.** Last observed failure: `FN-NNTP-NUMBER-RETRIEVAL-PRESERVES-CONSISTENT-SESSION`. A fix for it was applied and the confirming run was killed before it finished. Everything before that theorem in the book admitted. |
| `books/nntp-effects` | **not yet attempted with the current source** (it includes `nntp-invariants`, so it cannot be certified until that book does). |
| `tests/acl2/nntp-tests` | same; includes `nntp-effects`. |

A `certify_books.py` process was still running at handoff (evidence directory
`build/acl2/certify-20260919T064133Z-37013/`, log `build/certH.log`). It was
started with `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py
books/nntp-invariants`. I did not kill it. Note that `setsid` does not exist on
this machine; use `nohup … </dev/null & disown` or the harness's background
option.

## Done

### `books/nntp.lisp` (certifies)

New constants:

```lisp
(defconst *fn-nntp-max-response-octets* 512)
(defconst *fn-nntp-max-initial-line-octets* 510)
(defconst *fn-nntp-max-article-number* 2147483647)
(defconst *fn-nntp-max-group-octets* 460)
(defconst *fn-nntp-max-message-id-octets* 250)
(defconst *fn-nntp-max-decimal-octets* 10)
```

**Session gained a fourth field.** `(openp selected-group current-number
projected)`. `fn-nntp-initial-session` is gone; `fn-nntp-open-session` replaces
it and is the only place the whole-archive recognizer runs:

```lisp
(defun fn-nntp-open-session (archive)
  (fn-nntp-make-session t nil nil
                        (if (fn-nntp-projectionp archive) t nil)))
```

**`fn-nntp-projectionp` is now a configuration recognizer only** (this is the
heart of D3(a)):

```lisp
(defun fn-nntp-projectionp (archive)
  (and (fn-statep archive)
       (fn-nntp-safe-group-listp (fn-state-groups archive))
       (fn-nntp-nexts-boundedp (fn-state-nexts archive))
       (<= (len (fn-state-articles archive)) *fn-nntp-max-article-number*)))
```

with

```lisp
(defun fn-nntp-safe-group-namep (text)
  (and (stringp text)
       (let ((octets (fn-nntp-string-octets text)))
         (and (consp octets)
              (<= (len octets) *fn-nntp-max-group-octets*)
              (fn-nntp-printable-tokenp octets)))))
```

**Per-article checks split by what a response needs:**

```lisp
(defun fn-nntp-article-idp (article)
  (let ((text (fn-article-msgid article)))
    (and (stringp text)
         (<= (length text) *fn-nntp-max-message-id-octets*)
         (fn-nntp-message-id-tokenp (fn-nntp-string-octets text)))))

(defun fn-nntp-article-framedp (article)
  (let ((payload (fn-article-payload article)))
    (and (equal (car (fn-nntp-crlf-lines payload)) :ok)
         (fn-nntp-split-okp (fn-nntp-split-article payload)))))

(defun fn-nntp-projection-articlep (article)
  (and (fn-nntp-article-idp article)
       (fn-nntp-article-framedp article)))
```

`fn-nntp-crlf-lines-aux` now also rejects octet 0, so a payload carrying NUL is
not framed (RFC 3977 §3.1.1 forbids NUL in a multi-line block).

**Numbering rebuilt over articles, one pass.** `fn-nntp-group-numbers`,
`fn-nntp-range-numbers`, `fn-nntp-next-number` and `fn-nntp-last-number` are
**deleted**. Replacements: `fn-nntp-article-number` (available number or 0),
`fn-nntp-available-article` (the cursor's referent), `fn-nntp-group-count`,
`fn-nntp-group-low`, `fn-nntp-group-high`, `fn-nntp-group-next-number`,
`fn-nntp-group-last-number`, `fn-nntp-group-range-numbers` (filter-then-insert,
so the sort is charged to the command's own range), and `fn-nntp-orderedp`.
`fn-nntp-find-group-number` still matches the **raw** membership number, so a
command naming an unavailable article reaches an explicit error rather than
silently missing.

Supporting theorems proved in `books/nntp.lisp` (all certified):
`fn-nntp-article-number-natp`, `fn-nntp-article-number-bounded`,
`fn-nntp-available-number-article-is-projectable`,
`fn-nntp-available-article-is-projectable`,
`fn-nntp-insert-number-preserves-ordered`, `fn-nntp-insert-number-members`,
`fn-nntp-group-count-natp`, `fn-nntp-group-count-at-most-articles`,
`fn-nntp-group-low-natp`, `fn-nntp-group-low-bounded`,
`fn-nntp-group-low-is-available`, `fn-nntp-group-high-natp`,
`fn-nntp-group-high-bounded`, `fn-nntp-group-high-is-available`,
`fn-nntp-group-next-number-natp`, `fn-nntp-group-next-number-is-available`,
`fn-nntp-group-last-number-natp`, `fn-nntp-group-last-number-is-available`,
`fn-nntp-group-range-numbers-are-ordered`,
`fn-nntp-group-range-numbers-are-available`.

Verbatim, the two that carry the cursor claim:

```lisp
(defthm fn-nntp-group-low-is-available
  (implies (posp (fn-nntp-group-low group articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-low group articles) articles))))

(defthm fn-nntp-group-next-number-is-available
  (implies (posp (fn-nntp-group-next-number group current articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-next-number group current articles)
                   articles))))
```

**Bounded decimal field.** Every rendered number goes through

```lisp
(defun fn-nntp-decimal-field (number)
  (let ((octets (fn-nntp-decimal number)))
    (if (and (consp octets)
             (fn-nntp-decimal-tokenp octets)
             (<= (len octets) *fn-nntp-max-decimal-octets*))
        octets
      '(48))))
```

so the ten-octet field bound is structural rather than an arithmetic side
condition (see "Design decisions").

**Per-article degradation in the response constructor.**
`fn-nntp-article-response` now gates on the two per-article checks and returns
`503 stored article identifier unavailable` or `503 stored article framing
unavailable`, leaving the session untouched in both cases. The cursor moves only
on success.

**Dispatcher split.** `fn-nntp-archive-keywordp` names the nine archive
commands; `fn-nntp-session-command` (no archive argument) handles CAPABILITIES,
HELP, QUIT, 500 and 501; `fn-nntp-archive-command` handles the rest and is
reached only when the session's carried verdict is true, otherwise `503 archive
projection unavailable`. `fn-nntp-step` no longer mentions
`fn-nntp-projectionp` at all.

### `host/reader-host.lisp`

`fn-reader-reset` builds the session with `fn-nntp-open-session` over the
installed archive (guarded by `boundp-global`), so the recognizer runs once per
connection. `fn-reader-use-store` still returns `:ready`/`:refused` (the two
outcomes `tools/run_reader.py`, which I do not own, parses), but refusal is now
only for a store whose recognizer fails or whose **configuration** cannot be
rendered — a single unprojectable article no longer refuses the store.

### `specs/`

- `specs/nntp-audit.md` rewritten: per-clause table updated, plus new sections
  "The served path carries its projection verdict", "Per-command cost", "Effect
  typing" (including the 549-octet case), "Session invariant", "What is proved,
  what is tested, what is open", and "Why READER is not advertised".
- `specs/nntp.md`: new requirement NNT-007 for the carried verdict.
- `specs/reader-partition-matrix.md`: notes that the reset is where the
  recognizer runs, once per connection.

### `tests/test_reader.py` (not in the owned list — see "Proposals")

`test_store_with_non_news_payload_refuses_before_listening` asserted the D3
behaviour itself (the reader refusing to start because one article is not
news-shaped). Replaced by
`test_store_with_non_news_payload_degrades_only_that_article`, which posts one
opaque and one well-formed article and asserts CAPABILITIES, `GROUP fn.letters`
→ `211 2 1 2 fn.letters`, `STAT 1` → 223, `ARTICLE 1` → 503 framing,
`ARTICLE 2` → 220 with the payload, QUIT → 205.

## In progress

### `books/nntp-invariants.lisp` — written, not yet certified

The relation and the two availability keystones, verbatim as they stand:

```lisp
(defun fn-nntp-cursor-validp (group current archive)
  (and (posp current)
       (consp (fn-nntp-available-article
               group current (fn-state-articles archive)))))

(defun fn-nntp-group-nonemptyp (group archive)
  (posp (fn-nntp-group-low group (fn-state-articles archive))))

(defun fn-nntp-session-consistentp (session archive)
  (and (fn-nntp-sessionp session)
       (implies (fn-nntp-session-projected session)
                (fn-nntp-projectionp archive))
       (if (null (fn-nntp-session-group session))
           (null (fn-nntp-session-current session))
         (and (member-equal (fn-nntp-session-group session)
                            (fn-state-groups archive))
              (if (fn-nntp-group-nonemptyp (fn-nntp-session-group session) archive)
                  (fn-nntp-cursor-validp (fn-nntp-session-group session)
                                         (fn-nntp-session-current session)
                                         archive)
                (null (fn-nntp-session-current session)))))))

(defthm fn-nntp-step-preserves-carried-projection
  (equal (fn-nntp-session-projected
          (fn-nntp-result-session (fn-nntp-step session archive wire-event)))
         (fn-nntp-session-projected session)))

(defthm fn-nntp-archive-free-step-ignores-the-archive
  (implies (not (fn-nntp-archive-keywordp (car (fn-nntp-tokenize line))))
           (equal (fn-nntp-step session archive (list :command line))
                  (fn-nntp-step session other (list :command line))))
  :rule-classes nil)

(defthm fn-nntp-step-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-nntp-step session archive wire-event))
            archive)))

(defthm fn-nntp-finite-trace-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-run-session session archive events) archive)))

(defthm fn-nntp-finite-trace-preserves-carried-projection
  (equal (fn-nntp-session-projected (fn-nntp-run-session session archive events))
         (fn-nntp-session-projected session)))

(defthm fn-nntp-opened-finite-trace-is-consistent
  (and (fn-nntp-session-consistentp
        (fn-nntp-run-session (fn-nntp-open-session archive) archive events)
        archive)
       (fn-nntp-sessionp
        (fn-nntp-run-session (fn-nntp-open-session archive) archive events))))

(defthm fn-nntp-group-selects-the-first-available-article
  (implies (and (member-equal group (fn-state-groups archive))
                (fn-nntp-group-nonemptyp group archive))
           (and (equal (fn-nntp-session-group
                        (fn-nntp-result-session
                         (fn-nntp-group-result session archive group)))
                       group)
                (equal (fn-nntp-session-current
                        (fn-nntp-result-session
                         (fn-nntp-group-result session archive group)))
                       (fn-nntp-group-low group (fn-state-articles archive)))
                (fn-nntp-cursor-validp
                 group (fn-nntp-group-low group (fn-state-articles archive))
                 archive))))

(defthm fn-nntp-next-or-last-moves-only-to-an-available-article
  (implies (fn-nntp-session-consistentp session archive)
           (let ((result (fn-nntp-result-session
                          (fn-nntp-next-or-last session archive direction))))
             (or (equal result session)
                 (and (equal (fn-nntp-session-group result)
                             (fn-nntp-session-group session))
                      (fn-nntp-cursor-validp (fn-nntp-session-group session)
                                             (fn-nntp-session-current result)
                                             archive)))))
  :rule-classes nil)
```

**Known-good prefix.** In the last completed run
(`build/acl2/certify-20260919T063412Z-32839`) every event up to and including
`fn-nntp-article-response-without-identifier-preserves-session` admitted;
`fn-nntp-current-retrieval-preserves-consistent-session` admitted.

**The one failing event** was

```
ACL2 Error [Failure] in ( DEFTHM FN-NNTP-NUMBER-RETRIEVAL-PRESERVES-CONSISTENT-SESSION ...)
```

with key checkpoint (run `…-32839`):

```
Subgoal 2.381.17.13
(IMPLIES (AND (EQUAL (FN-NNTP-GROUP-LOW (CADR SESSION) (FN-STATE-ARTICLES ARCHIVE)) 0)
              (NOT (INTEGERP (FN-NNTP-DECIMAL-VALUE-AUX TOKEN 0)))
              ...
              (< 16 (LEN TOKEN)))
         (TRUE-LISTP (FN-NNTP-RESULT-SESSION
                        (CONS SESSION '((:REPLY (53 48 49 …)))))))
```

i.e. with `fn-nntp-result-session` closed but `fn-nntp-single` open, the 501
branch could not reduce. **The fix already applied to the file** (and not yet
confirmed) adds `fn-nntp-single fn-nntp-make-result` to that theorem's disable
list so `fn-nntp-single-preserves-session` and
`fn-nntp-result-session-of-make-result` fire. Resume by running

```
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/nntp-invariants
```

and reading the first `ACL2 Error [Failure] in ( DEFTHM` in
`build/acl2/certify-*/books--nntp-invariants.certify.log`.

**The recurring hint pathology, so Codex does not rediscover it.** All the
session-component rules are stated in the *closed* form
`(fn-nntp-session-projected (fn-nntp-result-session (fn-nntp-<ctor> …)))`. ACL2
tries rewrite rules for a function symbol before expanding its definition, so
these rules fire only when the **constructor** under `fn-nntp-result-session` is
still closed. Two consistent configurations work; mixing them does not:

- constructors open (`fn-nntp-single`, `fn-nntp-make-result` enabled) **and**
  accessors open — everything reduces to `car`/`cadddr` by computation; or
- constructors closed **and** `fn-nntp-result-session` closed — the rules fire.

Disabling `fn-nntp-make-result` while `fn-nntp-result-session` is open is the
failure mode that cost several runs.

**The other pathology: runaway theories.** Enabling `fn-nntp-article-response`
or `fn-nntp-group-result` without disabling the byte renderers pulls
`fn-nntp-decimal-field`, `fn-nntp-retrieval-initial`, `fn-nntp-group-initial`,
`fn-nntp-article-section` and then `fn-statep` into a session proof; one such
goal ran 487 s and ended asking about decimal lengths. Every session proof in
the file now disables, at minimum: `fn-nntp-projectionp fn-statep
fn-state-groups fn-state-articles fn-state-nexts fn-nntp-available-article
fn-nntp-group-low fn-nntp-article-idp fn-nntp-article-framedp
fn-nntp-article-section fn-nntp-retrieval-initial fn-nntp-decimal-field
fn-nntp-crlf fn-nntp-stuff-lines fn-nntp-group-initial
fn-nntp-listgroup-initial fn-nntp-number-lines fn-nntp-group-range-numbers`.
Keep that discipline.

Also note: with `fn-nntp-projectionp` closed, `(stringp group)` and
`(not (member-equal nil groups))` come from
`fn-nntp-projected-group-member-is-string` and
`fn-nntp-projected-groups-exclude-nil`, which need `fn-state-groups` closed too,
or their left-hand sides do not match.

### `books/nntp-effects.lisp` — written, never certified

This is the packet's item 2 and it has had **no prover exposure at all**. The
response grammar is a re-parse of the emitted octets, deliberately independent
of the constructors:

```lisp
(defun fn-nntp-response-octetp (byte)
  (and (integerp byte) (<= 1 byte) (<= byte 255)
       (not (equal byte 13)) (not (equal byte 10))))

(defun fn-nntp-status-prefixp (bytes)   ; three digits, then SP or CRLF
  …)

(defun fn-nntp-initial-line-tail (bytes seen)  ; ≤ 512 octets counting CRLF
  …)

(defun fn-nntp-block-scan (bytes startp)       ; dot-stuffed, ends ".\r\n"
  (declare (xargs :measure (+ (* 2 (acl2-count bytes)) (if startp 1 0))))
  …)

(defun fn-nntp-replyp (octets)
  (and (fn-nntp-status-prefixp octets)
       (let ((tail (fn-nntp-initial-line-tail octets 0)))
         (and (equal (car tail) :ok)
              (let ((rest (car (cdr tail))))
                (if (null rest) t (fn-nntp-block-scan rest t)))))))

(defun fn-nntp-effectp (effect)
  (or (and (true-listp effect)
           (equal (len effect) 2)
           (equal (car effect) :reply)
           (fn-octet-listp (car (cdr effect)))
           (fn-nntp-replyp (car (cdr effect))))
      (equal effect (fn-nntp-close-effect))))
```

The two goal theorems, as written:

```lisp
(defthm fn-nntp-command-effects-well-formed
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-command session archive tokens)))))

(defthm fn-nntp-step-effects-well-formed
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-nntp-step session archive wire-event)))))
```

The 512-octet argument is carried by

```lisp
(defthm fn-nntp-group-initial-fits
  (implies (fn-nntp-safe-group-namep group)
           (<= (+ (len (fn-nntp-group-initial archive group)) 2)
               *fn-nntp-max-response-octets*))
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-listgroup-initial-fits …)
(defthm fn-nntp-retrieval-initial-fits …)
```

and the chain of re-parse lemmas `fn-nntp-initial-line-tail-of-text`,
`fn-nntp-status-prefix-of-append`, `fn-nntp-block-scan-of-text-line`,
`fn-nntp-block-scan-of-stuffed-line`, `fn-nntp-block-scan-of-stuff-lines`,
`fn-nntp-replyp-of-single-line`, `fn-nntp-replyp-of-block`.

The last form in the book is an `encapsulate` with a `local (include-book
"arithmetic-5/top" :dir :system)` proving

```lisp
(defthm fn-nntp-decimal-field-is-exact-in-range
  (implies (and (natp number) (<= number *fn-nntp-max-article-number*))
           (equal (fn-nntp-decimal-field number) (fn-nntp-decimal number))))
```

This is the only arithmetic-heavy event in the lane and the most likely to need
work; if it resists, **delete it and record the gap** — the 512-octet theorems
do not depend on it, because `fn-nntp-decimal-field` bounds the width by
construction. The rest of the book must not be weakened to save it.

Expect several hint iterations here: I did one pre-emptive pass (append
associativity, `fn-nntp-message-id-tail-is-true-listp`,
`fn-nntp-projection-groups-are-safe`, and removing `fn-nntp-projectionp` from
three `enable` lists) but nothing in this book has been run.

### `tests/acl2/nntp-tests.lisp` — written, never certified

Includes `../../books/nntp-effects` and `std/testing/must-fail` (the runner
skips `:dir` include-books in its digest closure, so that is fine).

Teeth present, per keystone:

- `fn-nntp-step-preserves-carried-projection` (unconditional): both verdicts are
  reached from real archives, and traces keep each.
- `fn-nntp-archive-free-step-ignores-the-archive`: `assert-event` that QUIT and
  CAPABILITIES agree across two different archives, `assert-event` that GROUP
  does **not**, plus `(must-fail (thm …))` of the statement with the hypothesis
  dropped.
- `fn-nntp-step-preserves-consistent-session`: a reachable-shaped session whose
  cursor names no available article, shown inconsistent before and after a step,
  plus a `must-fail` of the hypothesis-free claim.
- `fn-nntp-step-effects-well-formed`: a session claiming a projection the
  archive does not have emits a 215 block whose line carries CRLF;
  `assert-event` that `fn-nntp-effectsp` is false there, plus a `must-fail`.
  Also `(not (fn-nntp-effectp '(:reply (65))))` — the review's own example.
- `fn-nntp-group-selects-the-first-available-article`: counterexamples for both
  hypotheses plus a `must-fail`.

D3 witnesses: `*fn-nntp-mixed-archive*` (a good article at 1 and an unframed one
at 2) exercises CAPABILITIES, QUIT, `211 2 1 2`, `STAT 2` → 223, `ARTICLE 2` →
503 framing, `ARTICLE 1` → 220, `NEXT` → 223. `*fn-nntp-bad-id-archive*` (an
article whose stored identifier carries CRLF) shows exclusion from LISTGROUP,
`STAT 2` → 503 identifier, and `NEXT` → 421.

549-octet witnesses: `fn-nntp-safe-group-namep` accepts 460 and rejects 461 and
497; `(not (fn-nntp-projectionp (fn-initial-state (list <497>))))`.

## Not started

- Nothing in the packet is unattempted, but **items 2 and 3 are unverified**:
  `books/nntp-effects.lisp` has never been run, and `books/nntp-invariants.lisp`
  has one known-failing event with an unconfirmed fix.
- The full gate was never run: `make check`, full `make certify`, and
  `python3 -m unittest tests.test_reader tests.test_reader_partitions -v` have
  **not** been executed against this tree.
- `specs/reader-partition-matrix.md` still quotes the previous run's timing
  ("7 tests and 65 serialized socket connections in 0.148 seconds"). Re-measure
  and update once the socket tests run.

## Design decisions, and why

1. **The carried verdict lives in the session, not in a separate store.** The
   host already threads the session through `fn-reader-session`, and
   `fn-nntp-step` already takes it, so the theorem subject stays the function
   the host calls (`host/reader-host.lisp:112`). A separate "view" value would
   have needed a new host global and a new argument.
2. **`fn-nntp-projectionp` keeps its name but changes meaning** — configuration
   only. Renaming would have churned the host and the specs; the meaning change
   is documented at its definition and in `specs/nntp-audit.md`.
3. **Per-article checks are split into identifier and framing** because STAT,
   NEXT and LAST need only the identifier. That is what lets an unframed article
   keep a usable article number instead of vanishing, which in turn keeps the
   GROUP count honest.
4. **Two distinct 503 texts**, not one, and not 423: RFC 3977 §3.2.1 assigns 503
   to "only handles a subset of legitimate cases", which is exactly this. 423
   would have been a lie for an article that does exist.
5. **`fn-nntp-find-group-number` keeps matching the raw membership number** so
   that the identifier branch of `fn-nntp-article-response` is *reachable* from
   `STAT n`. Making the finder skip unrenderable articles would have made that
   branch dead code, which the assurance rules forbid as evidence.
6. **`fn-nntp-group-numbers` and the list-level `next`/`last` were deleted
   rather than bridged.** A correspondence theorem between a fast fold and the
   insertion-sort spec would have needed `orderedp` plumbing for every one of
   six functions. Defining the fold *as* the specification needs only "the
   result is an available number", which is a one-line induction each, and it is
   the honest definition anyway: the RFC talks about the smallest number greater
   than the cursor, not about a sorted list.
7. **`fn-nntp-decimal-field` clamps the rendered width.** The alternative was to
   prove `(<= (len (fn-nntp-decimal n)) 10)` for `n ≤ 2^31-1`, which needs
   `floor`-monotonicity arithmetic in every book that renders a number. Clamping
   makes the 512-octet theorems *unconditional*, which is stronger than a
   conditional bound; `fn-nntp-decimal-field-is-exact-in-range` then says the
   clamp is inactive across the legal range, and boundary `assert-event`s pin
   0, 1 and 2147483647.
8. **The response grammar re-parses the bytes** instead of being a shape
   predicate over the constructors. A predicate written from the constructors
   would be the definition restated — precisely the §4 finding this packet
   exists to repair.
9. **Group names are bounded at 460 octets** because the widest generated
   initial line has a 52-octet fixed part (`211 `, three ≤10-octet decimal
   fields, three spaces, ` list follows`, CRLF); 460 + 52 = 512 exactly.
10. **`fn-nntp-session-command` takes no archive argument.** Making the
    independence *typed* rather than argued is what makes
    `fn-nntp-archive-free-step-ignores-the-archive` a one-line statement.
11. **`:ready`/`:refused` kept in `fn-reader-use-store`** because
    `tools/run_reader.py:70` parses exactly those two tokens and I do not own
    it. A third `:degraded` outcome would be better; see "Proposals".

## Gate commands and last results

| Command | Last result |
| --- | --- |
| `python3 tools/certify_books.py books/nntp` | passed; `books/nntp.cert` present |
| `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/nntp-invariants` | failed at `FN-NNTP-NUMBER-RETRIEVAL-PRESERVES-CONSISTENT-SESSION` (run `…-32839`); fix applied, unconfirmed |
| `python3 tools/certify_books.py books/nntp-effects` | never run with current source |
| `python3 tools/certify_books.py tests/acl2/nntp-tests` | never run with current source |
| `make check` | not run in this worktree |
| `make certify` | not run in this worktree since the edits (the pre-edit baseline was killed part way) |
| `python3 -m unittest tests.test_reader tests.test_reader_partitions -v` | not run |

Contention notes from the coordinator that apply to any resumed run: pass
`FN_ACL2_TIMEOUT_SECONDS=1800` (`books/article-properties` alone exceeds the
600 s default under ten-lane load), and never launch a long run with a bare `&`
from an agent shell.

## Known defects and risks

1. **`books/nntp-effects.lisp` is unproved.** Treat every theorem named in
   `specs/nntp-audit.md` from that book as *claimed, not proved* until it
   certifies. If it cannot be made to certify as written, the audit spec must be
   walked back in the same commit.
2. **`specs/nntp-audit.md` already describes the end state**, including theorem
   names from the uncertified books. That is a live honesty risk: it is prose
   ahead of evidence. Either finish the proofs or edit the spec.
3. `fn-nntp-decimal-field-is-exact-in-range` is the riskiest single event
   (arithmetic-5 inside an `encapsulate`). It is not load-bearing; drop it and
   record the gap rather than weakening anything else.
4. The LISTGROUP range ordering is still `O(k²)` in the size of the requested
   range's own output. Stated in `specs/nntp-audit.md`; not a cost theorem.
5. `LIST ACTIVE` is `O(G · A)` — one article pass per listed group. Previously
   `O(G · A²)`. Also only stated, not certified.
6. The per-command costs in `specs/nntp-audit.md` are read off the executed
   graph. There is no cost theorem in this lane.
7. `fn-nntp-article-response`'s identifier branch is reachable only through a
   numeric retrieval; the Message-ID path cannot reach it, because the token is
   itself a bounded printable message-id. That is documented at the definition,
   and no theorem is claimed about it.
8. The session relation is stated against an **immutable** archive. Cursor
   behaviour under removal or expiry is open and is called out in the spec.

## Proposals for files I do not own

- **`tools/run_reader.py`** (another lane). `acl2_archive_action` accepts only
  `:READY` and `:REFUSED`, which forces `fn-reader-use-store` to collapse
  "serving, but the configuration cannot be rendered" into a refusal. Proposal —
  accept a third token and report it distinctly, which also satisfies the
  "three outcomes stay distinct" rule:

  ```python
  match = re.fullmatch(rb"\s*:(READY|DEGRADED|REFUSED)\s*ACL2 !>", output.upper())
  ```

  and at the call site:

  ```python
  action = acl2_archive_action(self.call(selection))
  if action == b"refused":
      raise RuntimeError("reader store is not a recognized composed store")
  if action == b"degraded":
      print("WARNING: archive configuration is not projectable; "
            "only CAPABILITIES, HELP and QUIT will be served", file=sys.stderr)
  ```

  With that, `fn-reader-use-store` would return `:degraded` instead of
  `:refused` when `fn-sn-statep` holds but `fn-nntp-projectionp` does not, and
  the reader would still serve the archive-free commands.
- **`books/acceptance.lisp`** (not owned). `fn-statep` does not record that
  committed articles are in descending per-group number order, although
  `fn-accept-complete` always conses at the watermark. If that were an invariant,
  `fn-nntp-group-range-numbers` could drop its insertion entirely and LISTGROUP
  would be linear. Proposal: add `fn-articles-descending-in-groupp` to
  `fn-statep` and prove `fn-install-preserves-state` maintains it.
- **`tests/test_reader.py`** is not in either list in my packet. I changed it
  (see "Done") because the packet required `host/reader-host.lisp:65-70` to stop
  refusing the whole store, and that test asserted the old refusal. If another
  lane owns it, the change is one method and is easy to re-apply.

## Dirty and untracked files at handoff

Modified (all committed with this dump):

```
books/nntp-effects.lisp
books/nntp-invariants.lisp
books/nntp.lisp
host/reader-host.lisp
specs/nntp-audit.md
specs/nntp.md
specs/reader-partition-matrix.md
tests/acl2/nntp-tests.lisp
tests/test_reader.py
```

Untracked and **not** committed: `books/nntp.cert` and the other `*.cert`,
`*.port`, `*.cert.out` artifacts produced by certification, and everything under
`build/` (certification logs and evidence directories, including
`build/certify-baseline.log` and `build/acl2/certify-*/`). `.gitignore` already
covers them; they are local evidence only.
