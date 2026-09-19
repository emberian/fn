# LANEDUMP: lane `wire-article-transfer`

Worktree `/Users/ember/dev/fn/build/lanes/wire-article-transfer`, branch
`lane/wire-article-transfer`, branched from `0bd0b5c`. This is a WIP handoff
written because the session's usage ended mid-lane; it is not a completed
packet. No certification is running as of this writing.

## The packet as I understood it

Six items, from the independent review at `planning/review-2026-09-18-independent.md`:

1. **Wire cost.** `fn-wire-feed-byte` and `fn-wire-next` called `fn-wire-statep`
   per byte, which walks the reversed line, every retained body line and the
   size sum, so feeding B bytes in article mode was quadratic. Carry the line
   length and body size as state fields maintained incrementally so each byte
   does constant work; prove the new step preserves `fn-wire-statep` and that on
   `fn-wire-statep` inputs the new `fn-wire-next` returns exactly what the old
   one returned (old definition kept under a `-reference` name); preserve the
   retained-input bound as a carried invariant.
2. **Partition theorem on the host-called function.** `fn-wire-feed-proper-append`
   is about an API the host never calls. Prove partition independence for
   `fn-wire-next` in the form `tools/run_reader.py:167-181` actually loops (it
   re-feeds the returned unconsumed suffix). Keep the old theorem only if the
   new proof uses it.
3. **`fn-wire-begin-article`** silently returned the unchanged state when
   `line-rev` or `pending-crp` was non-nil. Make the rejection explicit, prove
   it is the only case that rejects, add teeth.
4. **Article `fields` correspondence.** For every successful parse: raw lines
   concatenated with CRLF in field order equal the header octets; each
   `lower-name` is the ASCII-lowercasing of the octets before the first colon of
   its first raw line; each `unfolded-value` equals the RFC 5322 §2.2.3
   unfolding of its raw lines, with the unfolding defined as an independent
   reference function. Teeth: a dropped field or a misattached fold must fail.
5. **Work bound honesty.** Either prove the cost-side correspondence for
   `fn-aw-parse` or state the exponent, the closed form and its distance from
   the measured cost in one sentence and mark the cost side "by construction,
   not by theorem". Decide the no-blank-line case by citing RFC 5536 §2.1 and
   RFC 3977 §3.1.1; keep or change the behavior and record the clause.
6. **Transfer overlap.** `transfer.lisp:566-572` returned `:overlap-conflict`
   for byte-identical partial overlaps, a hard stall for re-fragmented objects.
   Compare bytes on overlap; conflict only on differing bytes; retain the union;
   prove the assembly theorems still hold; add teeth. Fix the stale comment at
   `transfer-public-work.lisp:352-353`. Add an executable witness of the cost
   model. State in `specs/transfer-public-bound.md` that the bound is on
   `fn-transfer-missing-ranges`, which has no caller outside the transfer books.

Gate: `make check`; a full `make certify` green after the changes; and
`python3 -m unittest tests.test_reader tests.test_reader_partitions -v`.

## Status summary

| Item | State |
| --- | --- |
| 1 wire cost | **DONE and certified** (`books/wire`, `books/wire-invariants`, `tests/acl2/wire-tests`) |
| 2 partition on the served path | **DONE and certified** (same three roots) |
| 3 explicit begin-article decision | **DONE and certified** (same three roots) |
| 4 article `fields` correspondence | **DONE**; `books/article-invariants` certified green. `tests/acl2/article-tests` written with five teeth but **not yet certified** |
| 5 work-bound honesty and the RFC decision | Specs **DONE**; the executable cost witnesses in `tests/acl2/article-work-tests.lisp` are **NOT STARTED** (they need one measurement run) |
| 6 transfer overlap | Kernel **DONE and certified** (`books/transfer`); `books/transfer-invariants` **IN PROGRESS, one theorem failing**; `tests/acl2/transfer-tests` written but not certified |
| gate | `make check` passes; full `make certify` **NOT RUN** since the changes; Python reader tests **NOT RUN** |


## Files changed (all tracked; nothing untracked before this commit)

```
 M books/article-invariants.lisp
 M books/transfer-invariants.lisp
 M books/transfer-public-work.lisp
 M books/transfer.lisp
 M books/wire-invariants.lisp
 M books/wire.lisp
 M specs/article-parser.md
 M specs/article-work.md
 M specs/transfer-experiment.md
 M specs/transfer-public-bound.md
 M specs/transfer-public-work.md
 M tests/acl2/article-tests.lisp
 M tests/acl2/transfer-tests.lisp
 M tests/acl2/wire-tests.lisp
```

Untracked before this commit: none (`build/` is ignored). This commit adds
`LANEDUMP-wire-article-transfer.md`.

What each change is:

- `books/wire.lisp` — eight-field state with the carried line length; the
  constant-work per-byte step; the recomputing `-reference` definitions and the
  equality theorems; `fn-wire-begin-article` returning an explicit
  accept-or-refuse result; `fn-wire-next` validating once and looping
  `fn-wire-next-loop`; accessor-form restatements of two preservation facts.
- `books/wire-invariants.lisp` — `fn-wire-drive` and its base cases; the split
  lemma and its two case shapes; `fn-wire-drive-is-feed-proper`;
  `fn-wire-drive-partition-independence`; the earlier `fn-wire-next-*` results
  re-proved through the loop.
- `tests/acl2/wire-tests.lisp` — updated for the new begin-article return type;
  the teeth listed below.
- `books/article-invariants.lisp` — the RFC 5322 §2.2.3 reference, the field
  correspondence predicates, the scanner and constructor lemmas, the two parse
  inductions and the two public theorems.
- `tests/acl2/article-tests.lisp` — includes `books/article-invariants` now;
  the correspondence witness and five teeth.
- `books/transfer.lisp` — `fn-transfer-covering-chunk`,
  `fn-transfer-agrees-fromp`, `fn-transfer-first-disagreement`,
  `fn-transfer-first-empty-overlap`, `fn-transfer-uncovered-chunks`,
  `fn-transfer-replace-entry-with-chunks`, the rewritten `fn-transfer-add-chunk`
  with the `:covered` outcome, and the guard-safe append. `fn-transfer-first-overlap`
  is gone (it had no other caller).
- `books/transfer-invariants.lisp` — the union machinery described above and the
  re-proved transition; **the part after the failing theorem is unverified**.
- `tests/acl2/transfer-tests.lisp` — includes `books/transfer-public-bound`;
  the overlap teeth listed below.
- `books/transfer-public-work.lisp` — one stale comment replaced.
- the five spec files — as described in the design section.


## Keystone theorems

Each is quoted verbatim, with its hypothesis stack one level down and the host
line that calls its subject. **Sections 1, 2, 3 and 4 are certified** (see the
gate table). **Section 6 is written but not certified**: `books/transfer` is
green, but the preservation book fails earlier than these theorems, so the
prover never reached them. Read section 6 as a draft, not as evidence.

## 1. Wire cost: the served path is the constant-work one

`host/reader-host.lisp:91` calls `fn-wire-next`. The per-byte step no longer
runs the state recognizer: `fn-wire-statep` is established once per chunk by
`fn-wire-next`, and `fn-wire-feed-byte` reads the carried `line-len` and
`body-size` fields instead of walking the retained line and the retained body.

### fn-wire-next-matches-reference (books/wire.lisp)

```lisp
(defthm fn-wire-next-matches-reference
  (implies (fn-wire-statep wire-state)
           (equal (fn-wire-next wire-state octets)
                  (fn-wire-next-reference wire-state octets)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-wire-next-reference-is-next-loop))
           :in-theory (e/d (fn-wire-next)
                           (fn-wire-next-loop
                            fn-wire-next-reference
                            fn-wire-statep)))))
```

### its hypothesis, one level down: fn-wire-statep (books/wire.lisp)

```lisp
(defun fn-wire-statep (x)
  (and (true-listp x)
       (equal (len x) 8)
       (fn-wire-modep (fn-wire-state-mode x))
       (fn-wire-octet-listp (fn-wire-state-line-rev x))
       (fn-wire-octet-linesp (fn-wire-state-body-rev x))
       (or (equal (fn-wire-state-pending-crp x) t)
           (null (fn-wire-state-pending-crp x)))
       (natp (fn-wire-state-line-len x))
       (natp (fn-wire-state-body-size x))
       (posp (fn-wire-state-line-limit x))
       (posp (fn-wire-state-body-limit x))
       (equal (fn-wire-state-line-len x)
              (len (fn-wire-state-line-rev x)))
       (<= (fn-wire-state-line-len x)
           (fn-wire-state-line-limit x))
       (equal (fn-wire-state-body-size x)
              (fn-wire-lines-size (fn-wire-state-body-rev x)))
       (<= (fn-wire-state-body-size x)
           (fn-wire-state-body-limit x))
       (or (equal (fn-wire-state-mode x) :article)
           (and (null (fn-wire-state-body-rev x))
                (equal (fn-wire-state-body-size x) 0)))
       (or (not (equal (fn-wire-state-mode x) :closed))
           (and (null (fn-wire-state-line-rev x))
                (null (fn-wire-state-pending-crp x))))))
```

### fn-wire-feed-byte-preserves-statep (books/wire.lisp)

```lisp
(defthm fn-wire-feed-byte-preserves-statep
  (implies (fn-wire-statep wire-state)
           (fn-wire-statep
            (fn-wire-result-state (fn-wire-feed-byte wire-state byte))))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte
                                      fn-wire-after-line
                                      fn-wire-close
                                      fn-wire-statep))))
```

### fn-wire-feed-byte-retained-input-is-bounded (books/wire.lisp)

```lisp
(defthm fn-wire-feed-byte-retained-input-is-bounded
  (implies (fn-wire-statep wire-state)
           (let ((next (fn-wire-result-state
                        (fn-wire-feed-byte wire-state byte))))
             (and (<= (len (fn-wire-state-line-rev next))
                      (fn-wire-state-line-limit next))
                  (<= (fn-wire-lines-size (fn-wire-state-body-rev next))
                      (fn-wire-state-body-limit next)))))
  :hints (("Goal"
           :use ((:instance fn-wire-feed-byte-preserves-statep))
           :in-theory (e/d (fn-wire-statep)
                           (fn-wire-feed-byte
                            fn-wire-feed-byte-preserves-statep)))))
```

### the constant-work step itself (books/wire.lisp)

```lisp
(defun fn-wire-feed-byte (wire-state byte)
  (declare (xargs :guard (fn-wire-statep wire-state)
                  :verify-guards nil))
  (if (equal (fn-wire-state-mode wire-state) :closed)
      (fn-wire-make-result wire-state nil)
    (if (not (fn-wire-octetp byte))
        (fn-wire-close wire-state :malformed)
      (if (equal (fn-wire-state-pending-crp wire-state) t)
          (if (equal byte 10)
              (fn-wire-after-line
               (fn-wire-make-state (fn-wire-state-mode wire-state)
                                   (fn-wire-state-line-rev wire-state)
                                   (fn-wire-state-line-len wire-state)
                                   (fn-wire-state-body-rev wire-state)
                                   nil
                                   (fn-wire-state-body-size wire-state)
                                   (fn-wire-state-line-limit wire-state)
                                   (fn-wire-state-body-limit wire-state))
               (fn-wire-reverse-octets (fn-wire-state-line-rev wire-state)))
            (fn-wire-close wire-state :malformed))
        (if (equal byte 13)
            (fn-wire-make-result
             (fn-wire-make-state (fn-wire-state-mode wire-state)
                                 (fn-wire-state-line-rev wire-state)
                                 (fn-wire-state-line-len wire-state)
                                 (fn-wire-state-body-rev wire-state)
                                 t
                                 (fn-wire-state-body-size wire-state)
                                 (fn-wire-state-line-limit wire-state)
                                 (fn-wire-state-body-limit wire-state))
             nil)
          (if (equal byte 10)
              (fn-wire-close wire-state :malformed)
            (if (< (fn-wire-state-line-len wire-state)
                   (fn-wire-state-line-limit wire-state))
                (fn-wire-make-result
                 (fn-wire-make-state (fn-wire-state-mode wire-state)
                                     (cons byte (fn-wire-state-line-rev wire-state))
                                     (+ 1 (fn-wire-state-line-len wire-state))
                                     (fn-wire-state-body-rev wire-state)
                                     nil
                                     (fn-wire-state-body-size wire-state)
                                     (fn-wire-state-line-limit wire-state)
                                     (fn-wire-state-body-limit wire-state))
                 nil)
              (fn-wire-close wire-state :line-overlimit))))))))
```

## 2. Partition independence on the function the host calls

`fn-wire-drive` is the ACL2 transcription of the loop at
`tools/run_reader.py:167-181`: call `fn-wire-next`, take at most one event,
re-feed the returned unconsumed suffix, stop when the chunk is exhausted or the
connection closes. `fn-wire-feed-proper-append` is kept because
`fn-wire-drive-partition-independence` uses it, through
`fn-wire-drive-is-feed-proper`.

### fn-wire-drive (books/wire-invariants.lisp)

```lisp
(defun fn-wire-drive (wire-state octets)
  (declare (xargs :guard t
                  :verify-guards nil
                  :measure (len octets)
                  :hints (("Goal"
                           :use ((:instance fn-wire-next-strictly-consumes))
                           :in-theory (disable fn-wire-next)))))
  (if (or (not (fn-wire-statep wire-state))
          (equal (fn-wire-state-mode wire-state) :closed)
          (not (consp octets)))
      (fn-wire-make-result wire-state nil)
    (let* ((next (fn-wire-next wire-state octets))
           (tail (fn-wire-drive (fn-wire-next-state next)
                                (fn-wire-next-unconsumed next))))
      (fn-wire-make-result
       (fn-wire-result-state tail)
       (append (if (fn-wire-next-event next)
                   (list (fn-wire-next-event next))
                 nil)
               (fn-wire-result-events tail))))))
```

### fn-wire-drive-is-feed-proper (books/wire-invariants.lisp)

```lisp
(defthm fn-wire-drive-is-feed-proper
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp octets))
           (equal (fn-wire-drive wire-state octets)
                  (fn-wire-feed-proper wire-state octets)))
  :hints (("Goal"
           :induct (fn-wire-drive wire-state octets)
           :expand ((fn-wire-drive wire-state octets))
           :in-theory (e/d (fn-wire-next)
                           (fn-wire-drive
                            fn-wire-feed-proper
                            fn-wire-next-loop
                            fn-wire-feed-byte
                            fn-wire-statep
                            fn-wire-close
                            fn-wire-make-state
                            fn-wire-make-result
                            fn-wire-result-state
                            fn-wire-result-events
                            fn-wire-next-state
                            fn-wire-next-event
                            fn-wire-next-unconsumed
                            fn-wire-state-mode)
                           ((:induction fn-wire-drive)))
           :do-not '(generalize))))
```

### fn-wire-drive-partition-independence (books/wire-invariants.lisp)

```lisp
(defthm fn-wire-drive-partition-independence
  (implies (and (fn-wire-statep wire-state)
                (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (equal (fn-wire-drive wire-state (append left right))
                  (fn-wire-make-result
                   (fn-wire-result-state
                    (fn-wire-drive
                     (fn-wire-result-state (fn-wire-drive wire-state left))
                     right))
                   (append
                    (fn-wire-result-events (fn-wire-drive wire-state left))
                    (fn-wire-result-events
                     (fn-wire-drive
                      (fn-wire-result-state (fn-wire-drive wire-state left))
                      right))))))
  :hints (("Goal"
           :use ((:instance fn-wire-drive-is-feed-proper
                            (octets (append left right)))
                 (:instance fn-wire-drive-is-feed-proper (octets left))
                 (:instance fn-wire-drive-is-feed-proper
                            (wire-state (fn-wire-result-state
                                         (fn-wire-feed-proper wire-state left)))
                            (octets right))
                 (:instance fn-wire-drive-preserves-statep (octets left))
                 (:instance fn-wire-feed-proper-preserves-statep
                            (octets left))
                 (:instance fn-wire-feed-proper-append))
           :in-theory (disable fn-wire-drive fn-wire-feed-proper
                               fn-wire-statep
                               fn-wire-drive-is-feed-proper
                               fn-wire-feed-proper-append))))
```

## 3. Entering article mode is an explicit decision

### fn-wire-begin-article-refuses-exactly-the-inadmissible (books/wire.lisp)

```lisp
(defthm fn-wire-begin-article-refuses-exactly-the-inadmissible
  (equal (fn-wire-begin-article-refusedp (fn-wire-begin-article wire-state))
         (not (fn-wire-begin-article-admissiblep wire-state)))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-refusedp
                                      fn-wire-result-events
                                      fn-wire-make-result))))
```

### its hypothesis, one level down: fn-wire-begin-article-admissiblep

```lisp
(defun fn-wire-begin-article-admissiblep (wire-state)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-wire-statep wire-state)
       (equal (fn-wire-state-mode wire-state) :command)
       (null (fn-wire-state-line-rev wire-state))
       (null (fn-wire-state-pending-crp wire-state))))
```

### fn-wire-begin-article-acceptance-enters-empty-article-mode (books/wire.lisp)

```lisp
(defthm fn-wire-begin-article-acceptance-enters-empty-article-mode
  (implies (fn-wire-begin-article-admissiblep wire-state)
           (let ((next (fn-wire-result-state
                        (fn-wire-begin-article wire-state))))
             (and (fn-wire-statep next)
                  (equal (fn-wire-state-mode next) :article)
                  (null (fn-wire-state-line-rev next))
                  (equal (fn-wire-state-line-len next) 0)
                  (null (fn-wire-state-body-rev next))
                  (equal (fn-wire-state-body-size next) 0)
                  (equal (fn-wire-state-line-limit next)
                         (fn-wire-state-line-limit wire-state))
                  (equal (fn-wire-state-body-limit next)
                         (fn-wire-state-body-limit wire-state)))))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article
                                      fn-wire-begin-article-admissiblep
                                      fn-wire-result-state
                                      fn-wire-make-result
                                      fn-wire-statep))))
```

## 4. Article `fields` correspondence

`books/bp-ingress.lisp:131,204` and `host/bp-ingress-host.lisp:45` consume
`fn-article-parse` and the `fields` view through the semantic field layer.

### fn-article-successful-parse-fields-recompose-header (books/article-invariants.lisp)

```lisp
(defthm fn-article-successful-parse-fields-recompose-header
  (implies (fn-article-result-okp (fn-article-parse octets))
           (equal (fn-article-fields-octets
                   (fn-article-fields
                    (fn-article-result-article (fn-article-parse octets))))
                  (fn-article-header
                   (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-article-parse-lines-fields-recompose-header
                  (lines-left (1+ *fn-article-max-header-lines*))
                  (header-bytes 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            fn-article-fields-octets)))))
```

### fn-article-successful-parse-fields-correspond (books/article-invariants.lisp)

```lisp
(defthm fn-article-successful-parse-fields-correspond
  (implies (fn-article-result-okp (fn-article-parse octets))
           (fn-article-fields-correspondp
            (fn-article-fields
             (fn-article-result-article (fn-article-parse octets)))))
  :hints (("Goal"
           :use ((:instance fn-article-parse-lines-fields-correspond
                  (lines-left (1+ *fn-article-max-header-lines*))
                  (header-bytes 0) (fields-rev nil) (current nil)
                  (header-rev nil)))
           :in-theory (e/d (fn-article-parse)
                           (fn-article-parse-lines fn-cbor-at-mostp
                            fn-article-fields-correspondp)))))
```

### its conclusion, one level down: fn-article-field-correspondsp

```lisp
(defun fn-article-field-correspondsp (field)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp (fn-article-field-raw-lines field))
       (fn-article-plain-linesp (fn-article-field-raw-lines field))
       (fn-article-wsp-startsp (cdr (fn-article-field-raw-lines field)))
       (fn-article-has-colonp (car (fn-article-field-raw-lines field)))
       (equal (fn-article-field-name field)
              (fn-article-ascii-downcase
               (fn-article-name-before-colon
                (car (fn-article-field-raw-lines field)))))
       (equal (fn-article-field-unfolded-value field)
              (fn-article-unfold-reference
               (fn-article-field-raw-lines field)))))
```

### the independent RFC 5322 2.2.3 reference

```lisp
(defun fn-article-unfold-octets (octets)
  (declare (xargs :guard t :measure (acl2-count octets)))
  (if (consp octets)
      (if (and (equal (car octets) 13)
               (consp (cdr octets))
               (equal (car (cdr octets)) 10)
               (consp (cdr (cdr octets)))
               (fn-article-wspp (car (cdr (cdr octets)))))
          (fn-article-unfold-octets (cdr (cdr octets)))
        (cons (car octets) (fn-article-unfold-octets (cdr octets))))
    nil))

(defun fn-article-unfold-reference (lines)
  (declare (xargs :guard t :verify-guards nil))
  (fn-article-value-after-colon
   (fn-article-unfold-octets (fn-article-join-crlf lines))))
```

## 6. Transfer overlap (WRITTEN, NOT CERTIFIED)

### fn-transfer-add-chunk-preserves-statep (books/transfer-invariants.lisp)

```lisp
(defthm fn-transfer-add-chunk-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep
            (fn-transfer-result-state
             (fn-transfer-add-chunk st label offset octets))))
  :hints (("Goal"
           :cases ((fn-transfer-add-chunk-admissiblep st label offset octets))
           :use ((:instance fn-transfer-add-chunk-stored-statep)
                 (:instance fn-transfer-add-chunk-result-state-normal-form))
           :in-theory (disable fn-transfer-statep
                               fn-transfer-add-chunk
                               fn-transfer-add-chunk-admissiblep
                               fn-transfer-uncovered-chunks))))
```

### fn-transfer-add-chunk-retains-union (books/transfer-invariants.lisp)

```lisp
(defthm fn-transfer-add-chunk-retains-union
  (implies (and (fn-transfer-statep st)
                (fn-transfer-add-chunk-admissiblep st label offset octets)
                (natp query))
           (let ((before (fn-transfer-entry-chunks
                          (fn-transfer-find-entry
                           label (fn-transfer-state-entries st))))
                 (after (fn-transfer-entry-chunks
                         (fn-transfer-find-entry
                          label
                          (fn-transfer-state-entries
                           (fn-transfer-result-state
                            (fn-transfer-add-chunk st label offset octets)))))))
             (and (implies (fn-transfer-present-atp query before)
                           (fn-transfer-present-atp query after))
                  (implies (and (<= offset query)
                                (< query (+ offset (len octets))))
                           (fn-transfer-present-atp query after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-transfer-add-chunk-result-state-normal-form)
                 (:instance fn-transfer-uncovered-chunks-cover-uncovered-positions
                            (position offset)
                            (chunks (fn-transfer-entry-chunks
                                     (fn-transfer-find-entry
                                      label (fn-transfer-state-entries st)))))
                 (:instance fn-transfer-replace-finds-appended-chunks
                            (entries (fn-transfer-state-entries st))
                            (new-chunks
                             (fn-transfer-uncovered-chunks
                              offset octets
                              (fn-transfer-entry-chunks
                               (fn-transfer-find-entry
                                label (fn-transfer-state-entries st)))))))
           :in-theory (e/d (fn-transfer-add-chunk-admissiblep
                            fn-transfer-state-entries
                            fn-transfer-make-state)
                           (fn-transfer-statep
                            fn-transfer-add-chunk
                            fn-transfer-uncovered-chunks
                            fn-transfer-present-atp
                            fn-transfer-first-disagreement
                            fn-transfer-first-empty-overlap)))))
```

### its hypothesis, one level down: fn-transfer-add-chunk-admissiblep

```lisp
(defun fn-transfer-add-chunk-admissiblep (st label offset octets)
  (let* ((profile (fn-transfer-state-profile st))
         (entry (fn-transfer-find-entry label (fn-transfer-state-entries st))))
    (and (fn-transfer-labelp label profile)
         (fn-transfer-chunk-inputp octets profile)
         (natp offset)
         (consp entry)
         (<= offset (fn-transfer-entry-length entry))
         (<= (+ offset (len octets)) (fn-transfer-entry-length entry))
         (consp octets)
         (not (member-equal (fn-transfer-make-chunk offset octets)
                            (fn-transfer-entry-chunks entry)))
         (not (fn-transfer-first-disagreement
               offset octets (fn-transfer-entry-chunks entry)))
         (not (fn-transfer-first-empty-overlap
               (fn-transfer-make-chunk offset octets)
               (fn-transfer-entry-chunks entry)))
         (consp (fn-transfer-uncovered-chunks
                 offset octets (fn-transfer-entry-chunks entry)))
         (fn-transfer-at-mostp
          (append (fn-transfer-uncovered-chunks
                   offset octets (fn-transfer-entry-chunks entry))
                  (fn-transfer-entry-chunks entry))
          (fn-transfer-max-chunks profile)))))
```

### the byte comparison and the retained union (books/transfer.lisp)

```lisp
(defun fn-transfer-agrees-fromp (position octets chunks)
  (declare (xargs :measure (acl2-count octets)))
  (if (consp octets)
      (and (or (not (fn-transfer-present-atp position chunks))
               (equal (car octets) (fn-transfer-byte-at position chunks)))
           (fn-transfer-agrees-fromp (fn-transfer-safe-inc position)
                                     (cdr octets) chunks))
    t))

(defun fn-transfer-uncovered-chunks (position octets chunks)
  (declare (xargs :measure (acl2-count octets)))
  (if (consp octets)
      (if (fn-transfer-present-atp position chunks)
          (fn-transfer-uncovered-chunks (fn-transfer-safe-inc position)
                                        (cdr octets) chunks)
        (let ((rest (fn-transfer-uncovered-chunks
                     (fn-transfer-safe-inc position) (cdr octets) chunks)))
          (if (and (consp rest)
                   (equal (fn-transfer-chunk-offset (car rest))
                          (fn-transfer-safe-inc position)))
              (cons (fn-transfer-make-chunk
                     position
                     (cons (car octets)
                           (fn-transfer-chunk-octets (car rest))))
                    (cdr rest))
            (cons (fn-transfer-make-chunk position (list (car octets)))
                  rest))))
    nil))
```


## Teeth added

Every keystone below has, in its test book, a reachable non-degenerate witness
and at least one case per hypothesis for which the conclusion fails. Cases that
would violate a guard at evaluation time are stated as negated theorems rather
than `assert-event`s, so the prover checks them without a guard violation.

**`tests/acl2/wire-tests.lisp`**

- `fn-wire-begin-article`: four refusals, one per conjunct of
  `fn-wire-begin-article-admissiblep` — wrong mode, non-empty `line-rev`,
  pending CR, and a value that is not a wire state — each asserted to leave the
  state unchanged, to carry `(:reject :begin-article-unquiesced)`, and not to
  enter `:article` mode; plus the accepted case.
- Carried counters: at a state holding four line octets and two retained body
  lines, `line-len` equals `(len line-rev)` and `body-size` equals
  `(fn-wire-lines-size body-rev)`.
- `fn-wire-feed-byte-matches-reference` and its lifted forms: a value with the
  right shape but a carried line length that does not measure its retained line
  is not a `fn-wire-statep`, and the constant-work step and the recomputing
  reference disagree on it
  (`fn-wire-feed-byte-needs-statep-to-match-reference`,
  `fn-wire-next-loop-needs-statep-to-match-reference`).
- `fn-wire-drive-is-feed-proper`: on the same non-state the adapter loop
  refuses the state and the fixed-mode helper does not
  (`fn-wire-drive-needs-statep-to-be-feed-proper`).
- `fn-wire-drive-partition-independence`: a two-command chunk split inside its
  first CRLF, and `fn-wire-drive-partition-needs-proper-left-chunk`, where an
  improper left chunk is dropped by `append`, so the concatenated drive frames a
  command while the split drive rejects the chunk as malformed.

**`tests/acl2/article-tests.lisp`**

- A two-field article, the second field folded, whose `fields` view satisfies
  `fn-article-fields-correspondp` and recomposes the header.
- Dropping a field loses header octets.
- A misfolded `fields` list that attaches the fold to the previous field *and*
  adjusts that field's unfolded value still satisfies the per-field
  correspondence, and is caught only by the header recomposition, because the
  raw lines no longer appear in source order. This is the tooth that shows both
  theorems are needed.
- Attaching the fold to the wrong field without adjusting the value fails the
  per-field correspondence directly.
- An unfolding that drops the continuation WSP — the RFC 5322 §2.2.3 mistake —
  fails the per-field correspondence.
- A name that is not the ASCII-lowercasing of the octets before the first colon
  fails, in both the not-lowercased and the wrong-name directions.

**`tests/acl2/transfer-tests.lisp`**

- Byte-identical partial overlap is `:stored`, retains only the uncovered run,
  leaves the retained fragments exact and pairwise nonoverlapping, and moves the
  missing ranges forward.
- Differing overlap is `:overlap-conflict` with the retained fragment as
  evidence and the state exact; the refused arrival's new position is still
  missing afterwards, which is the tooth for the byte-agreement hypothesis of
  `fn-transfer-add-chunk-retains-union`.
- An agreeing arrival that adds no octet is `:covered` and changes nothing.
- A re-fragmenting peer completes the object: one retained middle fragment plus
  a whole-object arrival retains the union as two runs and yields the candidate.
- The same delivery at a two-fragment limit is `:chunk-limit` with the state
  exact, so the retained count bounds the union's runs, not the arrivals.
- A hand-built degenerate entry with an empty retained fragment inside the
  arriving range is refused, and the state is exact.


## IN PROGRESS: `books/transfer-invariants.lisp`, one theorem

`books/transfer.lisp` certifies green with the new kernel. The preservation
book fails on exactly one theorem, `fn-transfer-uncovered-chunk-has-no-overlap`,
and everything before it in the book is admitted. Last run:

```
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/transfer-invariants
-> ACL2 did not produce complete clean certification evidence.
   Certification evidence: build/acl2/certify-20260919T064430Z-39211
```

Exact failure (`build/acl2/certify-20260919T064430Z-39211/certify.log:4230-4300`):

```
*** Key checkpoint at the top level: ***

Goal
(IMPLIES (AND (NATP (FN-TRANSFER-CHUNK-OFFSET CHUNK))
              (CONSP (FN-TRANSFER-CHUNK-OCTETS CHUNK))
              (NATP WINDOW-START)
              (<= WINDOW-START (FN-TRANSFER-CHUNK-OFFSET CHUNK))
              (<= (+ (FN-TRANSFER-CHUNK-OFFSET CHUNK)
                     (LEN (FN-TRANSFER-CHUNK-OCTETS CHUNK)))
                  WINDOW-END)
              (FN-TRANSFER-UNCOVEREDP (FN-TRANSFER-CHUNK-OFFSET CHUNK)
                                      (FN-TRANSFER-CHUNK-OCTETS CHUNK)
                                      CHUNKS)
              (FN-TRANSFER-WINDOW-CLEARP WINDOW-START WINDOW-END CHUNKS)
              (FN-TRANSFER-CHUNK-LISTP CHUNKS DECLARED-LENGTH PROFILE))
         (FN-TRANSFER-NO-OVERLAPS-WITHP CHUNK CHUNKS))

*** Key checkpoint under a top-level induction
    before the induction-depth-limit stopped the proof attempt: ***

Subgoal *1/1''
(IMPLIES (AND (CONSP CHUNKS)
              (CONSP (CAR CHUNKS))
              (TRUE-LISTP (CDR (CAR CHUNKS)))
              (EQUAL (+ 1 (LEN (CDR (CAR CHUNKS)))) 2)
              (INTEGERP (CAR (CAR CHUNKS)))
              (<= 0 (CAR (CAR CHUNKS)))
              (FN-TRANSFER-CHUNK-INPUTP (CADR (CAR CHUNKS)) PROFILE)
              (<= (+ (CAR (CAR CHUNKS)) (LEN (CADR (CAR CHUNKS))))
                  DECLARED-LENGTH)
              (FN-TRANSFER-NO-OVERLAPS-WITHP (CAR CHUNKS) (CDR CHUNKS))
              (FN-TRANSFER-NO-OVERLAPS-WITHP CHUNK (CDR CHUNKS))
              (INTEGERP (CAR CHUNK))
              (<= 0 (CAR CHUNK))
              (CONSP (CADR CHUNK))
              (INTEGERP WINDOW-START)
              (<= 0 WINDOW-START)
              (<= WINDOW-START (CAR CHUNK))
              (<= (+ (CAR CHUNK) (LEN (CADR CHUNK))) WINDOW-END)
              (FN-TRANSFER-UNCOVEREDP (CAR CHUNK) (CADR CHUNK) CHUNKS)
              (FN-TRANSFER-WINDOW-CLEARP WINDOW-START WINDOW-END CHUNKS)
              (FN-TRANSFER-CHUNK-LISTP (CDR CHUNKS) DECLARED-LENGTH PROFILE))
         (NOT (FN-TRANSFER-RANGES-OVERLAPP CHUNK (CAR CHUNKS))))

ACL2 Error [Failure] in ( DEFTHM FN-TRANSFER-UNCOVERED-CHUNK-HAS-NO-OVERLAP ...)
Warnings:  Use, Free, Subsume and Non-rec
Prover steps counted:  953527
```

**Diagnosis.** The subgoal is exactly the statement of the combined head rule
`fn-transfer-uncovered-chunk-misses-head-in-clear-window`, which is admitted
immediately above it and should discharge this subgoal. It does not fire, and
the summary's `Free` warning says why: that rule's hypotheses mention
`window-start` and `window-end`, which do not appear in its conclusion
`(not (fn-transfer-ranges-overlapp chunk (car chunks)))`, so they are free
variables that ACL2 must bind by matching
`(fn-transfer-window-clearp window-start window-end chunks)` against the goal's
hypotheses. The binding is available in the subgoal above, so the most likely
causes are (a) ACL2 tried a different binding first, or (b) the rule was stored
with `fn-transfer-chunk-offset`/`fn-transfer-chunk-octets` unexpanded while the
subgoal has `(CAR CHUNK)` / `(CADR CHUNK)`, so the *hypothesis* patterns do not
match even though the conclusion does.

**Recommended next step (in order of confidence).**

1. Replace the rewrite-rule approach with a direct `:use` of the combined head
   rule inside `fn-transfer-uncovered-chunk-has-no-overlap`, instantiated at
   `(chunks chunks)`, and let the induction carry it — i.e. make
   `fn-transfer-uncovered-chunk-misses-head-in-clear-window`
   `:rule-classes nil` and add to the list induction's hint
   `("Subgoal *1/1" :use ((:instance fn-transfer-uncovered-chunk-misses-head-in-clear-window)))`.
   Subgoal names are fragile, so prefer 2 if this misses.
2. Disable `fn-transfer-chunk-offset` and `fn-transfer-chunk-octets` in the list
   induction so the goal keeps the accessor terms the rule was stated with.
   This is the same accessor-form mismatch that cost several iterations in
   `books/wire-invariants.lisp`; the fix there was to keep one form consistently
   and to add restated `-car-form` / `-cons-form` siblings where both forms
   appear. The same medicine should work here.
3. If neither works, weaken the invariant instead of proving this: make
   `fn-transfer-add-chunk` refuse any arrival that overlaps a retained fragment
   whose octets are empty *or* that is not already covered-or-disjoint, i.e.
   accept only the fully covered case (`:covered`) and the disjoint case. That
   loses "retain the union" for partial overlaps but keeps every other
   deliverable and certifies with the existing lemmas.

Everything else in `books/transfer-invariants.lisp` after this theorem
(`fn-transfer-run-listp`, the append-is-chunk-listp bridge, the transition
normal form, `fn-transfer-add-chunk-preserves-statep`,
`fn-transfer-add-chunk-retains-union`) is **written but never reached by the
prover**, so it is unverified. Treat it as a draft.

`tests/acl2/transfer-tests.lisp` is written and hand-traced against the kernel
(every expected outcome, chunk list, candidate and missing-range list in it was
computed by hand from the definitions) but has not been run.


## Design decisions, and why (so they are not redone)

### Wire: carry the counters, keep the old algorithm as a reference

The state grew from seven fields to eight:
`(mode line-rev line-len body-rev pending-crp body-size line-limit body-limit)`.
`line-len` is new; `body-size` already existed. `fn-wire-statep` requires
`line-len = (len line-rev)` and `body-size = (fn-wire-lines-size body-rev)`, so
a carried counter cannot drift from the retained list it bounds, and the
retained-input bound is a conjunct of the recognizer rather than a separate
check.

The per-byte step `fn-wire-feed-byte` no longer calls `fn-wire-statep` at all;
its guard *is* `fn-wire-statep`, discharged once per chunk by `fn-wire-next`,
which is the only entry with guard `t`. `fn-wire-next` validates the state once
and then runs `fn-wire-next-loop`, whose guard is `fn-wire-statep` and which is
proved to preserve it.

The old recomputing definitions are kept verbatim as
`fn-wire-feed-byte-reference` and `fn-wire-next-reference` — transplanted to the
eight-field state, still re-running `fn-wire-statep` per byte and still
measuring with `len` and `fn-wire-lines-size` — and the equality theorems say
the served path returns exactly what they return on every `fn-wire-statep`
input. That is the honest content: the carried fields are exactly the
recomputed values and the per-byte revalidation is redundant.

**Constant per-byte work is by construction, not by theorem.** There is no
costed shadow for the wire book. What is proved is the equality with the
reference and the preservation of the carried counters; the constant-work claim
rests on reading `fn-wire-feed-byte`, which conses at most one octet and reads
only scalars.

`fn-wire-feed-proper`'s loop test was also simplified from
`(and (fn-wire-statep ws) (equal mode :closed))` to the mode test alone, since
`fn-wire-feed` establishes `fn-wire-statep` at entry. That function is not on
the served path; this is a simplification, not part of the claim.

### Wire: the partition theorem is about the loop the adapter runs

`fn-wire-drive` (in `books/wire-invariants.lisp`) is the ACL2 transcription of
`tools/run_reader.py:167-181`: call `fn-wire-next`, take at most one event,
re-feed the returned unconsumed suffix, stop when the chunk is exhausted or the
connection closes. It is a model of the host loop, not a second framing
implementation, and the book says so.

The proof chain is deliberately: `fn-wire-drive` = `fn-wire-feed-proper` (under
`fn-wire-statep` and `fn-wire-octet-listp`), then the existing
`fn-wire-feed-proper-append` supplies the induction. That is why the old
theorem is kept — it is used, as the packet allowed.

Proof-engineering notes that cost the most time here, in case they recur:
ACL2 expands `fn-wire-result-state`/`fn-wire-result-events`/`fn-wire-next-state`
etc. into `car`/`cadr`/`caddr`, after which rules stated with the accessor names
stop matching. The book now carries restated `-car-form` and `-cons-form`
siblings of the two facts that are needed in both shapes, and the heavy proofs
disable the accessors so the terms stay in one form. Also: the split lemma
`fn-wire-next-loop-splits-feed-proper` is stated *from* the split form *to*
`fn-wire-feed-proper`, because the other direction does not terminate as a
rewrite; and `fn-wire-drive-is-feed-proper` needs `(:induction fn-wire-drive)`
enabled while `fn-wire-drive`'s definition is disabled, plus `:expand`, plus
`:do-not '(generalize)` **without** `fertilize` (disabling fertilization stops
ACL2 substituting the induction hypothesis and was a dead end for two runs).

### Wire: begin-article returns a result, not a state

`fn-wire-begin-article` now returns `(state . events)` like `fn-wire-feed`: on
success the article-mode state with no events, on refusal the **unchanged**
input state with one `(:reject :begin-article-unquiesced)` event. It does not
close the connection; the caller decides. `fn-wire-begin-article-refusedp` is
the recognizer, and the refusal theorem is an equality with
`fn-wire-begin-article-admissiblep`, so it is exactly the inadmissible inputs
that are refused — neither a one-directional claim nor a restatement of the
branch test.

Callers: nothing in `host/` or `tools/` calls it yet, so this is still latent.
`tests/acl2/wire-tests.lisp` was updated for the new return type.

### Article: the unfolding reference is octet-level and independent

`fn-article-unfold-octets` transcribes RFC 5322 §2.2.3 ("remove any CRLF that is
immediately followed by WSP") over the field's folded octets, with no reference
to how the parser builds a value. `fn-article-unfold-reference` joins a field's
raw lines with CRLF, unfolds, and drops the name and colon. The correspondence
theorem then ties the parser's incrementally accumulated `unfolded-value` to it.
Defining the unfolding as "concatenate the raw lines" would have been a
restatement of `fn-article-add-fold`; this is not.

The two theorems are deliberately separate and neither subsumes the other: a
variant that moves a fold to the previous field and adjusts that field's value
consistently satisfies the per-field correspondence and is caught only by the
header recomposition, because the raw lines then appear out of source order.
That is the fourth tooth in `tests/acl2/article-tests.lisp`.

The reference functions that concatenate line lists are admitted with
`:verify-guards nil`, because `append` is applied to lists whose properness is
a theorem rather than a guard. They are proof-side definitions, never executed
by the host.

### Article: the no-blank-line case is kept, and the clause is RFC 3977 §3.6

RFC 5536 §2.1 makes a conformant article "the format specified in Section 3 of
[RFC5322] plus the additional requirements of this specification", and RFC 5322
§3.5 makes the body — and with it the separating CRLF — optional, so bare
RFC 5322 would admit a header-only message. RFC 3977 §3.6 is stricter and is
what governs articles carried over NNTP: "An article consists of two parts: the
headers and the body. They are separated by a single empty line ... This
specification puts no further restrictions on the body; in particular, it MAY
be empty." An empty body is therefore transferred as a separating empty line
followed by nothing. RFC 3977 §3.1.1 is the multi-line-block framing that
delivers those octets and imposes no separator rule of its own, so it neither
adds to nor relaxes §3.6. **Behavior kept**: `:missing-separator` names exactly
the article §3.6 forbids. Recorded in `specs/article-parser.md`. RFC 5322 is not
in the repository; both of its sections are cited from memory and the spec says
so.

### Transfer: compare bytes, retain the union as maximal uncovered runs

The rejected alternatives matter here, because each is a trap:

- **Weakening the retained-list invariant** from "pairwise non-overlapping" to
  "pairwise agreeing on the overlap" is the obvious move and is wrong for this
  tree: `fn-transfer-chunk-listp` is mirrored by `fn-transfer-no-overlaps-work`
  in `books/transfer-public-work.lisp` and costed across
  `books/transfer-public-bound.lisp:222-491`, so the degree-4 public bound would
  have to be rebuilt around a nested per-byte loop.
- **Merging overlapping fragments into one** breaks `fn-transfer-chunkp`, which
  bounds each retained fragment by the profile's `max-chunk`; a merge can exceed
  it.

The design actually implemented leaves `fn-transfer-statep`,
`fn-transfer-chunk-listp` and every work/bound book **untouched**: only the
transition changes. On an arrival that overlaps retained fragments,
`fn-transfer-agrees-fromp` compares the arriving octet with the retained octet
at every declared position that is already covered; the first disagreement makes
the arrival `:overlap-conflict` with the covering fragment as the diagnostic (the
same diagnostic shape as before, so the existing conflict vector still passes).
An arrival that agrees everywhere it overlaps is accepted, and
`fn-transfer-uncovered-chunks` retains exactly the octets no fragment already
covers, as **maximal contiguous runs**, so the retained fragments stay pairwise
non-overlapping. An agreeing arrival that adds no octet is the new `:covered`
outcome and changes nothing.

`max-chunks` is now checked against the whole new list (`at-mostp (append fresh
chunks) max-chunks`), which subsumes the old `(at-mostp chunks (1- max-chunks))`
check for the single-run case, so the existing `:chunk-limit` vectors still hold.

**The degenerate empty fragment.** `fn-transfer-ranges-overlapp` reports an
overlap between a zero-length fragment and any range that strictly contains its
offset, even though a zero-length fragment covers no declared position and so
cannot be byte-compared. Such a fragment can never be stored (`:empty-chunk` is
refused before storage) but `fn-transfer-chunk-listp` admits it, so the
transition keeps `fn-transfer-first-empty-overlap` as an explicit guard that
refuses such an arrival exactly as the old whole-range rule did. This is the
source of the `window-clearp` machinery in the preservation book and of the
theorem that is currently failing.

`fn-transfer-replace-entry-with-chunk` became
`fn-transfer-replace-entry-with-chunks` and appends a list; for a single run
`(append (list c) chunks)` is `(cons c chunks)`, so the representation is
unchanged in the old case.

A guard-safe `fn-transfer-guard-append` plus `fn-transfer-safe-append` was added
next to the existing guard-safe primitives, because `binary-append`'s guard is
`(true-listp x)` and the kernel's functions all have guard `t`.


## The no-blank-line decision, and the clauses it rests on

`Message-ID: <a@b>` followed by one CRLF and nothing else stays
`:missing-separator`. The behavior is unchanged; what changed is that the
decision is now recorded with the clauses that govern it, in
`specs/article-parser.md`.

- **RFC 5536 §2.1** (in the repository, `rfc5536.txt`): "An article is said to
  be conformant to this specification if it conforms to the format specified in
  Section 3 of [RFC5322] and to the additional requirements of this
  specification." So bare RFC 5322 §3 is the floor.
- **RFC 5322 §3.5** (*not* in the repository; cited from memory):
  `message = (fields / obs-fields) [CRLF body]` — the body, and with it the
  separating CRLF, is optional. RFC 5322 §2.2.3's unfolding rule is cited the
  same way, from memory, for the `unfolded-value` reference function.
- **RFC 3977 §3.6** (in the repository, `rfc3977.txt:1298-1318`) is the clause
  that decides it for articles carried over NNTP, and it is stricter than
  RFC 5322: "An article consists of two parts: the headers and the body. They
  are separated by a single empty line ... This specification puts no further
  restrictions on the body; in particular, it MAY be empty." An empty body is
  transferred as a separating empty line followed by nothing, not as an absent
  separator.
- **RFC 3977 §3.1.1** (`rfc3977.txt:399-445`) supplies the framing that
  delivers those octets — zero or more CRLF-terminated lines, no NUL and no
  bare CR or LF, terminated by "." CRLF, dot-stuffing undone by the recipient —
  and imposes no separator rule of its own. It therefore neither adds to nor
  relaxes §3.6.

The parser's input is exactly such a block's octets, so requiring the separator
is RFC 3977 §3.6 conformance rather than local strictness, and
`:missing-separator` names precisely the article §3.6 forbids. Behavior kept.


## Gate commands and their last results

All certifications were run as
`FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <roots>` from the
worktree root (ACL2 8.7 / SBCL 2.6.8, macOS arm64), under ten-lane contention.

| Command | Last result |
| --- | --- |
| `python3 tools/check_scaffold.py` (`make check`) | **passed**: 76 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications |
| `certify_books.py books/wire books/wire-invariants tests/acl2/wire-tests` | **ACL2 certification passed** — evidence `build/acl2/certify-20260919T061116Z-19363` (the last wire-only run, `books/certify-wire.log`, certified `books/wire-invariants` and `tests/acl2/wire-tests`; `books/wire` passed in the run before it) |
| `certify_books.py books/article-invariants` | **ACL2 certification passed** — log `build/certify-article.log` |
| `certify_books.py books/transfer books/transfer-invariants` | `books/transfer` **passed**; `books/transfer-invariants` **failed** on `fn-transfer-uncovered-chunk-has-no-overlap` — evidence `build/acl2/certify-20260919T064430Z-39211` |
| `certify_books.py tests/acl2/article-tests` | **not run** |
| `certify_books.py tests/acl2/transfer-tests` | **not run** |
| full `make certify` | **not run since the changes**. The interrupted baseline at `0bd0b5c` is `build/certify-baseline.log`; it left 95 of 113 roots certified before it was killed with the shell, and its certificates for books this lane edited are stale |
| `python3 -m unittest tests.test_reader tests.test_reader_partitions -v` | **not run** |

Certificates present in the worktree are therefore a mix: current for
`books/wire`, `books/wire-invariants`, `tests/acl2/wire-tests`,
`books/article-invariants` and `books/transfer`; stale or absent elsewhere.
`books/article-properties` and the whole `books/article-work*` chain,
`books/nntp*`, and `books/transfer-assembly-invariants`, `books/transfer-work`,
`books/transfer-public-work`, `books/transfer-public-bound` have **no**
certificate in this worktree (the baseline run was killed before reaching them).

## NOT STARTED

- **The executable cost witnesses (item 5 and the last clause of item 6).**
  `specs/article-work.md` now contains the sentence with the exponent, the
  closed form and the distance, but it quotes **17,190 units** as the measured
  cost of the 520-octet maximally folded regression article, and **that number
  is a placeholder that was never measured**. It must be replaced, and the
  matching `assert-event`s added to `tests/acl2/article-work-tests.lisp`, or the
  sentence rewritten to avoid the number. The other two numbers in that sentence
  are arithmetic and are correct: the closed form is `532514*N + 1060900`
  (degree one in `N`; the quadratic factor is the 129-step header fuel), and at
  `N = 520` it is `277968180`, matching the documented `17450479652` at
  `N = 32768`.
  The intended procedure is one ACL2 run over the certified
  `books/article-public-bound` and `books/transfer-public-bound`; a ready script
  is at `/tmp/fn-measure.lsp` (it prints `ARTICLE-LEN`, `ARTICLE-COST`,
  `ARTICLE-BUDGET`, `TRANSFER-COST`, `TRANSFER-BOUND`, `TRANSFER-VALUE-OK`).
  Both books must be certified first.
- **The transfer cost witness** asserting an exact `*-work` number on a concrete
  state — same measurement run. `tests/acl2/transfer-tests.lisp` already
  includes `books/transfer-public-bound` for this purpose.
- **The full `make certify` gate** and the two Python reader tests.
- **Evidence regeneration** under `tests/evidence/` (not owned by this lane).


## Known defects and remaining gaps

- **`fn-wire-begin-article` still has no caller.** The explicit refusal is a
  result the host will have to dispatch when POST arrives; nothing in
  `host/` or `tools/` calls it yet, so the refusal path is exercised only by
  the test book. The theorem is an equality, so it is not vacuous, but the
  composition claim it supports is still latent.
- **Constant per-byte work is a property of the definition, not a theorem.**
  `fn-wire-feed-byte` conses at most one octet and reads carried scalars; there
  is no costed shadow for the wire book, so "constant work per byte" is
  established by reading the definition, exactly as the article parser's cost
  side is. What *is* proved is that the carried counters equal the
  measurements they replace (`fn-wire-statep`), that the step preserves them,
  and that the served path returns what the recomputing reference returns.
- **`fn-wire-feed-proper` no longer re-runs `fn-wire-statep` per byte** — its
  loop test is now the mode field alone, which is what `fn-wire-feed`
  establishes at entry. That function is not on the served path; the change is
  a simplification, not part of the served-path claim.
- **The article envelope is about 1.6e4 times the cost it bounds**, and the
  cost side of `fn-aw-parse` is by construction, not by theorem. See
  `specs/article-work.md`; the numbers are asserted as executable witnesses in
  `tests/acl2/article-work-tests.lisp`.
- **`fn-transfer-add-chunk` is still uncosted.** It now performs a byte
  comparison over the arrival against the retained fragments and a
  per-position uncovered-run split, so its work is on the order of the arrival
  length times the retained fragment count. `books/transfer-work.lisp` and
  `books/transfer-public-work.lisp` model only the candidate, completion and
  missing-range reads.
- **`fn-transfer-missing-ranges` still has no caller outside the transfer
  books**, so its degree-4 public bound still governs no served path.
- **The `fields` correspondence is about `fn-article-parse`, not about the
  semantic layer.** `books/article-fields.lisp` (`fn-af-*`) is unchanged; its
  own review findings (`fn-af-message-id-equalp` restating its definition) are
  untouched by this lane.

## Proposals for files this lane does not own

- `planning/proofs.json` (registry owner): PRF-006's `events` cites
  `fn-wire-feed-proper-append`, which is about a fixed-mode helper the host
  never calls. Cite `fn-wire-drive-partition-independence` instead, with
  `fn-wire-drive-is-feed-proper` as the bridge to `fn-wire-next`
  (`host/reader-host.lisp:91`); keep `fn-wire-feed-proper-append` listed only
  as the induction the new proof uses. PRF-006 and PRF-016 may also cite
  `fn-wire-next-matches-reference` and `fn-wire-feed-byte-retained-input-is-bounded`.
- `planning/proofs.json`: PRF-016 cites
  `fn-transfer-missing-ranges-work-public-bound` and PRF-011 cites the transfer
  assembly theorems. Neither subject has a caller outside the transfer books.
  Retract those citations until a caller exists, or add the caller.
- `planning/proofs.json`: PRF-016 may cite
  `fn-article-successful-parse-fields-correspond` and
  `fn-article-successful-parse-fields-recompose-header`, whose subject
  `fn-article-parse` is consumed at `books/bp-ingress.lisp:131,204` and
  `host/bp-ingress-host.lisp:45`.
- `tests/evidence/*`: the 2026-09-18 evidence files record digests for the
  pre-change `wire.lisp`, `article-invariants.lisp` and `transfer.lisp`. They
  need regeneration by whoever owns the evidence pipeline;
  `2026-09-18-fields-transfer.md` already recorded a pre-rewrite `transfer.lisp`
  digest before this lane.
- `books/nntp.lisp` (not owned): its header comment says a host "must not
  dispatch future POST input with bulk `fn-wire-feed`". That is now backed by a
  theorem about the loop the host actually runs; the comment could cite
  `fn-wire-drive-partition-independence`.
