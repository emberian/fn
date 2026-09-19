# HANDOFF: lane `w4/byte-store` (crash model v2, packets P0-P3)

HEAD: `c96e03a` on branch `w4/byte-store` from `dev` at `ca66782`.
Worktree `build/lanes/w4-byte-store` (remove when the lane lands).

## Per book

| Book | State | Evidence |
| --- | --- | --- |
| `books/byte-store.lisp` | certified | `build/acl2/certify-20260919T220927Z-25033` (this worktree) |
| `books/byte-store-invariants.lisp` | certified | `build/acl2/certify-20260919T220927Z-25052` (this worktree) |
| `books/byte-store-programs.lisp` | certified (against the `dep/store` store books, see below) | `build/acl2/certify-20260919T221729Z-53156` (this worktree) |
| `tests/acl2/byte-store-tests.lisp` | certified (against the `dep/store` store books, see below) | `build/acl2/certify-20260919T221731Z-53206` (this worktree) |

Blocking defect outside this lane: `books/replay` fails
`(verify-guards fn-replay-loop)` at `books/replay.lisp:312` on dev
`ca66782` (checkpoint: `fn-record-p` does not yield `true-listp`; records'
opacity withdrew the shape fact and exports no `fn-record-p-forward-shape`).
Evidence `build/acl2/certify-20260919T220428Z-15597` under this worktree.
Nothing that includes `store-files-traces` can certify until it is fixed;
ASK posted on `planning/deputies/BOARD.md` (2026-09-19 w4-byte-store) and
sent to the store deputy. ANSWER received: `dep/store` carries an interim
local fix for replay (two local forward-chaining facts) and the
convergence lane owns the final form (its one-line local enable, board
"2026-09-19 convergence"). `books/store-files` at `ca66782` also fails
(`(verify-guards fn-sf-replay-node)`, the bp ASK on the board), with or
without that line. To certify the two blocked roots this lane took, into
this worktree only and then restored, the convergence line in
`books/replay.lisp` and the store deputy's realigned `books/store-files`,
`store-files-invariants`, `store-files-traces` from `dep/store` at
`b373104` (`certify-20260919T221549Z-49208`, `-221552Z-40677`,
`-221637Z-51015`, `-221641Z-51203`, `-221650Z-51651`). The evidence
directories below for `byte-store-programs` and `byte-store-tests` are
against those books; the working tree committed here is `ca66782` plus
this lane's files, and the two roots must be recertified once the store
realignment and the replay fix land on `dev`. One consequence already
absorbed: the realigned kernel guards every transition by `fn-sf-statep`,
so the ground runs in `byte-store-programs` drive the initial kernel
state, not `NIL`.

The dependency closure of these books had no certificates in the cache
(`make certs-install` reported them uncached); this lane certified `cbor`,
`cbor-invariants`, `frame-octets`, `wildmat`, `frame-fields`,
`frame-journal`, `frame`, `records` (`certify-20260919T215702Z-5845`) and
stopped at `replay`.

## What the books say

`books/byte-store.lisp` is spec §1.2-1.6 verbatim except for the three
changes recorded in its header and in spec §7 (two extra `fn-bs-statep`
conjuncts, `:ebadf` on a write to an unknown inode, `:eexist` on a
duplicate directory id). The state is an opaque record; the export theory
withdraws the recognizer, the view, the fences, the crash, the admissibility
predicate and every syscall.

`books/byte-store-invariants.lisp`: keystones, verbatim, with their
hypothesis stacks.

```lisp
; K0, model well-formedness (one per transition; the syscalls' argument
; hypotheses are the syscall's domain, the outcome hypotheses say the
; failure's torn selection is admissible)
(defthm fn-bs-crash-preserves-statep
  (implies (and (fn-bs-statep s)
                (fn-bs-crash-choicesp choices (fn-bs-pending s) (fn-bs-unit s)))
           (fn-bs-statep (fn-bs-crash s choices))))
(defthm fn-bs-fence-file-preserves-statep
  (implies (fn-bs-statep s) (fn-bs-statep (fn-bs-fence-file s ino))))
(defthm fn-bs-fence-dir-preserves-statep
  (implies (fn-bs-statep s) (fn-bs-statep (fn-bs-fence-dir s dir))))
(defthm fn-bs-create-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp dir) (fn-bs-namep name))
           (fn-bs-statep (mv-nth 1 (fn-bs-create s dir name outcome)))))
(defthm fn-bs-write-preserves-statep
  (implies (and (fn-bs-statep s) (natp offset) (fn-cbor-octet-listp octets))
           (fn-bs-statep (mv-nth 1 (fn-bs-write s ino offset octets outcome)))))
(defthm fn-bs-fsync-file-preserves-statep
  (implies (and (fn-bs-statep s)
                (or (equal outcome :ok)
                    (fn-bs-crash-choicesp (cdr outcome)
                                          (fn-bs-ops-for-ino (fn-bs-pending s) ino)
                                          (fn-bs-unit s))))
           (fn-bs-statep (mv-nth 1 (fn-bs-fsync-file s ino outcome)))))
(defthm fn-bs-fsync-dir-preserves-statep   ; same shape over fn-bs-ops-for-dir
(defthm fn-bs-link-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp ddir) (fn-bs-namep dname))
           (fn-bs-statep (mv-nth 1 (fn-bs-link s sdir sname ddir dname outcome)))))
(defthm fn-bs-rename-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp ddir) (fn-bs-namep dname))
           (fn-bs-statep (mv-nth 1 (fn-bs-rename s sdir sname ddir dname outcome)))))
(defthm fn-bs-unlink-preserves-statep
  (implies (fn-bs-statep s)
           (fn-bs-statep (mv-nth 1 (fn-bs-unlink s dir name outcome)))))
(defthm fn-bs-mkdir-preserves-statep
  (implies (and (fn-bs-statep s) (fn-bs-dir-idp parent) (fn-bs-namep name)
                (fn-bs-dir-idp id))
           (fn-bs-statep (mv-nth 1 (fn-bs-mkdir s parent name id outcome)))))

; Fences: a completed fence removes the pending set it names and nothing else.
(defthm fn-bs-fence-file-drains-exactly-its-inode
  (and (equal (fn-bs-ops-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino) nil)
       (equal (fn-bs-ops-not-for-ino (fn-bs-pending (fn-bs-fence-file s ino)) ino)
              (fn-bs-ops-not-for-ino (fn-bs-pending s) ino))
       (equal (fn-bs-dirs (fn-bs-fence-file s ino)) (fn-bs-dirs s))))
(defthm fn-bs-fence-dir-drains-exactly-its-directory   ; dual, inodes unchanged
(defthm fn-bs-fence-file-touches-only-its-inode
  (implies (not (equal other ino))
           (equal (fn-bs-durable-content (fn-bs-fence-file s ino) other)
                  (fn-bs-durable-content s other))))
(defthm fn-bs-fence-dir-touches-only-its-directory     ; dual
(defthm fn-bs-refence-after-error-fences-nothing       ; no hypothesis
  (mv-let (r1 s1) (fn-bs-fsync-file s ino outcome)
    (declare (ignore r1))
    (mv-let (r2 s2) (fn-bs-fsync-file s1 ino :ok)
      (declare (ignore r2))
      (equal (fn-bs-inodes s2) (fn-bs-inodes s1)))))

; Crash images: bounded below by the durable state, above by the pending set.
(defthm fn-bs-crash-with-no-choices-is-the-durable-state
  (and (equal (fn-bs-inodes (fn-bs-crash s nil)) (fn-bs-inodes s))
       (equal (fn-bs-dirs (fn-bs-crash s nil)) (fn-bs-dirs s))
       (equal (fn-bs-pending (fn-bs-crash s nil)) nil)))
(defthm fn-bs-lose-everything-is-an-admissible-image
  (fn-bs-crash-imagep s (fn-bs-crash s nil)))
(defthm fn-bs-crash-keeps-fenced-content
  (implies (and (fn-bs-fencedp s ino) (fn-bs-crash-imagep s image))
           (equal (fn-bs-durable-content image ino)
                  (fn-bs-durable-content s ino))))
(defthm fn-bs-crash-keeps-quiet-directory
  (implies (and (fn-bs-dir-quietp s dir) (fn-bs-crash-imagep s image))
           (equal (assoc-equal dir (fn-bs-dirs image))
                  (assoc-equal dir (fn-bs-dirs s)))))
(defthm fn-bs-crash-entry-is-old-or-a-pending-target
  (implies (and (fn-bs-dir-idp dir) (fn-bs-namep name) (fn-bs-crash-imagep s image))
           (member-equal (fn-bs-durable-entry image dir name)
                         (fn-bs-entry-outcomes
                          (fn-bs-ops-for-name (fn-bs-pending s) dir name)
                          (fn-bs-durable-entry s dir name)))))

; Assumptions (proposed home books/assumptions.lisp, P7)
(encapsulate (((fn-assume-physical-crash * *) => *)) ...
  (defthm fn-assume-physical-crash-is-admissible
    (implies (fn-bs-statep s)
             (fn-bs-crash-imagep s (fn-assume-physical-crash s oracle)))))
(encapsulate (((fn-assume-crash-tearp * * *) => *)) ...
  (defthm fn-assume-crash-tear-is-a-model-tear
    (implies (fn-assume-crash-tearp unit observed written)
             (fn-bs-torn-variantp unit observed written)))
  (defthm fn-assume-crash-tear-never-validates-unless-exact
    (implies (and (fn-assume-crash-tearp unit observed written)
                  (not (equal observed written)))
             (not (fn-frame-result-okp (fn-frame-open observed max-payload))))))
```

Hypotheses dropped from the spec's statements, each because no violating
value exists: `fn-bs-statep` on every §1.7 contract; `dir-idp`/`namep` on
`unlink` and on `rename`'s source path (the lookup types them);
`(consp outcome)` on the refence theorem. Hypotheses kept that are the
proof's rather than the model's: `(fn-bs-dir-idp dir) (fn-bs-namep name)` on
the entry keystone (the `-same` alist lemmas need a non-NIL key); dropping
them is an open simplification, recorded in the test book.

Open, not weakened: `fn-bs-view-is-an-admissible-image` (obligation in the
book and spec §7); `fn-bs-image-admissiblep` and its iff; K1, K2, K3 as
commented `defthm`s with their exact obligations at the end of
`byte-store-invariants`.

`books/byte-store-programs.lisp`: `fn-bs-stepp`, `fn-bs-step`, `fn-bs-run`
(§2.1), P-FRONTIER, P-RECORD, P-FINISH, P-RECOVER, P-INIT with a `:cut`
after every durable syscall and the kernel's real event names
(`:frontier-dir`, `:record-dir`); D1-D3 as `assert-event`s with one
violating program each; D4 as `fn-bs-run-stops-at-first-error-by-definition`
(`:rule-classes nil`); D5 (`fn-bs-pending-disjointp`) and K0 asserted on
every state of the ground runs of the four programs with syscalls.

## Teeth (`tests/acl2/byte-store-tests.lisp`)

Reachable witnesses from an initialized store at unit 4 through
`fn-bs-run` of P-RECORD and P-FRONTIER: a torn record
`(10 11 12 13 0 0 0 0 7 7)` from `(:new :zero (:garble 7 7 7 7))`, a
truncated one, a zero-length one; a lost link and a kept link with
`fn-bs-entry-outcomes` = `(nil 2)`; a failed fsync (EIO after one unit;
`fn-bs-fencedp` afterwards; the retry changes nothing); a dropped rename
(old frontier inode 1 survives) and a staging orphan. Composed runs against
the real kernel: P-FRONTIER `:ready` to `:reserved`, `fn-sf-prepare-record`,
P-RECORD to `:completing` with one record, P-FINISH to `:ready` with
success `(0 . 0)`, `fn-sf-crash` `:old :absent` then P-RECOVER back to
`:ready` with an empty pending list. One `assert-event` per hypothesis of
each keystone (a non-keyword directory, a non-string name, a negative
offset, non-octet data, an inadmissible garble, a non-state), or the
statement that no violating value exists.

## Obligations for the store deputy and later packets

- **P3 (K1-K8), store seam.** Define `fn-bs-scan-store`, the frontier codec
  encapsulate, `fn-bs-record-of` over `fn-frame-store-decode`,
  `fn-bs-store-relation` and `fn-bs-pending-matches-phase` (spec §3.1-3.2)
  in `books/byte-store-scan.lisp`. K1 follows from
  `fn-bs-crash-keeps-fenced-content` (every authority inode is fenced by
  the relation), `fn-bs-crash-keeps-quiet-directory` and
  `fn-bs-crash-entry-is-old-or-a-pending-target` for the one pending entry
  the phase allows. K2 is the inhabitation of `fn-sf-crash-imagep`
  (`store-files.lisp:499`) by the scan of every admissible image; K3 from K2
  and `fn-sf-crash-realizes-every-admissible-image`. The relation's
  `fn-bs-pending-matches-phase` must be preserved by every `fn-sf`
  transition the programs observe: that is the store deputy's realignment
  to check against.
- **P2 host half.** Add `faults.at` sites for the new cut names
  (`frontier-created`, `frontier-written`, `record-created`,
  `record-written`, `record-stage-unlinked`, `init-*`) and write
  `tools/transcribe_check.py` against the constants in
  `byte-store-programs`.
- **P1 residual.** `fn-bs-view-is-an-admissible-image` (splice composition
  over unit pieces), `fn-bs-image-admissiblep` with its iff under
  `fn-bs-pending-disjointp`, guard verification of the model, and then the
  "no tears" witness for `fn-assume-crash-tearp`.
- **P7.** Move the two encapsulates to `books/assumptions.lisp` and retire
  `fn-assume-durability-image` / `fn-assume-write-isolation-observe`.
- **Core.** Fix `books/replay.lisp:312` (export `fn-record-p-forward-shape`
  from records or enable `fn-record-record-vocabulary` locally in replay).

## What ran

- `ld` of each book on a scratch driver with `(set-prover-step-limit 2000000)`.
- `FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py <book>`, one
  root at a time; evidence directories in the table above.
- `python3 tools/ledger.py --write`; `make check`: Scaffold OK: 142 Markdown files, 50 requirements, 18 proof targets, 18 scenario specifications.; Ledger OK: cited events exist, are not SUSPECT, and planning/ledger.md is current.; Ledger lints: 60 warnings (export hygiene, teeth form); see planning/ledger.json..
