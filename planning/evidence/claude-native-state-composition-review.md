# Independent review: native shared-state lifetime and composition

Reviewer: Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`622df08`**. 2026-09-21, one bounded pass (~15 min). Source inspection only:
no certificates re-run, no profiles rebuilt, no production edits, no saved
image built. The owner mutex fencing race, the locked-but-fenced store gap and
the shared publisher observer-before-step order are assigned elsewhere and are
not revisited here.

## Headline: the requested defect class is not reachable today

**I did not find a reachable public handler path on which an application
journal replays or decides against a different store/global image than the one
it owns.** The structural coupling that would permit it exists, and nothing
enforces it, but every public entry establishes the invariant by construction.

The chain, exactly:

* `host/native/workflow.lisp:106` `fnn-app-open (store root domain)` takes a
  raw-Lisp `fnn-store` struct and stores it in the journal's `store` slot.
* The ACL2 replay it triggers does **not** use that struct.
  `fnn-app-install:92-103` calls `fn-workflow-install-replay` /
  `fn-bprj-install`, and those read the global:
  `host/workflow-host.lisp:10` `(f-get-global 'fn-store-sn state)`, likewise
  `:54`, `:74`, and `host/bp-receipt-journal-host.lisp:5`.
* So the journal owns *struct* S while its ACL2 image replays against
  *global* `fn-store-sn`. Nothing in `fnn-app-open` checks that they agree; its
  only checks are `(typep store 'fnn-store)` and `(fnn-store-lock-fd store)`
  (`:107-108`).

Why it is nevertheless safe on every reachable path:

* `fnn-app-open` has exactly one caller, `fnn-app-call-with-journal:293`, and
  it opens the store immediately before the journal (`:297-298`).
* `fnn-open-live-store:1307` calls `fnn-bridge-reset` (→ `fn-store-sn-reset`)
  and then `fnn-recover`, which either installs the image through
  `fnn-bridge-recover` → `fn-store-sn-recover` (`io.lisp:1106`) or faults
  (`:1108`). There is no success path that leaves `fn-store-sn` stale or unset.
* All six public workflow/receipt commands (`workflow.lisp:304, 314, 325, 333,
  342, 357`) go through `fnn-app-call-with-journal`.
* The owner does not open application journals at all: `host/native/owner.lisp`
  contains no `fnn-app-*` call. This matters because the owner's store
  deliberately lives in a different global — `host/owner-host.lisp:779`,
  "fn-store-sn, which the owner never sets (its store lives in fn-owner)". Had
  the owner opened a journal, `fn-workflow-install-replay` would have replayed
  against `node = nil` via `(and sn (fn-sn-node sn))`. It does not, so this is
  a hazard the composition has not yet created, not a live defect.

That is the answer to the question as posed. Finding 2 records the unenforced
invariant, at the severity it actually deserves.

## Did native appending stop replaying history?

**At the ACL2 layer, yes.** `fnn-app-preflight:142-153` sends a non-`:config`
record to `fn-workflow-preflight-record` (`host/workflow-host.lisp:64-69`) or
`fn-bprj-preflight`, both of which apply **one** record to the carried state
and read no history. `fnn-app-apply:155-168` likewise calls
`fn-workflow-apply-record` (`:78-92`), single-record. The whole-history
replay function `fn-workflow-preflight-history` (`:71-76`) still exists and
still re-reads `fn-store-sn` and replays the full list, but it has **no native
caller** — its only caller in the tree is `tools/workflow_bridge.py:71`, the
Python bridge. So the removal is real for the native path and the old wrapper
survives for the Python one.

**At the host layer, no** — see Finding 1. A lower wrapper still rebuilds the
whole record history on every append, for a value nothing reads.

## Findings (2)

### F1 — Every append rebuilds the journal's whole record list, which is only ever null-tested. Severity: medium (host cost and retention, not correctness).

`host/native/workflow.lisp:165-167`, in `fnn-app-apply`:

    (setf (fnn-app-journal-records-image journal)
          (append (fnn-app-journal-records-image journal) (list record)))

`append` copies its first argument, so publishing onto a journal holding *n*
durable records allocates a fresh *n+1* cell list; *m* sequential publishes
allocate O(m²) cells and keep the entire decoded history resident in the
journal struct for the session.

The separating observation is what consumes that slot. Every use in the file:

* `:12` the struct field, default `nil`;
* `:103` `fnn-app-install` sets it to the records it just installed;
* `:133-135` `fnn-app-open` sets it to the records read at open;
* `:166-167` the append above;
* `:228` `(unless (null (fnn-app-journal-records-image journal)) ...)` in
  `fnn-workflow-initialize`;
* `:258` the identical guard in `fnn-receipt-initialize`.

After open, the **contents** are never read — only `null` is tested, twice, and
only to refuse re-initialisation. The record list is reconstructed on every
append to answer a boolean.

*Call sequence that exhibits it:* any public path that publishes more than once
against a non-empty journal, e.g. `fnn-command-workflow-enqueue` (`:314`)
against a journal whose `records/` directory already holds *n* records:
`fnn-app-open` reads *n* records, then each `fnn-workflow-enqueue` →
`fnn-app-publish` → `fnn-app-apply` copies all *n* again.

*Outcome implication:* host memory and allocation grow with retained journal
history on the publish path. No durability or ACL2 decision is affected — the
ACL2 owner carries its own state and never sees this slot.

*Smallest correct repair:* replace `records-image` with a count field, e.g.
`(records-count 0)`; `fnn-app-install:103` sets it to `(length records)`,
`fnn-app-apply` increments it, and the two guards at `:228`/`:258` become
`(unless (zerop (fnn-app-journal-records-count journal)) ...)`. Identical
behaviour, no list retained, O(1) per append. If a future consumer needs the
records themselves, it should re-read them rather than pin them.

*Scope limit:* this is a code-level allocation argument from the source, **not
a measurement**. I built no image and ran no benchmark, so I am making no claim
about native node throughput or about what this costs at any particular history
size.

### F2 — `fnn-app-open`'s store/journal pairing is an unchecked convention. Severity: low (latent; no reachable trigger today).

`fnn-app-open:106-108` validates that its `store` argument is a live locked
`fnn-store`, and its docstring promises "Open a journal beside an already-open
Store; never replace its ACL2 image". It never establishes that the ACL2 image
it is about to replay against *is* that store's.

*Separating call sequence — explicitly a misuse of an internal function, not a
reachable handler path:*

    (let ((a (fnn-open-live-store root-a nil)))    ; fn-store-sn := image(A)
      (let ((b (fnn-open-live-store root-b nil)))  ; fn-store-sn := image(B)
        (fnn-app-open a journal-root :workflow)))  ; journal.store = A

Both `fnn-app-open` checks pass on `a`. The journal's `store` slot holds A,
`fn-workflow-install-replay` replays its records against B's node, and the
resulting `fn-workflow-state` binds A's journal history to B's store bindings.
Nothing signals. The same shape would arise from any future caller that opens a
journal while the owner's store (which lives in `fn-owner`, never in
`fn-store-sn`) is the intended one.

*Outcome implication if it ever becomes reachable:* the journal's recovered
work set is computed against the wrong store node, so
`fn-bp-replay-journal`'s binding decisions and the `fn-workflow-recovered`
work-id list describe a store the journal does not own.

*Smallest correct repair:* make the pairing checkable rather than conventional.
`fnn-bridge-reset`/`fnn-recover` already bracket every install of
`fn-store-sn`; give the bridge a monotone epoch counter incremented there, stamp
it into the `fnn-store` struct at open, and have `fnn-app-open` refuse unless
the store's stamp equals the current bridge epoch. That is one integer, it
rejects exactly the sequence above, and it removes nothing.

*Scope limit:* I am not claiming a live defect. The single-caller discipline
holds at `622df08`, and this finding is about the discipline being unexpressed,
which is what makes the owner-composition direction risky when a journal is
eventually opened from a service that keeps its store elsewhere.

## Checked, nothing found — recorded so it is not re-audited

* **Cross-domain global collision.** `:workflow` and `:receipt` journals use
  disjoint globals (`fn-workflow-state`/`-effects`/`-recovered` versus
  `fn-bprj-state`), and `fnn-app-install:92-101` dispatches on the journal's
  own `domain` slot. No aliasing.
* **Sequential opens of the same domain.** `fnn-app-journal-close:14-22`
  releases the lock but does not clear the ACL2 globals; this is harmless
  because `fnn-app-open` unconditionally re-installs through
  `fnn-app-install:92-101`, which resets when the record list is empty.
* **Double initialisation.** I expected `fnn-app-apply`'s `:config` branch
  (`:156-157`) to skip the `records-image` update and so leave the `:228` guard
  open; it does not — `fnn-app-install:103` sets the slot. Guard intact.
* **Frontier accounting.** `journal-frontier` is set once at open (`:130`),
  read at `:172` and advanced incrementally at `:198` from
  `fn-aj-host-operation-successor`. It is not recomputed from the record list.

## Limits of this review

Source-level only, at one revision. I did not build or run the native image, so
nothing here is saved-image evidence, and I have deliberately not inferred
safety from successful admission or from the guard-checking startup assertion.
F1's cost argument is structural, not measured. The reachability arguments rest
on the caller sets I enumerated in this tree; a new caller of `fnn-app-open`
invalidates F2's "not reachable" qualifier, which is the point of F2.
