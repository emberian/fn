# The configured owner's relation at open, 2026-09-24

Lane `lane/ocl-at-open`, from dev `0e4b318e`. Commit `6729efec` (book,
teeth, Makefile roots, prefix, registry, host comment) and the evidence
commit that carries this record.

## The gap it closes

advance-projection finding 1: no theorem proved `fn-ocl-relation` of the
owner `fn-owner-recover` installs. The only open-time fact was
`fn-own-open-observed-start-relation`, which is `fn-own-relation` (not the
configured relation) of `fn-own-start` over `fn-sn-open-observed`, a function
the host does not call at recovery. The host comment also cited
`fn-own-open-kind-ok-is-okp`, which is about `fn-sn-open-observed` too. Every
carried keystone stated under `fn-ocl-relation` (served-carried,
commit-path-2, advance-projection) and the T17 premise
`fn-scar-view-indexedp` needed this first link.

## Theorems (`books/owner-recover-ocl.lisp`)

The composition, as `host/owner-host.lisp` `fn-owner-recover` calls it:

| Line | Call |
| --- | --- |
| :186 | `replayed = (fn-cpr-replay config-records records)` |
| :187 | checks `(fn-replay-result-kind replayed) = :ok` |
| :189-190 | `cfg = (fn-cnode-config (fn-replay-result-node replayed))` |
| :191 | `opened = (fn-cpo-open-observed config-records frontier records)` |
| :192-194 | checks `(fn-sn-open-kind opened) = :ok` and the `:recovering` phase |
| :195-201 | installs `(fn-ocfg-make (fn-own-configure (fn-own-start (fn-sn-open-state opened) max-conns) (fn-owner-post-config cfg)) cfg nil nil)`; `fn-owner-post-config` (:80) is `(fn-oag-post-config cfg *fn-record-max-payload*)` |

| Theorem | Statement |
| --- | --- |
| `fn-orec-recover-installs-ocl-relation` (keystone) | If `(natp max-conns)` and `(fn-sn-open-kind (fn-cpo-open-observed configs frontier events))` is `:ok`, then the owner the table above builds satisfies `fn-ocl-relation`, and its owner satisfies `fn-scar-view-indexedp`. |
| `fn-orec-open-kind-ok-is-okp` | For `fn-cpo-open-observed`, kind `:ok` is `fn-sn-open-okp` (the lemma the host comment should have cited). |
| `fn-orec-open-ok-replays-ok` | The open's kind `:ok` gives the replay's kind `:ok`. |
| `fn-orec-replay-ok-has-proper-configs` (over `fn-orec-cpr-loop-ok-has-proper-configs`) | A successful `fn-cpr-replay` consumed a proper configuration list; `true-listp` is derived, not assumed. |
| `fn-orec-started-owner-ocl-relation` | Over any store with `fn-cpo-history-relation`, a proper configuration history and an idle phase, `fn-own-configure` of `fn-own-start` with the store's replayed configuration, no pins and no stage, satisfies `fn-ocl-relation` (any posting configuration). |
| `fn-orec-admin-open-after-recover-keeps-premises` (corollary) | The same hypotheses: `(cdr (fn-ocfg-open oc acfg))` of the recovered owner satisfies both premises, for every `acfg`. |

The helper lemmas `fn-orec-start-view-historyp`, `-view-configp` and
`-config-historyp` do the per-conjunct work: `fn-own-start` refreshes at
every idle phase, `:recovering` among them, so the view is the whole
journal's replay at the store's frontier, which is the store node under
`fn-cst-relation` (`fn-cst-open-success-has-historical-relation` via
`fn-cst-idle-from-observed-history`).

### Hypotheses, and whether the host checks each

| Hypothesis | Host |
| --- | --- |
| `(natp max-conns)` | checked, :184, before anything is installed |
| `(fn-sn-open-kind opened) = :ok` | checked, :192, before anything is installed |

The host's other checks are implied by the second and need no hypothesis:
decoded journals not `:bad` (:183), a non-empty configuration journal
(:184), the replay's kind `:ok` (:187, `fn-orec-open-ok-replays-ok`), and the
`:recovering` phase (:193, `fn-cpo-open-success-exact-image`). Nothing is
evaluated at open beyond what the host already computes.

### Admin open

The native live administration opens a private logical connection before
staging (`host/native/admin.lisp:159` calls `fn-owner-open`, which calls
`fn-ocfg-open` at `host/owner-host.lisp:1337`). The keystones there already
existed: `fn-ocl-open-preserves-historical-relation`
(`books/config-owner-live.lisp`, hypothesis the relation alone, every
`acfg`) and `fn-oix-ocfg-open-keeps-view-indexed`. What was missing was the
first link; the corollary composes it for the first open after recovery.

## Findings

1. **No conjunct of `fn-ocl-relation` fails at open.** Every clause (store
   `fn-cst-relation`, config and view histories, view configuration,
   generation equals configuration-history length, empty connections and pins,
   the ledger, clock, facts and stage) follows from what recovery checks. The
   relation is not stated too strongly for open, and the host needs no new check.
2. **Stale host citation, fixed (comment only, line count kept).** The comment
   above `fn-owner-recover` cited `fn-own-open-observed-start-relation` and
   `fn-own-open-kind-ok-is-okp`, both over `fn-sn-open-observed`. It now cites
   `fn-orec-recover-installs-ocl-relation` and `fn-orec-open-kind-ok-is-okp`.
3. **PRF-028's crash-replay hypothesis is discharged at every recovery.**
   `fn-ocl-config-historyp`, the one hypothesis of
   `fn-ocl-crash-at-any-instant-recovers-the-live-generation`, is a conjunct
   of `fn-ocl-relation`, so it holds for every owner recovery installs.
4. **The rest of the admin sequence is still open (not this lane's scope).**
   After the open, the live arm stages through `fn-ocfg-step (:reconfigure id
   deltas)` (`fn-owner-reconfigure-deltas`), closes through `fn-ocfg-step
   (:close id)` and publishes through `fn-ocl-publish`. I found no theorem
   that `fn-ocfg-step` as a whole, or `fn-ocl-publish`, preserves
   `fn-ocl-relation`. The existing theorems cover `fn-ocfg-close`,
   `fn-ocl-complete` (`fn-ocl-complete-preserves-full-historical-relation`),
   and publish agreeing with complete only on readers
   (`fn-ocl-publish-agrees-with-ocfg-complete-on-readers`).

## Teeth (`tests/acl2/owner-recover-ocl-tests.lisp`)

- **Witness**: the journal the live publication wrote. It is the store of
  config-owner-publish-tests' `*ocp-published*`: three configuration records
  (the third published by `fn-ocl-publish`), two Store events and frontier 8,
  which is what a crash right after publication leaves. The two hypotheses and
  every host check hold. The installed owner is `:recovering` with view
  version 2, and both conclusions hold. The recovered configuration equals
  the live owner's published one (generation 3). The admin open pins
  connection 0 and keeps both premises. A second witness uses the ground
  journal (`*cpo-t-configs*`, `*cpo-t-events*`, frontier 8) with a
  connection bound of 0.
- **must-fail, one per hypothesis**:
  - without `natp`: the same journal opens `:ok`, bound -1, relation false;
  - without the open's `:ok`, with the replay still `:ok`: frontier 1. The
    host's :187 passes, its :192 refuses, and the relation is false;
  - a journal that replays `:fault` (first configuration record lost): the
    replay is `:fault` and the open `:error`, so the host installs nothing,
    and the composed owner is not related.
- The proper-list fact is derived: an improper configuration journal replays `:fault`.
- **Limitation**: the witness journals carry retention events and no article,
  so the view archive has no articles. The view-trie conclusion is checked on
  an empty trie.

## Certification (persvati, ACL2 8.7, toolchain `1b4169e9…`, 2 jobs, 300 s)

- **Run** `run-20260924T221249Z-f2d3`, manifest
  `manifests/certify-20260924T221303Z-1169743.json`, status passed, at
  `6729efec` bytes, `--affected-by books/owner-recover-ocl` plus both roots
  (no other Makefile root includes the new book). The run certified
  `books/owner-recover-ocl` in 4.3 s and `tests/acl2/owner-recover-ocl-tests`
  in 4.1 s. It also certified the two uncached dependencies
  `books/owner-offer-indexed` (4.9 s) and `books/owner-advance-carried` (3.8 s).
- `tools/green_check.py --changed-since 0e4b318e`: "2 changed books, 0 books
  include one; 0 not green at the bytes a merge would carry."
- **`make check`**: its only errors are `planning/ledger.*` and
  `planning/proofs.json` stale (the coordinator regenerates the ledger).
- **Host**: `host/owner-host.lisp` changed in a comment only; no image built.
- Iteration: a persvati `proof_repl.py` session over cached dependencies.
