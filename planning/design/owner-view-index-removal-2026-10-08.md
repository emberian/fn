# Removing the owner view's Message-ID trie (lane s-heap2; follows the 25k heap attribution)

Design and statements, 2026-10-08; no code. Subject: `fn-own-view-index` (books/owner.lisp:515, field 4 of the 10-element view).
Cost it holds: 755 B per article at 25k (`FN-OWNER.0.1.4`: 18.9 MB of conses, 47 per article; the 100k census scales it to ~75 MB), plus the
CPU of `fn-midx-refresh` on every accepted article (books/owner.lisp:1146) and one more retained trie per pinned old view.
Class (b): the catalog already answers the same question (`fn-cat-msgid-seqs`, `fn-cat-visible-at`, books/catalog.lisp:24,29). Measured by
`ha-deep` (coordinator/lanedumps/s-heap2-continue.md); not the retired event index (books/store-node.lisp:164).

## 1. What the trie is, and who reads it on the executed path

The trie is `(fn-midx-build (fn-state-articles (fn-own-view-archive view)))`, kept equal by `fn-midx-refresh`
(`fn-oix-refresh-keeps-correspondence`, owner-offer-indexed.lisp:33; `fn-scar-view-indexedp` = `fn-scj-trie-indexedp`,
served-catalog-join-read.lisp:144). The catalog is joined to the same visible list: `fn-scj-joinp`
(served-catalog-join.lisp:133) = `(fn-cat-view-articles count) = (fn-state-articles (fn-own-view-archive view))` plus marks-below and
seqs-below. Of the 105 defuns that mention the trie (script: s-heap2 `forms.py`; 77 files mention the accessors), the ones the host
actually executes ask four different questions:

| # | reader (file:line) | question asked | fn-cat in scope? |
|---|---|---|---|
| R1 | `fn-pix-history-hasp` (peer-offer-indexed.lisp:35), called by `fn-pgc-decide-offer` (peer-guard-carried.lisp:151,163); trie passed down from `fn-scr-ocfg-read-span` (served-catalog-chain.lisp:1963; the host's read, owner-host.lisp ~4262) | IHAVE/CHECK duplicate test: is Message-ID m known. Fast path only if the node's acceptance articles are `equal` the trie's list, else `fn-peer-history-hasp` scans the node | yes: `fn-scr-ocfg-read-span` has `fn-arena fn-cat`; `fn-pgc-decide-offer` is stobj-free logic and takes the trie as a parameter |
| R2 | `fn-sca-finish` called with `(fn-own-view-index view)` at host/owner-host.lisp:2659 (`fn-owner-finish-submission-synced`) and :2709 (`fn-owner-finish-identity`); inside it `fn-sca-withdraw-targets` (served-catalog-owner.lisp:211), `fn-sca-complete` (:166) | after a post: which cancel targets are no longer shown by the REFRESHED view (T4 withdraws their rows) and is the completed row shown (T2 hides it if not). The catalog is still the OLD view here: the join does not hold yet | yes (fn-cat is the thing being updated); the join is for the pre-refresh view |
| R3 | `fn-sca-load-held-row` (catalog-availability-owner-load.lisp:37-54) via `fn-sca-load-held-rows(-keyed)`; callers: open `fn-owner-install-extended` (owner-recovery-retain.lisp:140), reclaim `fn-owner-orcp-load-columns` (owner-host.lisp:5700) with `fn-owner-orcp-view-index` (:5719) | visible-set test per loaded row: `(fn-midx-lookup (fn-record-msgid h) view-index)` decides commit visible vs commit withdrawn-at-own-index. The catalog is being BUILT, so it cannot answer | no: it is the output |
| R4 | `fn-scr-dispatch-core` etc. carry `live trie lver arts` and each connection pins `fn-served-conn-index` / `fn-served-live-index` (served.lisp:109,193,1198; served-catalog-chain.lisp:147-152,1041) | the catalog arms read the catalog where the reference ("scar") arms read the trie; the trie is carried so that `fn-scr-...-is-scar-...` can be stated | yes |

Everything else in the 77 files is proof-side: the reference arms (`fn-nntp-*`, `fn-pix-msgid-retrieval-indexed`, `fn-ctl-served-held`,
`fn-cu-servedp`, ...) the catalog chain is proved equal to, and invariants that carry `fn-scar-view-indexedp` through every owner step.
To be confirmed by deletion (R4): whether `fn-scr-auth-step` uses `trie`/`arts` at all in the catalog arms; if not, R4 is only a parameter list.

## 2. The catalog expressions and the one Prop each question needs

Already proved and unconditional (books/catalog-view.lisp):
`fn-cat-view-find-article-is-walk` (keystone 1: `(fn-find-article m (fn-cat-view-below i v arena cat))` is the row article of
`(fn-cat-view-find m i v cat)`) and `fn-cat-view-find-is-msgid-column` (keystone 4: that seq is
`(fn-cat-view-last-visible (fn-cat-msgid-seqs m cat) v cat)`). `fn-mxc-lookup` = `fn-midx-lookup` (`fn-midx-concrete-lookup-is-lookup`).

P1 (visible lookup, answers R1's trie half and the visible-set questions; no new premise beyond the owner's join):

    (defthm fn-owner-view-lookup-is-the-catalog-walk
      (implies (and (fn-scj-joinp view fn-arena fn-cat)
                    (fn-midx-string-article-listp (fn-state-articles (fn-own-view-archive view))))
               (equal (fn-find-article m (fn-state-articles (fn-own-view-archive view)))
                      (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs m fn-cat) (fn-cat-count fn-cat) fn-cat)))
                        (if seq (fn-cat-row-article seq fn-arena fn-cat) nil)))))

  Proof sketch: `fn-scj-joinp` rewrites the archive articles to `fn-cat-view-articles count`, then keystones 1 and 4. While the trie
  exists the same statement with `(fn-mxc-lookup m (fn-own-view-index view))` on the left adds the existing premise
  `fn-scj-trie-indexedp`; when the field is gone that premise disappears and `fn-find-article` (the specification) is all that remains.
  Teeth: positive witness = a three-row catalog (m1 visible, m2 withdrawn by a cancel, m3 absent from the catalog) with `fn-scj-joinp`
  asserted by computation, asserting all three lookups and `(fn-midx-lookup m2 ...) = nil`; removal witness = the same catalog with
  row 2's withdrawal mark removed (join's first conjunct fails): the walk returns row 2 where `fn-find-article` over the visible list
  returns nil, so the premise carries weight. Premise inhabitation: `fn-scj-joinp` of a freshly opened view is
  `fn-scj-joinp-of-open` (served-catalog-join-entry.lisp, E for the opens).

P2 (R1, the history test is raw membership, not visible membership). Careful: the fast path holds only when the node's acceptance
articles equal the trie's list; with any withdrawal the code falls back to the O(N) scan `fn-peer-history-hasp` (a node scan of articles
and bindings). So the target is not P1: an offer for a withdrawn article must still say "known". Statement to write:

    (implies (and <the owner/catalog relation that makes the catalog's rows the node's acceptance articles>)
             (equal (fn-peer-history-hasp m node) (and (consp (fn-cat-msgid-seqs m fn-cat)) t)))   ; for string, non-empty m

  Open: `fn-peer-history-hasp` also looks at node BINDINGS (`fn-node-find-binding`), which the catalog does not hold; the Prop
  cannot be written until the lane reads whether bindings are a subset of acceptance msgids (the local lemma `fn-pix-member-of-subset`
  in peer-offer-indexed.lisp is the lead). Relation to name in the statement: the one `fn-sca-join`/`fn-scol-okp` family
  (served-catalog-owner.lisp) states for the whole catalog. This is the Prop that needs S's decision on bindings.
  Teeth (planned): a withdrawn article's id answers known; an id never posted answers unknown; hypothesis removal = a catalog missing a
  row the node has answers unknown where the node scan answers known.

P3 (R3, the load). The loader cannot ask the catalog it is building. Options, cheapest first:
  (a) the open and the reclaim build the trie transiently from the visible list, pass it to the loader and drop it
      (`(fn-midx-build (fn-state-articles archive))`, which is what `fn-own-start` does at owner.lisp:1168 today). No new Prop: the loader
      is called with exactly the value the field holds (`fn-scj-trie-indexedp`). Peak, not retention: ~755 B per article only during
      the open.
  (b) later: replace the test by "m not in the withdrawn set": `(not (member m (withdrawn-msgids view)))`, where the withdrawn list is
      small. Prop: for the loader's rows, `(fn-midx-lookup m (fn-midx-build visible))` = `(not (member-equal m (msgids (fn-own-view-withdrawn view))))`
      under distinct visible Message-IDs (`fn-ocl-view-historyp` already carries distinctness). Needs a duplicates argument: a raw
      list can hold two rows for one id; the first-wins rule must be stated.
  Teeth for (b): a raw list with a duplicate id and a withdrawal; removal = drop distinctness.

P4 (R2, the finish after a post). Hardest, because the catalog is the old view. The index here is the NEW view's visible set. Facts
available without any trie: the refresh's own outputs (`fn-ctl-refresh-visible`, `fn-ctl-visible-add`, the withdrawals it decided).
Statement shape: for the pre-refresh view, `fn-scj-joinp` holds; the new view's `shown(t)` for a cancel target t is
`(and old-shown(t) (not (member t dropped)))` where `dropped` is exactly what `fn-ctl-visible-add` removed, and old-shown is P1 on the
pre-refresh catalog. Decision needed: either (i) the refresh returns `dropped` (a returned value, not a field) and `fn-sca-finish`
takes it instead of the index, or (ii) the finish runs T2 before T4 against the catalog and the lookup becomes P1 afterwards. (i) is
the smaller change. `fn-scj-hitp` (served-catalog-join-step.lisp:112) already states the catalog side of this decision with
`(not (fn-midx-lookup target index))`; the Prop is `fn-scj-hitp` with the index replaced by the dropped list.
  Teeth: a cancel whose target is in the dropped list withdraws that row; a cancel for an already-withdrawn target does not re-mark;
  removal = a `dropped` list missing the target leaves the row visible, the join then fails.

## 3. Threading cost

- R1: low. `fn-scr-ocfg-read-span` and the peer arm already run under `fn-arena fn-cat`; `fn-pgc-decide-offer` (stobj-free) takes a
  boolean `knownp` computed by the caller from the catalog instead of `(trie arts)`; `fn-pgc-peer-command`, `fn-pgc-peer-arm` and
  their ~5 carriers lose the two parameters. The catalog's saturation answer `fn-cat-msgid-saturatedp` must be handled (a saturated
  bucket means unknown to the column; the paged table exports it): P2 needs its case.
- R2: medium. The refresh's return shape gains `dropped`; `fn-own-refresh`, `fn-oix-*`, `fn-owner-finish-*` (host/owner-host.lisp:2627,2694)
  and the join books `served-catalog-join-host-finish/-identity-finish/-complete` change.
- R3: none for (a); `fn-owner-install-extended` and `fn-owner-orcp-load-columns` build the transient locally.
- R4: the pins lose the `index` field (`fn-served-make-conn-pinned` served.lisp:459, `fn-served-pinned-index`, `fn-served-live-make`
  arity). Wide but mechanical; prefer `tools/lisp_rewrite.py` with fixtures over hand edits (AGENTS.md, more than ~5 identical edits).

## 4. The deletion list

- Field and builders: `fn-own-view-index` (owner.lisp:515) and the view's arity (10 -> 9; `fn-own-view-shapep` len), `fn-own-view-make-*`
  (owner.lisp:542-681), `fn-midx-refresh` in `fn-own-refresh` (:1146) and `fn-crf-apply-article` (catalog-refresh.lisp:273),
  `fn-own-refresh-ix` (owner-refresh-indexed.lisp:37), the `fn-midx-build` in `fn-own-start` (:1168; becomes local to open), the same
  in `fn-served-open(-peer)` (served.lisp:2369,2424) and `fn-rdc-selection`.
- Invariants that become vacuous and are deleted, not weakened: `fn-scar-view-indexedp`, `fn-scj-trie-indexedp(-is-view-indexedp)`,
  `fn-oix-refresh-keeps-correspondence/-view-indexed`, the `fn-sjh-okp` trie conjunct, `fn-scj-view-indexesp`, `fn-ocri-viewp` and
  `fn-own-view-okp` index conjuncts.
- Kept as the specification: `msgid-index.lisp` (`fn-midx-*`, `fn-find-article`); `fn-mxc-*` stays for `post-identity-index`,
  `replay-identity-index` (its own tries, `fn-rii-ix-of`; verify whether those are retained in the heap: not seen in the 25k walk) and
  `view-delta-concrete`.
- Files that mention the accessors (77), by kind: owner (32: owner.lisp, owner-offer-indexed, owner-refresh-indexed, owner-open-carried,
  owner-advance-carried, owner-recovery-retain, owner-served-carried, owner-invariants-*, owner-reader-*, owner-reclaim-*, owner-*-read, ...);
  catalog join (19: served-catalog-join*.lisp including the 11 `-host-*`); served/nntp reference arms (13: served.lisp,
  served-carried, served-span, served-available-*, article-stream-owner*, nntp-auth-*, served-tls-prefix, ...); productive-read and
  post (7); catalog chain/refresh (2); config/consumer (2); peer (1); host (1: owner-host.lisp).

## 5. Order of work

1. P1 as a book (new books/owner-view-catalog-lookup.lisp) with teeth; it is a theorem about existing functions, so it lands first and
   cannot go red against the rest of the tree.
2. R1: P2 after S rules on bindings; then `knownp` replaces `(trie arts)` in the peer arm and its carriers; the trie parameter of the
   peer functions is deleted in the same change (no twin).
3. R3 (a): transient build at open and reclaim.
4. R2/P4 with `dropped`.
5. R4: remove the pins' index and the view field (mechanical, last, whole-tree build; per-file green hides a red umbrella).
6. Re-measure `ha-deep` at 25k: `FN-OWNER.0.1.4` must be gone; expect about -755 B per article of conses. Gates: `--affected-by` certify
   per step, `host_check --load`, `interface_emit --check`, then a whole-tree build at step 5.

## 6. Not decided here
- Bindings in P2; the `dropped` return in P4 versus reordering; whether the sibling group-index buckets (`FN-OWNER.0.1.5`, ~90 B per
  article) go the same way (the catalog has the group-number columns).
- This note does not touch the history-root reserve (N-MEM10).
