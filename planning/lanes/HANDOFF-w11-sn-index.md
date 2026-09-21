# w11/sn-index — the index has a carrier, a keyring and a host line

Branch `w11/sn-index`, worktree `build/lanes/w11-sn-index`, from `dev`
`306f1ce`, merged with `dev` `3a2640c`. The packet was the route
[`HANDOFF-w11-node-index`](HANDOFF-w11-node-index.md) §6 named after refusing
the fifth slot on `fn-node-statep`: put the carrier in `fn-sn-statep`.

**It landed.** `fn-sn-state` is `(groups capacity files node keyring index)`,
`fn-sn-finish` grows the index by one cons, and
`host/store-node-host.lisp`'s `fn-store-sn-statement` calls
`fn-sn-statement-lookup` on the value the host holds. Two things about the
route were wrong in the proposal and are corrected here: **the keyring needed
a decision, and the agreement must not be a conjunct of `fn-sn-statep`.**

## 1. The keyring decision, and its cost (D21)

The index is a function of `(store, keyring)` and nothing in the tree holds a
keyring. Three candidates were open; the enumeration is in
`planning/decisions.md` D21 and the verdicts are:

- *Derived from the configuration the record already carries* — **closed by
  inspection.** That configuration is `(groups capacity)`. The nearest thing
  to a key table inside the node is `fn-node-bindings`, and
  `books/node.lisp:126` shows it is msgid-to-archive-obligation. A keyring
  reaches ACL2 today only as a file the operator names (`bin/fn:782`,
  `tools/stx.py:159`).
- *Carried in a form that needs no keyring* — **closed by the invariant's
  shape.** `fn-stx-index-invariantp` is `(equal index (fn-stx-index-of-store
  store keyring))`; two keyrings give two indexes over one store, so an index
  whose keyring is not carried is not determined by the state.
- **Taken: a `keyring` field beside the index**, initialised empty, replaced
  only by `fn-sn-set-keyring`, which recomputes.

**Cost, site by site.**

| Site | What it pays |
| --- | --- |
| `fn-sn-initial` | **nothing, and its arity does not change.** `nil` is a keyring, and `(fn-stx-index-of-store nil k)` is `(fn-stx-index-empty)` for every `k`, so the empty store's agreement holds under any keyring |
| `fn-sn-update` | **nothing, and its arity does not change.** It carries both fields across, which is what gives every transition that already routes through it — `fn-sn-refuse-reservation`, `fn-sn-known-abort`, `fn-sn-sweep-staging` — complete coverage for free |
| `fn-sn-finish` | **one cons**, `fn-stx-index-add` of the accepted article's delta. No walk |
| `fn-sn-crash` | free: the node resets to the empty store, so the recomputation is `(fn-stx-index-empty)` |
| `fn-sn-recover` | **a walk of the replayed store.** Once, at open, not on a served path |
| `fn-sn-set-keyring` | **a walk of the whole store.** A reconfiguration event, not a served path |
| `books/node-config.lisp:405`, `books/replay.lisp:198` | **nothing.** The packet flagged these and they do not bite: they build a fresh `fn-node-make-state`, not a fresh `fn-sn-state`, and neither book is in `books/store-node`'s closure nor above it. Because the carrier is on the SN record, their recomputation lands once, at the `fn-sn-recover` that consumes `fn-sf-replay-node` |

**The open half of the keyring story, stated so nobody assumes otherwise:**
the keyring is supplied per invocation and is **not** in the durable
configuration history, so a restart forgets it and the store answers every
statement query absent until one is installed again. That is fail-closed, and
it is where live reconfiguration of the verification context belongs.

## 2. The correction to the proposal: the agreement is a SECOND recognizer

`HANDOFF-w11-node-index` §6.1 proposed putting
`(fn-stx-index-invariantp (fn-sn-index s) (fn-sn-node s) (fn-sn-keyring s))`
into `fn-sn-statep`. **That would have been the D3 violation the index exists
to remove, made worse.** D20 records that the native host reaches the core
"through the ACL2 executable counterpart of `fnn-call`
(`host/native/io.lisp`), which checks the callee's guard on every call", and
`fn-sn-statep` is the guard of `fn-sn-prepare`, `fn-sn-io`, `fn-sn-finish` and
`fn-sn-recover`. The conjunct there would re-derive the index — and so run
`fn-stx-verdict`, and so verify every signature in the store — **per host
call**. The projection it replaces at least does not verify signatures.

So the split is D20's own cure, one book down:

- `fn-sn-statep` gains only `(fn-prin-keyringp (fn-sn-keyring s))`, which
  walks the keyring and never the store.
- `fn-sn-indexedp` is `fn-sn-statep` plus the agreement. **It is the guard of
  nothing.** It is established at `fn-sn-initial` and proved preserved by
  every transition, and it is the hypothesis of the query keystone.

`tests/acl2/store-node-index-tests` asserts the consequence directly:
`(fn-sn-statep *sni-stale*)` and `(not (fn-sn-indexedp *sni-stale*))` on the
same value.

Also **rejected: a wrapper record above `fn-sn-state`** holding
`(sn keyring index)` with its own five transitions. It would have cost
`books/store-node.lisp` nothing and left all 59 books above it untouched. It
is rejected because `fn-sn-refuse-reservation`, `fn-sn-known-abort`,
`fn-sn-sweep-staging` and `fn-sn-open-observed` move the state without going
through such a wrapper, so any transition it did not mirror would silently
desynchronise the index — and a stale index answers a query wrongly with no
fault anywhere. The slot has no such hole.

## 3. The reachability chain, complete over the host's global

`fn-sn-indexedp`'s usefulness is exactly the completeness of this list.
`grep -n "f-put-global 'fn-store-sn" host/*.lisp` is eight sites plus the new
`fn-store-sn-set-keyring`; every one of them is covered.

| Host site | Transition | Theorem | Book |
| --- | --- | --- | --- |
| `store-node-host.lisp:21` | `fn-sn-initial` | `fn-sn-initial-is-indexed` | `store-node-invariants` |
| `:79` | `fn-sn-open-observed` | `fn-sn-open-observed-is-indexed-by-recomputation` (with `fn-sn-observed-seed-is-indexed`) | `store-observed` |
| `:327` | `fn-sn-io` | `fn-sn-io-preserves-indexedp` | `store-node-invariants` |
| `:363` | `fn-sn-prepare` | `fn-sn-prepare-preserves-indexedp` | `store-node-invariants` |
| `:377` | `fn-sn-refuse-reservation` | `fn-sn-refuse-reservation-preserves-indexedp` | `store-node-resolution` |
| `:392` | `fn-sn-known-abort` | `fn-sn-known-abort-preserves-indexedp` | `store-node-resolution` |
| `:416` | `fn-sn-finish` | **`fn-sn-finish-preserves-indexedp`** | `store-node-invariants` |
| the new `fn-store-sn-set-keyring` | `fn-sn-set-keyring` | `fn-sn-set-keyring-preserves-indexedp-by-recomputation` | `store-node-invariants` |
| — (crash is the kernel's, the host never calls it) | `fn-sn-crash` | `fn-sn-crash-preserves-indexedp-by-recomputation` | `store-node-invariants` |
| — (the sweep returns the store unchanged) | `fn-sn-sweep-staging` | `fn-sn-sweep-staging-preserves-indexedp-by-definition` | `store-sweep` |

`host/bp-ingress-host.lisp:80` installs `(fn-bpi-result-store result)`, whose
store step is `fn-sn-prepare` inside `fn-bpi-ingress-prepare`
(`books/bp-ingress.lisp:457`); **that composition has no `-preserves-indexedp`
of its own and is the one gap in this table.** It is recorded, not papered
over: see §7.

**Which of these are proof events and which are not.** One does work:
`fn-sn-finish-preserves-indexedp`, 11,118 prover steps, where the store grows.
Its keystone is `fn-stx-index-invariant-preserved-by-accept`
(`books/stx-index.lisp`) and its hypothesis is discharged by
`fn-stx-durable-completion-is-an-acceptance` (`books/stx-lace.lisp`), which
`w11/node-index` banked. The prepare and io rows ride on a store-unchanged
equation, named `-unfolds`. The crash, recover, set-keyring and open rows are
named `-by-recomputation` because their conclusion is the recomputation
restated; they are obligations (what they rule out is a transition reaching a
new store with the old index) and they are **not** offered as proof events.

## 4. The host line, and the theorem whose subject it is

    host/store-node-host.lisp  fn-store-sn-statement
      -> fn-sn-statement-lookup      (books/store-node.lisp)
      -> fn-stx-index-lookup         (books/stx-index.lisp)

`fn-sn-statement-lookup`'s guard is `t` and its body mentions neither
`fn-stx-store` nor `fn-stx-lace` nor `fn-node-acceptance`, so the query walks
the index and nothing else. The equating theorem AGENTS.md rule 1 asks for is

```lisp
(defthm fn-sn-statement-lookup-is-the-lace-lookup
  (implies (fn-sn-indexedp s)
           (equal (fn-sn-statement-lookup s id)
                  (fn-lace-lookup (fn-stx-lace (fn-sn-node s) (fn-sn-keyring s))
                                  id)))
  :rule-classes nil)
```

`:rule-classes nil` on purpose: as a rewrite it would put the linear
projection back in place of the cheap query in every proof above it.
`fn-sn-equivocatorp-is-the-lace-equivocator` is the same bridge for
`fn-store-sn-equivocator`.

Reachable from outside: `tools/run_store.py --store <s> statement --id <hex>
[--keyring <file>]`, with `--equivocator`/`--incarnation` and `--index-size`
beside it. The three outcomes stay distinct (D13): found prints the
statement's canonical octets and exits 0, absent exits 1, a keyring this node
cannot read exits 5. Smoke-tested end to end on a fresh store: `init` then
`statement --index-size` prints `0`, exit 0, which is the whole bridge —
`ld` of the host file, the ACL2 call, `fn-store-sn-set-keyring` and
`fn-store-sn-index-size`.

## 5. The witness, and the teeth

`tests/acl2/store-node-index-tests` (new Makefile root, after
`tests/acl2/stx-transit-tests` because it needs both that cluster's crypto
realiser and the store cluster's machine). **No state in it is hand-built**,
which is the defect `w11/node-index` found in the substrate book.

The first run is `fn-sn-initial` → `fn-sn-set-keyring` → four `fn-sn-io` words to
reserve → `fn-sn-prepare` with an article carrying a signed `FN-Statement`
header → three `fn-sn-io` words to publish → `fn-sn-finish`. It pins: the
store 0 → 1 articles and the payload equal to the signed octets; the index
0 → 1 bindings and `<= 1 +` the previous count; the lace `nil` →
`(list *sni-stmt*)`; `fn-sn-indexedp` at every step; the query finding the
statement by its content id and answering `nil` for an absent id; and the two
keystone instances evaluated on the reached state.

- **Tooth, one per hypothesis** (the keystone has one, `fn-sn-indexedp`):
  `*sni-stale*` is `*sni-finished*` with the empty index put back. It is still
  a `fn-sn-statep`, it is not `fn-sn-indexedp`, and the conclusion **fails** —
  the query answers `nil` where the projection answers the statement.
- **Separating witness**: the same run under the empty keyring. Byte-identical
  store, empty index, empty lace, absent query. It separates the two runs by
  the keyring field alone, which is the spine sentence made executable: the
  statement layer refuses authority, never bytes.
- **Crash and recovery**: `fn-sn-crash` resets the store and the index to
  empty and keeps the keyring; `fn-sn-recover` replays the article and
  recomputes the index back to the pre-crash value.
- **`fn-sn-set-keyring`'s own tooth**: a malformed keyring is refused and the
  state is returned unchanged.
- **Reconfiguration after the fact**: installing the keyring on the unkeyed
  run's finished state recomputes to the keyed run's index exactly.
- **A fork, accepted.** A second real transaction puts a second article by
  the same creator at the same `(incarnation, sequence)` slot into the store.
  Both are accepted and stored — refusing the second would let a hostile peer
  delete content by replaying a fork and would destroy the evidence — the
  index holds two bindings, `fn-sn-equivocatorp` answers **T**, the slot still
  answers with the older statement, and both forks are still reachable by
  their own content ids.

**Two findings from `tools/teeth_check.py --report` on the first draft of
this book, both real and both fixed rather than waived.** (1)
`fn-sn-equivocatorp` was asserted FALSE once and TRUE nowhere in the whole
corpus, so a constantly-false definition would have satisfied every
assertion about it — that is what the fork run above exists for, and the
equivocator keystone instance now has both sides TRUE. (2) The keystone
instance on the unkeyed run had NIL on both sides and distinguished nothing;
it is replaced by the assertion that carries the content, that the two runs
give *different* answers for the same id over the same store.
`--evaluate` on the book: 186 probes, prefix ok, exit 0, 186 values.

**A third `--report` finding on this book is the TOOL being wrong, and it is
worth an owner.** After the two real fixes, `--report` still says
`both-sides-degenerate: … both sides of the equality are NIL` of
`(equal (fn-stx-store (fn-sn-node *sni-unkeyed-finished*))
(fn-stx-store (fn-sn-node *sni-finished*)))` — while the same book asserts,
and `certify-book` evaluates to T, that
`(len (fn-stx-store (fn-sn-node *sni-finished*)))` is **1**. So that side is
not NIL and the claim does distinguish something. Twice in a row, deleting
the flagged form moved the identical complaint to the next assertion
(`:245` → `:248` → `:251`), which is the shape of a probe whose values have
desynchronised from the book rather than of three real defects. The second
residual finding, `predicate-never-anchored` on `fn-sn-statement-lookup`, is
the same kind: that function returns a statement, not a boolean, so it never
appears as a bare assertion and the "asserted TRUE" side of the heuristic can
never be satisfied for it. **Neither was worked around by weakening a
witness.** Owner: whoever owns `tools/teeth_check.py`; this book is a small
reproducer, and it uses `make-event`-built constants, which is the obvious
suspect for the probe prefix.

## 6. Certification

`--affected-by books/store-node.lisp --closure` is **132 roots**, because
`books/store-node` gained `(include-book "stx-index")` and 59 books' closures
contain it.

| Box | Run | Evidence | ACL2 | Jobs | Roots | Wall |
| --- | --- | --- | --- | --- | --- | --- |
| hbox | **`run-20260921T023259Z-07ca`** (the final tree, `aecd39b`) | `build/acl2/certify-20260921T023304Z-1454300` | `/tank/fn/acl2-8.7/saved_acl2` sha256 `64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`, SBCL 2.6.8 | 8 | **133 of 133, `passed`** | 203.7 s |
| hbox | `run-20260921T022409Z-7db2` (`8b9aa25`, after `w11/bytestore-k2` landed below this lane) | `build/acl2/certify-20260921T022417Z-1447188` | same | 8 | 131 of 132; the one red root was the foreign `tests/acl2/checkpoint-codec-tests` | 209.1 s |
| hbox | `run-20260921T021436Z-32a0` (before that merge) | `build/acl2/certify-20260921T021450Z-1440524` | same | 8 | 131 of 132 | 209.3 s |
| hbox | `run-20260921T015356Z-e888` (before the fork witness) | `build/acl2/certify-20260921T015400Z-1419906` | same | 8 | 131 of 132 | 218.6 s |
| hbox | `run-20260921T014724Z-9505` (the round before) | `build/acl2/certify-20260921T014734Z-1414858` | same | 8 | 127 of 132; **every book in `books/` passed**, the five reds were test books with a hand-built `fn-sn-make` plus the foreign one | 219.3 s |
| laptop | local, per root | `certify-20260921T012023Z-18407` (`store-node`), `…T012817Z-29647` (`store-node-invariants`), `…T013339Z-38841` (`store-node-resolution`), `…T013506Z-40800` (`store-observed`), `…T013514Z-40943` (`store-sweep`), `…T013134Z-35686` (`store-node-traces`), `…T013924Z-49733` (`store-node-index-tests`) | `/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` | 1 | 7 of 7 | — |

**The control, stated separately from the green.** The FINAL hbox run's own
`source_digests_sha256` (`run-20260921T023259Z-07ca`) was re-checked against
the working tree afterwards: **133 of 133 certified sources byte-identical,
0 changed.** So the certification is a claim about the tree as it stands, not
about an earlier one. `dev` was merged (`3a2640c`) BEFORE that run, not
after, and so was `w11/bytestore-k2`'s landing below this lane
(`books/store-files`, `books/store-files-invariants`, `books/byte-store-scan`,
the new `books/frame-trailer`) -- **which costs this carrier nothing**: the
run over the merged tree has the same 131 of 132 and the same single foreign
failure as the run before it. That re-run is the one this lane's board CHANGE
promised. The earlier runs are kept in the table because one of them is what
identified the four hand-built `fn-sn-make` sites; they are not the evidence
for the final tree.

Per root, hbox: `books/store-node` 0.72 s, `books/store-node-invariants`
**73.53 s** (the cluster's own cost, unchanged in shape — the new theorems are
0.01 to 0.02 s each), `books/store-node-resolution` 1.03 s,
`books/store-observed` 1.00 s, `books/store-sweep` 1.11 s,
`books/store-node-traces` 4.61 s, `books/stx-index` 0.78 s,
`tests/acl2/store-node-index-tests` 0.98 s with 69 `assert-event`s (final
run: `books/store-node` 0.69 s, `books/store-node-invariants` 71.46 s,
`tests/acl2/store-node-index-tests` 0.98 s).
hbox's cache reported `installed 23, kept 178, uncached 77` before the second
run and `installed 103, kept 47, uncached 128` before the first; the run's
passing pairs are published back for the next lane.

**The include-closure cost, measured.** `books/store-node`'s closure goes from
13 books to 26, gaining `article cbor-invariants crypto-seam lace
lace-invariants principal records-invariants statement statement-invariants
stx-carrier stx-index stx-lace stx-verify`, and the **59 books whose closure
contains `books/store-node`** inherit those 13. That is smaller than the
alternative `w11/node-index` priced, where the same 13 would have been
inherited by the 70 books above `books/node`.

**Per-form cost of the new theorems** (laptop, from
`certify-20260921T012817Z-29647`): `fn-sn-finish-preserves-indexedp` 11,118
steps / 0.02 s; `fn-sn-prepare-preserves-indexedp` 5,795 / 0.01 s;
`fn-sn-crash-…` 3,237; `fn-sn-recover-…` 1,796; `fn-sn-io-…` 945;
`fn-sn-initial-is-indexed` 468; the two query bridges 167 and 180. No new
lemma needed a profile; nothing here is slow.

**The fan is green with no exceptions to declare.** Until the third `dev`
merge one root was red — `tests/acl2/checkpoint-codec-tests`, whose
`assert-event` on line 204 was simply false (the validator accepted the
bad-generation witness), reported as an ASK by `w10/teeth-audit` and again by
`w11/wildmat-xpat`. `w11/checkpoint-validator` landed the fix on `dev` while
this lane was finishing, and the final run has **no failing root at all**.
The fan is 133 rather than 132 because `dev` also added
`tests/acl2/store-node-resolution-traces-tests` to the Makefile roots.

## 7. Open, recorded not weakened

1. **`host/bp-ingress-host.lisp:80` is outside the chain.** It installs
   `(fn-bpi-result-store result)` from `fn-bpi-ingress-prepare`
   (`books/bp-ingress.lisp:457`), whose store step is `fn-sn-prepare`. The
   index is therefore carried correctly *in fact* — `fn-sn-prepare` does not
   publish — but there is no `fn-bpi-ingress-prepare-preserves-indexedp`, so
   the chain has a hole at the BP ingress path and the sentence
   "`fn-sn-indexedp` holds of every state the host installs" is a claim about
   nine sites out of ten. Owner: the BP cluster with the store cluster.
   **This lane attempted it and withdrew it, with a measurement worth having**
   before anyone else tries the obvious hint. The statement is

   ```lisp
   (defthm fn-bpi-ingress-prepare-preserves-indexedp
     (implies (and (fn-sn-indexedp store)
                   (equal (fn-bpi-result-kind
                           (fn-bpi-ingress-prepare store policy context adu))
                          :prepared))
              (fn-sn-indexedp
               (fn-bpi-result-store
                (fn-bpi-ingress-prepare store policy context adu)))))
   ```

   — the kind hypothesis is not decoration, because the `:rejected` branches
   put a reason keyword where `fn-bpi-result-store` reads the state. Proved
   by `:use` of `fn-sn-prepare-preserves-indexedp` with
   `fn-bpi-ingress-prepare` ENABLED and `fn-article-parse`,
   `fn-af-proto-article-check` and `fn-bpi-record-for` disabled, it did
   **not** close in **seven minutes** on the laptop, against a baseline of
   **1.07 s for the whole of `books/bp-ingress`** on hbox
   (`certify-20260921T015400Z-1419906`). That is the case explosion the
   book's own guard-hint comment warns about at `books/bp-ingress.lisp:461`.
   `books/bp-ingress.lisp` is therefore **untouched by this lane**. The next
   attempt should profile first (`tools/proof_profile.py`) and should almost
   certainly keep `fn-bpi-ingress-prepare` CLOSED, proving the
   `:prepared` branch as a `fn-deftransition`-style branch lemma instead of
   opening the whole nested `if`.
2. **PRF-023 stays `in-progress`, not `certified`**, for four reasons and they
   are in its registry note: `fn-stx-index-slots-agree` still has no caller
   (no served query walks the slot list); the keyring is per-invocation and
   not in the durable configuration history; A-CRYPTO stands behind every
   verification and the only witnesses run under the toy realiser of
   `tests/acl2/crypto-seam-tests`; and item 3 below.
3. **The ADMISSION path is where D3 is still open.**
   `fn-stx-transit-authority-ok` (`books/stx-policy.lisp:23`) walks
   `(fn-stx-lace node keyring)` — linear in the store — once per article, and
   has no caller: `fn-peer-transfer` (`books/peer-inbound.lisp:328`) does not
   call it. **What wiring it would cost, now that the carrier exists**: the
   gate needs `(fn-pol-current group lace)` over the lace, and the index's
   three lists are keyed by content id, by `(creator, incarnation, sequence)`
   slot and by equivocating creator — *none of them by group*. So the carrier
   as built does **not** discharge the admission walk; a policy-by-group
   projection would be a **fourth** list in `fn-stx-index`, extended at
   `fn-stx-index-add1` alongside the other three, with its own agreement
   theorem against `fn-pol-current`. That is a `books/stx-index` change with a
   new keystone, not a wiring change, and it is the honest answer to the
   question the packet asked. Owner: the substrate cluster.
4. **PRF-025 is untouched and stays `in-progress` with both events
   `pending_subject`.** Nothing changed for it: no book outside the stx
   cluster includes `books/stx-epochs` and there is no reconnection path to
   wire `fn-stx-commits-of-batch` to. Future feature work, not missing
   evidence for implemented behaviour.
5. **`fn-sn-fence-node` and `fn-sn-resolve-node` remain
   `unreachable-in-composition`** and are unchanged; they take a node, not a
   state, so they never touch the index.

## 8. The next global step

Item 3 is the one that moves the design forward rather than the ledger: the
index answers the *query* and the *admission gate still walks the store*, so
D3 is half-answered. The fourth list in `fn-stx-index` keyed by group, with
`fn-stx-index-policy-agrees-with-fn-pol-current`, and then
`fn-peer-transfer` consulting it, is the packet that finishes it — and unlike
this one it needs no new record, because `fn-sn-state` now has the slot.
