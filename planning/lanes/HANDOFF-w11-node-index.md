# w11/node-index — the fifth slot is the wrong change, and here is the right one

Branch `w11/node-index`, worktree `build/lanes/w11-node-index`, from `dev`
`ad9a794`. The packet was `w10/substrate-2`'s board ASK (BOARD.md, 2026-09-20):
give `fn-node-statep` a fifth slot holding
`(fn-stx-index-of-store (fn-stx-store node) keyring)` so that PRF-023's and
PRF-025's keystones acquire the host line they lack.

**`books/node.lisp` is untouched.** The slot is not implementable at this
revision, would not close either target if it were, and the record that should
carry the index is a different one. What this lane did instead is close the
subject gap *underneath* the reported one: `fn-stx-acceptedp`, the hypothesis
of every S3 keystone, was an assumption attributed to a book that has never
existed, and it is now a theorem about the transition the host calls.

## 0. Certification

Two boxes, both green, `--affected-by books/stx-lace.lisp --closure`. The fan
is 31 roots and not most of the tree, because `books/node.lisp` is untouched:
only `stx-index` and `stx-policy` include `stx-lace`, and no book outside the
stx cluster includes `stx-index`, `stx-authority` or `stx-epochs`.

| Box | Run | Evidence | ACL2 | Jobs | Roots | Wall |
| --- | --- | --- | --- | --- | --- | --- |
| laptop | local | `build/acl2/certify-20260921T004848Z-71469` | `/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2` sha256 `36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324` | 1 | **31 of 31, exit 0** | 225.8 s |
| hbox | `run-20260921T005550Z-81ad` | `build/acl2/certify-20260921T005558Z-1362139` | `/tank/fn/acl2-8.7/saved_acl2` sha256 `64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5` | 8 | **31 of 31, exit 0** | 137.6 s |

Per root, hbox: `books/stx-lace` 0.47 s, `books/stx-index` 0.71 s,
`books/stx-policy` 0.48 s, `books/stx-authority` 0.82 s, `books/stx-epochs`
0.63 s, `tests/acl2/stx-transit-tests` 0.91 s with 84 `assert-event`s. The new
theorem is **1,542 prover steps, 0.01 s**, with no new lemma. hbox's cache
reported `installed 59, kept 36, uncached 181` over the whole tree before the
run. Baseline before any edit, laptop, the same six-book chain:
`build/acl2/certify-20260921T004453Z-66002`, exit 0.

**The control, stated separately from the green.** `dev` was merged twice
after the hbox run (`e67b6cb`, then `bdf40d0`, `w11/clock-seam`), and the
run's own `source_digests_sha256` was re-checked against the working tree
afterwards: **31 of 31 certified sources byte-identical, 0 changed.** So the
certification is a claim about the tree as it stands, not about an older one.
`w11/clock-seam` brought `books/owner`, `books/owner-invariants` and
`books/nntp-post`; none is in this closure.

Ledger, before to after: `defthm`/`defthmd` events 5559 to 5560,
`assert-event` checks 5400 to 5422, `books/stx-lace.lisp` theorems 19 to 20,
`tests/acl2/stx-transit-tests.lisp` witnesses 62 to 84. The new theorem is not
flagged SUSPECT. `make check` exits 0.

## 1. The enumeration the packet asked for, with a verdict per site

Measured over `books/`, `tests/acl2/` and `host/` by an s-expression walk, not
by eye. Reproduce with the script in the commit body of this lane's second
commit.

### 1a. `fn-node-make-state` — 26 four-argument occurrences, 21 real applications

One occurrence is the `fn-defrecord` `:constructor` declaration and four are the
argument positions of one local accessor-of-constructor lemma; the other 21 are
applications.

| Site | What it builds | Verdict for a fifth slot |
| --- | --- | --- |
| `books/node.lisp:126` | the `fn-defrecord` `:constructor` declaration | arity change; regenerates 5 accessor-of-constructor lemmas, `-OF-ACCESSORS`, `-INJECTIVE`, the three forward facts |
| `books/node.lisp:159` `fn-node-initial-state` | fresh, empty store | must build `(fn-stx-index-empty)`; needs a keyring to prove it equals `fn-stx-index-of-store` of `nil` |
| `books/node.lisp:200` `fn-node-prepare` | `next-acceptance`, stage | store unchanged (`fn-node-prepare-does-not-publish-or-commit-retention`), so the index is carried; needs `-OF-ACCESSORS` or an explicit pass-through |
| `books/node.lisp:212` `fn-node-complete :durable` | `fn-accept-complete … :durable` | **the store grows here.** Must apply `fn-stx-index-add` to the accepted delta — and `fn-node-complete` has neither the article nor a keyring in its formals |
| `books/node.lisp:222` `:aborted` | store unchanged | carried |
| `books/node.lisp:228` `:indeterminate` | store unchanged | carried |
| `books/node.lisp:244` `fn-node-recover :committed` | `fn-accept-recover … :committed` | **the store grows here too**; same two missing formals |
| `books/node.lisp:254` `:absent` | store unchanged | carried |
| `books/node-invariants.lisp:89` | `fn-node-install-stage` | store grows; same problem, in a second book |
| `books/node-config.lisp:405` | a **fresh** `fn-make-state` from a replayed configuration | must recompute the index over the whole store, with a keyring the config cluster would have to own — and `books/node-config.lisp` includes `node-invariants`, so the config cluster sits *above* node while the keyring's owner would sit *inside* it |
| `books/replay.lisp:198` | a **fresh** `fn-make-state` from a replay | same recomputation |
| `books/bp-release.lisp:133` | rebuild with a new retention | carried |
| `books/store-node-invariants.lisp:380` | the rebuild-from-fields identity | exactly what `<ctor>-OF-ACCESSORS` is for; widens to five accessors |
| `books/bp-receiver-evolving-node-invariants.lisp:375` | mirrors the durable completion | store grows; third book with the same obligation |
| `books/bp-receiver-evolving-node-invariants.lisp:415-418` | a local accessor-of-constructor lemma over `(a r s b)` | four statements change arity |
| `tests/acl2/node-tests.lisp` ×8, `tests/acl2/stx-transit-tests.lisp:80` | hand-built states | every one needs a fifth argument |

### 1b. `fn-node-statep` — 341 mentions in 38 files, 113 `defthm` statements

Split by what the statement does with it, which is what decides whether a
strengthening breaks the proof:

- **26 theorems CONCLUDE `fn-node-statep`, in 13 books.** Each must re-prove
  the new conjunct. They are `fn-node-{prepare,complete,recover,install-stage}-preserves-state`
  and `fn-node-initial-state-is-state` (node, node-invariants);
  `fn-node-step-preserves-state`, `fn-node-trace-preserves-state`
  (node-traces); `fn-bprl-{node-release,node-admit}-preserves-statep`,
  `fn-bprl-{release,undertake}-preserves-node-state` (bp-release-invariants);
  `fn-bprv-committed-implies-node-statep` (bp-receiver-evolving-node-invariants);
  `fn-bp-statep-components` (bp-workflow-invariants);
  `fn-bp-statep-of-initial-state-implies-inputs` (bp-workflow-records-invariants);
  `fn-ct-publish-article-preserves-node-statep` (container);
  `fn-peer-session-consistentp-forward`, `fn-peer-sessionp-forward-fields`
  (peer-inbound); `fn-replay-advance-preserves-node-statep`,
  `fn-replay-apply-record-non-nil-is-node-state`,
  `fn-replay-apply-record-statep-iff-consp` (replay);
  `fn-sn-successful-replay-node-is-state`,
  `fn-sn-file-recovery-produces-valid-replay`,
  `fn-snt-replayed-node-idle-and-frontier`,
  `fn-snt-prepared-durable-is-idle-at-successor` (store-node-invariants);
  `fn-snt-typed-store-components` (store-node-traces);
  `fn-sn-prepare-node-preserves-state` (store-node).
  **Verdict: each of these thirteen books would have to reason about statement
  parsing and signature verification to re-prove a node-state fact.**
- 87 theorems only hypothesise it and survive a strengthening unchanged.

## 2. Why the slot is not the change — three measured blockers

1. **It is a dependency cycle.** `books/stx-index.lisp:22` includes `stx-lace`;
   `books/stx-lace.lisp:23` includes `node`; `fn-stx-store` *is*
   `(fn-state-articles (fn-node-acceptance node))`
   (`books/stx-lace.lisp:117`). The index is defined above the node by
   construction. Node's local include closure is **6** books; `stx-index`'s is
   **20**. The 14 node would gain — `article cbor-invariants crypto-seam lace
   lace-invariants principal records records-invariants statement
   statement-invariants stx-carrier stx-index stx-lace stx-verify` — are
   inherited by the **70 books whose closure contains `node`**. The cycle can
   be cut (`fn-stx-index-of-store` takes `(articles keyring)` and needs no
   node), but the cut is that inheritance, not a rename.
2. **The conjunct is not statable.** `fn-node-statep` takes one formal; the
   index is a function of `(store, keyring)`. The token `keyring` occurs in ten
   books — `principal policy policy-invariants stx-{authority,epochs,index,invariants,lace,policy,verify}`
   — and in **no state or configuration record in the tree**. The slot needs
   either a second recognizer formal (341 mentions) or a keyring slot beside
   it, whose owner is the config cluster, which sits above node. A keyring
   change would also invalidate the conjunct for the whole store, which is the
   live-reconfiguration direction pointing the other way.
3. **It would still have no host line.** `grep -rn fn-stx host/ bin/ tools/` is
   five hits, all `tools/stx.py` calling `fn-stx-header-value`,
   `fn-stx-verdict*` and `fn-stx-parse-header` on ONE article. No book outside
   the stx cluster includes `books/stx-index`, `books/stx-authority` or
   `books/stx-epochs`; the cluster is a leaf. Wiring a CLI query without a
   carrier would compute `(fn-stx-index-lookup (fn-stx-index-of-store store
   keyring) id)` — a whole-store walk per query, which is the D3 violation the
   index exists to remove. **A host line bought that way is worse than none.**

## 3. What this lane closed instead: the observation had no subject either

`books/stx-lace.lisp:147` said of `fn-stx-acceptedp` that "`books/stx-transit.lisp`
names that composition and proves it satisfies this predicate", and that
"`tests/acl2/stx-lace-tests.lisp` exhibits a run where it holds".
**Neither file has ever existed.** `books/stx-policy.lisp:35` cited the same
book for `fn-stx-transit-gate-is-the-gate`. So `fn-stx-acceptedp` was an
assumption, and the four keystones that hypothesise it —
`fn-stx-lace-of-accept-is-merge`, `fn-stx-transit-ids-are-union`,
`fn-stx-transit-equivocation-survives-later-merges` and
`fn-stx-index-invariant-preserved-by-accept` — were preservation under a
hypothesis nothing established. That is a second subject gap, *under* the one
`w10/substrate-2` reported.

New in `books/stx-lace.lisp`, one exported theorem, no existing statement
changed:

```lisp
(defthm fn-stx-durable-completion-is-an-acceptance
  (implies (fn-node-pending-matchesp s txid generation)
           (fn-stx-acceptedp
            s
            (fn-node-complete s txid generation :durable)
            (fn-article-from-pending
             (fn-state-pending (fn-node-acceptance s))))))
```

**The host line, as the assurance rule requires it to be named:**
`host/store-node-host.lisp:402` `fn-store-sn-finish` → `fn-sn-finish`
(`books/store-node.lisp:200`) → `(fn-node-complete (fn-sn-node s) txid
generation :durable)` (`books/store-node.lisp:204`). The host adds no
acknowledgement any other way:
`fn-snrt-new-success-is-actual-matching-durable-completion`
(`books/store-node-resolution.lisp:414`) already proves it. Those two books sit
above `books/stx-lace`, so the theorem is stated about `fn-node-complete`
itself and the chain is named in the book's comment.

The accepted article is *named*, not existentially claimed: the one
`fn-install-pending` conses (`books/acceptance.lisp:236`). Cost: **1,454 prover
steps, 0.01 s**, no new lemma.

## 4. Teeth, and a vacuity this exposed

`tests/acl2/stx-transit-tests.lisp` gains section S3-0. Its first assertion is
the finding: `(not (fn-node-statep (fn-stxt-node (list *stxt-r1*))))`. **Every
S3 witness in that book reaches its "next" node with `fn-stxt-node`, which
builds a store by hand and produces a value that is not a node state** (its
retention field is `nil`, which is not a `fn-retain-statep`). Nothing in the
substrate cluster had ever taken an acceptance step.

The new section runs one: `fn-node-initial-state` → `fn-node-prepare` with
`*stxt-r1*`'s own signed octets → `fn-node-complete … :durable`. It asserts
the keystone instance; that the store grows from 0 to 1 and the accepted
payload is the signed one (so the delta is not the empty one that made two
earlier substrate witnesses vacuous); that the lace goes from `nil` to
`(list *stxt-s1*)`; S3-1's merge conclusion on that run; S3-3's preservation
equation and its lookup, *evaluated on a node the transitions reached*; and
one tooth per hypothesis on two concrete violating values — a node with no
pending, and a node that holds a stage but is offered the wrong transaction.
There is one hypothesis, so there are two teeth and the second separates the
matching test rather than the existence of a proposal.

## 5. PRF-023 and PRF-025 — honest status

- **PRF-023 stays `in-progress`**, and `pending_subject` stays on
  `fn-stx-index-equivocators-agree`. The *query* still has no caller. What
  changed is that its sibling event
  `fn-stx-index-invariant-preserved-by-accept` now has one: its hypothesis
  `fn-stx-acceptedp` is discharged at `fn-node-complete`, which the host calls.
  The note records the three blockers above so the next lane does not re-derive
  them.
- **PRF-025 stays `in-progress`** with both events `pending_subject`. The gap
  is wider than "no caller": no book outside the stx cluster includes
  `books/stx-epochs`, and there is no reconnection path in the tree to wire it
  to. That is future feature work, not missing evidence for implemented
  behaviour.
- No registry id was claimed.

## 6. The proposal — the carrier belongs in `fn-sn-statep`, and who owns it

`books/store-node.lisp`'s `fn-sn-state` is `(groups capacity files node)`: it
already carries **configuration** beside the node, it is the value the host
holds (`(f-get-global 'fn-store-sn state)`), and **it is not in
`books/stx-index`'s include closure**, so it can include the index with no
cycle. The change, for whoever takes it:

1. `books/store-node.lisp`: `fn-sn-make` gains `keyring` and `index`;
   `fn-sn-statep` gains `(fn-prin-keyringp (fn-sn-keyring s))` and
   `(fn-stx-index-invariantp (fn-sn-index s) (fn-sn-node s) (fn-sn-keyring s))`
   — the second is exactly `books/stx-index.lisp:394`, already written.
2. The obligation lands at one site: `fn-sn-finish` (`:200`), whose node step
   is the durable completion. `fn-stx-index-invariant-preserved-by-accept`
   discharges it, with §3's theorem supplying its hypothesis. `fn-sn-prepare`,
   `fn-sn-io`, `fn-sn-crash` and `fn-sn-recover` carry the index unchanged —
   except `fn-sn-recover`, which rebuilds the node from a replay and must
   recompute, as `books/replay.lisp:198` does.
3. The query: `fn-sn-statement-lookup` and `fn-sn-equivocatorp`, one line each
   over `fn-sn-index`, and a `fn-store-sn-*` wrapper beside
   `fn-store-sn-lookup` (`host/store-node-host.lisp:464`), reached from
   `bin/fn statement`. Then and only then does `fn-stx-index-lookup` have a
   host line and PRF-023's theorem-subject rule is met.
4. The cost, measured: `books/store-node.lisp`'s include closure (itself
   included) is **14** books and would become **27**, gaining `article
   cbor-invariants crypto-seam lace lace-invariants principal
   records-invariants statement statement-invariants stx-carrier stx-index
   stx-lace stx-verify`. That is real, and it is paid by the store cluster
   alone rather than by the 70 books above `node`. `store-node` is not in
   `stx-index`'s closure, so there is no cycle.

**Owner: the store-node cluster, with the substrate cluster.** Not this lane:
`w11/bytestore-k2` is live on the crash model below `store-files`, and
`fn-sn-` is two records away from it.

## 7. Also still open, recorded not weakened

- `fn-stx-transit-authority-ok` (`books/stx-policy.lisp`) walks
  `(fn-stx-lace node keyring)` — linear in the store — once per article, and
  **has no caller**: the host's transit path `fn-peer-transfer`
  (`books/peer-inbound.lisp:328`) does not call it. So even inside the model,
  the index does not yet replace the projection on the admission path. The
  false `books/stx-transit.lisp` citation there is replaced with this.
- The three theorems in `books/stx-authority.lisp` each restate a `cond` branch
  with its own test as hypothesis. Named as such would be `-by-definition`;
  not renamed here because the book is outside this lane's edits.
- A-CRYPTO stands behind every verification in the new witness: the toy
  realisers of `tests/acl2/crypto-seam-tests.lisp`.
