# LANEDUMP: substrate (C1-11) — WIP handoff

Worktree `/Users/ember/dev/fn/build/lanes/substrate`, branch `lane/substrate`,
branched from `0bd0b5c`. Written 2026-09-19 on coordinator order; no
certification is running (the last stale smoke session was stopped by me).

## Packet as understood

1. `books/crypto-seam.lisp`: `fn-digest` and `fn-sig-*` as `encapsulate`s with local witnesses; shape constraints only plus the single verify-of-sign property; tagged (domain-separated) preimages; hex helper.
2. `books/principal.lisp`: principal id = tagged digest of (public key, token) mirroring dregg `CellId`; key succession statements with a validity predicate; theorems on preimage determination and holder-only succession.
3. `books/statement.lisp`: block-shaped header (creator, incarnation, sequence, preds, kind, ref) + payload + signature; item-sequence codec over `fn-cbor` uint32/bytes; round trip, accepted-input canonicality, bounds before allocation; content id = tagged digest of the canonical header bytes; receipts of kind `:receipt`.
4. `books/lace.lisp`: laces keyed by content id; `fn-lace-merge`; union/idempotent/commutative/associative; canonical and cross-canonical with the gap exhibited; equivocation (restore/fork); causal closure preserved by merge.
5. `books/policy.lisp`: policy statements by the group authority; `fn-pol-authorizedp`; authority confinement; teeth (forged, unauthorized, stale); `fn-pol-term` and receipts committing to it; FNWF/FNRJ field proposal.
6. `planning/decision-packet-d09-d11.md`.
7. Specs `identity.md`, `statement.md`, `lace.md`, `policy.md`; prefix rows; Makefile roots.
Gate: `make check`; full `make certify` green including new roots.

## Certification state (exact)

| Book | State | Evidence |
| --- | --- | --- |
| `books/crypto-seam` | CERTIFIED | `build/acl2/certify-20260919T061815Z-24588/books--crypto-seam.certify.log` line 1459 `FN_CERTIFY_SUCCESS`; `books/crypto-seam.cert` exists |
| `books/statement` | CERTIFIED | `build/acl2/certify-20260919T063011Z-30836/books--statement.certify.log` line 3833 `FN_CERTIFY_SUCCESS`; `books/statement.cert` exists |
| `books/statement-invariants` | NOT certified; in progress | see below |
| `books/principal` | NOT certified; one proof fixed on disk, unverified | see below |
| `books/principal-invariants` | NOT certified; loaded partially in smoke runs (see below) | |
| `books/lace`, `lace-invariants`, `policy`, `policy-invariants` | written, NEVER loaded in ACL2 | |
| five test books | written, NEVER loaded in ACL2 | |

Dependency certificates `books/cbor.cert`, `cbor-invariants.cert`, `records.cert`,
`records-invariants.cert` exist from the first partial baseline (Sep 18 23:36 to 23:50)
and match the unchanged sources.

### statement-invariants: exact state

Smoke `ld` pass `build/smoke/smoke4.log` (against the certified `statement`):
every theorem up to and including `fn-stmt-decode-items-of-encode-items` proved
(the item-codec round trip). `fn-stmt-encode-items-of-decode-items` FAILED with
checkpoint (verbatim, abbreviated with ...):

```
Subgoal *1/6''
(IMPLIES (AND (CONSP OCTETS) (NOT (ZP FUEL))
  (FN-CBOR-RESULT-OKP (FN-CBOR-DECODE OCTETS))
  (FN-STMT-OKP (FN-STMT-DECODE-ITEMS (+ -1 FUEL) (FN-CBOR-RESULT-REST (FN-CBOR-DECODE OCTETS))))
  (EQUAL (FN-STMT-ENCODE-ITEMS (FN-STMT-VALUE (FN-STMT-DECODE-ITEMS (+ -1 FUEL) (FN-CBOR-RESULT-REST (FN-CBOR-DECODE OCTETS)))))
         (FN-CBOR-RESULT-REST (FN-CBOR-DECODE OCTETS)))
  (FN-STMT-OKP (LIST :OK (CONS (FN-CBOR-RESULT-VALUE (FN-CBOR-DECODE OCTETS)) (FN-STMT-VALUE (FN-STMT-DECODE-ITEMS ...))))))
 (EQUAL (FN-STMT-ENCODE-ITEMS (FN-STMT-VALUE (LIST :OK (CONS (FN-CBOR-RESULT-VALUE (FN-CBOR-DECODE OCTETS)) ...)))) OCTETS))
```

Cause: `fn-stmt-ok` opened to `(list :ok ...)` while `fn-stmt-value` was disabled, so
`fn-stmt-value-of-ok` could not fire. FIX APPLIED ON DISK, UNVERIFIED: the hint now also
disables `fn-stmt-ok fn-stmt-ok2 fn-stmt-error`. Expected to close via `fn-stmt-value-of-ok`,
`fn-stmt-encode-items` opening on the cons, the IH, and `fn-cbor-decode-reencode-prefix`.
Everything after this theorem in the book is unverified.

The last runner attempt `python3 tools/certify_books.py books/statement-invariants`
(evidence dir `build/acl2/certify-20260919T064359Z-38764`) exited with code 2 and produced no per-book log; its
`certify.log` tail:

```

```

### principal: exact state

`fn-prin-acceptablep-implies-shapes` (a helper before `fn-prin-apply-succession`) FAILED
in smoke4 (`build/smoke/smoke4.log` line 3736), checkpoint: needed
`(INTEGERP (CADDR (CAR S)))` with `fn-prin-statep` disabled by my hint. FIX ON DISK,
UNVERIFIED: hint now disables `fn-stmt-verifiedp fn-prin-succession-key fn-stmt-decode-items`
and the field accessors instead, leaving `fn-prin-statep`/`fn-stmt-p` enabled.
`fn-prin-apply-succession`'s guard hint uses that lemma with `fn-prin-succession-acceptablep`,
`fn-stmt-p`, `fn-prin-succession-key` disabled (earlier failure: the guard proof exploded,
36 s, 2.3M steps, no checkpoints). Everything after `apply-succession` in the book is
unverified.

### principal-invariants: exact state

Against an uncertified `principal` (smoke2/3/4), proved: `fn-prin-preimage-decodes`,
`fn-prin-preimage-injective`, `fn-prin-succession-payload-is-payload`,
`fn-prin-succession-key-of-payload`, `fn-prin-succession-key-of-sign`,
`fn-prin-sign-succession-is-verified`, `fn-prin-sign-succession-fields`.
`fn-prin-sign-succession-is-acceptable` EXPLODED (150 subgoals with `fn-cbor-encode`,
`fn-stmt-header-encode`, `fn-stmt-headerp`, `floor` opened: `fn-stmt-p` of the signed
statement was being expanded). FIX ON DISK, UNVERIFIED: new lemma
`fn-prin-sign-succession-is-stmt` (from `-is-verified` via `fn-prin-verified-implies-stmt-p`)
is `:use`d and `fn-stmt-p` is disabled in the `-is-acceptable` hint. Theorems after it
unverified.

### Earlier defects already fixed and verified by later runs

- `fn-digest-hex-chars` guard: local floor/mod bound lemmas with `floor mod` disabled (verified: crypto-seam certified).
- Parser guard conjectures (`fn-stmt-header-of-items` etc.): `:do-not-induct t` and disabling `fn-stmt-okp fn-stmt-value fn-stmt-rest fn-stmt-take-id-items ...` per function, with only already-defined names (verified: statement certified).
- `fn-stmt-take-id-items-value-is-true-list` made conditional on `fn-stmt-okp` (verified).
- `fn-stmt-header-encode-is-octet-list` hint disabling `fn-cbor-encode` (verified).
- `fn-stmt-decode-items-of-encode-items`: added `fn-stmt-encode-uint-item-consp`, `fn-stmt-encode-bytes-item-consp`, `fn-stmt-consp-of-append` (verified in smoke4).

## Operational notes for the next owner

- Run certification with `FN_ACL2_TIMEOUT_SECONDS=1800` (coordinator order); never a bare trailing `&` (SIGTERM at turn end); use harness background or `setsid nohup`.
- An external reaper killed long ACL2 processes twice under load 14 (exit 144); keep runs short or detached.
- Smoke technique that worked: `acl2 < build/smoke/driver2.lsp` where the driver `include-book`s the last certified book and `ld`s the rest with `:ld-error-action :return`; grep `ACL2 Error` and `^Form:`.
- Two `make certify` baselines died (session reset; SIGTERM). The full gate has NOT been run. `make check` passes (81 Markdown files, 49 requirements, 18 proof targets, 18 scenarios).

## DONE

- Books written: all nine (`crypto-seam`, `statement`, `statement-invariants`, `principal`, `principal-invariants`, `lace`, `lace-invariants`, `policy`, `policy-invariants`).
- Test books written: all five, using `defattach` toy realisers (`fn-toy-mix-digest`, `fn-toy-length-digest`, `fn-toy-public-key/sign/verify` in `tests/acl2/crypto-seam-tests.lisp`; others include it). ACL2 doc check: attachments are used in the top-level loop (assert-event) but not in `defconst`, so witnesses are zero-arg `defun`s.
- Specs: `specs/identity.md`, `specs/statement.md`, `specs/lace.md`, `specs/policy.md`.
- `planning/decision-packet-d09-d11.md` (P1 to P9, all marked proposal).
- `docs/prefixes.md`: rows for `fn-digest-`/`fn-sig-`, `fn-prin-`, `fn-stmt-`, `fn-lace-`, `fn-pol-`, `fn-toy-`/`fn-t-`.
- `Makefile`: fifteen roots appended after `tests/acl2/nntp-tests`.
- `HANDOFF.md` skeleton (mirror table, proposals); gate tails not yet filled.

## IN-PROGRESS

Certification of `statement-invariants`, `principal`, `principal-invariants` (state above).

## NOT-STARTED (in ACL2)

Loading/certifying `lace`, `lace-invariants`, `policy`, `policy-invariants`, the five test
books; the full `make certify` gate; filling gate tails into HANDOFF.md. (All files are
written; the specs and decision packet are complete drafts.)

## Design decisions and why

- Seam constraints are shape-only plus `fn-sig-verify-of-sign`; the local digest witness is a
  CONSTANT so equal digests provably imply nothing; the local signature witness publishes the
  seed as the key so unforgeability is visibly absent. Reason: AGENTS.md "assumptions are
  constrained functions"; the test book attaches a colliding realiser (minidregg `lengthScheme`).
- Every preimage is `bstr(tag) || message` (`fn-digest-tagged-preimage`), proved to separate
  (`-separates`, `-injective`), so domain separation is a theorem below the digest.
- Statement = dregg `Block` plus `incarnation` (D10) and `kind`; content id over header bytes
  only, header binds payload through `ref = fn-digest-tagged "fn-payload-v1" payload` (lib.rs
  `Block::id` covers payload; here via the ref so payloads can be large/opaque).
- Codec: one generic item-sequence codec (`fn-stmt-encode-items`/`fn-stmt-decode-items fuel`)
  with structures as projections of item lists; proofs are one round trip for the sequence codec
  and small projection lemmas per structure. No arrays/maps added to cbor.lisp (not owned).
- `fn-lace-canonicalp` is DEFINED as `fn-lace-cross-canonicalp lace lace` so `crossCanonical_self`
  is by definition; `fn-lace-same-view-of-cross-canonical` needs only same-ids and cross-canonical
  (ACL2 lookup returns the first match), documented in specs/lace.md.
- Id-set laws are proved by a pick-a-point witness (`fn-lace-ids-witness`,
  `fn-lace-ids-subsetp-by-witness`) from the pointwise union law.
- `fn-lace-equivocatorp lace principal incarnation` = two distinct members at one
  (creator, incarnation, sequence) (lib.rs `EquivocationProof`), not the Lean incomparability
  form; `fn-lace-reissue` is the D10 scenario as a function.
- Policy in force = latest verified candidate by (incarnation, sequence) with `nfix`ed fields
  (total order in the logic); a same-slot conflict yields NO policy in force (fail closed,
  both kept). Authority confinement is stated as invariance of `fn-pol-current` under any delta
  without a verified authority statement, plus the constructive contrapositive naming the
  authority statement.
- Policy term = (id of policy in force . tagged digest of [authority key, creator key,
  canonical statement bytes]); receipts carry it; `fn-pol-receipt-groundedp` re-resolves it
  via `fn-lace-lookup` (needs canonicity; the length-digest tooth shows why).
- Packet name `fn-equivocatorp` became `fn-lace-equivocatorp` for the prefix registry.

## Ground truth each shape mirrors

| fn definition | dregg / minidregg artifact |
| --- | --- |
| `fn-stmt-make-header` (creator incarnation sequence preds kind ref), `fn-stmt-make` (header payload signature) | `~/dev/breadstuffs/blocklace/src/lib.rs` `pub struct Block { creator, sequence, predecessors, payload, signature, pq_signature }`; `~/dev/breadstuffs/metatheory/Dregg2/Authority/Blocklace.lean:58` `structure Block` |
| `fn-stmt-content-id` = tagged digest of header bytes; `fn-stmt-sign` signs the id | lib.rs `Block::id` (`new_derive_key("dregg-blocklace-block-v1")` over creator, sequence, predecessors, payload) and `Block::sign_by` (signature over `id()`) |
| `fn-prin-id pk token` = tagged digest of (bstr pk, bstr token) | `~/dev/breadstuffs/README-LLMs.md` section 2: `CellId = blake3::derive_key("dregg-cell-id-v1", pubkey||token)` |
| `fn-sig-verify` as an opaque boolean oracle; `fn-prin-chain-validp` | `Dregg2/Authority/BiscuitGraph.lean:55` `SigChecker`, `WellFormed`; `Dregg2/Crypto/CapabilityChain.lean:65` `VerifyFrom` / `VerifyChain` |
| seam shapes (32-octet seed, key up to 4096, signature up to 4096), domain-separated preimages | `blocklace/src/pq.rs` (`BLOCK_PQ_CTX`, `MlDsaSigningKey::from_seed`, PK_LEN 1952, SIG_LEN 3309), `signer.rs` `HybridBlockSigner` |
| `fn-lace-p`, `fn-lace-lookup` | Blocklace.lean:66 `Lace := List Block`, :70 `Lace.lookup` |
| `fn-lace-canonicalp` | Blocklace.lean:80 `Lace.Canonical` |
| `fn-lace-lookup-of-member` | Blocklace.lean:86 `lookup_of_mem` |
| `fn-lace-new`, `fn-lace-merge` | `Dregg2/Distributed/LaceMerge.lean` `newBlocks`, `mergeLace` (finality.rs:690); `~/dev/minidregg/Theory/LaceMerge.lean` `newEvents`, `merge` |
| `fn-lace-merge-ids-are-union`, `-idempotent`, `-commutative-ids`, `-associative-ids`, `-monotone`, `-lub` | LaceMerge.lean `laceIds_mergeLace`; minidregg `ids_merge`, `merge_idem`, `merge_comm`, `merge_assoc`, `merge_monotone`, `merge_lub` |
| `fn-lace-cross-canonicalp`, `fn-lace-cross-canonical-self`, `fn-lace-canonical-append-iff`, `fn-lace-same-view-of-cross-canonical` | LaceMerge.lean:247 `CrossCanonical`, `crossCanonical_self`, `canonical_append_iff`, `sameView_of_canonical_eq_ids`; minidregg section 3 |
| `lace-tests` gap section under `fn-toy-length-digest` | minidregg `lengthScheme`, `lengthScheme_not_binding`, `crossCanonical_is_the_gap`, `merge_drops_at_collision`, `merge_computes` |
| `fn-lace-equivocatorp`, `fn-lace-distinct-same-slot-is-equivocation` | lib.rs `EquivocationProof { creator, sequence, existing, conflicting }`; Blocklace.lean:152 `Equivocator` |
| `fn-lace-causally-closedp`, `fn-lace-merge-preserves-closure` | lib.rs "Key Invariants" 2 (`Blocklace::insert` causal closure) |
| design rules applied (satisfiable pole plus teeth per keystone, policy term not decision bit, pessimistic number) | `~/dev/minidregg/ATLAS.md` section 6 laws 1, 2, 12, 14 |

The packet asked for `fn-equivocatorp`; the prefix registry requires a layer
tag, so it is `fn-lace-equivocatorp` (same signature: lace, principal,
incarnation).


## Gate commands and last results

- `make check`: passed (Scaffold OK: 81 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications).
- `make certify`: never completed in this lane (two baselines killed at 54 and 6 roots; logs `build/certify-baseline.log`, evidence dirs `build/acl2/certify-20260919T033339Z-70117`, `build/acl2/certify-20260919T053937Z-163`).
- Per-book: crypto-seam and statement certified (dirs above).

## Known defects

- All items under IN-PROGRESS; nothing after `fn-stmt-encode-items-of-decode-items` in
  statement-invariants, nothing after `apply-succession` in principal, nothing in lace/policy/tests
  has been checked by ACL2. Expect further hint work of the same kind (accessor visibility,
  `:do-not-induct`, free-variable rewrite rules).
- `must-fail (thm ...)` forms in the test books may be slow if the prover explores induction; drop
  or replace with negated `assert-event`s if so.
- `tests/acl2/lace-tests.lisp` and `policy-tests.lisp` re-`defattach` `fn-digest` twice; if ACL2
  refuses re-attachment inside a book, split the length-digest sections into separate books.

## Proposals for files this lane does not own

### `specs/objects.md`

- Line 14 (table row "Statement"): replace `| Statement | Kind, issuer, scope, subject references, terms/dependencies, authenticated encoding |` with `| Statement | Block-shaped header (creator principal, incarnation, sequence, predecessor content ids, kind, payload ref), payload, signature over the content id; see [statement](specs/statement.md) |`.
- Line 15 (row "Origin event"): replace with `| Origin event | Subsumed by the statement header: (creator, incarnation, sequence) is the slot, predecessors are the causal references; see [lace](specs/lace.md) |`.
- OBJ-004 paragraph: append the sentence `Two distinct statements at one (creator, incarnation, sequence) are retained and make the creator an equivocator in every lace holding both (fn-lace-distinct-same-slot-is-equivocation); which fork is served is a policy decision.`
- OBJ-006 paragraph: append `The structural half is fn-lace-reissue-is-equivocation; detection needs no freshness anchor, only both statements.`
- OBJ-007 paragraph: append `Authorization is a policy statement by the group authority resolved in the local lace (fn-pol-current); admission and receipts commit to the policy term, never to a boolean; see [policy](specs/policy.md).`

### `specs/encoding.md`

- Status paragraph, after "The byte grammar is not frozen": add `The substrate books use item sequences of the existing primitives (uint32 and byte strings, one item per field, explicit counts) as a local profile; see [statement](specs/statement.md). This is Candidate A of the article-byte examples over CBOR heads and is not a D08 selection.`
- ENC-003: append `Every digest and signing preimage in the substrate starts with the length-prefixed ASCII tag fn-<purpose>-v1 (fn-digest-tagged-preimage), proved to separate tag from message.`

### `planning/decisions.md`

- D09 row, Recommendation cell: append `Proposal P1/P2/P4/P5 of [the packet](planning/decision-packet-d09-d11.md): ed25519 now, hybrid ML-DSA-65 profile slot, BLAKE3 derive-key digest, seeds in a host keystore, rotation by :succession statements.`
- D10 row: append `Proposal P6/P7 of the packet: structural fork detection via equivocation; a fresh incarnation is declared by its first statement; no external anchor for detection.`
- D11 row: append `Proposal P8 of the packet: a group is (authority principal, name); owner-only policy change; depth-one authority.`
- D08 row: append `Proposal P3 of the packet: item sequences as the local profile until C2-01.`
- Resolution log: nothing to add until ember selects.

### FNWF / FNRJ record fields (books/bp-workflow-records.lisp, books/bp-receipt-records.lisp, tools/workflow_journal.py, tools/receipt_journal.py)

| Record | Current field | Proposed |
| --- | --- | --- |
| FNWF `:enqueue` (11 fields) | index 7 `policy-id` text | keep, and add index 11 `policy-stmt-id` (32-octet blob, `fn-stmt-id` of the policy in force) and index 12 `policy-evidence` (32-octet blob, `fn-pol-evidence-digest`); `fn-bp-enqueue-prepare-event` takes the pair |
| FNWF `:receipt-intent` (12 fields) | receipt fields 3 to 11 | add `policy-stmt-id`, `policy-evidence` copied from the decoded receipt's term (`fn-stmt-receipt-term`) |
| FNRJ `:request-context` (5 fields) | index 4 `policy-authorized` constant `t` | replace by `policy-stmt-id` and `policy-evidence`; `fn-bprr-recordp` requires both to be `fn-digest-octetsp`; `fn-bpr-accept-request` receives the term and the record is applied only if `fn-pol-receipt-groundedp` holds against the local lace |
| FNRJ `:receipt-intent` (5 fields) | index 4 `policy-authorized` constant `t` | replace likewise; `fn-bpr-prepare-receipt` takes the term; the emitted receipt ADU carries it |
| Python `workflow_journal.py` SCHEMA, `receipt_journal.py` SCHEMA | `("policy-authorized","true")` | `("policy-stmt-id","blob32"), ("policy-evidence","blob32")` with a 32-octet length check; the constant `t` path is removed |

This is the record-level closure of review defect D9; it is a proposal for the
FNWF/FNRJ refinement wave (C1-02/C1-03), not done here.

## Verbatim keystone theorem statements (as on disk; certification state per book above)

### books/crypto-seam.lisp
```lisp
(defthm fn-digest-shape
    (fn-digest-octetsp (fn-digest m)))
```
```lisp
(defthm fn-sig-verify-of-sign
    (implies (and (fn-sig-seed-p sk)
                  (fn-cbor-octet-listp m))
             (fn-sig-verify (fn-sig-public-key sk) m (fn-sig-sign sk m))))
```
```lisp
(defthm fn-digest-tagged-preimage-separates
  (implies (and (fn-digest-tagp tag)
                (fn-cbor-octet-listp m)
                (<= (+ 3 (len tag) (len m)) *fn-cbor-max-input*))
           (equal (fn-cbor-decode (fn-digest-tagged-preimage tag m))
                  (fn-cbor-ok (cons :bytes tag) m)))
  :hints (("Goal"
           :use ((:instance fn-record-cbor-stream-bytes-round-trip
                            (xs tag) (rest m)))
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-record-cbor-stream-bytes-round-trip))))
```
```lisp
(defthm fn-digest-tagged-preimage-injective
  (implies (and (fn-digest-tagp tag1) (fn-cbor-octet-listp m1)
                (fn-digest-tagp tag2) (fn-cbor-octet-listp m2)
                (<= (+ 3 (len tag1) (len m1)) *fn-cbor-max-input*)
                (<= (+ 3 (len tag2) (len m2)) *fn-cbor-max-input*)
                (equal (fn-digest-tagged-preimage tag1 m1)
                       (fn-digest-tagged-preimage tag2 m2)))
           (and (equal tag1 tag2)
                (equal m1 m2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-digest-tagged-preimage-separates
                            (tag tag1) (m m1))
                 (:instance fn-digest-tagged-preimage-separates
                            (tag tag2) (m m2)))
           :in-theory (disable fn-digest-tagged-preimage-separates
                               fn-digest-tagged-preimage
                               fn-cbor-decode fn-cbor-encode))))
```

### books/statement-invariants.lisp
```lisp
(defthm fn-stmt-decode-items-of-encode-items
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items fuel (fn-stmt-encode-items items))
                  (fn-stmt-ok items)))
  :hints (("Goal" :induct (fn-stmt-items-fuel-induct fuel items)
           :in-theory (disable fn-cbor-decode fn-cbor-encode))))
```
```lisp
(defthm fn-stmt-encode-items-of-decode-items
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (equal (fn-stmt-encode-items
                   (fn-stmt-value (fn-stmt-decode-items fuel octets)))
                  octets))
  :hints (("Goal" :induct (fn-stmt-decode-items fuel octets)
           :in-theory (disable fn-cbor-decode fn-cbor-encode
                               fn-cbor-result-okp fn-cbor-result-value
                               fn-cbor-result-rest
                               fn-stmt-okp fn-stmt-value fn-stmt-rest
                               fn-stmt-ok fn-stmt-ok2 fn-stmt-error))))
```
```lisp
(defthm fn-stmt-header-round-trip
  (implies (fn-stmt-headerp h)
           (equal (fn-stmt-header-decode-exact (fn-stmt-header-encode h))
                  (fn-stmt-ok h)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-header-items h))
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-encoding-bound)
                 (:instance fn-stmt-header-items-length))
           :in-theory (disable fn-stmt-header-items fn-stmt-headerp
                               fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-header-encoding-bound
                               fn-stmt-header-items-length))))
```
```lisp
(defthm fn-stmt-header-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-header-decode-exact octets))
           (equal (fn-stmt-header-encode
                   (fn-stmt-value (fn-stmt-header-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-header-items*))
                 (:instance fn-stmt-header-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-header-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-header-of-items
                               fn-stmt-header-items fn-stmt-encode-items
                               fn-stmt-headerp
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-header-of-items-sound))))
```
```lisp
(defthm fn-stmt-round-trip
  (implies (fn-stmt-p s)
           (equal (fn-stmt-decode-exact (fn-stmt-encode s))
                  (fn-stmt-ok s)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-items s))
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-encoding-bound)
                 (:instance fn-stmt-items-length))
           :in-theory (disable fn-stmt-items fn-stmt-p
                               fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-encoding-bound
                               fn-stmt-items-length))))
```
```lisp
(defthm fn-stmt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-decode-exact octets))
           (equal (fn-stmt-encode (fn-stmt-value (fn-stmt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items
                            (fuel *fn-stmt-max-items*))
                 (:instance fn-stmt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items
                                     *fn-stmt-max-items* octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-of-items
                               fn-stmt-items fn-stmt-encode-items fn-stmt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-of-items-sound))))
```
```lisp
(defthm fn-stmt-sign-is-verified
  (implies (and (fn-sig-seed-p sk)
                (fn-digest-octetsp creator)
                (fn-record-uint32p incarnation)
                (fn-record-uint32p sequence)
                (fn-stmt-predsp preds)
                (fn-stmt-kindp kind)
                (fn-stmt-payloadp payload))
           (fn-stmt-verifiedp
            (fn-stmt-sign sk creator incarnation sequence preds kind payload)
            (fn-sig-public-key sk)))
  :hints (("Goal"
           :in-theory (disable fn-digest-tagged fn-digest-tagged-preimage
                               fn-stmt-header-encode fn-stmt-content-id
                               fn-stmt-signing-preimage fn-stmt-payload-ref
                               fn-digest-octetsp fn-stmt-predsp fn-stmt-kindp
                               fn-record-uint32p fn-sig-signature-p))))
```
```lisp
(defthm fn-stmt-receipt-round-trip
  (implies (fn-stmt-receipt-p r)
           (equal (fn-stmt-receipt-decode-exact (fn-stmt-receipt-encode r))
                  (fn-stmt-ok r)))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (fn-stmt-receipt-items r))
                            (fuel 4))
                 (:instance fn-stmt-receipt-encoding-bound))
           :in-theory (disable fn-stmt-receipt-items fn-stmt-receipt-p
                               fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-encode-items
                               fn-stmt-decode-items-of-encode-items
                               fn-stmt-receipt-encoding-bound))))
```
```lisp
(defthm fn-stmt-receipt-accepted-input-is-canonical
  (implies (fn-stmt-okp (fn-stmt-receipt-decode-exact octets))
           (equal (fn-stmt-receipt-encode
                   (fn-stmt-value (fn-stmt-receipt-decode-exact octets)))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-stmt-encode-items-of-decode-items (fuel 4))
                 (:instance fn-stmt-receipt-of-items-sound
                            (items (fn-stmt-value
                                    (fn-stmt-decode-items 4 octets)))))
           :in-theory (disable fn-stmt-decode-items fn-stmt-receipt-of-items
                               fn-stmt-receipt-items fn-stmt-encode-items
                               fn-stmt-receipt-p
                               fn-stmt-encode-items-of-decode-items
                               fn-stmt-receipt-of-items-sound))))
```
```lisp
(defthm fn-stmt-receipt-bytes-determine-term
  (implies (and (fn-stmt-receipt-p r1)
                (fn-stmt-receipt-p r2)
                (equal (fn-stmt-receipt-encode r1) (fn-stmt-receipt-encode r2)))
           (equal (fn-stmt-receipt-term r1) (fn-stmt-receipt-term r2)))
  :rule-classes nil
  :hints (("Goal" :use fn-stmt-receipt-encode-injective
           :in-theory (disable fn-stmt-receipt-encode fn-stmt-receipt-p))))
```

### books/principal-invariants.lisp
```lisp
(defthm fn-prin-preimage-injective
  (implies (and (fn-sig-public-key-p pk1) (fn-prin-tokenp token1)
                (fn-sig-public-key-p pk2) (fn-prin-tokenp token2)
                (equal (fn-prin-preimage pk1 token1)
                       (fn-prin-preimage pk2 token2)))
           (and (equal pk1 pk2)
                (equal token1 token2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-prin-preimage-decodes (pk pk1) (token token1))
                 (:instance fn-prin-preimage-decodes (pk pk2) (token token2)))
           :in-theory (disable fn-prin-preimage fn-stmt-decode-items
                               fn-prin-preimage-decodes))))
```
```lisp
(defthm fn-prin-sign-succession-advances-key
  (implies (and (fn-prin-statep st)
                (fn-sig-seed-p sk)
                (equal (fn-sig-public-key sk) (fn-prin-state-key st))
                (fn-sig-public-key-p new-pk)
                (< (fn-prin-state-next st) *fn-cbor-max-uint*))
           (equal (fn-prin-state-key
                   (fn-prin-apply-succession
                    st (fn-prin-sign-succession sk st new-pk)))
                  new-pk))
  :hints (("Goal"
           :use ((:instance fn-prin-sign-succession-is-acceptable)
                 (:instance fn-prin-succession-key-of-sign))
           :in-theory (disable fn-prin-sign-succession
                               fn-prin-succession-acceptablep
                               fn-prin-succession-key fn-prin-statep
                               fn-prin-sign-succession-is-acceptable
                               fn-prin-succession-key-of-sign))))
```
```lisp
(defthm fn-prin-first-key-move-is-verified-under-prior-key
  (implies (and (fn-prin-statep st)
                (not (equal (fn-prin-state-key (fn-prin-resolve st stmts))
                            (fn-prin-state-key st))))
           (and (member-equal (fn-prin-first-accepted st stmts) stmts)
                (fn-stmt-verifiedp (fn-prin-first-accepted st stmts)
                                   (fn-prin-state-key st))
                (equal (fn-stmt-creator (fn-prin-first-accepted st stmts))
                       (fn-prin-state-id st))
                (equal (fn-stmt-kind (fn-prin-first-accepted st stmts))
                       :succession)))
  :hints (("Goal" :induct (fn-prin-first-accepted st stmts)
           :in-theory (e/d (fn-prin-apply-succession)
                           (fn-stmt-verifiedp fn-stmt-creator fn-stmt-kind
                            fn-prin-succession-key fn-stmt-p
                            fn-stmt-incarnation fn-stmt-sequence
                            fn-prin-statep)))))
```
```lisp
(defthm fn-prin-trail-is-valid-chain
  (fn-prin-chain-validp st (fn-prin-trail st stmts))
  :hints (("Goal" :induct (fn-prin-trail st stmts)
           :in-theory (disable fn-prin-succession-acceptablep
                               fn-prin-apply-succession))))
```

### books/lace-invariants.lisp
```lisp
(defthm fn-lace-merge-ids-are-union
  (iff (member-equal h (fn-lace-ids (fn-lace-merge lace delta)))
       (or (member-equal h (fn-lace-ids lace))
           (member-equal h (fn-lace-ids delta)))))
```
```lisp
(defthm fn-lace-merge-idempotent
  (implies (true-listp lace)
           (equal (fn-lace-merge lace lace) lace)))
```
```lisp
(defthm fn-lace-merge-commutative-ids
  (fn-lace-same-idsp (fn-lace-merge a b) (fn-lace-merge b a))
  :hints (("Goal"
           :use ((:instance fn-lace-merge-lub
                            (lace a) (delta b) (u (fn-lace-merge b a)))
                 (:instance fn-lace-merge-lub
                            (lace b) (delta a) (u (fn-lace-merge a b))))
           :in-theory (disable fn-lace-merge-lub fn-lace-ids-subsetp
                               fn-lace-merge))))
```
```lisp
(defthm fn-lace-merge-associative-ids
  (fn-lace-same-idsp (fn-lace-merge (fn-lace-merge a b) c)
                     (fn-lace-merge a (fn-lace-merge b c)))
  :hints (("Goal"
           :use ((:instance fn-lace-merge-lub
                            (lace (fn-lace-merge a b)) (delta c)
                            (u (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-merge-lub
                            (lace a) (delta b)
                            (u (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-merge-lub
                            (lace a) (delta (fn-lace-merge b c))
                            (u (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-merge-lub
                            (lace b) (delta c)
                            (u (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a b) (b (fn-lace-merge b c))
                            (c (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a c) (b (fn-lace-merge b c))
                            (c (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a a) (b (fn-lace-merge a b))
                            (c (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a b) (b (fn-lace-merge a b))
                            (c (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-merge-monotone (lace a) (delta b))
                 (:instance fn-lace-merge-monotone
                            (lace (fn-lace-merge a b)) (delta c))
                 (:instance fn-lace-merge-monotone (lace b) (delta c))
                 (:instance fn-lace-merge-monotone
                            (lace a) (delta (fn-lace-merge b c)))
                 (:instance fn-lace-merge-absorbs-delta (lace a) (delta b))
                 (:instance fn-lace-merge-absorbs-delta
                            (lace (fn-lace-merge a b)) (delta c))
                 (:instance fn-lace-merge-absorbs-delta (lace b) (delta c))
                 (:instance fn-lace-merge-absorbs-delta
                            (lace a) (delta (fn-lace-merge b c))))
           :in-theory (disable fn-lace-merge-lub fn-lace-ids-subsetp
                               fn-lace-merge fn-lace-merge-monotone
                               fn-lace-merge-absorbs-delta
                               fn-lace-ids-subsetp-transitive))))
```
```lisp
(defthm fn-lace-merge-monotone
  (fn-lace-ids-subsetp lace (fn-lace-merge lace delta))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness
                                   (a lace) (b (fn-lace-merge lace delta))))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp
                               fn-lace-merge))))
```
```lisp
(defthm fn-lace-merge-lub
  (implies (and (fn-lace-ids-subsetp lace u)
                (fn-lace-ids-subsetp delta u))
           (fn-lace-ids-subsetp (fn-lace-merge lace delta) u))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness
                                   (a (fn-lace-merge lace delta)) (b u)))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp
                               fn-lace-merge))))
```
```lisp
(defthm fn-lace-lookup-of-member
  (implies (and (fn-lace-canonicalp lace)
                (member-equal s lace))
           (equal (fn-lace-lookup lace (fn-stmt-id s)) s))
  :hints (("Goal"
           :use ((:instance fn-lace-cross-canonicalp-elim
                            (a lace) (b lace)
                            (x (fn-lace-lookup lace (fn-stmt-id s))) (y s)))
           :in-theory (disable fn-lace-lookup))))
```
```lisp
(defthm fn-lace-canonical-append-iff
  (iff (fn-lace-canonicalp (append a b))
       (and (fn-lace-canonicalp a)
            (fn-lace-canonicalp b)
            (fn-lace-cross-canonicalp a b)))
  :hints (("Goal" :in-theory (enable fn-lace-canonicalp))))
```
```lisp
(defthm fn-lace-same-view-of-cross-canonical
  (implies (and (fn-lace-same-idsp a b)
                (fn-lace-cross-canonicalp a b))
           (equal (fn-lace-lookup a h) (fn-lace-lookup b h)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((member-equal h (fn-lace-ids a)))
           :use ((:instance fn-lace-cross-canonicalp-elim
                            (x (fn-lace-lookup a h)) (y (fn-lace-lookup b h)))
                 (:instance fn-lace-ids-subsetp-elim (a a) (b b))
                 (:instance fn-lace-ids-subsetp-elim (a b) (b a)))
           :in-theory (disable fn-lace-lookup fn-lace-ids-subsetp
                               fn-lace-ids-subsetp-elim
                               fn-lace-cross-canonicalp
                               fn-lace-no-conflictp-elim))))
```
```lisp
(defthm fn-lace-merge-preserves-canonical
  (implies (and (fn-lace-canonicalp lace)
                (fn-lace-canonicalp delta))
           (fn-lace-canonicalp (fn-lace-merge lace delta)))
  :hints (("Goal"
           :use ((:instance fn-lace-cross-canonicalp-symmetric
                            (a lace) (b (fn-lace-new lace delta))))
           :in-theory (e/d (fn-lace-canonicalp)
                           (fn-lace-cross-canonicalp-symmetric)))))
```
```lisp
(defthm fn-lace-merge-drops-at-collision
  (implies (and (member-equal b lace)
                (equal (fn-stmt-id d) (fn-stmt-id b))
                (not (member-equal d lace)))
           (not (member-equal d (fn-lace-merge lace delta)))))
```
```lisp
(defthm fn-lace-distinct-same-slot-is-equivocation
  (implies (and (member-equal s1 lace)
                (member-equal s2 lace)
                (not (equal s1 s2))
                (fn-lace-same-slotp s1 s2))
           (fn-lace-equivocatorp lace (fn-stmt-creator s1)
                                 (fn-stmt-incarnation s1)))
  :hints (("Goal"
           :use ((:instance fn-lace-slot-conflictp-intro)
                 (:instance fn-lace-equivocator-scan-intro
                            (rest lace)
                            (principal (fn-stmt-creator s1))
                            (incarnation (fn-stmt-incarnation s1))))
           :in-theory (disable fn-lace-slot-conflictp-intro
                               fn-lace-equivocator-scan-intro
                               fn-lace-slot-conflictp
                               fn-lace-equivocator-scan))))
```
```lisp
(defthm fn-lace-reissue-is-equivocation
  (implies (and (not (equal p1 p2))
                (member-equal (fn-stmt-sign sk1 c i n preds1 k1 p1) lace)
                (member-equal (fn-stmt-sign sk2 c i n preds2 k2 p2) lace))
           (fn-lace-equivocatorp lace c i))
  :hints (("Goal"
           :use ((:instance fn-lace-distinct-same-slot-is-equivocation
                            (s1 (fn-stmt-sign sk1 c i n preds1 k1 p1))
                            (s2 (fn-stmt-sign sk2 c i n preds2 k2 p2))))
           :in-theory (disable fn-lace-distinct-same-slot-is-equivocation
                               fn-lace-equivocatorp))))
```
```lisp
(defthm fn-lace-reissue-detected-after-merge
  (implies (and (not (equal p1 p2))
                (not (equal (fn-stmt-id (fn-stmt-sign sk c i n nil :article p1))
                            (fn-stmt-id (fn-stmt-sign sk c i n nil :article p2)))))
           (fn-lace-equivocatorp
            (fn-lace-merge (list (fn-stmt-sign sk c i n nil :article p1))
                           (list (fn-stmt-sign sk c i n nil :article p2)))
            c i))
  :hints (("Goal"
           :use ((:instance fn-lace-reissue-is-equivocation
                            (sk1 sk) (sk2 sk) (preds1 nil) (preds2 nil)
                            (k1 :article) (k2 :article)
                            (lace (fn-lace-merge
                                   (list (fn-stmt-sign sk c i n nil :article p1))
                                   (list (fn-stmt-sign sk c i n nil :article p2))))))
           :in-theory (disable fn-lace-reissue-is-equivocation
                               fn-lace-equivocatorp fn-lace-merge))))
```
```lisp
(defthm fn-lace-merge-preserves-closure
  (implies (and (fn-lace-causally-closedp lace)
                (fn-lace-causally-closedp delta))
           (fn-lace-causally-closedp (fn-lace-merge lace delta)))
  :hints (("Goal"
           :use ((:instance fn-lace-closed-inp-monotone
                            (stmts lace) (a lace)
                            (b (fn-lace-merge lace delta)))
                 (:instance fn-lace-closed-inp-monotone
                            (stmts (fn-lace-new lace delta)) (a delta)
                            (b (fn-lace-merge lace delta)))
                 (:instance fn-lace-closed-inp-of-new (x lace) (lace delta)))
           :in-theory (e/d (fn-lace-causally-closedp)
                           (fn-lace-closed-inp-monotone
                            fn-lace-closed-inp-of-new
                            fn-lace-closed-inp fn-lace-ids-subsetp)))))
```

### books/policy-invariants.lisp
```lisp
(defthm fn-pol-current-unchanged-by-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-current (fn-lace-merge lace delta)
                                  keyring group authority)
                  (fn-pol-current lace keyring group authority)))
  :hints (("Goal" :in-theory (e/d (fn-pol-current)
                                  (fn-lace-merge fn-pol-candidates
                                   fn-pol-latest
                                   fn-pol-same-slot-conflictp)))))
```
```lisp
(defthm fn-pol-admitp-unchanged-by-foreign-delta
  (implies (fn-pol-delta-without-authority-p delta keyring authority)
           (equal (fn-pol-admitp (fn-lace-merge lace delta)
                                 keyring group authority s)
                  (fn-pol-admitp lace keyring group authority s)))
  :hints (("Goal" :in-theory (disable fn-lace-merge fn-pol-current
                                      fn-pol-authorizedp))))
```
```lisp
(defthm fn-pol-policy-change-needs-authority-signature
  (implies (not (equal (fn-pol-current (fn-lace-merge lace delta)
                                       keyring group authority)
                       (fn-pol-current lace keyring group authority)))
           (let ((d (fn-pol-first-authority-stmt delta keyring authority)))
             (and (member-equal d delta)
                  (fn-stmt-p d)
                  (equal (fn-stmt-creator d) authority)
                  (fn-prin-verifiedp d keyring))))
  :hints (("Goal" :in-theory (disable fn-lace-merge fn-pol-current
                                      fn-pol-first-authority-stmt))))
```
```lisp
(defthm fn-pol-admission-is-grounded
  (implies (fn-pol-admitp lace keyring group authority s)
           (let ((p (fn-pol-current lace keyring group authority)))
             (and (member-equal p lace)
                  (fn-pol-candidatep p keyring group authority)
                  (equal (fn-stmt-creator p) authority)
                  (equal (fn-stmt-kind p) :policy)
                  (fn-prin-verifiedp p keyring)
                  (member-equal (fn-stmt-creator s) (fn-pol-authorized-set p))
                  (fn-prin-verifiedp s keyring)
                  (equal (fn-stmt-kind s) :article)
                  (fn-stmt-p s))))
  :hints (("Goal"
           :use ((:instance fn-pol-current-is-candidate-in-lace)
                 (:instance fn-pol-candidatep-implies-authority-stmt
                            (s (fn-pol-current lace keyring group authority))))
           :in-theory (disable fn-pol-current fn-pol-authorized-set
                               fn-pol-current-is-candidate-in-lace
                               fn-pol-candidatep-implies-authority-stmt))))
```
```lisp
(defthm fn-pol-current-is-not-superseded
  (implies (and (member-equal p1 lace)
                (fn-pol-candidatep p1 keyring group authority)
                (member-equal p2 lace)
                (fn-pol-candidatep p2 keyring group authority)
                (fn-pol-slot-lessp p1 p2))
           (not (equal (fn-pol-current lace keyring group authority) p1)))
  :hints (("Goal"
           :use ((:instance fn-pol-latest-is-maximal
                            (cands (fn-pol-candidates lace keyring group
                                                      authority))
                            (c p2))
                 (:instance fn-pol-member-candidate-is-in-candidates (p p2))
                 (:instance fn-pol-candidatep-implies-authority-stmt (s p1)))
           :in-theory (e/d (fn-pol-current)
                           (fn-pol-latest fn-pol-candidates
                            fn-pol-same-slot-conflictp fn-pol-slot-lessp
                            fn-pol-latest-is-maximal
                            fn-pol-member-candidate-is-in-candidates
                            fn-pol-candidatep-implies-authority-stmt)))))
```
```lisp
(defthm fn-pol-receipt-commits-to-term-by-construction
  (implies (fn-pol-admitp lace keyring group authority s)
           (let ((r (fn-pol-make-receipt lace keyring group authority s
                                         obligation)))
             (and (equal (fn-stmt-receipt-term r)
                         (fn-pol-term lace keyring group authority s))
                  (equal (fn-stmt-receipt-policy-id r)
                         (fn-stmt-id (fn-pol-current lace keyring group
                                                     authority)))
                  (equal (fn-stmt-receipt-evidence r)
                         (fn-pol-evidence-digest keyring authority s))
                  (equal (fn-stmt-receipt-subject r) (fn-stmt-id s))
                  (equal (fn-stmt-receipt-obligation r) obligation))))
  :hints (("Goal" :in-theory (disable fn-pol-current fn-pol-authorizedp))))
```
```lisp
(defthm fn-pol-receipt-re-verifiable
  (implies (and (fn-lace-p lace)
                (fn-lace-canonicalp lace)
                (fn-pol-admitp lace keyring group authority s))
           (let ((r (fn-pol-make-receipt lace keyring group authority s
                                         obligation)))
             (and (equal (fn-lace-lookup lace (fn-stmt-receipt-policy-id r))
                         (fn-pol-current lace keyring group authority))
                  (fn-pol-receipt-groundedp r lace keyring group authority))))
  :hints (("Goal"
           :use ((:instance fn-pol-current-is-candidate-in-lace)
                 (:instance fn-lace-lookup-of-member
                            (s (fn-pol-current lace keyring group authority))))
           :in-theory (disable fn-pol-current fn-pol-authorizedp
                               fn-lace-canonicalp
                               fn-pol-current-is-candidate-in-lace
                               fn-lace-lookup-of-member))))
```
```lisp
(defthm fn-pol-signed-receipt-carries-term
  (implies (fn-stmt-receipt-p receipt)
           (and (equal (fn-stmt-receipt-decode-exact
                        (fn-stmt-payload
                         (fn-pol-sign-receipt sk receiver incarnation sequence
                                              preds receipt)))
                       (fn-stmt-ok receipt))
                (equal (fn-stmt-kind
                        (fn-pol-sign-receipt sk receiver incarnation sequence
                                             preds receipt))
                       :receipt)))
  :hints (("Goal"
           :use ((:instance fn-lace-sign-fields
                            (c receiver) (i incarnation) (n sequence)
                            (k :receipt)
                            (p (fn-stmt-receipt-encode receipt))))
           :in-theory (e/d (fn-stmt-kind fn-stmt-sign fn-stmt-header)
                           (fn-lace-sign-fields fn-stmt-receipt-encode
                            fn-stmt-receipt-decode-exact
                            fn-stmt-receipt-p)))))
```


## Dirty and untracked files (`git status --short`, before this commit)

```
M Makefile
 M docs/prefixes.md
?? HANDOFF.md
?? books/crypto-seam.lisp
?? books/lace-invariants.lisp
?? books/lace.lisp
?? books/policy-invariants.lisp
?? books/policy.lisp
?? books/principal-invariants.lisp
?? books/principal.lisp
?? books/statement-invariants.lisp
?? books/statement.lisp
?? planning/decision-packet-d09-d11.md
?? specs/identity.md
?? specs/lace.md
?? specs/policy.md
?? specs/statement.md
?? tests/acl2/crypto-seam-tests.lisp
?? tests/acl2/lace-tests.lisp
?? tests/acl2/policy-tests.lisp
?? tests/acl2/principal-tests.lisp
?? tests/acl2/statement-tests.lisp
```
