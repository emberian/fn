# Handoff: w3/private-profile (packet C3-08)

Branch `w3/private-profile`, branched from `dev` at `9321344`.
HEAD at handoff: see the last commit on this branch (`git log --oneline -1`).

This lane invented no cryptography and selected no protocol. It produced a
reviewable design packet and one executable policy model.

## Certification status

**All three roots certified by ACL2 in this worktree**, one book at a time:

```
books/membership-epochs                 ACL2 certification passed
books/membership-epochs-invariants      ACL2 certification passed
tests/acl2/membership-epochs-tests      ACL2 certification passed
```

Evidence directories: `build/acl2/certify-20260919T153804Z-85696`, `build/acl2/certify-20260919T153833Z-85852`, `build/acl2/certify-20260919T153835Z-85866`.
The roots include no fn book -- only the system books `arithmetic/top`
(local, in the invariants book) and `std/testing/must-fail` (in the test
book) -- so they did not depend on the lane's interrupted baseline run, which
root moved to a remote box. `make check` is green: 106 Markdown files, 50
requirements, 18 proof targets, 18 scenarios; ledger cited events exist and
are not SUSPECT. `tools/ledger.py` flags no SUSPECT theorem in any of the
three books. The full-tree `make certify` for this branch has NOT been run
here and remains the integrator's step.

Three certification fixes were needed and are in the committed source: a
`true-listp` lemma for the roster fold (without it the `fn-me-decide` guard
proof pushed a subgoal subsumed by its own parent), `:verify-guards nil` on
the local induction scheme (`cdr` of an arbitrary second chain has no guard),
and reflexivity of the chain-prefix order (`fn-me-adopt` is a no-op on a
commit premised on the wrong epoch).

## What landed

- `books/membership-epochs.lisp` — the policy model. Commits over an explicit
  base epoch, a site's adopted chain separate from its evidence set, the
  lace-shaped merge with first-class fork evidence, rosters, revocation
  knowledge, and a four-outcome admissibility decision (`:admit`, `:hold`,
  `:refuse`, `:capacity`). No keys, no ciphertext, no digest.
- `books/membership-epochs-invariants.lisp` — the keystones, quoted verbatim
  below.
- `tests/acl2/membership-epochs-tests.lisp` — the partition witness (two sites
  remove different members at the same epoch) and one `must-fail` per
  hypothesis of each keystone.
- `planning/private-profile-packet.md` — threat/metadata matrix, a section per
  decision-agenda row, archive/key separation, the equality-leakage policy, and
  the MLS/HPKE evaluation with dated citations.
- `specs/privacy.md` — links the packet and the model; SEC-004's design cases
  are now a table, each row naming a theorem or a packet section.
- `Makefile` (three roots after `tests/acl2/clock-tests`), `docs/prefixes.md`
  (`fn-me-` row), regenerated `planning/ledger.*` and `planning/proofs.json`.

## The packet's recommendations, in ten lines

1. A private NNTP gateway IS a trusted endpoint; list it in the profile and
   refuse private groups on any other listener.
2. Partitioned membership: keep both commits, report the fork, never tie-break
   inside a merge; resolution is a separate authorized act.
3. History: a joiner or replacement device reads nothing from before it joined;
   archive transfer is explicit and separately authorized.
4. Delayed delivery: an epoch **window** behind and a bounded **hold** ahead,
   both stated in epochs, never in wall-clock time.
5. Keep three stores apart — retained ciphertext, endpoint plaintext archive,
   live crypto state — and never put a secret in the replicated store.
6. Deleting an epoch secret is not a retention release; the vocabularies must
   not merge, or an operator will "release" an archive by deleting a key.
7. Authorship: public articles keep D02's transferable signature; private
   articles are group-attributable by default, under a separate profile.
8. Content ids under a private profile become **keyed** identities; the
   unkeyed `sha256:` derivation is a plaintext-equality and guessing oracle.
9. MLS does not fit as specified — RFC 9420 §14 needs a conflict-resolution
   rule fn cannot supply, and OpenMLS treats a fork as a bug to recover from.
10. HPKE sender keys fit fn's ordering and hand fn the forward-secrecy and
    revocation-delay problem instead. Neither is selected; §7 lists the gates.

## Theorems, verbatim

From `books/membership-epochs-invariants.lisp`:

```lisp
(defthm fn-me-revoked-scan-stable-under-prefix
  (implies (and (fn-me-chain-prefixp a b)
                (< 0 (fn-me-revoked-scan a member index)))
           (equal (fn-me-revoked-scan b member index)
                  (fn-me-revoked-scan a member index)))
  :hints (("Goal" :induct (fn-me-revoked-induct a b member index))))

(defthm fn-me-roster-fold-omits-removed
  (implies (and (not (fn-me-addsp member chain))
                (not (member-equal member roster)))
           (not (member-equal member (fn-me-roster-fold roster chain)))))

(defthm fn-me-revoked-sender-is-not-admitted
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (< 0 (fn-me-revoked-at site (fn-me-msg-sender msg)))
                (<= (fn-me-revoked-at site (fn-me-msg-sender msg))
                    (fn-me-msg-epoch msg)))
           (not (equal (fn-me-decide site msg) :admit))))

(defthm fn-me-revoked-refusal-is-monotone
  (implies (and (fn-me-sitep a)
                (fn-me-sitep b)
                (fn-me-messagep msg)
                (fn-me-knowledge-extendsp a b)
                (< 0 (fn-me-revoked-at a (fn-me-msg-sender msg)))
                (<= (fn-me-revoked-at a (fn-me-msg-sender msg))
                    (fn-me-msg-epoch msg)))
           (equal (fn-me-decide b msg) :refuse))
  :hints (("Goal"
           :use ((:instance fn-me-revoked-scan-stable-under-prefix
                            (a (fn-me-chain a))
                            (b (fn-me-chain b))
                            (member (fn-me-msg-sender msg))
                            (index 0))))))

(defthm fn-me-decide-outcome
  (implies (and (fn-me-sitep site) (fn-me-messagep msg))
           (member-equal (fn-me-decide site msg) *fn-me-outcomes*)))

(defthm fn-me-ahead-message-is-held
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (equal (fn-me-decide site msg) :hold))
           (and (member-equal msg (fn-me-held (fn-me-receive site msg)))
                (equal (len (fn-me-held (fn-me-receive site msg)))
                       (+ 1 (len (fn-me-held site)))))))

(defthm fn-me-hold-count-bounded
  (implies (and (fn-me-sitep site)
                (fn-me-messagep msg)
                (<= (len (fn-me-held site)) (fn-me-hold-limit site)))
           (<= (len (fn-me-held (fn-me-receive site msg)))
               (fn-me-hold-limit site))))

(defthm fn-me-hold-resolves-on-reaching-epoch
  (implies (and (fn-me-sitep a)
                (fn-me-sitep b)
                (fn-me-messagep msg)
                (equal (fn-me-decide a msg) :hold)
                (<= (fn-me-msg-epoch msg) (fn-me-epoch b))
                (<= (fn-me-epoch b) (+ (fn-me-msg-epoch msg) (fn-me-window b)))
                (equal (fn-me-revoked-at b (fn-me-msg-sender msg)) 0)
                (member-equal (fn-me-msg-sender msg)
                              (fn-me-roster-at b (fn-me-msg-epoch msg))))
           (and (member-equal msg (fn-me-held (fn-me-receive a msg)))
                (equal (fn-me-decide b msg) :admit))))

(defthm fn-me-adopt-extends-chain
  (implies (and (fn-me-sitep site) (fn-me-commitp commit))
           (fn-me-chain-prefixp (fn-me-chain site)
                                (fn-me-chain (fn-me-adopt site commit)))))

(defthm fn-me-adopt-advances-epoch
  (implies (and (fn-me-sitep site)
                (fn-me-commitp commit)
                (equal (fn-me-commit-base commit) (fn-me-epoch site)))
           (equal (fn-me-epoch (fn-me-adopt site commit))
                  (+ 1 (fn-me-epoch site)))))

(defthm fn-me-merge-keeps-left-ids
  (implies (member-equal id (fn-me-commit-ids a))
           (member-equal id (fn-me-commit-ids (fn-me-merge a b)))))

(defthm fn-me-merge-keeps-right-ids
  (implies (member-equal id (fn-me-commit-ids b))
           (member-equal id (fn-me-commit-ids (fn-me-merge a b)))))

(defthm fn-me-merge-invents-no-ids
  (implies (member-equal id (fn-me-commit-ids (fn-me-merge a b)))
           (or (member-equal id (fn-me-commit-ids a))
               (member-equal id (fn-me-commit-ids b))))
  :rule-classes nil)

(defthm fn-me-merge-ids-are-order-independent
  (implies (member-equal id (fn-me-commit-ids (fn-me-merge a b)))
           (member-equal id (fn-me-commit-ids (fn-me-merge b a))))
  :hints (("Goal" :use ((:instance fn-me-merge-invents-no-ids)))))

(defthm fn-me-merge-exposes-the-partition
  (implies (and (fn-me-commitsp a)
                (fn-me-commitsp b)
                (member-equal ca a)
                (member-equal cb b)
                (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))
                (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids a))))
           (and (member-equal ca (fn-me-merge a b))
                (member-equal cb (fn-me-merge a b))
                (fn-me-forkedp (fn-me-merge a b))))
  :hints (("Goal"
           :use ((:instance fn-me-conflict-with-finds-a-conflict
                            (c ca) (other cb) (commits (fn-me-merge a b)))
                 (:instance fn-me-fork-scan-detects-a-conflict
                            (c ca) (rest (fn-me-merge a b))
                            (commits (fn-me-merge a b)))
                 (:instance fn-me-new-retains-unknown-commits
                            (c cb) (delta b) (commits a))))))

(defthm fn-me-site-merge-preserves-chain
  (implies (and (fn-me-sitep site) (fn-me-commitsp delta))
           (and (equal (fn-me-chain (fn-me-site-merge site delta))
                       (fn-me-chain site))
                (equal (fn-me-epoch (fn-me-site-merge site delta))
                       (fn-me-epoch site)))))

(defthm fn-me-site-merge-never-revises-admissibility
  (implies (and (fn-me-sitep site)
                (fn-me-commitsp delta)
                (fn-me-messagep msg))
           (equal (fn-me-decide (fn-me-site-merge site delta) msg)
                  (fn-me-decide site msg))))
```

## What is open, and what must not be claimed

- No cryptography exists in fn. Certifying these books says nothing about any
  cipher, ratchet, signature or key schedule. The model's own header records
  the assumption it does not prove: it cannot refuse a message a revoked member
  manufactures while claiming a pre-revocation epoch. That is epoch-bound
  authentication's job, in a protocol not yet selected.
- Device loss/rejoin, compromise, replay, backup and state rollback have packet
  sections but no model; `specs/privacy.md`'s SEC-004 table marks each one open.
- The re-admission policy (`fn-me-no-readmissionp`) is a lane recommendation,
  not a user decision. It is what makes revocation monotone under partition;
  if the user wants re-admission under the same identity, the monotonicity
  keystone has to be restated and the teeth case in the test book explains why.
- D04 is unchanged: shared community groups first, private groups deferred.
