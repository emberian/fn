; fn: membership epochs across a partition -- what a reconnected peer
; carries, and what it may not carry.
;
; specs/substrate-transport.md section 4, keystone S5-1 (packet S5).
;
; What crosses a partition is COMMITS AND FORK EVIDENCE, never a roster.
; fn-me-site-merge extends the commits set and leaves the chain alone; only
; fn-me-adopt extends the chain, and adoption is a local act.  The two
; corollaries below are the substrate keystones with a wire-shaped delta;
; the new content of this book is the CARRIER obligation
; fn-stx-commits-of-batch-are-verified-and-well-formed, which is where a
; mistake would hide: without it an unverified article could inject a commit
; and the corollaries would be true of a poisoned delta -- true, and
; worthless.

(in-package "ACL2")
(include-book "stx-policy")
(include-book "stx-commit-codec")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-me-commitp)
                          (:definition fn-me-commitsp))))

(local (in-theory (enable (:d fn-stx-delta) (:d fn-stx-batch-delta))))

; -----------------------------------------------------------------------------
; The commit codec: a membership commit as a statement payload
;
; Five CBOR items in the fn-stmt- item vocabulary, bounded before any item is
; parsed, in the discipline of statement.md: the length bound first, then the
; item budget, then each item.  No allocation is sized by a number the input
; supplied.

(defun fn-stx-commits-of-lace (lace)
  (declare (xargs :guard (fn-lace-p lace)))
  (if (consp lace)
      (let ((c (fn-stx-commit-of-statement (car lace))))
        (if c
            (cons c (fn-stx-commits-of-lace (cdr lace)))
          (fn-stx-commits-of-lace (cdr lace))))
    nil))

(defun fn-stx-commits-of-batch (batch keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (fn-stx-commits-of-lace (fn-stx-batch-delta batch keyring)))

; Every statement in a batch's delta is verified under the local keyring:
; that is what fn-stx-delta is, and it is the hypothesis the carrier
; obligation needs.
(defthm fn-stx-batch-delta-members-are-verified
  (implies (member-equal s (fn-stx-batch-delta batch keyring))
           (fn-prin-verifiedp s keyring))
  :hints (("Goal" :in-theory (enable (:d fn-stx-verifiedp)))))

(defun fn-stx-commit-witness-scan (c delta keyring)
  (declare (xargs :guard (and (fn-lace-p delta) (fn-prin-keyringp keyring))))
  (if (consp delta)
      (or (and (equal (fn-stx-commit-of-statement (car delta)) c)
               (fn-prin-verifiedp (car delta) keyring)
               t)
          (fn-stx-commit-witness-scan c (cdr delta) keyring))
    nil))

(defun fn-stx-every-commit-has-a-verified-statement (commits batch keyring)
  (declare (xargs :guard (and (fn-me-commitsp commits)
                              (fn-prin-keyringp keyring))))
  (if (consp commits)
      (and (fn-stx-commit-witness-scan (car commits)
                                       (fn-stx-batch-delta batch keyring)
                                       keyring)
           (fn-stx-every-commit-has-a-verified-statement (cdr commits) batch
                                                         keyring))
    t))

(local (defthm fn-stx-commits-of-lace-are-commits
         (fn-me-commitsp (fn-stx-commits-of-lace lace))
         :hints (("Goal" :in-theory (disable fn-stx-commit-of-statement)))))

(local (defthm fn-stx-commit-witness-scan-of-member
         (implies (and (member-equal s delta)
                       (equal (fn-stx-commit-of-statement s) c)
                       (fn-prin-verifiedp s keyring))
                  (fn-stx-commit-witness-scan c delta keyring))
         :hints (("Goal" :in-theory (disable fn-stx-commit-of-statement)))))

; Every statement of a lace verifies under this keyring.  The witness scan
; walks the list, so the member-shaped
; fn-stx-batch-delta-members-are-verified is the wrong shape for its
; induction; this is the same fact in the shape the induction consumes.
(local
 (defun fn-stx-lace-verifiedp (lace keyring)
   (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring))))
   (if (consp lace)
       (and (fn-prin-verifiedp (car lace) keyring)
            (fn-stx-lace-verifiedp (cdr lace) keyring))
     t)))

(local (defthm fn-stx-lace-verifiedp-of-append
         (iff (fn-stx-lace-verifiedp (append a b) keyring)
              (and (fn-stx-lace-verifiedp a keyring)
                   (fn-stx-lace-verifiedp b keyring)))))

(local (defthm fn-stx-lace-verifiedp-of-delta
         (fn-stx-lace-verifiedp (fn-stx-delta octets keyring) keyring)
         :hints (("Goal" :in-theory (enable (:d fn-stx-verifiedp))))))

(local (defthm fn-stx-lace-verifiedp-of-batch-delta
         (fn-stx-lace-verifiedp (fn-stx-batch-delta batch keyring) keyring)
         :hints (("Goal" :induct (fn-stx-batch-delta batch keyring)
                  :in-theory (disable fn-stx-delta)))))

; The hypothesis is the verification of the delta, not its lace shape.  As
; first written this lemma asked only (fn-lace-p delta) and was FALSE: the
; scan's disjunct requires (fn-prin-verifiedp (car delta) keyring), and an
; arbitrary lace supplies no such thing -- ACL2's checkpoint was exactly
; (implies (fn-stmt-p delta1) (fn-prin-verifiedp delta1 keyring)).  The
; hypothesis holds on every reachable delta: fn-stx-batch-delta is built out
; of fn-stx-delta, which is a singleton only for a verified statement.
(local (defthm fn-stx-commits-of-lace-have-witnesses
         (implies (and (member-equal c (fn-stx-commits-of-lace delta))
                       (fn-stx-lace-verifiedp delta keyring))
                  (fn-stx-commit-witness-scan c delta keyring))
         :rule-classes nil
         :hints (("Goal" :induct (fn-stx-commits-of-lace delta)
                  :in-theory (disable fn-stx-commit-of-statement)))))

(local (defthm fn-stx-subsetp-equal-cons
         (implies (subsetp-equal a b)
                  (subsetp-equal a (cons x b)))))

(local (defthm fn-stx-subsetp-equal-reflexive
         (subsetp-equal x x)))

(local (defthm fn-stx-every-commit-by-sublist
         (implies (and (subsetp-equal commits
                                      (fn-stx-commits-of-lace
                                       (fn-stx-batch-delta batch keyring))))
                  (fn-stx-every-commit-has-a-verified-statement commits batch
                                                                keyring))
         :hints (("Goal" :induct (fn-stx-every-commit-has-a-verified-statement
                                  commits batch keyring)
                  :in-theory (disable fn-stx-commit-witness-scan
                                      fn-stx-commits-of-lace
                                      fn-stx-batch-delta
                                      (:d fn-stx-lace-verifiedp)))
                 ; The scheme is three-way (base, no witness, witness), so
                 ; the case that needs the witness is *1/2, not *1/1.
                 ("Subgoal *1/2"
                  :use ((:instance fn-stx-commits-of-lace-have-witnesses
                                   (c (car commits))
                                   (delta (fn-stx-batch-delta batch
                                                              keyring))))))))

; S5-1's carrier obligation.  Without the keyring hypothesis an unverified
; article could inject a commit.
(defthm fn-stx-commits-of-batch-are-verified-and-well-formed
  (implies (fn-prin-keyringp keyring)
           (and (fn-me-commitsp (fn-stx-commits-of-batch batch keyring))
                (fn-stx-every-commit-has-a-verified-statement
                 (fn-stx-commits-of-batch batch keyring) batch keyring)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-stx-commits-of-lace fn-stx-batch-delta
                               fn-stx-every-commit-has-a-verified-statement))))

; -----------------------------------------------------------------------------
; The two corollaries (labelled as corollaries; the keystones are the
; membership-epochs theorems named beside each)

(defthm fn-stx-reconnect-never-revises-admissibility   ; corollary of
  (implies (and (fn-me-sitep site)                     ; fn-me-site-merge-never-
                (fn-prin-keyringp keyring)             ; revises-admissibility
                (fn-me-messagep msg))
           (equal (fn-me-decide
                   (fn-me-site-merge site
                                     (fn-stx-commits-of-batch batch keyring))
                   msg)
                  (fn-me-decide site msg)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-me-site-merge-never-revises-admissibility
                            (delta (fn-stx-commits-of-batch batch keyring)))
                 (:instance fn-stx-commits-of-batch-are-verified-and-well-formed))
           :in-theory (disable fn-me-site-merge-never-revises-admissibility
                               fn-stx-commits-of-batch-are-verified-and-well-formed
                               fn-stx-commits-of-batch fn-me-site-merge
                               fn-me-decide))))

(defthm fn-stx-reconnect-does-not-extend-the-chain     ; corollary of
  (implies (and (fn-me-sitep site)                     ; fn-me-site-merge-
                (fn-prin-keyringp keyring))            ; preserves-chain
           (and (equal (fn-me-chain
                        (fn-me-site-merge
                         site (fn-stx-commits-of-batch batch keyring)))
                       (fn-me-chain site))
                (equal (fn-me-epoch
                        (fn-me-site-merge
                         site (fn-stx-commits-of-batch batch keyring)))
                       (fn-me-epoch site))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-me-site-merge-preserves-chain
                            (delta (fn-stx-commits-of-batch batch keyring)))
                 (:instance fn-stx-commits-of-batch-are-verified-and-well-formed))
           :in-theory (disable fn-me-site-merge-preserves-chain
                               fn-stx-commits-of-batch-are-verified-and-well-formed
                               fn-stx-commits-of-batch fn-me-site-merge
                               fn-me-chain fn-me-epoch))))

(defthm fn-stx-reconnect-exposes-the-partition         ; corollary of
  (implies (and (fn-me-commitsp a)                     ; fn-me-merge-exposes-
                (fn-prin-keyringp keyring)             ; the-partition
                (member-equal ca a)
                (member-equal cb (fn-stx-commits-of-batch batch keyring))
                (equal (fn-me-commit-base ca) (fn-me-commit-base cb))
                (not (equal (fn-me-commit-id ca) (fn-me-commit-id cb)))
                (not (member-equal (fn-me-commit-id cb) (fn-me-commit-ids a))))
           (and (member-equal ca (fn-me-merge
                                  a (fn-stx-commits-of-batch batch keyring)))
                (member-equal cb (fn-me-merge
                                  a (fn-stx-commits-of-batch batch keyring)))
                (fn-me-forkedp (fn-me-merge
                                a (fn-stx-commits-of-batch batch keyring)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-me-merge-exposes-the-partition
                            (b (fn-stx-commits-of-batch batch keyring)))
                 (:instance fn-stx-commits-of-batch-are-verified-and-well-formed))
           :in-theory (disable fn-me-merge-exposes-the-partition
                               fn-stx-commits-of-batch-are-verified-and-well-formed
                               fn-stx-commits-of-batch fn-me-merge
                               fn-me-forkedp))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(in-theory (disable (:d fn-stx-commit-of-statement) (:d fn-stx-commits-of-lace)
                    (:d fn-stx-commits-of-batch) (:d fn-stx-commit-witness-scan)
                    (:d fn-stx-every-commit-has-a-verified-statement)
                    (:d fn-stx-op-of-code) (:d fn-stx-op-code)))
