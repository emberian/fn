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
(include-book "membership-epochs-invariants")

(local (in-theory (enable (:d fn-stx-delta) (:d fn-stx-batch-delta))))

; -----------------------------------------------------------------------------
; The commit codec: a membership commit as a statement payload
;
; Five CBOR items in the fn-stmt- item vocabulary, bounded before any item is
; parsed, in the discipline of statement.md: the length bound first, then the
; item budget, then each item.  No allocation is sized by a number the input
; supplied.

(defconst *fn-stx-max-commit-octets* 512)

(defun fn-stx-op-of-code (n)
  (declare (xargs :guard t))
  (cond ((equal n 0) :add)
        ((equal n 1) :remove)
        ((equal n 2) :rotate)
        (t nil)))

(defun fn-stx-op-code (op)
  (declare (xargs :guard t))
  (cond ((equal op :add) 0)
        ((equal op :remove) 1)
        ((equal op :rotate) 2)
        (t 3)))

(defthm fn-stx-op-of-code-is-an-op
  (implies (fn-stx-op-of-code n)
           (fn-me-opp (fn-stx-op-of-code n))))

(defun fn-stx-commit-items (c)
  (declare (xargs :guard (fn-me-commitp c)))
  (list (cons :bytes (fn-me-commit-id c))
        (cons :uint (fn-me-commit-base c))
        (cons :bytes (fn-me-commit-actor c))
        (cons :uint (fn-stx-op-code (fn-me-commit-op c)))
        (cons :bytes (fn-me-commit-subject c))))

(defun fn-stx-commit-encodablep (c)
  (declare (xargs :guard t))
  (and (fn-me-commitp c)
       (fn-cbor-octet-listp (fn-me-commit-id c))
       (fn-record-uint32p (fn-me-commit-base c))
       (fn-cbor-octet-listp (fn-me-commit-actor c))
       (fn-cbor-octet-listp (fn-me-commit-subject c))))

(defun fn-stx-commit-encode (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-stx-commit-encodablep c)
      (fn-stmt-encode-items (fn-stx-commit-items c))
    nil))

(defun fn-stx-commit-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory
                                 (enable fn-stmt-uint-item-p
                                         fn-stmt-bytes-item-p)))))
  (if (not (and (consp items) (fn-stmt-bytes-item-p (car items))))
      (fn-stmt-error :id)
    (let ((i1 (cdr items)))
      (if (not (and (consp i1) (fn-stmt-uint-item-p (car i1))))
          (fn-stmt-error :base)
        (let ((i2 (cdr i1)))
          (if (not (and (consp i2) (fn-stmt-bytes-item-p (car i2))))
              (fn-stmt-error :actor)
            (let ((i3 (cdr i2)))
              (if (not (and (consp i3) (fn-stmt-uint-item-p (car i3))
                            (fn-stx-op-of-code (cdr (car i3)))))
                  (fn-stmt-error :op)
                (let ((i4 (cdr i3)))
                  (if (not (and (consp i4) (fn-stmt-bytes-item-p (car i4))))
                      (fn-stmt-error :subject)
                    (if (not (null (cdr i4)))
                        (fn-stmt-error :trailing)
                      (fn-stmt-ok
                       (fn-me-commit (cdr (car items)) (cdr (car i1))
                                     (cdr (car i2))
                                     (fn-stx-op-of-code (cdr (car i3)))
                                     (cdr (car i4)))))))))))))))

(defun fn-stx-commit-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stx-max-commit-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items 5 octets)))
      (if (not (fn-stmt-okp items))
          items
        (fn-stx-commit-of-items (fn-stmt-value items))))))

(defthm fn-stx-commit-decode-is-a-commit
  (implies (fn-stmt-okp (fn-stx-commit-decode-exact octets))
           (fn-me-commitp (fn-stmt-value (fn-stx-commit-decode-exact octets))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-me-commitp fn-me-commit fn-stmt-uint-item-p
                            fn-record-uint32p fn-me-opp
                            (:d fn-stx-commit-of-items)
                            (:d fn-stx-commit-decode-exact))
                           (fn-stmt-decode-items fn-cbor-at-mostp)))))

(in-theory (disable (:d fn-stx-commit-of-items)
                    (:d fn-stx-commit-decode-exact)
                    (:d fn-stx-commit-encode)))

; -----------------------------------------------------------------------------
; The commits a contact batch carries
;
; A commit enters only from a VERIFIED statement: fn-stx-batch-delta is
; already the verified projection, so the scan below never sees an
; unverified article's payload.

(defun fn-stx-commit-of-statement (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (if (not (equal (fn-stmt-kind s) :policy))
      nil
    (let ((r (fn-stx-commit-decode-exact (fn-stmt-payload s))))
      (if (fn-stmt-okp r)
          (fn-stmt-value r)
        nil))))

(defthm fn-stx-commit-of-statement-is-a-commit
  (implies (fn-stx-commit-of-statement s)
           (fn-me-commitp (fn-stx-commit-of-statement s)))
  :hints (("Goal" :in-theory (disable fn-stx-commit-decode-exact))))

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

(local (defthm fn-stx-commits-of-lace-have-witnesses
         (implies (and (member-equal c (fn-stx-commits-of-lace delta))
                       (fn-lace-p delta))
                  (fn-stx-commit-witness-scan c delta keyring))
         :rule-classes nil
         :hints (("Goal" :induct (fn-stx-commits-of-lace delta)
                  :in-theory (disable fn-stx-commit-of-statement)))))

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
                                      fn-stx-batch-delta))
                 ("Subgoal *1/1"
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
