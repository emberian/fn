; fn: the record log's txids (T5 of planning/design-2026-09-27-storage-log.md,
; section 5.1: allocation non-reuse over the durable history).
;
; The kernel (books/store-log-kernel.lisp) carries records as opaque octets.
; This book reads each record's txid through the record codec
; (fn-record-decode-exact-impl, books/records.lisp: the host's decoder) and
; adds the allocation rule to the kernel:
;
;   fn-lgt-prepare     admits a record only when its txid is the kernel's
;                      NEXT-TXID (otherwise the state is unchanged: the owner
;                      stamped a stale or future txid);
;   fn-lgt-recover     the recovered kernel's NEXT-TXID is one past the
;                      largest txid the scan reads, or the checkpoint's floor
;                      when that is larger.
;
; The invariant fn-lgt-okp: along COMMITTED ++ INFLIGHT ++ BATCH every record
; decodes and the txids strictly increase, each below NEXT-TXID.  Every
; kernel transition preserves it (fn-lgt-*-preserves-okp), and
;
;   fn-lg-txids-strictly-increase (T5)  a crash image of any related state
;                      whose damaged entry is a platform tear (the premise of
;                      T2's A-CRYPTO-TRAILER corollary) recovers to a kernel
;                      satisfying fn-lgt-okp: the durable txids strictly
;                      increase along the scan and the recovered NEXT-TXID
;                      exceeds every one of them, so no durable txid is
;                      handed out again.
(in-package "ACL2")

(include-book "store-log-recover")
(include-book "records")

(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The codec's txid.

(defun fn-lgt-txid (record)
  (declare (xargs :guard t))
  (let ((r (fn-record-decode-exact-impl record)))
    (if (fn-record-parse-okp r)
        (ec-call (fn-record-txid (fn-record-parse-value r)))
      nil)))

; Every record from the front decodes, its txid is at least LOW and below
; NEXT, and the rest continue strictly above it.
(defun fn-lgt-chainp (records low next)
  (declare (xargs :guard t))
  (if (atom records)
      t
    (let ((x (fn-lgt-txid (car records))))
      (and (natp x) (<= (nfix low) x) (< x (nfix next))
           (fn-lgt-chainp (cdr records) (1+ x) next)))))

; One past the largest txid of RECORDS, or FLOOR when that is larger.
(defun fn-lgt-next-after (records floor)
  (declare (xargs :guard t))
  (if (atom records)
      (nfix floor)
    (max (1+ (nfix (fn-lgt-txid (car records))))
         (fn-lgt-next-after (cdr records) floor))))

; The kernel's allocation invariant.
(defun fn-lgt-okp (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgt-chainp (append (true-list-fix (fn-lgk-committed ks))
                         (true-list-fix (fn-lgk-inflight ks))
                         (true-list-fix (fn-lgk-batch ks)))
                 0 (fn-lgk-next-txid ks)))

; -----------------------------------------------------------------------------
; The transitions the host calls in place of the kernel's prepare and
; recover.

(defun fn-lgt-prepare (ks record)
  (declare (xargs :guard (true-listp ks)))
  (if (equal (fn-lgt-txid record) (fn-lgk-next-txid ks))
      (fn-lgk-prepare ks record)
    ks))

(defun fn-lgt-recover (c genesis unit max floor)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-recover c genesis unit max
                  (fn-lgt-next-after (car (fn-lg-scan c genesis unit max)) floor)))

; -----------------------------------------------------------------------------
; The chain's algebra.

(local (in-theory (disable fn-lgt-txid)))

(defun fn-lgt-chainp-prefix-ind (p b low)
  (declare (xargs :guard t))
  (if (and (consp p) (consp b))
      (fn-lgt-chainp-prefix-ind (cdr p) (cdr b) (1+ (nfix (fn-lgt-txid (car b)))))
    low))

(defthm fn-lgt-chainp-of-true-list-fix
  (equal (fn-lgt-chainp (true-list-fix x) low next) (fn-lgt-chainp x low next)))

(defthm fn-lgt-append-true-list-fix
  (equal (append (true-list-fix x) y) (append x y)))

(defthm fn-lgt-true-list-fix-of-append
  (equal (true-list-fix (append x y)) (append x (true-list-fix y))))

(defthm fn-lgt-append-nil
  (equal (append x nil) (true-list-fix x)))

(defthm fn-lgt-chainp-of-append-true-list-fix
  (equal (fn-lgt-chainp (append a (true-list-fix b)) low next)
         (fn-lgt-chainp (append a b) low next))
  :hints (("Goal" :induct (fn-lgt-chainp a low next) :in-theory (enable fn-lgt-chainp))))

(defthm fn-lgt-chainp-of-prefix
  (implies (and (fn-lgt-chainp b low next) (fn-lg-prefixp p b))
           (fn-lgt-chainp p low next))
  :hints (("Goal" :induct (fn-lgt-chainp-prefix-ind p b low))))

(defthm fn-lgt-chainp-of-append-prefix
  (implies (and (fn-lgt-chainp (append a b) low next) (fn-lg-prefixp p b))
           (fn-lgt-chainp (append a p) low next))
  :hints (("Goal" :induct (fn-lgt-chainp a low next))))

(defthm fn-lgt-chainp-of-bigger-next
  (implies (and (fn-lgt-chainp x low next) (<= (nfix next) (nfix n2)))
           (fn-lgt-chainp x low n2)))

(defthm fn-lgt-chainp-of-smaller-low
  (implies (and (fn-lgt-chainp x low next) (<= (nfix l2) (nfix low)))
           (fn-lgt-chainp x l2 next)))

(defthm fn-lgt-chainp-of-snoc
  (implies (and (fn-lgt-chainp x low next) (<= (nfix low) (nfix next))
                (equal (fn-lgt-txid r) (nfix next)))
           (fn-lgt-chainp (append x (list r)) low (1+ (nfix next)))))

(defthm fn-lgt-next-after-bounds
  (and (<= (nfix floor) (fn-lgt-next-after x floor))
       (natp (fn-lgt-next-after x floor)))
  :rule-classes ((:linear :corollary (<= (nfix floor) (fn-lgt-next-after x floor)))
                 (:type-prescription :corollary (natp (fn-lgt-next-after x floor)))))

(defthm fn-lgt-chainp-below-next-after
  (implies (fn-lgt-chainp x low next)
           (fn-lgt-chainp x low (fn-lgt-next-after x floor)))
  :hints (("Goal" :induct (fn-lgt-chainp x low next))
          ("Subgoal *1/2"
           :use ((:instance fn-lgt-chainp-of-bigger-next
                            (x (cdr x)) (low (1+ (fn-lgt-txid (car x))))
                            (next (fn-lgt-next-after (cdr x) floor))
                            (n2 (fn-lgt-next-after x floor)))))))

(defthm fn-lgt-chainp-of-append-drop
  (implies (fn-lgt-chainp (append a b) low next)
           (fn-lgt-chainp a low next)))

; -----------------------------------------------------------------------------
; The transitions preserve the invariant.

(local (in-theory (disable fn-lgt-chainp)))

(defthm fn-lgt-prepare-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgt-prepare ks record)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgt-chainp-of-snoc
                            (x (append (true-list-fix (fn-lgk-committed ks))
                                       (true-list-fix (fn-lgk-inflight ks))
                                       (true-list-fix (fn-lgk-batch ks))))
                            (low 0) (next (fn-lgk-next-txid ks)) (r record))))))

(defthm fn-lgt-known-abort-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgk-known-abort ks))))

(defthm fn-lgt-append-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgk-append ks unit extent)))
  :hints (("Goal" :in-theory (disable fn-lgk-fitsp))))

(defthm fn-lgt-fence-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgk-fence ks unit))))

(defthm fn-lgt-fence-failed-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgk-fence-failed ks))))

(defthm fn-lgt-finish-one-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-lgk-finish-one ks))))

; The kernel's own relation is preserved by the checked prepare.
(defthm fn-lgt-prepare-preserves-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgk-relp bs (fn-lgt-prepare ks record) ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-relp fn-lgk-prepare fn-lg-recordp))))

; -----------------------------------------------------------------------------
; T5.

; The recovered kernel of a scan that reads COMMITTED ++ P, P a prefix of the
; batch in flight, satisfies the invariant.
(defthm fn-lgt-prefixp-of-true-list-fix
  (equal (fn-lg-prefixp p (true-list-fix b)) (fn-lg-prefixp p b)))

(defthm fn-lgt-chain-of-a-prefix-of-the-history
  (implies (and (fn-lgt-chainp (append cm inf b) 0 n)
                (fn-lg-prefixp p inf)
                (equal recs (append cm p)))
           (fn-lgt-chainp recs 0 (fn-lgt-next-after recs floor)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgt-chainp-of-append-prefix fn-lgt-chainp-below-next-after
                               fn-lgt-chainp-of-append-drop)
           :use ((:instance fn-lgt-chainp-of-append-drop (a (append cm inf)) (b b) (low 0) (next n))
                 (:instance fn-lgt-chainp-of-append-prefix (a cm) (b inf) (low 0) (next n))
                 (:instance fn-lgt-chainp-below-next-after (x recs) (low 0) (next n))))))

(defthm fn-lgt-okp-of-recover
  (equal (fn-lgt-okp (fn-lgk-recover c genesis unit max n))
         (fn-lgt-chainp (car (fn-lg-scan c genesis unit max)) 0 (nfix n)))
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last))))

(defthm fn-lgt-recovered-okp-of-verdict
  (implies (and (fn-lgt-okp ks)
                (fn-lg-crash-verdictp (fn-lg-scan c genesis unit max)
                                      (fn-lgk-committed ks) f (fn-lgk-inflight ks)
                                      last unit))
           (fn-lgt-okp (fn-lgt-recover c genesis unit max floor)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-crash-verdictp)
                           (fn-lg-scan fn-lg-scan-last fn-lgk-recover fn-lg-log fn-lgt-okp
                            fn-lgk-committed fn-lgk-inflight fn-lgk-batch fn-lgk-next-txid))
           :use ((:instance fn-lgt-chain-of-a-prefix-of-the-history
                            (cm (true-list-fix (fn-lgk-committed ks)))
                            (inf (true-list-fix (fn-lgk-inflight ks)))
                            (b (true-list-fix (fn-lgk-batch ks)))
                            (n (fn-lgk-next-txid ks))
                            (p (nthcdr (len (fn-lgk-committed ks))
                                       (car (fn-lg-scan c genesis unit max))))
                            (recs (car (fn-lg-scan c genesis unit max))))
                 (:instance fn-lgt-okp)))))

(defthm fn-lg-txids-strictly-increase
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (fn-lgt-okp ks)
                (consp (fn-lgk-inflight ks))
                (fn-bs-crash-imagep bs image)
                (fn-lg-platform-tears-p
                 (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                 (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
           (fn-lgt-okp (fn-lgt-recover (fn-bs-durable-content image ino)
                                       genesis (fn-bs-unit bs) max floor)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgk-relp fn-lgt-okp fn-lgt-recover fn-lg-crash-verdictp
                               fn-lg-forgery-in fn-lg-platform-tears-p fn-bs-crash-imagep
                               fn-bs-durable-content fn-lg-scan)
           :use ((:instance fn-lgk-crash-of-related-state-is-a-prefix)
                 (:instance fn-lg-no-forgery-under-a-crypto-trailer
                            (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino)))
                            (batch (fn-lgk-inflight ks)) (prev (fn-lgk-last ks))
                            (unit (fn-bs-unit bs)))
                 (:instance fn-lgt-recovered-okp-of-verdict
                            (c (fn-bs-durable-content image ino)) (unit (fn-bs-unit bs))
                            (f (fn-lgk-frontier ks)) (last (fn-lgk-last ks)))))))
