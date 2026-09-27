; fn: the record log's kernel and its relation to the byte store
; (design 2026-09-27-storage-log section 4, lane w6-log-core).
;
; The kernel state (fn-lgk-):
;   (:lgk COMMITTED LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)
;   COMMITTED  the records the durable segment scans to, in order
;   LAST       the chain head: the trailer of the last committed entry
;   FRONTIER   the unit-aligned offset where the next append goes
;   NEXT-TXID  the allocation counter (a known abort consumes one)
;   BATCH      the records prepared since the last append (pipelined group
;              commit: it accumulates while INFLIGHT's barrier runs)
;   INFLIGHT   the records written at FRONTIER and not yet fenced
;   ACKED      the acknowledged prefix length of COMMITTED (A <= D)
;   PHASE      :ready | :appended | :fenced | :fault
;
; The relation R (fn-lgk-relp) between a byte store BS and a kernel state
; KS over the segment inode INO from GENESIS:
;   1. the durable content C's first FRONTIER octets scan completely to
;      COMMITTED, ending on LAST (the prefix read back, padding included);
;   2. the octets of C from FRONTIER on are zeros (the preallocated extent),
;      FRONTIER is a multiple of the unit, C is a whole number of units;
;   3. the pending operations are exactly the one write of INFLIGHT's log at
;      FRONTIER (none when INFLIGHT is empty), and it fits the extent;
;   4. ACKED <= (len COMMITTED), COMMITTED a true list.
; Established by P-LOG-RECOVER (fn-lgk-recover-establishes-relation: the
; scan, the tail zeroed, one fence), preserved by the append
; (fn-lgk-append-preserves-relation) and the fence
; (fn-lgk-fence-preserves-relation), untouched by prepare, finish and a
; known abort (they change no byte and no field R reads but ACKED), and every
; crash image of a related state scans to COMMITTED ++ a prefix of INFLIGHT
; (fn-lgk-crash-of-related-state-is-a-prefix: T2 lifted).  The served path
; never re-scans: R is carried.

(in-package "ACL2")
(include-book "store-log-crash")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (enable fn-bs-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; The state.

(defun fn-lgk-make (committed last frontier next-txid batch inflight acked phase)
  (declare (xargs :guard t))
  (list :lgk committed last frontier next-txid batch inflight acked phase))

(defun fn-lgk-committed (ks) (declare (xargs :guard (true-listp ks))) (nth 1 ks))
(defun fn-lgk-last (ks) (declare (xargs :guard (true-listp ks))) (nth 2 ks))
(defun fn-lgk-frontier (ks) (declare (xargs :guard (true-listp ks))) (nfix (nth 3 ks)))
(defun fn-lgk-next-txid (ks) (declare (xargs :guard (true-listp ks))) (nfix (nth 4 ks)))
(defun fn-lgk-batch (ks) (declare (xargs :guard (true-listp ks))) (nth 5 ks))
(defun fn-lgk-inflight (ks) (declare (xargs :guard (true-listp ks))) (nth 6 ks))
(defun fn-lgk-acked (ks) (declare (xargs :guard (true-listp ks))) (nfix (nth 7 ks)))
(defun fn-lgk-phase (ks) (declare (xargs :guard (true-listp ks))) (nth 8 ks))

; -----------------------------------------------------------------------------
; The transitions.  Each is total over any state and any record list, so the
; owner lane (w6-log-owner) calls them without a new signature.

; Prepare: the record joins the open batch; its txid is consumed.  A faulted
; kernel admits nothing.
(defun fn-lgk-prepare (ks record)
  (declare (xargs :guard (true-listp ks)))
  (if (equal (fn-lgk-phase ks) :fault)
      ks
    (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
                 (1+ (fn-lgk-next-txid ks))
                 (append (true-list-fix (fn-lgk-batch ks)) (list record))
                 (fn-lgk-inflight ks) (fn-lgk-acked ks) (fn-lgk-phase ks))))

; A known abort consumes the txid for the incarnation and writes nothing.
(defun fn-lgk-known-abort (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
               (1+ (fn-lgk-next-txid ks)) (fn-lgk-batch ks)
               (fn-lgk-inflight ks) (fn-lgk-acked ks) (fn-lgk-phase ks)))

; The append's octets and offset: the batch's chained entries from LAST, at
; FRONTIER.  The host writes exactly these (fnn-log-append); it computes no
; offset, length or digest itself.
(defun fn-lgk-append-octets (ks unit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (fn-lgk-batch ks) (fn-lgk-last ks) unit))

; The batch fits the segment's extent EXTENT (the preallocated length).
(defun fn-lgk-fitsp (ks unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (<= (+ (fn-lgk-frontier ks) (len (fn-lgk-append-octets ks unit))) (nfix extent)))

; Append: the open batch becomes the batch in flight.  Refused (the state
; unchanged) when a batch is already in flight, when the kernel is faulted,
; or when the batch does not fit the extent (rotation or extension first:
; lane w6-log-recovery).
(defun fn-lgk-append (ks unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (consp (fn-lgk-inflight ks)) (equal (fn-lgk-phase ks) :fault)
          (not (fn-lgk-fitsp ks unit extent)))
      ks
    (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
                 (fn-lgk-next-txid ks) nil (true-list-fix (fn-lgk-batch ks))
                 (fn-lgk-acked ks) :appended)))

; The barrier returned :ok: the batch in flight is committed.
(defun fn-lgk-fence (ks unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
    (fn-lgk-make (append (true-list-fix (fn-lgk-committed ks))
                         (true-list-fix (fn-lgk-inflight ks)))
                 (fn-lg-last-trailer (fn-lgk-inflight ks) (fn-lgk-last ks))
                 (+ (fn-lgk-frontier ks) (len w))
                 (fn-lgk-next-txid ks) (fn-lgk-batch ks) nil
                 (fn-lgk-acked ks) :fenced)))

; The barrier failed: every member of the batch in flight is uncertain and
; the kernel is fenced until recovery decides (fsyncgate).
(defun fn-lgk-fence-failed (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
               (fn-lgk-next-txid ks) (fn-lgk-batch ks) (fn-lgk-inflight ks)
               (fn-lgk-acked ks) :fault))

; One member acknowledged, in order: only a committed record.
(defun fn-lgk-finish-one (ks)
  (declare (xargs :guard (true-listp ks)))
  (if (< (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
      (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
                   (fn-lgk-next-txid ks) (fn-lgk-batch ks) (fn-lgk-inflight ks)
                   (1+ (fn-lgk-acked ks)) (fn-lgk-phase ks))
    ks))

; Recovery: the kernel of the scan of the durable content C.  NEXT-TXID is
; the owner's (lane w6-log-owner reads the records' txids); here it is a
; parameter.
(defun fn-lgk-recover (c genesis unit max next-txid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((scan (fn-lg-scan c genesis unit max)))
    (fn-lgk-make (car scan) (fn-lg-scan-last c genesis unit max) (cdr scan)
                 next-txid nil nil (len (car scan)) :ready)))

; -----------------------------------------------------------------------------
; The relation.

; R's conjuncts over the segment's durable content C (1, 2, 4 and the fit).
(defun fn-lgk-content-okp (c ks unit genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((f (fn-lgk-frontier ks))
         (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
    (and (true-listp c)
         (equal (mod (len c) unit) 0)
         (equal (mod f unit) 0)
         (<= f (len c))
         (equal (fn-lg-scan (fn-bs-take f c) genesis unit max)
                (cons (fn-lgk-committed ks) f))
         (equal (fn-lg-scan-last (fn-bs-take f c) genesis unit max) (fn-lgk-last ks))
         (fn-frame-digestp (fn-lgk-last ks))
         (fn-lg-zerosp (nthcdr f c))
         (fn-lg-recordsp (fn-lgk-inflight ks) max)
         (fn-lg-recordsp (fn-lgk-batch ks) max)
         (<= (+ f (len w)) (len c))
         (true-listp (fn-lgk-committed ks))
         (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))))

(defun fn-lgk-relp (bs ks ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit bs)))
    (and (posp unit) ino
         (assoc-equal ino (fn-bs-inodes bs))
         (fn-lgk-content-okp (fn-bs-durable-content bs ino) ks unit genesis max)
         (equal (fn-bs-pending bs)
                (if (consp (fn-lgk-inflight ks))
                    (list (list :write ino (fn-lgk-frontier ks)
                                (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                  nil)))))

; -----------------------------------------------------------------------------
; List and unit arithmetic (local).

(local
 (defthm fn-lgkc-len-nthcdr
   (equal (len (nthcdr k x)) (nfix (- (len x) (nfix k))))
   :hints (("Goal" :induct (nthcdr k x)))))
(local
 (defthm fn-lgkc-take-len
   (equal (len (fn-bs-take n x)) (nfix n))))
(local
 (defthm fn-lgkc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-lgkc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))
(local
 (defthm fn-lgkc-take-of-append-exact
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n (append a b)) a))))
(local
 (defthm fn-lgkc-take-of-append-longer
   (implies (and (true-listp a) (natp n) (<= (len a) n))
            (equal (fn-bs-take n (append a b))
                   (append a (fn-bs-take (- n (len a)) b))))
   :hints (("Goal" :induct (fn-bs-take n a)))))
(local
 (defthm fn-lgkc-take-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (fn-bs-take n (append a b)) (fn-bs-take n a)))))
(local
 (defthm fn-lgkc-nthcdr-of-append-longer
   (implies (and (true-listp a) (natp n) (<= (len a) n))
            (equal (nthcdr n (append a b)) (nthcdr (- n (len a)) b)))
   :hints (("Goal" :induct (nthcdr n a)))))
(local
 (defthm fn-lgkc-take-then-nthcdr
   (implies (and (true-listp x) (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))
   :hints (("Goal" :induct (nthcdr n x)))))
(local
 (defthm fn-lgkc-true-listp-append
   (implies (true-listp b) (true-listp (append a b)))))
(local
 (defthm fn-lgkc-append-nil
   (implies (true-listp x) (equal (append x nil) x))))
(local
 (defthm fn-lgkc-take-of-true-list-all
   (implies (and (true-listp a) (equal n (len a)))
            (equal (fn-bs-take n a) a))))
(local
 (defthm fn-lgkc-scan-records-true-listp
   (true-listp (car (fn-lg-scan octets prev unit max)))
   :hints (("Goal" :induct (fn-lg-scan octets prev unit max)
            :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-slice-record
                                fn-lg-declared-len fn-lg-trailer fn-lg-pad-len)))))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgkc-mod-zero-is-times
     (implies (and (natp f) (posp unit) (equal (mod f unit) 0))
              (equal (* (floor f unit) unit) f)))
   (defthm fn-lgkc-mod-of-times-plus
     (implies (and (natp a) (natp b) (posp unit))
              (equal (mod (+ (* a unit) b) unit) (mod b unit))))
   (defthm fn-lgkc-mod-of-sum-zero
     (implies (and (natp a) (natp b) (posp unit)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (+ a b) unit) 0)))
   (defthm fn-lgkc-floor-natp
     (implies (and (natp f) (posp unit)) (natp (floor f unit)))
     :rule-classes :type-prescription)))

(defthm fn-lg-log-len-aligned
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max) (posp unit))
           (equal (mod (len (fn-lg-log records prev unit)) unit) 0))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (disable fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-recordp
                               fn-lg-entry-units))))

; -----------------------------------------------------------------------------
; The scan's last trailer.

(defthm fn-lg-scan-last-of-log-append
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (equal (fn-lg-scan-last (append (fn-lg-log records prev unit) x) prev unit max)
                  (fn-lg-scan-last x (fn-lg-last-trailer records prev) unit max)))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (disable fn-lg-entry fn-lg-trailer fn-lg-entry-len fn-lg-entry-len-is-units
                               fn-lg-recordp fn-lg-frame fn-lg-pad-len fn-lg-slice
                               fn-lg-entry-okp))
          ("Subgoal *1/1"
           :expand ((fn-lg-scan-last (append (fn-lg-entry prev (car records) unit)
                                             (append (fn-lg-log (cdr records)
                                                                (fn-lg-trailer (fn-lg-frame prev (car records)))
                                                                unit)
                                                     x))
                                     prev unit max))
           :use ((:instance fn-lg-slice-of-entry-append (record (car records))
                            (x (append (fn-lg-log (cdr records)
                                                  (fn-lg-trailer (fn-lg-frame prev (car records)))
                                                  unit)
                                       x)))
                 (:instance fn-lg-entry-okp-of-frame (record (car records)))
                 (:instance fn-lg-entry-len (record (car records)))
                 (:instance fn-lg-nthcdr-of-entry-append (record (car records))
                            (x (append (fn-lg-log (cdr records)
                                                  (fn-lg-trailer (fn-lg-frame prev (car records)))
                                                  unit)
                                       x)))))))

(defthm fn-lg-scan-last-of-zeros
  (implies (fn-lg-zerosp z)
           (equal (fn-lg-scan-last z prev unit max) prev))
  :hints (("Goal" :expand ((fn-lg-scan-last z prev unit max))
           :use fn-lg-scan-of-zeros
           :in-theory (disable fn-lg-scan-of-zeros fn-lg-entry-okp))))

(local
 (defthm fn-lgkc-declared-len-of-append
   (implies (<= *fn-frame-header-octets* (len d))
            (equal (fn-lg-declared-len (append d x)) (fn-lg-declared-len d)))
   :hints (("Goal" :in-theory (e/d (fn-lg-declared-len) (fn-cbor-u32-from))))))
(local
 (defthm fn-lgkc-slice-of-append
   (implies (consp (fn-lg-slice d))
            (equal (fn-lg-slice (append d x)) (fn-lg-slice d)))
   :hints (("Goal" :in-theory (e/d (fn-lg-slice) (fn-lg-declared-len))
            :use ((:instance fn-lg-slice-len (octets d)))))))
(local
 (defthm fn-lgkc-nthcdr-of-append-shorter
   (implies (and (natp n) (<= n (len a)))
            (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))
   :hints (("Goal" :induct (nthcdr n a)))))
(local
 (defthm fn-lgkc-true-list-len-0
   (implies (and (true-listp d) (not (consp d))) (equal d nil))
   :rule-classes :forward-chaining))

(defthm fn-lg-scan-last-of-complete-append
  (implies (and (true-listp d)
                (equal (cdr (fn-lg-scan d prev unit max)) (len d)))
           (equal (fn-lg-scan-last (append d x) prev unit max)
                  (fn-lg-scan-last x (fn-lg-scan-last d prev unit max) unit max)))
  :hints (("Goal" :induct (fn-lg-scan d prev unit max)
           :expand ((fn-lg-scan-last (append d x) prev unit max)
                    (fn-lg-scan d prev unit max)
                    (fn-lg-scan-last d prev unit max))
           :in-theory (disable fn-lg-declared-len fn-lg-entry-okp fn-lg-slice-record
                               fn-lg-trailer fn-lg-pad-len fn-lg-slice)
           :do-not '(generalize))
          ("Subgoal *1/2" :use ((:instance fn-lg-slice-len (octets d))
                                (:instance fn-lg-entry-okp-consp
                                           (slice (fn-lg-slice d)) (prev prev))))))

; -----------------------------------------------------------------------------
; P-BATCH preserves R.

(local
 (defthm fn-lgkc-log-of-atom
   (implies (not (consp records)) (equal (fn-lg-log records prev unit) nil))))

(defthm fn-lg-log-nonempty
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max) (consp records))
           (< 0 (len (fn-lg-log records prev unit))))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-lg-log records prev unit))
           :in-theory (disable fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-recordp
                               fn-lg-entry-len-is-units fn-lg-frame-len)
           :use ((:instance fn-lg-entry-len (record (car records)))
                 (:instance fn-lg-frame-len (record (car records)))))))

(local
 (defthm fn-lgkc-recordsp-nil
   (fn-lg-recordsp nil max)))

(local
 (defthm fn-lgkc-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(defthm fn-lgk-append-preserves-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (not (equal (fn-lgk-phase ks) :fault))
                (fn-lgk-fitsp ks (fn-bs-unit bs) (len (fn-bs-durable-content bs ino))))
           (fn-lgk-relp (mv-nth 1 (fn-bs-write bs ino (fn-lgk-frontier ks)
                                               (fn-lgk-append-octets ks (fn-bs-unit bs)) :ok))
                        (fn-lgk-append ks (fn-bs-unit bs) (len (fn-bs-durable-content bs ino)))
                        ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-durable-content)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp))
           :use ((:instance fn-lg-log-true-listp (records (fn-lgk-batch ks))
                            (prev (fn-lgk-last ks)) (unit (fn-bs-unit bs)))))))

(local
 (defthm fn-lgkc-splice-at-prefix
   (implies (and (true-listp d) (true-listp w) (true-listp z))
            (equal (fn-bs-splice (append d z) (len d) w)
                   (append d (append w (nthcdr (len w) z)))))
   :hints (("Goal" :in-theory (enable fn-bs-splice)
            :use ((:instance fn-lg-splice-past-prefix (s 0) (octets w)))))))

(local
 (defthm fn-lgkc-append-of-len-0
   (implies (equal (len d) 0) (equal (append d z) z))))

; The fence at the content level: C = D ++ Z becomes D ++ W ++ the rest of Z.
(defthm fn-lgk-fence-content
  (implies (and (posp unit) (true-listp d) (true-listp z)
                (equal (len d) (fn-lgk-frontier ks))
                (fn-lgk-content-okp (append d z) ks unit genesis max))
           (let ((w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
             (fn-lgk-content-okp (append d (append w (nthcdr (len w) z)))
                                 (fn-lgk-fence ks unit) unit genesis max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp mod
                               fn-lg-scan-of-complete-append fn-lg-scan-last-of-complete-append
                               fn-lgkc-mod-of-sum-zero)
           :use ((:instance fn-lgkc-mod-of-sum-zero
                            (a (len d))
                            (b (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))))
                 (:instance fn-lg-log-true-listp (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lg-scan-of-complete-append
                            (x (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                            (prev genesis))
                 (:instance fn-lg-scan-last-of-complete-append
                            (x (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                            (prev genesis))
                 (:instance fn-lg-scan-of-log (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lg-scan-last-of-log-append (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)) (x nil))
                 (:instance fn-lg-log-len-aligned (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lg-last-trailer-digestp (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))))))

(defthm fn-lgk-fence-content-when-nothing-in-flight
  (implies (and (fn-lgk-content-okp c ks unit genesis max) (posp unit)
                (not (consp (fn-lgk-inflight ks))))
           (fn-lgk-content-okp c (fn-lgk-fence ks unit) unit genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last mod fn-lg-recordsp))))

(defthm fn-lgk-inflight-of-fence
  (equal (fn-lgk-inflight (fn-lgk-fence ks unit)) nil))

(defthm fn-lgk-content-okp-forward
  (implies (fn-lgk-content-okp c ks unit genesis max)
           (and (true-listp c) (<= (fn-lgk-frontier ks) (len c))
                (<= (+ (fn-lgk-frontier ks)
                       (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                    (len c))))
  :rule-classes :forward-chaining)

(local
 (defthm fn-lgkc-fence-one-write
   (implies (and ino (equal pending (list (list :write ino f w))))
            (equal (cdr (assoc-equal ino (fn-bs-apply-writes
                                          inodes
                                          (fn-bs-ops-for-ino pending ino))))
                   (fn-bs-splice (cdr (assoc-equal ino inodes)) f w)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-bs-splice)))))

(defthm fn-lgk-fence-content-splice
  (implies (and (posp unit) (fn-lgk-content-okp c ks unit genesis max))
           (fn-lgk-content-okp (fn-bs-splice c (fn-lgk-frontier ks)
                                             (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                               (fn-lgk-fence ks unit) unit genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-log fn-lgk-content-okp fn-lgk-fence fn-bs-splice
                               fn-lgkc-take-then-nthcdr fn-lgkc-splice-at-prefix
                               fn-lgk-fence-content fn-lgk-frontier)
           :use ((:instance fn-lgk-content-okp-forward)
                 (:instance fn-lgkc-take-then-nthcdr (n (fn-lgk-frontier ks)) (x c))
                 (:instance fn-lgkc-splice-at-prefix
                            (d (fn-bs-take (fn-lgk-frontier ks) c))
                            (z (nthcdr (fn-lgk-frontier ks) c))
                            (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                 (:instance fn-lg-log-true-listp (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lgk-fence-content
                            (d (fn-bs-take (fn-lgk-frontier ks) c))
                            (z (nthcdr (fn-lgk-frontier ks) c)))))))

(defthm fn-lgk-fence-preserves-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp (mv-nth 1 (fn-bs-fsync-file bs ino :ok))
                        (fn-lgk-fence ks (fn-bs-unit bs))
                        ino genesis max))
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-lgk-inflight ks)))
           :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content)
                           (fn-lg-log fn-lgk-content-okp fn-lgk-fence fn-bs-splice
                            fn-lgk-fence-content-splice fn-lgk-frontier
                            fn-lgk-fence-content-when-nothing-in-flight))
           :use ((:instance fn-lgkc-fence-one-write
                            (pending (fn-bs-pending bs)) (inodes (fn-bs-inodes bs))
                            (f (fn-lgk-frontier ks))
                            (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                 (:instance fn-lgk-fence-content-splice
                            (unit (fn-bs-unit bs))
                            (c (cdr (assoc-equal ino (fn-bs-inodes bs)))))
                 (:instance fn-lgk-fence-content-when-nothing-in-flight
                            (unit (fn-bs-unit bs))
                            (c (cdr (assoc-equal ino (fn-bs-inodes bs)))))))))

; -----------------------------------------------------------------------------
; The transitions that touch no byte preserve R.

(defthm fn-lg-recordsp-of-append
  (implies (and (fn-lg-recordsp a max) (fn-lg-recordsp b max))
           (fn-lg-recordsp (append a b) max)))

(defthm fn-lgk-prepare-preserves-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgk-relp bs (fn-lgk-prepare ks record) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-log mod fn-lg-recordp)
           :use ((:instance fn-lg-recordsp-of-append (a (fn-lgk-batch ks)) (b (list record)))))))

(defthm fn-lgk-finish-one-preserves-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp bs (fn-lgk-finish-one ks) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-log mod fn-lg-recordsp))))

(defthm fn-lgk-known-abort-preserves-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp bs (fn-lgk-known-abort ks) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-log mod fn-lg-recordsp))))

; -----------------------------------------------------------------------------
; T2 lifted: every crash image of a related state scans to COMMITTED
; followed by a prefix of the batch in flight, or the first damaged entry
; forges.  At the cuts with nothing in flight (ready, fenced, finish-k) the
; image scans to exactly COMMITTED.

(defthm fn-lgk-crash-of-related-state-is-a-prefix
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (fn-bs-crash-imagep bs image))
           (let ((content (fn-bs-durable-content image ino))
                 (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
             (or (fn-lg-crash-verdictp (fn-lg-scan content genesis unit max)
                                       (fn-lgk-committed ks) f (fn-lgk-inflight ks)
                                       (fn-lgk-last ks) unit)
                 (fn-lg-forgery-in (nthcdr f content) (fn-lgk-inflight ks)
                                   (fn-lgk-last ks) unit max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-durable-content)
                           (fn-lg-log fn-lgk-content-okp fn-lgk-frontier fn-lg-crash-verdictp
                            fn-lg-forgery-in fn-lg-scan fn-lgkc-take-then-nthcdr
                            fn-lgkc-mod-zero-is-times))
           :use ((:instance fn-lgk-content-okp-forward
                            (c (cdr (assoc-equal ino (fn-bs-inodes bs)))) (unit (fn-bs-unit bs)))
                 (:instance fn-lgkc-take-then-nthcdr
                            (n (fn-lgk-frontier ks)) (x (cdr (assoc-equal ino (fn-bs-inodes bs)))))
                 (:instance fn-lgkc-mod-zero-is-times
                            (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-lg-batch-crash-is-a-prefix
                            (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                            (d (fn-bs-take (fn-lgk-frontier ks) (cdr (assoc-equal ino (fn-bs-inodes bs)))))
                            (z (nthcdr (fn-lgk-frontier ks) (cdr (assoc-equal ino (fn-bs-inodes bs)))))
                            (committed (fn-lgk-committed ks)) (last (fn-lgk-last ks))
                            (batch (fn-lgk-inflight ks)))))
          ("Goal'" :in-theory (e/d (fn-bs-durable-content fn-lgk-content-okp)
                                   (fn-lg-log fn-lgk-frontier fn-lg-crash-verdictp
                                    fn-lg-forgery-in fn-lg-scan fn-lgkc-take-then-nthcdr
                                    fn-lgkc-mod-zero-is-times)))))
