; fn: the record log's recovery (design 2026-09-27-storage-log section 4,
; lanes w6-log-core and w6-log-core-2).
;
; T3 (fn-lg-recovered-frontier-is-the-last-complete-record): the scan of a
; unit-aligned durable content C consumes an aligned prefix F of C, and the
; content cut at F scans to exactly the same records and ends on the same
; trailer (a fixed point).  P-LOG-RECOVER reads that scan, zeroes C from F
; on with one :write and fences it; fn-lgk-recover-establishes-relation says
; the byte store after that fence and the kernel of the scan satisfy R.

(in-package "ACL2")
(include-book "store-log-kernel")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable fn-bs-invariants-vocabulary)))

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (defthm fn-lgkc-s1
     (implies (and (natp n) (posp unit) (natp k) (<= n (* k unit)) (not (equal (mod n unit) 0)))
              (< (floor n unit) k))
     :rule-classes :linear
     :hints (("Goal" :in-theory (enable mod) :nonlinearp t))))
   (local (defthm fn-lgkc-s6
     (implies (and (posp unit) (integerp a) (integerp b) (<= a b))
              (<= (* unit a) (* unit b)))
     :hints (("Goal" :nonlinearp t))))
   (local (defthm fn-lgkc-s8
     (implies (and (natp n) (posp unit))
              (equal (+ n (fn-lg-pad-len n unit))
                     (* unit (if (equal (mod n unit) 0) (floor n unit)
                               (1+ (floor n unit))))))
     :rule-classes nil
     :hints (("Goal" :in-theory (enable fn-lg-pad-len)))))
   (local (defthm fn-lgkc-s9
     (implies (and (natp n) (posp unit) (equal (mod n unit) 0))
              (equal (* unit (floor n unit)) n))
     :rule-classes nil))
   (local (defthm fn-lgkc-s7a
     (implies (and (natp n) (posp unit) (natp k) (<= n (* k unit)) (equal (mod n unit) 0))
              (<= (+ n (fn-lg-pad-len n unit)) (* k unit)))
     :hints (("Goal" :in-theory (enable fn-lg-pad-len)))))
   (local (defthm fn-lgkc-s7b
     (implies (and (natp n) (posp unit) (natp k) (<= n (* k unit)) (not (equal (mod n unit) 0)))
              (<= (+ n (fn-lg-pad-len n unit)) (* k unit)))
     :hints (("Goal" :in-theory (e/d (fn-lgkc-s1) (fn-lgkc-s6 fn-lg-pad-len))
              :use (fn-lgkc-s8 (:instance fn-lgkc-s6 (a (+ 1 (floor n unit))) (b k)))))))
   (local (defthm fn-lgkc-s7
     (implies (and (natp n) (posp unit) (natp k) (<= n (* k unit)))
              (<= (+ n (fn-lg-pad-len n unit)) (* k unit)))
     :hints (("Goal" :in-theory (disable fn-lg-pad-len fn-lgkc-s7a fn-lgkc-s7b)
              :cases ((equal (mod n unit) 0))
              :use (fn-lgkc-s7a fn-lgkc-s7b)))))
   (defthm fn-lgkc-pad-within-aligned
     (implies (and (natp n) (posp unit) (natp l) (<= n l) (equal (mod l unit) 0))
              (<= (+ n (fn-lg-pad-len n unit)) l))
     :rule-classes :linear
     :hints (("Goal" :in-theory (disable fn-lgkc-s7 fn-lg-pad-len)
              :use ((:instance fn-lgkc-s7 (k (floor l unit)))))))
   (local (defthm fn-lgkc-mod-of-times
     (implies (and (integerp k) (posp unit)) (equal (mod (* unit k) unit) 0))))
   (defthm fn-lgkc-pad-is-aligned
     (implies (and (natp n) (posp unit))
              (equal (mod (+ n (fn-lg-pad-len n unit)) unit) 0))
     :hints (("Goal" :do-not-induct t
              :in-theory (union-theories '(fn-lgkc-mod-of-times natp posp (:type-prescription floor))
                                         (theory 'minimal-theory))
              :use (fn-lgkc-s8
                    (:instance fn-lgkc-mod-of-times
                               (k (if (equal (mod n unit) 0) (floor n unit) (1+ (floor n unit)))))))))
   (defthm fn-lgkc-mod-of-zero
     (implies (posp unit) (equal (mod 0 unit) 0)))
   (defthm fn-lgkc-mod-of-sum-zero
     (implies (and (natp a) (natp b) (posp unit)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (+ a b) unit) 0)))
   (defthm fn-lgkc-mod-of-difference-zero
     (implies (and (natp a) (natp b) (<= b a) (posp unit)
                   (equal (mod a unit) 0) (equal (mod b unit) 0))
              (equal (mod (- a b) unit) 0)))))

(local (in-theory (disable fn-lg-declared-len fn-lg-entry-okp fn-lg-slice-records
                           fn-lg-trailer fn-lg-pad-len)))

(defthm fn-lg-scan-consumed-aligned
  (implies (posp unit)
           (equal (mod (cdr (fn-lg-scan x prev unit max)) unit) 0))
  :hints (("Goal" :induct (fn-lg-scan x prev unit max)
           :in-theory (union-theories '(fn-lgkc-mod-of-zero car-cons cdr-cons
                                        (:type-prescription fn-lg-scan-consumed-natp)
                                        (:type-prescription len)
                                        (:type-prescription fn-lg-pad-len-natp) (:induction fn-lg-scan) natp posp)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-lg-scan x prev unit max))
           :use ((:instance fn-lgkc-pad-is-aligned (n (len (fn-lg-slice x))))
                 (:instance fn-lgkc-mod-of-sum-zero
                            (a (+ (len (fn-lg-slice x))
                                  (fn-lg-pad-len (len (fn-lg-slice x)) unit)))
                            (b (cdr (fn-lg-scan (nthcdr (+ (len (fn-lg-slice x))
                                                           (fn-lg-pad-len (len (fn-lg-slice x)) unit))
                                                        x)
                                                (fn-lg-trailer (fn-lg-slice x))
                                                unit max))))))
          ("Subgoal *1/1" :expand ((fn-lg-scan x prev unit max)))))

(local
 (defthm fn-lgkc-len-nthcdr
   (implies (and (natp n) (<= n (len x)))
            (equal (len (nthcdr n x)) (- (len x) n)))))

(local
 (defthm fn-lgkc-step-within
   (implies (and (posp unit) (fn-lg-entry-okp (fn-lg-slice x) prev max)
                 (equal (mod (len x) unit) 0))
            (let ((step (+ (len (fn-lg-slice x)) (fn-lg-pad-len (len (fn-lg-slice x)) unit))))
              (and (<= step (len x))
                   (equal (mod (- (len x) step) unit) 0))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '((:type-prescription len)
                                         (:type-prescription fn-lg-pad-len-natp) natp posp)
                                       (theory 'minimal-theory))
            :use ((:instance fn-lg-entry-okp-consp (slice (fn-lg-slice x)))
                  (:instance fn-lg-slice-len (octets x))
                  (:instance fn-lgkc-pad-within-aligned (n (len (fn-lg-slice x))) (l (len x)))
                  (:instance fn-lgkc-pad-is-aligned (n (len (fn-lg-slice x))))
                  (:instance fn-lgkc-mod-of-difference-zero
                             (a (len x))
                             (b (+ (len (fn-lg-slice x)) (fn-lg-pad-len (len (fn-lg-slice x)) unit)))))))))

(defthm fn-lg-scan-consumed-within
  (implies (and (posp unit) (equal (mod (len x) unit) 0))
           (<= (cdr (fn-lg-scan x prev unit max)) (len x)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-lg-scan x prev unit max)
           :in-theory (union-theories '(car-cons cdr-cons
                                        (:type-prescription fn-lg-scan-consumed-natp)
                                        (:type-prescription len)
                                        (:type-prescription fn-lg-pad-len-natp)
                                        (:induction fn-lg-scan) natp posp)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-lg-scan x prev unit max))
           :use ((:instance fn-lgkc-step-within)
                 (:instance fn-lgkc-len-nthcdr
                            (n (+ (len (fn-lg-slice x)) (fn-lg-pad-len (len (fn-lg-slice x)) unit))))))
          ("Subgoal *1/1" :expand ((fn-lg-scan x prev unit max)))))

(local
 (defun fn-lgkc-take2-ind (m n x)
   (if (zp m) (list n x) (fn-lgkc-take2-ind (1- m) (1- n) (cdr x)))))
(local
 (defun fn-lgkc-drop-ind (k n x)
   (if (zp k) (list n x) (fn-lgkc-drop-ind (1- k) (1- n) (cdr x)))))
(local
 (defthm fn-lgkc-take-of-take
   (implies (and (natp m) (natp n) (<= m n))
            (equal (fn-bs-take m (fn-bs-take n x)) (fn-bs-take m x)))
   :hints (("Goal" :induct (fn-lgkc-take2-ind m n x)))))
(local
 (defthm fn-lgkc-take-of-nthcdr-of-take
   (implies (and (natp k) (natp m) (natp n) (<= (+ k m) n))
            (equal (fn-bs-take m (nthcdr k (fn-bs-take n x)))
                   (fn-bs-take m (nthcdr k x))))
   :hints (("Goal" :induct (fn-lgkc-drop-ind k n x)))))
(local
 (defthm fn-lgkc-nthcdr-of-take
   (implies (and (natp k) (natp n) (<= k n))
            (equal (nthcdr k (fn-bs-take n x)) (fn-bs-take (- n k) (nthcdr k x))))
   :hints (("Goal" :induct (fn-lgkc-drop-ind k n x)))))

(local
 (defthm fn-lgkc-declared-len-of-take
   (implies (and (natp n) (<= *fn-frame-header-octets* n) (<= n (len x)))
            (equal (fn-lg-declared-len (fn-bs-take n x)) (fn-lg-declared-len x)))
   :hints (("Goal" :in-theory (e/d (fn-lg-declared-len)
                                   (fn-cbor-u32-from fn-cbor-octet-listp fn-bs-take))))))

(local
 (defthm fn-lgkc-declared-len-of-short-take
   (implies (and (natp n) (< n *fn-frame-header-octets*))
            (not (fn-lg-declared-len (fn-bs-take n x))))
   :hints (("Goal" :in-theory (enable fn-lg-declared-len)))))

; A slice of a prefix is no slice, or the slice.
(defthm fn-lg-slice-of-take
  (implies (and (natp n) (<= n (len x)) (consp (fn-lg-slice (fn-bs-take n x))))
           (equal (fn-lg-slice (fn-bs-take n x)) (fn-lg-slice x)))
  :hints (("Goal" :in-theory (enable fn-lg-slice)
           :cases ((<= *fn-frame-header-octets* n)))))

(defthm fn-lg-slice-of-take-when-within
  (implies (and (natp n) (<= n (len x)) (consp (fn-lg-slice x))
                (<= (len (fn-lg-slice x)) n))
           (equal (fn-lg-slice (fn-bs-take n x)) (fn-lg-slice x)))
  :hints (("Goal" :in-theory (enable fn-lg-slice)
           :use ((:instance fn-lg-slice-len (octets x))))))

(defun fn-lgkc-take-ind (x n prev unit max)
  (declare (xargs :measure (len x)
                  :hints (("Goal" :use ((:instance fn-lg-slice-len (octets x))
                                        (:instance fn-lg-entry-okp-consp
                                                   (slice (fn-lg-slice x))))
                           :in-theory (disable fn-lg-slice fn-lg-slice-len fn-lg-entry-okp-consp)))))
  (let ((slice (fn-lg-slice x)))
    (if (not (fn-lg-entry-okp slice prev max))
        (list x n)
      (let ((step (+ (len slice) (fn-lg-pad-len (len slice) unit))))
        (fn-lgkc-take-ind (nthcdr step x) (- n step) (fn-lg-trailer slice) unit max)))))

(defthm fn-lg-scan-of-take-consumed
  (implies (and (natp n) (<= (cdr (fn-lg-scan x prev unit max)) n) (<= n (len x)))
           (and (equal (fn-lg-scan (fn-bs-take n x) prev unit max) (fn-lg-scan x prev unit max))
                (equal (fn-lg-scan-last (fn-bs-take n x) prev unit max)
                       (fn-lg-scan-last x prev unit max))))
  :hints (("Goal" :induct (fn-lgkc-take-ind x n prev unit max)
           :expand ((fn-lg-scan (fn-bs-take n x) prev unit max)
                    (fn-lg-scan x prev unit max)
                    (fn-lg-scan-last (fn-bs-take n x) prev unit max)
                    (fn-lg-scan-last x prev unit max))
           :in-theory (disable fn-lg-slice))
          ("Subgoal *1/2" :use ((:instance fn-lg-slice-len (octets x))
                                (:instance fn-lg-entry-okp-consp (slice (fn-lg-slice x)))
                                (:instance fn-lg-slice-of-take-when-within)))
          ("Subgoal *1/1" :use ((:instance fn-lg-slice-of-take)))))

(defthm fn-lg-recovered-frontier-is-the-last-complete-record
  (implies (and (posp unit) (true-listp c) (equal (mod (len c) unit) 0))
           (let* ((scan (fn-lg-scan c genesis unit max)) (f (cdr scan)))
             (and (<= f (len c))
                  (equal (mod f unit) 0)
                  (equal (fn-lg-scan (fn-bs-take f c) genesis unit max) scan)
                  (equal (fn-lg-scan-last (fn-bs-take f c) genesis unit max)
                         (fn-lg-scan-last c genesis unit max)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-scan-of-take-consumed)
           :use ((:instance fn-lg-scan-consumed-within (x c) (prev genesis))
                 (:instance fn-lg-scan-consumed-aligned (x c) (prev genesis))
                 (:instance fn-lg-scan-of-take-consumed (x c) (prev genesis)
                            (n (cdr (fn-lg-scan c genesis unit max))))))))


; -----------------------------------------------------------------------------
; The scan ends on a digest: every trailer it steps to is an opened frame's.

(local
 (defthm fn-lgkc-decode-ok-octets
   (implies (fn-frame-result-okp (fn-frame-decode octets digest max))
            (fn-cbor-octet-listp octets))
   :rule-classes nil
   :hints (("Goal" :expand ((fn-frame-decode octets digest max)) :in-theory (disable fn-cbor-u32-from fn-frame-head-fields fn-frame-split
                                       fn-cbor-at-mostp fn-frame-digestp fn-cbor-octet-listp)))))

(local
 (defthm fn-lgkc-trailer-of-okp-slice-is-a-digest
   (implies (fn-lg-entry-okp (fn-lg-slice x) prev max)
            (fn-frame-digestp (fn-lg-trailer (fn-lg-slice x))))
   :hints (("Goal" :in-theory (e/d (fn-lg-trailer fn-lg-entry-okp fn-frame-open fn-frame-digestp)
                                   (fn-frame-decode fn-lg-slice fn-lg-declared-len
                                    fn-lg-open-bound fn-lg-unpack-okp))
            :use ((:instance fn-lg-slice-len (octets x))
                  (:instance fn-lgkc-decode-ok-octets (octets (fn-lg-slice x))
                             (max (fn-lg-open-bound (fn-lg-slice x) max))
                             (digest (fn-frame-digest (fn-frame-protected-prefix (fn-lg-slice x))))))))))

(defthm fn-lg-scan-last-digestp
  (implies (fn-frame-digestp prev)
           (fn-frame-digestp (fn-lg-scan-last x prev unit max)))
  :hints (("Goal" :induct (fn-lg-scan-last x prev unit max)
           :in-theory (disable fn-lg-slice fn-lg-entry-okp fn-lg-trailer fn-frame-digestp
                               fn-lg-pad-len))))

; -----------------------------------------------------------------------------
; The owner's obligation: while the log recovers, no store operation other
; than the log's own writes is pending.  Lane w6-log-owner makes the log the
; only pending store write and discharges this by functional instantiation
; with its own predicate (its state's pending list names only the segment);
; the constraint is all this book uses.  It is not a platform assumption and
; is not in books/assumptions.lisp: fn proves it, of its own owner.

(encapsulate
  (((fn-assume-log-sole-pending-writer * *) => *))
  (local (defun fn-assume-log-sole-pending-writer (bs ino)
           (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino))))
  (defthm fn-assume-log-sole-pending-writer-names-only-the-log
    (implies (fn-assume-log-sole-pending-writer bs ino)
             (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino)))))

(local
 (defthm fn-lgkc-ops-all-for-ino
   (implies (and (true-listp ops) (not (fn-bs-ops-not-for-ino ops ino)))
            (equal (fn-bs-ops-for-ino ops ino) ops))))

(local
 (defthm fn-lgkc-nthcdr-len
   (implies (true-listp c) (equal (nthcdr (len c) c) nil))))

(local
 (defthm fn-lgkc-zerosp-of-append
   (implies (and (fn-lg-zerosp a) (fn-lg-zerosp b)) (fn-lg-zerosp (append a b)))))

; -----------------------------------------------------------------------------
; R established.  P-LOG-RECOVER: the scan of the durable content C gives the
; kernel (fn-lgk-recover); the tail [F, len C) is zeroed by one :write (a
; no-op when F = len C) and fenced by one fsync.  The byte store after that
; fence and the recovered kernel satisfy R.

(defthm fn-lgk-fields-of-recover
  (let ((ks (fn-lgk-recover c genesis unit max next-txid)))
    (and (equal (fn-lgk-committed ks) (car (fn-lg-scan c genesis unit max)))
         (equal (fn-lgk-last ks) (fn-lg-scan-last c genesis unit max))
         (equal (fn-lgk-frontier ks) (cdr (fn-lg-scan c genesis unit max)))
         (equal (fn-lgk-inflight ks) nil)
         (equal (fn-lgk-batch ks) nil)
         (equal (fn-lgk-phase ks) :ready)))
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last))))

(defthm fn-lgk-recovered-content-okp
  (implies (and (posp unit) (true-listp c) (equal (mod (len c) unit) 0)
                (fn-frame-digestp genesis))
           (let* ((ks (fn-lgk-recover c genesis unit max next-txid))
                  (f (fn-lgk-frontier ks)))
             (fn-lgk-content-okp (fn-bs-splice c f (fn-bs-zeros (- (len c) f)))
                                 ks unit genesis max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-splice)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp))
           :expand ((fn-lg-recordsp nil max) (fn-lg-log nil (fn-lg-scan-last c genesis unit max) unit))
           :use ((:instance fn-lg-recovered-frontier-is-the-last-complete-record)
                 (:instance fn-lgc-scan-records-true-listp (octets c) (prev genesis))))))

(local
 (defthm fn-lgkc-ops-for-ino-of-append
   (equal (fn-bs-ops-for-ino (append a b) ino)
          (append (fn-bs-ops-for-ino a ino) (fn-bs-ops-for-ino b ino)))))

(local
 (defthm fn-lgkc-ops-not-for-ino-of-append
   (equal (fn-bs-ops-not-for-ino (append a b) ino)
          (append (fn-bs-ops-not-for-ino a ino) (fn-bs-ops-not-for-ino b ino)))))

(local
 (defthm fn-lgkc-take-len-self
   (implies (true-listp c) (equal (fn-bs-take (len c) c) c))))

(local
 (defthm fn-lgkc-splice-nothing-at-end
   (implies (true-listp c) (equal (fn-bs-splice c (len c) nil) c))
   :hints (("Goal" :in-theory (disable fn-bs-take)))))

(defthm fn-lgk-recover-establishes-relation
  (let* ((unit (fn-bs-unit bs)) (c (fn-bs-durable-content bs ino))
         (ks (fn-lgk-recover c genesis unit max next-txid))
         (f (fn-lgk-frontier ks))
         (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok)))
         (bs2 (mv-nth 1 (fn-bs-fsync-file bs1 ino :ok))))
    (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp c) (equal (mod (len c) unit) 0)
                  (fn-frame-digestp genesis)
                  (fn-assume-log-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
             (fn-lgk-relp bs2 ks ino genesis max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp fn-lgk-content-okp fn-lgk-recover fn-bs-splice
                            fn-lgk-recovered-content-okp fn-bs-zeros fn-lgk-frontier fn-lgk-inflight))
           :use ((:instance fn-lgk-recovered-content-okp
                            (unit (fn-bs-unit bs)) (c (fn-bs-durable-content bs ino)))
                 (:instance fn-assume-log-sole-pending-writer-names-only-the-log)))))
