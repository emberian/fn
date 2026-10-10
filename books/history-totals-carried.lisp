; fn: the charged totals the owner carries (K-TOTALS; Builder M, memory
; landing 3+4, 2026-10-09).
;
; The owner admits an article by the memory equation at the launch's limit
; (books/memory-model.lisp fn-mm-gate-p) over the store's charged totals
; (books/charged-totals.lisp) plus the article's.  It carries those totals
; the way it carries the record octets (books/history-columns-store.lisp
; fn-hist-bytes-carried): a (K . TOT) cache of the first K records' totals,
; advanced over the records committed since through the history stobj, one
; row each (fn-hist-at), never a walk of the history.
;
; Per record (fn-ct-row-tot):
;   RECORDS 1; ARENA HCHARGE MEMBERSHIPS EVENTS CHARGE exactly fn-ct-row's;
;   HISTORY exactly the history image's padded row length of the record
;     (fn-hp-x-rowlen's third value: the image's events are the store's
;     records, books/history-pages-owner.lisp);
;   LOG the record's log share at its ceiling: one frame of its own (the
;     batch's four-octet length, the frame header, the 32-octet chain and the
;     trailer, *fn-ct-log-frame-octets*) around its encoding, an article's at
;     fn-record-encoded-octets-ceiling of its payload and groups
;     (books/records-shape.lisp; fn-record-encode-narrow-length-bound).
;     The unit's padding and a segment's rotation entry are not records'
;     octets: LOG is "the octets of the log's records a full replay reads"
;     (books/charged-totals.lisp).  O-LOG, checked by the census: the
;     replayed records' octets are within the carried LOG.
;
; KEYSTONES (K-TOTALS)
;   fn-hist-totals-carried-is-totals-extend   under R the carried totals are
;                                             the extend specification
;   fn-ct-totals-extend-of-a-valid-cache      a valid cache extends to the
;                                             fold over every record
;   fn-ct-charged-covers-the-store            the fold is at least the
;                                             store's totals (fn-mm-tot-le)
;                                             when the log's records are
;                                             within their charges (O-LOG)

(in-package "ACL2")
(include-book "history-columns-store")
(include-book "charged-totals")

(local (in-theory (disable (tau-system))))

(defun fn-ct-row-log (row)
  (declare (xargs :guard t :verify-guards nil))
  (+ *fn-ct-log-frame-octets*
     (cond ((fn-held-p row)
            (fn-record-encoded-octets-ceiling (nfix (fn-hf-octets (fn-held-facts row)))
                                              (len (fn-record-groups row))))
           ((fn-hstxa-p row) (len (fn-store-event-encode (fn-hstxa-stxa row))))
           (t (len (fn-store-event-encode row))))))

(defun fn-ct-row-history (row)
  (declare (xargs :guard t))
  (mv-let (err tl plen) (fn-hp-x-rowlen row)
    (declare (ignore err tl))
    (nfix plen)))

; One record's charged totals.
(defun fn-ct-row-tot (row residency)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-ct-row row)))
    (fn-mm-make-tot 1 (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)
                    (fn-ct-row-log row) (fn-ct-row-history row) (nth 4 r)
                    residency)))

(defun fn-ct-zero-tot (residency)
  (declare (xargs :guard t))
  (fn-mm-make-tot 0 0 0 0 0 0 0 0 residency))

; The fold: the charged totals of RECORDS at RESIDENCY.
(defun fn-ct-charged (records residency)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (fn-mm-tot-plus (fn-ct-row-tot (car records) residency)
                      (fn-ct-charged (cdr records) residency))
    (fn-ct-zero-tot residency)))

; A cache (K . TOT) is valid for RECORDS when TOT is the fold over the first K.
(defun fn-ct-totals-cache-validp (cache records residency)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp cache) (natp (car cache)) (<= (car cache) (len records))
       (equal (cdr cache) (fn-ct-charged (take (car cache) records) residency))))

; The extend specification: the cached totals plus the records past K; the
; whole fold when CACHE is not a (K . TOT) pair within RECORDS.
(defun fn-ct-totals-extend (cache records residency)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp cache) (natp (car cache)) (fn-mm-tot-p (cdr cache))
           (<= (car cache) (len records)))
      (fn-mm-tot-plus (cdr cache) (fn-ct-charged (nthcdr (car cache) records) residency))
    (fn-ct-charged records residency)))

; The carried reader, from the history stobj: one row per record past K.
(defun fn-hist-totals-advance (k count tot residency fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp k) (natp count) (<= count (fn-hist-count fn-hist)))
                  :measure (nfix (- (nfix count) (nfix k)))
                  :verify-guards nil))
  (if (and (natp k) (natp count) (< k count))
      (fn-hist-totals-advance (1+ k) count
                              (fn-mm-tot-plus tot (fn-ct-row-tot (fn-hist-at k fn-hist) residency))
                              residency fn-hist)
    tot))

(defun fn-hist-totals-carried (cache s residency fn-hist)
  (declare (xargs :stobjs fn-hist :guard t :verify-guards nil))
  (let ((count (fn-hist-count fn-hist)))
    (if (and (consp cache) (natp (car cache)) (fn-mm-tot-p (cdr cache))
             (<= (car cache) count))
        (fn-hist-totals-advance (car cache) count (cdr cache) residency fn-hist)
      (fn-ct-charged (fn-sf-records (fn-sn-files s)) residency))))

; KEYSTONE K-TOTALS (1): under R, the carried totals are the extend spec.
(local
 (defthm kt-nfix-nfix (equal (nfix (nfix a)) (nfix a))))

(local
 (defthm kt-records-of-make
   (equal (fn-mm-tot-records (fn-mm-make-tot a b c d e f g h r)) (nfix a))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-records fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-arena-of-make
   (equal (fn-mm-tot-arena (fn-mm-make-tot a b c d e f g h r)) (nfix b))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-arena fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-hcharge-of-make
   (equal (fn-mm-tot-hcharge (fn-mm-make-tot a b c d e f g h r)) (nfix c))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-hcharge fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-memberships-of-make
   (equal (fn-mm-tot-memberships (fn-mm-make-tot a b c d e f g h r)) (nfix d))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-memberships fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-events-of-make
   (equal (fn-mm-tot-events (fn-mm-make-tot a b c d e f g h r)) (nfix e))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-events fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-log-of-make
   (equal (fn-mm-tot-log (fn-mm-make-tot a b c d e f g h r)) (nfix f))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-log fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-history-of-make
   (equal (fn-mm-tot-history (fn-mm-make-tot a b c d e f g h r)) (nfix g))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-history fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-charge-of-make
   (equal (fn-mm-tot-charge (fn-mm-make-tot a b c d e f g h r)) (nfix h))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-charge fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm kt-paged-of-make
   (equal (fn-mm-tot-paged-p (fn-mm-make-tot a b c d e f g h r)) (equal r :paged))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-paged-p fn-mm-make-tot) (nfix))))))

(local
 (in-theory (disable fn-mm-make-tot fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge fn-mm-tot-paged-p)))

(local
 (defthm kt-plus-assoc
   (equal (fn-mm-tot-plus (fn-mm-tot-plus a b) c) (fn-mm-tot-plus a (fn-mm-tot-plus b c)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))

(local
 (in-theory (disable fn-mm-tot-p)))

(local
 (defthm kt-tot-p-of-plus (fn-mm-tot-p (fn-mm-tot-plus a b))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))

(local
 (defthm kt-tot-p-of-zero (fn-mm-tot-p (fn-ct-zero-tot r))
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm kt-tot-p-of-row-tot (fn-mm-tot-p (fn-ct-row-tot row res))
   :hints (("Goal" :in-theory (e/d (fn-ct-row-tot) (fn-ct-row fn-ct-row-log fn-ct-row-history))))))

(local
 (defthm kt-tot-p-of-charged (fn-mm-tot-p (fn-ct-charged rs res))
   :hints (("Goal" :induct (fn-ct-charged rs res)
            :in-theory (disable fn-ct-row-tot fn-mm-tot-plus fn-ct-zero-tot)))))

(local
 (defthm kt-take-len (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm kt-take9
   (equal (take 9 x) (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                           (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth)
            :expand ((take 9 x) (take 8 (cdr x)) (take 7 (cddr x)) (take 6 (cdddr x))
                     (take 5 (cddddr x)) (take 4 (cdr (cddddr x))) (take 3 (cddr (cddddr x)))
                     (take 2 (cdddr (cddddr x))) (take 1 (cddddr (cddddr x))) (take 0 (cdr (cddddr (cddddr x)))))))))

(local
 (defthm kt-shape9
   (implies (and (true-listp x) (equal (len x) 9))
            (equal x (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                           (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance kt-take-len) (:instance kt-take9))
            :in-theory (disable kt-take-len)))))

(local
 (defthm kt-tot-shape
   (implies (fn-mm-tot-p tot)
            (equal tot (list (nth 0 tot) (nth 1 tot) (nth 2 tot) (nth 3 tot) (nth 4 tot)
                             (nth 5 tot) (nth 6 tot) (nth 7 tot) (nth 8 tot))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance kt-shape9 (x tot)))
            :in-theory (enable fn-mm-tot-p)))))

(local
 (defthm kt-plus-zero-list
   (implies (and (natp a) (natp b) (natp c) (natp d) (natp e) (natp f) (natp g) (natp h)
                 (member-equal r '(:resident :paged)))
            (equal (fn-mm-tot-plus (list a b c d e f g h r) (fn-ct-zero-tot res))
                   (list a b c d e f g h r)))
   :hints (("Goal"
            :in-theory (e/d (fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot
                             fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                             fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                             fn-mm-tot-paged-p fn-mm-nat)
                            ())))))

(local
 (defthm kt-plus-zero
   (implies (fn-mm-tot-p tot)
            (equal (fn-mm-tot-plus tot (fn-ct-zero-tot res)) tot))
   :hints (("Goal" :use (kt-tot-shape
                         (:instance kt-plus-zero-list (a (nth 0 tot)) (b (nth 1 tot)) (c (nth 2 tot))
                                    (d (nth 3 tot)) (e (nth 4 tot)) (f (nth 5 tot)) (g (nth 6 tot))
                                    (h (nth 7 tot)) (r (nth 8 tot))))
            :in-theory (e/d (fn-mm-tot-p) (kt-plus-zero-list))))))

(local
 (in-theory (disable fn-ct-row-tot fn-ct-row fn-ct-row-log fn-ct-row-history fn-ct-zero-tot fn-mm-tot-plus)))

(local
 (defthm kt-nthcdr-unroll
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :rule-classes nil))

(local
 (defthm kt-nthcdr-past-len
   (implies (and (natp k) (<= (len x) k)) (not (consp (nthcdr k x))))))

(local
 (defthm kt-charged-of-atom
   (implies (not (consp rs)) (equal (fn-ct-charged rs res) (fn-ct-zero-tot res)))))

(local
 (defthm kt-charged-of-cons
   (equal (fn-ct-charged (cons r rs) res)
          (fn-mm-tot-plus (fn-ct-row-tot r res) (fn-ct-charged rs res)))
   :hints (("Goal" :in-theory (enable fn-ct-charged)))))

(local
 (in-theory (disable fn-ct-charged)))

(local
 (defthm kt-charged-nthcdr-step
   (implies (and (natp k) (< k (len records)))
            (equal (fn-ct-charged (nthcdr k records) res)
                   (fn-mm-tot-plus (fn-ct-row-tot (nth k records) res)
                                   (fn-ct-charged (nthcdr (1+ k) records) res))))
   :hints (("Goal" :use (:instance kt-nthcdr-unroll (xs records))
            :in-theory (disable nth nthcdr len)))))

(local
 (defthm kt-advance-is-suffix
   (implies (and (natp k) (<= k (len h)) (fn-mm-tot-p tot))
            (equal (fn-hist-totals-advance k (len h) tot res h)
                   (fn-mm-tot-plus tot (fn-ct-charged (nthcdr k h) res))))
   :hints (("Goal" :induct (fn-hist-totals-advance k (len h) tot res h)
            :in-theory (disable fn-mm-tot-plus fn-ct-row-tot nthcdr nth)))))

(defthm fn-hist-totals-carried-is-totals-extend
  (implies (equal fn-hist (fn-sf-records (fn-sn-files s)))
           (equal (fn-hist-totals-carried cache s residency fn-hist)
                  (fn-ct-totals-extend cache (fn-sf-records (fn-sn-files s)) residency)))
  :hints (("Goal" :in-theory (e/d (fn-ct-totals-extend fn-hist-totals-carried)
                                  (fn-hist-totals-advance fn-ct-charged)))))

; KEYSTONE K-TOTALS (2): a valid cache extends to the whole fold.
(local
 (defthm kt-paged-of-charged
   (equal (fn-mm-tot-paged-p (fn-ct-charged rs res)) (equal res :paged))
   :hints (("Goal" :induct (fn-ct-charged rs res)
            :in-theory (e/d (fn-mm-tot-plus fn-ct-row-tot fn-ct-zero-tot kt-charged-of-cons kt-charged-of-atom (:induction fn-ct-charged)) ())))))

(local
 (defthm kt-plus-zero-left-list
   (implies (and (natp a) (natp b) (natp c) (natp d) (natp e) (natp f) (natp g) (natp h)
                 (member-equal r '(:resident :paged))
                 (equal (equal r :paged) (equal res :paged)))
            (equal (fn-mm-tot-plus (fn-ct-zero-tot res) (list a b c d e f g h r))
                   (list a b c d e f g h r)))
   :hints (("Goal"
            :in-theory (e/d (fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot
                             fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                             fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                             fn-mm-tot-paged-p fn-mm-nat)
                            ())))))

(local
 (defthm kt-plus-zero-left
   (implies (and (fn-mm-tot-p tot) (equal (fn-mm-tot-paged-p tot) (equal res :paged)))
            (equal (fn-mm-tot-plus (fn-ct-zero-tot res) tot) tot))
   :hints (("Goal" :use (kt-tot-shape
                         (:instance kt-plus-zero-left-list (a (nth 0 tot)) (b (nth 1 tot)) (c (nth 2 tot))
                                    (d (nth 3 tot)) (e (nth 4 tot)) (f (nth 5 tot)) (g (nth 6 tot))
                                    (h (nth 7 tot)) (r (nth 8 tot))))
            :in-theory (e/d (fn-mm-tot-p fn-mm-tot-paged-p) (kt-plus-zero-left-list))))))

(local
 (defthm kt-charged-open
   (implies (consp r)
            (equal (fn-ct-charged r res)
                   (fn-mm-tot-plus (fn-ct-row-tot (car r) res) (fn-ct-charged (cdr r) res))))
   :hints (("Goal" :in-theory (enable fn-ct-charged)))))

(local
 (defun kt-split-ind (k r)
   (declare (xargs :measure (nfix k)))
   (if (or (zp k) (atom r)) (list k r) (kt-split-ind (1- k) (cdr r)))))

(local
 (defthm kt-charged-split
   (implies (and (natp k) (<= k (len r)))
            (equal (fn-ct-charged r res)
                   (fn-mm-tot-plus (fn-ct-charged (take k r) res)
                                   (fn-ct-charged (nthcdr k r) res))))
   :hints (("Goal" :induct (kt-split-ind k r)
            :in-theory (e/d (take nthcdr) (fn-mm-tot-plus fn-ct-row-tot fn-ct-zero-tot))))
   :rule-classes nil))

(local
 (defthm kt-take-append
   (implies (and (natp k) (<= k (len r)))
            (equal (take k (append r m)) (take k r)))
   :hints (("Goal" :induct (kt-split-ind k r) :in-theory (e/d (take) ())))))

(defthm fn-ct-totals-extend-of-a-valid-cache
  (implies (fn-ct-totals-cache-validp cache records residency)
           (equal (fn-ct-totals-extend cache records residency)
                  (fn-ct-charged records residency)))
  :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp fn-ct-totals-extend) (fn-ct-charged))
           :use ((:instance kt-charged-split (k (car cache)) (r records) (res residency))))))

; The owner keeps the cache valid while the records only grow.
(defthm fn-ct-totals-cache-valid-after-commit
  (implies (fn-ct-totals-cache-validp cache records residency)
           (fn-ct-totals-cache-validp cache (append records more) residency))
  :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp) (fn-ct-charged take)))))

(defthm fn-ct-totals-empty-cache-is-valid
  (fn-ct-totals-cache-validp (cons 0 (fn-ct-zero-tot residency)) records residency)
  :hints (("Goal" :in-theory (e/d (fn-ct-totals-cache-validp) ()))))

; The log's records' octets a full replay reads, charged.
(defun fn-ct-log-of-records (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (+ (fn-ct-row-log (car records)) (fn-ct-log-of-records (cdr records)))
    0))

(local
 (defthm kt-nfix-natp (implies (natp x) (equal (nfix x) x))))

(local
 (defthm kt-row-log-natp (natp (fn-ct-row-log row))
   :hints (("Goal" :in-theory (e/d (fn-ct-row-log fn-record-encoded-octets-ceiling)
                                   (fn-store-event-encode fn-held-p fn-hstxa-p fn-hf-octets fn-held-facts fn-record-groups nfix))))
   :rule-classes :type-prescription))

(local
 (defthm kt-fields-of-row-tot
   (and (equal (fn-mm-tot-records (fn-ct-row-tot row res)) 1)
        (equal (fn-mm-tot-arena (fn-ct-row-tot row res)) (nfix (nth 0 (fn-ct-row row))))
        (equal (fn-mm-tot-hcharge (fn-ct-row-tot row res)) (nfix (nth 1 (fn-ct-row row))))
        (equal (fn-mm-tot-memberships (fn-ct-row-tot row res)) (nfix (nth 2 (fn-ct-row row))))
        (equal (fn-mm-tot-events (fn-ct-row-tot row res)) (nfix (nth 3 (fn-ct-row row))))
        (equal (fn-mm-tot-log (fn-ct-row-tot row res)) (nfix (fn-ct-row-log row)))
        (equal (fn-mm-tot-history (fn-ct-row-tot row res)) (nfix (fn-ct-row-history row)))
        (equal (fn-mm-tot-charge (fn-ct-row-tot row res)) (nfix (nth 4 (fn-ct-row row))))
        (equal (fn-mm-tot-paged-p (fn-ct-row-tot row res)) (equal res :paged)))
   :hints (("Goal" :in-theory (e/d (fn-ct-row-tot) (nfix fn-ct-row fn-ct-row-log fn-ct-row-history))))))

(local
 (defthm kt-natp-accessors
   (and (natp (fn-mm-tot-records a)) (natp (fn-mm-tot-arena a)) (natp (fn-mm-tot-hcharge a))
        (natp (fn-mm-tot-memberships a)) (natp (fn-mm-tot-events a)) (natp (fn-mm-tot-log a))
        (natp (fn-mm-tot-history a)) (natp (fn-mm-tot-charge a)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                                      fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log
                                      fn-mm-tot-history fn-mm-tot-charge fn-mm-nat)))))

(local
 (defthm kt-fields-of-plus
   (and (equal (fn-mm-tot-records (fn-mm-tot-plus a b)) (+ (fn-mm-tot-records a) (fn-mm-tot-records b)))
        (equal (fn-mm-tot-arena (fn-mm-tot-plus a b)) (+ (fn-mm-tot-arena a) (fn-mm-tot-arena b)))
        (equal (fn-mm-tot-hcharge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b)))
        (equal (fn-mm-tot-memberships (fn-mm-tot-plus a b)) (+ (fn-mm-tot-memberships a) (fn-mm-tot-memberships b)))
        (equal (fn-mm-tot-events (fn-mm-tot-plus a b)) (+ (fn-mm-tot-events a) (fn-mm-tot-events b)))
        (equal (fn-mm-tot-log (fn-mm-tot-plus a b)) (+ (fn-mm-tot-log a) (fn-mm-tot-log b)))
        (equal (fn-mm-tot-history (fn-mm-tot-plus a b)) (+ (fn-mm-tot-history a) (fn-mm-tot-history b)))
        (equal (fn-mm-tot-charge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-charge a) (fn-mm-tot-charge b)))
        (equal (fn-mm-tot-paged-p (fn-mm-tot-plus a b)) (fn-mm-tot-paged-p a)))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus)))))

(local
 (in-theory (disable fn-mm-tot-plus)))

(local
 (defthm kt-fields-of-zero
   (and (equal (fn-mm-tot-records (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-arena (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-hcharge (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-memberships (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-events (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-log (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-history (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-charge (fn-ct-zero-tot res)) 0)
        (equal (fn-mm-tot-paged-p (fn-ct-zero-tot res)) (equal res :paged)))
   :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))

(local
 (defthm kt-of-records-nats
   (and (natp (nth 0 (fn-ct-of-records rs))) (natp (nth 1 (fn-ct-of-records rs)))
        (natp (nth 2 (fn-ct-of-records rs))) (natp (nth 3 (fn-ct-of-records rs)))
        (natp (nth 4 (fn-ct-of-records rs))))
   :hints (("Goal" :induct (fn-ct-of-records rs)
            :in-theory (e/d ((:induction fn-ct-of-records)) ((:definition fn-ct-of-records) fn-ct-row nfix))
            :expand ((fn-ct-of-records rs))))))

(local
 (defthm kt-history-of-events-cons
   (equal (fn-ct-history-of-events (cons e es))
          (+ (fn-ct-row-history e) (fn-ct-history-of-events es)))
   :hints (("Goal" :in-theory (e/d (fn-ct-history-of-events fn-ct-row-history) (nfix))))))

(local
 (defthm kt-history-of-events-atom
   (implies (not (consp es)) (equal (fn-ct-history-of-events es) 0))
   :hints (("Goal" :in-theory (enable fn-ct-history-of-events)))))

(local
 (defthm kt-log-of-records-cons
   (equal (fn-ct-log-of-records (cons e es))
          (+ (fn-ct-row-log e) (fn-ct-log-of-records es)))
   :hints (("Goal" :in-theory (enable fn-ct-log-of-records)))))

(local
 (defthm kt-log-of-records-atom
   (implies (not (consp es)) (equal (fn-ct-log-of-records es) 0))
   :hints (("Goal" :in-theory (enable fn-ct-log-of-records)))))

(local
 (defthm kt-row-history-natp (natp (fn-ct-row-history row))
   :hints (("Goal" :in-theory (enable fn-ct-row-history)))
   :rule-classes :type-prescription))

(local
 (defthm kt-charged-fields
   (and (equal (fn-mm-tot-records (fn-ct-charged rs res)) (len rs))
        (equal (fn-mm-tot-arena (fn-ct-charged rs res)) (nth 0 (fn-ct-of-records rs)))
        (equal (fn-mm-tot-hcharge (fn-ct-charged rs res)) (nth 1 (fn-ct-of-records rs)))
        (equal (fn-mm-tot-memberships (fn-ct-charged rs res)) (nth 2 (fn-ct-of-records rs)))
        (equal (fn-mm-tot-events (fn-ct-charged rs res)) (nth 3 (fn-ct-of-records rs)))
        (equal (fn-mm-tot-log (fn-ct-charged rs res)) (fn-ct-log-of-records rs))
        (equal (fn-mm-tot-history (fn-ct-charged rs res)) (fn-ct-history-of-events rs))
        (equal (fn-mm-tot-charge (fn-ct-charged rs res)) (nth 4 (fn-ct-of-records rs))))
   :hints (("Goal" :induct (fn-ct-charged rs res)
            :in-theory (e/d ((:induction fn-ct-charged))
                            (fn-ct-row-tot fn-ct-zero-tot fn-ct-row fn-ct-row-log fn-ct-row-history
                             (:definition fn-ct-charged) fn-ct-of-records fn-ct-log-of-records
                             fn-ct-history-of-events fn-ct-of-records-charge-is-the-budget fn-ct-row-charge
                             nfix))
            :expand ((fn-ct-of-records rs))))))

(local
 (defthm kt-of-records-car-natp (natp (car (fn-ct-of-records rs)))
   :hints (("Goal" :use ((:instance kt-of-records-nats)) :in-theory (disable kt-of-records-nats)))))

; KEYSTONE K-TOTALS (3): the fold is at least the store's totals (K3's ask
; of an observer), every field but LOG exactly, LOG when the log's records
; are within their charges (O-LOG).  The history image's events are the
; store's records.
(defthm fn-ct-charged-covers-the-store
  (implies (<= (fn-ct-sum-lengths lens) (fn-ct-log-of-records (fn-sf-records (fn-sn-files s))))
           (fn-mm-tot-le (fn-ct-of-store s lens (fn-sf-records (fn-sn-files s)) residency)
                         (fn-ct-charged (fn-sf-records (fn-sn-files s)) residency)))
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-le fn-ct-of-store fn-sbud-used)
                                  (fn-ct-charged fn-ct-of-records fn-ct-log-of-records
                                   fn-ct-history-of-events fn-ct-sum-lengths nfix)))))

; Equal in every field but LOG: the carried totals charge nothing the store
; does not hold (the teeth of the cover above).
(defthm fn-ct-charged-is-the-store-but-the-log
  (let ((a (fn-ct-of-store s lens (fn-sf-records (fn-sn-files s)) residency))
        (b (fn-ct-charged (fn-sf-records (fn-sn-files s)) residency)))
    (and (equal (fn-mm-tot-records b) (fn-mm-tot-records a))
         (equal (fn-mm-tot-arena b) (fn-mm-tot-arena a))
         (equal (fn-mm-tot-hcharge b) (fn-mm-tot-hcharge a))
         (equal (fn-mm-tot-memberships b) (fn-mm-tot-memberships a))
         (equal (fn-mm-tot-events b) (fn-mm-tot-events a))
         (equal (fn-mm-tot-history b) (fn-mm-tot-history a))
         (equal (fn-mm-tot-charge b) (fn-mm-tot-charge a))
         (equal (fn-mm-tot-paged-p b) (fn-mm-tot-paged-p a))
         (equal (fn-mm-tot-log b) (fn-ct-log-of-records (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (e/d (fn-ct-of-store fn-sbud-used)
                                  (fn-ct-charged fn-ct-of-records fn-ct-log-of-records
                                   fn-ct-history-of-events fn-ct-sum-lengths nfix)))))
