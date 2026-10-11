; fn: the charged totals, the one shape the checkpoint header and the log
; suffix carry and every store-opening command sizes itself by (Builder M,
; landing 1, 2026-10-09; the seam with Builder A, frozen by the coordinator
; 2026-10-09: a change comes as a DECISION with its counterexample).
;
; TOT = (RECORDS ARENA HCHARGE MEMBERSHIPS EVENTS LOG HISTORY CHARGE
;        RESIDENCY), nine fields, each CARRIED by the writer, none derived
; from another:
;   RECORDS      the committed records: fn-sbud-used.
;   ARENA        the physical octets of every held payload, an accepted-
;                statement composite's held payload included.
;   HCHARGE      the held rows' header charges, fn-sbud-held-heap-charge.
;   MEMBERSHIPS  their group memberships, fn-sbud-row-memberships.
;   EVENTS       the encoded octets of every record that is not a plain held
;                row (a composite's whole encoding, a non-article event's).
;   LOG          the octets of the log's records a full replay reads.
;   HISTORY      the history image's event column: the padded SCC encodings
;                (books/history-image-plan.lisp fn-hp-x-rowlen, third value).
;   CHARGE       fn-sbud-bytes-used itself (the budget's coordinate; it is not
;                ARENA's: a composite's encoding carries its payload).
;   RESIDENCY    :resident (payloads in the heap's arena) or :paged.
; The per-record definitions of the first six over a store's records are
; fn-ct-of-records below; LOG and HISTORY are summed over the log's entry
; lengths and the image's row lengths (fn-ct-sum-lengths,
; fn-ct-history-of-events).  The writer's keystone (Builder A, landing 2)
; states the header and the suffix scan equal to these over the durable
; prefix.

(in-package "ACL2")
(include-book "store-budget")
(include-book "history-image-plan")
(include-book "frame-octets")

(local (in-theory (disable (tau-system))))

(defun fn-mm-nat (i x)
  (declare (xargs :guard (natp i)))
  (nfix (nth i (true-list-fix x))))

(defun fn-mm-tot-records (tot) (declare (xargs :guard t)) (fn-mm-nat 0 tot))
(defun fn-mm-tot-arena (tot) (declare (xargs :guard t)) (fn-mm-nat 1 tot))
(defun fn-mm-tot-hcharge (tot) (declare (xargs :guard t)) (fn-mm-nat 2 tot))
(defun fn-mm-tot-memberships (tot) (declare (xargs :guard t)) (fn-mm-nat 3 tot))
(defun fn-mm-tot-events (tot) (declare (xargs :guard t)) (fn-mm-nat 4 tot))
(defun fn-mm-tot-log (tot) (declare (xargs :guard t)) (fn-mm-nat 5 tot))
(defun fn-mm-tot-history (tot) (declare (xargs :guard t)) (fn-mm-nat 6 tot))
(defun fn-mm-tot-charge (tot) (declare (xargs :guard t)) (fn-mm-nat 7 tot))
(defun fn-mm-tot-paged-p (tot)
  (declare (xargs :guard t))
  (equal (nth 8 (true-list-fix tot)) :paged))

(defun fn-mm-make-tot (records arena hcharge memberships events log history charge residency)
  (declare (xargs :guard t))
  (list (nfix records) (nfix arena) (nfix hcharge) (nfix memberships)
        (nfix events) (nfix log) (nfix history) (nfix charge)
        (if (equal residency :paged) :paged :resident)))

; Componentwise order, residency equal: a store that is a prefix of
; another, or what a reclaim leaves of it.
(defun fn-mm-tot-le (a b)
  (declare (xargs :guard t))
  (and (<= (fn-mm-tot-records a) (fn-mm-tot-records b))
       (<= (fn-mm-tot-arena a) (fn-mm-tot-arena b))
       (<= (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b))
       (<= (fn-mm-tot-memberships a) (fn-mm-tot-memberships b))
       (<= (fn-mm-tot-events a) (fn-mm-tot-events b))
       (<= (fn-mm-tot-log a) (fn-mm-tot-log b))
       (<= (fn-mm-tot-history a) (fn-mm-tot-history b))
       (<= (fn-mm-tot-charge a) (fn-mm-tot-charge b))
       (equal (fn-mm-tot-paged-p a) (fn-mm-tot-paged-p b))))

; Two totals together: a checkpoint's and the log's past it.  Residency is
; the first's.
(defun fn-mm-tot-plus (a b)
  (declare (xargs :guard t))
  (fn-mm-make-tot (+ (fn-mm-tot-records a) (fn-mm-tot-records b))
                  (+ (fn-mm-tot-arena a) (fn-mm-tot-arena b))
                  (+ (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b))
                  (+ (fn-mm-tot-memberships a) (fn-mm-tot-memberships b))
                  (+ (fn-mm-tot-events a) (fn-mm-tot-events b))
                  (+ (fn-mm-tot-log a) (fn-mm-tot-log b))
                  (+ (fn-mm-tot-history a) (fn-mm-tot-history b))
                  (+ (fn-mm-tot-charge a) (fn-mm-tot-charge b))
                  (if (fn-mm-tot-paged-p a) :paged :resident)))


; The recognizer: nine fields, eight naturals and a residency word.
(defun fn-mm-tot-p (tot)
  (declare (xargs :guard t))
  (and (true-listp tot) (equal (len tot) 9)
       (natp (nth 0 tot)) (natp (nth 1 tot)) (natp (nth 2 tot)) (natp (nth 3 tot))
       (natp (nth 4 tot)) (natp (nth 5 tot)) (natp (nth 6 tot)) (natp (nth 7 tot))
       (member-equal (nth 8 tot) '(:resident :paged))))

(defthm fn-mm-make-tot-is-a-tot
  (fn-mm-tot-p (fn-mm-make-tot records arena hcharge memberships events log history charge
                               residency))
  :hints (("Goal" :in-theory (e/d (fn-mm-make-tot fn-mm-tot-p) (nfix)))))

; One record's frame in the log: the batch's four-octet length, the frame
; header, the 32-octet chain value the frame carries and its trailer
; (books/history-totals-carried.lisp fn-ct-row-log charges each record one).
(defconst *fn-ct-log-frame-octets*
  (+ 4 *fn-frame-header-octets* *fn-frame-trailer-octets* *fn-frame-trailer-octets*))

; -----------------------------------------------------------------------------
; The per-record definitions over a store's records (fn-sf-records).

; One record's (ARENA HCHARGE MEMBERSHIPS EVENTS CHARGE).
(defun fn-ct-row (row)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-held-p row)
         (list (nfix (fn-hf-octets (fn-held-facts row)))
               (fn-sbud-held-heap-charge row)
               (fn-sbud-row-memberships row)
               0
               (fn-sbud-row-octets row)))
        ((fn-hstxa-p row)
         (list (nfix (fn-hf-octets (fn-held-facts (fn-hstxa-held row))))
               (fn-sbud-held-heap-charge (fn-hstxa-held row))
               (fn-sbud-row-memberships row)
               (len (fn-store-event-encode (fn-hstxa-stxa row)))
               (fn-sbud-row-octets row)))
        (t (list 0 0 0 (len (fn-store-event-encode row)) (fn-sbud-row-octets row)))))

(defun fn-ct-of-records (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (let ((r (fn-ct-row (car records))) (rest (fn-ct-of-records (cdr records))))
        (list (+ (nfix (nth 0 r)) (nfix (nth 0 rest)))
              (+ (nfix (nth 1 r)) (nfix (nth 1 rest)))
              (+ (nfix (nth 2 r)) (nfix (nth 2 rest)))
              (+ (nfix (nth 3 r)) (nfix (nth 3 rest)))
              (+ (nfix (nth 4 r)) (nfix (nth 4 rest)))))
    (list 0 0 0 0 0)))

; LOG: the log's entry lengths summed.
(defun fn-ct-sum-lengths (lens)
  (declare (xargs :guard t))
  (if (consp lens) (+ (nfix (car lens)) (fn-ct-sum-lengths (cdr lens))) 0))

; HISTORY: the image's padded SCC row lengths over its events.
(defun fn-ct-history-of-events (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (mv-let (err tl plen) (fn-hp-x-rowlen (car events))
        (declare (ignore err tl))
        (+ (nfix plen) (fn-ct-history-of-events (cdr events))))
    0))

; The totals of a store S, its log's entry lengths LENS and the image's
; events EVENTS, at RESIDENCY: what the writer carries.
(defun fn-ct-of-store (s lens events residency)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-ct-of-records (fn-sf-records (fn-sn-files s)))))
    (fn-mm-make-tot (fn-sbud-used s) (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r)
                    (fn-ct-sum-lengths lens) (fn-ct-history-of-events events) (nth 4 r)
                    residency)))

; CHARGE is the budget's own sum.
(defthm fn-ct-row-charge
  (equal (nth 4 (fn-ct-row row)) (fn-sbud-row-octets row))
  :hints (("Goal" :in-theory (e/d (fn-ct-row)
                                  (fn-sbud-row-octets fn-sbud-held-heap-charge fn-sbud-row-memberships
                                   fn-store-event-encode fn-held-p fn-hstxa-p)))))

(defthm fn-ct-of-records-charge-is-the-budget
  (equal (nth 4 (fn-ct-of-records records)) (nfix (fn-sbud-record-octets records)))
  :hints (("Goal" :induct (fn-ct-of-records records)
           :in-theory (e/d (fn-sbud-record-octets) (fn-ct-row fn-sbud-row-octets)))))

; -----------------------------------------------------------------------------
; The charged fold (Builder M, books/history-totals-carried.lisp K-TOTALS;
; moved here verbatim by Builder A's charged-totals header, 2026-10-10, so
; the checkpoint's F row (books/store-checkpoint-tables.lisp) folds them
; without the history stobj's closure).

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

; The log's records' octets a full replay reads, charged.
(defun fn-ct-log-of-records (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (+ (fn-ct-row-log (car records)) (fn-ct-log-of-records (cdr records)))
    0))

(verify-guards fn-ct-row)
(verify-guards fn-ct-row-log)
(verify-guards fn-ct-row-tot)
(verify-guards fn-ct-charged)
(verify-guards fn-ct-log-of-records)

(local (in-theory (disable fn-ct-row fn-ct-row-log fn-ct-row-history)))

; The algebra of the fold (the technique of Builder M's K-TOTALS lemmas in
; books/history-totals-carried.lisp): a tot is the list of its nine fields,
; the sum is associative, and the zero of a residency is its identity.
(local
 (defthm fn-ct-take-len (implies (true-listp x) (equal (take (len x) x) x))))

(local
 (defthm fn-ct-take9
   (equal (take 9 x) (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x)
                           (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable nth)
            :expand ((take 9 x) (take 8 (cdr x)) (take 7 (cddr x)) (take 6 (cdddr x))
                     (take 5 (cddddr x)) (take 4 (cdr (cddddr x))) (take 3 (cddr (cddddr x)))
                     (take 2 (cdddr (cddddr x))) (take 1 (cddddr (cddddr x)))
                     (take 0 (cdr (cddddr (cddddr x)))))))))

(local
 (defthm fn-ct-tot-shape
   (implies (fn-mm-tot-p tot)
            (equal tot (list (nth 0 tot) (nth 1 tot) (nth 2 tot) (nth 3 tot) (nth 4 tot)
                             (nth 5 tot) (nth 6 tot) (nth 7 tot) (nth 8 tot))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-ct-take-len (x tot)) (:instance fn-ct-take9 (x tot)))
            :in-theory (e/d (fn-mm-tot-p) (fn-ct-take-len))))))

(local
 (defthm fn-ct-plus-zero-list
   (implies (and (natp a) (natp b) (natp c) (natp d) (natp e) (natp f) (natp g) (natp h)
                 (member-equal r '(:resident :paged)))
            (and (equal (fn-mm-tot-plus (list a b c d e f g h r) (fn-ct-zero-tot res))
                        (list a b c d e f g h r))
                 (implies (equal (equal r :paged) (equal res :paged))
                          (equal (fn-mm-tot-plus (fn-ct-zero-tot res) (list a b c d e f g h r))
                                 (list a b c d e f g h r)))))
   :hints (("Goal" :in-theory (enable fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot
                             fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                             fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                             fn-mm-tot-paged-p fn-mm-nat)))))

(local
 (defthm fn-ct-plus-zero
   (implies (fn-mm-tot-p tot)
            (and (equal (fn-mm-tot-plus tot (fn-ct-zero-tot res)) tot)
                 (implies (equal (fn-mm-tot-paged-p tot) (equal res :paged))
                          (equal (fn-mm-tot-plus (fn-ct-zero-tot res) tot) tot))))
   :hints (("Goal" :use (fn-ct-tot-shape
                         (:instance fn-ct-plus-zero-list (a (nth 0 tot)) (b (nth 1 tot))
                                    (c (nth 2 tot)) (d (nth 3 tot)) (e (nth 4 tot))
                                    (f (nth 5 tot)) (g (nth 6 tot)) (h (nth 7 tot))
                                    (r (nth 8 tot))))
            :in-theory (e/d (fn-mm-tot-p fn-mm-tot-paged-p) (fn-ct-plus-zero-list))))))

(local
 (defthm fn-ct-nfix-nfix (equal (nfix (nfix a)) (nfix a))))

(local
 (defthm fn-ct-records-of-make
   (equal (fn-mm-tot-records (fn-mm-make-tot a b c d e f g h r)) (nfix a))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-records fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-records
   (natp (fn-mm-tot-records a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-records fn-mm-nat)))))

(local
 (defthm fn-ct-arena-of-make
   (equal (fn-mm-tot-arena (fn-mm-make-tot a b c d e f g h r)) (nfix b))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-arena fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-arena
   (natp (fn-mm-tot-arena a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-arena fn-mm-nat)))))

(local
 (defthm fn-ct-hcharge-of-make
   (equal (fn-mm-tot-hcharge (fn-mm-make-tot a b c d e f g h r)) (nfix c))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-hcharge fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-hcharge
   (natp (fn-mm-tot-hcharge a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-hcharge fn-mm-nat)))))

(local
 (defthm fn-ct-memberships-of-make
   (equal (fn-mm-tot-memberships (fn-mm-make-tot a b c d e f g h r)) (nfix d))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-memberships fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-memberships
   (natp (fn-mm-tot-memberships a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-memberships fn-mm-nat)))))

(local
 (defthm fn-ct-events-of-make
   (equal (fn-mm-tot-events (fn-mm-make-tot a b c d e f g h r)) (nfix e))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-events fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-events
   (natp (fn-mm-tot-events a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-events fn-mm-nat)))))

(local
 (defthm fn-ct-log-of-make
   (equal (fn-mm-tot-log (fn-mm-make-tot a b c d e f g h r)) (nfix f))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-log fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-log
   (natp (fn-mm-tot-log a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-log fn-mm-nat)))))

(local
 (defthm fn-ct-history-of-make
   (equal (fn-mm-tot-history (fn-mm-make-tot a b c d e f g h r)) (nfix g))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-history fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-history
   (natp (fn-mm-tot-history a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-history fn-mm-nat)))))

(local
 (defthm fn-ct-charge-of-make
   (equal (fn-mm-tot-charge (fn-mm-make-tot a b c d e f g h r)) (nfix h))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-charge fn-mm-nat fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-natp-charge
   (natp (fn-mm-tot-charge a))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-mm-tot-charge fn-mm-nat)))))

(local
 (defthm fn-ct-paged-of-make
   (equal (fn-mm-tot-paged-p (fn-mm-make-tot a b c d e f g h r)) (equal r :paged))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-paged-p fn-mm-make-tot) (nfix))))))

(local
 (defthm fn-ct-plus-assoc
   (equal (fn-mm-tot-plus (fn-mm-tot-plus a b) c) (fn-mm-tot-plus a (fn-mm-tot-plus b c)))
   :hints (("Goal" :in-theory (e/d (fn-mm-tot-plus)
                                   (fn-mm-make-tot fn-mm-tot-records fn-mm-tot-arena
                                    fn-mm-tot-hcharge fn-mm-tot-memberships fn-mm-tot-events
                                    fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                                    fn-mm-tot-paged-p))))))

(local
 (defthm fn-ct-tot-p-of-plus (fn-mm-tot-p (fn-mm-tot-plus a b))
   :hints (("Goal" :in-theory (union-theories '(fn-mm-tot-plus fn-mm-make-tot-is-a-tot)
                                            (theory 'minimal-theory))))))

(local
 (defthm fn-ct-tot-p-of-zero (fn-mm-tot-p (fn-ct-zero-tot r))
   :hints (("Goal" :in-theory (union-theories '(fn-ct-zero-tot fn-mm-make-tot-is-a-tot)
                                            (theory 'minimal-theory))))))

(local
 (defthm fn-ct-paged-of-charged
   (equal (fn-mm-tot-paged-p (fn-ct-charged rs res)) (equal res :paged))
   :hints (("Goal" :induct (fn-ct-charged rs res)
            :in-theory (e/d (fn-mm-tot-plus fn-ct-row-tot fn-ct-zero-tot)
                            (fn-mm-make-tot fn-mm-tot-paged-p fn-mm-tot-p))))))

(local
 (defthm fn-ct-tot-p-of-charged (fn-mm-tot-p (fn-ct-charged rs res))
   :hints (("Goal" :expand ((fn-ct-charged rs res))
            :in-theory (disable fn-mm-tot-p fn-mm-tot-plus fn-ct-zero-tot)))))

(local
 (in-theory (disable fn-mm-tot-plus fn-ct-zero-tot (:e fn-ct-zero-tot) fn-ct-row-tot fn-mm-tot-p)))

; The fold over an append is the sum of the folds (the checkpoint's header
; plus its suffix, books/charged-totals-header.lisp).  No hypothesis.
(defthm fn-ct-charged-of-append
  (equal (fn-ct-charged (append a b) residency)
         (fn-mm-tot-plus (fn-ct-charged a residency) (fn-ct-charged b residency)))
  :hints (("Goal" :induct (len a))))

; The fold's shape, for its readers (the checkpoint's header, the open's
; seed): a tot, its RECORDS the record count, its residency the argument's,
; blind to a list's terminator, and equal at two residency words that are
; equally :paged.
(defthm fn-ct-charged-is-a-tot
  (fn-mm-tot-p (fn-ct-charged records residency))
  :hints (("Goal" :expand ((fn-ct-charged records residency)))))

(defthm fn-ct-charged-records
  (equal (fn-mm-tot-records (fn-ct-charged records residency)) (len records))
  :hints (("Goal" :induct (len records)
           :in-theory (e/d (fn-mm-tot-plus fn-ct-row-tot fn-ct-zero-tot)
                           (fn-mm-make-tot fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                            fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log
                            fn-mm-tot-history fn-mm-tot-charge fn-mm-tot-paged-p)))))

(defthm fn-ct-charged-paged-p
  (equal (fn-mm-tot-paged-p (fn-ct-charged records residency)) (equal residency :paged))
  :hints (("Goal" :expand ((fn-ct-charged records residency)))))

(defthm fn-ct-charged-of-true-list-fix
  (equal (fn-ct-charged (true-list-fix records) residency) (fn-ct-charged records residency))
  :hints (("Goal" :induct (len records) :in-theory (enable fn-ct-charged))))

(defthm fn-ct-charged-residency-word
  (implies (equal (equal r1 :paged) (equal r2 :paged))
           (equal (fn-ct-charged records r1) (fn-ct-charged records r2)))
  :rule-classes nil
  :hints (("Goal" :induct (len records)
           :in-theory (enable fn-ct-charged fn-mm-tot-plus fn-ct-row-tot fn-ct-zero-tot
                              fn-mm-make-tot fn-mm-tot-paged-p))))

; The fold with an accumulator: one frame however many records (the list
; fold holds one a record).  The checkpoint's writer runs it through
; fn-ct-charged-exec; fn-ct-charged-acc-is-the-fold makes it the fold.
(defun fn-ct-charged-acc (records residency acc)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-ct-charged-acc (cdr records) residency
                         (fn-mm-tot-plus acc (fn-ct-row-tot (car records) residency)))
    acc))

(local
 (defthm fn-ct-tot-p-of-row-tot (fn-mm-tot-p (fn-ct-row-tot r res))
   :hints (("Goal" :in-theory (union-theories '(fn-ct-row-tot fn-mm-make-tot-is-a-tot)
                                            (theory 'minimal-theory))))))

(local
 (defthm fn-ct-charged-of-singleton
   (equal (fn-ct-charged (list r) res) (fn-ct-row-tot r res))
   :hints (("Goal" :expand ((fn-ct-charged (list r) res))))))

(local
 (defun fn-ct-acc-ind (records a)
   (if (consp records)
       (fn-ct-acc-ind (cdr records) (append a (list (car records))))
     a)))

(local
 (defthm fn-ct-append-assoc-singleton
   (equal (append (append a (list x)) y) (append a (cons x y)))))

(local
 (defthm fn-ct-charged-acc-is-plus
   (equal (fn-ct-charged-acc records residency (fn-ct-charged a residency))
          (fn-ct-charged (append a records) residency))
   :hints (("Goal" :induct (fn-ct-acc-ind records a)
            :expand ((fn-ct-charged-acc records residency (fn-ct-charged a residency))))
           ("Subgoal *1/1" :use ((:instance fn-ct-charged-of-append (a a) (b (list (car records)))))))))

(defthm fn-ct-charged-acc-is-the-fold
  (equal (fn-ct-charged-acc records residency (fn-ct-zero-tot residency))
         (fn-ct-charged records residency))
  :hints (("Goal" :use ((:instance fn-ct-charged-acc-is-plus (a nil)))
           :in-theory (e/d (fn-ct-charged) (fn-ct-charged-acc-is-plus)))))

; The executable fold: the list fold in the logic, the accumulator at run time.
(defun fn-ct-charged-exec (records residency)
  (declare (xargs :guard t))
  (mbe :logic (fn-ct-charged records residency)
       :exec (fn-ct-charged-acc records residency (fn-ct-zero-tot residency))))
