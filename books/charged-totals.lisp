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
