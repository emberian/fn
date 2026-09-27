; Witnesses for books/store-log-walk-once (the full replay's walk decodes
; each record once).
;
; fn-lgw-run-nf-then-fold-is-run, fn-lgw-run-of-set-next-is-run-nf,
; fn-lgw-step-buf-nf-is-step-nf, fn-lgb-decode-next-exec-fold and
; fn-lgb-decode-next-exec-decode have no hypothesis.  REACHABLE:
;   (1) three one-record entries and one batch entry, walked the host's way
;       (header window, entry length, the entry into the buffer, the step
;       that keeps NEXT), the records decoded in two chunks by
;       fn-lgb-decode-next, NEXT set to the fold at the end: the records, the
;       state and the kernel are fn-lgw-run's, and the chunks' events are
;       fn-srs-decode's of all the records;
;   (2) the walk without the fold keeps the start's NEXT (1) where the run's
;       is 4: the fold is what sets it (the equality is not vacuous);
;   (3) a torn tail and a splice: the same stop, BROKEN for the splice.
(in-package "ACL2")
(include-book "../../books/store-log-walk-once")
(include-book "../../books/codec-attach")

(defun sloo-unit () (declare (xargs :guard t)) 4)
(defun sloo-max () (declare (xargs :guard t)) 4096)
(defun sloo-extent () (declare (xargs :guard t)) 2048)
(defun sloo-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))
(defun sloo-pad (log)
  (declare (xargs :guard t :verify-guards nil))
  (append log (fn-bs-zeros (- (sloo-extent) (len log)))))
(defun sloo-t1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (sloo-rec 1)) *fn-lg-genesis*))
(defun sloo-t2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (sloo-rec 2)) (sloo-t1)))
(defun sloo-log3 () (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (sloo-rec 1)) *fn-lg-genesis* (sloo-unit))
          (fn-lg-log (list (sloo-rec 2)) (sloo-t1) (sloo-unit))
          (fn-lg-log (list (sloo-rec 3)) (sloo-t2) (sloo-unit))))
(defun sloo-seg () (declare (xargs :guard t :verify-guards nil)) (sloo-pad (sloo-log3)))
(defun sloo-batch () (declare (xargs :guard t :verify-guards nil))
  (sloo-pad (fn-lg-log (list (sloo-rec 1) (sloo-rec 2) (sloo-rec 3)) *fn-lg-genesis* (sloo-unit))))
(defun sloo-torn () (declare (xargs :guard t :verify-guards nil))
  (let ((l (sloo-log3)))
    (sloo-pad (append (fn-bs-take (- (len l) 8) l) (fn-bs-zeros 8)))))
(defun sloo-splice () (declare (xargs :guard t :verify-guards nil))
  (sloo-pad (append (fn-lg-log (list (sloo-rec 1)) *fn-lg-genesis* (sloo-unit))
                    (fn-lg-log (list (sloo-rec 2))
                               (fn-lg-last-trailer (list (sloo-rec 7)) *fn-lg-genesis*)
                               (sloo-unit)))))

; The host's walk without the fold (fnn-log-stream-segment under
; *fnn-log-stream-finish*): the records it hands on, and its final state.
(defun sloo-walk (c st fuel acc fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgw-stop st))
      (mv (reverse acc) st fn-octets-lg)
    (let* ((pos (fn-lgw-pos st))
           (h (fn-bs-take (fn-lgw-header-len st (len c)) (nthcdr pos c)))
           (n (fn-lgw-entry-len h st (len c)))
           (e (and n (fn-bs-take n (nthcdr pos c))))
           (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
      (mv-let (took records st2) (fn-lgw-step-buf-nf st (sloo-unit) (sloo-max) (len c) fn-octets-lg)
        (sloo-walk c st2 (1- fuel) (if took (revappend records acc) acc) fn-octets-lg)))))

; The replay's two chunks (the first record, then the rest), decoded with
; the fold carried; then NEXT set to the fold (the segment's end).
(defun sloo-host (c fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil))
  (mv-let (records st fn-octets-lg)
    (sloo-walk c (fn-lgw-start *fn-lg-genesis* 1) 100 nil fn-octets-lg)
    (mv-let (ev1 n1) (fn-lgb-decode-next (take 1 records) 1)
      (mv-let (ev2 n2) (fn-lgb-decode-next (nthcdr 1 records) n1)
        (mv records (fn-lgw-set-next st n2) (append ev1 ev2) st fn-octets-lg)))))

(defun sloo-agrees (c fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil))
  (mv-let (records st events st-nf fn-octets-lg) (sloo-host c fn-octets-lg)
    (mv-let (rrecords rst) (fn-lgw-run c (fn-lgw-start *fn-lg-genesis* 1) (sloo-unit) (sloo-max))
      (mv (and (equal records rrecords)
               (equal st rst)
               (equal (fn-lgw-kernel st) (fn-lgw-kernel rst))
               (equal events (fn-srs-decode records))
               (not (equal events :bad))
               (equal (len events) (len records))
               (equal (fn-lgw-next st-nf) 1))
          records st fn-octets-lg))))

; (1) and (2): three entries; one batch entry.
(assert-event
 (mv-let (ok records st fn-octets-lg) (sloo-agrees (sloo-seg) fn-octets-lg)
   (mv (and ok
            (equal records (list (sloo-rec 1) (sloo-rec 2) (sloo-rec 3)))
            (equal (fn-lgw-next st) 4)
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (mv-let (ok records st fn-octets-lg) (sloo-agrees (sloo-batch) fn-octets-lg)
   (mv (and ok
            (equal records (list (sloo-rec 1) (sloo-rec 2) (sloo-rec 3)))
            (equal (fn-lgw-next st) 4))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (3) The torn tail and the splice.
(assert-event
 (mv-let (ok records st fn-octets-lg) (sloo-agrees (sloo-torn) fn-octets-lg)
   (mv (and ok
            (equal records (list (sloo-rec 1) (sloo-rec 2)))
            (equal (fn-lgw-next st) 3)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (mv-let (ok records st fn-octets-lg) (sloo-agrees (sloo-splice) fn-octets-lg)
   (mv (and ok
            (equal records (list (sloo-rec 1)))
            (equal (fn-lgw-broken st) t))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; The decode's events and fold over records the codec refuses: a
; non-record answers :bad as fn-srs-decode does, and its txid folds as nil.
(assert-event
 (mv-let (events next) (fn-lgb-decode-next (list (sloo-rec 1) '(1 2 3)) 1)
   (and (equal events (fn-srs-decode (list (sloo-rec 1) '(1 2 3))))
        (equal events :bad)
        (equal next (fn-lgw-next-fold (list (sloo-rec 1) '(1 2 3)) 1))
        (equal next 2))))

(assert-event
 (and (eq (symbol-class 'fn-lgw-step-buf-nf (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-decode-next (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgw-set-next (w state)) :common-lisp-compliant)))
