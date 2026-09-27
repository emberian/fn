; Witnesses for books/store-log-buffer (the log walk over the entry's octet
; buffer: the host preads the entry into fn-octets-lg and ACL2 decides it in
; place).
;
; fn-lgw-step-buf-is-step, fn-lgb-decide-is-decide and
; fn-lgb-entry-places-is-list-places are unconditional equalities (no
; hypothesis to remove); fn-lgb-decide-fast-is-decide and
; fn-lgb-decide-is-flat carry the buffer's representation invariant and the
; fast path's range, which the unconditional ones discharge.  Witnesses, all
; REACHABLE (the host's own loop, spelled over the live buffer):
;   (1) three one-record entries chained from genesis, walked by the buffer
;       step and by the list step: the same records, places and state at
;       every step, and the run's records;
;   (2) one batch entry (kind 2, three records): the buffer step takes all
;       three through the index unpack; each record's place is the list
;       walk's (fn-arx-list-places) and addresses the record's octets in the
;       entry;
;   (3) the torn tail and the splice stop the buffer walk exactly where the
;       list walk stops, BROKEN for the splice;
;   (4) the fast path's range: every entry above is at least 74 octets and
;       max a frame bound (fn-lgb-decide-fast answers them); a 60-octet
;       window and an out-of-range bound go to the list fallback and answer
;       as the list step does.
(in-package "ACL2")
(include-book "../../books/store-log-buffer")

(defun slb-unit () (declare (xargs :guard t)) 4)
(defun slb-max () (declare (xargs :guard t)) 4096)
(defun slb-extent () (declare (xargs :guard t)) 2048)
(defun slb-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))

(defun slb-pad (log)
  (declare (xargs :guard t :verify-guards nil))
  (append log (fn-bs-zeros (- (slb-extent) (len log)))))

(defun slb-t1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slb-rec 1)) *fn-lg-genesis*))
(defun slb-t2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slb-rec 2)) (slb-t1)))
(defun slb-log3 () (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (slb-rec 1)) *fn-lg-genesis* (slb-unit))
          (fn-lg-log (list (slb-rec 2)) (slb-t1) (slb-unit))
          (fn-lg-log (list (slb-rec 3)) (slb-t2) (slb-unit))))
(defun slb-seg () (declare (xargs :guard t :verify-guards nil)) (slb-pad (slb-log3)))
(defun slb-batch () (declare (xargs :guard t :verify-guards nil))
  (slb-pad (fn-lg-log (list (slb-rec 1) (slb-rec 2) (slb-rec 3)) *fn-lg-genesis* (slb-unit))))
(defun slb-torn () (declare (xargs :guard t :verify-guards nil))
  (let ((l (slb-log3)))
    (slb-pad (append (fn-bs-take (- (len l) 8) l) (fn-bs-zeros 8)))))
(defun slb-splice () (declare (xargs :guard t :verify-guards nil))
  (slb-pad (append (fn-lg-log (list (slb-rec 1)) *fn-lg-genesis* (slb-unit))
                   (fn-lg-log (list (slb-rec 2))
                              (fn-lg-last-trailer (list (slb-rec 7)) *fn-lg-genesis*)
                              (slb-unit)))))

; The host's loop (host/native/io.lisp fnn-log-stream-segment): the header
; window, the entry length, the entry's octets into the buffer (none: an
; empty buffer), the buffer step, and the places of a taken entry.  Beside
; it, the list step and fn-arx-list-places on the same window; SAME is
; whether every step agreed.
(defun slb-walk (c st fuel acc places same fn-octets-lg)
  (declare (xargs :stobjs fn-octets-lg :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgw-stop st))
      (mv (reverse acc) (reverse places) same st fn-octets-lg)
    (let* ((pos (fn-lgw-pos st))
           (h (fn-bs-take (fn-lgw-header-len st (len c)) (nthcdr pos c)))
           (n (fn-lgw-entry-len h st (len c)))
           (e (and n (fn-bs-take n (nthcdr pos c))))
           (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
      (mv-let (took records st2) (fn-lgw-step-buf st (slb-unit) (slb-max) (len c) fn-octets-lg)
        (mv-let (ltook lrecords lst2) (fn-lgw-step e st (slb-unit) (slb-max) (len c))
          (let* ((pl (and took (fn-lgb-entry-places pos (len records) (slb-unit) fn-octets-lg)))
                 (lpl (and ltook (fn-arx-list-places e pos (len lrecords) (slb-unit) 0 0 nil 0 0 nil)))
                 (same (and same (equal took ltook) (equal records lrecords)
                            (equal st2 lst2) (equal pl lpl)
                            (or (not n) (<= *fn-lgb-min* n)))))
            (slb-walk c st2 (1- fuel) (if took (revappend records acc) acc)
                      (revappend pl places) same fn-octets-lg)))))))

; (1) Three one-record entries.
(assert-event
 (mv-let (records places same st fn-octets-lg)
   (slb-walk (slb-seg) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2) (slb-rec 3)))
            (equal (len places) 3)
            (mv-let (lrecords lst) (fn-lgw-run (slb-seg) (fn-lgw-start *fn-lg-genesis* 1)
                                               (slb-unit) (slb-max))
              (and (equal records lrecords) (equal st lst)))
            (equal (fn-lgw-count st) 3)
            (equal (fn-lgw-next st) 4)
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (2) One batch entry: three records by the index unpack; each place
; (START N ROFF RLEN) addresses its record's octets in the segment.
(defun slb-at (c place)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-take (nth 3 place) (nthcdr (nth 2 place) c)))

(assert-event
 (mv-let (records places same st fn-octets-lg)
   (slb-walk (slb-batch) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2) (slb-rec 3)))
            (equal (len places) 3)
            (equal (slb-at (slb-batch) (nth 0 places)) (slb-rec 1))
            (equal (slb-at (slb-batch) (nth 1 places)) (slb-rec 2))
            (equal (slb-at (slb-batch) (nth 2 places)) (slb-rec 3))
            (equal (fn-lgw-count st) 3)
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (3) The torn tail: two records, not broken.  The splice: one record, BROKEN.
(assert-event
 (mv-let (records places same st fn-octets-lg)
   (slb-walk (slb-torn) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (declare (ignore places))
   (mv (and same
            (equal records (list (slb-rec 1) (slb-rec 2)))
            (fn-lgw-stop st)
            (not (fn-lgw-broken st)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (mv-let (records places same st fn-octets-lg)
   (slb-walk (slb-splice) (fn-lgw-start *fn-lg-genesis* 1) 100 nil nil t fn-octets-lg)
   (declare (ignore places))
   (mv (and same
            (equal records (list (slb-rec 1)))
            (fn-lgw-stop st)
            (equal (fn-lgw-broken st) t))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

; (4) The fast path answers the first entry of the batch segment; a 60-octet
; window and a bound past the frame grammar's go to the list fallback, and
; every answer is the list step's.
(assert-event
 (let* ((c (slb-batch))
        (n (fn-lgw-entry-len (fn-bs-take 10 c) (fn-lgw-start *fn-lg-genesis* 1) (len c)))
        (e (fn-bs-take n c))
        (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
   (mv (and (<= *fn-lgb-min* n)
            (equal (mv-list 2 (fn-lgb-decide-fast *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (mv-list 2 (fn-lgw-decide e *fn-lg-genesis* (slb-max))))
            (mv-let (ok records) (fn-lgb-decide *fn-lg-genesis* (slb-max) fn-octets-lg)
              (and (equal ok t) (equal (len records) 3)))
            (equal (mv-list 2 (fn-lgb-decide *fn-lg-genesis* (+ 1 *fn-frame-max-payload*)
                                             fn-octets-lg))
                   (mv-list 2 (fn-lgw-decide e *fn-lg-genesis* (+ 1 *fn-frame-max-payload*))))
            ;; a wrong predecessor: refused before the digest, as the list refuses
            (equal (mv-list 2 (fn-lgb-decide (slb-t1) (slb-max) fn-octets-lg))
                   (mv-list 2 (fn-lgw-decide e (slb-t1) (slb-max))))
            (mv-let (ok records) (fn-lgb-decide (slb-t1) (slb-max) fn-octets-lg)
              (declare (ignore records))
              (equal ok nil)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (let* ((e (fn-bs-take 60 (slb-batch)))
        (fn-octets-lg (fn-octets-lg-from-list e fn-octets-lg)))
   (mv (and (equal (mv-list 2 (fn-lgb-decide *fn-lg-genesis* (slb-max) fn-octets-lg))
                   (mv-list 2 (fn-lgw-decide e *fn-lg-genesis* (slb-max))))
            (mv-let (ok records) (fn-lgb-decide *fn-lg-genesis* (slb-max) fn-octets-lg)
              (declare (ignore records))
              (equal ok nil)))
       fn-octets-lg))
 :stobjs-out '(nil fn-octets-lg))

(assert-event
 (and (eq (symbol-class 'fn-lgw-step-buf (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-decide-fast (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-lgb-entry-places (w state)) :common-lisp-compliant)))
