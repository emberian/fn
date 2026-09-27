; Witnesses for books/store-log-stream (the format-9 open as a stream of
; entries: the host reads one entry's octets at a time and ACL2 decides it).
;
; fn-lgw-run-is-the-open and fn-lgw-run-is-fn-lgc-open are unconditional
; equalities; fn-lgw-run-is-the-scan has two hypotheses (the stream has not
; stopped; POS is inside the segment).  Witnesses:
;   (1) REACHABLE: a real segment (the codec's workload records chained from
;       genesis, zero padded), walked the way the host walks it (header window,
;       entry length, entry window, step) and by fn-lgw-run; both sides of
;       each keystone evaluated and equal; the stream holds no record in its
;       state.
;   (2) REACHABLE: a torn tail (the third entry's last units zeroed) stops the
;       stream after two records, as the scan does; a splice (the second entry
;       chained from another history) stops it with BROKEN, as
;       fn-lgs-chain-broken-p says.
;   (3) HYPOTHESIS REMOVAL for fn-lgw-run-is-the-scan: a stopped stream (the
;       omitted hypothesis false) emits nothing while the scan reads two
;       records: the conclusion fails; the retained hypothesis (POS inside the
;       segment) holds there.
;   (4) CORRUPTED STATE (labelled): a stream started from a predecessor that is
;       not the segment's genesis reads no record and reports the splice.
(in-package "ACL2")
(include-book "../../books/store-log-stream")

(defun slw-unit () (declare (xargs :guard t)) 4)
(defun slw-max () (declare (xargs :guard t)) 4096)
(defun slw-extent () (declare (xargs :guard t)) 2048)
(defun slw-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))

(defun slw-pad (log)
  (declare (xargs :guard t :verify-guards nil))
  (append log (fn-bs-zeros (- (slw-extent) (len log)))))

; Records 1 .. 3 as three appends of one record each (three entries), chained
; from genesis, zeros to the extent.
; T1, T2, T3: the trailers after each one-record entry.
(defun slw-t1 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slw-rec 1)) *fn-lg-genesis*))
(defun slw-t2 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slw-rec 2)) (slw-t1)))
(defun slw-t3 () (declare (xargs :guard t :verify-guards nil))
  (fn-lg-last-trailer (list (slw-rec 3)) (slw-t2)))
(defun slw-log3 () (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (slw-rec 1)) *fn-lg-genesis* (slw-unit))
          (fn-lg-log (list (slw-rec 2)) (slw-t1) (slw-unit))
          (fn-lg-log (list (slw-rec 3)) (slw-t2) (slw-unit))))

; The same three records as ONE append: a batch entry (kind 2, PKT-749).
(defun slw-batch () (declare (xargs :guard t :verify-guards nil))
  (slw-pad (fn-lg-log (list (slw-rec 1) (slw-rec 2) (slw-rec 3)) *fn-lg-genesis* (slw-unit))))
(defun slw-seg () (declare (xargs :guard t :verify-guards nil)) (slw-pad (slw-log3)))

; The torn tail: the third entry's last eight octets zeroed.
(defun slw-torn () (declare (xargs :guard t :verify-guards nil))
  (let ((l (slw-log3)))
    (slw-pad (append (fn-bs-take (- (len l) 8) l) (fn-bs-zeros 8)))))

; The splice: entry 1 from genesis, then an entry chained from another
; history's trailer (record 7's, from genesis).
(defun slw-splice () (declare (xargs :guard t :verify-guards nil))
  (slw-pad (append (fn-lg-log (list (slw-rec 1)) *fn-lg-genesis* (slw-unit))
                   (fn-lg-log (list (slw-rec 2))
                              (fn-lg-last-trailer (list (slw-rec 7)) *fn-lg-genesis*)
                              (slw-unit)))))

; The host's walk, spelled as host/native/io.lisp fnn-log-stream-segment does
; it: read the header window, ask the entry length, read the entry (or none),
; step; emit a taken record; stop when the state stops.  FUEL bounds it.
(defun slw-host-walk (c st fuel acc)
  (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn-lgw-stop st))
      (mv (reverse acc) st)
    (let* ((pos (fn-lgw-pos st))
           (h (fn-bs-take (fn-lgw-header-len st (len c)) (nthcdr pos c)))
           (n (fn-lgw-entry-len h st (len c)))
           (e (and n (fn-bs-take n (nthcdr pos c)))))
      (mv-let (took records st2) (fn-lgw-step e st (slw-unit) (slw-max) (len c))
        (slw-host-walk c st2 (1- fuel) (if took (revappend records acc) acc))))))

(defun slw-recover (c) (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover c *fn-lg-genesis* (slw-unit) (slw-max) 1))

; (1) The whole segment: the host's walk, the run and the recovered kernel agree.
(assert-event
 (let* ((c (slw-seg))
        (st0 (fn-lgw-start *fn-lg-genesis* 1))
        (ks (slw-recover c)))
   (mv-let (walked stw) (slw-host-walk c st0 100 nil)
     (mv-let (records st) (fn-lgw-run c st0 (slw-unit) (slw-max))
       (and (equal records (list (slw-rec 1) (slw-rec 2) (slw-rec 3)))
            (equal records (fn-lgk-committed ks))
            (equal walked records)
            (equal stw st)
            (equal (fn-lgw-kernel st) (fn-lgc-of ks))
            (equal (fn-lgw-count st) 3)
            (equal (fn-lgw-next st) 4)
            (equal (fn-lgw-pos st) (len (slw-log3)))
            (equal (fn-lgw-prev st) (slw-t3))
            (fn-lgw-stop st)
            (not (fn-lgw-broken st))
            (not (fn-lgs-chain-broken-p c *fn-lg-genesis* (slw-unit) (slw-max)))
            (not (member-equal (slw-rec 1) st)))))))

; (1) The whole-segment open over the same octets as a string gives the same
; records and kernel (fn-lgw-run-is-fn-lgc-open's two sides).
(defun slw-chars (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (code-char (if (and (natp (car xs)) (< (car xs) 256)) (car xs) 0))
            (slw-chars (cdr xs)))
    nil))
(assert-event
 (let ((s (coerce (slw-chars (slw-seg)) 'string)))
   (mv-let (records st) (fn-lgw-run (fn-lgd-octets s) (fn-lgw-start *fn-lg-genesis* 1)
                                    (slw-unit) (slw-max))
     (mv-let (r2 c2) (fn-lgc-open s *fn-lg-genesis* (slw-unit) (slw-max) 1)
       (and (equal records r2) (equal (fn-lgw-kernel st) c2)
            (equal (len records) 3))))))

; (1) One step, as the host takes it: the header window names the first
; entry's length, and the step over that window takes that entry's records
; (record 1 first; one entry may carry a batch, PKT-749).
(assert-event
 (let* ((c (slw-seg)) (st0 (fn-lgw-start *fn-lg-genesis* 1))
        (n (fn-lgw-entry-len (fn-bs-take (fn-lgw-header-len st0 (len c)) c) st0 (len c))))
   (mv-let (took records st1) (fn-lgw-step (fn-bs-take n c) st0 (slw-unit) (slw-max) (len c))
     (and (natp n)
          (equal (fn-bs-take n c) (fn-lg-slice c))
          (equal took t)
          (consp records)
          (equal (car records) (slw-rec 1))
          (equal records (fn-lg-slice-records (fn-lg-slice c) (slw-max)))
          (equal (fn-lgw-count st1) (len records))
          (equal (mod (fn-lgw-pos st1) (slw-unit)) 0)))))

; (1) A batch entry: one step takes all three records; the run, the scan
; and the counts agree.
(assert-event
 (let* ((c (slw-batch)) (ks (slw-recover c)))
   (mv-let (records st) (fn-lgw-run c (fn-lgw-start *fn-lg-genesis* 1) (slw-unit) (slw-max))
     (and (equal records (list (slw-rec 1) (slw-rec 2) (slw-rec 3)))
          (equal records (fn-lgk-committed ks))
          (equal (fn-lgw-kernel st) (fn-lgc-of ks))
          (equal (fn-lgw-count st) 3)
          (equal (fn-lgw-next st) 4)
          (fn-lgw-stop st)
          (not (fn-lgw-broken st))))))

; (2) The torn tail: two records, the frontier at the second entry's end,
; not broken; the scan says the same.
(assert-event
 (let* ((c (slw-torn)) (ks (slw-recover c)))
   (mv-let (records st) (fn-lgw-run c (fn-lgw-start *fn-lg-genesis* 1) (slw-unit) (slw-max))
     (and (equal records (list (slw-rec 1) (slw-rec 2)))
          (equal records (fn-lgk-committed ks))
          (equal (fn-lgw-kernel st) (fn-lgc-of ks))
          (equal (fn-lgw-pos st)
                 (+ (len (fn-lg-log (list (slw-rec 1)) *fn-lg-genesis* (slw-unit)))
                    (len (fn-lg-log (list (slw-rec 2)) (slw-t1) (slw-unit)))))
          (fn-lgw-stop st)
          (not (fn-lgw-broken st))))))

; (2) The splice: one record, then BROKEN, and fn-lgs-chain-broken-p agrees.
(assert-event
 (let ((c (slw-splice)))
   (mv-let (records st) (fn-lgw-run c (fn-lgw-start *fn-lg-genesis* 1) (slw-unit) (slw-max))
     (and (equal records (list (slw-rec 1)))
          (fn-lgw-stop st)
          (equal (fn-lgw-broken st) t)
          (fn-lgs-chain-broken-p c *fn-lg-genesis* (slw-unit) (slw-max))))))

; (3) fn-lgw-run-is-the-scan without (not (fn-lgw-stop st)): a stopped stream
; at POS 0 (inside the segment: the retained hypothesis holds) emits nothing,
; while the scan from its predecessor reads three records.
(assert-event
 (let* ((c (slw-seg))
        (st (fn-lgw-make 0 *fn-lg-genesis* 0 1 t nil))
        (scan (car (fn-lg-scan c *fn-lg-genesis* (slw-unit) (slw-max)))))
   (mv-let (records st2) (fn-lgw-run c st (slw-unit) (slw-max))
     (declare (ignore st2))
     (and (fn-lgw-stop st)
          (<= (fn-lgw-pos st) (len c))
          (equal records nil)
          (equal (len scan) 3)
          (not (equal records scan))))))

; (4) CORRUPTED STATE: a stream started from another predecessor (record 7's
; trailer, not the genesis the segment is chained from) reads no record and
; reports the splice at offset 0.
(assert-event
 (let ((c (slw-seg))
       (other (fn-lg-last-trailer (list (slw-rec 7)) *fn-lg-genesis*)))
   (mv-let (records st) (fn-lgw-run c (fn-lgw-start other 1) (slw-unit) (slw-max))
     (and (equal records nil)
          (equal (fn-lgw-pos st) 0)
          (equal (fn-lgw-broken st) t)))))
