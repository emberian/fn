; fn's first durable BP-node record: the creation-sequence frontier.
;
; This is intentionally smaller than the bundle-store machine designed in
; specs/bp-design.md section 1.5.  It gives the host one completed vertical
; rule now: reserve a sequence in ACL2, make its FNBS frame in ACL2, persist
; that frame, and only then author a bundle with the reserved sequence.  The
; bundle lifecycle, constraints and fn-bpn-step remain open.

(in-package "ACL2")

(include-book "frame-trailer")
(include-book "bp-primary")

; A frontier is the NEXT value to allocate.  It is a u64 because the FNBS
; :nat field grammar is a fixed eight-byte unsigned integer.
(defun fn-bpn-sequence-frontierp (n)
  (declare (xargs :guard t))
  (and (fn-bpp-timep n) (fn-frame-natp n)))

(defun fn-bpn-sequence-record (next)
  (declare (xargs :guard (fn-bpn-sequence-frontierp next)))
  (list :bpn-sequence next))

(defun fn-bpn-sequence-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record)
       (equal (len record) 2)
       (equal (car record) :bpn-sequence)
       (fn-bpn-sequence-frontierp (cadr record))))

(verify-guards fn-bpn-sequence-frontierp)
(verify-guards fn-bpn-sequence-record)
(verify-guards fn-bpn-sequence-recordp)

; The returned record carries the next frontier, not the allocated value.  It
; must become durable before `sequence' can be passed to fn-bpn-send.
(defun fn-bpn-sequence-reserve (frontier)
  (declare (xargs :guard (fn-bpn-sequence-frontierp frontier)))
  (if (equal frontier *fn-bpc-max-uint*)
      (list :refused :sequence-exhausted)
    (list :reserved frontier (fn-bpn-sequence-record (+ 1 frontier)))))

(defun fn-bpn-sequence-reservationp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 3) (equal (car r) :reserved)
       (fn-bpn-sequence-frontierp (cadr r))
       (fn-bpn-sequence-recordp (caddr r))
       (equal (cadr (caddr r)) (+ 1 (cadr r)))))

(defun fn-bpn-sequence-reservation-sequence (r)
  (declare (xargs :guard (fn-bpn-sequence-reservationp r)))
  (cadr r))

(defun fn-bpn-sequence-reservation-record (r)
  (declare (xargs :guard (fn-bpn-sequence-reservationp r)))
  (caddr r))

(verify-guards fn-bpn-sequence-reserve)
(verify-guards fn-bpn-sequence-reservationp)
(verify-guards fn-bpn-sequence-reservation-sequence)
(verify-guards fn-bpn-sequence-reservation-record)

; The concrete record is framed and trailed wholly by ACL2.  A host copies the
; resulting octets to a staged inode, replaces the frontier name and barriers
; its directory; it never serializes the record or computes its digest.
(defun fn-bpn-sequence-record-frame (record)
  (declare (xargs :guard (fn-bpn-sequence-recordp record)))
  (let ((protected (fn-frame-bundle-store-protected :sequence
                                                    (list (cadr record)))))
    (append protected (fn-frame-trailer protected))))

(defun fn-bpn-sequence-frame-limit ()
  (declare (xargs :guard t))
  (+ *fn-frame-header-octets* *fn-frame-max-bundle-store-payload*
     *fn-frame-trailer-octets*))

(defun fn-bpn-sequence-record-unframe (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (let ((answer (fn-frame-bundle-store-decode
                 octets
                 (fn-frame-trailer (fn-frame-protected-prefix octets)))))
    (if (and (fn-frame-result-okp answer)
             (equal (fn-frame-result-kind answer) :sequence)
             (true-listp (fn-frame-result-payload answer))
             (equal (len (fn-frame-result-payload answer)) 1))
        (let ((record (fn-bpn-sequence-record
                       (car (fn-frame-result-payload answer)))))
          (if (fn-bpn-sequence-recordp record) record nil))
      nil)))

(verify-guards fn-bpn-sequence-record-frame)
(verify-guards fn-bpn-sequence-record-unframe)

; Recovery is intentionally conservative: an absent frontier is fresh only
; while the host is establishing a newly durable sequence namespace.  Once the
; namespace has existed, absence and malformed bytes are separate faults,
; never resets that could reuse an old sequence.
(defun fn-bpn-sequence-recover (octets presentp freshp)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (not presentp)
      (if freshp (list :ready 0) (list :fault :sequence-frontier-missing))
    (let ((record (fn-bpn-sequence-record-unframe octets)))
      (if (fn-bpn-sequence-recordp record)
          (list :ready (cadr record))
        (list :fault :sequence-frontier)))))

(defun fn-bpn-sequence-recovery-readyp (answer)
  (declare (xargs :guard t))
  (and (true-listp answer) (equal (len answer) 2)
       (equal (car answer) :ready)
       (fn-bpn-sequence-frontierp (cadr answer))))

(defun fn-bpn-sequence-recovery-frontier (answer)
  (declare (xargs :guard (fn-bpn-sequence-recovery-readyp answer)))
  (cadr answer))

(verify-guards fn-bpn-sequence-recover)
(verify-guards fn-bpn-sequence-recovery-readyp)
(verify-guards fn-bpn-sequence-recovery-frontier)

; Keystone: a non-exhausted frontier produces exactly that sequence and a
; record for its successor.  This is the transition the native host calls.
(defthm fn-bpn-sequence-reserve-advances-frontier
  (implies (and (fn-bpn-sequence-frontierp frontier)
                (not (equal frontier *fn-bpc-max-uint*)))
           (and (fn-bpn-sequence-reservationp
                 (fn-bpn-sequence-reserve frontier))
                (equal (fn-bpn-sequence-reservation-sequence
                        (fn-bpn-sequence-reserve frontier))
                       frontier)
                (equal (cadr (fn-bpn-sequence-reservation-record
                              (fn-bpn-sequence-reserve frontier)))
                       (+ 1 frontier))))
  :hints (("Goal" :in-theory (enable fn-bpn-sequence-reserve
                                      fn-bpn-sequence-reservationp
                                      fn-bpn-sequence-recordp
                                      fn-bpn-sequence-frontierp))))

(defthm fn-bpn-sequence-recover-of-record-frame
  (implies (fn-bpn-sequence-recordp record)
           (equal (fn-bpn-sequence-recover (fn-bpn-sequence-record-frame record) t nil)
                  (list :ready (cadr record))))
  :hints (("Goal" :in-theory (enable fn-bpn-sequence-recover
                                      fn-bpn-sequence-record-unframe
                                      fn-bpn-sequence-record-frame
                                      fn-bpn-sequence-recordp))))

(deftheory fn-bpn-records-vocabulary
  '((:d fn-bpn-sequence-frontierp) (:d fn-bpn-sequence-record)
    (:d fn-bpn-sequence-recordp) (:d fn-bpn-sequence-reserve)
    (:d fn-bpn-sequence-reservationp) (:d fn-bpn-sequence-record-frame)
    (:d fn-bpn-sequence-record-unframe) (:d fn-bpn-sequence-recover)
    (:d fn-bpn-sequence-recovery-readyp)))

(in-theory (disable fn-bpn-records-vocabulary))
