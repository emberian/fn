; ACL2-owned durable identity and publication authorization for a bundle this
; node authors.  The host has already made the reservation's successor FNBS
; frontier durable before it calls this operation.  This book neither writes
; that mutable frontier nor interprets filesystem results; journal-publish owns
; the immutable no-replace phase machine used for the exact name below.
(in-package "ACL2")

(include-book "bp-node")
(include-book "bp-node-records")
(include-book "byte-store-txn-name")
(include-book "journal-publish")

(defconst *fn-bpn-authored-wire-prefix*
  '(#\a #\u #\t #\h #\o #\r #\e #\d #\-))
(defconst *fn-bpn-authored-wire-suffix*
  '(#\. #\w #\i #\r #\e))

; Reuse the transaction-name book's proved decimal renderer, without its
; transaction padding or suffix.  This preserves the deployed spelling
; `authored-N.wire' while leaving decimal conversion with one implementation.
(defun fn-bpn-authored-wire-name-chars (sequence)
  (declare (xargs :guard t))
  (append *fn-bpn-authored-wire-prefix*
          (fn-bs-txn-natural-digits sequence)
          *fn-bpn-authored-wire-suffix*))

(defun fn-bpn-authored-wire-name-for-reservation (reservation)
  (declare (xargs :guard t))
  (if (fn-bpn-sequence-reservationp reservation)
      (fn-bpn-authored-wire-name-chars
       (fn-bpn-sequence-reservation-sequence reservation))
    nil))

; (:ok :authored-wire sequence name-chars wire publication).  NAME-CHARS and WIRE are the
; values the host must consume; it may not substitute the preview it observed.
(defun fn-bpn-authored-wire-operation (sequence name wire publication)
  (declare (xargs :guard t))
  (list :ok :authored-wire sequence name wire publication))

(defun fn-bpn-authored-wire-operationp (operation)
  (declare (xargs :guard t))
  (and (true-listp operation)
       (equal (len operation) 6)
       (equal (car operation) :ok)
       (equal (nth 1 operation) :authored-wire)
       (fn-bpn-sequence-frontierp (nth 2 operation))
       (equal (nth 3 operation)
              (fn-bpn-authored-wire-name-chars (nth 2 operation)))
       (fn-cbor-octet-listp (nth 4 operation))
       (equal (nth 5 operation) (fn-jpub-initial t))))

(defun fn-bpn-authored-wire-operation-label (operation)
  (declare (xargs :guard t))
  (nth 1 operation))

(defun fn-bpn-authored-wire-operation-sequence (operation)
  (declare (xargs :guard t))
  (nth 2 operation))

(defun fn-bpn-authored-wire-operation-name-chars (operation)
  (declare (xargs :guard t))
  (nth 3 operation))

(defun fn-bpn-authored-wire-operation-wire (operation)
  (declare (xargs :guard t))
  (nth 4 operation))

(defun fn-bpn-authored-wire-operation-publication (operation)
  (declare (xargs :guard t))
  (nth 5 operation))

; The shared spool lock serializes every BP journal user.  FINAL-ABSENT is an
; observation of the exact ACL2 preview made while that lock is held.  The
; reservation is the token returned by the ACL2 sequence allocator whose
; successor the host has already made durable.  A collision is not a retry:
; the reservation can never authorize replacement of existing evidence.
(defun fn-bpn-authored-wire-authorize
  (config peer adu reservation obs lock-owned final-absent)
  (declare (xargs :guard t))
  (if (and (fn-bpn-configp config)
           (fn-bpp-eidp peer)
           (fn-bpb-datap adu)
           (fn-bpn-sequence-reservationp reservation)
           (fn-clock-observationp obs)
           lock-owned
           final-absent)
      (let* ((sequence
              (fn-bpn-sequence-reservation-sequence reservation))
             (wire (fn-bpn-send config peer adu sequence obs)))
        (fn-bpn-authored-wire-operation
         sequence (fn-bpn-authored-wire-name-chars sequence) wire
         (fn-jpub-initial t)))
    (list :fault :authored-wire-authority)))

(defthm fn-bpn-authored-wire-authorize-carries-reservation
  (implies (and (fn-bpn-configp config)
                (fn-bpp-eidp peer)
                (fn-bpb-datap adu)
                (fn-bpn-sequence-reservationp reservation)
                (fn-clock-observationp obs)
                lock-owned
                final-absent)
           (let ((operation
                  (fn-bpn-authored-wire-authorize
                   config peer adu reservation obs lock-owned final-absent)))
             (and (fn-bpn-authored-wire-operationp operation)
                  (equal (fn-bpn-authored-wire-operation-sequence operation)
                         (fn-bpn-sequence-reservation-sequence reservation))
                  (equal (fn-bpn-authored-wire-operation-name-chars operation)
                         (fn-bpn-authored-wire-name-for-reservation reservation))
                  (equal (fn-bpn-authored-wire-operation-wire operation)
                         (fn-bpn-send
                          config peer adu
                          (fn-bpn-sequence-reservation-sequence reservation)
                          obs)))))
  :hints (("Goal" :in-theory
           (enable fn-bpn-authored-wire-authorize
                   fn-bpn-authored-wire-operation
                   fn-bpn-authored-wire-operationp
                   fn-bpn-authored-wire-operation-sequence
                   fn-bpn-authored-wire-operation-name-chars
                   fn-bpn-authored-wire-operation-wire
                   fn-bpn-authored-wire-name-for-reservation))))

(deftheory fn-bpn-authored-wire-vocabulary
  '((:d fn-bpn-authored-wire-name-chars)
    (:d fn-bpn-authored-wire-name-for-reservation)
    (:d fn-bpn-authored-wire-operation)
    (:d fn-bpn-authored-wire-operationp)
    (:d fn-bpn-authored-wire-authorize)))

(in-theory (disable fn-bpn-authored-wire-vocabulary))
