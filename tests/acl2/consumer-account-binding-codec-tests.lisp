(in-package "ACL2")
(include-book "../../books/consumer-account-binding-codec-invariants")

(defconst *fn-cab-test-bind*
 (list :consumer-authority 7 11 3
       (fn-cab-operation '(99) 5 '(97) 0 2 (make-list 32 :initial-element 9))))
(defconst *fn-cab-test-delete*
 (list :consumer-authority 8 12 3
       (fn-cab-operation '(99) 5 '(97) 0 1 *fn-cab-zero-principal*)))
(defconst *fn-cab-test-preserve*
 (list :consumer-authority 9 13 3
       (fn-cab-operation '(99) 5 '(97) 1 0 *fn-cab-zero-principal*)))
(defconst *fn-cab-test-tombstone*
 (list :consumer-authority 10 14 3
       (fn-cab-operation '(99) 5 '(97) 2 1 *fn-cab-zero-principal*)))
(defconst *fn-cab-test-wide*
 (list :consumer-authority *fn-cbor-max-uint64* *fn-cbor-max-uint64* *fn-cbor-max-uint64*
       (fn-cab-operation (make-list 64 :initial-element 255) *fn-cbor-max-uint64*
                         (make-list 64 :initial-element 255) 0 2
                         (make-list 32 :initial-element 255))))
(defconst *fn-cab-test-v2*
 (list :consumer-authority 1 2 3 (list :authority-begin '(99) 0 1 0)))

; Literal complete hypotheses and conclusions for all four legal decisions.
(assert-event
 (and (fn-cab-eventp *fn-cab-test-bind*)
      (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-bind*)) (list :ok *fn-cab-test-bind*))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-bind*))
      (equal (fn-cab-event-charge *fn-cab-test-bind*) (len (fn-cab-encode *fn-cab-test-bind*)))
      (<= (len (fn-cab-encode *fn-cab-test-bind*)) (fn-cab-octet-ceiling))))
(assert-event
 (and (fn-cab-eventp *fn-cab-test-delete*)
      (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-delete*)) (list :ok *fn-cab-test-delete*))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-delete*))
      (equal (fn-cab-event-charge *fn-cab-test-delete*) (len (fn-cab-encode *fn-cab-test-delete*)))
      (<= (len (fn-cab-encode *fn-cab-test-delete*)) (fn-cab-octet-ceiling))))
(assert-event
 (and (fn-cab-eventp *fn-cab-test-preserve*)
      (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-preserve*)) (list :ok *fn-cab-test-preserve*))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-preserve*))
      (equal (fn-cab-event-charge *fn-cab-test-preserve*) (len (fn-cab-encode *fn-cab-test-preserve*)))
      (<= (len (fn-cab-encode *fn-cab-test-preserve*)) (fn-cab-octet-ceiling))))
(assert-event
 (and (fn-cab-eventp *fn-cab-test-tombstone*)
      (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-tombstone*)) (list :ok *fn-cab-test-tombstone*))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-tombstone*))
      (equal (fn-cab-event-charge *fn-cab-test-tombstone*) (len (fn-cab-encode *fn-cab-test-tombstone*)))
      (<= (len (fn-cab-encode *fn-cab-test-tombstone*)) (fn-cab-octet-ceiling))))
(assert-event
 (and (fn-cab-eventp *fn-cab-test-wide*)
      (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-wide*)) (list :ok *fn-cab-test-wide*))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-wide*))
      (equal (fn-cab-event-charge *fn-cab-test-wide*) (len (fn-cab-encode *fn-cab-test-wide*)))
      (<= (len (fn-cab-encode *fn-cab-test-wide*)) (fn-cab-octet-ceiling))))
(assert-event (and (equal (fn-cab-octet-ceiling) 202)
                   (equal (len (fn-cab-encode *fn-cab-test-wide*)) 202)))
; Removing the sole eventp premise breaks the universal inverse.
(assert-event
 (and (fn-cac-eventp *fn-cab-test-v2*)
      (not (fn-cab-eventp *fn-cab-test-v2*))
      (not (equal (fn-cab-decode-exact (fn-cab-encode *fn-cab-test-v2*))
                  (list :ok *fn-cab-test-v2*)))
      (fn-cbor-octet-listp (fn-cab-encode *fn-cab-test-v2*))
      (equal (fn-cab-event-charge *fn-cab-test-v2*) (len (fn-cab-encode *fn-cab-test-v2*)))
      (<= (len (fn-cab-encode *fn-cab-test-v2*)) (fn-cab-octet-ceiling))))
(assert-event (not (fn-cac-eventp *fn-cab-test-bind*)))
(assert-event (equal (car (fn-cab-decode-exact (fn-cac-encode *fn-cab-test-v2*))) :error))
(assert-event (equal (car (fn-cac-decode-exact (fn-cab-encode *fn-cab-test-bind*))) :error))
; Rejected decision matrix and noncanonical placeholders.
(assert-event
 (and (not (fn-cab-decisionp 0 0 *fn-cab-zero-principal*))
      (not (fn-cab-decisionp 1 2 *fn-cab-zero-principal*))
      (not (fn-cab-decisionp 2 0 *fn-cab-zero-principal*))
      (not (fn-cab-decisionp 3 1 *fn-cab-zero-principal*))
      (not (fn-cab-decisionp 1 0 (make-list 32 :initial-element 1)))
      (not (fn-cab-decisionp 0 1 (make-list 32 :initial-element 1)))))
(defun fn-cab-test-prefixes (n bytes)
 (declare (xargs :guard (natp n) :measure (nfix n)))
 (if (zp n) (equal (car (fn-cab-decode-exact nil)) :error)
   (and (equal (car (fn-cab-decode-exact (ec-call (take (- n 1) bytes)))) :error)
        (fn-cab-test-prefixes (- n 1) bytes))))
(assert-event (fn-cab-test-prefixes (len (fn-cab-encode *fn-cab-test-bind*))
                                    (fn-cab-encode *fn-cab-test-bind*)))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 4 2 (fn-cab-encode *fn-cab-test-bind*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 5 6 (fn-cab-encode *fn-cab-test-bind*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 30 0 (fn-cab-encode *fn-cab-test-bind*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 42 3 (fn-cab-encode *fn-cab-test-bind*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 43 0 (fn-cab-encode *fn-cab-test-bind*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (update-nth 44 1 (fn-cab-encode *fn-cab-test-delete*)))) :error))
(assert-event (equal (car (fn-cab-decode-exact
 (append (fn-cab-encode *fn-cab-test-bind*) '(0)))) :error))
(assert-event (equal (car (fn-cab-decode-exact (make-list 203 :initial-element 0))) :error))
(assert-event (equal (car (fn-cab-decode-exact '(300))) :error))
(assert-event (equal (car (fn-cab-decode-exact '(102 . 1))) :error))
