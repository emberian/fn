; Exact durable account row/fence codec teeth. No native authority activated.
(in-package "ACL2")
(include-book "../../books/consumer-authority-codec")

(defconst *fn-cac-test-32* (make-list 32 :initial-element 255))
(defconst *fn-cac-test-16* (make-list 16 :initial-element 254))
(defconst *fn-cac-test-name* (make-list 64 :initial-element 253))
(defconst *fn-cac-test-row*
  (list :consumer-authority *fn-cbor-max-uint64* 4294967296 4294967297
        (list :authority-row *fn-cac-test-name* 4294967298 *fn-cac-test-name*
              *fn-cbor-max-uint64* *fn-cac-test-32* *fn-cac-test-16*
              *fn-cac-test-32* *fn-cac-test-32* *fn-cac-test-32* 1)))

;@positive fn-cac-decode-after-encode-is-the-complete-event
(assert-event
 (and (fn-cac-eventp *fn-cac-test-row*)
      (equal (fn-cac-decode-exact (fn-cac-encode *fn-cac-test-row*))
             (list :ok *fn-cac-test-row*))))

;@positive fn-cac-event-charge-is-exact-encoding
(assert-event
 (equal (fn-cac-event-charge *fn-cac-test-row*)
        (len (fn-cac-encode *fn-cac-test-row*))))

;@positive fn-cac-event-charge-fits-derived-row-bound
(assert-event
 (and (equal (fn-cac-event-charge *fn-cac-test-row*) 321)
      (<= (fn-cac-event-charge *fn-cac-test-row*) 321)))

;@hypothesis-removal fn-cac-decode-after-encode-is-the-complete-event fn-cac-eventp
(assert-event
 (let ((invalid '(:consumer-authority 0 0 0 (:authority-row (97) 0 (97) 0))))
   (and (not (fn-cac-eventp invalid))
        (not (equal (fn-cac-decode-exact (fn-cac-encode invalid))
                    (list :ok invalid))))))

; The two unconditional charge properties have no hypotheses to remove.
;@mutation fn-cac-event-charge-is-exact-encoding
(assert-event
 (and (fn-cac-eventp *fn-cac-test-row*)
      (not (equal (fn-cac-event-charge *fn-cac-test-row*) 512))))

; All staged lifecycle arms, including deletion and scalar fence. No whole
; adopted table is present in either the begin or fence row.
(assert-event
 (let ((op '(:authority-begin (65) 4294967296 4294967297 7)))
   (let ((e (list :consumer-authority 3 4294967296 2 op)))
     (and (fn-cac-operationp op) (fn-cac-eventp e)
          (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e))))))

(assert-event
 (let ((e '(:consumer-authority 4 4294967297 2
            (:authority-tombstone (65) 4294967296 (97 98) 4294967296))))
   (and (fn-cac-eventp e)
        (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e)))))

(assert-event
 (let ((e (list :consumer-authority 5 4294967298 2
                (list :authority-fence '(65) 4294967296 4294967297 *fn-cac-test-32*))))
   (and (fn-cac-eventp e)
        (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e)))))

(assert-event
 (let ((e '(:consumer-authority 6 4294967299 2 (:authority-discard (65) 4294967296))))
   (and (fn-cac-eventp e)
        (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e)))))

; Malformed/truncated/trailing/version input refuses. The byte budget comes
; from the structural row bound; arbitrary tables use many charged rows.
(assert-event
 (and (not (eq (car (fn-cac-decode-exact (append (fn-cac-encode *fn-cac-test-row*) '(0)))) :ok))
      (not (eq (car (fn-cac-decode-exact (take 320 (fn-cac-encode *fn-cac-test-row*)))) :ok))
      (not (eq (car (fn-cac-decode-exact '(102 110 99 101 1 0))) :ok))
      (not (fn-cac-eventp
             '(:consumer-authority 18446744073709551616 0 0
               (:authority-discard (65) 0))))
      (not (fn-cac-operationp '(:authority-begin (65) 0 1 8)))))

; Direct positive parser anchor and both resumable lifecycle wire arms.
(defconst *fn-cac-test-begin-op* '(:authority-begin (65) 0 1 7))
(assert-event (fn-cac-operationp *fn-cac-test-begin-op*))
(assert-event
 (let ((e (list :consumer-authority 7 4294967300 2
                (list :authority-seal '(65) 4294967296 4294967297 *fn-cac-test-32*))))
   (and (fn-cac-eventp e)
        (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e)))))
(assert-event
 (let ((e '(:consumer-authority 8 4294967301 2 (:authority-prepare (65) 4294967296))))
   (and (fn-cac-eventp e)
        (equal (fn-cac-decode-exact (fn-cac-encode e)) (list :ok e)))))
