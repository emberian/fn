; Executable witnesses and teeth for configuration-history namespace recovery.
(in-package "ACL2")
(include-book "../../books/native-config-observation")

(defconst *fn-nco-test-record-1*
  (fn-cfg-encode (fn-cfg-record-make 0 0 1 (list (fn-cfg-set-capacity 1)) (fn-clock-observation 0 0 0 t))))
(defconst *fn-nco-test-record-2*
  (fn-cfg-encode (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-capacity 2)) (fn-clock-observation 1 1 0 t))))
(defconst *fn-nco-test-record-3*
  (fn-cfg-encode (fn-cfg-record-make 2 2 3 (list (fn-cfg-set-capacity 3)) (fn-clock-observation 2 2 0 t))))

(defconst *fn-nco-test-good*
  (list (list "00000003.cfg" *fn-nco-test-record-3*)
        (list "00000001.cfg" *fn-nco-test-record-1*)
        (list "00000002.cfg" *fn-nco-test-record-2*)))

; The separating accepted witness arrives in physical directory order opposite
; to its logical generation plan.  ACL2 sorts decoded generations and returns
; canonical name/octet bindings, so the raw adapter need not parse a decimal.
(assert-event
 (equal (fn-nco-observe *fn-nco-test-good*)
        (list :ok nil
              (list (list "00000001.cfg" *fn-nco-test-record-1*)
                    (list "00000002.cfg" *fn-nco-test-record-2*)
                    (list "00000003.cfg" *fn-nco-test-record-3*)))))

; This is a model witness, not a raw-host stub: a nonempty valid observation
; must produce the exact nonempty canonical output, and the sorter must retain
; every decoded source entry even when physical order is the reverse plan.
(assert-event
 (equal (fn-nco-sort-by-generation
         (fn-nco-decode-entries *fn-nco-test-good*))
        (list (fn-nco-decode-entry (list "00000001.cfg" *fn-nco-test-record-1*))
              (fn-nco-decode-entry (list "00000002.cfg" *fn-nco-test-record-2*))
              (fn-nco-decode-entry (list "00000003.cfg" *fn-nco-test-record-3*)))))

; The public helpers declare guard T.  These malformed logical calls exercise
; their total arithmetic projections rather than relying on the decoder as a
; hidden guard precondition.
(assert-event
 (equal (fn-nco-insert-by-generation 'bad (list 'worse))
        (list 'bad 'worse)))
(assert-event
 (not (fn-nco-canonical-contiguousp (list 'bad) 'not-a-generation)))

; Each tooth retains the observed input as a fault rather than silently taking
; a shorter prefix: name/record mismatch, an absent generation, duplicate
; generation, malformed entry, and resource exhaustion are distinct failures.
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (list (list "00000002.cfg" *fn-nco-test-record-1*))))
        :namespace))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (list (list "00000001.cfg" *fn-nco-test-record-1*)
                               (list "00000003.cfg" *fn-nco-test-record-3*))))
        :namespace))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (list (list "00000001.cfg" *fn-nco-test-record-1*)
                               (list "other.cfg" *fn-nco-test-record-1*))))
        :namespace))
(assert-event
 (equal (fn-nco-observe (list (list "malformed-name.cfg" *fn-nco-test-record-1*)))
        (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-observe (list (list "00000002.cfg" *fn-nco-test-record-1*)))
        (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-result-reason (fn-nco-observe (list (list "bad.cfg" '(255)))))
        :decode))
(assert-event
 (equal (fn-nco-observe nil) (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (make-list (+ 1 *fn-nco-max-config-observations*)
                                    :initial-element nil)))
        :budget))
