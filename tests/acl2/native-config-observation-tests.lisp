; Executable witnesses and teeth for configuration-history namespace recovery.
(in-package "ACL2")
(include-book "../../books/native-config-observation")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; The pre-D27 listing bound (8192): every witness below that predates the
; profile runs at this instance of the operator's `max-config-generations'.
(defconst *ncot-old* 8192)

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
 (equal (fn-nco-observe *fn-nco-test-good* *ncot-old*)
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
         (fn-nco-observe (list (list "00000002.cfg" *fn-nco-test-record-1*)) *ncot-old*))
        :namespace))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (list (list "00000001.cfg" *fn-nco-test-record-1*)
                               (list "00000003.cfg" *fn-nco-test-record-3*)) *ncot-old*))
        :namespace))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (list (list "00000001.cfg" *fn-nco-test-record-1*)
                               (list "other.cfg" *fn-nco-test-record-1*)) *ncot-old*))
        :namespace))
(assert-event
 (equal (fn-nco-observe (list (list "malformed-name.cfg" *fn-nco-test-record-1*)) *ncot-old*)
        (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-observe (list (list "00000002.cfg" *fn-nco-test-record-1*)) *ncot-old*)
        (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-result-reason (fn-nco-observe (list (list "bad.cfg" '(255))) *ncot-old*))
        :decode))
(assert-event
 (equal (fn-nco-observe nil *ncot-old*) (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-result-reason
         (fn-nco-observe (make-list (+ 1 *ncot-old*)
                                    :initial-element nil) *ncot-old*))
        :budget))

; Fresh initialization differs from recovery only for the exactly empty list.
(assert-event (equal (fn-nco-observe-initial nil *ncot-old*) (list :ok nil nil)))
(assert-event (equal (fn-nco-observe nil *ncot-old*) (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-observe-initial *fn-nco-test-good* *ncot-old*)
        (fn-nco-observe *fn-nco-test-good* *ncot-old*)))
(assert-event
 (equal (fn-nco-observe-initial
         (list (list "00000002.cfg" *fn-nco-test-record-1*)) *ncot-old*)
        (list :fault :namespace nil)))
(assert-event
 (equal (fn-nco-observe-initial 'malformed *ncot-old*) (list :fault :budget nil)))

; D27, PRF-102: the bound is the operator's.  The three-generation history is
; accepted exactly when the profile's max-config-generations is at least 3,
; and refused for its size, by :budget, one below.
(assert-event (equal (fn-nco-result-status (fn-nco-observe *fn-nco-test-good* 3)) :ok))
(assert-event (equal (fn-nco-result-reason (fn-nco-observe *fn-nco-test-good* 2)) :budget))
(assert-event (equal (fn-nco-result-reason (fn-nco-observe-initial *fn-nco-test-good* 2))
                     :budget))
; Above the old cap: 8193 entries pass the size gate under the default
; profile's 2^20 (they fail later, by :decode, for their content), while the
; pre-D27 figure refused them for their number.
(defconst *ncot-above-old-cap* (make-list 8193 :initial-element (list "x.cfg" '(255))))
(assert-event
 (equal (fn-nco-result-reason (fn-nco-observe *ncot-above-old-cap* 1048576)) :decode))
(assert-event
 (equal (fn-nco-result-reason (fn-nco-observe *ncot-above-old-cap* *ncot-old*)) :budget))
; The keystone's hypothesis is needed: a value that is not a proper list is
; refused by :budget under any bound, though its LEN is 0.
(must-fail
 (defthm ncot-refusal-without-true-listp
   (iff (equal (fn-nco-result-reason (fn-nco-observe 'malformed 5)) :budget)
        (< (nfix 5) (len 'malformed)))
   :rule-classes nil))
