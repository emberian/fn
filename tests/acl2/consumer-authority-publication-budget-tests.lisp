; Literal planned resource-gate teeth. These must execute in a matching
; budget/Store world before source qualification; no allocation grant follows.
(in-package "ACL2")
(include-book "../../books/consumer-publication-budget")
(defconst *capbt-profile* (fn-bs-config-for-profile :development))
(defconst *capbt-carry* (fn-pvc-make *capbt-profile*))
(defconst *capbt-v* (fn-bs-profile-admittedp *capbt-profile*))
(defconst *capbt-h* (fn-bs-profile-max-history-octets *capbt-profile*))
(defconst *capbt-begin* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *capbt-row*
 (list :consumer-authority 1 2 0
  (list :authority-row (make-list 64 :initial-element 65) 0
        (make-list 64 :initial-element 97) 2
        (make-list 32 :initial-element 9) (make-list 16 :initial-element 8)
        (make-list 32 :initial-element 9) (make-list 32 :initial-element 9)
        (make-list 32 :initial-element 9) 1)))
;@positive fn-cpb-authority-charge-is-persisted-row-octets
(assert-event
 (and (fn-cac-eventp *capbt-begin*) (fn-cac-eventp *capbt-row*)
      (equal (fn-cac-event-charge *capbt-begin*) 49)
      (equal (fn-cac-event-charge *capbt-row*) 321)
      (equal (fn-cac-event-charge *capbt-begin*) (fn-sbud-row-octets *capbt-begin*))
      (equal (fn-cac-event-charge *capbt-row*) (fn-sbud-row-octets *capbt-row*))
      (equal (fn-cac-event-charge *capbt-row*) (len (fn-store-event-encode *capbt-row*)))))
;@hypothesis-removal fn-cpb-authority-charge-is-persisted-row-octets authority-event
(assert-event
 (let ((consumer (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
  (and (not (fn-cac-eventp consumer)) (fn-cpe-eventp consumer)
       (not (equal (fn-cac-event-charge consumer) (fn-sbud-row-octets consumer))))))
;@positive fn-cpb-authority-admission-keeps-actual-row-and-release-headroom
(assert-event
 (and (equal (fn-cpb-authority-event-verdict-carried *capbt-carry* *capbt-profile*
                  10 100000 1 *capbt-row*) :admissible)
      (fn-cac-eventp *capbt-row*) (posp (fn-sbud-row-octets *capbt-row*))
      (fn-pvc-history-admissiblep (fn-pvc-admittedp *capbt-carry* *capbt-profile*)
                                  *capbt-profile* 100000 (fn-sbud-row-octets *capbt-row*))
      (fn-pvc-roomp (fn-pvc-admittedp *capbt-carry* *capbt-profile*) *capbt-profile*
                    11 (+ 100000 (fn-sbud-row-octets *capbt-row*))
                    (fn-cvec-debt-step :consumer-authority 1))))
;@hypothesis-removal fn-cpb-authority-admission-keeps-actual-row-and-release-headroom admission
(assert-event
 (and (not (equal (fn-cpb-authority-event-verdict-carried *capbt-carry* *capbt-profile*
                       10 *capbt-h* 0 *capbt-row*) :admissible))
      (fn-cac-eventp *capbt-row*) (posp (fn-sbud-row-octets *capbt-row*))
      (not (fn-pvc-history-admissiblep
            (fn-pvc-admittedp *capbt-carry* *capbt-profile*) *capbt-profile*
            *capbt-h* (fn-sbud-row-octets *capbt-row*)))))
; Exact small FNCE row admits where the inherited fixed512 estimate refuses.
(assert-event
 (let* ((charge (fn-cac-event-charge *capbt-begin*))
        (bytes (- *capbt-h* (+ charge (fn-smr-reserve-octets)))))
  (and (natp bytes) (fn-cac-eventp *capbt-begin*) (equal charge 49)
       (equal (fn-pvc-verdict-carried *capbt-carry* *capbt-profile*
                                      :consumer 10 bytes 0) :unaffordable)
       (equal (fn-cpb-authority-event-verdict-carried *capbt-carry* *capbt-profile*
                                                      10 bytes 0 *capbt-begin*) :admissible)
       (fn-pvc-roomp *capbt-v* *capbt-profile* 11 (+ bytes charge) 0))))
; A history-only fit does not cover pending maintenance/release debt.
(assert-event
 (let ((bytes (- *capbt-h* 321)))
  (and (fn-pvc-history-admissiblep *capbt-v* *capbt-profile* bytes 321)
       (not (fn-pvc-roomp *capbt-v* *capbt-profile* 11 *capbt-h* 1))
       (equal (fn-cpb-authority-event-verdict-carried *capbt-carry* *capbt-profile*
                                                      10 bytes 1 *capbt-row*) :unaffordable))))
; Current CPE gate intentionally stays separate; malformed FNCE never gains a charge.
(assert-event
 (and (equal (fn-cpb-event-verdict-carried *capbt-carry* *capbt-profile*
                                          10 100000 1 *capbt-row*) :unaffordable)
      (not (fn-cac-eventp '(:consumer-authority 1 2 0 (:authority-row))))
      (equal (fn-cpb-authority-event-verdict-carried *capbt-carry* *capbt-profile*
             10 100000 1 '(:consumer-authority 1 2 0 (:authority-row))) :unaffordable)))
