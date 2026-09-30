; Literal actual-charge/headroom witnesses. No host or durable completion
; verdict is implied by a standalone admission decision.
(in-package "ACL2")
(include-book "../../books/consumer-publication-budget")

(defconst *cpbt-profile* (fn-bs-config-for-profile :development))
(defconst *cpbt-carry* (fn-pvc-make *cpbt-profile*))
(defconst *cpbt-v* (fn-bs-profile-admittedp *cpbt-profile*))
(defconst *cpbt-h*
  (fn-bs-profile-max-history-octets *cpbt-profile*))
(defconst *cpbt-r*
  (fn-bs-profile-max-record-octets *cpbt-profile*))

; Complete positive antecedent and conclusion, nonempty larger-than512 event
; and a live release debt. Scope: consumer publication consumes one record
; and its actual bytes, then retains the original release reservation.
(assert-event
 (and (fn-pvc-carryp *cpbt-carry*) *cpbt-v*
      (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                    10 100000 1 1024) :admissible)
      (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                    10 100000 1 1024)
             (fn-cpb-verdict-at *cpbt-v* *cpbt-profile* 10 100000 1 1024))
      (natp 10) (natp 100000) (natp 1) (posp 1024)
      (<= 1024 *cpbt-r*)
      (fn-pvc-history-admissiblep *cpbt-v* *cpbt-profile* 100000 1024)
      (fn-pvc-roomp *cpbt-v* *cpbt-profile* 11 101024
                    (fn-cvec-debt-step :consumer 1))))

; An old 512-byte reservation admits this history coordinate, but this
; event's actual charge cannot fit. The rejection precedes frontier use.
(assert-event
 (let ((bytes (- *cpbt-h* (+ 512 (fn-smr-reserve-octets)))))
   (and (natp bytes)
        (equal (fn-pvc-verdict-carried *cpbt-carry* *cpbt-profile*
                                       :consumer 10 bytes 0) :admissible)
        (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                       10 bytes 0 1024) :unaffordable))))

; The actual event fits H, but its release debt would no longer fit. This
; affirmative case distinguishes admission from an H-only capacity check.
(assert-event
 (let ((bytes (- *cpbt-h* 1024)))
   (and (fn-pvc-history-admissiblep *cpbt-v* *cpbt-profile* bytes 1024)
        (not (fn-pvc-roomp *cpbt-v* *cpbt-profile* 11 *cpbt-h* 1))
        (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                       10 bytes 1 1024) :unaffordable))))

(assert-event
 (and (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                    10 100000 0 (+ 1 *cpbt-r*)) :unaffordable)
      (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                    10 100000 0 0) :unaffordable)
      (equal (fn-cpb-verdict-carried *cpbt-carry* *cpbt-profile*
                                    -1 100000 0 1024) :unaffordable)))
