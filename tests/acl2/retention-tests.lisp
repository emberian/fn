; Executable scenarios for the finite-capacity retention ledger.
(in-package "ACL2")
(include-book "../../books/retention")

(defconst *retention-empty* (fn-retain-initial-state 10))
(assert-event (fn-retain-statep *retention-empty*))
(assert-event (equal (fn-retain-reserved *retention-empty*) 0))

; One archive pin reserves its own charge.
(defconst *retention-archive*
  (fn-retain-admit *retention-empty* "archive-1" "object-a" :archive
                   "operator-release-a" 6))
(assert-event (fn-retain-statep *retention-archive*))
(assert-event (equal (fn-retain-reserved *retention-archive*) 6))
(assert-event (equal (len (fn-retain-pins *retention-archive*)) 1))

; Capacity refusal leaves the whole ledger unchanged before it overcommits.
(assert-event
 (equal (fn-retain-admit *retention-archive* "forward-1" "object-a" :forward
                        "receipt-from-successor" 5)
        *retention-archive*))

; Two independent roots for the same immutable subject have independent charges.
(defconst *retention-two-pins*
  (fn-retain-admit *retention-archive* "forward-1" "object-a" :forward
                   "receipt-from-successor" 4))
(assert-event (fn-retain-statep *retention-two-pins*))
(assert-event (equal (fn-retain-reserved *retention-two-pins*) 10))
(assert-event (equal (len (fn-retain-pins *retention-two-pins*)) 2))

; A successor receipt cannot discharge the archive pin, and wrong subject or
; evidence cannot discharge the forwarding pin.
(assert-event
 (equal (fn-retain-release *retention-two-pins* "archive-1" "object-a" :archive
                          "receipt-from-successor")
        *retention-two-pins*))
(assert-event
 (equal (fn-retain-release *retention-two-pins* "forward-1" "object-b" :forward
                          "receipt-from-successor")
        *retention-two-pins*))
(assert-event
 (equal (fn-retain-release *retention-two-pins* "forward-1" "object-a" :forward
                          "stale-or-unauthorized")
        *retention-two-pins*))

; A matching forwarding receipt frees only its allocation and records release.
(defconst *retention-forward-released*
  (fn-retain-release *retention-two-pins* "forward-1" "object-a" :forward
                     "receipt-from-successor"))
(assert-event (fn-retain-statep *retention-forward-released*))
(assert-event (equal (fn-retain-reserved *retention-forward-released*) 6))
(assert-event (equal (len (fn-retain-pins *retention-forward-released*)) 1))
(assert-event (equal (len (fn-retain-releases *retention-forward-released*)) 1))

; A release record prevents reuse of an obligation identity with another subject.
(assert-event
 (equal (fn-retain-admit *retention-forward-released* "forward-1" "object-b"
                        :forward "other-receipt" 1)
        *retention-forward-released*))

; Archive release is separate and has no clock or automatic-expiry input.
(defconst *retention-all-released*
  (fn-retain-release *retention-forward-released* "archive-1" "object-a"
                     :archive "operator-release-a"))
(assert-event (fn-retain-statep *retention-all-released*))
(assert-event (equal (fn-retain-reserved *retention-all-released*) 0))
(assert-event (equal (len (fn-retain-pins *retention-all-released*)) 0))
