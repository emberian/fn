; Teeth for books/config-walk-loops.lisp (PRF-383).  The two statements have
; no hypothesis, so there is no removal witness; each has a positive witness
; at a non-empty accumulator and a table where the walk keeps some rows and
; skips others, and mutations of the loop's accumulator discipline that the
; statement refutes.
(in-package "ACL2")
(include-book "../../books/defkeystone")

(defconst *cwl-rows*
  '(("alice" "path-identity" "k1") ("bob" "other" "k2") ("alice" "path-identity" "k3")
    ("carol" "path-identity" "k4")))

; Both walks really filter at the witness: the table has rows each skips.
(assert-event (equal (fn-cfg-rows-with-key *cwl-rows* "alice")
                     '(("alice" "path-identity" "k1") ("alice" "path-identity" "k3"))))
(assert-event (equal (fn-cfg-peer-names *cwl-rows*) '("alice" "alice" "carol")))
