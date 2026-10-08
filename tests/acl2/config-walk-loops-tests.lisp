; Teeth for books/config-walk-loops.lisp (PRF-383).  The two statements have
; no hypothesis, so there is no removal witness; each has a positive witness
; at a non-empty accumulator and a table where the walk keeps some rows and
; skips others, and mutations of the loop's accumulator discipline that the
; statement refutes.
(in-package "ACL2")
(include-book "../../books/config-walk-loops")
(include-book "../../books/defkeystone")

(defconst *cwl-rows*
  '(("alice" "path-identity" "k1") ("bob" "other" "k2") ("alice" "path-identity" "k3")
    ("carol" "path-identity" "k4")))

(defteeth fn-cfg-rows-with-key-loop-is-revappend-of-the-walk
  :claim (()
          (equal (fn-cfg-rows-with-key-loop rows a acc)
                 (revappend acc (fn-cfg-rows-with-key rows a))))
  :subject fn-cfg-rows-with-key
  :witness ((rows *cwl-rows*) (a "alice") (acc '(1 2)))
  :breaks ()
  :mutations ((accumulator-not-reversed
               (:conclusion
                (equal (fn-cfg-rows-with-key-loop rows a acc)
                       (append acc (fn-cfg-rows-with-key rows a))))
               ((rows *cwl-rows*) (a "alice") (acc '(1 2)))
               :fault "the loop leaves the accumulator in push order instead of reversing it onto the walk")
              (accumulator-dropped
               (:conclusion
                (equal (fn-cfg-rows-with-key-loop rows a acc)
                       (fn-cfg-rows-with-key rows a)))
               ((rows *cwl-rows*) (a "alice") (acc '(1 2)))
               :fault "the loop discards the accumulator it was started with")))

(defteeth fn-cfg-peer-names-loop-is-revappend-of-the-walk
  :claim (()
          (equal (fn-cfg-peer-names-loop peers acc)
                 (revappend acc (fn-cfg-peer-names peers))))
  :subject fn-cfg-peer-names
  :witness ((peers *cwl-rows*) (acc '(1 2)))
  :breaks ()
  :mutations ((accumulator-not-reversed
               (:conclusion
                (equal (fn-cfg-peer-names-loop peers acc)
                       (append acc (fn-cfg-peer-names peers))))
               ((peers *cwl-rows*) (acc '(1 2)))
               :fault "the loop leaves the accumulator in push order instead of reversing it onto the walk")
              (skipped-rows-kept
               (:conclusion
                (equal (fn-cfg-peer-names-loop peers acc)
                       (revappend acc (revappend (fn-cfg-peer-names peers) '("bob")))))
               ((peers *cwl-rows*) (acc '(1 2)))
               :fault "a row that is not a path-identity peer is walked as one")))

; Both walks really filter at the witness: the table has rows each skips.
(assert-event (equal (fn-cfg-rows-with-key *cwl-rows* "alice")
                     '(("alice" "path-identity" "k1") ("alice" "path-identity" "k3"))))
(assert-event (equal (fn-cfg-peer-names *cwl-rows*) '("alice" "alice" "carol")))
