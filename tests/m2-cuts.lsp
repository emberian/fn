; M2 spine cuts over the served core (tests/m2-cuts.lisp): one line per cut,
; M2CUT c<i> PASS|FAIL <reasons>, then M2 <n>/12. H's nightly turns the lines
; into OUT/m2.json:
;   tools/acl2 --timeout 1800 < tests/m2-cuts.lsp | python3 tests/m2_json.py OUT
(in-package "ACL2")
(set-cbd "tests/")
(include-book "m2-cuts")
(set-inhibit-output-lst '(proof-tree prove event summary observation warning))
(set-fmt-hard-right-margin 100000 state)
(set-fmt-soft-right-margin 100000 state)
(make-event (let ((n (m2-report *mini-cuts* 0)))
              (prog2$ (cw "M2 ~x0/~x1~%" n (len *mini-cuts*)) (value '(value-triple :done)))))
(good-bye)
