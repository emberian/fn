; Scenario M3 over many seeds (the nightly row; forge or hbox, not a unit).
; 10,000 seeds (from 1000) of 30 offers, honest; prints (passed refused stales seals first-refusal).
(include-book "fn2/tests/sim-layer-c")
(set-inhibit-output-lst '(proof-tree warning observation prove event))
(time$ (cw "FN2-M3-SWEEP ~x0~%" (fn2-m3-sweep 10000 1000 30 nil 0 0 0 0 nil)))
(good-bye)
