(in-package "ACL2")
(include-book "../../books/bp-heap-command")
(assert-event
 (equal (fn-bph-command-plan '("bp-node" "serve" "0" "journal" "store" "receipts"
                               "workflow" "node" "peer" "dest" "policy" "issuer" "host" "4556"))
        '(:run "store" 1)))
(assert-event
 (equal (fn-bph-command-plan '("bp-app" "receive" "0" "spool" "store" "receipts"
                               "node" "peer" "dest" "policy" "issuer" "1" "02"))
        '(:run "store" 2)))
(assert-event (equal (fn-bph-command-plan '("bp-node" "dispatch" "journal" "store"))
                     '(:not-served-bp)))
(assert-event (equal (fn-bph-command-plan '("bp-node" "serve")) '(:refused :store-root)))
(assert-event
 (equal (fn-bph-command-plan '("bp-node" "serve" "0" "journal" "store"))
        '(:refused :node-arguments)))
(assert-event (equal (fn-bph-connections "18446744073709551615") 18446744073709551615))
(assert-event (equal (fn-bph-connections "18446744073709551616") nil))
(assert-event (equal (fn-bph-connections "123456789012345678901") nil))
(assert-event (equal (fn-bph-connections "0") nil))
(assert-event (equal (fn-bph-connections "+2") nil))
(assert-event (equal (fn-bph-connections "2x") nil))
