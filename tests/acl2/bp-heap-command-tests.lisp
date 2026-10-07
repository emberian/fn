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

; The BP terms of a node serve: argument positions, the optional trailing control
; pair, the transfer MRU's default and its refusals.
(defconst *bph-serve*
 '("bp-node" "serve" "0" "journal" "store" "receipts" "workflow" "node" "peer" "dest"
   "policy" "issuer" "host" "4556" "1" "3600000" "2" "32" "1048576" "0" "0" "0"))
(assert-event (fn-bph-node-serve-p *bph-serve*))
(assert-event (equal (fn-bph-node-journal *bph-serve*) "journal"))
(assert-event (equal (fn-bph-node-transfer *bph-serve* 7) 1048576))
(assert-event (equal (fn-bph-node-transfer (append (take 19 *bph-serve*) '("--control-config" "c")) 7) 1048576))
(assert-event (equal (fn-bph-node-transfer (append (take 18 *bph-serve*) '("--control-config" "c")) 7) 7))
(assert-event (equal (fn-bph-node-transfer (take 14 *bph-serve*) 7) 7))
(assert-event (equal (fn-bph-node-transfer (append (take 18 *bph-serve*) '("0")) 7) nil))
(assert-event (equal (fn-bph-node-transfer (append (take 18 *bph-serve*) '("+5")) 7) nil))
(assert-event (not (fn-bph-node-serve-p '("bp-app" "receive" "0" "spool" "store" "receipts" "node" "peer" "dest" "policy" "issuer" "1" "02"))))
(assert-event (not (fn-bph-node-serve-p '("bp-node" "dispatch" "journal" "store"))))

; The two-node test's terms: the default session profile (2 in, 1 out) and node
; profile, transfer MRU 1048576, segment MRU 1024.  The base is a 4096 MB store
; reservation, its figure 4096 MB.
(defconst *bph-session* '(2 1 nil 30000 120000 600000))
(defconst *bph-node* (fn-bpnpf-node-profile-read nil nil))
(defconst *bph-terms* (list *bph-session* *bph-node* 1048576 1024))
(defconst *bph-base* '(:heap 4096 "p" 65536 1024 20))
(defconst *bph-machine* '(137438953472))
(defconst *bph-launch* (fn-bph-extend-reservation *bph-base* *bph-terms* 100 *bph-machine*))
; Premise inhabitation: the terms are funded and the extended reservation is accepted.
(assert-event (and (equal (fn-bpsp-node-capacity *bph-session* *bph-node* 1048576 1024) 944178640)
                   (equal (car *bph-launch*) :heap)
                   (equal (nth 1 *bph-launch*) 4997)))
; Keystone, ground: at the extended reservation the node's startup check holds.
(assert-event
 (equal (car (fn-bpsp-node-startup *bph-session* *bph-node* 1048576 1024
              (* 1048576 (nth 1 *bph-launch*)) (* 1048576 4096)))
        :hold))
; TEETH: the unextended reservation, same terms, is refused by name.
(assert-event
 (equal (fn-bpsp-node-startup *bph-session* *bph-node* 1048576 1024
         (* 1048576 (nth 1 *bph-base*)) (* 1048576 4096))
        '(:refused :bp-session-capacity-not-held)))
; TEETH: no terms is the base unchanged; a machine too small is refused; unfunded terms are refused.
(assert-event (equal (fn-bph-extend-reservation *bph-base* nil 100 *bph-machine*) *bph-base*))
(assert-event (equal (car (fn-bph-extend-reservation *bph-base* *bph-terms* 100 '(4294967296))) :refused))
(assert-event (equal (fn-bph-extend-reservation *bph-base* (list '(2 1 1 30000 120000 600000) *bph-node* 1048576 1024) 100 *bph-machine*)
                     '(:refused :invalid-bp-session-terms 0 65536)))
(assert-event (equal (fn-bph-extend-reservation '(:refused :x 0 0) *bph-terms* 100 *bph-machine*) '(:refused :x 0 0)))
