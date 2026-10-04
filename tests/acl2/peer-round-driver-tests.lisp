(in-package "ACL2")
(include-book "../../books/peer-round-driver")
(include-book "must-fail-checked")
(defconst *prd-active* '((:pull (65)) (:pull (66)) (:catch-up (67))))
; PRF-1260 antecedent and whole ordered visit conclusion.
(assert-event (and (true-listp *prd-active*)
                   (subsetp-equal *prd-active* *prd-active*)
                   (equal (fn-prd-sweep *prd-active* *prd-active*) *prd-active*)))
; Retained subset hypothesis is needed: an absent round cannot be selected.
(defconst *prd-absent* '((:pull (65)) (:pull (68)) (:catch-up (67))))
(assert-event (and (true-listp *prd-absent*)
                   (not (subsetp-equal *prd-absent* *prd-active*))
                   (not (equal (fn-prd-sweep *prd-active* *prd-absent*) *prd-absent*))))
(assert-event (equal (fn-prd-select *prd-active* *prd-active*)
                     '((:pull (65)) ((:pull (66)) (:catch-up (67))))))
(assert-event (equal (fn-prd-select *prd-active* (cdr *prd-active*))
                     '((:pull (66)) ((:catch-up (67))))))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 9 10 nil)
                     '(:io :write)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 10 10 nil)
                     '(:lost :timeout)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) nil 10 nil nil)
                     '(:effect (:remote 1))))
(assert-event (equal (fn-prd-read-limit nil) 512))
(assert-event (equal (fn-prd-write-end 500 2000) 1012))
(assert-event (not (fn-prd-loss-class-ok :read "fnn-store-indeterminate")))
(assert-event (not (fn-prd-loss-class-ok :read "unknown-io-subclass")))
(assert-event (fn-prd-loss-class-ok :dial "fnn-peer-dial-error"))

; Push selection retains write before later framer events and offers.
(assert-event (equal (fn-prd-feed-action nil t t t 9 10) :write))
(assert-event (equal (fn-prd-feed-action nil t t t 10 10) :timeout))
(assert-event (equal (fn-prd-feed-action :tls nil t nil 9 10) :tls))
(assert-event (equal (fn-prd-feed-action nil nil t t 11 nil) :reply))
(assert-event (equal (fn-prd-feed-action nil nil nil t 11 nil) :offer))
(assert-event (equal (fn-prd-feed-action nil nil nil nil 11 nil) :read))
(assert-event (equal (fn-prd-write-quantum-end 65500 100000 65536) 100000))
(assert-event (equal (fn-prd-write-end 512 (fn-prd-write-quantum-end 0 2000 600)) 600))

; Teeth: fn-prd-round-past-deadline-is-lost. An unfinished round at its
; deadline is lost even with a pending write, effect and event.
(assert-event (equal (fn-prd-action nil '((:remote 1)) '((:local 2)) :write 9 10 9)
                     '(:lost :round-deadline)))
; Each retained hypothesis matters: a finished round finishes; one millisecond
; before the deadline the I/O continues; no deadline is no round bound.
(assert-event (equal (fn-prd-action t nil nil nil 9 nil 9) '(:finish)))
(assert-event (equal (fn-prd-action nil '((:remote 1)) nil :write 8 10 9) '(:io :write)))
(assert-event (equal (fn-prd-action nil nil nil nil 9 nil nil) '(:read)))
(assert-event (equal (fn-prd-round-deadline 5) 600005))
