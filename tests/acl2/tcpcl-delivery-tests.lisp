; A real fn-tcl-complete END acknowledgement held across a BPA decision.
(in-package "ACL2")
(include-book "../../books/tcpcl-delivery-invariants")
(include-book "tcpcl-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *t-delivery-events* (fn-tcl-result-events *t-b3*))
(defconst *t-delivery-held*
  (list (cadr (nth 0 *t-delivery-events*))
        (cadr (nth 1 *t-delivery-events*))))

(assert-event (fn-tcl-held-final-ackp *t-delivery-held* 0))
(assert-event (equal (nth 2 *t-delivery-events*)
                     '(:bundle-received 0 (10 20 30 40 50))))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted nil)))
        :accepted))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted nil)))
        *t-delivery-held*))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :capacity)))
        (list (fn-tcl-make-xfer-ack 2 0 3)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-no-resources* 0))))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :identity-conflict)))
        (list (fn-tcl-make-xfer-ack 2 0 3)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-not-acceptable* 0))))
(assert-event
 (null (fn-tcl-delivery-plan-messages
        (fn-tcl-delivery-plan *t-delivery-held* 0 '(:uncertain :persistence)))))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan nil 0 '(:refused :capacity)))
        :fault))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 18 '(:refused :capacity)))
        :fault))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted 99)))
        :fault))
(assert-event
 (not (fn-tcl-output-has-final-ackp
       (fn-tcl-delivery-plan-messages
        (fn-tcl-delivery-plan *t-delivery-held* 0 '(:refused :capacity)))
       0)))

; One actual fn-tcl-drive batch has an ACK for transfer 0, then a definitive
; refusal of transfer 0, then the held END ACK for transfer 1.  The callback
; for transfer 1 must preserve both earlier machine outputs.
(defconst *t-delivery-short-tle*
  (list (fn-tcl-make-item 0 *fn-tcl-ext-transfer-length*
                          '(0 0 0 0 0 0 0 4))))
(defconst *t-delivery-mixed-wire*
  (append
   (fn-tcl-encode (fn-tcl-make-xfer-segment
                   2 0 *t-delivery-short-tle* '(1 2 3)))
   (fn-tcl-encode (fn-tcl-make-xfer-segment 0 0 nil '(4 5)))
   (fn-tcl-encode (fn-tcl-make-xfer-segment 3 1 nil '(7 8)))))
(defconst *t-delivery-mixed-events*
  (fn-tcl-result-events (fn-tcl-drive *t-b* *t-delivery-mixed-wire* 0)))
(assert-event
 (equal *t-delivery-mixed-events*
        (list (list :send (fn-tcl-make-xfer-ack 2 0 3))
              (list :send (fn-tcl-make-xfer-refuse
                           *fn-tcl-refuse-not-acceptable* 0))
              (list :inbound-refused 0 *fn-tcl-refuse-not-acceptable*)
              (list :send (fn-tcl-make-xfer-ack 3 1 2))
              (list :bundle-received 1 '(7 8)))))
(defconst *t-delivery-mixed-held*
  (list (cadr (nth 0 *t-delivery-mixed-events*))
        (cadr (nth 1 *t-delivery-mixed-events*))
        (cadr (nth 3 *t-delivery-mixed-events*))))
(assert-event (fn-tcl-held-final-ackp *t-delivery-mixed-held* 1))
(assert-event
 (equal (fn-tcl-delivery-plan-messages
         (fn-tcl-delivery-plan *t-delivery-mixed-held* 1
                               '(:refused :capacity)))
        (list (fn-tcl-make-xfer-ack 2 0 3)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-not-acceptable* 0)
              (fn-tcl-make-xfer-refuse *fn-tcl-refuse-no-resources* 1))))
(assert-event
 (not (fn-tcl-output-has-final-ackp
       (fn-tcl-delivery-plan-messages
        (fn-tcl-delivery-plan *t-delivery-mixed-held* 1
                              '(:refused :capacity)))
       1)))

; Two complete transfers in one socket read exercise the host's reset after
; the first callback.  Both held prefixes come from actual host-drive output.
(defconst *t-delivery-two-wire*
  (append (fn-tcl-encode
           (fn-tcl-make-xfer-segment 3 0 nil '(11 12)))
          (fn-tcl-encode
           (fn-tcl-make-xfer-segment 3 1 nil '(21 22)))))
(defconst *t-delivery-two-events*
  (cadr (fn-tcl-host-drive *t-b* *t-delivery-two-wire* 0)))
(assert-event (fn-tcl-delivery-eventsp *t-delivery-two-events*))
(assert-event
 (equal (cadr (fn-tcl-first-bundle-event *t-delivery-two-events*)) 0))
(assert-event
 (fn-tcl-held-final-ackp
  (fn-tcl-held-before-first-bundle *t-delivery-two-events*) 0))
(assert-event
 (equal (cadr (fn-tcl-first-bundle-event
               (fn-tcl-events-after-first-bundle *t-delivery-two-events*))) 1))
(assert-event
 (fn-tcl-held-final-ackp
  (fn-tcl-held-before-first-bundle
   (fn-tcl-events-after-first-bundle *t-delivery-two-events*)) 1))

; Dropping either premise of the host boundary theorem is materially wrong.
(must-fail
 (defthm fn-tcl-events-without-first-bundle-held-final
   (implies (fn-tcl-delivery-eventsp events)
            (fn-tcl-held-final-ackp
             (fn-tcl-held-before-first-bundle events)
             (cadr (fn-tcl-first-bundle-event events))))))
(must-fail
 (defthm fn-tcl-arbitrary-events-have-held-final
   (implies (fn-tcl-first-bundle-event events)
            (fn-tcl-held-final-ackp
             (fn-tcl-held-before-first-bundle events)
             (cadr (fn-tcl-first-bundle-event events))))))
(assert-event
 (not (fn-tcl-held-final-ackp
       (fn-tcl-held-before-first-bundle '((:bundle-received 0 (1)))) 0)))

; An accepted path must be NIL (exact duplicate) or a native path string.
; If its type premise is dropped, an invalid callback is a fault, not release.
(must-fail
 (defthm fn-tcl-accepted-without-path-type-releases-held
   (implies (fn-tcl-held-final-ackp messages xfer-id)
            (equal (fn-tcl-delivery-plan-messages
                    (fn-tcl-delivery-plan messages xfer-id
                                          (list :accepted path)))
                   messages))))
(assert-event
 (equal (fn-tcl-delivery-plan-status
         (fn-tcl-delivery-plan *t-delivery-held* 0 '(:accepted 99)))
        :fault))
(must-fail
 (assert-event
  (equal (fn-tcl-delivery-plan-status
          (fn-tcl-delivery-plan nil 0 '(:refused :capacity)))
         :refused)))
