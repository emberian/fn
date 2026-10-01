(in-package "ACL2")
(include-book "../../books/consumer-account-config-posting-relation")

(defconst *fn-bcpo-test-accounts*
  '(("invite" "issuer" "42" 0)
    ("a" "old-signing-key" "" 2)
    ("a" "read" "fn.discuss" 3)
    ("moderator" "a" "fn.discuss" 4)
    ("redeemed" "b" "verifier" 1)))
(defconst *fn-bcpo-test-base*
  (fn-cfg-make 7
    (fn-cfg-value-make-full nil nil nil nil nil nil nil nil nil
                            *fn-bcpo-test-accounts* nil)))
(defconst *fn-bcpo-test-event*
  (list :consumer-authority 0 0 0
        (fn-cab-operation '(99) 5 '(97) 0 2 (make-list 32 :initial-element 7))))
(defconst *fn-bcpo-test-begun* (fn-bcp-begin '(99) *fn-bcpo-test-base* 5))
(defconst *fn-bcpo-test-expected*
  (fn-cp-nth 1 (fn-bcp-expect *fn-bcpo-test-begun* '(97) :row)))
(defconst *fn-bcpo-test-staged*
  (fn-cp-nth 1 (fn-bcp-stage *fn-bcpo-test-expected* *fn-bcpo-test-event*)))
(defconst *fn-bcpo-test-sealed*
  (fn-cp-nth 1 (fn-bcp-seal *fn-bcpo-test-staged*)))

; Test harness only: every transition is the original fn-bcp-tick.
(defun fn-bcpo-test-run (fuel s)
  (declare (xargs :guard (natp fuel)))
  (if (or (zp fuel) (eq (fn-cp-nth 4 s) :ready)) s
    (fn-bcpo-test-run (- fuel 1) (fn-cp-nth 1 (fn-bcp-tick s nil)))))
(defconst *fn-bcpo-test-ready* (fn-bcpo-test-run 32 *fn-bcpo-test-sealed*))

(assert-event
 (and (fn-cab-eventp *fn-bcpo-test-event*)
      (equal (car (fn-bcp-stage *fn-bcpo-test-expected* *fn-bcpo-test-event*)) :ok)
      (equal (fn-bcpo-policy-rows (fn-cp-nth 9 *fn-bcpo-test-staged*))
             (fn-bcpo-policy-rows (fn-cp-nth 9 *fn-bcpo-test-expected*)))
      (equal (fn-cp-nth 4 *fn-bcpo-test-staged*) :collect)
      (equal (fn-bcpo-policy-rows (fn-cp-nth 9 *fn-bcpo-test-staged*)) nil)
      (fn-bcpo-base-relatedp *fn-bcpo-test-sealed*)))

(defun fn-bcpo-test-ticks-preserve (fuel s)
  (declare (xargs :guard (natp fuel)))
  (and (fn-bcpo-base-relatedp s)
       (let ((next (fn-cp-nth 1 (fn-bcp-tick s nil))))
         (and (equal (fn-bcpo-projected-result next) (fn-bcpo-projected-result s))
              (fn-bcpo-base-relatedp next)
              (or (zp fuel) (eq (fn-cp-nth 4 s) :ready)
                  (fn-bcpo-test-ticks-preserve (- fuel 1) next))))))
(assert-event (fn-bcpo-test-ticks-preserve 32 *fn-bcpo-test-sealed*))

; Complete antecedent and conclusion of the prepared boundary, plus literal
; full projected rows. Signing changes; access, moderation, invitation and
; credential rows keep their exact bytes and order.
(assert-event
 (let ((answer (fn-bcp-prepared *fn-bcpo-test-ready* 8)))
   (and (fn-bcpo-base-relatedp *fn-bcpo-test-ready*)
        (equal (fn-cp-nth 4 *fn-bcpo-test-ready*) :ready)
        (equal (car answer) :ok)
        (equal (fn-bcpo-policy-rows
                 (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 1 answer))))
               (fn-bcpo-policy-rows
                 (fn-cfg-accounts (fn-cfg-value
                                   (fn-cp-nth 2 *fn-bcpo-test-ready*))))))))
(assert-event
 (equal (fn-bcpo-policy-rows (fn-cp-nth 14 *fn-bcpo-test-ready*))
        '(("invite" "issuer" "42" 0)
          ("a" "read" "fn.discuss" 3)
          ("moderator" "a" "fn.discuss" 4)
          ("redeemed" "b" "verifier" 1))))

; Remove READY: this is the genuine successful seal before any scan ticks.
(assert-event
 (and (fn-bcpo-base-relatedp *fn-bcpo-test-sealed*)
      (not (equal (fn-cp-nth 4 *fn-bcpo-test-sealed*) :ready))
      (not (equal
             (fn-bcpo-policy-rows
              (fn-cfg-accounts (fn-cfg-value
               (fn-cp-nth 1 (fn-bcp-prepared *fn-bcpo-test-sealed* 8)))))
             (fn-bcpo-policy-rows
              (fn-cfg-accounts (fn-cfg-value
               (fn-cp-nth 2 *fn-bcpo-test-sealed*))))))))

; Remove the relation: corrupt the ready result after the real computation.
(assert-event
 (let ((corrupt (update-nth 14 nil *fn-bcpo-test-ready*)))
   (and (equal (fn-cp-nth 4 corrupt) :ready)
        (not (fn-bcpo-base-relatedp corrupt))
        (not (equal
               (fn-bcpo-policy-rows (fn-cfg-accounts (fn-cfg-value
                 (fn-cp-nth 1 (fn-bcp-prepared corrupt 8)))))
               (fn-bcpo-policy-rows (fn-cfg-accounts (fn-cfg-value
                 (fn-cp-nth 2 corrupt)))))))))

; Seal's phase premise matters at the real :binding predecessor.
(assert-event
 (and (equal (fn-bcpo-policy-rows (fn-cp-nth 9 *fn-bcpo-test-expected*)) nil)
      (not (equal (fn-cp-nth 4 *fn-bcpo-test-expected*) :collect))
      (not (fn-bcpo-base-relatedp
             (fn-cp-nth 1 (fn-bcp-seal *fn-bcpo-test-expected*))))))

; Corrupted new-binding input: a non-signing row cannot be waved away.
(assert-event
 (let ((corrupt (update-nth 9 '(("intruder" "read" "group" 3))
                            *fn-bcpo-test-staged*)))
   (and (equal (fn-cp-nth 4 corrupt) :collect)
        (not (equal (fn-bcpo-policy-rows (fn-cp-nth 9 corrupt)) nil))
        (not (fn-bcpo-base-relatedp (fn-cp-nth 1 (fn-bcp-seal corrupt)))))))

; The maintained tick relation cannot be assumed before the actual seal.
(assert-event
 (and (not (fn-bcpo-base-relatedp *fn-bcpo-test-begun*))
      (not (fn-bcpo-base-relatedp
             (fn-cp-nth 1 (fn-bcp-tick *fn-bcpo-test-begun* nil))))))

; Stage success-premise removal on explicitly corrupted new-binding storage.
(assert-event
 (let* ((corrupt (update-nth 9 '(("intruder" "read" "group" 3))
                             *fn-bcpo-test-begun*))
        (answer (fn-bcp-stage corrupt *fn-bcpo-test-event*)))
   (and (not (equal (car answer) :ok))
        (not (equal (fn-bcpo-policy-rows (fn-cp-nth 9 (fn-cp-nth 1 answer)))
                    (fn-bcpo-policy-rows (fn-cp-nth 9 corrupt)))))))

; Nonempty actual observer results, with signing rows interleaved between
; policy rows. The equations are unconditional and have no hypotheses to drop.
(defconst *fn-bcpo-observer-rows*
  '(("a" "old-signing" "" 2)
    ("alice" "*" "fn.discuss" 3)
    ("fn.discuss" "fn.queue" "moderator@example" 5)
    ("alice" "fn.discuss" "" 4)
    ("b" "other-signing" "" 2)
    ("bob" "fn.discuss" "" 4)
    ("fn.discuss" "later-queue" "later-address" 5)))
(assert-event
 (and (equal (fn-cfg-access-table (fn-bcpo-policy-rows *fn-bcpo-observer-rows*))
             (fn-cfg-access-table *fn-bcpo-observer-rows*))
      (equal (fn-cfg-access-table *fn-bcpo-observer-rows*)
             '(("alice" "*" "fn.discuss" 3)))))
(assert-event
 (and (equal (fn-cfg-moderation-row
              (fn-bcpo-policy-rows *fn-bcpo-observer-rows*) "fn.discuss")
             (fn-cfg-moderation-row *fn-bcpo-observer-rows* "fn.discuss"))
      (equal (fn-cfg-moderation-row *fn-bcpo-observer-rows* "fn.discuss")
             '("fn.discuss" "fn.queue" "moderator@example" 5))))
(assert-event
 (and (equal (fn-cfg-moderator-logins
              (fn-bcpo-policy-rows *fn-bcpo-observer-rows*) "fn.discuss")
             (fn-cfg-moderator-logins *fn-bcpo-observer-rows* "fn.discuss"))
      (equal (fn-cfg-moderator-logins *fn-bcpo-observer-rows* "fn.discuss")
             '("alice" "bob"))))

(defconst *fn-bcpo-observer-ready*
  (fn-bcpo-test-run 32
   (fn-cp-nth 1 (fn-bcp-seal
    (fn-cp-nth 1 (fn-bcp-stage
     (fn-cp-nth 1 (fn-bcp-expect
      (fn-bcp-begin '(99)
       (fn-cfg-make 7
        (fn-cfg-value-make-full nil nil nil nil nil nil nil nil nil
                                *fn-bcpo-observer-rows* nil)) 5)
      '(97) :row)) *fn-bcpo-test-event*))))))
(assert-event
 (let* ((s *fn-bcpo-observer-ready*)
        (answer (fn-bcp-prepared s 8))
        (before (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 2 s))))
        (after (fn-cfg-accounts (fn-cfg-value (fn-cp-nth 1 answer)))))
   (and (fn-bcpo-base-relatedp s)
        (equal (fn-cp-nth 4 s) :ready)
        (equal (car answer) :ok)
        (not (equal before after))
        (equal (fn-cfg-access-table after) (fn-cfg-access-table before))
        (equal (fn-cfg-moderation-row after "fn.discuss")
               (fn-cfg-moderation-row before "fn.discuss"))
        (equal (fn-cfg-moderator-logins after "fn.discuss")
               (fn-cfg-moderator-logins before "fn.discuss")))))
