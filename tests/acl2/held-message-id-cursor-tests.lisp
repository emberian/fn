(in-package "ACL2")
(include-book "../../books/held-message-id-cursor")

(defun hmid-test-three (text)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hmid-one (fn-hmid-one (fn-hmid-one (fn-hmid-begin text)))))

; Reachable positives assert the literal antecedent and conclusion.
(assert-event
 (and (fn-hmid-ready-p (fn-hmid-begin "<x>"))
      (fn-hmid-ready-p (fn-hmid-begin "abc"))
      (fn-hmid-ready-p (fn-hmid-begin 7))
      (equal (fn-hmid-status (fn-hmid-begin 7)) :invalid)))
(assert-event
 (let ((c (fn-hmid-begin "<x>")))
   (and (fn-hmid-cursorp c) (fn-hmid-cursorp (fn-hmid-one c))
        (fn-hmid-ready-p c) (fn-hmid-ready-p (fn-hmid-one c)))))
(assert-event
 (let ((c (hmid-test-three "<x>")))
   (and (fn-hmid-ready-p c)
        (equal (fn-hmid-at 2 c) (fn-hmid-at 3 c))
        (equal (equal (fn-hmid-status c) :valid)
               (fn-scat-msgid-idp (fn-hmid-at 1 c))))))
(assert-event
 (let ((c (hmid-test-three "abc")))
   (and (fn-hmid-ready-p c)
        (equal (fn-hmid-at 2 c) (fn-hmid-at 3 c))
        (equal (equal (fn-hmid-status c) :valid)
               (fn-scat-msgid-idp (fn-hmid-at 1 c))))))

; Corrupted-state hypothesis removals use logical execution outside guards.
(set-guard-checking :none)
(assert-event
 (let ((c '(:held-msgid "<x>" 0 4 t)))
   (and (not (fn-hmid-cursorp c))
        (not (fn-hmid-cursorp (ec-call (fn-hmid-one c)))))))
(assert-event
 (let ((c '(:held-msgid "<x>" 0 3 nil)))
   (and (fn-hmid-cursorp c) (not (fn-hmid-ready-p c))
        (not (fn-hmid-ready-p (fn-hmid-one c))))))
(assert-event
 (let ((c '(:held-msgid "abc" 3 3 t)))
   (and (not (fn-hmid-ready-p c))
        (equal (fn-hmid-at 2 c) (fn-hmid-at 3 c))
        (not (equal (equal (fn-hmid-status c) :valid)
                    (fn-scat-msgid-idp (fn-hmid-at 1 c)))))))
(assert-event
 (let ((c (fn-hmid-begin "<x>")))
   (and (fn-hmid-ready-p c)
        (not (equal (fn-hmid-at 2 c) (fn-hmid-at 3 c)))
        (not (equal (equal (fn-hmid-status c) :valid)
                    (fn-scat-msgid-idp (fn-hmid-at 1 c)))))))

(set-guard-checking t)
