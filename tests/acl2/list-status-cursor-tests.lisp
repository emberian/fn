(in-package "ACL2")
(include-book "../../books/list-status-cursor")

(defun lss-test-drain (cur fuel)
  (declare (xargs :mode :program :guard (natp fuel)))
  (if (fn-lss-donep cur) (list :done (fn-lss-status cur))
    (if (zp fuel) (list :limit nil)
      (lss-test-drain (fn-lss-one cur) (1- fuel)))))

(defun lss-test-agrees (group closed)
  (declare (xargs :mode :program :guard t))
  (equal (lss-test-drain (fn-lss-start group closed) 10000)
         (list :done (fn-nntp-closed-status (fn-nntp-string-octets group) closed))))

(assert-event
 (and (lss-test-agrees "fn.a" nil)
      (lss-test-agrees "fn.a" '((102 110 46 98) (102 110 46 97)))
      (lss-test-agrees "fn.a" '((:moderated (102 110 46 97) queue nil)))
      (lss-test-agrees "fn.a" '((:approver (102 110 46 97) queue)))
      (lss-test-agrees "fn.a" '((:moderated (102 110 46 97) queue nil)
                                (102 110 46 97)))
      (lss-test-agrees "fn.a" '((102 110 46 97)
                                (:moderated (102 110 46 97) queue nil)))
      (lss-test-agrees "fn.a" '((102 110 46 97 . bad) (:moderated (102 110 46 97))))
      (lss-test-agrees "" '(nil))
      (lss-test-agrees nil '(nil))
      (lss-test-agrees "" '((:moderated nil queue nil)))))

(assert-event
 (let* ((cur (fn-lss-start "fn.a" '((102 110 46 97))))
        (one (fn-lss-one cur))
        (two (fn-lss-one one)))
   (and (equal (fn-cur-at 5 one) 0)
        (equal (fn-cur-at 5 two) 1)
        (equal (fn-cur-at 4 two) '(110 46 97))
        (not (fn-lss-donep two)))))

(defthm lss-literal-entry-progress
  (let* ((cur (fn-lss-start "fn.a" '((102 110 46 98) (102 110 46 97))))
         (next (fn-lss-one cur)))
    (and (posp (fn-lss-remaining-work cur))
         (< (fn-lss-remaining-work next) (fn-lss-remaining-work cur))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lss-start fn-lss-make
                                     fn-lss-one fn-lss-remaining-work fn-cur-at))))
(defthm lss-literal-character-progress
  (let* ((cur (fn-lss-one (fn-lss-start "fn.a" '((102 110 46 98)))))
         (next (fn-lss-one cur)))
    (and (posp (fn-lss-remaining-work cur))
         (< (fn-lss-remaining-work next) (fn-lss-remaining-work cur))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lss-start fn-lss-make
                                     fn-lss-one fn-lss-remaining-work fn-cur-at))))
; Actual factory-to-settlement reachability, not an invented corrupted state.
; The progress theorem has exactly one premise; its removal fails at settlement.
(defthm lss-progress-premise-removal
  (let* ((a (fn-lss-start "fn.a" '((102 110 46 97))))
         (b (fn-lss-one a)) (c (fn-lss-one b)) (d (fn-lss-one c))
         (e (fn-lss-one d)) (f (fn-lss-one e)) (cur (fn-lss-one f)))
    (and (fn-lss-donep cur)
         (equal (fn-lss-status cur) "n")
         (not (posp (fn-lss-remaining-work cur)))
         (not (< (fn-lss-remaining-work (fn-lss-one cur))
                 (fn-lss-remaining-work cur)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lss-start fn-lss-make fn-lss-one
                                     fn-lss-donep fn-lss-status
                                     fn-lss-remaining-work fn-cur-at))))
