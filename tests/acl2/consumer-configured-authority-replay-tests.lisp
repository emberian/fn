; Actual account decisions retained by the paired cursor constructor. These
; tests do not establish the currently missing prefix Store/history source.
(in-package "ACL2")
(include-book "../../books/consumer-configured-authority-replay")
(local (include-book "consumer-account-config-commit-tests"))

(defconst *caprt-prior*
 (list :ok (fn-cp-nth 1 *acjt-final*) (fn-cp-nth 2 *acjt-final*)
           (fn-cp-nth 3 *acjt-final*)))
(defconst *caprt-later-begin*
 (let* ((cp (fn-cp-nth 1 *acjt-final*)) (seq (fn-cp-nth 3 cp)))
  (fn-acj-stage cp (fn-cp-nth 4 *acjt-final*) nil (fn-cp-nth 6 *acjt-final*)
   (list :consumer-authority seq (1+ seq) 0
         (list :authority-begin '(66) 1 (fn-cp-nth 2 (fn-cp-nth 6 cp)) 7)) seq nil)))

;@mutation-witness real-typed-c-full8-publication-retained
(assert-event
 (and (equal (fn-cp-nth 0 *acjt-final*) :ok)
      (equal (len *acjt-final*) 8)
      (equal (fn-capr-publication '(:ok nil nil nil) *acjt-final*) *caprt-prior*)
      (equal (fn-cp-nth 3 (fn-cp-nth 1 *caprt-prior*))
             (fn-cp-nth 3 *acjt-final*))))

;@mutation-witness real-nonauthorizing-full7-borrows-prior-publication
(assert-event
 (and (equal (fn-cp-nth 0 *caprt-later-begin*) :ok)
      (equal (len *caprt-later-begin*) 7)
      (null (fn-cp-nth 2 *caprt-later-begin*))
      (null (fn-cp-nth 3 *caprt-later-begin*))
      (equal (fn-capr-publication *caprt-prior* *caprt-later-begin*)
             (list :ok (fn-cp-nth 1 *caprt-later-begin*)
                   (fn-cp-nth 2 *caprt-prior*) (fn-cp-nth 3 *caprt-prior*)))
      (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 *caprt-later-begin*)))))

;@mutation-witness complete-configured-cursor-retains-once-produced-full8
(assert-event
 (let* ((before (fn-capr-state :physical :original :fields nil nil :preparation
                   '(:ok nil nil nil) 0 :withdrawals :visible :verdicts 8 13
                   '(:config-tail) '(:event-tail) '(:config-history)))
        (one (fn-capr-install before :new-physical :same-original :same-fields
               *acjt-final* nil nil :same-withdrawals :same-visible :same-verdicts
               9 13 nil '(:event-tail)))
        (s (fn-cp-nth 1 one)))
  (and (equal (fn-cp-nth 0 one) :advanced)
       (equal (fn-cp-nth 2 one) *acjt-final*)
       (equal s
        (list :configured-authority-replay :new-physical :same-original :same-fields
          (fn-cp-nth 1 *acjt-final*) (fn-cp-nth 4 *acjt-final*) nil *caprt-prior* nil
          :same-withdrawals :same-visible :same-verdicts 9 13 nil '(:event-tail)
          '(:config-history))))))
