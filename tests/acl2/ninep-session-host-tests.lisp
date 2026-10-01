(in-package "ACL2")
(include-book "../../host/ninep-session-host")

(defthm ninep-host-disconnect-complete-positive
 (let ((session '(:base 64 (:internal-source 17) (:internal-mount 0)
                  (1) (:open) (:internal-selection) (1)
                  (9) (:running) ((:internal-read 1)) (0) ((:internal-borrow 1))
                  :held nil 0 nil)))
  (and (fn-ninep-sessionp session)
       (equal (fn-ninep-session-disconnect session state)
              (list :draining
               (update-nth 15 0 (update-nth 0 :draining-requests session)) state))))
 :rule-classes nil)
