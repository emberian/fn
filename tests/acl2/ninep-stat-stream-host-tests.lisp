(in-package "ACL2")
(include-book "../../host/ninep-stat-stream-host")

; Codec metadata fixture, not a source/QID or allocation grant.
(defthm n9pst-host-one-header-octet-complete-boundary-positive
 (let* ((stat (mv-nth 1 (fn-9pst-begin "a" '(128 0 7) 0)))
        (reply (mv-nth 1 (fn-9pst-reply-begin :stat 3 64 0 stat)))
        (buffer (create-fn-octets)))
  (and (fn-9pst-ready-p stat) (equal (fn-octets-len buffer) 0)
       (equal (fn-ninep-stat-reply-step reply buffer state)
              (list :yield (list :ninep-stat-reply :stat 3 stat 1 59) '(59) state))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-octets-len fn-octets-append-octet))))

(defthm n9pst-host-corrupt-refusal-complete-boundary-positive
 (let ((cursor '(:ninep-stat-reply :stat 3 nil 59 59)) (buffer (create-fn-octets)))
  (and (not (fn-9pst-ready-p nil))
       (equal (fn-ninep-stat-reply-step cursor buffer state)
              (list :recovery-required cursor buffer state))))
 :rule-classes nil)
