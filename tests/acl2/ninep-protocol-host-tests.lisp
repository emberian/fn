; Actual guarded dispatch output and STATE frame, with literal wire bytes.
(in-package "ACL2")
(include-book "../../host/ninep-protocol-host")

(defun-nx ninep-host-prefix-positive (the-state)
 (let* ((buf (fn-octets-from-list '(23 0 0 0 116 52 18) (create-fn-octets)))
        (answer (mv-list 3 (fn-ninep-frame-prefix 0 7 32 buf the-state))))
  (and (fn-octets-p buf)
       (equal (nth 0 answer) '(:header 116 4660 23 7 23))
       (equal (nth 1 answer) '(:need-body 16))
       (equal (nth 2 answer) the-state)
       (equal (nth 0 answer) (fn-9p-header-reference 0 7 32 buf)))))
(defthm ninep-host-prefix-complete-positive
 (ninep-host-prefix-positive the-state) :rule-classes nil)

(defun-nx ninep-host-prefix-refusals (the-state)
 (let* ((buf (fn-octets-from-list '(23 0 0 0 116 52 18) (create-fn-octets)))
        (short (mv-list 3 (fn-ninep-frame-prefix 0 6 32 buf the-state)))
        (large (mv-list 3 (fn-ninep-frame-prefix 0 7 22 buf the-state))))
  (and (fn-octets-p buf)
       (equal (nth 0 short) '(:need-header 1))
       (equal (nth 1 short) '(:need-header 1))
       (equal (nth 2 short) the-state)
       (equal (nth 0 large) '(:refused :message-too-large))
       (equal (nth 1 large) '(:refused :message-too-large))
       (equal (nth 2 large) the-state))))
(defthm ninep-host-prefix-preserves-need-and-refusal
 (ninep-host-prefix-refusals the-state) :rule-classes nil)

(defun-nx ninep-host-directory-positive (the-state)
 (let* ((tasks '((:visit ((:group-number 5 nil) nil) (0 1 1 0 0 0 0 1) 8)))
        (answer (mv-list 4 (fn-ninep-group-directory-step tasks the-state))))
  (and (equal (nth 0 answer) :group)
       (equal (nth 1 answer) '(:group-path (0 1 1 0 0 0 0 1) 8 (:group-number 5 nil)))
       (equal (nth 3 answer) the-state)
       (equal (fn-9p-ge-remaining tasks)
              (append (list (nth 1 answer)) (fn-9p-ge-remaining (nth 2 answer)))))))
(defthm ninep-host-directory-complete-positive
 (ninep-host-directory-positive the-state) :rule-classes nil)
