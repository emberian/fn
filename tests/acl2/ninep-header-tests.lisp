; Literal9P2000 wire witnesses over the actual concrete-buffer boundary.
(in-package "ACL2")
(include-book "../../books/ninep-header")

(defun-nx ninep-header-positive ()
 (let* ((buf (fn-octets-from-list '(23 0 0 0 116 52 18) (create-fn-octets)))
        (answer (fn-9p-header-at 0 7 32 buf)))
  (and (fn-octets-p buf)
       (equal answer '(:header 116 4660 23 7 23))
       (equal answer (fn-9p-header-reference 0 7 32 buf))
       (equal (fn-9p-body-action answer 7) '(:need-body 16))
       (equal (fn-9p-body-action answer 22) '(:need-body 1))
       (equal (fn-9p-body-action answer 23) '(:frame 116 4660 7 23))
       (equal (fn-9p-body-action answer 30) '(:frame 116 4660 7 23)))))
(defthm ninep-header-literal-complete-positive
 (ninep-header-positive) :rule-classes nil)

(defun-nx ninep-header-limit-and-prefix-refusals ()
 (let ((buf (fn-octets-from-list '(23 0 0 0 116 52 18) (create-fn-octets))))
  (and (fn-octets-p buf)
       (equal (fn-9p-header-at 0 6 32 buf) '(:need-header 1))
       (equal (fn-9p-header-at 0 7 22 buf) '(:refused :message-too-large))
       (equal (fn-9p-header-at 0 7 6 buf) '(:refused :profile-unrepresentable))
       (equal (fn-9p-header-at 0 7 4294967296 buf)
              '(:refused :profile-unrepresentable)))))
(defthm ninep-header-framing-refusals
 (ninep-header-limit-and-prefix-refusals) :rule-classes nil)

(defun-nx ninep-header-byteorder-mutation-witness ()
 (let* ((buf (fn-octets-from-list '(23 0 0 0 116 52 18) (create-fn-octets)))
        (answer (fn-9p-header-at 0 7 32 buf)))
  (and (fn-octets-p buf)
       (equal answer (fn-9p-header-reference 0 7 32 buf))
       (equal answer '(:header 116 4660 23 7 23))
       ; Wrong big-endian tag interpretation, on the same guarded input.
       (not (equal answer '(:header 116 13330 23 7 23))))))
(defthm ninep-header-byteorder-mutation-refuted
 (ninep-header-byteorder-mutation-witness) :rule-classes nil)

(defun-nx ninep-header-offset-and-short-size ()
 (let* ((buf (fn-octets-from-list '(99 6 0 0 0 116 52 18) (create-fn-octets)))
        (answer (fn-9p-header-at 1 8 32 buf)))
  (and (fn-octets-p buf)
       (equal answer '(:refused :short-message))
       (equal answer (fn-9p-header-reference 1 8 32 buf)))))
(defthm ninep-header-short-declaration-refused
 (ninep-header-offset-and-short-size) :rule-classes nil)
