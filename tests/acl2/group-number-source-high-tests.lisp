(in-package "ACL2")
(include-book "../../books/group-number-source-high")
; Positive literal high propagation through two distinct assigned groups.
(assert-event
 (let* ((members '(("a" . 8) ("b" . 1)))
        (root (fn-gns-group-set "a" 0 0 (fn-gns-group-value 7 nil) nil)))
   (and (fn-gns-membershipsp members)
        (equal (fn-gns-group-value-high
                 (fn-gns-group-get "a" 0 0 (fn-gns-memberships-root members 0 root)))
               (max (fn-gns-group-value-high (fn-gns-group-get "a" 0 0 root))
                    (fn-gns-member-high "a" members))))))
; Positive literal complete one-set antecedent and conclusion.
(assert-event
 (and (or (stringp "a") (stringp "a")) (natp 8)
      (equal (fn-gns-group-value-high
               (fn-gns-group-get "a" 0 0
                 (fn-gns-group-set "a" 0 0 (fn-gns-group-value 8 nil) nil)))
             (if (equal "a" "a") 8
               (fn-gns-group-value-high (fn-gns-group-get "a" 0 0 nil))))))
; Hypothesis removal for membership fold: invalid first member stops runtime
; fold, whereas later matching metadata would affect the logical max.
(assert-event
 (let ((members '((7 . 1) ("a" . 8))))
   (and (not (fn-gns-membershipsp members))
        (not (equal (fn-gns-group-value-high
                      (fn-gns-group-get "a" 0 0 (fn-gns-memberships-root members 0 nil)))
                     (max (fn-gns-group-value-high (fn-gns-group-get "a" 0 0 nil))
                          (fn-gns-member-high "a" members)))))))
; Logical guard-external removals, other retained hypothesis affirmatively
; checked; these do not call malformed source states on a served path.
(defthm fn-tgnh-key-domain-hypothesis-removal
 (and (not (or (stringp 7) (stringp 7))) (natp 8)
      (not (equal (fn-gns-group-value-high
                    (fn-gns-group-get 7 0 0
                      (fn-gns-group-set 7 0 0 (fn-gns-group-value 8 nil) nil)))
                   (if (equal 7 7) 8
                     (fn-gns-group-value-high (fn-gns-group-get 7 0 0 nil))))))
 :rule-classes nil)
(defthm fn-tgnh-high-type-hypothesis-removal
 (and (or (stringp "a") (stringp "a")) (not (natp -1))
      (not (equal (fn-gns-group-value-high
                    (fn-gns-group-get "a" 0 0
                      (fn-gns-group-set "a" 0 0 (fn-gns-group-value -1 nil) nil)))
                   (if (equal "a" "a") -1
                     (fn-gns-group-value-high (fn-gns-group-get "a" 0 0 nil))))))
 :rule-classes nil)
