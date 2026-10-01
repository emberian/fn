(in-package "ACL2")
(include-book "../../books/ninep-group-buckets")

; Borrowed immutable source fixture only, not a grant or mounted source.
(defthm ninep-group-buckets-enumeration-full-effect-positive
 (let* ((buckets '(("fn.news" (article0) number0) ("fn.docs" nil number1)))
        (cursor (fn-9pb-groups-begin buckets))
        (first (fn-9pb-groups-step cursor fn-octets))
        (second (fn-9pb-groups-step (mv-nth 2 first) fn-octets)))
  (and (equal first (list :group (car buckets)
                         (list :ninep-groups :enumerate (cdr buckets) nil nil 0 0 1)))
       (equal second (list :group (cadr buckets)
                          '(:ninep-groups :enumerate nil nil nil 0 0 2)))
       (equal (fn-9pb-groups-step (mv-nth 2 second) fn-octets)
              (list :complete nil (mv-nth 2 second)))))
 :rule-classes nil)

(defthm ninep-group-buckets-zero-length-name-terminal-positive
 (let* ((bucket '("" nil number0))
        (cursor (fn-9pb-group-walk-begin (list bucket) 0 0))
        (result (fn-9pb-groups-step cursor fn-octets)))
  (implies (equal (fn-octets-len fn-octets) 0)
   (and (equal result (list :yield nil
                            (list :ninep-groups :compare nil bucket '(0 0) 0 0 0)))
        (equal (fn-9pb-groups-step (mv-nth 2 result) fn-octets)
               (list :group bucket (mv-nth 2 result))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-octets-len))))

(defthm ninep-group-buckets-corrupt-source-refuses-complete-positive
 (let ((cursor (fn-9pb-groups-begin '((not-a-name retained-root)))))
  (equal (fn-9pb-groups-step cursor fn-octets)
         (list :recovery-required nil cursor)))
 :rule-classes nil)

; No host comparison substitutes for the real one-character decision.
(defthm ninep-group-buckets-character-mismatch-full-result
 (let* ((buffer (fn-octets-from-list '(98) (create-fn-octets)))
        (cursor '(:ninep-groups :compare nil ("a" retained-root) (0 1) 0 0 0)))
  (and (fn-octets-p buffer)
       (equal (fn-9pb-groups-step cursor buffer)
              '(:yield nil (:ninep-groups :lookup nil nil (0 1) 0 0 1)))
       (not (equal (mv-nth 0 (fn-9pb-groups-step cursor buffer)) :group))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-octets-p fn-octets-len fn-octets-get))))
