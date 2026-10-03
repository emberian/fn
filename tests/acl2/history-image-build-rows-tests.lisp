; PRF-1265 teeth: literal antecedents/conclusions and discrimination between
; appended all-event rows, corrupted logical history, and malformed custody.
(in-package "ACL2")
(include-book "../../books/history-image-build-rows")

(local (in-theory (enable fn-hrs-img-ok fn-hp-vhold-is-x)))
(defconst *hibr-empty*
  '( (nil nil nil nil nil nil) nil 0 0 0
     (0 0 0 0 0) (1 1 1 1 1) 0 0 nil 0 0))
(defconst *hibr-event* '(:other 7 nil))

; Reachable positive: actual beginning followed by the host-called row step.
(defthm hibr-row-positive
  (let* ((c (fn-his-build-begin 0 *hibr-empty*))
         (n (mv-nth 1 (fn-his-build-row *hibr-event* c))))
    (and (fn-hrc-wfp c) (fn-hrs-rel nil c)
         (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
         (equal (mv-nth 0 (fn-his-build-row *hibr-event* c)) :ok)
         (fn-hrc-wfp n) (fn-hrs-rel (list *hibr-event*) n)
         (equal (fn-hrc-lo n) 0) (equal (fn-hrc-hi n) 0)
         (equal (fn-hrc-sfxi 0 n) nil)
         (equal (fn-hrc-sfx-length n) 16)))
  :rule-classes nil)

; A pending suffix refuses before any append and keeps exact state.
(defconst *hibr-pending* (update-nth 11 1 (update-nth 9 (list *hibr-event*) *hibr-empty*)))
(defthm hibr-pending-positive
  (let* ((c *hibr-pending*) (n (mv-nth 1 (fn-his-build-row :later c))))
    (and (fn-hrc-wfp c) (fn-hrs-rel (list *hibr-event*) c)
         (not (and (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)))
         (equal (mv-nth 0 (fn-his-build-row :later c)) '(:refused :pending-suffix))
         (fn-hrc-wfp n) (equal n c)))
  :rule-classes nil)

; Hypothesis removal: actual beginning is well formed but the claimed
; logical history contains a ghost row. The literal append conclusion fails.
(defthm hibr-row-rel-removal
  (let* ((c (fn-his-build-begin 0 *hibr-empty*))
         (h '(:ghost))
         (n (mv-nth 1 (fn-his-build-row *hibr-event* c))))
    (and (fn-hrc-wfp c) (not (fn-hrs-rel h c))
         (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
         (not (fn-hrs-rel (append h (list *hibr-event*)) n))))
  :rule-classes nil)

; Hypothesis removal: retained relation is true (empty suffix), but the
; suffix window is backwards. Refusal keeps the corrupted shape, so the
; literal theorem's shape conclusion fails.
(defthm hibr-row-wfp-removal
  (let ((c (update-nth 10 3 *hibr-empty*)))
    (and (not (fn-hrc-wfp c)) (fn-hrs-rel nil c)
         (not (fn-hrc-wfp (mv-nth 1 (fn-his-build-row :later c))))))
  :rule-classes nil)
