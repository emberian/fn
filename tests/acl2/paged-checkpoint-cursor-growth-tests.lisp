; Configuration growth must update the retained cursor, not just the live owner.
(in-package "ACL2")
(include-book "paged-checkpoint-cursor-tests")
(assert-event
 (let* ((old-configs (list *fn-cfg-default-record*))
        (old (fn-sco-capture old-configs (list *sfi-t-undertake* *sfi-t-release*)))
        (r (fn-sco-cpr old))
        (rest (nthcdr (fn-sco-at 2 r) old-configs))
        (out (pckc-raw-resume r rest *pckc-delta* (fn-sfi-carry old)))
        (expected (fn-sco-cpr-resume r *sfi-t-configs* *pckc-delta*)))
   (and (equal r *pckc-r*)
        (equal rest nil)
        (equal (nthcdr (fn-sco-at 2 r) *sfi-t-configs*)
               (list *sfi-t-decrease* *sfi-t-increase*))
        (fn-sco-pausedp (car out))
        (fn-sco-pausedp expected)
        (not (equal (car out) expected)))))

(must-fail-checked
 (assert-event
  (let* ((old-configs (list *fn-cfg-default-record*))
         (old (fn-sco-capture old-configs (list *sfi-t-undertake* *sfi-t-release*)))
         (r (fn-sco-cpr old)))
    (equal (car (pckc-raw-resume r nil *pckc-delta* (fn-sfi-carry old)))
           (fn-sco-cpr-resume r *sfi-t-configs* *pckc-delta*)))))
