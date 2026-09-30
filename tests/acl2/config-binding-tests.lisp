; Literal descriptor effect at the actual configured prepare entry.
(in-package "ACL2")
(include-book "../../books/node-config")
(include-book "node-binding-fixture")

(defconst *cbt-empty*
  (fn-cnode-initial
   (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*))))
(defconst *cbt-prepared*
  (fn-cnode-prepare *cbt-empty* 1 1 "<configured-bound@example>" 0 '("fn.test")
                    "archive" "content" "release" 4 841000000 *nbft-binding*))

; Complete literal hypothesis and conclusion, executable entry guard, and
; nonempty prospective retention from the actual reachable preparation.
(assert-event
 (and (fn-cnode-statep *cbt-empty*)
      (not (equal *cbt-prepared* *cbt-empty*))
      (fn-ab-p *nbft-binding*)
      (equal (fn-node-stage-binding
              (fn-node-stage (fn-cnode-node *cbt-prepared*))) *nbft-binding*)
      (fn-cnode-statep *cbt-prepared*)
      (equal (len (fn-retain-pins
                   (fn-node-stage-retention
                    (fn-node-stage (fn-cnode-node *cbt-prepared*))))) 1)))

; Removing the sole changed-state premise permits a checked descriptor
; refusal: entry guard holds but the literal descriptor conclusion fails.
(assert-event
 (let ((next (fn-cnode-prepare *cbt-empty* 1 1 "<configured-bound@example>"
                              0 '("fn.test") "archive" "content" "release"
                              4 841000000 :invalid)))
   (and (fn-cnode-statep *cbt-empty*)
        (equal next *cbt-empty*)
        (not (and (fn-ab-p :invalid)
                  (equal (fn-node-stage-binding
                          (fn-node-stage (fn-cnode-node next))) :invalid))))))
