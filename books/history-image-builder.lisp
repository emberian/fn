; The native incremental history builder, composed with the existing commit.
(in-package "ACL2")
(include-book "history-image-build-rows")
(include-book "history-image-snapshot")

(defun fn-his-build-finish (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory
                    (union-theories '(fn-his-plan-okp-true-listp
                                      fn-his-true-listp-lpages natp (:e natp)
                                      true-listp (:e true-listp))
                                    (theory 'minimal-theory))))))
  (if (not (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
      (mv (list :refused :suffix) nil nil fn-hrecs$c)
    (let ((lpages (fn-his-lpages fn-hrecs$c)))
      (mv-let (res fn-hrecs$c) (fn-his-commit fn-hrecs$c)
        (if (not (fn-his-plan-okp res))
            (mv (if (consp res) res (list :refused :commit)) nil nil fn-hrecs$c)
          (mv :ok (nth 1 res) (fn-his-plan-writes lpages res) fn-hrecs$c))))))
