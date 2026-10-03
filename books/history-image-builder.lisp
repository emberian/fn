; The native incremental history builder, composed with the existing commit.
(in-package "ACL2")
(include-book "history-image-build-rows")
(include-book "history-image-row-step")
(include-book "history-image-snapshot")

(defun fn-his-build-source-count (records)
  (declare (xargs :guard (true-listp records)))
  (len records))

(defun fn-his-build-finish (expected-count fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp expected-count) (fn-hrc-wfp fn-hrecs$c))
                  :guard-hints (("Goal" :in-theory
                    (union-theories '(fn-his-plan-okp-true-listp
                                      fn-his-true-listp-lpages natp (:e natp)
                                      true-listp (:e true-listp))
                                    (theory 'minimal-theory))))))
  (if (not (equal (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
      (mv (list :refused :suffix) nil nil (fn-hrc-nimg fn-hrecs$c) fn-hrecs$c)
    (if (not (equal expected-count (fn-hrc-nimg fn-hrecs$c)))
        (mv (list :refused :image-count) nil nil (fn-hrc-nimg fn-hrecs$c) fn-hrecs$c)
      (let ((lpages (fn-his-lpages fn-hrecs$c)))
      (mv-let (res fn-hrecs$c) (fn-his-commit fn-hrecs$c)
        (if (not (fn-his-plan-okp res))
            (mv (if (consp res) res (list :refused :commit)) nil nil
                (fn-hrc-nimg fn-hrecs$c) fn-hrecs$c)
          (mv :ok (nth 1 res) (fn-his-plan-writes lpages res)
              (fn-hrc-nimg fn-hrecs$c) fn-hrecs$c)))))))
