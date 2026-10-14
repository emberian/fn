; OW4: inspect the admitted world, including events emitted by macros.
(in-package "ACL2")

(defmacro fn-one-world-assert-attach-table ()
  (let ((creator-check
         '(assert-event
           (let* ((generic (access absstobj-info
                                   (getpropc 'ow4-g 'absstobj-info nil (w state))
                                   :absstobj-tuples))
                  (impl (access absstobj-info
                                (getpropc 'ow4-i 'absstobj-info nil (w state))
                                :absstobj-tuples))
                  (g-creator (assoc-eq 'ow4-gc generic))
                  (i-creator (assoc-eq 'ow4-ic impl)))
             (or (and (consp g-creator) (consp i-creator)
                      (equal (caddr g-creator) (caddr i-creator)))
                 (prog2$ (cw "OW4 creator mismatch for ~x0: generic ~x1, implementation ~x2.~%"
                             '(ow4-g . ow4-i) g-creator i-creator)
                         nil))))))
    `(with-guard-checking-event
      :none
      (progn
        (assert-event
         (let* ((actual (merge-sort-lexorder
                         (table-alist 'attach-stobj-table (w state))))
                (expected '((fn-arena . fn-arena-extent)
                            (fn-cat . fn-cat-paged)
                            (fn-hist . fn-hist-paged))))
           (or (equal actual expected)
               (prog2$ (cw "OW4 attachment table mismatch: actual ~x0; expected ~x1.~%"
                           actual expected)
                       nil))))
        ,(sublis '((ow4-g . fn-arena) (ow4-i . fn-arena-extent)
                   (ow4-gc . create-fn-arena) (ow4-ic . create-fn-arena-extent))
                 creator-check)
        ,(sublis '((ow4-g . fn-cat) (ow4-i . fn-cat-paged)
                   (ow4-gc . create-fn-cat) (ow4-ic . create-fn-cat-paged))
                 creator-check)
        ,(sublis '((ow4-g . fn-hist) (ow4-i . fn-hist-paged)
                   (ow4-gc . create-fn-hist) (ow4-ic . create-fn-hist-paged))
                 creator-check)))))
