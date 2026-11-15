; Whole formulas stay fixed; output observers compose through opaque calls.
(in-package "ACL2")
(include-book "../books/format-check")

; Exact old statement for a single direct carrier, including its full H.
(assert-event
 (equal
  (caddr (fn2-fc-shape-event 'sample '(sample fn2-fields)
           '(and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))
           '((fn2-fields nil))))
  '(implies (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))
    (and (fn2-fieldsp (sample fn2-fields))
         (fn2-fields-wfp (sample fn2-fields))
         (equal (fn2-fields-rows (sample fn2-fields)) (fn2-fields-rows fn2-fields))))))

; Preserve zero/nonzero MV indices and B3's additional words-length facet.
(assert-event
 (equal
  (caddr (fn2-fc-shape-event 'sample '(sample fn2-pool fn2-b3) '(actual-hyp x)
           '((fn2-pool 0) (fn2-b3 2))))
  '(implies (actual-hyp x)
    (and (fn2-poolp (mv-nth 0 (sample fn2-pool fn2-b3)))
         (fn2-pool-wfp (mv-nth 0 (sample fn2-pool fn2-b3)))
         (equal (fn2-pool-rows (mv-nth 0 (sample fn2-pool fn2-b3))) (fn2-pool-rows fn2-pool))
         (fn2-b3p (mv-nth 2 (sample fn2-pool fn2-b3)))
         (fn2-b3-wfp (mv-nth 2 (sample fn2-pool fn2-b3)))
         (equal (fn2-b3-rows (mv-nth 2 (sample fn2-pool fn2-b3))) (fn2-b3-rows fn2-b3))
         (equal (len (nth *fn2-b3-wordsi* (mv-nth 2 (sample fn2-pool fn2-b3))))
                (len (nth *fn2-b3-wordsi* fn2-b3)))))))

; The output list, not a fixed five-table list, selects the disabled observers.
(assert-event
 (equal
  (fn2-fc-shape-event 'sample '(sample x) t '((fn2-pool 4) (extra-table 7)))
  `(defthm sample
    (implies t (and ,@(fn2-fc-shape-claims '((fn2-pool 4) (extra-table 7)) '(sample x))))
    :hints (("Goal" :in-theory
      (disable fn2-digestsp fn2-digests-wfp fn2-fcp fn2-fc-wfp fn2-fc-contextp fn2-fc-context-wfp
               fn2-b3p fn2-b3-wfp fn2-fieldsp fn2-fields-wfp fn2-poolp fn2-pool-wfp
               length char len fn2-pool-rows extra-table-rows)))))))

(defun fn2-shape-observer-leaf (i value fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp i)
              (< i (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 value))))
 (fn2-fields-set-value i value fn2-fields))
(fn2-fc-shape fn2-shape-observer-leaf-shape
 (fn2-shape-observer-leaf i value fn2-fields)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp i)
      (< i (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 value))
 ((fn2-fields nil)))
(in-theory (disable fn2-shape-observer-leaf))
(defun fn2-shape-observer-wrapper (i value fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp i)
              (< i (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 value))))
 (fn2-shape-observer-leaf i value fn2-fields))
(fn2-fc-shape fn2-shape-observer-wrapper-shape
 (fn2-shape-observer-wrapper i value fn2-fields)
 (and (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (natp i)
      (< i (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 value))
 ((fn2-fields nil)))
(assert-event (eq (symbol-class 'fn2-shape-observer-wrapper (w state)) :common-lisp-compliant))
