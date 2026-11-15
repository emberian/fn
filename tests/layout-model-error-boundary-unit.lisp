; Executable ORIGINAL baseline witness for layout2060684e, before model repair.
; Typed/owned malformed padding makes generated STEP return fault NEXT while
; the original generic model wrapper returns OFF. Do not revise this control
; into the repaired expectation; retain it with its original source key.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/layout")
(deflayout fn2-model-error-fixture '((a :u8) (padding (:zero 2))))

(defun fn2-model-error-fields (fn2-fields)
 (declare (xargs :stobjs fn2-fields :verify-guards nil))
 (list (fn2-fields-value 0 fn2-fields) (fn2-fields-ref-slot 0 fn2-fields)
       (fn2-fields-ref-gen 0 fn2-fields) (fn2-fields-ref-off 0 fn2-fields)
       (fn2-fields-ref-len 0 fn2-fields) (fn2-fields-status 0 fn2-fields)
       (fn2-fields-value 1 fn2-fields) (fn2-fields-ref-slot 1 fn2-fields)
       (fn2-fields-ref-gen 1 fn2-fields) (fn2-fields-ref-off 1 fn2-fields)
       (fn2-fields-ref-len 1 fn2-fields) (fn2-fields-status 1 fn2-fields)))

(defun fn2-model-error-case (fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* ((fn2-fields (fn2-fields-init 8 fn2-fields))
      (fn2-pool (fn2-pool-init '((1 . 16)) 1 100 fn2-pool))
      ((mv reserved slot gen fn2-pool) (fn2-pool-reserve 0 1 0 1 fn2-pool))
      ((mv w0 fn2-pool) (fn2-pool-write slot gen 0 7 1 0 1 fn2-pool))
      ((mv w1 fn2-pool) (fn2-pool-write slot gen 1 0 1 0 1 fn2-pool))
      ((mv w2 fn2-pool) (fn2-pool-write slot gen 2 9 1 0 1 fn2-pool))
      (premise (and (eq reserved :ok) (eq w0 :ok) (eq w1 :ok) (eq w2 :ok)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-poolp fn2-pool) (fn2-pool-semanticp fn2-pool)
        (eq (fn2-layout-range-code slot gen 0 3 nil 1 0 1 fn2-pool) :ok)
        (<= *fn2-model-error-fixture-num-fields* (fn2-fields-rows fn2-fields))))
      (before (fn2-model-error-fields fn2-fields))
      ((mv model model-next fn2-fields)
       (fn2-layout-decode-run '((a :u8) (padding (:zero 2))) slot gen 0 3 1 0 1 4096 nil fn2-fields fn2-pool))
      (model-rollback (equal before (fn2-model-error-fields fn2-fields)))
      (fn2-fields (fn2-fields-init 8 fn2-fields))
      (fn2-fields (fn2-model-error-fixture-start 0 fn2-fields))
      ((mv concrete concrete-next fn2-fields)
       (fn2-model-error-fixture-decode-step 0 slot gen 0 3 1 0 1 4096 fn2-fields fn2-pool))
      (concrete-rollback (equal before (fn2-model-error-fields fn2-fields))))
  (mv (list premise model model-next concrete concrete-next model-rollback concrete-rollback)
      fn2-fields fn2-pool)))

(defun fn2-model-error-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (result fn2-fields)
   (with-local-stobj fn2-pool
    (mv-let (result fn2-fields fn2-pool) (fn2-model-error-case fn2-fields fn2-pool)
     (mv result fn2-fields))) result)))

(assert-event
 (equal (fn2-model-error-test)
        '(t :nonzero-padding 0 :nonzero-padding 3 t t)))
