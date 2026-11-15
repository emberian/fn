; Atomic reservation of the SAME C binder during successful typed B admission.
(in-package "ACL2")
(include-book "successor-state")
(fn2-book-layer :b)
(defun fn2-successor-bind-claim-reserve
 (tx txgen batch event slot gen len kind owner ogen fn2-succ-txns fn2-id-engine)
 (declare (xargs :stobjs (fn2-succ-txns fn2-id-engine)
  :guard (and (fn2-succ-txns-wfp fn2-succ-txns)
              (fn2-id-engine-wfp fn2-id-engine))))
 (if (not (and (fn2-successor-binder-idle-p fn2-id-engine)
               (unsigned-byte-p 32 tx) (unsigned-byte-p 60 txgen)
               (posp batch) (unsigned-byte-p 60 batch)
               (unsigned-byte-p 60 event)
               (fn2-successor-emit-claim-current-p
                tx txgen slot gen len kind owner ogen fn2-succ-txns)))
     (mv :state fn2-succ-txns fn2-id-engine)
  (let* ((fn2-id-engine
           (fn2-id-engine-put 0 (binding-phase *fn2-succ-binder-phase-admitted*)
            (binding-tx tx) (binding-generation txgen)
            (binding-batch batch) (binding-event event)
            (binding-slot 0) (binding-scan 0)))
         (fn2-succ-txns
           (fn2-succ-txns-put tx (phase *fn2-succ-phase-binding*)
            (batch batch) (event event) (bind-phase *fn2-succ-bind-phase-claimed*)
            (bind-slot 0))))
   (mv :ok fn2-succ-txns fn2-id-engine))))
