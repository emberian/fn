; The probe scenario's raw-Lisp driver (LEAN-METATHEORY §6): live stobjs created and initialized
; on the tiny profile, row fields set through the generated setters, each child-form arm and
; handler of the probe kinds called directly (so record-arms.lisp's wrappers see every call).
; Loaded after record-arms.lisp in a world that includes meta/emit/meta-probe. Test-only I/O.
(in-package "ACL2")

(defun mp-profile () (eval '*fn2-profile-tiny*))

(defun mp-children (kind rows)
  ; a fresh tuple: the kind's table with ROWS rows, the directory, pool, ops and control
  (let ((p (mp-profile)))
    (list (cons kind (funcall (meta-sym kind "-INIT") rows (funcall (meta-sym "CREATE-" kind))))
          (cons 'fn2-machines (fn2-machines-init p (create-fn2-machines)))
          (cons 'fn2-pool (fn2-pool-init (fn2-profile-pool-classes p) (fn2-profile-generation-start p)
                                         (fn2-profile-generation-limit p) (create-fn2-pool)))
          (cons 'fn2-ops (fn2-ops-init p (create-fn2-ops)))
          (cons 'fn2-control (fn2-control-init p (create-fn2-control))))))

(defun mp-set (kids kind slot field v)
  (funcall (meta-sym kind "-SET-" field) slot v (cdr (assoc kind kids))))

(defun mp-call (fn kids vals)
  ; VALS fill the value formals in order; the stobj formals take the tuple's live children
  (let* ((ins (stobjs-in fn (w *the-live-state*)))
         (args (loop for s in ins collect (if s (cdr (assoc s kids)) (pop vals)))))
    (multiple-value-list (apply fn args))))

(defun mp-arm (kind tag fields &key (id 0) (slot 0) (budget 4096) (rows 4))
  ; one call of KIND's run arm TAG on a fresh tuple whose row SLOT has FIELDS ((field . v) ...)
  (let ((kids (mp-children kind rows))
        (fn (fn2-arms-child-name (fn2-arms-fn-name kind "-RUN-" tag))))
    (dolist (f fields) (mp-set kids kind slot (car f) (cdr f)))
    (format t "~&META PROBE ~s ~s => ~s~%" fn fields
            (subseq (mp-call fn kids (list id slot 7 0 budget)) 0 4))))

(defun mp-observe (kind tag fields obs &key (id 0) (slot 0) (rows 4))
  ; one call of KIND's handler TAG; OBS = (event outcome reason count aux0 aux1)
  (let ((kids (mp-children kind rows))
        (fn (fn2-arms-child-name (fn2-arms-fn-name kind "-ON-" tag))))
    (dolist (f fields) (mp-set kids kind slot (car f) (cdr f)))
    (format t "~&META PROBE ~s ~s => ~s~%" fn fields
            (car (mp-call fn kids (list* id slot 7 0 obs))))))

(defun meta-probe-run ()
  (let ((none (eval '*fn2-none*)))
    ;; fn2-arms-probe: a kind's own stop, the plain path, :wake-row + :goto close with its :issue
    (mp-arm 'fn2-arms-probe :work '((count . 100)))
    (mp-arm 'fn2-arms-probe :work `((count . 5) (target . ,none)))
    (mp-arm 'fn2-arms-probe :work '((count . 5) (target . 1)))
    (mp-arm 'fn2-arms-probe :work '((count . 5) (target . 1) (cap-index . 0) (cap-nonce . 0)) :id 2 :slot 1)
    ;; :repeat: four passes, then the :until stopping early
    (mp-arm 'fn2-arms-probe :loop '((count . 0)))
    (mp-arm 'fn2-arms-probe :loop '((count . 8)))
    (mp-arm 'fn2-arms-probe :loop '((count . 10)))
    ;; accept-hand: no hand to take, and a target row
    (mp-arm 'fn2-arms-probe :take `((target . ,none)))
    (mp-arm 'fn2-arms-probe :take '((target . 1)))
    (mp-arm 'fn2-arms-probe :wait nil)
    (mp-arm 'fn2-arms-probe :free nil)
    (mp-arm 'fn2-arms-probe :done nil)
    (mp-observe 'fn2-arms-probe :close-result '((pending . 1)) '(0 0 0 0 0 0))
    ;; fn2-arms-probe6: an operation without :ok, accepted and routed
    (mp-arm 'fn2-arms-probe6 :work '((count . 0)))
    (mp-arm 'fn2-arms-probe6 :work '((count . 1)))
    ;; fn2-meta-probe: the park variants and :do :when
    (mp-arm 'fn2-meta-probe :pool '((class . 0)))
    (mp-arm 'fn2-meta-probe :pool '((class . 1)))
    (mp-arm 'fn2-meta-probe :seal nil)
    (mp-arm 'fn2-meta-probe :admit '((target . 0)))
    (mp-arm 'fn2-meta-probe :admit '((target . 1)))
    (mp-arm 'fn2-meta-probe :skip '((class . 0) (count . 0)))
    (mp-arm 'fn2-meta-probe :skip '((class . 0) (count . 1)))
    (mp-arm 'fn2-meta-probe :skip '((class . 1) (count . 0)))
    (mp-arm 'fn2-meta-probe :casing '((count . 0)))
    (mp-arm 'fn2-meta-probe :casing '((count . 5)))
    (mp-arm 'fn2-meta-probe :halting nil)
    (mp-observe 'fn2-meta-probe :receive-result nil '(0 0 0 0 0 0))
    (mp-arm 'fn2-meta-probe :free nil)
    (mp-arm 'fn2-meta-probe :done nil)))
