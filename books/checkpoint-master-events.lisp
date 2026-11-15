; Materialize the actual generated owner after core construction and kind tags.
; Executor genesis creates its sole row; the typed pressure source wakes it.
(in-package "ACL2")
(include-book "checkpoint-master-arms")
(fn2-book-layer :c)
; Reuse the shared declared-child face generator across the actual DSL's
; leaf books. B lifecycle/commit and C snapshot operations already have core
; faces, so a core-form generated actor can compose them without a twin or
; an invented child adapter over the complete core.
(defun fn2-checkpoint-master-face-ops (tree world)
 (declare (xargs :verify-guards nil))
 (if (atom tree) nil
  (let* ((op (car tree)) (row (and (symbolp op) (fn2-arms-op-row op world)))
         (child (and row (fn2-decl-get :child row))))
   (union-eq (and child (function-symbolp child world) (not (function-symbolp op world)) (list op))
    (union-eq (fn2-checkpoint-master-face-ops (car tree) world)
              (fn2-checkpoint-master-face-ops (cdr tree) world))))))
(defun fn2-checkpoint-master-face-events (ops world)
 (declare (xargs :verify-guards nil))
 (if (atom ops) nil
  (append (fn2-arms-op-face-events (car ops) (fn2-decl-get :child (fn2-arms-op-row (car ops) world)) world)
          (fn2-checkpoint-master-face-events (cdr ops) world))))
(defmacro fn2-checkpoint-master-faces ()
 '(make-event
   (value (cons 'progn
    (fn2-checkpoint-master-face-events
     (fn2-checkpoint-master-face-ops
      (cdr (assoc-eq 'fn2-checkpoint-master (table-alist 'fn2-machine-arm-bodies (w state)))) (w state))
     (w state))))))

(defmacro fn2-checkpoint-master-events ()
 '(progn
   (fn2-checkpoint-master-abort-events)
   (fn2-checkpoint-teardown-events)
   (fn2-checkpoint-master-faces)
   (defmachine-arms fn2-checkpoint-master)
   (defun fn2-checkpoint-needed-ready (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (let ((id (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core)))
     (and (not (fn2-core-stopped-p fn2-core))
          (not (equal id *fn2-none*)) (fn2-machine-idp id fn2-core)
          (eq (fn2-checkpoint-master-snapshot-read-code id fn2-core) :ok)
          (equal (fn2-machine-phase id fn2-core) *fn2-checkpoint-master-state-idle*)
          (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-checkpoint-needed*)
          (mv-nth 1 (fn2-checkpoint-master-pressure-op
                     (fn2-checkpoint-master-row-retirement-seen id fn2-core) fn2-core)))))
   (defun fn2-checkpoint-needed-grant (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (if (fn2-checkpoint-needed-ready fn2-core)
        (let* ((id (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core))
               (fn2-core (fn2-machine-write-wait-reason id *fn2-wait-none* fn2-core)))
         (mv id fn2-core))
      (mv *fn2-none* fn2-core)))
   (fn2-core-preserves fn2-checkpoint-needed-grant (fn2-core) :position 1 :rows nil)
   (defthm fn2-checkpoint-needed-ready-id
    (implies (fn2-checkpoint-needed-ready fn2-core)
             (not (equal (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core) *fn2-none*)))
    :hints (("Goal" :in-theory (e/d (fn2-checkpoint-needed-ready)
      (fn2-machine-kind-base fn2-machine-idp fn2-checkpoint-master-pressure-op)))))
   (defthm fn2-checkpoint-needed-grant-live
    (implies (fn2-checkpoint-needed-ready fn2-core)
             (not (equal (mv-nth 0 (fn2-checkpoint-needed-grant fn2-core)) *fn2-none*)))
    :hints (("Goal" :in-theory (e/d (fn2-checkpoint-needed-grant)
      (fn2-checkpoint-needed-ready fn2-machine-write-wait-reason fn2-machine-kind-base)))))
   (defthm fn2-checkpoint-needed-grant-type
    (and (consp (fn2-checkpoint-needed-grant fn2-core))
         (true-listp (fn2-checkpoint-needed-grant fn2-core)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (e/d (fn2-checkpoint-needed-grant)
      (fn2-checkpoint-needed-ready fn2-machine-write-wait-reason)))))
   (in-theory (disable fn2-checkpoint-needed-ready fn2-checkpoint-needed-grant))
   (fn2-wait-attach :checkpoint-needed fn2-checkpoint-needed-grant)
   (defattach (fn2-checkpoint-needed-ready-p fn2-checkpoint-needed-ready)
              (fn2-checkpoint-needed-grant-one fn2-checkpoint-needed-grant)
    :hints (("Goal" :use ((:instance fn2-checkpoint-needed-grant-live)
                          (:instance fn2-checkpoint-needed-grant-wait-kids)
                          (:instance fn2-checkpoint-needed-grant-wait-directory)))))
   (defmachine-run fn2-checkpoint-master)))
