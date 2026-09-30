; Actual retained lifecycle transitions; no last-borrow settlement shortcut.
(in-package "ACL2")
(include-book "decoded-worker-controller")

(defun fn-dwl-cancel (token fn-pww-carry)
 (declare (xargs :stobjs fn-pww-carry :guard t :verify-guards nil))
 (cond
  ((not (and (fn-pwz-tokenp token)
             (equal token (fn-pww-token fn-pww-carry))))
   (mv :stale-decoded-worker fn-pww-carry))
  ((member-eq (fn-pww-phase fn-pww-carry)
              '(:cancelled-running :cancelled-returned))
   (mv :cancelled fn-pww-carry))
  ((eq (fn-pww-phase fn-pww-carry) :returned)
   (let ((fn-pww-carry (update-fn-pww-phase :cancelled-returned fn-pww-carry)))
    (mv :cancelled fn-pww-carry)))
  ((member-eq (fn-pww-phase fn-pww-carry) '(:assigned :initializing :running))
   (let ((fn-pww-carry (update-fn-pww-phase :cancelled-running fn-pww-carry)))
    (mv :cancelled fn-pww-carry)))
  (t (mv :decoded-worker-unavailable fn-pww-carry))))

; Callable only by the actual registered worker activation-return dispatcher,
; after its dynamic bindings unwind. This is not a host supplied JOINED fact.
; It changes only execution phase, retaining every source/alias/charge field.
; Native caller installation and physical-return refinement remain open.
(defun fn-dwl-activation-return (token fn-pww-carry)
 (declare (xargs :stobjs fn-pww-carry :guard t :verify-guards nil))
 (cond
  ((not (and (fn-pwz-tokenp token)
             (equal token (fn-pww-token fn-pww-carry))))
   (mv :stale-decoded-worker fn-pww-carry))
  ((eq (fn-pww-phase fn-pww-carry) :running)
   (let ((fn-pww-carry (update-fn-pww-phase :returned fn-pww-carry)))
    (mv :activation-returned fn-pww-carry)))
  ((eq (fn-pww-phase fn-pww-carry) :cancelled-running)
   (let ((fn-pww-carry (update-fn-pww-phase :cancelled-returned fn-pww-carry)))
    (mv :activation-returned fn-pww-carry)))
  ((member-eq (fn-pww-phase fn-pww-carry) '(:returned :cancelled-returned))
   (mv :already-returned fn-pww-carry))
  (t (mv :decoded-worker-unavailable fn-pww-carry))))

(defun fn-dwl-node-transition (token operation fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-pww-children-boundp 'fn-pww-carry fn-pww-node))
     (mv :decoded-worker-storage-unavailable fn-pww-node)
   (stobj-let
    ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
    (word fn-pww-carry)
    (cond ((eq operation :cancel) (fn-dwl-cancel token fn-pww-carry))
          ((eq operation :activation-return) (fn-dwl-activation-return token fn-pww-carry))
          (t (mv :unsupported-decoded-transition fn-pww-carry)))
    (mv word fn-pww-node))))
