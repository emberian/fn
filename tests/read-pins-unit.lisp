(in-package "ACL2")
(include-book "../books/assembly")

; The generator's footprint boundary excludes operation-history mutation.
(assert-event
 (and (fn2-core-harvest-bindingsp
        '((fn2-core-extents fn2-extents))
        '((fn2-core-extents :stobj fn2-extents)))
      (not (fn2-core-harvest-bindingsp
        '((fn2-core-ops fn2-ops)) '((fn2-core-ops :stobj fn2-ops))))
      (not (fn2-core-harvest-bindingsp '((missing nil)) nil))
      (not (fn2-core-harvest-bindingsp
        '((fn2-core-extents fn2-extents) (fn2-core-extents fn2-extents))
        '((fn2-core-extents :stobj fn2-extents))))))

(defun fn2-read-pin-test-allocate (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
  (ok extent epoch allocation fn2-extents)
  (b* (((mv begin fn2-extents) (fn2-alloc-begin-epoch 1 fn2-extents))
       ((mv reserve & extent epoch allocation fn2-extents) (fn2-alloc-reserve fn2-extents))
       ((mv commit fn2-extents) (fn2-alloc-commit-allocation extent epoch allocation 1 1 fn2-extents)))
   (mv (and (eq begin :ok) (eq reserve :ok) (eq commit :ok)) extent epoch allocation fn2-extents))
  (mv ok extent epoch allocation fn2-core)))

(defun fn2-read-pin-test-retire (extent epoch allocation fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-extents (fn2-core-extents fn2-core)))
  (ok fn2-extents)
  (b* (((mv retire fn2-extents) (fn2-alloc-retire extent epoch allocation 1 fn2-extents))
       ((mv checkpoint fn2-extents) (fn2-alloc-checkpoint-advance 1 1 fn2-extents)))
   (mv (and (eq retire :ok) (eq checkpoint :ok)) fn2-extents))
  (mv ok fn2-core)))

(defun fn2-read-pin-test-release-code (extent epoch allocation fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-extents (fn2-core-extents fn2-core))
             (fn2-alloc-edges (fn2-core-alloc-edges fn2-core)))
  (code invariant)
  (mv (fn2-alloc-release-code extent epoch allocation fn2-extents)
      (fn2-alloc-ownership-invp fn2-extents fn2-alloc-edges))
  (mv code invariant)))

(defun fn2-read-pin-test-ack (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
  (code fn2-ops) (fn2-outbox-ack 1 fn2-ops) (mv code fn2-core)))

(defun fn2-read-pin-test-post (op gen fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
  (fn2-ops)
  (fn2-post-result 0 op gen *fn2-event-read-result* *fn2-outcome-failed* *fn2-reason-io* 0 0 0 fn2-ops)
  fn2-core))

; The actual BLOCK-READ acquires the pin. Interleave retirement/checkpoint,
; ACK, a stale completion, then the real failed physical completion. Failure
; still excludes physical access and therefore releases the source pin.
; OMIT removes precisely that acquired pin as the hypothesis-removal control;
; the same concrete release preflight then allows reuse while I/O is pending.
(defun fn2-read-pin-test-body (omit fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      ((mv allocated extent epoch allocation fn2-core) (fn2-read-pin-test-allocate fn2-core))
      ((unless allocated) (mv nil fn2-core))
      ((mv pool slot gen fn2-core) (fn2-core-reserve 0 1 0 1 fn2-core))
      ((unless (eq pool :ok)) (mv nil fn2-core))
      ((mv issued op og fn2-core)
       (fn2-block-read (* extent *fn2-commit-write-resources*) epoch allocation 0 1 slot gen 1 0 1 0 fn2-core))
      ((unless (eq issued :ok)) (mv nil fn2-core))
      ((mv retired fn2-core) (fn2-read-pin-test-retire extent epoch allocation fn2-core))
      ((unless retired) (mv nil fn2-core))
      ((mv before invariant) (fn2-read-pin-test-release-code extent epoch allocation fn2-core))
      ((unless (and invariant (fn2-core-wfp fn2-core) (eq before :outstanding-io))) (mv nil fn2-core))
      ((when omit)
       (b* (((mv removed fn2-core)
             (fn2-core-alloc-edges-harvest op og 0 *fn2-event-read-result*
               *fn2-outcome-failed* *fn2-reason-io* 0 0 0 fn2-core))
            ((mv after invariant) (fn2-read-pin-test-release-code extent epoch allocation fn2-core)))
        (mv (and (eq removed :ok) invariant (eq after :ok)) fn2-core)))
      ((mv ack fn2-core) (fn2-read-pin-test-ack fn2-core))
      ((unless (eq ack :ok)) (mv nil fn2-core))
      ((mv after-ack invariant) (fn2-read-pin-test-release-code extent epoch allocation fn2-core))
      ((unless (and invariant (eq after-ack :outstanding-io))) (mv nil fn2-core))
      (fn2-core (fn2-read-pin-test-post op (+ 1 og) fn2-core))
      ((mv stray & & & & & & & & & fn2-core) (fn2-harvest-one fn2-core))
      ((mv after-stray invariant) (fn2-read-pin-test-release-code extent epoch allocation fn2-core))
      ((unless (and (not stray) invariant (eq after-stray :outstanding-io))) (mv nil fn2-core))
      (fn2-core (fn2-read-pin-test-post op og fn2-core))
      ((mv delivered & & & & & & & & & fn2-core) (fn2-harvest-one fn2-core))
      ((mv after invariant) (fn2-read-pin-test-release-code extent epoch allocation fn2-core)))
  (mv (and delivered invariant (eq after :ok) (not (fn2-core-stopped-p fn2-core))) fn2-core)))

(defun fn2-read-pin-test (omit)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-read-pin-test-body omit fn2-core) answer)))
(assert-event (fn2-read-pin-test nil))
(assert-event (fn2-read-pin-test t))
