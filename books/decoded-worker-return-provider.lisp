; Token-bound actual registered activation return/cancel path. No join receipt.
(in-package "ACL2")
(include-book "decoded-worker-lifecycle")

; Full physical worker address uses a variable LSB path, so registry growth
; never reinterprets an existing address. Reads create no missing child.
; The address is the registered assignment's worker scalar, not the PRS nonce.
(defun fn-dwr-node-transition (token worker address operation fuel fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard (and (fn-pwz-tokenp token) (natp worker) (natp address) (natp fuel))
                 :measure (nfix fuel) :verify-guards nil))
 (cond
  ((zp fuel) (mv :yield fuel fn-pww-node))
  ((zp address)
   (if (not (fn-pww-children-boundp 'fn-pww-carry fn-pww-node))
    (mv :worker-unavailable (- fuel 1) fn-pww-node)
    (stobj-let
     ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
     (word fn-pww-carry)
     (if (not (and (equal worker (fn-pww-id fn-pww-carry))
                   (equal token (fn-pww-token fn-pww-carry))))
      (mv :stale-worker fn-pww-carry)
      (case operation
       (:cancel (fn-dwl-cancel token fn-pww-carry))
       (:activation-return (fn-dwl-activation-return token fn-pww-carry))
       (otherwise (mv :stale-worker fn-pww-carry))))
     (mv word (- fuel 1) fn-pww-node))))
  ((equal (mod address 2) 0)
   (if (not (fn-pww-children-boundp 'fn-pww-left fn-pww-node))
    (mv :worker-unavailable (- fuel 1) fn-pww-node)
    (stobj-let
     ((fn-pww-left (fn-pww-children-get 'fn-pww-left fn-pww-node (create-fn-pww-left))))
     (word left fn-pww-left)
     (fn-dwr-node-transition token worker (floor address 2) operation (- fuel 1) fn-pww-left)
     (mv word left fn-pww-node))))
  (t
   (if (not (fn-pww-children-boundp 'fn-pww-right fn-pww-node))
    (mv :worker-unavailable (- fuel 1) fn-pww-node)
    (stobj-let
     ((fn-pww-right (fn-pww-children-get 'fn-pww-right fn-pww-node (create-fn-pww-right))))
     (word left fn-pww-right)
     (fn-dwr-node-transition token worker (floor address 2) operation (- fuel 1) fn-pww-right)
     (mv word left fn-pww-node))))))

; Future actual outer activation dispatcher supplies its retained token/worker,
; never a row snapshot or returned Boolean. This entry itself establishes no
; physical return: the native calling epilogue must be named and qualified.
(defun fn-dwr-registered-transition (token worker operation fuel fn-page-window-workers)
 (declare (xargs :stobjs fn-page-window-workers :guard (and (fn-pwz-tokenp token) (natp worker) (natp fuel))
                 :verify-guards nil))
 (stobj-let
  ((fn-pww-node (fn-pww-registry fn-page-window-workers)))
  (word left fn-pww-node)
  (fn-dwr-node-transition token worker worker operation fuel fn-pww-node)
  (mv word left fn-page-window-workers)))
