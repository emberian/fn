; One actual lazy constructor per source turn. No public allowance gate.
(in-package "ACL2")
(include-book "decoded-worker-controller")

(defun fn-dwf-next-child (fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t))
 (cond
  ((not (fn-pww-children-boundp 'fn-octets fn-pww-node)) 'fn-octets)
  ((not (fn-pww-children-boundp 'pgs-digest-state fn-pww-node)) 'pgs-digest-state)
  ((not (fn-pww-children-boundp 'fn-zin-st fn-pww-node)) 'fn-zin-st)
  ((not (fn-pww-children-boundp 'fn-zin-win fn-pww-node)) 'fn-zin-win)
  ((not (fn-pww-children-boundp 'fn-zin-tab fn-pww-node)) 'fn-zin-tab)
  ((not (fn-pww-children-boundp 'fn-zin-out fn-pww-node)) 'fn-zin-out)
  ((not (fn-pww-children-boundp 'fn-ew-buffer fn-pww-node)) 'fn-ew-buffer)
  (t nil)))

; INTERNAL only. CURRENT storage-constructing must have been published by
; a genuine SAME-pool issuer before this factory becomes callable. This
; packet supplies neither that issuer nor an installed role/BODY allowance.
(defun fn-dwf-prepare (token kind fn-pww-carry)
 (declare (xargs :stobjs fn-pww-carry :guard t :verify-guards nil))
 (cond
  ((not (and (fn-pwz-tokenp token)
             (equal token (fn-pww-token fn-pww-carry))
             (eq (fn-pww-phase fn-pww-carry) :storage-constructing)))
   (mv :decoded-factory-unavailable fn-pww-carry))
  ((and (consp (fn-pww-observation fn-pww-carry))
        (eq (car (fn-pww-observation fn-pww-carry)) :constructor-intent))
   ; Unknown prior constructor outcome is debt, never a retry instruction.
   (mv :decoded-constructor-uncertain fn-pww-carry))
  ((not kind) (mv :decoded-storage-present fn-pww-carry))
  (t
   (let ((fn-pww-carry (update-fn-pww-observation
                        (list :constructor-intent token kind) fn-pww-carry)))
    (mv :constructor-intent fn-pww-carry)))))

(defun fn-dwf-node-one (token fn-pww-node)
 (declare (xargs :stobjs fn-pww-node :guard t :verify-guards nil))
 (if (not (fn-pww-children-boundp 'fn-pww-carry fn-pww-node))
     (mv :decoded-factory-unavailable fn-pww-node)
   (let ((kind (fn-dwf-next-child fn-pww-node)))
    (mv-let (word fn-pww-node)
     (stobj-let
      ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
      (word fn-pww-carry)
      (fn-dwf-prepare token kind fn-pww-carry)
      (mv word fn-pww-node))
     (if (not (eq word :constructor-intent))
         (mv word fn-pww-node)
       (let ((fn-pww-node
              (case kind
               (fn-octets
                (stobj-let ((fn-octets (fn-pww-children-get 'fn-octets fn-pww-node (create-fn-octets))))
                 (fn-octets)
                 fn-octets
                 fn-pww-node))
               (pgs-digest-state
                (stobj-let ((pgs-digest-state (fn-pww-children-get 'pgs-digest-state fn-pww-node (create-pgs-digest-state))))
                 (pgs-digest-state)
                 pgs-digest-state
                 fn-pww-node))
               (fn-zin-st
                (stobj-let ((fn-zin-st (fn-pww-children-get 'fn-zin-st fn-pww-node (create-fn-zin-st))))
                 (fn-zin-st)
                 fn-zin-st
                 fn-pww-node))
               (fn-zin-win
                (stobj-let ((fn-zin-win (fn-pww-children-get 'fn-zin-win fn-pww-node (create-fn-zin-win))))
                 (fn-zin-win)
                 fn-zin-win
                 fn-pww-node))
               (fn-zin-tab
                (stobj-let ((fn-zin-tab (fn-pww-children-get 'fn-zin-tab fn-pww-node (create-fn-zin-tab))))
                 (fn-zin-tab)
                 fn-zin-tab
                 fn-pww-node))
               (fn-zin-out
                (stobj-let ((fn-zin-out (fn-pww-children-get 'fn-zin-out fn-pww-node (create-fn-zin-out))))
                 (fn-zin-out)
                 fn-zin-out
                 fn-pww-node))
               (fn-ew-buffer
                (stobj-let ((fn-ew-buffer (fn-pww-children-get 'fn-ew-buffer fn-pww-node (create-fn-ew-buffer))))
                 (fn-ew-buffer)
                 fn-ew-buffer
                 fn-pww-node))
               (otherwise fn-pww-node))))
        ; Only definite constructor return clears the retained intent. A cut
        ; before this write leaves an unavailable constructor-intent row.
        (stobj-let
         ((fn-pww-carry (fn-pww-children-get 'fn-pww-carry fn-pww-node (create-fn-pww-carry))))
         (fn-pww-carry)
         (update-fn-pww-observation (list :constructor-returned token kind) fn-pww-carry)
         (mv :decoded-child-created fn-pww-node))))))))
