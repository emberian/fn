; Registered persistent worker storage source candidate. No public installer.
; Declaration/default construction is not funded capacity or a worker grant.
; The actual selected installer must reserve the SAME-pool constructor claim
; before creating any path/child, and retain partial construction on faults.
(in-package "ACL2")
(include-book "page-window-executor")
(include-book "extent-window-stream")
(set-verify-guards-eagerness 2)

; The carry and all three buffers occupy the SAME address in this registry.
; The immutable borrow root is the CURRENT query custody root, not a native
; supplied row. Ordinary metadata reads never export a buffer child.
(defstobj fn-pww-carry
  (fn-pww-id :type (integer 0 *) :initially 0)
  (fn-pww-token :initially nil)
  (fn-pww-phase :initially :uninstalled)
  (fn-pww-root :initially nil)
  (fn-pww-storage-receipt :initially nil)
  (fn-pww-borrow-phase :initially :none)
  (fn-pww-input-capacity :type (integer 0 *) :initially 0)
  (fn-pww-controller :initially nil)
  (fn-pww-source-incarnation :initially nil)
  (fn-pww-observation :initially nil)
  (fn-pww-pending-action :initially nil)
  (fn-pww-action-revision :type (integer 0 *) :initially 0)
  :inline t)

; Fixed keys: left/right/carry/input/digest/window. Logical missing-child
; reads are refused before GET. Selected raw GET default-creator lowering,
; table creation and image defaults remain separate runtime obligations.
(defstobj fn-pww-node
  (fn-pww-children :type (stobj-table 16))
  :inline t)
(defstobj fn-pww-left
  (fn-pwwl-children :type (stobj-table 16))
  :congruent-to fn-pww-node :inline t)
(defstobj fn-pww-right
  (fn-pwwr-children :type (stobj-table 16))
  :congruent-to fn-pww-node :inline t)

(defstobj fn-page-window-workers
  (fn-pww-installation :initially nil)
  (fn-pww-registry :type fn-pww-node)
  :inline t)

; Internal metadata fence. TOKEN comes from the actual CURRENT query root
; in the acquire/epilogue parent. It is not a native worker-row snapshot.
; This function does not claim that :returned proves last-alias settlement.
(defun fn-pww-carry-read (token fn-pww-carry)
  (declare (xargs :stobjs fn-pww-carry :guard t))
  (cond
   ((eq (fn-pww-phase fn-pww-carry) :uninstalled)
    (mv :worker-storage-unavailable nil nil nil))
   ((not (and (fn-pwx-tokenp token)
              (equal token (fn-pww-token fn-pww-carry))))
    (mv :stale-worker nil nil nil))
   ((eq (fn-prl-nth 0 token) :decoded-window)
    ; Input/digest/requested-window alone are not the decoder's private
    ; ring/table/output/source custody. Keep that distinct family closed.
    (mv :decoded-worker-storage-unavailable nil nil nil))
   ((eq (fn-pww-phase fn-pww-carry) :fenced)
    (mv :worker-fenced nil nil nil))
   ((not (member-eq (fn-pww-phase fn-pww-carry)
                   '(:assigned :running :returned :cancelled-running
                     :cancelled-returned)))
    (mv :worker-storage-unavailable nil nil nil))
   (t
    (mv :worker-current (fn-pww-id fn-pww-carry)
        (fn-pww-phase fn-pww-carry) (fn-pww-root fn-pww-carry)))))

; Presence is checked for all actual retained children before selecting the
; carry. It does not install them, bless their capacity, or release U.
(defun fn-pww-storage-boundp (fn-pww-node)
  (declare (xargs :stobjs fn-pww-node :guard t))
  (and (fn-pww-children-boundp 'fn-pww-carry fn-pww-node)
       (fn-pww-children-boundp 'fn-octets fn-pww-node)
       (fn-pww-children-boundp 'pgs-digest-state fn-pww-node)
       (fn-pww-children-boundp 'fn-ew-buffer fn-pww-node)))

(defun fn-pww-storage-read (token fn-pww-node)
  (declare (xargs :stobjs fn-pww-node :guard t))
  (if (not (fn-pww-storage-boundp fn-pww-node))
      (mv :worker-storage-unavailable nil nil nil)
    (stobj-let
     ((fn-pww-carry
       (fn-pww-children-get 'fn-pww-carry fn-pww-node
                            (create-fn-pww-carry))))
     (word id phase root)
     (fn-pww-carry-read token fn-pww-carry)
     (mv word id phase root))))

; No initializer, free-worker selection, issued-token assignment, return
; observation, last-borrow transition or native callback is exported here.
; Those must be actual source-derived serialized parents over this SAME
; registry and pool; an installation-shaped record is not their authority.
