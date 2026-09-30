; Guarded registered RH-to-query terminal source component, uninstalled.
(in-package "ACL2")
(include-book "render-window-terminal-slot")
(include-book "served-render-holder")

; Reads never create missing registry nodes. Existing-child raw GET lowering
; and the caller's allocation BODY still need their selected-runtime envelope.
(defun fn-prwt-node-step (token fuel address depth fn-ibp-node fn-page-read-pool)
  (declare (xargs :stobjs (fn-ibp-node fn-page-read-pool)
                  :measure (nfix depth)
                  :guard (and (fn-ibp-query-tokenp token) (natp fuel)
                              (natp address) (natp depth))
                  :verify-guards nil))
  (cond
   ((<= fuel depth) (mv :yield nil fuel fn-ibp-node fn-page-read-pool))
   ((zp depth)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-query-segment fn-ibp-node))
        (mv :unavailable nil fuel fn-ibp-node fn-page-read-pool)
      (stobj-let ((fn-ibp-query-segment
                   (fn-ibp-node-children-get 'fn-ibp-query-segment fn-ibp-node
                                             (create-fn-ibp-query-segment))))
       (word receipt left fn-ibp-query-segment fn-page-read-pool)
       (fn-prwt-slot-step token (- fuel 1) fn-ibp-query-segment fn-page-read-pool)
       (mv word receipt left fn-ibp-node fn-page-read-pool))))
   ((equal (mod address 2) 0)
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-left fn-ibp-node))
        (mv :unavailable nil fuel fn-ibp-node fn-page-read-pool)
      (stobj-let ((fn-ibp-node-left
                   (fn-ibp-node-children-get 'fn-ibp-node-left fn-ibp-node
                                             (create-fn-ibp-node-left))))
       (word receipt left fn-ibp-node-left fn-page-read-pool)
       (fn-prwt-node-step token (- fuel 1) (floor address 2) (- depth 1)
                          fn-ibp-node-left fn-page-read-pool)
       (mv word receipt left fn-ibp-node fn-page-read-pool))))
   (t
    (if (not (fn-ibp-node-children-boundp 'fn-ibp-node-right fn-ibp-node))
        (mv :unavailable nil fuel fn-ibp-node fn-page-read-pool)
      (stobj-let ((fn-ibp-node-right
                   (fn-ibp-node-children-get 'fn-ibp-node-right fn-ibp-node
                                             (create-fn-ibp-node-right))))
       (word receipt left fn-ibp-node-right fn-page-read-pool)
       (fn-prwt-node-step token (- fuel 1) (floor address 2) (- depth 1)
                          fn-ibp-node-right fn-page-read-pool)
       (mv word receipt left fn-ibp-node fn-page-read-pool))))
))

(verify-guards fn-prwt-node-step
 :hints (("Goal" :in-theory
          (disable fn-prwt-slot-step fn-ibp-node-children-get
                   fn-ibp-node-children-boundp fn-ibp-nodep
                   fn-page-read-poolp))))

; Native supplies fuel and actual stobjs only. The full query identity is
; obtained from RH, and the selected nested child checks its CURRENT ticket.
; No root7->cursor or cursor->settlement authority is manufactured here.
(defun fn-rh-window-terminal-step
 (fuel fn-render-holder fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-render-holder fn-mio$c fn-page-read-pool)
                 :guard (natp fuel) :verify-guards nil))
 (let ((token (fn-rh-query fn-render-holder)))
  (if (not (and (fn-rh-live fn-render-holder) (fn-ibp-query-tokenp token)))
      (mv :unavailable nil fuel fn-mio$c fn-page-read-pool)
   (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
    (word receipt left fn-index-backing fn-page-read-pool)
    (let ((depth (fn-ibp-slot-depth fn-index-backing))
          (capacity (fn-ibp-pool-capacity fn-index-backing))
          (address (- (nth 2 token) 1)))
     (if (not (and (natp depth) (natp capacity) (< address capacity)))
         (mv :unavailable nil fuel fn-index-backing fn-page-read-pool)
      (stobj-let ((fn-ibp-node (fn-ibp-registry fn-index-backing)))
       (word receipt left fn-ibp-node fn-page-read-pool)
       (fn-prwt-node-step token fuel address depth fn-ibp-node fn-page-read-pool)
       (mv word receipt left fn-index-backing fn-page-read-pool))))
    (mv word receipt left fn-mio$c fn-page-read-pool)))))

; Allocation, original/partial root custody and actual epilogue settlement
; remain distinct obligations. This internal step returns no terminal receipt,
; never clears qs-inputs and never releases C/U/A or an ATS allocating turn.

(verify-guards fn-rh-window-terminal-step
 :hints (("Goal" :in-theory
          (e/d (fn-ibp-query-tokenp)
               (fn-prwt-node-step fn-mio$cp fn-index-backingp
                fn-page-read-poolp fn-ibp-nodep)))))
