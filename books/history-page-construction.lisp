; One privately owned fixed child/page construction per call. Existing pages
; are never reinitialized and no history row is appended by this mechanism.
(in-package "ACL2")
(include-book "history-event-provider")

(defun fn-hpc-node-one (slot depth epoch id incarnation base fuel fn-hep-node)
 (declare (xargs :stobjs fn-hep-node :measure (nfix depth) :verify-guards nil
   :guard (and (natp slot) (natp depth) (posp epoch) (posp id)
               (natp incarnation) (natp base) (natp fuel))))
 (cond
  ((<= fuel depth) (mv :yield fuel fn-hep-node))
  ((and (zp depth) (not (equal slot 0)))
   (mv :route-depth-required fuel fn-hep-node))
  ((equal slot 0)
   (stobj-let ((fn-history-event-page
     (fn-hep-node-children-get 'fn-history-event-page fn-hep-node
                              (create-fn-history-event-page))))
    (word fn-history-event-page)
    (if (and (fn-hec-matches epoch id incarnation fn-history-event-page)
             (equal base (fn-hec-base fn-history-event-page))
             (equal 0 (fn-hec-committed fn-history-event-page)))
        (mv :page-ready fn-history-event-page)
     (mv-let (word fn-history-event-page)
      (fn-hec-initialize epoch id incarnation base fn-history-event-page)
      (mv (if (eq word :initialized) :page-ready word) fn-history-event-page)))
    (mv word (- fuel 1) fn-hep-node)))
  ((equal (mod slot 2) 0)
   (if (not (fn-hep-node-presentp 'fn-hep-left fn-hep-node))
       (stobj-let ((fn-hep-left
         (fn-hep-node-children-get 'fn-hep-left fn-hep-node (create-fn-hep-left))))
        (fn-hep-left) fn-hep-left
        (mv :constructed (- fuel 1) fn-hep-node))
    (stobj-let ((fn-hep-left
      (fn-hep-node-children-get 'fn-hep-left fn-hep-node (create-fn-hep-left))))
     (word left fn-hep-left)
     (fn-hpc-node-one (floor slot 2) (- depth 1) epoch id incarnation base
                       (- fuel 1) fn-hep-left)
     (mv word left fn-hep-node))))
  (t
   (if (not (fn-hep-node-presentp 'fn-hep-right fn-hep-node))
       (stobj-let ((fn-hep-right
         (fn-hep-node-children-get 'fn-hep-right fn-hep-node (create-fn-hep-right))))
        (fn-hep-right) fn-hep-right
        (mv :constructed (- fuel 1) fn-hep-node))
    (stobj-let ((fn-hep-right
      (fn-hep-node-children-get 'fn-hep-right fn-hep-node (create-fn-hep-right))))
     (word left fn-hep-right)
     (fn-hpc-node-one (floor slot 2) (- depth 1) epoch id incarnation base
                       (- fuel 1) fn-hep-right)
     (mv word left fn-hep-node))))))
(verify-guards fn-hpc-node-one)
