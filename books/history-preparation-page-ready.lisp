; Before durability, inspect the actual existing append leaf. This read never
; creates a child or writes a row. The durable publisher performs the append.
(in-package "ACL2")
(include-book "history-event-provider")

(defun fn-hpr-page-ready (epoch id incarnation base expected fn-history-event-page)
 (declare (xargs :stobjs fn-history-event-page :guard t))
 (cond ((not (and (fn-hec-matches epoch id incarnation fn-history-event-page)
                  (equal base (fn-hec-base fn-history-event-page))
                  (natp expected)
                  (equal expected (fn-hec-committed fn-history-event-page)))) :stale)
       ((>= (fn-hec-committed fn-history-event-page) 256) :constructor-required)
       (t :append-ready)))

(defun fn-hpr-node-ready (slot depth epoch id incarnation base expected fuel fn-hep-node)
 (declare (xargs :stobjs fn-hep-node :measure (nfix depth)
                 :guard (and (natp slot) (natp depth) (natp fuel))
                 :verify-guards nil))
 (cond ((<= fuel depth) (mv :yield fuel))
       ((and (zp depth) (not (equal slot 0))) (mv :unavailable fuel))
       ((zp depth)
        (if (not (fn-hep-node-presentp 'fn-history-event-page fn-hep-node))
            (mv :constructor-required fuel)
         (stobj-let ((fn-history-event-page
           (fn-hep-node-children-get 'fn-history-event-page fn-hep-node
                                    (create-fn-history-event-page))))
          (word)
          (fn-hpr-page-ready epoch id incarnation base expected fn-history-event-page)
          (mv word (1- fuel)))))
       ((equal (mod slot 2) 0)
        (if (not (fn-hep-node-presentp 'fn-hep-left fn-hep-node))
            (mv :constructor-required fuel)
         (stobj-let ((fn-hep-left
           (fn-hep-node-children-get 'fn-hep-left fn-hep-node (create-fn-hep-left))))
          (word left)
          (fn-hpr-node-ready (floor slot 2) (1- depth) epoch id incarnation
                             base expected (1- fuel) fn-hep-left)
          (mv word left))))
       (t
        (if (not (fn-hep-node-presentp 'fn-hep-right fn-hep-node))
            (mv :constructor-required fuel)
         (stobj-let ((fn-hep-right
           (fn-hep-node-children-get 'fn-hep-right fn-hep-node (create-fn-hep-right))))
          (word left)
          (fn-hpr-node-ready (floor slot 2) (1- depth) epoch id incarnation
                             base expected (1- fuel) fn-hep-right)
          (mv word left))))))
(verify-guards fn-hpr-node-ready)
