; Readonly CURRENT pending-job projection for core installer composition.
; This projection is not a runtime allowance or a native CURRENT export.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-payload-directory")

(defun fn-bpcc-segment-pending-capture (controller slot fn-bpc-segment)
  (declare (xargs :stobjs fn-bpc-segment :verify-guards nil
                  :guard (and (natp slot) (< slot 64))))
  (let* ((row (fn-bpcs-rowsi slot fn-bpc-segment))
         (token (fn-bpn-nth 0 (fn-bpn-nth 4 row))))
    (if (not (and (fn-bpc-tokenp controller)
                  (equal (mod (caddr controller) 64) slot)
                  (fn-bpc-row-livep (cadr controller) row)
                  (fn-bpcc-job-tokenp token)
                  (equal (caddr token) controller)))
        (mv :stale-checkpoint nil nil nil nil nil nil)
      (mv-let (word current claim payload phase revision)
        (fn-bpcc-segment-payload-read token slot fn-bpc-segment)
        (if (eq word :checkpoint-current)
            (mv word token current claim payload phase revision)
          (mv word nil nil nil nil nil nil))))))

(defun fn-bpcc-node-pending-capture (controller slot physical-segment depth fuel fn-bpc-node)
  (declare (xargs :stobjs fn-bpc-node :measure (nfix depth)
                  :verify-guards nil
                  :guard (and (natp slot) (< slot 64) (natp physical-segment)
                              (natp depth) (natp fuel))))
  (cond
   ((<= fuel depth)
    (mv :yield nil nil nil nil nil nil fuel))
   ((zp depth)
    (if (not (fn-bpcn-children-boundp 'fn-bpc-segment fn-bpc-node))
        (mv :controller-unavailable nil nil nil nil nil nil (- fuel 1))
      (stobj-let ((fn-bpc-segment
                  (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node
                                       (create-fn-bpc-segment))))
        (word token current claim payload phase revision)
        (fn-bpcc-segment-pending-capture controller slot fn-bpc-segment)
        (mv word token current claim payload phase revision (- fuel 1)))))
   ((equal (mod physical-segment 2) 0)
    (if (not (fn-bpcn-children-boundp 'fn-bpc-left fn-bpc-node))
        (mv :controller-unavailable nil nil nil nil nil nil (- fuel 1))
      (stobj-let ((fn-bpc-left
                  (fn-bpcn-children-get 'fn-bpc-left fn-bpc-node
                                       (create-fn-bpc-left))))
        (word token current claim payload phase revision left)
        (fn-bpcc-node-pending-capture controller slot (floor physical-segment 2)
                                     (- depth 1) (- fuel 1) fn-bpc-left)
        (mv word token current claim payload phase revision left))))
   (t
    (if (not (fn-bpcn-children-boundp 'fn-bpc-right fn-bpc-node))
        (mv :controller-unavailable nil nil nil nil nil nil (- fuel 1))
      (stobj-let ((fn-bpc-right
                  (fn-bpcn-children-get 'fn-bpc-right fn-bpc-node
                                       (create-fn-bpc-right))))
        (word token current claim payload phase revision left)
        (fn-bpcc-node-pending-capture controller slot (floor physical-segment 2)
                                     (- depth 1) (- fuel 1) fn-bpc-right)
        (mv word token current claim payload phase revision left))))))

(local
 (defthm fn-bpcc-pending-address-ranges
   (implies (natp address)
            (and (natp (mod address 64)) (< (mod address 64) 64)
                 (natp (floor address 64))))
   :hints (("Goal" :in-theory (disable mod floor)))))

(defun fn-bpcc-pending-capture (controller fuel fn-bp-controller-registry)
  (declare (xargs :stobjs fn-bp-controller-registry :verify-guards nil
                  :guard (natp fuel)))
  (if (not (and (fn-bpc-tokenp controller)
                (< (caddr controller) (fn-bpcr-highwater fn-bp-controller-registry))))
      (mv :stale-controller nil nil nil nil nil nil fuel)
    (let ((depth (fn-bpcr-depth fn-bp-controller-registry)))
      (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
        (word token current claim payload phase revision left)
        (fn-bpcc-node-pending-capture controller (mod (caddr controller) 64)
                                     (floor (caddr controller) 64) depth fuel fn-bpc-node)
        (mv word token current claim payload phase revision left)))))

(verify-guards fn-bpcc-segment-pending-capture
 :hints (("Goal" :in-theory (enable fn-bpc-tokenp fn-bpcc-job-tokenp))))
(verify-guards fn-bpcc-node-pending-capture)
(verify-guards fn-bpcc-pending-capture
 :hints (("Goal" :in-theory (disable mod floor)
                 :use ((:instance fn-bpcc-pending-address-ranges
                                  (address (caddr controller)))))))

(defthm fn-bpcc-node-pending-capture-keeps-fuel-domain
  (implies (and (natp depth) (natp fuel))
           (let ((left (mv-nth 7 (fn-bpcc-node-pending-capture
                                  controller slot physical-segment depth fuel fn-bpc-node))))
             (and (natp left) (<= left fuel))))
  :hints (("Goal" :induct (fn-bpcc-node-pending-capture
                           controller slot physical-segment depth fuel fn-bpc-node)
                  :in-theory (e/d (fn-bpcc-node-pending-capture)
                                  (fn-bpcc-segment-pending-capture
                                   fn-bpcn-children-get fn-bpcn-children-boundp
                                   create-fn-bpc-left create-fn-bpc-right
                                   create-fn-bpc-segment))))
  :rule-classes nil)

(defthm fn-bpcc-pending-capture-keeps-fuel-domain
  (implies (and (natp fuel) (natp (fn-bpcr-depth fn-bp-controller-registry)))
           (let ((left (mv-nth 7 (fn-bpcc-pending-capture
                                  controller fuel fn-bp-controller-registry))))
             (and (natp left) (<= left fuel))))
  :hints (("Goal" :in-theory (e/d (fn-bpcc-pending-capture)
                                  (fn-bpcc-node-pending-capture))
                  :use ((:instance fn-bpcc-node-pending-capture-keeps-fuel-domain
                           (slot (mod (caddr controller) 64))
                           (physical-segment (floor (caddr controller) 64))
                           (depth (fn-bpcr-depth fn-bp-controller-registry))
                           (fn-bpc-node (fn-bpcr-root fn-bp-controller-registry))))))
  :rule-classes nil)
