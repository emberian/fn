; Exact private prefix incarnation projection for registered digest install.
; Maintained I/O control reaches DIGEST-START only after the prefix-end
; observation; the revisioned handler must settle that observation before
; exposing this capture. A phase supplied by native is never an authority.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-handler")
(set-verify-guards-eagerness 2)
(defun fn-bpck-control-source-incarnation (payload)
 (declare (xargs :guard t))
 (let ((job (fn-bpck-control-job payload)) (io (fn-bpck-control-io payload)))
  (and (equal (fn-bpn-nth 0 payload) :bp-checkpoint-control)
       (equal (fn-bpn-nth 0 job) :bp-checkpoint-job)
       (fn-bpcc-job-tokenp (fn-bpn-nth 1 job))
       (equal (fn-bpn-nth 6 job) :digest-finish)
       (equal (fn-bpn-nth 11 job) :private)
       (posp (fn-bpn-nth 8 job))
       (<= (fn-bpn-nth 8 job) *fn-bpc-max-uint*)
       (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job)))
       (equal io '(:digest-start :pending))
       (null (fn-bpck-control-action payload))
       (list :bp-checkpoint-stage (fn-bpn-nth 1 job) (fn-bpn-nth 3 job)))))
