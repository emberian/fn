; BP semantic payload ownership for actual SAME-pool digest installation.
; Shape does not grant authority: token/claim/allowance are issued/derived by
; the physical allocator against installed source/runtime, never native inputs.
(in-package "ACL2")
(include-book "bp-checkpoint-source-incarnation")
(set-verify-guards-eagerness 2)

; Intent6 = tag/token/phase/immutable-source/actual-claim/selected-allowance.
(defun fn-bpdi-make (token phase source claim allowance)
 (declare (xargs :guard t))
 (list :bp-digest-install-intent token phase source claim allowance))
(defun fn-bpdi-token (intent) (declare (xargs :guard t)) (fn-bpn-nth 1 intent))
(defun fn-bpdi-phase (intent) (declare (xargs :guard t)) (fn-bpn-nth 2 intent))
(defun fn-bpdi-source (intent) (declare (xargs :guard t)) (fn-bpn-nth 3 intent))
(defun fn-bpdi-claim (intent) (declare (xargs :guard t)) (fn-bpn-nth 4 intent))
(defun fn-bpdi-allowance (intent) (declare (xargs :guard t)) (fn-bpn-nth 5 intent))
(defun fn-bpdi-payload-intent (payload)
 (declare (xargs :guard t))
 (let ((intent (fn-bpck-control-digest payload)))
  (and (equal (fn-bpn-nth 0 payload) :bp-checkpoint-control)
       (equal (fn-bpn-nth 0 intent) :bp-digest-install-intent) intent)))
(defun fn-bpdi-with-intent (payload intent)
 (declare (xargs :guard t))
 (fn-bpck-control-make (fn-bpck-control-job payload) (fn-bpck-control-io payload)
                      intent (fn-bpck-control-action payload)))

; Bounded matching of the actual registered identifiers, not receipt authority.
(defun fn-bpdi-token-matches-jobp (token controller job)
 (declare (xargs :guard t))
 (and (consp token) (eq (car token) :bp-digest)
      (consp (cdr token)) (natp (cadr token))
      (consp (cddr token)) (consp (cdddr token)) (null (cddddr token))
      (fn-bpc-tokenp controller) (fn-bpcc-job-tokenp job)
      (equal (caddr token) controller) (equal (cadddr token) job)
      (equal (caddr job) controller)))
