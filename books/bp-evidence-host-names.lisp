; The native BP receiver's next result-evidence name, in a certified book
; (was host/bp-receive-evidence-host.lisp's): before authorizing the
; allocation (host/native/bp.lisp), the host asks which final name the next
; record of this outcome would take, to observe it absent; a state or
; outcome the books do not recognize names nothing, so a corrupt tally never
; names record 0.  Guard-verified shim over fn-bpn-evidence-next-result-name
; (bp-receive-evidence), with the keystone.
(in-package "ACL2")
(include-book "bp-receive-evidence")

(defun fn-bpn-host-evidence-next-result-name (st outcome)
  (declare (xargs :guard t))
  (if (and (fn-bpn-evidence-statep st)
           (fn-bpn-evidence-outcomep outcome))
      (fn-bpn-evidence-next-result-name st outcome)
    nil))

; KEYSTONE.  Two-sided: a name is answered exactly when the state is an
; evidence state and the outcome one of the three; then it is a string, the
; evidence name of the state's next sequence under the outcome's result
; kind (the name the authorization will publish).
(defthm fn-bpn-host-evidence-next-result-name-names-exactly-the-next-record
  (let ((name (fn-bpn-host-evidence-next-result-name st outcome)))
    (and (iff name
              (and (fn-bpn-evidence-statep st)
                   (fn-bpn-evidence-outcomep outcome)))
         (implies name
                  (and (stringp name)
                       (equal name
                              (fn-bpn-evidence-name
                               (fn-bpn-evidence-next st)
                               (fn-bpn-evidence-result-kind outcome)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bpn-host-evidence-next-result-name
                                   fn-bpn-evidence-next-result-name
                                   fn-bpn-evidence-name)
                                  (fn-bpn-evidence-statep
                                   fn-bpn-evidence-outcomep
                                   fn-bpn-evidence-next
                                   fn-bpn-evidence-result-kind
                                   fn-bpn-evidence-name-chars)))))
