; PRF1303: actual host-called one-frame source parser/control composition.
(in-package "ACL2")
(include-book "tcpcl-source-control")
(include-book "tcpcl-received-source")

; The concrete one-byte KEEP frame refines the original session transition,
; including all events, unconsumed input and the driver's scheduling status.
; No whole-session or arbitrary clock hypothesis is needed for this identity.
(defthm fn-tclsctl-source-drive-keepalive-refines-session
 (implies (fn-tcl-transferringp (fn-tcl-session-phase s))
  (equal (fn-tcl-host-source-drive s (cons 4 rest) now)
   (let ((r (fn-tcl-step s (fn-tcl-make-keepalive) now)))
    (list (fn-tcl-result-session r) (fn-tcl-result-events r) rest :stepped))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-tcl-host-source-drive fn-tcl-step-source fn-tcl-decode-for
                fn-tcl-decode-message fn-tcl-transferringp fn-tcl-make-keepalive
                fn-tcl-msg-kind)
               (fn-tcl-step fn-tcl-segment-mru)))))

; The actual source driver preserves the retained inbound record and observes
; reception, while consuming exactly that control frame and retaining the rest. Native private roots,
; END ACK gating and physical aliases remain the separate composed obligation.
(defthm fn-tclsctl-source-drive-keepalive-preserves-custody-and-reception
 (implies (fn-tcl-transferringp (fn-tcl-session-phase s))
  (let ((r (fn-tcl-host-source-drive s (cons 4 rest) now)))
   (and (equal (fn-tcl-session-inbound (car r)) (fn-tcl-session-inbound s))
        (equal (fn-tcl-session-last-rx (car r)) now)
        (equal (caddr r) rest)
        (equal (cadddr r) :stepped))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-tclsctl-source-drive-keepalive-refines-session)
                (:instance fn-tclsctl-received-keepalive-preserves-inbound)
                (:instance fn-tclsctl-received-keepalive-records-actual-reception))
          :in-theory (e/d (fn-tcl-transferringp)
                          (fn-tcl-host-source-drive fn-tcl-step
                           fn-tclsctl-received-keepalive-preserves-inbound
                           fn-tclsctl-received-keepalive-records-actual-reception)))))
