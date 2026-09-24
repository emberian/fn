; N04/N05 forwarding fixtures use actual received kind-5 rows and the outer
; host-called FNBS step.  The later assertions in this book exercise kind
; 6/8/9 once the forwarding extension is present.
(in-package "ACL2")
(include-book "../../books/bp-node-progress")
(include-book "../../books/bp-node-debt")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpfx-local* (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47)))
(defconst *bpfx-sender* (cons :dtn '(47 47 98 112 45 115 101 110 100 101 114 47)))
(defconst *bpfx-dest* (cons :dtn '(47 47 98 112 45 100 101 115 116 47)))
(defconst *bpfx-config* (fn-bpn-config *bpfx-local* 3600000 2 32 1048576))
(defconst *bpfx-sender-config*
  (fn-bpn-config *bpfx-sender* 3600000 2 32 1048576))
(defconst *bpfx-observation* (fn-clock-observation 1000 0 0 nil))
(defconst *bpfx-ingress*
  (list :cl (cons 0 1) 1 *bpfx-sender* '(115 101 110 100 101 114) 0))

; The older entry is inside the 131072-octet held-image bound but cannot fit
; a 32768-octet session MRU.  Its no-fragment flag makes this a real MRU wait
; even when a later fragmentation policy is enabled.  The younger entry fits.
(defconst *bpfx-old-base*
  (fn-bpn-send-bundle *bpfx-sender-config* *bpfx-dest*
                      (make-list 49152 :initial-element 65)
                      7 *bpfx-observation*))
(defconst *bpfx-old-bundle*
  (fn-bpb-make-bundle
   (update-nth 1 *fn-bpp-flag-no-fragment*
               (fn-bpb-bundle-primary *bpfx-old-base*))
   (fn-bpb-bundle-blocks *bpfx-old-base*)
   (fn-bpb-bundle-payload *bpfx-old-base*)))
(defconst *bpfx-new-bundle*
  (fn-bpn-send-bundle *bpfx-sender-config* *bpfx-dest*
                      (make-list 8192 :initial-element 66)
                      8 *bpfx-observation*))
(defconst *bpfx-old-wire* (fn-bpb-encode *bpfx-old-bundle*))
(defconst *bpfx-new-wire* (fn-bpb-encode *bpfx-new-bundle*))

(assert-event
 (and (fn-bpb-bundlep *bpfx-old-bundle*)
      (fn-bpb-bundlep *bpfx-new-bundle*)
      (fn-bpp-no-fragmentp
       (fn-bpp-flags (fn-bpb-bundle-primary *bpfx-old-bundle*)))
      (> (len *bpfx-old-wire*) 32768)
      (<= (len *bpfx-old-wire*) *fn-bpnf-max-held-image*)
      (< (len *bpfx-new-wire*) 32768)
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpfx-config* *bpfx-old-wire* *bpfx-observation* *bpfx-ingress*))
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event
        *bpfx-config* *bpfx-new-wire* *bpfx-observation* *bpfx-ingress*))))

(defun bpfx-durable-receive (st wire)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prepared (fn-bpnf-receive-wire-event
                    *bpfx-config* wire *bpfx-observation* *bpfx-ingress*))
         (proposed (fn-bpnp-step
                    st (fn-bpnf-receive-wire-event-value prepared)))
         (effect (car (fn-bpnf-answer-effects proposed))))
    (if (and (fn-bpnf-receive-wire-readyp prepared)
             (equal (car effect) :persist))
        (fn-bpnf-answer-state
         (fn-bpnp-step
          (fn-bpnf-answer-state proposed)
          (list :persist-result (fn-bpn-nth 1 effect)
                (fn-bpn-nth 2 effect) :durable)))
      st)))

(defconst *bpfx-raw-s0* (fn-bpnf-initial-state *bpfx-config* 8 1048576))
(defconst *bpfx-boot-event*
  (fn-bpnf-family-recover-auto-event *bpfx-raw-s0* nil :ready nil))
(defconst *bpfx-boot* (fn-bpnp-step *bpfx-raw-s0* *bpfx-boot-event*))
(defconst *bpfx-s0* (fn-bpnf-answer-state *bpfx-boot*))
(assert-event
 (and (fn-bpnp-host-eventp *bpfx-boot-event*)
      (equal (car (car (fn-bpnf-answer-effects *bpfx-boot*)))
             :restart-ready)
      (equal (fn-bpnp-used *bpfx-s0*) 0)
      (equal (fn-bpnp-debt *bpfx-s0*) 0)))
(defconst *bpfx-s1* (bpfx-durable-receive *bpfx-s0* *bpfx-old-wire*))
(defconst *bpfx-s2* (bpfx-durable-receive *bpfx-s1* *bpfx-new-wire*))
(defconst *bpfx-old-held* (second (fn-bpnf-held-list *bpfx-s2*)))
(defconst *bpfx-new-held* (first (fn-bpnf-held-list *bpfx-s2*)))

(assert-event
 (and (equal (len (fn-bpnf-held-list *bpfx-s2*)) 2)
      (equal (fn-bpn-nth 3 *bpfx-old-held*) 0)
      (equal (fn-bpn-nth 3 *bpfx-new-held*) 1)
      (not (fn-bpnf-issued *bpfx-s2*))
      (equal (fn-bpnd-held-debt *bpfx-old-held* *bpfx-local*) 2)
      (equal (fn-bpnd-held-debt *bpfx-new-held* *bpfx-local*) 2)))
