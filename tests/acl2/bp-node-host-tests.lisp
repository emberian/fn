; The native BP command's exact mixed article/transport result policy.
(in-package "ACL2")
(include-book "../../host/bp-node-host")
(include-book "../../books/codec-attach")

; The native BP command's mixed article/transport result (fnn-bp-exit-code,
; host/native/bp.lisp): one complete article was refused while the TCPCL
; session was lost after it existed.  The run is :interrupted (exit 6), not
; refused; had a publication in the delivery callback been uncertain, it is
; :fenced (exit 3, recovery required).
(assert-event
 (equal (fn-bprc-run-exit-code
         (fn-bprc-note (fn-bprc-note (fn-bprc-empty) :refused)
                       (fn-bprc-session-evidence :uncertain nil)))
        6))
(assert-event
 (equal (fn-bprc-run-exit-code
         (fn-bprc-note (fn-bprc-note (fn-bprc-empty) :refused)
                       (fn-bprc-session-evidence :uncertain t)))
        3))
; Each domain can independently raise the run result; a session with no
; adverse outcome records nothing.
(assert-event
 (equal (fn-bprc-run-exit-code
         (fn-bprc-note (fn-bprc-note (fn-bprc-empty) :uncertain)
                       (fn-bprc-session-evidence :accepted nil)))
        6))
(assert-event
 (equal (fn-bprc-run-exit-code
         (fn-bprc-note (fn-bprc-empty) (fn-bprc-session-evidence :refused nil)))
        1))
(assert-event
 (equal (fn-bprc-run-exit-code
         (fn-bprc-note (fn-bprc-empty) (fn-bprc-session-evidence nil nil)))
        0))
; Invalid evidence fails closed, as a fence.
(assert-event (equal (fn-bprc-run-exit-code '(0 -1 0 0)) 3))
(assert-event (equal (fn-bprc-session-evidence :garbled nil) :fenced))

; `bp send` RETRY: a durable authored wire is re-offered with its own
; identity, and only when ACL2 finds it is this node's bundle for this ADU to
; this peer under its sequence's authored-wire name.
(defun bpnh-test-octets (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (atom chars) nil
    (cons (char-code (car chars)) (bpnh-test-octets (cdr chars)))))

(defconst *bpnh-test-config*
  (fn-bpn-host-config
   (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://fn-a/" 'list)))
   3600000 2 32 1048576))
(defconst *bpnh-test-peer*
  (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://dtn7d/incoming" 'list))))
(defconst *bpnh-test-adu* (bpnh-test-octets (coerce "fn-a article" 'list)))
(defconst *bpnh-test-wire*
  (fn-bpn-host-send *bpnh-test-config* *bpnh-test-peer* *bpnh-test-adu* 7
                    (fn-bpn-host-observation 5 812345678 0 t)))
(defconst *bpnh-test-wire-no-clock*
  (fn-bpn-host-send *bpnh-test-config* *bpnh-test-peer* *bpnh-test-adu* 3
                    (fn-bpn-host-observation 5 0 0 nil)))

; The reachable witness: the original creation time and sequence, from the
; wire, with a wall clock and without one (creation time 0).
(assert-event
 (equal (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                    *bpnh-test-adu* "authored-7.wire"
                                    *bpnh-test-wire*)
        '(812345678 7)))
(assert-event
 (equal (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                    *bpnh-test-adu* "authored-3.wire"
                                    *bpnh-test-wire-no-clock*)
        '(0 3)))

; Each condition refuses on its own: another ADU, another peer, another
; node, a name that is not this sequence's, and a truncated wire.
(assert-event
 (null (fn-bpn-host-authored-retry
        *bpnh-test-config* *bpnh-test-peer*
        (bpnh-test-octets (coerce "another article" 'list))
        "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry
        *bpnh-test-config*
        (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://other/incoming" 'list)))
        *bpnh-test-adu* "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry
        (fn-bpn-host-config
         (fn-bpn-host-eid (bpnh-test-octets (coerce "dtn://fn-b/" 'list)))
         3600000 2 32 1048576)
        *bpnh-test-peer* *bpnh-test-adu* "authored-7.wire" *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                   *bpnh-test-adu* "authored-8.wire"
                                   *bpnh-test-wire*)))
(assert-event
 (null (fn-bpn-host-authored-retry *bpnh-test-config* *bpnh-test-peer*
                                   *bpnh-test-adu* "authored-7.wire"
                                   (butlast *bpnh-test-wire* 1))))

; -----------------------------------------------------------------------------
; Teeth for books/bp-node-host-transfer.lisp (PRF-944): the receive boundary
; over a bundle this node's own send authored, as the host composes it.
; Reachable positive witness: the complete antecedent of
; fn-bpn-host-receive-of-host-send-hands-over-the-adu by name, the outcome
; :accepted, and the ADU handed over.
(defconst *bnh-a* (cons :dtn '(47 47 102 110 45 97 47)))     ; dtn://fn-a/
(defconst *bnh-b* (cons :dtn '(47 47 102 110 45 98 47)))     ; dtn://fn-b/
(defconst *bnh-config-a* (fn-bpn-host-config *bnh-a* 3600000 2 32 1048576))
(defconst *bnh-config-b* (fn-bpn-host-config *bnh-b* 3600000 2 32 1048576))
(defconst *bnh-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bnh-obs-later* (fn-clock-observation 4000 0 0 nil))
(defconst *bnh-adu* '(104 101 108 108 111))                  ; "hello"
(defconst *bnh-wire* (fn-bpn-host-send *bnh-config-a* *bnh-b* *bnh-adu* 7 *bnh-obs*))
(defconst *bnh-received*
  (fn-bpn-host-receive *bnh-config-b* *bnh-wire* *bnh-obs-later*))
(assert-event (and (fn-bpn-configp *bnh-config-a*) (fn-bpn-configp *bnh-config-b*)
                   (fn-bpp-eidp *bnh-b*) (fn-bpb-datap *bnh-adu*) (fn-bpp-timep 7)
                   (fn-clock-observationp *bnh-obs*)
                   (fn-clock-observationp *bnh-obs-later*)
                   (fn-cbor-octet-listp *bnh-wire*)))
(assert-event (equal (fn-bpn-host-receive-outcome *bnh-received*) :accepted))
(assert-event (equal (fn-bpn-host-receive-adu *bnh-received*) *bnh-adu*))
(assert-event (equal (fn-bpn-host-receive-reason *bnh-received*) nil))
(assert-event (equal *bnh-received* (list :accepted nil *bnh-adu* 5)))
; Hypothesis removal, the wire: the ADU itself offered as the transfer is not
; a bundle; the outcome is :refused with the book's reason and no ADU.
(defconst *bnh-refused*
  (fn-bpn-host-receive *bnh-config-b* *bnh-adu* *bnh-obs-later*))
(assert-event (equal (fn-bpn-host-receive-outcome *bnh-refused*) :refused))
(assert-event (equal (fn-bpn-host-receive-adu *bnh-refused*) nil))
(assert-event (and (fn-bpn-host-receive-reason *bnh-refused*)
                   (equal (fn-bpn-host-receive-reason *bnh-refused*)
                          (fn-bpn-outcome-reason
                           (fn-bpn-receive *bnh-config-b* *bnh-adu*
                                           *bnh-obs-later*)))))
; Hypothesis removal, well-formed arguments: no configuration, or no clock
; observation, is the refusal :host-arguments, never an acceptance.
(assert-event (equal (fn-bpn-host-receive nil *bnh-wire* *bnh-obs-later*)
                     (list :refused :host-arguments nil 0)))
(assert-event (equal (fn-bpn-host-receive *bnh-config-b* *bnh-wire* nil)
                     (list :refused :host-arguments nil 0)))
(assert-event (equal (fn-bpn-host-send nil *bnh-b* *bnh-adu* 7 *bnh-obs*) nil))
; The :uncertain arm's reachable witness is fn-bpn-receive's
; (*bpn-undecidable*, tests/acl2/bp-node-tests.lisp); the flattening of that
; arm is the keystone's third conjunct.
(assert-event (equal (symbol-class 'fn-bpn-host-receive (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpn-host-send (w state))
                     :common-lisp-compliant))
