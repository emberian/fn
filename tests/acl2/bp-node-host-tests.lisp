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
