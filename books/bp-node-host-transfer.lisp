; The BP transfer boundary the native host calls: host/native/bp.lisp, through
; host/bp-node-host.lisp, sends and receives bundles by exactly these
; functions (lane decision-keystones, K4: the entries were :ideal in the host
; file with no theorem about them; here they are guard-verified with their
; keystones).  books/bp-node.lisp decides everything; this book flattens its
; three-way outcome for a host that applies no record accessor, and proves
; that the flattening keeps the three outcomes distinct and hands over the
; ADU only for an acceptance.
(in-package "ACL2")
(include-book "bp-node")

; -----------------------------------------------------------------------------
; Sending.  NIL when the arguments are not what the books' send is defined
; over: a refusal the host reports, never a bundle.

(defun fn-bpn-host-send (config peer adu sequence obs)
  (declare (xargs :guard t))
  (if (and (fn-bpn-configp config) (fn-bpp-eidp peer) (fn-bpb-datap adu)
           (fn-bpp-timep sequence) (fn-clock-observationp obs))
      (fn-bpn-send config peer adu sequence obs)
    nil))

; -----------------------------------------------------------------------------
; Receiving.  The flat result is
;
;   (outcome reason adu payload-length)
;
; with OUTCOME one of :accepted, :refused or :uncertain -- the three kept
; distinct all the way out to the host's exit code -- REASON the book's
; keyword, and ADU the payload octets when there are any.  Arguments that are
; not a configuration, an octet list and a clock observation are refused by
; the name :host-arguments before the books' receive sees them.

(defun fn-bpn-host-receive (config octets obs)
  (declare (xargs :guard t))
  (if (not (and (fn-bpn-configp config) (fn-cbor-octet-listp octets)
                (fn-clock-observationp obs)))
      (list :refused :host-arguments nil 0)
    (let ((r (fn-bpn-receive config octets obs)))
      (cond ((fn-bpn-acceptedp r)
             (list :accepted nil (fn-bpn-received-adu r)
                   (len (fn-bpn-received-adu r))))
            ((fn-bpn-uncertainp r)
             (list :uncertain (fn-bpn-outcome-reason r) nil 0))
            (t (list :refused (fn-bpn-outcome-reason r) nil 0))))))

(defun fn-bpn-host-receive-outcome (r)
  (declare (xargs :guard t))
  (fn-cbor-ag-car r))
(defun fn-bpn-host-receive-reason (r)
  (declare (xargs :guard t))
  (fn-cbor-ag-car (fn-cbor-ag-cdr r)))
(defun fn-bpn-host-receive-adu (r)
  (declare (xargs :guard t))
  (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr r))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-944).  What the host reads is one of the three outcomes and
; nothing else; it is :accepted exactly when the arguments are well formed
; and books/bp-node.lisp accepted, :uncertain exactly when they are well
; formed and the book could not decide; malformed arguments are the refusal
; :host-arguments with no ADU; the ADU is present only for an acceptance,
; where it is the book's received ADU, and every other outcome carries the
; book's reason.  Uncertain, refused and accepted stay distinct at the
; boundary (AGENTS.md); the proof is the case split over
; fn-bpn-receive-yields-one-of-three.

(defthm fn-bpn-host-receive-keeps-the-three-outcomes-distinct
  (let ((r (fn-bpn-host-receive config octets obs))
        (d (fn-bpn-receive config octets obs))
        (wf (and (fn-bpn-configp config) (fn-cbor-octet-listp octets)
                 (fn-clock-observationp obs))))
    (and (member-equal (fn-bpn-host-receive-outcome r)
                       (list :accepted :refused :uncertain))
         (iff (equal (fn-bpn-host-receive-outcome r) :accepted)
              (and wf (fn-bpn-acceptedp d)))
         (iff (equal (fn-bpn-host-receive-outcome r) :uncertain)
              (and wf (fn-bpn-uncertainp d)))
         (implies (not wf) (equal r (list :refused :host-arguments nil 0)))
         (implies (equal (fn-bpn-host-receive-outcome r) :accepted)
                  (equal (fn-bpn-host-receive-adu r) (fn-bpn-received-adu d)))
         (implies (not (equal (fn-bpn-host-receive-outcome r) :accepted))
                  (and (equal (fn-bpn-host-receive-adu r) nil)
                       (implies wf (equal (fn-bpn-host-receive-reason r)
                                          (fn-bpn-outcome-reason d)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use fn-bpn-receive-yields-one-of-three
           :in-theory (e/d (fn-bpn-host-receive fn-bpn-host-receive-outcome
                            fn-bpn-host-receive-adu fn-bpn-host-receive-reason)
                           (fn-bpn-receive fn-bpn-acceptedp fn-bpn-refusedp
                            fn-bpn-uncertainp fn-bpn-received-adu
                            fn-bpn-outcome-reason fn-bpn-configp
                            fn-cbor-octet-listp fn-clock-observationp)))))

; KEYSTONE (PRF-944), the composition at the host's two entries: a bundle
; this node's send authored for a peer, received by that peer's
; configuration and accepted, hands over the ADU that was sent -- through
; fn-bpn-receive-of-send-carries-the-adu (books/bp-node.lisp).  Acceptance
; is the hypothesis because a transfer limit below the wire refuses this very
; bundle (tests/acl2/bp-node-tests.lisp has that witness).

(defthm fn-bpn-host-receive-of-host-send-hands-over-the-adu
  (implies (and (fn-bpn-configp config) (fn-bpn-configp peer-config)
                (fn-bpp-eidp peer) (fn-bpb-datap adu) (fn-bpp-timep sequence)
                (fn-clock-observationp obs) (fn-clock-observationp obs2)
                (equal (fn-bpn-host-receive-outcome
                        (fn-bpn-host-receive
                         peer-config (fn-bpn-host-send config peer adu sequence obs)
                         obs2))
                       :accepted))
           (equal (fn-bpn-host-receive-adu
                   (fn-bpn-host-receive
                    peer-config (fn-bpn-host-send config peer adu sequence obs)
                    obs2))
                  adu))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-receive-of-send-carries-the-adu))
           :in-theory (e/d (fn-bpn-host-receive fn-bpn-host-receive-outcome
                            fn-bpn-host-receive-adu fn-bpn-host-send)
                           (fn-bpn-receive fn-bpn-send fn-bpn-acceptedp
                            fn-bpn-refusedp fn-bpn-uncertainp fn-bpn-received-adu
                            fn-bpn-outcome-reason fn-bpn-configp fn-bpp-eidp
                            fn-bpb-datap fn-bpp-timep
                            fn-cbor-octet-listp fn-clock-observationp)))))
