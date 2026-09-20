; ACL2 wrappers for the native host's BPv7 node (RFC 9171).
;
; host/native/bp.lisp calls exactly these, through `fnn-call', and opens no
; bundle record of its own.  Every value that decides anything -- whether a
; string is an endpoint ID, what creation timestamp goes on the wire, whether
; a received transfer is a bundle, whether it is in lifetime, whether its hop
; count has passed its limit, what its ADU is -- is computed here by
; books/bp-node.lisp and books/bp-bundle.lisp.  The raw host contributes the
; socket, one clock reading per wakeup and the durability barrier, and nothing
; else (AGENTS.md, "one owner per decision, and it is ACL2").
;
; Results are flat lists so that the host never applies a record accessor.

(in-package "ACL2")
(include-book "../books/bp-node")

; -----------------------------------------------------------------------------
; Endpoint IDs from the command line.
;
; The host hands over the URI's octets; the scheme prefix is matched here, so
; the host does not decide what "dtn:" means.  Section 4.2.5.1.1 requires the
; complete scheme-specific part, "//node/demux", which is what remains after
; the four octets of "dtn:".

(defun fn-bpn-host-eid (uri)
  (if (and (fn-cbor-octet-listp uri)
           (equal (nth 0 uri) 100)      ; d
           (equal (nth 1 uri) 116)      ; t
           (equal (nth 2 uri) 110)      ; n
           (equal (nth 3 uri) 58))      ; :
      (let ((e (cons :dtn (nthcdr 4 uri))))
        (if (fn-bpp-eidp e) e nil))
    nil))

(defun fn-bpn-host-eidp (e)
  (and (fn-bpp-eidp e) t))

(defun fn-bpn-host-node-idp (e)
  (and (fn-bpp-previous-nodep e) t))

; -----------------------------------------------------------------------------
; Configuration.  NIL when the operator's numbers are not a configuration:
; a refusal, distinct from a node.

(defun fn-bpn-host-config (node-id lifetime crc-type hop-limit transfer-limit)
  (let ((c (fn-bpn-config node-id lifetime crc-type hop-limit transfer-limit)))
    (if (fn-bpn-configp c) c nil)))

(defun fn-bpn-host-configp (c)
  (and (fn-bpn-configp c) t))

; -----------------------------------------------------------------------------
; The clock observation.  The host has a monotonic millisecond reading and,
; when the operator supplied one, a DTN wall reading with its error bound.
; The observation is built here so that its shape is the books'.

(defun fn-bpn-host-observation (monotonic wall wall-error has-wall)
  (let ((obs (fn-clock-observation monotonic wall wall-error (if has-wall t nil))))
    (if (fn-clock-observationp obs) obs nil)))

; -----------------------------------------------------------------------------
; Sending.  NIL when the ADU or the peer is not one this node can address;
; otherwise the octets of one complete BPv7 bundle.

(defun fn-bpn-host-send (config peer adu sequence obs)
  (if (and (fn-bpn-configp config) (fn-bpp-eidp peer) (fn-bpb-datap adu)
           (fn-bpp-timep sequence) (fn-clock-observationp obs))
      (fn-bpn-send config peer adu sequence obs)
    nil))

; What the host prints about what it just authored, without opening a record:
; (creation-time sequence lifetime payload-length).
(defun fn-bpn-host-sent-summary (config peer adu sequence obs)
  (if (and (fn-bpn-configp config) (fn-bpp-eidp peer) (fn-bpb-datap adu)
           (fn-bpp-timep sequence) (fn-clock-observationp obs))
      (list (fn-bpn-creation-time obs)
            sequence
            (fn-bpn-config-lifetime config)
            (len adu))
    nil))

; -----------------------------------------------------------------------------
; Receiving.  The flat result is
;
;   (outcome reason adu payload-length)
;
; with OUTCOME one of :accepted, :refused or :uncertain -- the three kept
; distinct all the way out to the host's exit code -- REASON the book's
; keyword, and ADU the payload octets when there are any.

(defun fn-bpn-host-receive (config octets obs)
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

(defun fn-bpn-host-receive-outcome (r) (nth 0 r))
(defun fn-bpn-host-receive-reason (r) (nth 1 r))
(defun fn-bpn-host-receive-adu (r) (nth 2 r))
(defun fn-bpn-host-receive-length (r) (nth 3 r))
