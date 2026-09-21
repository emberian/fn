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
(include-book "../books/bp-node-records")
(include-book "../books/bp-authored-wire")

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
; Durable creation-sequence frontier.  These are the only sequence operations
; host/native/bp.lisp may call.  In particular it does not parse an FNBS frame,
; increment a counter, or choose a fallback after an uncertain write.

(defun fn-bpn-host-sequence-recover (octets presentp freshp)
  (if (fn-cbor-octet-listp octets)
      (fn-bpn-sequence-recover octets (if presentp t nil) (if freshp t nil))
    (list :fault :host-arguments)))

(defun fn-bpn-host-sequence-ready-p (answer)
  (and (fn-bpn-sequence-recovery-readyp answer) t))

(defun fn-bpn-host-sequence-frontier (answer)
  (if (fn-bpn-sequence-recovery-readyp answer)
      (fn-bpn-sequence-recovery-frontier answer)
    nil))

(defun fn-bpn-host-sequence-reserve (frontier)
  (if (fn-bpn-sequence-frontierp frontier)
      (fn-bpn-sequence-reserve frontier)
    (list :refused :host-arguments)))

(defun fn-bpn-host-sequence-reservationp (reservation)
  (and (fn-bpn-sequence-reservationp reservation) t))

(defun fn-bpn-host-sequence-reservation-sequence (reservation)
  (if (fn-bpn-sequence-reservationp reservation)
      (fn-bpn-sequence-reservation-sequence reservation)
    nil))

(defun fn-bpn-host-sequence-reservation-frame (reservation)
  (if (fn-bpn-sequence-reservationp reservation)
      (fn-bpn-sequence-record-frame
       (fn-bpn-sequence-reservation-record reservation))
    nil))

(defun fn-bpn-host-sequence-frame-limit ()
  (fn-bpn-sequence-frame-limit))

; -----------------------------------------------------------------------------
; Immutable authored-wire evidence.  The preview is used only to observe the
; exact final path under the BP spool lock.  The later operation carries that
; same ACL2 name and the wire bytes produced by fn-bpn-send.

(defun fn-bpn-host-authored-wire-name (reservation)
  (let ((chars (fn-bpn-authored-wire-name-for-reservation reservation)))
    (if (character-listp chars) (coerce chars 'string) "")))

(defun fn-bpn-host-authored-wire-authorize
  (config peer adu reservation obs lock-owned final-absent)
  (fn-bpn-authored-wire-authorize
   config peer adu reservation obs lock-owned final-absent))

(defun fn-bpn-host-authored-wire-operationp (operation)
  (and (fn-bpn-authored-wire-operationp operation) t))

(defun fn-bpn-host-authored-wire-operation-label (operation)
  (fn-bpn-authored-wire-operation-label operation))

(defun fn-bpn-host-authored-wire-operation-name (operation)
  (let ((chars (fn-bpn-authored-wire-operation-name-chars operation)))
    (if (character-listp chars) (coerce chars 'string) "")))

(defun fn-bpn-host-authored-wire-operation-wire (operation)
  (fn-bpn-authored-wire-operation-wire operation))

(defun fn-bpn-host-authored-wire-operation-publication (operation)
  (fn-bpn-authored-wire-operation-publication operation))

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

; -----------------------------------------------------------------------------
; One process result from two different kinds of evidence.
;
; ARTICLE-* counts are verdicts about complete inbound BP bundles.  OPERATIONAL
; is the convergence session's result.  An uncertain socket/session result is
; therefore not overwritten by a refused article: uncertainty dominates across
; both domains, then refusal, then acceptance.  host/native/bp.lisp calls this
; function directly before mapping the returned keyword to its public exit code.

(defun fn-bpn-host-run-outcome (article-accepted article-refused
                                                 article-uncertain operational)
  (if (not (and (natp article-accepted)
                (natp article-refused)
                (natp article-uncertain)
                (member-equal operational '(nil :accepted :refused :uncertain))))
      :uncertain
    (cond ((or (< 0 article-uncertain)
               (equal operational :uncertain))
           :uncertain)
          ((or (< 0 article-refused)
               (equal operational :refused))
           :refused)
          (t :accepted))))
