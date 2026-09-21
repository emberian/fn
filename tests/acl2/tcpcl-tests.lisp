; Witnesses and teeth for the TCPCLv4 codec and session machine.
;
; In order: golden octet vectors for every message kind; a full session
; between an active and a passive fn (contact, SESS_INIT, one two-segment
; transfer each way, keepalive, termination); a refused transfer; the
; chunk-size sweep that is the partition tooth (C1); the interleaving,
; TCP-close, version, TLS, unknown-type and MRU cases; then one concrete
; violating value per keystone hypothesis that has one.  Every check is an
; assert-event on a specific value (docs/proof-style.md section 5).
;
; fn-t-* are test-only executable realisers (docs/prefixes.md).

(in-package "ACL2")
(include-book "../../books/tcpcl-invariants")

; -----------------------------------------------------------------------------
; Test-only helpers: the octets a result asks the host to write, and the
; host's chunk loop (read k octets, prepend the carry, drive).

(defun fn-t-sent-octets (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (append (if (and (consp (car events)) (equal (car (car events)) :send))
                  (fn-tcl-encode (car (cdr (car events))))
                nil)
              (fn-t-sent-octets (cdr events)))
    nil))

(defun fn-t-kinds (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (cons (if (and (consp (car events)) (equal (car (car events)) :send))
                (list :send (fn-tcl-msg-kind (car (cdr (car events)))))
              (car (car events)))
            (fn-t-kinds (cdr events)))
    nil))

(defun fn-t-drive-chunks (s pending stream k now)
  (declare (xargs :measure (len stream)
                  :verify-guards nil
                  :hints (("Goal" :in-theory (enable fn-tcl-has-is-len-bound fn-tcl-drop)))))
  (if (or (not (consp stream)) (zp k))
      (fn-tcl-drive s (append pending stream) now)
    (let* ((n (min k (len stream)))
           (r (fn-tcl-drive s (append pending (fn-tcl-take n stream)) now))
           (rest (fn-t-drive-chunks (fn-tcl-result-session r)
                                    (fn-tcl-result-unconsumed r)
                                    (fn-tcl-drop n stream) k now)))
      (fn-tcl-make-result (fn-tcl-result-session rest)
                          (append (fn-tcl-result-events r) (fn-tcl-result-events rest))
                          (fn-tcl-result-unconsumed rest)))))

; -----------------------------------------------------------------------------
; Golden vectors (RFC 9174 figures 16, 19, 22, 23, 24, 27, 21).

(defconst *t-node-a* '(100 116 110 58 47 47 97 47))   ; "dtn://a/"
(defconst *t-node-b* '(100 116 110 58 47 47 98 47))   ; "dtn://b/"

(assert-event (equal (fn-tcl-encode (fn-tcl-make-contact 4 0)) '(100 116 110 33 4 0)))
(assert-event (equal (fn-tcl-decode-contact '(100 116 110 33 4 1 9 9))
                     (fn-tcl-parse-ok (fn-tcl-make-contact 4 1) '(9 9))))
(assert-event (equal (fn-tcl-encode (fn-tcl-make-keepalive)) '(4)))
(assert-event (equal (fn-tcl-encode (fn-tcl-make-sess-term 1 2)) '(5 1 2)))
(assert-event (equal (fn-tcl-encode (fn-tcl-make-msg-reject 3 1)) '(6 3 1)))
(assert-event (equal (fn-tcl-encode (fn-tcl-make-xfer-refuse 6 258))
                     '(3 6 0 0 0 0 0 0 1 2)))
(assert-event (equal (fn-tcl-encode (fn-tcl-make-xfer-ack 1 0 5))
                     '(2 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 5)))
(defconst *t-init-a* (fn-tcl-make-sess-init 30 3 64 *t-node-a* nil))
(assert-event (equal (fn-tcl-encode *t-init-a*)
                     (append '(7 0 30 0 0 0 0 0 0 0 3 0 0 0 0 0 0 0 64 0 8)
                             *t-node-a* '(0 0 0 0))))
(assert-event (equal (fn-tcl-decode-message (append (fn-tcl-encode *t-init-a*) '(4)) 3)
                     (fn-tcl-parse-ok *t-init-a* '(4))))
; a START segment with the Transfer Length Extension, then its data.
; Derived from the RFC, field by field, not read off the encoder: figure 22
; (section 5.2.2) for the message, figure 25 (section 5.2.5) for the item
; container, section 5.2.5.1 for the Transfer Length data.
;   1                 message header: XFER_SEGMENT type code 0x01 (table 14)
;   2                 message flags U8: START 0x02 set, END 0x01 clear (table 5)
;   0 0 0 0 0 0 0 0   transfer ID U64 = 0
;   0 0 0 13          transfer extension items length U32 = 13 (START only)
;     0               item flags U8 = 0, CRITICAL 0x01 clear (table 7)
;     0 1             item type U16 = 0x0001, Transfer Length (table 13)
;     0 8             item length U16 = 8
;     0 0 0 0 0 0 0 5 item value: total bundle length U64 = 5 (section 5.2.5.1)
;   0 0 0 0 0 0 0 3   data length U64 = 3
;   10 20 30          data contents
; 38 octets.  The wave-4 vector wrote the item header as `0 1 0 0 8`: the type
; before the flags.  Figure 25 puts Item Flags first, so the vector was wrong
; and fn-tcl-encode-items (flags, then be-bytes of type, then be-bytes of the
; value length) is right; this is the corrected vector.
(defconst *t-seg-1*
  (fn-tcl-make-xfer-segment 2 0 (list (fn-tcl-make-item 0 1 (fn-tcl-be-bytes 5 8))) '(10 20 30)))
(assert-event (equal (fn-tcl-encode *t-seg-1*)
                     '(1 2 0 0 0 0 0 0 0 0 0 0 0 13 0 0 1 0 8 0 0 0 0 0 0 0 5
                       0 0 0 0 0 0 0 3 10 20 30)))
(assert-event (equal (fn-tcl-decode-message (fn-tcl-encode *t-seg-1*) 3)
                     (fn-tcl-parse-ok *t-seg-1* nil)))
; a partial message is a need, never a copy; an over-MRU segment an error
(assert-event (fn-tcl-parse-needp (fn-tcl-decode-message '(1 2 0 0 0 0 0 0 0 0 0 0 0 13) 3)))
(assert-event (equal (fn-tcl-decode-message
                      (fn-tcl-encode (fn-tcl-make-xfer-segment 3 7 nil '(1 2 3 4))) 3)
                     (fn-tcl-parse-error :segment-exceeds-mru)))
(assert-event (equal (fn-tcl-decode-message '(9 1 2) 3)
                     (fn-tcl-parse-error '(:unknown-type 9))))
; canonicality over an arbitrary accepted vector: reserved flag bits survive
(defconst *t-ack-raw* '(2 129 0 0 0 0 0 0 0 4 0 0 0 0 0 0 1 0 77))
(assert-event (fn-tcl-parse-okp (fn-tcl-decode-message *t-ack-raw* 3)))
(assert-event (equal (append (fn-tcl-encode (fn-tcl-parse-msg (fn-tcl-decode-message *t-ack-raw* 3)))
                             (fn-tcl-parse-rest (fn-tcl-decode-message *t-ack-raw* 3)))
                     *t-ack-raw*))
(assert-event (fn-tcl-flag-end 129))
(assert-event (not (fn-tcl-flag-start 129)))

; -----------------------------------------------------------------------------
; A full session: A active, B passive, segment MRU 3, transfer MRU 64.

(defconst *t-pa* (fn-tcl-make-params 30 3 64 *t-node-a* nil *t-node-b*))
(defconst *t-pb* (fn-tcl-make-params 30 3 64 *t-node-b* nil nil))
(defconst *t-a0* (fn-tcl-initial-session :active *t-pa* 0))
(defconst *t-b0* (fn-tcl-initial-session :passive *t-pb* 0))
(assert-event (and (fn-tcl-sessionp *t-a0*) (fn-tcl-sessionp *t-b0*)))

(defconst *t-a1* (fn-tcl-open *t-a0* 0))
(assert-event (equal (fn-t-sent-octets (fn-tcl-result-events *t-a1*)) '(100 116 110 33 4 0)))
(defconst *t-b1* (fn-tcl-drive *t-b0* (fn-t-sent-octets (fn-tcl-result-events *t-a1*)) 0))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b1*)) :messaging))
(assert-event (equal (fn-t-kinds (fn-tcl-result-events *t-b1*)) '((:send :contact))))
(defconst *t-a2* (fn-tcl-drive (fn-tcl-result-session *t-a1*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-b1*)) 0))
(assert-event (equal (fn-t-kinds (fn-tcl-result-events *t-a2*)) '((:send :sess-init))))
(defconst *t-b2* (fn-tcl-drive (fn-tcl-result-session *t-b1*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-a2*)) 0))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b2*)) :established))
(assert-event (equal (fn-t-kinds (fn-tcl-result-events *t-b2*)) '((:send :sess-init) :session-up)))
(defconst *t-a3* (fn-tcl-drive (fn-tcl-result-session *t-a2*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-b2*)) 0))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-a3*)) :established))
(assert-event (equal (fn-tcl-negotiated-peer-node-id
                      (fn-tcl-session-negotiated (fn-tcl-result-session *t-a3*)))
                     *t-node-b*))
(assert-event (equal (fn-tcl-negotiated-keepalive
                      (fn-tcl-session-negotiated (fn-tcl-result-session *t-a3*)))
                     30))
(assert-event (equal (fn-tcl-result-unconsumed *t-a3*) nil))
(defconst *t-a* (fn-tcl-result-session *t-a3*))
(defconst *t-b* (fn-tcl-result-session *t-b2*))

; A sends five octets: START with the Transfer Length Extension, then END.
(defconst *t-a4* (fn-tcl-send *t-a* :bundle-1 '(10 20 30 40 50) 0))
(defconst *t-a5* (fn-tcl-pump (fn-tcl-result-session *t-a4*) 0))
(assert-event (equal (fn-tcl-result-events *t-a4*) (list (list :send *t-seg-1*))))
(assert-event (equal (fn-tcl-result-events *t-a5*)
                     (list (list :send (fn-tcl-make-xfer-segment 1 0 nil '(40 50))))))
(assert-event (equal (fn-tcl-result-events (fn-tcl-pump (fn-tcl-result-session *t-a5*) 0)) nil))
(defconst *t-seg-octets* (append (fn-t-sent-octets (fn-tcl-result-events *t-a4*))
                                 (fn-t-sent-octets (fn-tcl-result-events *t-a5*))))
(defconst *t-b3* (fn-tcl-drive *t-b* *t-seg-octets* 0))
(assert-event (equal (fn-tcl-result-events *t-b3*)
                     (list (list :send (fn-tcl-make-xfer-ack 2 0 3))
                           (list :send (fn-tcl-make-xfer-ack 1 0 5))
                           (list :bundle-received 0 '(10 20 30 40 50)))))
(assert-event (null (fn-tcl-session-inbound (fn-tcl-result-session *t-b3*))))
(defconst *t-a6* (fn-tcl-drive (fn-tcl-result-session *t-a5*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-b3*)) 0))
(assert-event (equal (fn-tcl-result-events *t-a6*) '((:outbound-sent 0 :bundle-1))))
(assert-event (null (fn-tcl-session-outbound (fn-tcl-result-session *t-a6*))))

; B sends the other way: a single-segment transfer, no extension.
(defconst *t-b4* (fn-tcl-send (fn-tcl-result-session *t-b3*) :bundle-2 '(7 8) 0))
(assert-event (equal (fn-tcl-result-events *t-b4*)
                     (list (list :send (fn-tcl-make-xfer-segment 3 0 nil '(7 8))))))
(defconst *t-a7* (fn-tcl-drive (fn-tcl-result-session *t-a6*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-b4*)) 0))
(assert-event (member-equal '(:bundle-received 0 (7 8)) (fn-tcl-result-events *t-a7*)))
(defconst *t-b5* (fn-tcl-drive (fn-tcl-result-session *t-b4*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-a7*)) 0))
(assert-event (equal (fn-tcl-result-events *t-b5*) '((:outbound-sent 0 :bundle-2))))

; Keepalive after one interval of silence on the send side; idle timeout
; after two intervals without anything received.
(defconst *t-tick-1* (fn-tcl-tick (fn-tcl-result-session *t-a7*)
                                  (fn-clock-observation 31000 0 0 nil)))
(assert-event (equal (fn-tcl-result-events *t-tick-1*) (list (list :send (fn-tcl-make-keepalive)))))
(defconst *t-tick-2* (fn-tcl-tick (fn-tcl-result-session *t-tick-1*)
                                  (fn-clock-observation 61000 0 0 nil)))
(assert-event (equal (fn-tcl-result-events *t-tick-2*)
                     (list (list :send (fn-tcl-make-sess-term 0 1)))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-tick-2*)) :ending))

; Clean termination from A: SESS_TERM, the reply, both close.
(defconst *t-a8* (fn-tcl-terminate (fn-tcl-result-session *t-a7*) 0 5))
(assert-event (equal (fn-tcl-result-events *t-a8*) (list (list :send (fn-tcl-make-sess-term 0 0)))))
(defconst *t-b6* (fn-tcl-drive (fn-tcl-result-session *t-b5*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-a8*)) 5))
(assert-event (equal (fn-tcl-result-events *t-b6*)
                     (list (list :send (fn-tcl-make-sess-term 1 0)) '(:peer-terminating 0) '(:close))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b6*)) :closed))
(defconst *t-a9* (fn-tcl-drive (fn-tcl-result-session *t-a8*)
                               (fn-t-sent-octets (fn-tcl-result-events *t-b6*)) 6))
(assert-event (equal (fn-tcl-result-events *t-a9*) '((:peer-terminating 0) (:close))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-a9*)) :closed))

; -----------------------------------------------------------------------------
; A refused transfer: a peer announces a total beyond B's transfer MRU.

(defconst *t-big-start*
  (fn-tcl-make-xfer-segment 2 5 (list (fn-tcl-make-item 0 1 (fn-tcl-be-bytes 100 8))) '(1 2 3)))
(defconst *t-b-refuse* (fn-tcl-drive *t-b* (fn-tcl-encode *t-big-start*) 0))
(assert-event (equal (fn-tcl-result-events *t-b-refuse*)
                     (list (list :send (fn-tcl-make-xfer-refuse 4 5)) '(:inbound-refused 5 4))))
(assert-event (null (fn-tcl-session-inbound (fn-tcl-result-session *t-b-refuse*))))
; and the sender side of a refusal: no further segments of that transfer
(defconst *t-a-refused* (fn-tcl-drive (fn-tcl-result-session *t-a4*)
                                      (fn-tcl-encode (fn-tcl-make-xfer-refuse 2 0)) 0))
(assert-event (equal (fn-tcl-result-events *t-a-refused*) '((:outbound-refused 0 :bundle-1 2))))
(assert-event (equal (fn-tcl-result-events (fn-tcl-pump (fn-tcl-result-session *t-a-refused*) 0)) nil))

; -----------------------------------------------------------------------------
; The partition tooth: the same octets at every chunk size give the same
; session and the same events (C1 as a sweep).

(assert-event (equal (fn-t-drive-chunks *t-b* nil *t-seg-octets* 1 0) *t-b3*))
(assert-event (equal (fn-t-drive-chunks *t-b* nil *t-seg-octets* 2 0) *t-b3*))
(assert-event (equal (fn-t-drive-chunks *t-b* nil *t-seg-octets* 3 0) *t-b3*))
(assert-event (equal (fn-t-drive-chunks *t-b* nil *t-seg-octets* 7 0) *t-b3*))
(assert-event (equal (fn-t-drive-chunks *t-b* nil *t-seg-octets* 64 0) *t-b3*))
; a split inside the first segment leaves a carry and no event
(defconst *t-b-half* (fn-tcl-drive *t-b* (fn-tcl-take 20 *t-seg-octets*) 0))
(assert-event (equal (fn-tcl-result-events *t-b-half*) nil))
(assert-event (equal (fn-tcl-result-unconsumed *t-b-half*) (fn-tcl-take 20 *t-seg-octets*)))
(assert-event (equal (fn-tcl-drive (fn-tcl-result-session *t-b-half*)
                                   (append (fn-tcl-result-unconsumed *t-b-half*)
                                           (fn-tcl-drop 20 *t-seg-octets*))
                                   0)
                     *t-b3*))

; -----------------------------------------------------------------------------
; Interleaving, TCP close, version mismatch, TLS, unknown type, MRU.

(defconst *t-b-mid* (fn-tcl-drive *t-b* (fn-tcl-encode *t-seg-1*) 0))
(assert-event (equal (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound (fn-tcl-result-session *t-b-mid*))) 0))
(assert-event (equal (fn-tcl-inbound-received-len (fn-tcl-session-inbound (fn-tcl-result-session *t-b-mid*))) 3))
; a START for another id while a transfer is live
(defconst *t-b-inter* (fn-tcl-drive (fn-tcl-result-session *t-b-mid*)
                                    (fn-tcl-encode (fn-tcl-make-xfer-segment 2 9 nil '(1))) 0))
(assert-event (equal (fn-tcl-result-events *t-b-inter*)
                     (list (list :send (fn-tcl-make-msg-reject 3 1))
                           (list :send (fn-tcl-make-xfer-refuse 3 0))
                           '(:inbound-refused 0 3)
                           (list :send (fn-tcl-make-sess-term 0 4)))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b-inter*)) :ending))
; the same interleaving after the peer has terminated.  The SESS_TERM
; handshake is complete (term :both) and nothing is outbound, so clearing
; the live transfer is the last thing "Transfers Done" (section 6.1) was
; waiting for and the session closes in that very step: this is the witness
; that separates the two cases of fn-tcl-no-interleaving's phase, and the
; value that refutes the wave-4 statement of it (which asserted :ending).
(defconst *t-b-term* (fn-tcl-drive (fn-tcl-result-session *t-b-mid*)
                                   (fn-tcl-encode (fn-tcl-make-sess-term 0 0)) 0))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b-term*)) :ending))
(assert-event (equal (fn-tcl-session-term (fn-tcl-result-session *t-b-term*)) :both))
(assert-event (fn-tcl-session-inbound (fn-tcl-result-session *t-b-term*)))
(assert-event (null (fn-tcl-session-outbound (fn-tcl-result-session *t-b-term*))))
(defconst *t-b-inter-both*
  (fn-tcl-drive (fn-tcl-result-session *t-b-term*)
                (fn-tcl-encode (fn-tcl-make-xfer-segment 2 9 nil '(1))) 0))
(assert-event (equal (fn-tcl-result-events *t-b-inter-both*)
                     (list (list :send (fn-tcl-make-msg-reject 3 1))
                           (list :send (fn-tcl-make-xfer-refuse 3 0))
                           '(:inbound-refused 0 3)
                           '(:close))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b-inter-both*)) :closed))
(assert-event (null (fn-tcl-session-inbound (fn-tcl-result-session *t-b-inter-both*))))
; TCP close in the middle of a transfer fails it and completes nothing
(defconst *t-b-cut* (fn-tcl-tcp-closed (fn-tcl-result-session *t-b-mid*)))
(assert-event (equal (fn-tcl-result-events *t-b-cut*) '((:inbound-failed 0) (:session-down))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b-cut*)) :closed))
; a declared total that the data contradicts is Not Acceptable
(defconst *t-b-short* (fn-tcl-drive (fn-tcl-result-session *t-b-mid*)
                                    (fn-tcl-encode (fn-tcl-make-xfer-segment 1 0 nil '(40))) 0))
(assert-event (equal (fn-tcl-result-events *t-b-short*)
                     (list (list :send (fn-tcl-make-xfer-refuse 4 0)) '(:inbound-refused 0 4))))
; a START in Ending is refused Session Terminating
(defconst *t-b-ending* (fn-tcl-drive (fn-tcl-result-session *t-b-inter*)
                                     (fn-tcl-encode (fn-tcl-make-xfer-segment 3 11 nil '(1))) 0))
(assert-event (equal (fn-tcl-result-events *t-b-ending*)
                     (list (list :send (fn-tcl-make-xfer-refuse 6 11)) '(:inbound-refused 11 6))))
; the passive entity answers version 3 with its header and Version mismatch
(defconst *t-b-v3* (fn-tcl-drive *t-b0* '(100 116 110 33 3 0) 0))
(assert-event (equal (fn-tcl-result-events *t-b-v3*)
                     (list (list :send (fn-tcl-make-contact 4 0))
                           (list :send (fn-tcl-make-sess-term 0 2)))))
; the active entity closes on version 3
(defconst *t-a-v3* (fn-tcl-drive (fn-tcl-result-session *t-a1*) '(100 116 110 33 3 0) 0))
(assert-event (equal (fn-tcl-result-events *t-a-v3*) '((:close))))
; a bad magic string closes silently before any message
(defconst *t-b-magic* (fn-tcl-drive *t-b0* '(100 116 110 63 4 0) 0))
(assert-event (equal (fn-tcl-result-events *t-b-magic*) '((:close))))
; Enable TLS is the conjunction: peer CAN_TLS alone negotiates nothing
(defconst *t-b-tls* (fn-tcl-drive *t-b0* '(100 116 110 33 4 1) 0))
(assert-event (equal (fn-tcl-session-tls (fn-tcl-result-session *t-b-tls*)) nil))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-b-tls*)) :messaging))
; both willing: a true conjunction is refused Contact Failure in wave 4
(defconst *t-pc* (fn-tcl-make-params 30 3 64 *t-node-b* t nil))
(defconst *t-c-tls* (fn-tcl-drive (fn-tcl-initial-session :passive *t-pc* 0) '(100 116 110 33 4 1) 0))
(assert-event (equal (fn-tcl-session-tls (fn-tcl-result-session *t-c-tls*)) t))
(assert-event (member-equal (list :send (fn-tcl-make-sess-term 0 4))
                            (fn-tcl-result-events *t-c-tls*)))
; an unknown message type: MSG_REJECT Message Type Unknown, then close
(defconst *t-b-unknown* (fn-tcl-drive *t-b* '(9 1 2) 0))
(assert-event (equal (fn-tcl-result-events *t-b-unknown*)
                     (list (list :send (fn-tcl-make-msg-reject 1 9)) '(:close))))
(assert-event (equal (fn-tcl-result-unconsumed *t-b-unknown*) '(9 1 2)))
; a segment over the segment MRU: refused at the decoder, no data taken
(defconst *t-b-over* (fn-tcl-drive *t-b* (fn-tcl-encode (fn-tcl-make-xfer-segment 3 7 nil '(1 2 3 4))) 0))
(assert-event (equal (fn-t-kinds (fn-tcl-result-events *t-b-over*)) '((:send :msg-reject) :close)))
; a peer whose node ID is not the contact plan's is refused Contact Failure
(defconst *t-init-x* (fn-tcl-make-sess-init 30 3 64 '(100 116 110 58 47 47 120 47) nil))
(defconst *t-a-wrong* (fn-tcl-drive (fn-tcl-result-session *t-a2*) (fn-tcl-encode *t-init-x*) 0))
(assert-event (equal (fn-tcl-result-events *t-a-wrong*)
                     (list (list :send (fn-tcl-make-sess-term 0 4)))))
(assert-event (equal (fn-tcl-session-phase (fn-tcl-result-session *t-a-wrong*)) :ending))
; a send while another transfer is live, and outside Established
(assert-event (equal (fn-tcl-result-events (fn-tcl-send (fn-tcl-result-session *t-a4*) :b2 '(1) 0))
                     '((:send-refused :b2 :busy))))
(assert-event (equal (fn-tcl-result-events (fn-tcl-send (fn-tcl-result-session *t-a8*) :b3 '(1) 0))
                     '((:send-refused :b3 :not-established))))
(assert-event (equal (fn-tcl-result-events (fn-tcl-send *t-a* :b4 (make-list 65 :initial-element 0) 0))
                     '((:send-refused :b4 :exceeds-transfer-mtu))))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per keystone hypothesis that has one.

; fn-tcl-no-interleaving without a live inbound: the START is accepted.
(assert-event (fn-tcl-session-inbound (fn-tcl-result-session *t-b-mid*)))
; fn-tcl-ending-refuses-new-transfers outside Ending: the START is accepted.
(assert-event (equal (fn-tcl-session-phase *t-b*) :established))
(assert-event (not (member-equal (list :send (fn-tcl-make-xfer-refuse 6 0))
                                 (fn-tcl-result-events *t-b-mid*))))
; fn-tcl-ending-refuses-new-sends in Established: the send goes out.
(assert-event (not (equal (fn-tcl-result-events *t-a4*) '((:send-refused :bundle-1 :not-established)))))
; fn-tcl-keepalive-zero-disables-both with keepalive 30: a KEEPALIVE is sent.
(assert-event (consp (fn-tcl-result-events *t-tick-1*)))
; fn-tcl-live-inbound-ends-in-exactly-one-outcome when the inbound persists:
; a continuation segment produces no outcome at all.
(defconst *t-b-cont* (fn-tcl-drive (fn-tcl-result-session *t-b-mid*)
                                   (fn-tcl-encode (fn-tcl-make-xfer-segment 0 0 nil '(40))) 0))
(assert-event (equal (fn-tcl-inbound-outcome-count (fn-tcl-result-events *t-b-cont*) 0) 0))
(assert-event (equal (fn-tcl-inbound-received-len (fn-tcl-session-inbound (fn-tcl-result-session *t-b-cont*))) 4))
; fn-tcl-retained-input-is-bounded on a closed session: the whole buffer
; comes back, longer than any message.
(defconst *t-long* (make-list 6000 :initial-element 4))
(assert-event (equal (fn-tcl-result-unconsumed (fn-tcl-drive (fn-tcl-result-session *t-b-cut*) *t-long* 0))
                     *t-long*))
(assert-event (< (fn-tcl-max-message 3) (len *t-long*)))
; fn-tcl-tcp-close-never-completes-a-transfer: a close with nothing live
; fails nothing, so the :inbound-failed conjunct needs its hypothesis.
(assert-event (equal (fn-tcl-result-events (fn-tcl-tcp-closed *t-b*)) '((:session-down))))
; fn-tcl-final-ack-means-every-segment: an END segment with the wrong id
; completes nothing (refused Retransmit), and one for the live id does.
(assert-event (not (member-equal '(:bundle-received 9 (1)) (fn-tcl-result-events *t-b-inter*))))
(assert-event (member-equal (list :send (fn-tcl-make-xfer-ack 1 0 5)) (fn-tcl-result-events *t-b3*)))
; fn-tcl-refused-transfer-sends-no-more-segments with a refusal for a
; transfer that is not the live one: the live transfer keeps going.
(defconst *t-a-stray* (fn-tcl-drive (fn-tcl-result-session *t-a4*)
                                    (fn-tcl-encode (fn-tcl-make-xfer-refuse 2 77)) 0))
(assert-event (equal (fn-tcl-result-events *t-a-stray*) nil))
(assert-event (consp (fn-tcl-result-events (fn-tcl-pump (fn-tcl-result-session *t-a-stray*) 0))))
; fn-tcl-drive-partition-independence: no separating value exists for its
; hypotheses (a non-session, a non-octet chunk and a non-time are no-ops on
; both sides); they are the guard of the served path, see specs/tcpcl.md.
; 42 is outside fn-tcl-drive's guard, so the :logic body is what is being
; evaluated here and the check is made under with-guard-checking :none
; (docs/proof-style.md section 5).
(assert-event
 (with-guard-checking :none
  (equal (fn-tcl-drive 42 *t-seg-octets* 0) (fn-tcl-make-result 42 nil *t-seg-octets*))))

; -----------------------------------------------------------------------------
; The cheap guard is STRICTLY weaker than the specification recognizer, and
; strictly weaker in each of the two conjuncts it drops.  Without this,
; `fn-tcl-sessionp-is-cheap' could be an identity between two spellings of
; the same predicate and the served path would still be walking the staged
; octets once per socket chunk (specs/tcpcl.md section 3).  Each witness is
; the live-transfer session of *t-b-mid* with its inbound record rebuilt
; through `fn-tcl-next' to violate exactly one conjunct, so the separation is
; by more than the recognizers' weakest clause.

(defconst *t-b-live* (fn-tcl-result-session *t-b-mid*))
(assert-event (fn-tcl-sessionp *t-b-live*))
(assert-event (fn-tcl-session-cheapp *t-b-live*))
(assert-event (fn-tcl-session-inbound *t-b-live*))

; (a) staged that is not octet lists.  `fn-tcl-lists-len' still measures 1,
; so the carried sum agrees and `fn-tcl-octet-listsp' is the only conjunct
; that separates them.
(defconst *t-b-nonoctet*
  (fn-tcl-next *t-b-live* (fn-tcl-session-phase *t-b-live*)
               (fn-tcl-make-inbound
                (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound *t-b-live*))
                '((300)) 1 nil)
               (fn-tcl-session-outbound *t-b-live*)
               (fn-tcl-session-term *t-b-live*)
               (fn-tcl-session-last-tx *t-b-live*)))
(assert-event
 (equal (fn-tcl-lists-len (fn-tcl-inbound-staged (fn-tcl-session-inbound *t-b-nonoctet*))) 1))
(assert-event (fn-tcl-session-cheapp *t-b-nonoctet*))
(assert-event (not (fn-tcl-sessionp *t-b-nonoctet*)))

; (b) a carried sum that is not the measurement of the staged list.  The
; staged segments are octets here, so the length equation is the only
; conjunct that separates them.
(defconst *t-b-wrong-sum*
  (fn-tcl-next *t-b-live* (fn-tcl-session-phase *t-b-live*)
               (fn-tcl-make-inbound
                (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound *t-b-live*))
                '((1 2 3)) 0 nil)
               (fn-tcl-session-outbound *t-b-live*)
               (fn-tcl-session-term *t-b-live*)
               (fn-tcl-session-last-tx *t-b-live*)))
(assert-event
 (fn-tcl-octet-listsp (fn-tcl-inbound-staged (fn-tcl-session-inbound *t-b-wrong-sum*))))
(assert-event (fn-tcl-session-cheapp *t-b-wrong-sum*))
(assert-event (not (fn-tcl-sessionp *t-b-wrong-sum*)))

; And the guard is reached on real sessions, not only on the two witnesses
; above: every session the golden exchange drives through satisfies it, which
; is what makes `fn-tcl-sessionp-is-cheap' the one cheap rule an includer
; keeps enabled -- it discharges `fn-tcl-drive's totality test wherever the
; session is known.
(assert-event (fn-tcl-session-cheapp (fn-tcl-result-session *t-b-cont*)))
(assert-event (fn-tcl-session-cheapp (fn-tcl-result-session *t-b3*)))
(assert-event (fn-tcl-session-cheapp (fn-tcl-result-session *t-b-cut*)))
(assert-event (fn-tcl-session-cheapp *t-a*))

; -----------------------------------------------------------------------------
; The same separation on the SENDING side (w11/tcpcl-outbound, D19).  The
; cheap guard also drops the two conjuncts of `fn-tcl-outboundp' that measure
; the unsent suffix, so `fn-tcl-outboundp-is-cheap' needs the same teeth:
; without them it could be an identity between two spellings and a send of n
; octets would still walk the suffix once per socket chunk (specs/tcpcl.md
; section 6).  Each witness is the mid-transfer session of *t-a4* -- A has
; sent the first 3 of 5 octets and holds `(40 50)' unsent -- with its
; outbound record rebuilt through `fn-tcl-next' to violate exactly one
; conjunct, and each assertion is accompanied by the check that the OTHER
; conjunct still holds.

(defconst *t-a-mid* (fn-tcl-result-session *t-a4*))
(assert-event (fn-tcl-sessionp *t-a-mid*))
(assert-event (fn-tcl-session-cheapp *t-a-mid*))
(assert-event (fn-tcl-session-outbound *t-a-mid*))
(assert-event (equal (fn-tcl-outbound-remaining (fn-tcl-session-outbound *t-a-mid*)) '(40 50)))
(assert-event (equal (fn-tcl-outbound-sent-len (fn-tcl-session-outbound *t-a-mid*)) 3))
(assert-event (equal (fn-tcl-outbound-total (fn-tcl-session-outbound *t-a-mid*)) 5))

; (c) an unsent suffix that is not octets.  It still has two cells, so
; 3 + 2 = 5 and the length equation agrees; `fn-cbor-octet-listp' is the only
; conjunct that separates the two recognizers here.
(defconst *t-a-nonoctet*
  (fn-tcl-next *t-a-mid* (fn-tcl-session-phase *t-a-mid*)
               (fn-tcl-session-inbound *t-a-mid*)
               (fn-tcl-make-outbound
                (fn-tcl-outbound-xfer-id (fn-tcl-session-outbound *t-a-mid*))
                (fn-tcl-outbound-ref (fn-tcl-session-outbound *t-a-mid*))
                '(300 400) 5 3 0)
               (fn-tcl-session-term *t-a-mid*)
               (fn-tcl-session-last-tx *t-a-mid*)))
(assert-event
 (equal (+ (fn-tcl-outbound-sent-len (fn-tcl-session-outbound *t-a-nonoctet*))
           (len (fn-tcl-outbound-remaining (fn-tcl-session-outbound *t-a-nonoctet*))))
        (fn-tcl-outbound-total (fn-tcl-session-outbound *t-a-nonoctet*))))
(assert-event (fn-tcl-session-cheapp *t-a-nonoctet*))
(assert-event (not (fn-tcl-sessionp *t-a-nonoctet*)))

; (d) an unsent suffix whose length is not (- total sent).  Its one cell is
; an octet, so `fn-cbor-octet-listp' holds and the length equation is the
; only conjunct that separates them.
(defconst *t-a-wrong-len*
  (fn-tcl-next *t-a-mid* (fn-tcl-session-phase *t-a-mid*)
               (fn-tcl-session-inbound *t-a-mid*)
               (fn-tcl-make-outbound
                (fn-tcl-outbound-xfer-id (fn-tcl-session-outbound *t-a-mid*))
                (fn-tcl-outbound-ref (fn-tcl-session-outbound *t-a-mid*))
                '(40) 5 3 0)
               (fn-tcl-session-term *t-a-mid*)
               (fn-tcl-session-last-tx *t-a-mid*)))
(assert-event
 (fn-cbor-octet-listp (fn-tcl-outbound-remaining (fn-tcl-session-outbound *t-a-wrong-len*))))
(assert-event
 (not (equal (+ (fn-tcl-outbound-sent-len (fn-tcl-session-outbound *t-a-wrong-len*))
                (len (fn-tcl-outbound-remaining (fn-tcl-session-outbound *t-a-wrong-len*))))
             (fn-tcl-outbound-total (fn-tcl-session-outbound *t-a-wrong-len*)))))
(assert-event (fn-tcl-session-cheapp *t-a-wrong-len*))
(assert-event (not (fn-tcl-sessionp *t-a-wrong-len*)))

; The cheap outbound recognizer is reached on the real sending sessions of
; the golden exchange, not only on the two witnesses above.
(assert-event (fn-tcl-outbound-cheapp (fn-tcl-session-outbound *t-a-mid*)))
(assert-event (fn-tcl-outbound-cheapp
               (fn-tcl-session-outbound (fn-tcl-result-session *t-a5*))))
(assert-event (fn-tcl-outbound-cheapp
               (fn-tcl-session-outbound (fn-tcl-result-session *t-b4*))))
(assert-event (fn-tcl-session-cheapp (fn-tcl-result-session *t-a5*)))
(assert-event (fn-tcl-session-cheapp (fn-tcl-result-session *t-b4*)))

; And fn-tcl-take/fn-tcl-drop are guard-total now (D19): both answer on a
; count past the end of the list, with the SAME value the logical definition
; always had, so relaxing the guard changed no behaviour.  Without this the
; length equation could not have left the cheap recognizer.
(assert-event (equal (fn-tcl-take 3 '(1 2)) '(1 2 nil)))
(assert-event (equal (fn-tcl-drop 3 '(1 2)) nil))
(assert-event (equal (fn-tcl-take 2 '(1 2 3)) '(1 2)))
(assert-event (equal (fn-tcl-drop 2 '(1 2 3)) '(3)))
