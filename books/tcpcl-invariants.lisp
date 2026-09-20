; fn TCPCLv4: the keystones C1 to C4 of specs/tcpcl.md over the session
; machine of tcpcl-session.
;
; C1  fn-tcl-drive-partition-independence: driving a concatenation is
;     driving the left part and then the right part prepended with the
;     carry the left part returned, with the events in order.  This is the
;     host's loop (read a chunk, prepend the carry, drive), in the shape of
;     fn-wire-drive-partition-independence with the unconsumed carry added.
; C2  fn-tcl-final-ack-means-every-segment and its two companions: a
;     :bundle-received event is emitted only by an END segment of the
;     started transfer, the acknowledgement it carries is the carried sum of
;     every accepted segment plus this one, that sum is the length of the
;     delivered data, and a declared Transfer Length agrees with it.
; C3  fn-tcl-tcp-close-never-completes-a-transfer,
;     fn-tcl-step-emits-at-most-one-inbound-outcome and
;     fn-tcl-live-inbound-ends-in-exactly-one-outcome: an inbound transfer
;     that stops being live does so with exactly one of :bundle-received,
;     :inbound-refused, :inbound-failed, and a TCP close only fails it.
; C4  fn-tcl-no-interleaving, fn-tcl-ending-refuses-new-transfers (both
;     directions), fn-tcl-refused-transfer-sends-no-more-segments,
;     fn-tcl-keepalive-zero-disables-both, fn-tcl-negotiation-is-min-and-and,
;     fn-tcl-retained-input-is-bounded (the carry the served path returns
;     is shorter than one maximal message whenever the session is open), and
;     the carried transfer bound fn-tcl-retained-transfer-is-bounded.
;
; This book opens the transitions and the recognizers locally; every
; includer above sees them closed.

(in-package "ACL2")
(include-book "tcpcl-session")

(local (in-theory (enable fn-tcl-session-vocabulary fn-tcl-has-is-len-bound)))
; clock withdraws fn-clock-observationp under fn-clock-vocabulary; the tick
; keystone reads fn-clock-monotonic under it, so it is opened here as well.
(local (in-theory (enable fn-clock-observationp)))
(local (in-theory (disable fn-tcl-sessionp fn-tcl-messagep)))

(local (defthm fn-tcl-append-assoc
         (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-tcl-append-nil
         (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-tcl-member-equal-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))

; -----------------------------------------------------------------------------
; The drive loop's shape facts.

(defthm fn-tcl-drive-is-a-result
  (equal (fn-tcl-make-result (fn-tcl-result-session (fn-tcl-drive s buf now))
                             (fn-tcl-result-events (fn-tcl-drive s buf now))
                             (fn-tcl-result-unconsumed (fn-tcl-drive s buf now)))
         (fn-tcl-drive s buf now))
  :hints (("Goal" :expand ((fn-tcl-drive s buf now)))))

(defthm fn-tcl-drive-closed-is-noop
  (implies (equal (fn-tcl-session-phase s) :closed)
           (equal (fn-tcl-drive s buf now) (fn-tcl-make-result s nil buf)))
  :hints (("Goal" :expand ((fn-tcl-drive s buf now)))))

(defthm fn-tcl-drive-of-empty-chunk
  (implies (not (consp buf))
           (equal (fn-tcl-drive s buf now) (fn-tcl-make-result s nil buf)))
  :hints (("Goal" :expand ((fn-tcl-drive s buf now)))))

(defthm fn-tcl-input-error-closes
  (equal (fn-tcl-session-phase (fn-tcl-result-session (fn-tcl-input-error s header reason now)))
         :closed))

(defthm fn-tcl-decode-for-append-ok
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-okp (fn-tcl-decode-for s left)))
           (equal (fn-tcl-decode-for s (append left right))
                  (fn-tcl-parse-ok (fn-tcl-parse-msg (fn-tcl-decode-for s left))
                                   (append (fn-tcl-parse-rest (fn-tcl-decode-for s left))
                                           right)))))

(defthm fn-tcl-decode-for-append-error
  (implies (and (fn-cbor-octet-listp left) (fn-tcl-parse-errorp (fn-tcl-decode-for s left)))
           (equal (fn-tcl-decode-for s (append left right))
                  (fn-tcl-decode-for s left))))

(defthm fn-tcl-decode-for-outcomes
  (implies (and (fn-cbor-octet-listp buf)
                (not (fn-tcl-parse-okp (fn-tcl-decode-for s buf)))
                (not (fn-tcl-parse-needp (fn-tcl-decode-for s buf))))
           (fn-tcl-parse-errorp (fn-tcl-decode-for s buf))))

; -----------------------------------------------------------------------------
; C1.  Partition independence of the served path, with the carry.

(defthm fn-tcl-drive-partition-independence
  (implies (and (fn-tcl-sessionp s)
                (fn-cbor-octet-listp left)
                (fn-cbor-octet-listp right)
                (fn-clock-timep now))
           (equal (fn-tcl-drive s (append left right) now)
                  (fn-tcl-make-result
                   (fn-tcl-result-session
                    (fn-tcl-drive (fn-tcl-result-session (fn-tcl-drive s left now))
                                  (append (fn-tcl-result-unconsumed (fn-tcl-drive s left now))
                                          right)
                                  now))
                   (append (fn-tcl-result-events (fn-tcl-drive s left now))
                           (fn-tcl-result-events
                            (fn-tcl-drive (fn-tcl-result-session (fn-tcl-drive s left now))
                                          (append (fn-tcl-result-unconsumed
                                                   (fn-tcl-drive s left now))
                                                  right)
                                          now)))
                   (fn-tcl-result-unconsumed
                    (fn-tcl-drive (fn-tcl-result-session (fn-tcl-drive s left now))
                                  (append (fn-tcl-result-unconsumed (fn-tcl-drive s left now))
                                          right)
                                  now)))))
  :hints (("Goal" :induct (fn-tcl-drive s left now)
           :in-theory (e/d (fn-tcl-drive)
                           (fn-tcl-step fn-tcl-decode-for fn-tcl-input-error
                            fn-tcl-drive-is-a-result)))
          ("Subgoal *1/2" :expand ((fn-tcl-drive s (append left right) now)))
          ("Subgoal *1/1" :expand ((fn-tcl-drive s (append left right) now)))))

; -----------------------------------------------------------------------------
; C2.  A final acknowledgement means every segment.

(local (in-theory (enable fn-tcl-sessionp)))

(defthm fn-tcl-final-ack-means-every-segment
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now)
                (member-equal (list :bundle-received id data)
                              (fn-tcl-result-events (fn-tcl-step s m now))))
           (and (equal (fn-tcl-msg-kind m) :xfer-segment)
                (equal id (fn-tcl-xfer-segment-xfer-id m))
                (fn-tcl-flag-end (fn-tcl-xfer-segment-flags m))
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                ; the segment ends the live transfer, or starts and ends one
                (if (fn-tcl-session-inbound s)
                    (and (not (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
                         (equal id (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s))))
                  (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
                ; nothing is live afterwards
                (null (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now))))
                ; the delivered data is every accepted segment then this one
                (equal (len data)
                       (+ (if (fn-tcl-session-inbound s)
                              (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                            0)
                          (len (fn-tcl-xfer-segment-data m))))
                ; the acknowledgement carries exactly that length
                (member-equal (list :send (fn-tcl-make-xfer-ack
                                           (fn-tcl-xfer-segment-flags m) id (len data)))
                              (fn-tcl-result-events (fn-tcl-step s m now)))
                ; a declared Transfer Length agrees
                (implies (and (fn-tcl-session-inbound s)
                              (fn-tcl-inbound-total (fn-tcl-session-inbound s)))
                         (equal (fn-tcl-inbound-total (fn-tcl-session-inbound s)) (len data)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep)
                           (fn-tcl-ext-decision fn-tcl-recv-contact fn-tcl-recv-init
                            fn-tcl-recv-ack fn-tcl-recv-refuse fn-tcl-recv-term)))))

; The carried sum is the measurement of the staged segments: the theorem
; above speaks of received-len, and this says what it is.
(defthm fn-tcl-received-len-is-staged-length-by-definition
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-inbound s))
           (equal (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                  (fn-tcl-lists-len (fn-tcl-inbound-staged (fn-tcl-session-inbound s)))))
  :rule-classes nil)

; A transfer is started only by a START segment: the inbound record after a
; step is nil, the record before, or a record created by this segment's START.
(defthm fn-tcl-inbound-is-created-only-by-start
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now)
                (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now)))
                (not (equal (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now)))
                            (fn-tcl-session-inbound s))))
           (and (equal (fn-tcl-msg-kind m) :xfer-segment)
                (equal (fn-tcl-inbound-xfer-id
                        (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now))))
                       (fn-tcl-xfer-segment-xfer-id m))
                (implies (null (fn-tcl-session-inbound s))
                         (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
                (implies (fn-tcl-session-inbound s)
                         (equal (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s))
                                (fn-tcl-xfer-segment-xfer-id m)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep)
                           (fn-tcl-ext-decision fn-tcl-recv-contact fn-tcl-recv-init
                            fn-tcl-recv-ack fn-tcl-recv-refuse fn-tcl-recv-term)))))

; -----------------------------------------------------------------------------
; C3.  Exactly one outcome.

(defun fn-tcl-inbound-outcome-count (events id)
  (declare (xargs :guard t))
  (if (consp events)
      (+ (if (and (consp (car events))
                  (or (equal (car (car events)) :bundle-received)
                      (equal (car (car events)) :inbound-refused)
                      (equal (car (car events)) :inbound-failed))
                  (equal (fn-cbor-ag-car (fn-cbor-ag-cdr (car events))) id))
             1
           0)
         (fn-tcl-inbound-outcome-count (cdr events) id))
    0))

(defthm fn-tcl-inbound-outcome-count-append
  (equal (fn-tcl-inbound-outcome-count (append a b) id)
         (+ (fn-tcl-inbound-outcome-count a id) (fn-tcl-inbound-outcome-count b id))))

(defthm fn-tcl-tcp-close-never-completes-a-transfer
  (implies (fn-tcl-sessionp s)
           (and (not (member-equal (list :bundle-received id data)
                                   (fn-tcl-result-events (fn-tcl-tcp-closed s))))
                (implies (and (fn-tcl-session-inbound s)
                              (not (equal (fn-tcl-session-phase s) :closed)))
                         (member-equal (list :inbound-failed
                                             (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))
                                       (fn-tcl-result-events (fn-tcl-tcp-closed s))))
                (null (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-tcp-closed s)))))))

(defthm fn-tcl-input-error-never-completes-a-transfer
  (implies (fn-tcl-sessionp s)
           (and (not (member-equal (list :bundle-received id data)
                                   (fn-tcl-result-events
                                    (fn-tcl-input-error s header reason now))))
                (null (fn-tcl-session-inbound
                       (fn-tcl-result-session (fn-tcl-input-error s header reason now)))))))

(defthm fn-tcl-step-emits-at-most-one-inbound-outcome
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now))
           (<= (fn-tcl-inbound-outcome-count (fn-tcl-result-events (fn-tcl-step s m now)) id)
               1))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep) (fn-tcl-ext-decision)))))

(defthm fn-tcl-live-inbound-ends-in-exactly-one-outcome
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now)
                (fn-tcl-session-inbound s)
                (equal id (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))
                (not (and (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now)))
                          (equal (fn-tcl-inbound-xfer-id
                                  (fn-tcl-session-inbound
                                   (fn-tcl-result-session (fn-tcl-step s m now))))
                                 id))))
           (equal (fn-tcl-inbound-outcome-count
                   (fn-tcl-result-events (fn-tcl-step s m now)) id)
                  1))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep) (fn-tcl-ext-decision)))))

(defthm fn-tcl-tick-fails-a-live-inbound-only-when-closing
  (implies (and (fn-tcl-sessionp s) (fn-clock-observationp obs))
           (and (not (member-equal (list :bundle-received id data)
                                   (fn-tcl-result-events (fn-tcl-tick s obs))))
                (iff (member-equal (list :inbound-failed id)
                                   (fn-tcl-result-events (fn-tcl-tick s obs)))
                     (and (fn-tcl-session-inbound s)
                          (equal id (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))
                          (equal (fn-tcl-session-phase (fn-tcl-result-session (fn-tcl-tick s obs)))
                                 :closed))))))

; -----------------------------------------------------------------------------
; C4.  Discipline and bounds.

(defthm fn-tcl-no-interleaving
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now)
                (equal (fn-tcl-msg-kind m) :xfer-segment)
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                (fn-tcl-session-inbound s)
                (not (equal (fn-tcl-xfer-segment-xfer-id m)
                            (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))))
           (and (null (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now))))
                (member-equal (list :send (fn-tcl-make-msg-reject 3 1))
                              (fn-tcl-result-events (fn-tcl-step s m now)))
                (not (member-equal (list :bundle-received id data)
                                   (fn-tcl-result-events (fn-tcl-step s m now))))
                (equal (fn-tcl-session-phase (fn-tcl-result-session (fn-tcl-step s m now)))
                       :ending)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep) (fn-tcl-ext-decision)))))

(defthm fn-tcl-ending-refuses-new-transfers
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (fn-clock-timep now)
                (equal (fn-tcl-session-phase s) :ending)
                (fn-tcl-session-negotiated s)
                (null (fn-tcl-session-inbound s))
                (equal (fn-tcl-msg-kind m) :xfer-segment)
                (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
           (and (null (fn-tcl-session-inbound (fn-tcl-result-session (fn-tcl-step s m now))))
                (member-equal (list :send (fn-tcl-make-xfer-refuse
                                           6 (fn-tcl-xfer-segment-xfer-id m)))
                              (fn-tcl-result-events (fn-tcl-step s m now)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep) (fn-tcl-ext-decision)))))

(defthm fn-tcl-ending-refuses-new-sends
  (implies (and (fn-tcl-sessionp s)
                (not (equal (fn-tcl-session-phase s) :established)))
           (equal (fn-tcl-send s ref octets now)
                  (fn-tcl-make-result s (list (list :send-refused ref :not-established)) nil))))

(defthm fn-tcl-refused-transfer-sends-no-more-segments
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-messagep m (fn-tcl-segment-mru s))
                (equal (fn-tcl-msg-kind m) :xfer-refuse)
                (fn-tcl-transferringp (fn-tcl-session-phase s))
                (fn-tcl-session-outbound s)
                (equal (fn-tcl-xfer-refuse-xfer-id m)
                       (fn-tcl-outbound-xfer-id (fn-tcl-session-outbound s))))
           (and (null (fn-tcl-session-outbound (fn-tcl-result-session (fn-tcl-step s m now))))
                (equal (fn-tcl-result-events
                        (fn-tcl-pump (fn-tcl-result-session (fn-tcl-step s m now)) later))
                       nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-tcl-messagep) (fn-tcl-ext-decision fn-tcl-recv-segment
                                              fn-tcl-recv-contact fn-tcl-recv-init
                                              fn-tcl-recv-ack fn-tcl-recv-term)))))

(defthm fn-tcl-keepalive-zero-disables-both
  (implies (and (fn-tcl-sessionp s)
                (fn-tcl-session-negotiated s)
                (equal (fn-tcl-negotiated-keepalive (fn-tcl-session-negotiated s)) 0))
           (equal (fn-tcl-tick s obs) (fn-tcl-make-result s nil nil))))

(defthm fn-tcl-negotiation-is-min-and-and
  (and (equal (fn-tcl-negotiated-keepalive (fn-tcl-negotiate local tls m))
              (min (fn-tcl-params-keepalive local) (fn-tcl-sess-init-keepalive m)))
       (equal (fn-tcl-negotiated-segment-mtu (fn-tcl-negotiate local tls m))
              (fn-tcl-sess-init-segment-mru m))
       (equal (fn-tcl-negotiated-transfer-mtu (fn-tcl-negotiate local tls m))
              (fn-tcl-sess-init-transfer-mru m))
       (iff (fn-tcl-negotiated-tls (fn-tcl-negotiate local tls m)) tls)
       (equal (fn-tcl-negotiated-peer-node-id (fn-tcl-negotiate local tls m))
              (fn-tcl-sess-init-node-id m))))

; Enable TLS is the conjunction of the two CAN_TLS flags, and a true
; conjunction is refused Contact Failure in wave 4.
(defthm fn-tcl-contact-tls-is-conjunction
  (implies (and (fn-tcl-sessionp s) (fn-clock-timep now)
                (fn-tcl-pre-establishedp (fn-tcl-session-phase s))
                (fn-tcl-contact-shapep m)
                (fn-cbor-octetp (fn-tcl-contact-flags m)))
           (and (iff (fn-tcl-session-tls (fn-tcl-result-session (fn-tcl-recv-contact s m now)))
                     (and (fn-tcl-params-can-tls (fn-tcl-session-local s))
                          (fn-tcl-flag-can-tls (fn-tcl-contact-flags m))))
                (implies (and (fn-tcl-params-can-tls (fn-tcl-session-local s))
                              (fn-tcl-flag-can-tls (fn-tcl-contact-flags m))
                              (equal (fn-tcl-contact-version m) 4))
                         (member-equal (list :send (fn-tcl-make-sess-term 0 4))
                                       (fn-tcl-result-events (fn-tcl-recv-contact s m now)))))))

(defthm fn-tcl-step-keeps-local
  (equal (fn-tcl-session-local (fn-tcl-result-session (fn-tcl-step s m now)))
         (fn-tcl-session-local s))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-tcl-sessionp fn-tcl-ext-decision))))

(defthm fn-tcl-retained-input-is-bounded
  (implies (and (fn-tcl-sessionp s)
                (fn-cbor-octet-listp buf)
                (fn-clock-timep now)
                (not (equal (fn-tcl-session-phase (fn-tcl-result-session (fn-tcl-drive s buf now)))
                            :closed)))
           (< (len (fn-tcl-result-unconsumed (fn-tcl-drive s buf now)))
              (fn-tcl-max-message (fn-tcl-segment-mru s))))
  :hints (("Goal" :induct (fn-tcl-drive s buf now)
           :in-theory (e/d (fn-tcl-drive fn-tcl-max-message)
                           (fn-tcl-step fn-tcl-input-error fn-tcl-sessionp
                            fn-tcl-drive-is-a-result)))))

(defthm fn-tcl-retained-transfer-is-bounded-by-definition
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-inbound s))
           (and (<= (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                    (fn-tcl-transfer-mru s))
                (<= (fn-tcl-lists-len (fn-tcl-inbound-staged (fn-tcl-session-inbound s)))
                    (fn-tcl-transfer-mru s))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory: the keystones stay; the outcome counter is list vocabulary.

(in-theory (disable fn-tcl-drive-is-a-result))
