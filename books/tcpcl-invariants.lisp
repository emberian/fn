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
; The four transitions the profile named (w9/dtn-e2e, 2026-09-20:
; FN-TCL-STEP 481,747 frames / 81 tries, FN-TCL-RECV-SEGMENT 213,787/19,
; FN-TCL-RECV-INIT 182,438/19, FN-TCL-BROKEN-STREAM 130,858/57) are closed
; for the whole book and opened at the forms that need them.  The enable
; above is wholesale, so they were open everywhere -- including under the
; subgoal `:in-theory' hints below, because a subgoal's `:in-theory' is
; evaluated against the book's CURRENT theory and not against its parent
; goal's: C1's ("Subgoal *1/3" :in-theory (enable fn-tcl-drive-is-a-result))
; undid C1's own Goal `(e/d ... (fn-tcl-step ...))' and reopened the step
; function under every subgoal of the fold.  Measured: with nothing else
; changed, C1 went from 0.42 s to 0.05 s when this line closed them.
; Both whole-state recognizers are named here, and they must be: the
; vocabulary now holds two of them, and fn-tcl-drive's totality test names
; fn-tcl-session-cheapp, so an open one turns every expansion of
; fn-tcl-drive into a case split over its conjuncts and their
; sub-recognizers -- 8844 subgoals for fn-tcl-drive-is-a-result when
; w9/dtn-e2e first merged the guard change.
(local (in-theory (disable fn-tcl-sessionp fn-tcl-session-cheapp fn-tcl-messagep
                           fn-tcl-step fn-tcl-recv-segment fn-tcl-recv-init
                           fn-tcl-broken-stream)))
; fn-tcl-session-cheapp reaches this book only as fn-tcl-drive's totality
; test, and the one rewrite fn-tcl-sessionp-is-cheap discharges it wherever
; the session is known.  Everything else the cheap recognizer exports is put
; aside under one name: the whole family, facts and forward-chaining fields
; and preservation together, because the forward-chaining half is what costs
; -- it runs to fixpoint beside the fn-tcl-sessionp family on every goal
; carrying either recognizer's term, which C1 measured as
; `Time: 2688.15 seconds (prove: 0.02, print: 0.00, other: 2688.13)`.
; Naming only the preservation chain here (configuration A' of
; HANDOFF-w9-dtn-e2e) left C1 open at 2688 s: it was the wrong half.
(local (in-theory (disable fn-tcl-cheap-rules)))

(local (defthm fn-tcl-append-assoc
         (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn-tcl-append-nil
         (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-tcl-member-equal-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))
(local (defthm fn-tcl-car-append
         (implies (consp a) (equal (car (append a b)) (car a)))))
(local (defthm fn-tcl-consp-append
         (implies (consp a) (consp (append a b)))))
; C1's decode-error case appends the closing events to the no-op's nil.
(local (defthm fn-tcl-input-error-events-true-listp
         (true-listp (fn-tcl-result-events (fn-tcl-input-error s header reason now)))))

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
           ; fn-tcl-segment-mru stays closed so that
           ; fn-tcl-decode-for-yields-message meets fn-tcl-step-preserves-sessionp
           :in-theory (e/d (fn-tcl-drive)
                           (fn-tcl-step fn-tcl-decode-for fn-tcl-input-error
                            fn-tcl-drive-is-a-result fn-tcl-segment-mru)))
          ; the consuming case: the split's right side is the whole drive
          ; rebuilt
          ("Subgoal *1/3" :in-theory (enable fn-tcl-drive-is-a-result))
          ; the need case: the left part keeps the whole buffer, so the
          ; right side is the whole drive rebuilt here too.  It needed no
          ; rule while fn-tcl-drive's totality test was the literal
          ; (fn-tcl-sessionp s) of this theorem's own hypothesis; with the
          ; test naming fn-tcl-session-cheapp the two sides no longer open
          ; to the same term and Subgoal *1/2'4' is fn-tcl-drive-is-a-result.
          ("Subgoal *1/2" :expand ((fn-tcl-drive s (append left right) now))
                          :in-theory (enable fn-tcl-drive-is-a-result))
          ; the base case: an empty or closed left leaves the whole drive,
          ; rebuilt, on the right
          ("Subgoal *1/1" :expand ((fn-tcl-drive s (append left right) now))
                          :in-theory (enable fn-tcl-drive-is-a-result))
          ("Subgoal *1/4" :in-theory (enable fn-tcl-drive-is-a-result))))

; -----------------------------------------------------------------------------
; C2.  A final acknowledgement means every segment.
;
; The recognizer stays CLOSED through this section.  Opening it here (the
; wave-4 lane's `(in-theory (enable fn-tcl-sessionp))` plus `:do-not-induct t`)
; put the eleven conjuncts of fn-tcl-sessionp, each itself a sub-recognizer
; over a record, into the clause and split it into 1082 subgoals before the
; segment cases were reached.  The two facts C2 actually needs about the live
; transfer -- that received-len is the measured length of the staged segments,
; and that a declared Transfer Length is not below it -- arrive through the
; forward-chaining field facts of books/tcpcl-session.lisp
; (fn-tcl-sessionp-forward-inbound, fn-tcl-inboundp-forward-fields,
; fn-tcl-inboundp-forward-total), which is what they were written for.

; fn-tcl-concat-rev accumulates `(append data nil)`, and the length of the
; delivered data is measured through it; fn-tcl-append-nil above needs
; true-listp, which the closed recognizer does not hand over.
(local (defthm fn-tcl-len-append
         (equal (len (append a b)) (+ (len a) (len b)))))

; The theory C2 reasons in: the segment path and the result builders are
; open, every other branch of fn-tcl-step and every recognizer is shut.
(local (deftheory fn-tcl-c2-closed
  '(fn-tcl-sessionp fn-tcl-paramsp fn-tcl-peer-initp fn-tcl-negotiatedp
    fn-tcl-inboundp fn-tcl-outboundp fn-tcl-messagep
    fn-tcl-ext-decision fn-tcl-recv-contact fn-tcl-recv-init fn-tcl-recv-ack
    fn-tcl-recv-refuse fn-tcl-recv-term fn-tcl-unexpected fn-tcl-pump
    fn-tcl-touch-rx)))

; Only fn-tcl-complete emits :bundle-received.  Each of the other branches of
; fn-tcl-step is dismissed by opening that one branch with everything else
; closed, so that C2 itself never opens them.
(local (defthm fn-tcl-recv-contact-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-recv-contact s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-contact s m now))))))

(local (defthm fn-tcl-recv-init-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-recv-init s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-init s m now))))))

(local (defthm fn-tcl-unexpected-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-unexpected s header now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-unexpected s header now))))))

(local (defthm fn-tcl-recv-ack-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-recv-ack s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-ack s m now))))))

(local (defthm fn-tcl-recv-refuse-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-recv-refuse s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-refuse s m now))))))

(local (defthm fn-tcl-recv-term-emits-no-bundle-received
         (not (member-equal (list :bundle-received id data)
                            (fn-tcl-result-events (fn-tcl-recv-term s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-term s m now))))))

; The content of C2, at the transition that owns it.  fn-tcl-recv-segment
; reaches fn-tcl-complete on exactly two paths: a START+END segment of a
; transfer with nothing live, and an END segment of the live transfer.  On
; the first the delivered data is the segment's own; on the second it is the
; staged segments in arrival order followed by this one, whose length is
; received-len + this segment, and received-len is the measured length of
; the staged list because fn-tcl-inboundp carries that equation.
(local
 (defthm fn-tcl-recv-segment-final-ack-means-every-segment
   (implies (and (fn-tcl-sessionp s)
                 (member-equal (list :bundle-received id data)
                               (fn-tcl-result-events (fn-tcl-recv-segment s m now))))
            (and (equal id (fn-tcl-xfer-segment-xfer-id m))
                 (fn-tcl-flag-end (fn-tcl-xfer-segment-flags m))
                 (if (fn-tcl-session-inbound s)
                     (and (not (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
                          (equal id (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s))))
                   (fn-tcl-flag-start (fn-tcl-xfer-segment-flags m)))
                 (null (fn-tcl-session-inbound
                        (fn-tcl-result-session (fn-tcl-recv-segment s m now))))
                 (equal (len data)
                        (+ (if (fn-tcl-session-inbound s)
                               (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                             0)
                           (len (fn-tcl-xfer-segment-data m))))
                 (member-equal (list :send (fn-tcl-make-xfer-ack
                                            (fn-tcl-xfer-segment-flags m) id (len data)))
                               (fn-tcl-result-events (fn-tcl-recv-segment s m now)))
                 (implies (and (fn-tcl-session-inbound s)
                               (fn-tcl-inbound-total (fn-tcl-session-inbound s)))
                          (equal (fn-tcl-inbound-total (fn-tcl-session-inbound s))
                                 (len data)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-tcl-broken-stream) (fn-tcl-c2-closed))
            :expand ((fn-tcl-recv-segment s m now))))))

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
  ; an equality with the variable id on its left is not a rewrite rule
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-tcl-recv-segment-final-ack-means-every-segment
                            (s (fn-tcl-touch-rx s now))))
           :in-theory (e/d (fn-tcl-step fn-tcl-settle)
                           (fn-tcl-c2-closed fn-tcl-recv-segment
                            fn-tcl-complete fn-tcl-stage fn-tcl-refuse
                            fn-tcl-broken-stream)))))

; Which branches of fn-tcl-step can leave an inbound record behind.  Only
; fn-tcl-stage builds one; the contact exchange clears it, and every other
; branch carries the record it was given.  Proved one branch at a time so
; that the theorem below keeps the recognizer closed.
(local (defthm fn-tcl-recv-contact-creates-no-inbound
         (not (fn-tcl-session-inbound
               (fn-tcl-result-session (fn-tcl-recv-contact s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-contact s m now))))))

(local (defthm fn-tcl-recv-init-creates-no-inbound
         (not (fn-tcl-session-inbound
               (fn-tcl-result-session (fn-tcl-recv-init s m now))))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-init s m now))))))

(local (defthm fn-tcl-unexpected-keeps-inbound
         (equal (fn-tcl-session-inbound
                 (fn-tcl-result-session (fn-tcl-unexpected s header now)))
                (fn-tcl-session-inbound s))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-unexpected s header now))))))

(local (defthm fn-tcl-recv-ack-keeps-inbound
         (equal (fn-tcl-session-inbound
                 (fn-tcl-result-session (fn-tcl-recv-ack s m now)))
                (fn-tcl-session-inbound s))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-ack s m now))))))

(local (defthm fn-tcl-recv-refuse-keeps-inbound
         (equal (fn-tcl-session-inbound
                 (fn-tcl-result-session (fn-tcl-recv-refuse s m now)))
                (fn-tcl-session-inbound s))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-refuse s m now))))))

(local (defthm fn-tcl-recv-term-keeps-inbound
         (equal (fn-tcl-session-inbound
                 (fn-tcl-result-session (fn-tcl-recv-term s m now)))
                (fn-tcl-session-inbound s))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-term s m now))))))

; The carried sum is the measurement of the staged segments: the theorem
; above speaks of received-len, and this says what it is.
(defthm fn-tcl-received-len-is-staged-length-by-definition
  (implies (and (fn-tcl-sessionp s) (fn-tcl-session-inbound s))
           (equal (fn-tcl-inbound-received-len (fn-tcl-session-inbound s))
                  (fn-tcl-lists-len (fn-tcl-inbound-staged (fn-tcl-session-inbound s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-tcl-c2-closed))))

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
           :in-theory (e/d (fn-tcl-step fn-tcl-settle fn-tcl-recv-segment
                            fn-tcl-broken-stream)
                           (fn-tcl-c2-closed)))))

; The recognizer stays CLOSED from here too.  C3 and C4 were written against
; an open one, and that cost 596.12 s of this book's 609.53 s (hbox,
; certify-20260920T230902Z-1283742): six forms whose clauses carried the
; eleven sub-recognizers of fn-tcl-sessionp.  What they actually need about
; a field arrives by forward chaining, as it does in C2 above.

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
           :in-theory (e/d (fn-tcl-messagep fn-tcl-step fn-tcl-recv-segment
                            fn-tcl-recv-init fn-tcl-broken-stream)
                           (fn-tcl-ext-decision)))))

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
           :in-theory (e/d (fn-tcl-messagep fn-tcl-step fn-tcl-recv-segment
                            fn-tcl-recv-init fn-tcl-broken-stream)
                           (fn-tcl-ext-decision)))))

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

; The interleaving branch of the transition that owns it: a segment whose
; Transfer ID is not the live transfer's (or a second START) is the broken
; stream of section 5.2.2, whatever the rest of the session holds.  Proved
; with the recognizer closed, as C2 measured: the branch test does not read
; a single conjunct of fn-tcl-sessionp.
(local (defthm fn-tcl-recv-segment-interleave-is-broken-stream
         (implies (and (fn-tcl-session-inbound s)
                       (not (equal (fn-tcl-xfer-segment-xfer-id m)
                                   (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))))
                  (equal (fn-tcl-recv-segment s m now)
                         (fn-tcl-broken-stream
                          s (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)) now)))
         :hints (("Goal" :in-theory (disable fn-tcl-c2-closed)
                  :expand ((fn-tcl-recv-segment s m now))))))

; What a broken stream leaves behind, after fn-tcl-settle has had its say.
; The session it hands back is in Ending -- unless the SESS_TERM handshake
; was already complete and nothing is outbound, in which case clearing the
; inbound transfer is the last thing "Transfers Done" was waiting for and
; the session closes in the same step (section 6.1).  That case is why the
; wave-4 statement of C4 below, which asserted :ending outright, is not a
; theorem: see specs/tcpcl.md section 6 and the witness *t-b-inter-both* in
; tests/acl2/tcpcl-tests.lisp.  Cited by :use so that the constructor in
; the event survives evaluation on both sides (a rewrite rule whose
; conclusion holds the ground term (fn-tcl-make-msg-reject 3 1) does not
; match the goal, where it has already been evaluated to a constant).
(local (defthm fn-tcl-settle-of-broken-stream
         (and (not (fn-tcl-session-inbound
                    (fn-tcl-result-session
                     (fn-tcl-settle (fn-tcl-broken-stream s live-id now)))))
              (equal (fn-tcl-session-phase
                      (fn-tcl-result-session
                       (fn-tcl-settle (fn-tcl-broken-stream s live-id now))))
                     (if (and (equal (fn-tcl-session-term s) :both)
                              (not (fn-tcl-session-outbound s)))
                         :closed
                       :ending))
              (member-equal (list :send (fn-tcl-make-msg-reject 3 1))
                            (fn-tcl-result-events
                             (fn-tcl-settle (fn-tcl-broken-stream s live-id now))))
              (implies live-id
                       (member-equal (list :inbound-refused live-id 3)
                                     (fn-tcl-result-events
                                      (fn-tcl-settle (fn-tcl-broken-stream s live-id now)))))
              (not (member-equal (list :bundle-received id data)
                                 (fn-tcl-result-events
                                  (fn-tcl-settle (fn-tcl-broken-stream s live-id now))))))
         :rule-classes nil
         :hints (("Goal" :in-theory (e/d (fn-tcl-broken-stream)
                                         (fn-tcl-c2-closed))))))

; C4, first theorem: one transfer at a time per direction (RFC 9174
; section 5.2).  A segment for another Transfer ID while one is live never
; opens a second transfer: the live one is refused Retransmit, MSG_REJECT
; Message Unexpected is sent, nothing is delivered, and the session stops
; accepting transfers -- Ending, or Closed when this was the last thing the
; SESS_TERM handshake was waiting for.  The phase is stated exactly, not as
; a disjunction: the two cases are separated by the session's own term
; field.
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
                ; the live transfer is refused Retransmit, not completed
                (member-equal (list :inbound-refused
                                    (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)) 3)
                              (fn-tcl-result-events (fn-tcl-step s m now)))
                (not (member-equal (list :bundle-received id data)
                                   (fn-tcl-result-events (fn-tcl-step s m now))))
                (equal (fn-tcl-session-phase (fn-tcl-result-session (fn-tcl-step s m now)))
                       (if (and (equal (fn-tcl-session-term s) :both)
                                (not (fn-tcl-session-outbound s)))
                           :closed
                         :ending))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-tcl-settle-of-broken-stream
                            (s (fn-tcl-touch-rx s now))
                            (live-id (fn-tcl-inbound-xfer-id (fn-tcl-session-inbound s)))))
           :in-theory (e/d (fn-tcl-step)
                           (fn-tcl-c2-closed fn-tcl-settle fn-tcl-recv-segment
                            fn-tcl-broken-stream)))))

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
           :in-theory (e/d (fn-tcl-messagep fn-tcl-step fn-tcl-recv-segment)
                           (fn-tcl-ext-decision)))))

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
           :in-theory (e/d (fn-tcl-messagep fn-tcl-step)
                           (fn-tcl-ext-decision fn-tcl-recv-segment
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
           :in-theory (e/d (fn-tcl-step fn-tcl-recv-segment fn-tcl-recv-init
                            fn-tcl-broken-stream)
                           (fn-tcl-sessionp fn-tcl-ext-decision)))))

; The two "need more input" cases of the fold below: the decoder keeps the
; whole buffer, so the carry is bounded by the decoder's own need bound.
; Both bounds are keystones of books/tcpcl-octets; they are restated here
; against the opened `fn-tcl-max-message` (the fold's hint opens it), which
; is what makes them visible to linear arithmetic at the induction step:
; fn-tcl-need-means-short-buffer is triggered on (len buf) with `mru` free,
; and fn-tcl-need-means-short-buffer-contact is a rewrite rule only, so
; neither fires on the goal (fn-tcl-max-message mru) leaves behind.  The
; contact bound is cited with its own rule disabled: enabled, it rewrites
; the cited instance to T before linear arithmetic can use it.
(local (defthm fn-tcl-need-message-under-max
         (implies (and (fn-cbor-octet-listp buf) (natp mru)
                       (fn-tcl-parse-needp (fn-tcl-decode-message buf mru)))
                  (< (len buf) (+ 5145 mru)))
         :hints (("Goal" :in-theory (e/d (fn-tcl-max-message)
                                         (fn-tcl-need-means-short-buffer))
                  :use fn-tcl-need-means-short-buffer))))

(local (defthm fn-tcl-need-contact-under-max
         (implies (and (natp mru) (fn-tcl-parse-needp (fn-tcl-decode-contact buf)))
                  (< (len buf) (+ 5145 mru)))
         :hints (("Goal" :use fn-tcl-need-means-short-buffer-contact
                  :in-theory (disable fn-tcl-need-means-short-buffer-contact)))))

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
