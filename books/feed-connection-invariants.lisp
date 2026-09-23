; fn: carried validity of the outbound connection-phase table.
;
; fn-fc-tablep is a logical invariant over every retained peer framer.  The
; host establishes it once with fn-fc-table-initial-state and preserves it
; only through fn-fc-table-put/remove.  Served input checks the selected state;
; it does not rescan this table or every peer's retained input.
(in-package "ACL2")
(include-book "feed-connection")
(include-book "wire-invariants")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-fc-table-initial-state ()
  (declare (xargs :guard t))
  nil)

(defthm fn-fc-table-initial-state-is-table
  (fn-fc-tablep (fn-fc-table-initial-state)))

(local
 (defthm fn-fwi-input-is-chunk
   (implies (and (fn-fwi-statep st) (fn-fwi-chunkp octets))
            (fn-fwi-chunkp (fn-fwi-input st octets)))
   :hints (("Goal" :in-theory (enable fn-fwi-statep fn-fwi-chunkp
                                      fn-fwi-input)))))

(local
 (defthm fn-fc-wire-next-unconsumed-is-bounded-linear
   (implies (and (fn-wire-statep wire) (fn-wire-octet-listp octets))
            (<= (len (fn-wire-next-unconsumed (fn-wire-next wire octets)))
                (len octets)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-wire-next-unconsumed-is-bounded
                                    (wire-state wire)))))))

(local
 (defthm fn-fwi-wire-next-unconsumed-is-chunk
   (implies (and (fn-wire-statep wire) (fn-fwi-chunkp octets))
            (fn-fwi-chunkp
             (fn-wire-next-unconsumed (fn-wire-next wire octets))))
   :hints (("Goal"
            :use ((:instance fn-wire-next-unconsumed-is-bounded
                             (wire-state wire))
                  (:instance fn-wire-next-unconsumed-octet-listp
                             (wire-state wire)))
            :in-theory (enable fn-fwi-chunkp)))))

(local
 (defthm fn-fwi-from-wire-next-preserves-state
   (implies (and (fn-wire-statep wire) (fn-fwi-chunkp octets))
            (fn-fwi-statep
             (fn-fwi-next-state
              (fn-fwi-from-wire-next (fn-wire-next wire octets)))))
   :hints (("Goal"
            :use ((:instance fn-wire-next-preserves-statep
                             (wire-state wire))
                  (:instance fn-fwi-wire-next-unconsumed-is-chunk))
            :in-theory (enable fn-fwi-from-wire-next fn-fwi-next-state
                               fn-fwi-make-state fn-fwi-statep
                               fn-fwi-chunkp)))))

(local
 (defthm fn-fwi-step-preserves-state
   (implies (and (fn-fwi-statep st) (fn-fwi-chunkp octets))
            (fn-fwi-statep (fn-fwi-next-state (fn-fwi-step st octets))))
   :hints (("Goal" :cases ((fn-fwi-callp st octets))
                   :in-theory (enable fn-fwi-step fn-fwi-next-state
                                      fn-fwi-result fn-fwi-callp
                                      fn-fwi-statep)))))

(local
 (defthm fn-fc-with-input-phase-is-state
   (implies (and (fn-fc-statep st)
                 (fn-fwi-statep input)
                 (fn-fc-phasep phase))
            (fn-fc-statep (fn-fc-with-input-phase st input phase)))
   :hints (("Goal" :in-theory (e/d (fn-fc-statep
                                    fn-fc-with-input-phase
                                    fn-fc-make-state)
                                   (fn-fwi-statep fn-wire-octet-listp
                                    fn-wire-octetp fn-fap-tokenp))))))

(local
 (defthm fn-fc-from-line-preserves-state
   (implies (and (fn-fc-statep st) (fn-fwi-statep input))
            (fn-fc-statep
             (fn-fc-next-state (fn-fc-from-line st input line))))
   :hints (("Goal" :in-theory (e/d (fn-fc-from-line fn-fc-next-state
                                    fn-fc-result fn-fc-phasep)
                                   (fn-fc-statep fn-fc-with-input-phase
                                    fn-fwi-statep))))))

; What the step proof needs of a state and of a result, so that the state
; recognizer, the phase update and the line handler stay closed there and
; the two lemmas above do the work.
(local
 (defthm fn-fc-statep-input-and-phase
   (implies (fn-fc-statep st)
            (and (fn-fwi-statep (fn-fc-input st))
                 (fn-fc-phasep (fn-fc-phase st))))
   :hints (("Goal" :in-theory (e/d (fn-fc-statep)
                                   (fn-fwi-statep fn-fc-phasep fn-fc-input
                                    fn-fc-phase fn-wire-octet-listp
                                    fn-fap-tokenp))))))

(local
 (defthm fn-fc-next-state-of-result
   (equal (fn-fc-next-state (fn-fc-result kind st line)) st)
   :hints (("Goal" :in-theory (enable fn-fc-next-state fn-fc-result)))))

; The recognizers, the line handler and the phase update stay closed: this
; goal dispatches on the wire event's kind and each arm is one of the lemmas
; above.  Opened, ACL2 rewrote them inside out before those lemmas could
; match and split the state recognizer, the input framer's recognizer and
; the octet recognizers on every arm: 41.5 s and 12.0 M prover steps (t1-seam
; certify-20260923T000250Z-1473169); closed, under 0.1 s.
(defthm fn-fc-step-preserves-state
  (implies (fn-fc-statep st)
           (fn-fc-statep (fn-fc-next-state (fn-fc-step st octets))))
  :hints (("Goal" :cases ((fn-fwi-chunkp octets))
                  :in-theory (e/d (fn-fc-step)
                                  (fn-fc-next-state fn-fc-result
                                   fn-fc-statep fn-fc-from-line
                                   fn-fc-with-input-phase fn-fwi-statep
                                   fn-fwi-step fn-fwi-chunkp fn-fc-input
                                   fn-fc-phase fn-fwi-next-state fn-fwi-kind
                                   fn-fwi-line)))))

(defthm fn-fc-table-lookup-after-remove
  (equal (fn-fc-table-lookup peer (fn-fc-table-remove peer table)) nil)
  :hints (("Goal" :induct (fn-fc-table-remove peer table)
                  :in-theory (enable fn-fc-table-remove fn-fc-table-lookup))))

(defthm fn-fc-table-lookup-after-put
  (equal (fn-fc-table-lookup peer (fn-fc-table-put peer st table)) st)
  :hints (("Goal" :in-theory (enable fn-fc-table-put fn-fc-table-lookup))))

; The same posture as the put below: the entry recognizer asks for
; `fn-fc-statep' of the entry and that is the whole fact the lookup needs, so
; the state recognizers stay closed.  With them open this proof took 278-320
; s of every certification of this book (hbox certify-20260922T060312Z-2712514
; 319.1 s for the book; nextop certify-20260922T195818Z-16948, 277.9 s for
; this event alone); closed, it is under a second.
(defthm fn-fc-table-lookup-is-state
  (implies (and (fn-fc-tablep table)
                (fn-fc-table-lookup peer table))
           (fn-fc-statep (fn-fc-table-lookup peer table)))
  :hints (("Goal" :induct (fn-fc-table-lookup peer table)
                  :in-theory (e/d (fn-fc-tablep fn-fc-table-entryp
                                   fn-fc-table-lookup)
                                  (fn-fc-statep fn-fwi-statep
                                   fn-wire-octet-listp fn-wire-octetp)))))

(local
 (defthm fn-fc-table-name-member-of-remove
   (implies (fn-fc-table-memberp name
                                 (fn-fc-table-names
                                  (fn-fc-table-remove peer table)))
            (fn-fc-table-memberp name (fn-fc-table-names table)))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (enable fn-fc-table-remove fn-fc-table-names
                                      fn-fc-table-memberp)))))

(local
 (defthm fn-fc-table-unique-namesp-of-remove
   (implies (fn-fc-table-unique-namesp (fn-fc-table-names table))
            (fn-fc-table-unique-namesp
             (fn-fc-table-names (fn-fc-table-remove peer table))))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (enable fn-fc-table-remove fn-fc-table-names
                                      fn-fc-table-memberp
                                      fn-fc-table-unique-namesp)))))

(defthm fn-fc-table-remove-preserves-table
  (implies (fn-fc-tablep table)
           (fn-fc-tablep (fn-fc-table-remove peer table)))
  :hints (("Goal" :induct (fn-fc-table-remove peer table)
                  :in-theory (e/d (fn-fc-tablep fn-fc-table-remove
                                   fn-fc-table-names)
                                  (fn-fc-statep fn-fwi-statep
                                   fn-wire-octet-listp fn-wire-octetp)))))

(local
 (defthm fn-fc-table-removed-name-absent
   (implies (fn-fc-tablep table)
            (not (fn-fc-table-memberp
                  peer (fn-fc-table-names
                        (fn-fc-table-remove peer table)))))
   :hints (("Goal" :induct (fn-fc-table-remove peer table)
                   :in-theory (e/d (fn-fc-table-remove fn-fc-table-names
                                    fn-fc-table-memberp fn-fc-tablep
                                    fn-fc-table-entryp)
                                   (fn-fc-statep fn-fwi-statep
                                    fn-wire-octet-listp fn-wire-octetp))))))

(local
 (defthm fn-fc-tablep-implies-unique-names
   (implies (fn-fc-tablep table)
            (fn-fc-table-unique-namesp (fn-fc-table-names table)))
   :hints (("Goal" :in-theory (e/d (fn-fc-tablep fn-fc-table-names
                                    fn-fc-table-unique-namesp)
                                   (fn-fc-statep fn-fwi-statep
                                    fn-wire-octet-listp fn-wire-octetp))))))

; The table recognizers open here; the state recognizers must not.  With
; `fn-fc-statep' left enabled this goal splits it, `fn-fwi-statep' and the
; wire octet recognizers on every branch -- 101 subgoals for Goal, 104 for
; Subgoal 101, and the book is killed at the 1800 s per-book limit (hbox
; certify-20260922T025220Z-2602458 and certify-20260922T031240Z-2615431,
; 1800.041 s in the second; the same source certified in 21.4 s on
; 2026-09-21, certify-20260921T170420Z-2003857, before seven of its
; dependencies moved).  The `fn-fc-statep' hypothesis is the
; whole fact the put needs about `st', and the entry recognizer asks for
; exactly it, so the recognizer stays closed: AGENTS.md, no whole-state
; revalidation on a served path.
(defthm fn-fc-table-put-preserves-table
  (implies (and (stringp peer)
                (fn-fc-statep st)
                (fn-fc-tablep table))
           (fn-fc-tablep (fn-fc-table-put peer st table)))
  :hints (("Goal" :in-theory (e/d (fn-fc-table-put fn-fc-tablep
                                   fn-fc-table-entryp fn-fc-table-names
                                   fn-fc-table-unique-namesp)
                                  (fn-fc-statep fn-fwi-statep
                                   fn-wire-octet-listp fn-wire-octetp)))))

; =============================================================================
; The protected channel (PRF-047, PRF-051; plan 2026-09-22 T9c).
;
; THE SUBJECT IS WHAT THE HOST CALLS.  Two ACL2 functions move a peer's
; connection phase, and the host calls both on the entry it keeps in
; `fn-owner-feed-inputs':
;
;   host/owner-host.lisp:1374  (fn-fc-step input octets), inside
;     `fn-owner-feed-reply-chunk', which host/native/feed-service.lisp:256
;     calls for every socket read (and every retained-suffix drain);
;   host/owner-host.lisp:1279  (fn-fc-after-tls ...), inside
;     `fn-owner-feed-tls-established', which host/native/feed-service.lisp:194
;     calls once `fnn-tls-connect' has verified the peer's certificate
;     against the configured anchor and server name (feed-service.lisp:210).
;
; The step's KIND is the whole of what the host may do next
; (host/owner-host.lisp:1381-1418): :starttls, :auth-user, :auth-pass and
; :mode render and send one command (STARTTLS, AUTHINFO USER, AUTHINFO PASS,
; MODE STREAM); :tls starts the TLS handshake (feed-service.lisp:400);
; :ready installs the connection in the feed port with `(:feed-conn peer
; conn)' (owner-host.lisp:1237) and sets the link ready (feed-service.lisp:
; 398), and only a ready link is ticked for an offer (feed-service.lisp:415;
; `fn-feed-offer' in books/peer-feed wants a natp `fn-feed-conn', which only
; that install sets); :reply hands a post-ready line to the feed port.  So an
; IHAVE, CHECK or TAKETHIS on this connection is preceded by a :ready kind,
; and a credential leaves only on an :auth-user or :auth-pass kind.
;
; `fn-fc-drive' is the host's view of one connection incarnation: a list of
; events, each either a chunk (handed to `fn-fc-step') or the symbol :tls-up
; (handed to `fn-fc-after-tls'), and for each event one observation
; (KIND CODE TLS-UPP): the kind the host acts on, the response code of the
; line the step consumed (nil when it consumed none), and whether the event
; was the TLS report.  The host's order of calls is one such list; the
; theorems below quantify over every list, so they hold for any order the
; host could produce, including ones it does not.
;
; `fn-fc-gate-okp' is the property, written over observations only (it never
; reads the machine's phase): a stage counter that moves 0 -> 1 only on an
; observation (:tls 382), 1 -> 2 only on a TLS report the machine accepted,
; and 2 -> 3 only on a line coded 281 that the machine answered with :mode
; or :ready; a credential kind needs stage 2, and :mode, :ready or :reply
; need stage 3 when the connection carries a credential (2 when it carries
; none).  Implicit TLS has no STARTTLS exchange, so it starts at stage 1.
; What is trusted and not proved here: that the host reports :tls-up only
; after a verified handshake (OpenSSL's chain and hostname checks, and
; tests/test_native_tls_transport.py's wrong-anchor and wrong-hostname
; witnesses), and that the socket carries the bytes rendered.

(defun fn-fc-loginp (st)
  (declare (xargs :guard t))
  (if (fn-fc-user st) t nil))

(defun fn-fc-event-result (st ev)
  (declare (xargs :guard t))
  (if (equal ev :tls-up) (fn-fc-after-tls st) (fn-fc-step st ev)))

(defun fn-fc-line-code (st ev)
  "The response code of the line `fn-fc-step' consumes on EV, or nil."
  (declare (xargs :guard t))
  (if (and (not (equal ev :tls-up)) (fn-fc-statep st) (fn-fwi-chunkp ev))
      (let ((fwi (fn-fwi-step (fn-fc-input st) ev)))
        (if (equal (fn-fwi-kind fwi) :line)
            (fn-own-feed-response-code (fn-fwi-line fwi))
          nil))
    nil))

(defun fn-fc-drive (st events)
  (declare (xargs :guard t))
  (if (consp events)
      (let ((r (fn-fc-event-result st (car events))))
        (cons (list (fn-fc-kind r)
                    (fn-fc-line-code st (car events))
                    (equal (car events) :tls-up))
              (fn-fc-drive (fn-fc-next-state r) (cdr events))))
    nil))

(defun fn-fc-drive-state (st events)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-fc-drive-state (fn-fc-next-state (fn-fc-event-result st (car events)))
                         (cdr events))
    st))

(defun fn-fc-obs-kind (rec)
  (declare (xargs :guard t))
  (if (consp rec) (car rec) nil))
(defun fn-fc-obs-code (rec)
  (declare (xargs :guard t))
  (if (and (consp rec) (consp (cdr rec))) (cadr rec) nil))
(defun fn-fc-obs-tls-upp (rec)
  (declare (xargs :guard t))
  (if (and (consp rec) (consp (cdr rec)) (consp (cddr rec))) (caddr rec) nil))

(defun fn-fc-gate-start (security)
  (declare (xargs :guard t))
  (if (equal security :implicit) 1 0))

(defun fn-fc-gate-done (loginp)
  (declare (xargs :guard t))
  (if loginp 3 2))

(defun fn-fc-gate-next (k rec)
  (declare (xargs :guard t))
  (let ((kind (fn-fc-obs-kind rec))
        (code (fn-fc-obs-code rec))
        (tls-upp (fn-fc-obs-tls-upp rec)))
    (cond ((and (equal k 0) (not tls-upp) (equal kind :tls) (equal code 382)) 1)
          ((and (equal k 1) tls-upp (not (equal kind :invalid))) 2)
          ((and (equal k 2) (not tls-upp) (equal code 281)
                (member-equal kind '(:mode :ready)))
           3)
          (t k))))

(defun fn-fc-gate-allowsp (k loginp kind)
  (declare (xargs :guard t))
  (cond ((member-equal kind '(:mode :ready :reply))
         (and (natp k) (<= (fn-fc-gate-done loginp) k)))
        ((member-equal kind '(:auth-user :auth-pass))
         (and (natp k) (<= 2 k)))
        (t t)))

(defun fn-fc-gate-okp (k loginp obs)
  (declare (xargs :guard t :measure (acl2-count obs)))
  (if (consp obs)
      (let ((k2 (fn-fc-gate-next k (car obs))))
        (and (fn-fc-gate-allowsp k2 loginp (fn-fc-obs-kind (car obs)))
             (fn-fc-gate-okp k2 loginp (cdr obs))))
    t))

; The kinds on which the host sends a byte, starts a handshake, or makes the
; connection live.  A quiet observation list has none of them.
(defun fn-fc-effect-kindp (kind)
  (declare (xargs :guard t))
  (if (member-equal kind '(:starttls :tls :auth-user :auth-pass :mode :ready :reply))
      t nil))

(defun fn-fc-quiet-obsp (obs)
  (declare (xargs :guard t))
  (if (consp obs)
      (and (not (fn-fc-effect-kindp (fn-fc-obs-kind (car obs))))
           (fn-fc-quiet-obsp (cdr obs)))
    t))

; A peer record that requires a protected channel: its transport is STARTTLS
; or implicit TLS (`fn-owner-feed-dial-open' reads it from the record's
; transport, owner-host.lisp:1255-1259), or it carries a credential whose
; profile did not set the explicit clear-text permission (`(:authinfo PATH
; ALLOW-CLEAR)', RFC 4643 section 2.2's advice made a refusal).
(defun fn-fc-protected-profilep (st)
  (declare (xargs :guard t))
  (or (equal (fn-fc-security st) :starttls)
      (equal (fn-fc-security st) :implicit)
      (and (fn-fc-loginp st) (not (fn-fc-allow-clear st)))))

; The phase `fn-fc-initial-state' and `fn-fc-initial-auth-state' install,
; which `fn-owner-feed-dial-open' (owner-host.lisp:1264-1269) puts in the
; table for every new connection.
(defun fn-fc-opening-phasep (st)
  (declare (xargs :guard t))
  (equal (fn-fc-phase st)
         (if (equal (fn-fc-security st) :implicit) :tls :greeting)))

; Proof support: the least stage a phase can be reached at.
(defun fn-fc-gate-floor (st)
  (declare (xargs :guard t))
  (case (fn-fc-phase st)
    (:greeting (if (equal (fn-fc-security st) :implicit) 2 0))
    (:tls 1)
    ((:auth-user :auth-pass) 2)
    ((:mode :ready) (fn-fc-gate-done (fn-fc-loginp st)))
    (otherwise 0)))

(defun fn-fc-gate-induct (k st events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (consp events)
      (let ((r (fn-fc-event-result st (car events))))
        (fn-fc-gate-induct
         (fn-fc-gate-next k (list (fn-fc-kind r)
                                  (fn-fc-line-code st (car events))
                                  (equal (car events) :tls-up)))
         (fn-fc-next-state r) (cdr events)))
    (list k st)))

; Shape facts the keystones' proofs (and their teeth) use; exported so the
; teeth book's must-fails run the same proof with one hypothesis dropped.
(defthm fn-fc-statep-shape
  (implies (fn-fc-statep st)
           (and (true-listp st) (member-equal (len st) '(5 8))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-fc-statep))))

(defthm fn-fc-statep-security-cases
  (implies (fn-fc-statep st)
           (or (equal (fn-fc-security st) :clear)
               (equal (fn-fc-security st) :implicit)
               (equal (fn-fc-security st) :starttls)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-fc-statep)
                                  (fn-fc-security fn-fwi-statep)))))

(defthm fn-fc-with-input-phase-accessors
  (implies (and (true-listp st) (member-equal (len st) '(5 8)))
           (let ((nx (fn-fc-with-input-phase st input phase)))
             (and (equal (fn-fc-phase nx) phase)
                  (equal (fn-fc-security nx) (fn-fc-security st))
                  (equal (fn-fc-user nx) (fn-fc-user st))
                  (equal (fn-fc-pass nx) (fn-fc-pass st))
                  (equal (fn-fc-allow-clear nx) (fn-fc-allow-clear st)))))
  :hints (("Goal" :in-theory (enable fn-fc-with-input-phase fn-fc-make-state
                                     fn-fc-phase fn-fc-security fn-fc-user
                                     fn-fc-pass fn-fc-allow-clear
                                     fn-fc-streamingp fn-fc-conn
                                     fn-fc-input))))

(defthm fn-fc-fwi-line-needs-a-chunk
  (implies (equal (fn-fwi-kind (fn-fwi-step fwi octets)) :line)
           (fn-fwi-chunkp octets))
  :hints (("Goal" :in-theory (e/d (fn-fwi-step fn-fwi-callp fn-fwi-kind
                                   fn-fwi-result)
                                  (fn-fwi-chunkp fn-fwi-statep
                                   fn-fwi-from-wire-next fn-wire-next)))))

; One event keeps the gate: the step the host calls never emits a kind the
; stage does not allow, and the stage it reaches is at least the floor of the
; phase it leaves the connection in.
(defthm fn-fc-event-result-keeps-the-gate
  (implies (and (natp k)
                (<= (fn-fc-gate-floor st) k)
                (fn-fc-protected-profilep st))
           (let* ((r (fn-fc-event-result st ev))
                  (k2 (fn-fc-gate-next
                       k (list (fn-fc-kind r) (fn-fc-line-code st ev)
                               (equal ev :tls-up)))))
             (and (fn-fc-gate-allowsp k2 (fn-fc-loginp st) (fn-fc-kind r))
                  (natp k2)
                  (<= (fn-fc-gate-floor (fn-fc-next-state r)) k2)
                  (fn-fc-protected-profilep (fn-fc-next-state r))
                  (equal (fn-fc-loginp (fn-fc-next-state r))
                         (fn-fc-loginp st)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-fc-event-result fn-fc-step fn-fc-from-line
                                   fn-fc-after-tls fn-fc-begin-auth-or-mode
                                   fn-fc-after-auth fn-fc-result fn-fc-kind
                                   fn-fc-next-state fn-fc-line-code
                                   fn-fc-gate-next fn-fc-gate-allowsp
                                   fn-fc-gate-done fn-fc-gate-floor
                                   fn-fc-protected-profilep fn-fc-loginp
                                   fn-fc-obs-kind fn-fc-obs-code
                                   fn-fc-obs-tls-upp)
                                  (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                                   fn-own-feed-response-code
                                   fn-fc-greetingp fn-fc-mode-okp
                                   fn-fc-with-input-phase fn-fc-phase
                                   fn-fc-security fn-fc-user fn-fc-pass
                                   fn-fc-allow-clear
                                   fn-fc-input fn-fc-streamingp fn-fc-conn
                                   fn-fwi-kind fn-fwi-line fn-fwi-next-state)))))

(defthm fn-fc-gate-holds-above-the-floor
  (implies (and (natp k)
                (<= (fn-fc-gate-floor st) k)
                (fn-fc-protected-profilep st))
           (fn-fc-gate-okp k (fn-fc-loginp st) (fn-fc-drive st events)))
  :hints (("Goal" :induct (fn-fc-gate-induct k st events)
                  :in-theory (e/d (fn-fc-drive fn-fc-gate-okp fn-fc-obs-kind)
                                  (fn-fc-event-result fn-fc-gate-next
                                   fn-fc-gate-allowsp fn-fc-gate-floor
                                   fn-fc-protected-profilep fn-fc-loginp
                                   fn-fc-line-code fn-fc-kind fn-fc-next-state)))
          ("Subgoal *1/1" :use ((:instance fn-fc-event-result-keeps-the-gate
                                           (ev (car events)))))))

; KEYSTONE (PRF-047, PRF-051).  A connection opened for a peer record that
; requires a protected channel, driven by any sequence of reads and TLS
; reports: no MODE, no ready (so no IHAVE, CHECK or TAKETHIS) and no
; delivered reply until a 382 was read, the TLS layer was reported up, and
; -- when the peer record carries a credential -- a 281 was read; and no
; AUTHINFO USER or PASS until the 382 and the TLS report.  A credential
; profile without the clear-text permission on a clear transport therefore
; never sends the credential and never goes live, since neither the 382 nor
; the TLS report can move that machine.
(defthm fn-fc-offers-and-credentials-wait-for-tls-and-login
  (implies (and (fn-fc-protected-profilep st)
                (fn-fc-opening-phasep st))
           (fn-fc-gate-okp (fn-fc-gate-start (fn-fc-security st))
                           (fn-fc-loginp st)
                           (fn-fc-drive st events)))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-fc-gate-holds-above-the-floor
                                   (k (fn-fc-gate-start (fn-fc-security st)))))
                  :in-theory (e/d (fn-fc-opening-phasep fn-fc-gate-floor
                                   fn-fc-gate-start)
                                  (fn-fc-gate-holds-above-the-floor
                                   fn-fc-protected-profilep fn-fc-loginp
                                   fn-fc-drive fn-fc-gate-okp)))))

(defthm fn-fc-event-result-of-a-closed-connection
  (implies (equal (fn-fc-phase st) :closed)
           (let ((r (fn-fc-event-result st ev)))
             (and (not (fn-fc-effect-kindp (fn-fc-kind r)))
                  (equal (fn-fc-phase (fn-fc-next-state r)) :closed))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-fc-event-result fn-fc-step fn-fc-from-line
                                   fn-fc-after-tls fn-fc-result fn-fc-kind
                                   fn-fc-next-state fn-fc-effect-kindp)
                                  (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                                   fn-own-feed-response-code
                                   fn-fc-with-input-phase fn-fc-phase
                                   fn-fc-security fn-fc-user fn-fc-allow-clear
                                   fn-fc-input fn-fc-streamingp fn-fc-conn
                                   fn-fwi-kind fn-fwi-line fn-fwi-next-state)))))

; A closed connection does nothing the host acts on, whatever it is fed.
(defthm fn-fc-closed-connection-stays-quiet
  (implies (equal (fn-fc-phase st) :closed)
           (fn-fc-quiet-obsp (fn-fc-drive st events)))
  :hints (("Goal" :induct (fn-fc-drive st events)
                  :in-theory (e/d (fn-fc-drive fn-fc-quiet-obsp fn-fc-obs-kind)
                                  (fn-fc-event-result fn-fc-effect-kindp
                                   fn-fc-line-code fn-fc-kind
                                   fn-fc-next-state fn-fc-phase)))))

; KEYSTONE (PRF-051).  A refused login ends the connection without an offer:
; in either login phase, a line whose code is not 281 (and, answering USER,
; not 381) is :refused -- which owner-host.lisp:1356 reports as
; :connection-refused and feed-service.lisp:391-395 answers by recording the
; peer-local loss and closing the socket -- and the connection is closed, so
; nothing fed to it afterwards produces a command, a handshake or an offer.
(defthm fn-fc-refused-login-closes-without-an-offer
  (implies (and (fn-fc-statep st)
                (member-equal (fn-fc-phase st) '(:auth-user :auth-pass))
                (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
                (not (equal (fn-own-feed-response-code
                             (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
                            281))
                (or (equal (fn-fc-phase st) :auth-pass)
                    (not (equal (fn-own-feed-response-code
                                 (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
                                381))))
           (let ((r (fn-fc-step st octets)))
             (and (equal (fn-fc-kind r) :refused)
                  (equal (fn-fc-phase (fn-fc-next-state r)) :closed)
                  (fn-fc-quiet-obsp (fn-fc-drive (fn-fc-next-state r) events)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-fc-step fn-fc-from-line fn-fc-result
                                   fn-fc-kind fn-fc-next-state)
                                  (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                                   fn-own-feed-response-code fn-fc-drive
                                   fn-fc-with-input-phase fn-fc-phase
                                   fn-fc-security fn-fc-user fn-fc-allow-clear
                                   fn-fc-input fn-fc-streamingp fn-fc-conn
                                   fn-fwi-kind fn-fwi-line fn-fwi-next-state)))))

; KEYSTONE (PRF-047).  A peer that does not take STARTTLS is not sent the
; credential: answered with anything but 382 (RFC 4642 section 2.2.1: 502
; or 580 from a peer that cannot or will not), the connection is refused
; and closed and stays quiet, so no AUTHINFO line and no offer follows on
; it and nothing falls back to clear text.  fn does not read CAPABILITIES
; before STARTTLS; the peer's answer to STARTTLS is the advertisement this
; machine acts on.
(defthm fn-fc-starttls-refusal-closes-before-the-credential
  (implies (and (fn-fc-statep st)
                (equal (fn-fc-phase st) :starttls)
                (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
                (not (equal (fn-own-feed-response-code
                             (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
                            382)))
           (let ((r (fn-fc-step st octets)))
             (and (equal (fn-fc-kind r) :refused)
                  (equal (fn-fc-phase (fn-fc-next-state r)) :closed)
                  (fn-fc-quiet-obsp (fn-fc-drive (fn-fc-next-state r) events)))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-fc-step fn-fc-from-line fn-fc-result
                                   fn-fc-kind fn-fc-next-state)
                                  (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                                   fn-own-feed-response-code fn-fc-drive
                                   fn-fc-with-input-phase fn-fc-phase
                                   fn-fc-security fn-fc-user fn-fc-allow-clear
                                   fn-fc-input fn-fc-streamingp fn-fc-conn
                                   fn-fwi-kind fn-fwi-line fn-fwi-next-state)))))

; -----------------------------------------------------------------------------
; Secret custody on the wire (PRF-051).  The rendered AUTHINFO lines carry
; the profile's bytes verbatim and nothing else: one line each, so a
; credential cannot smuggle a second command into the connection.  The
; subject is `fn-fc-auth-user-command' and `fn-fc-auth-pass-command', which
; host/owner-host.lisp:1288, :1388 and :1393 call on the state the step just
; produced.

(local
 (defthm fn-fc-wire-reverse-octets-aux-is-revappend
   (equal (fn-wire-reverse-octets-aux x acc) (revappend x acc))
   :hints (("Goal" :in-theory (enable fn-wire-reverse-octets-aux)))))

(local
 (defthm fn-fc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-fc-wire-append-is-append
   (equal (fn-wire-append a b) (append a b))
   :hints (("Goal" :in-theory (enable fn-wire-append)))))

; An octet list with no CR and no LF: the body of exactly one command line.
(defun fn-fc-line-bodyp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-wire-octetp (car xs))
           (not (equal (car xs) 13))
           (not (equal (car xs) 10))
           (fn-fc-line-bodyp (cdr xs)))
    (null xs)))

(local
 (defthm fn-fc-line-body-is-true-list
   (implies (fn-fc-line-bodyp xs) (true-listp xs))
   :rule-classes :forward-chaining))

(local
 (defthm fn-fc-command-line-aux-of-a-line-body
   (implies (and (fn-fc-line-bodyp xs)
                 (<= (+ 2 (len xs)) (nfix fuel)))
            (equal (fn-wire-outbound-command-line-aux (append xs '(13 10)) fuel rev)
                   (fn-wire-outbound-ok
                    (list (fn-wire-append (append (rev rev) xs) '(13 10))
                          nil))))
   :hints (("Goal" :induct (fn-wire-outbound-command-line-aux xs fuel rev)
                   :in-theory (enable fn-wire-outbound-command-line-aux
                                      fn-wire-reverse-octets)))))

(local
 (defthm fn-fc-line-body-of-printable-token
   (implies (and (fn-nntp-printable-tokenp x) (true-listp x))
            (fn-fc-line-bodyp x))
   :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp
                                      fn-wire-octetp)))))

(local
 (defthm fn-fc-line-body-of-append
   (implies (and (fn-fc-line-bodyp a) (fn-fc-line-bodyp b))
            (fn-fc-line-bodyp (append a b)))))

(defthm fn-fc-auth-command-renders-a-token-verbatim
  (implies (and (fn-fap-tokenp token) (true-listp token)
                (member-equal prefix (list *fn-fc-auth-user-prefix*
                                           *fn-fc-auth-pass-prefix*)))
           (equal (fn-fc-auth-command prefix token)
                  (append prefix token '(13 10))))
  :hints (("Goal" :do-not-induct t
                  :use ((:instance fn-fc-command-line-aux-of-a-line-body
                                   (xs (append prefix token))
                                   (fuel *fn-nntp-max-initial-line-octets*)
                                   (rev nil)))
                  :in-theory (e/d (fn-fc-auth-command fn-fap-tokenp
                                   fn-wire-outbound-command-line
                                   fn-wire-outbound-okp fn-wire-outbound-ok
                                   fn-wire-outbound-octets)
                                  (fn-fc-command-line-aux-of-a-line-body
                                   fn-nntp-printable-tokenp)))))

(defthm fn-fc-auth-user-command-sends-the-configured-name-alone
  (implies (and (fn-fap-tokenp (fn-fc-user st)) (true-listp (fn-fc-user st)))
           (equal (fn-fc-auth-user-command st)
                  (append *fn-fc-auth-user-prefix* (fn-fc-user st) '(13 10))))
  :hints (("Goal" :in-theory (e/d (fn-fc-auth-user-command)
                                  (fn-fc-auth-command fn-fap-tokenp)))))

(defthm fn-fc-auth-pass-command-sends-the-configured-secret-alone
  (implies (and (fn-fap-tokenp (fn-fc-pass st)) (true-listp (fn-fc-pass st)))
           (equal (fn-fc-auth-pass-command st)
                  (append *fn-fc-auth-pass-prefix* (fn-fc-pass st) '(13 10))))
  :hints (("Goal" :in-theory (e/d (fn-fc-auth-pass-command)
                                  (fn-fc-auth-command fn-fap-tokenp)))))

(defthm fn-fc-event-result-keeps-the-credential
  (let ((nx (fn-fc-next-state (fn-fc-event-result st ev))))
    (and (equal (fn-fc-user nx) (fn-fc-user st))
         (equal (fn-fc-pass nx) (fn-fc-pass st))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn-fc-event-result fn-fc-step fn-fc-from-line
                                   fn-fc-after-tls fn-fc-begin-auth-or-mode
                                   fn-fc-after-auth fn-fc-result
                                   fn-fc-next-state)
                                  (fn-fc-statep fn-fwi-step fn-fwi-chunkp
                                   fn-own-feed-response-code
                                   fn-fc-greetingp fn-fc-mode-okp
                                   fn-fc-with-input-phase fn-fc-phase
                                   fn-fc-security fn-fc-user fn-fc-pass
                                   fn-fc-allow-clear
                                   fn-fc-input fn-fc-streamingp fn-fc-conn
                                   fn-fwi-kind fn-fwi-line fn-fwi-next-state)))))

(defthm fn-fc-drive-state-keeps-the-credential
  (and (equal (fn-fc-user (fn-fc-drive-state st events)) (fn-fc-user st))
       (equal (fn-fc-pass (fn-fc-drive-state st events)) (fn-fc-pass st)))
  :hints (("Goal" :induct (fn-fc-drive-state st events)
                  :in-theory (e/d (fn-fc-drive-state)
                                  (fn-fc-event-result fn-fc-next-state
                                   fn-fc-user fn-fc-pass)))))

;
(defthm fn-fc-auth-commands-without-a-credential
  (and (implies (not (fn-fc-user st))
                (equal (fn-fc-auth-user-command st)
                       (append *fn-fc-auth-user-prefix* nil '(13 10))))
       (implies (not (fn-fc-pass st))
                (equal (fn-fc-auth-pass-command st)
                       (append *fn-fc-auth-pass-prefix* nil '(13 10)))))
  :hints (("Goal" :in-theory (enable fn-fc-auth-user-command
                                     fn-fc-auth-pass-command))))

; KEYSTONE (PRF-051).  The composition the host performs: the bytes of the
; profile file go through `fn-fap-decode' (host/native/feed-service.lisp:172,
; through `fn-owner-feed-profile-decode'), the decoded name and secret are
; installed by `fn-owner-feed-dial-open' (owner-host.lisp:1267), and the
; connection then reads and is told whatever it is -- in every state it can
; reach, the USER and PASS lines the host would render are the prefix, the
; decoded field's bytes and CRLF, one line each.  No hypothesis: a profile
; ACL2 refuses decodes to no name and no secret (and the host does not dial
; on it, feed-service.lisp:174-176).  WHEN the lines are sent is
; `fn-fc-offers-and-credentials-wait-for-tls-and-login'; this one is WHAT.
(defthm fn-fc-decoded-profile-renders-verbatim-in-every-state
  (let ((st (fn-fc-drive-state
             (fn-fc-initial-auth-state streamingp conn security
                                       (cadr (fn-fap-decode profile))
                                       (caddr (fn-fap-decode profile))
                                       allow-clear)
             events)))
    (and (equal (fn-fc-auth-user-command st)
                (append *fn-fc-auth-user-prefix*
                        (cadr (fn-fap-decode profile)) '(13 10)))
         (equal (fn-fc-auth-pass-command st)
                (append *fn-fc-auth-pass-prefix*
                        (caddr (fn-fap-decode profile)) '(13 10)))))
  :hints (("Goal" :do-not-induct t
                  :cases ((equal (car (fn-fap-decode profile)) :ok))
                  :use ((:instance fn-fap-decode-yields-two-renderable-tokens
                                   (octets profile)))
                  :in-theory (e/d (fn-fc-initial-auth-state fn-fc-user fn-fc-pass)
                                  (fn-fap-tokenp
                                   fn-fap-decode-yields-two-renderable-tokens
                                   fn-fc-drive-state fn-fc-auth-user-command
                                   fn-fc-auth-pass-command)))))
