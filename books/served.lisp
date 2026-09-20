; The served path of the NNTP reader, in logic mode, with POST plugged in.
;
; Before this book the served path was split in two untrusted halves: the
; `while pending:' loop of tools/run_reader.py fed one chunk at a time into
; `fn-reader-chunk' (host/reader-host.lisp, :program mode), which consumed at
; most one wire event and handed the unconsumed suffix back to Python.  The
; two together computed `fn-wire-drive' followed by `fn-nntp-step' per event,
; and no theorem said so.  That is the wire `pending_subject' note and packet
; P1 of specs/node-functionality.md section 6.
;
; This book writes that loop once, in logic mode, with guard `t' verified:
; `fn-served-step' is one socket read.  The host performs exactly one call of
; it per read and keeps no protocol state of its own, so the subject of every
; theorem below is the function host/reader-host.lisp `fn-reader-chunk' calls.
;
; The loop is a fold over the read's octets, one byte at a time
; (`fn-wire-feed-byte', which is what `fn-wire-drive' computes by
; `fn-wire-drive-is-feed-proper'), and the dispatcher runs on each framed
; event before the next byte is framed.  That order is what POST needs: the
; 340 offer from `fn-auth-step' (books/nntp-auth.lisp, over
; books/peer-inbound.lisp and books/nntp-post.lisp) carries a
; `:begin-article' effect, and the byte after the offer must be framed in
; article mode.  `fn-served-dispatch' switches the wire with
; `fn-wire-begin-article' on that effect, so article mode is wire state inside
; the connection, the terminated body comes back as one `(:article lines)'
; event, and the fold hands it to the injection path.  An injected article is
; not a reply: it leaves the step as a `(:submit decision)' effect the host
; carries through its durable path, and the host answers by calling
; `fn-served-post-outcome' with what it observed.  Every reply octet is still
; produced here.
;
; What is proved here, each lifted from a named keystone rather than reproved:
;
;   fn-served-step-preserves-connp          fn-wire-feed-byte-preserves-statep
;                                           fn-wire-begin-article-preserves-statep
;                                           fn-post-step-preserves-consistent-
;                                             session
;   fn-served-step-effects-are-typed        fn-auth-step-effects-well-formed
;                                           fn-post-submission-is-an-injected-
;                                             article
;   fn-served-step-partition-independence   fn-served-feed-of-append (a byte
;                                           fold splits over append by its
;                                           shape; no wire lemma is needed)
;   fn-served-run-is-the-concatenated-step  the two above, by induction
;   fn-served-reply-stream-is-partition-independent   the corollary the host
;                                           needs: the reply octets depend only
;                                           on the concatenated input, not on
;                                           how the network cut it
;   fn-served-step-nntp-steps-is-bounded    fn-wire-feed-byte-emits-at-most-
;                                             one-event
;
; OPEN (no theorem here): the cost of one `fn-auth-step' is not yet
; bounded by a closed form.  See the obligation recorded at the end of this
; book.

(in-package "ACL2")
(include-book "wire-invariants")
(include-book "nntp-post")
(include-book "nntp-auth")

; -----------------------------------------------------------------------------
; The connection record: wire framing state, POST session, pinned archive,
; posting configuration, clock observation
;
; The archive is the immutable snapshot the connection was opened against.  It
; is a field of the connection, not a global, because a served step must not be
; able to observe a later commit: that is the pinned-prefix discipline of
; specs/node-functionality.md section 1.1 with the version pin still to come.
; The configuration and the observation are likewise pinned at open: the
; served step reads them and never a global.

(defun fn-served-conn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 6)))

(defun fn-served-conn-wire (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-served-conn-session (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-served-conn-archive (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-served-conn-config (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-served-conn-observation (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

; The clock reading supplied with THIS read.  It is not pinned: the owner
; rebuilds the served connection on every read and puts its current
; observation here (books/owner.lisp, fn-own-read), because RFC 5537
; section 3.4 makes Injection-Date the time of injection and a generated
; Message-ID is derived from the same reading.  `observation` above is the
; reading pinned at accept and is the reader environment; the two are
; deliberately distinct fields.
(defun fn-served-conn-injection (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))

(defun fn-served-make-conn (wire session archive config observation injection)
  (declare (xargs :guard t))
  (list wire session archive config observation injection))

(defthm fn-served-conn-shapep-of-fn-served-make-conn
  (fn-served-conn-shapep
   (fn-served-make-conn wire session archive config observation
                        injection)))

(defthm fn-served-conn-wire-of-fn-served-make-conn
  (equal (fn-served-conn-wire
          (fn-served-make-conn wire session archive config observation
                        injection))
         wire))

(defthm fn-served-conn-session-of-fn-served-make-conn
  (equal (fn-served-conn-session
          (fn-served-make-conn wire session archive config observation
                        injection))
         session))

(defthm fn-served-conn-archive-of-fn-served-make-conn
  (equal (fn-served-conn-archive
          (fn-served-make-conn wire session archive config observation
                        injection))
         archive))

(defthm fn-served-conn-config-of-fn-served-make-conn
  (equal (fn-served-conn-config
          (fn-served-make-conn wire session archive config observation
                        injection))
         config))

(defthm fn-served-conn-observation-of-fn-served-make-conn
  (equal (fn-served-conn-observation
          (fn-served-make-conn wire session archive config observation
                               injection))
         observation))

(defthm fn-served-conn-injection-of-fn-served-make-conn
  (equal (fn-served-conn-injection
          (fn-served-make-conn wire session archive config observation
                               injection))
         injection))

(defthm fn-served-conn-shapep-forward-shape
  (implies (fn-served-conn-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-served-conn-shapep) (:d fn-served-conn-wire)
                    (:d fn-served-conn-session) (:d fn-served-conn-archive)
                    (:d fn-served-conn-config) (:d fn-served-conn-observation)
                    (:d fn-served-conn-injection)
                    (:d fn-served-make-conn)))

; The result record: the connection after the read, and the effects the host
; must perform in order.

(defun fn-served-result-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))

(defun fn-served-result-conn (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-served-result-effects (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-served-make-result (conn effects)
  (declare (xargs :guard t))
  (list conn effects))

(defthm fn-served-result-shapep-of-fn-served-make-result
  (fn-served-result-shapep (fn-served-make-result conn effects)))

(defthm fn-served-result-conn-of-fn-served-make-result
  (equal (fn-served-result-conn (fn-served-make-result conn effects)) conn))

(defthm fn-served-result-effects-of-fn-served-make-result
  (equal (fn-served-result-effects (fn-served-make-result conn effects))
         effects))

(defthm fn-served-result-shapep-forward-shape
  (implies (fn-served-result-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-served-result-shapep) (:d fn-served-result-conn)
                    (:d fn-served-result-effects) (:d fn-served-make-result)))

; Constructor injectivity for the two records.  Local: an equality rule of this
; shape is proof vocabulary for the theorems below, not something an includer
; should inherit.

(local
 (defthm fn-served-make-conn-equal
   (equal (equal (fn-served-make-conn w1 s1 a1 c1 o1 j1)
                 (fn-served-make-conn w2 s2 a2 c2 o2 j2))
          (and (equal w1 w2) (equal s1 s2) (equal a1 a2)
               (equal c1 c2) (equal o1 o2) (equal j1 j2)))
   :hints (("Goal" :in-theory (enable fn-served-make-conn)))))

(local
 (defthm fn-served-make-result-equal
   (equal (equal (fn-served-make-result c1 e1) (fn-served-make-result c2 e2))
          (and (equal c1 c2) (equal e1 e2)))
   :hints (("Goal" :in-theory (enable fn-served-make-result)))))

; -----------------------------------------------------------------------------
; The carried invariant
;
; fn-served-connp is a whole-connection recognizer and therefore never runs on
; the served path: fn-served-step tests the wire recognizer once per read (as
; fn-wire-drive did) and branches on nothing else.  It is the hypothesis the
; keystones below carry and the step preserves (proof-style section 4).  It is
; deliberately not guard verified: it is specification vocabulary, and
; fn-auth-session-consistentp, which walks the pinned archive, is not
; executable on a served read by design.

(defun fn-served-connp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-served-conn-shapep c)
       (fn-wire-statep (fn-served-conn-wire c))
       (fn-auth-session-consistentp (fn-served-conn-session c)
                                    (fn-served-conn-archive c))))

(defthm fn-served-connp-forward-shape
  (implies (fn-served-connp c) (and (consp c) (true-listp c)))
  :rule-classes :forward-chaining)

(defthm fn-served-connp-is-wire-state
  (implies (fn-served-connp c)
           (fn-wire-statep (fn-served-conn-wire c))))

(defthm fn-served-connp-is-consistent-session
  (implies (fn-served-connp c)
           (fn-auth-session-consistentp (fn-served-conn-session c)
                                        (fn-served-conn-archive c))))

(in-theory (disable fn-served-connp))

; -----------------------------------------------------------------------------
; The typed effects of a served read
;
; fn-nntp-effectsp (books/nntp-effects.lisp) enumerates what the dispatcher
; may emit: a reply, the close effect, the begin-article marker.  A served
; read emits one thing more, the submission of an injected article, which is
; the host's obligation and not a reply.  fn-served-effectsp is that closed
; enumeration.  Both recognizers are specification vocabulary and never run on
; the served path, so neither is guard verified.

(defun fn-served-submit-effect (decision)
  (declare (xargs :guard t))
  (list :submit decision))

(defun fn-served-submit-effectp (effect)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp effect)
       (equal (len effect) 2)
       (equal (car effect) :submit)
       (or (fn-inj-injectedp (car (cdr effect)))
           (fn-peer-submissionp (car (cdr effect))))))

(defun fn-served-effectp (effect)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-nntp-effectp effect)
      (fn-served-submit-effectp effect)
      ; RFC 4642 section 2.2.2's handshake instruction.  It is neither a
      ; reply nor a submission: like :submit it is an obligation the host
      ; owes, and like :submit the host may not invent one
      ; (fn-auth-starttls-effect-only-with-382, books/nntp-auth.lisp).
      (equal effect (fn-auth-starttls-effect))))

(defun fn-served-effectsp (effects)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp effects)
      (and (fn-served-effectp (car effects))
           (fn-served-effectsp (cdr effects)))
    (null effects)))

(defthm fn-served-effectsp-of-append
  (implies (and (fn-served-effectsp left) (fn-served-effectsp right))
           (fn-served-effectsp (append left right)))
  :hints (("Goal" :induct (fn-served-effectsp left)
           :in-theory (disable fn-served-effectp))))

(defthm fn-served-nntp-effects-are-served-effects
  (implies (fn-nntp-effectsp effects)
           (fn-served-effectsp effects))
  :hints (("Goal" :induct (fn-served-effectsp effects)
           :in-theory (e/d (fn-nntp-effectsp fn-served-effectp)
                           (fn-nntp-effectp fn-served-submit-effectp)))))

(defthm fn-served-auth-effects-are-served-effects
  (implies (fn-auth-effectsp effects)
           (fn-served-effectsp effects))
  :hints (("Goal" :induct (fn-served-effectsp effects)
           :in-theory (e/d (fn-auth-effectsp fn-served-effectp fn-auth-effectp)
                           (fn-nntp-effectp fn-served-submit-effectp
                            fn-auth-starttls-effect)))))

(local
 (defthm fn-served-close-effect-is-typed
   (fn-served-effectsp (list (fn-nntp-close-effect)))
   :hints (("Goal" :in-theory (enable fn-nntp-effectp fn-nntp-close-effect)))))

; -----------------------------------------------------------------------------
; One framed event
;
; fn-auth-step (books/nntp-auth.lisp) is the dispatcher with AUTHINFO,
; STARTTLS and POST
; composed in: it answers the offer, reassembles the article body and decides
; injection.  This step does two things with its result.  The 340 offer
; carries the begin-article marker, and here the wire is switched with
; fn-wire-begin-article, so the next byte is framed in article mode; and a
; submission leaves as a :submit effect rather than a reply.

(defun fn-served-dispatch (conn event)
  (declare (xargs :guard t))
  (let* ((r (fn-auth-step (fn-served-conn-session conn)
                               (fn-served-conn-archive conn)
                               (fn-served-conn-config conn)
                               (fn-served-conn-observation conn)
                               (fn-served-conn-injection conn)
                               event))
         (effects (fn-post-result-effects r))
         (submission (fn-post-result-submission r))
         (wire (fn-served-conn-wire conn))
         (wire2 (if (fn-post-offeredp effects)
                    (fn-wire-result-state (fn-wire-begin-article wire))
                  wire)))
    (fn-served-make-result
     (fn-served-make-conn wire2 (fn-post-result-session r)
                          (fn-served-conn-archive conn)
                          (fn-served-conn-config conn)
                          (fn-served-conn-observation conn)
                          (fn-served-conn-injection conn))
     (mbe :logic (append effects
                         (if submission
                             (list (fn-served-submit-effect submission))
                           nil))
          :exec (fn-ag-append effects
                              (if submission
                                  (list (fn-served-submit-effect submission))
                                nil))))))

; Local projections of one dispatch, in accessor vocabulary, so that nothing
; below opens fn-served-dispatch.

(local
 (defthm fn-served-dispatch-conn-projections
   (and (fn-served-conn-shapep
         (fn-served-result-conn (fn-served-dispatch conn event)))
        (equal (fn-served-conn-session
                (fn-served-result-conn (fn-served-dispatch conn event)))
               (fn-post-result-session
                (fn-auth-step (fn-served-conn-session conn)
                                   (fn-served-conn-archive conn)
                                   (fn-served-conn-config conn)
                                   (fn-served-conn-observation conn)
                                   (fn-served-conn-injection conn)
                                   event)))
        (equal (fn-served-conn-archive
                (fn-served-result-conn (fn-served-dispatch conn event)))
               (fn-served-conn-archive conn))
        (equal (fn-served-conn-config
                (fn-served-result-conn (fn-served-dispatch conn event)))
               (fn-served-conn-config conn))
        (equal (fn-served-conn-observation
                (fn-served-result-conn (fn-served-dispatch conn event)))
               (fn-served-conn-observation conn))
        (equal (fn-served-conn-injection
                (fn-served-result-conn (fn-served-dispatch conn event)))
               (fn-served-conn-injection conn)))
   :hints (("Goal" :in-theory (disable fn-auth-step fn-post-offeredp
                                       fn-wire-begin-article)))))

(local
 (defthm fn-served-dispatch-effects-unfold
   (equal (fn-served-result-effects (fn-served-dispatch conn event))
          (let ((r (fn-auth-step (fn-served-conn-session conn)
                                      (fn-served-conn-archive conn)
                                      (fn-served-conn-config conn)
                                      (fn-served-conn-observation conn)
                                      (fn-served-conn-injection conn)
                                      event)))
            (append (fn-post-result-effects r)
                    (if (fn-post-result-submission r)
                        (list (fn-served-submit-effect
                               (fn-post-result-submission r)))
                      nil))))
   :hints (("Goal" :in-theory (disable fn-auth-step fn-post-offeredp
                                       fn-wire-begin-article)))))

(defthm fn-served-dispatch-preserves-wire-statep
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-served-dispatch conn event)))))
  :hints (("Goal"
           :in-theory (disable fn-wire-statep fn-wire-begin-article
                               fn-auth-step fn-post-offeredp
                               fn-wire-begin-article-preserves-statep)
           :use ((:instance fn-wire-begin-article-preserves-statep
                            (wire-state (fn-served-conn-wire conn)))))))

(defthm fn-served-dispatch-preserves-connp
  (implies (fn-served-connp conn)
           (fn-served-connp
            (fn-served-result-conn (fn-served-dispatch conn event))))
  :hints (("Goal"
           :in-theory (e/d (fn-served-connp)
                           (fn-served-dispatch fn-wire-statep
                            fn-auth-step fn-auth-session-consistentp
                            fn-auth-step-preserves-consistent-session
                            fn-served-dispatch-preserves-wire-statep))
           :use ((:instance fn-served-dispatch-preserves-wire-statep)
                 (:instance fn-auth-step-preserves-consistent-session
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))))))

(defthm fn-served-dispatch-effects-are-typed
  (implies (fn-served-connp conn)
           (fn-served-effectsp
            (fn-served-result-effects (fn-served-dispatch conn event))))
  :hints (("Goal"
           :in-theory (e/d ()
                           (fn-served-dispatch fn-auth-step
                            fn-auth-sessionp fn-served-connp
                            fn-nntp-effectp fn-inj-injectedp fn-peer-submissionp
                            ; else the :use hypothesis is rewritten to T
                            ; by this very rule and the forward-chaining
                            ; bridge never sees the consistency it was
                            ; added for
                            fn-served-connp-is-consistent-session
                            fn-auth-step-effects-well-formed))
           ; a connection's session IS an auth session: that dismisses
           ; fn-auth-step's non-session branch, which emits nothing
           :use ((:instance fn-served-connp-is-consistent-session (c conn))
                 (:instance fn-auth-consistent-forward
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn)))
                 (:instance fn-auth-step-effects-well-formed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-auth-step-submission-is-typed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))))))

; The three theorems above are the only readers of the two local projections;
; below them fn-served-dispatch is closed and only its keystones are used.
(local (in-theory (disable fn-served-dispatch-conn-projections
                           fn-served-dispatch-effects-unfold)))

; The events one byte framed, in order (fn-wire-feed-byte emits at most one;
; the fold is written over the list so that it is total without that fact).

(defun fn-served-dispatch-events (conn events)
  (declare (xargs :guard t))
  (if (consp events)
      (let* ((here (fn-served-dispatch conn (car events)))
             (tail (fn-served-dispatch-events (fn-served-result-conn here)
                                              (cdr events))))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    (fn-served-make-result conn nil)))

(defthm fn-served-dispatch-events-preserves-wire-statep
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-served-dispatch-events conn events)))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch fn-wire-statep))))

(defthm fn-served-dispatch-events-preserves-connp
  (implies (fn-served-connp conn)
           (fn-served-connp
            (fn-served-result-conn (fn-served-dispatch-events conn events))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch fn-served-connp))))

(defthm fn-served-dispatch-events-effects-are-typed
  (implies (fn-served-connp conn)
           (fn-served-effectsp
            (fn-served-result-effects (fn-served-dispatch-events conn events))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch fn-served-connp
                               fn-served-effectp (:d fn-served-effectsp)))))

; -----------------------------------------------------------------------------
; One socket read
;
; The fold over the read's octets.  Each byte goes to fn-wire-feed-byte, the
; events it framed go to the dispatcher before the next byte, and the reply
; and submission effects accumulate in order.  Once the wire is closed the
; rest of the read is not walked, which is what makes the append law below
; hold without a hypothesis and what the host does (it stops reading after a
; close).  The guard carries fn-wire-statep: fn-served-step tests it once at
; entry and the preservation lemmas above discharge it through the recursion.

(defun fn-served-closed-wirep (wire)
  (declare (xargs :guard t))
  (equal (fn-wire-state-mode wire) :closed))

; The second stopping condition, and the reason it is a property of the
; CONNECTION rather than of the effects just emitted.  RFC 4642 section 2.2
; puts the TLS handshake's first octet immediately after the 382's CRLF and
; forbids pipelining STARTTLS, so once books/nntp-auth.lisp has answered 382
; the rest of this read is handshake and not NNTP.  Written as a test on the
; effects it would break the append law: a read cut before the STARTTLS line
; and one cut after it would frame different octets.  Carried in the session
; (fn-auth-session-handshakingp) it behaves exactly as a closed wire does --
; feeding a handshaking connection is a no-op whatever the octets -- so
; fn-served-feed-of-append and every law above it hold unchanged.  This is
; the "Open, and a real one" paragraph of specs/nntp.md, closed.
(defun fn-served-tls-handshakingp (conn)
  (declare (xargs :guard t))
  (and (fn-auth-session-handshakingp (fn-served-conn-session conn)) t))

(defun fn-served-feed (conn octets)
  (declare (xargs :guard (fn-wire-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-make-result conn nil)
    (let* ((fed (fn-wire-feed-byte (fn-served-conn-wire conn) (car octets)))
           (here (fn-served-dispatch-events
                  (fn-served-make-conn (fn-wire-result-state fed)
                                       (fn-served-conn-session conn)
                                       (fn-served-conn-archive conn)
                                       (fn-served-conn-config conn)
                                       (fn-served-conn-observation conn)
                                       (fn-served-conn-injection conn))
                  (fn-wire-result-events fed)))
           (tail (fn-served-feed (fn-served-result-conn here) (cdr octets))))
      (fn-served-make-result
       (fn-served-result-conn tail)
       (mbe :logic (append (fn-served-result-effects here)
                           (fn-served-result-effects tail))
            :exec (fn-ag-append (fn-served-result-effects here)
                                (fn-served-result-effects tail)))))))

(defthm fn-served-feed-preserves-wire-statep
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-served-feed conn octets)))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep))))

(verify-guards fn-served-feed
  :hints (("Goal" :in-theory (disable fn-served-dispatch-events
                                      fn-wire-feed-byte fn-wire-statep))))

(local
 (defthm fn-served-fed-conn-is-a-connection
   (implies (fn-served-connp conn)
            (fn-served-connp
             (fn-served-make-conn
              (fn-wire-result-state
               (fn-wire-feed-byte (fn-served-conn-wire conn) byte))
              (fn-served-conn-session conn)
              (fn-served-conn-archive conn)
              (fn-served-conn-config conn)
              (fn-served-conn-observation conn)
              (fn-served-conn-injection conn))))
   :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                   (fn-wire-feed-byte fn-wire-statep
                                    fn-auth-session-consistentp))))))

(defthm fn-served-feed-preserves-connp
  (implies (fn-served-connp conn)
           (fn-served-connp
            (fn-served-result-conn (fn-served-feed conn octets))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep fn-served-connp))))

(defthm fn-served-feed-effects-are-typed
  (implies (fn-served-connp conn)
           (fn-served-effectsp
            (fn-served-result-effects (fn-served-feed conn octets))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep fn-served-connp
                               fn-served-effectp (:d fn-served-effectsp)))))

; One read.  The close effect is appended on the transition edge only: a read
; that finds the wire already closed is a no-op, which is what makes the
; partition law below unconditional in the close effect.

(defun fn-served-step (conn octets)
  (declare (xargs :guard t))
  (let ((wire (fn-served-conn-wire conn)))
    (if (not (fn-wire-statep wire))
        (fn-served-make-result conn nil)
      (let* ((fed (fn-served-feed conn octets))
             (wire2 (fn-served-conn-wire (fn-served-result-conn fed))))
        (fn-served-make-result
         (fn-served-result-conn fed)
         (mbe :logic (append (fn-served-result-effects fed)
                             (if (and (not (fn-served-closed-wirep wire))
                                      (fn-served-closed-wirep wire2))
                                 (list (fn-nntp-close-effect))
                               nil))
              :exec (fn-ag-append (fn-served-result-effects fed)
                                  (if (and (not (fn-served-closed-wirep wire))
                                           (fn-served-closed-wirep wire2))
                                      (list (fn-nntp-close-effect))
                                    nil))))))))

; A list of reads, in arrival order.

(defun fn-served-chunk-listp (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (fn-wire-octet-listp (car chunks))
           (fn-served-chunk-listp (cdr chunks)))
    (null chunks)))

(defun fn-served-concat (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (mbe :logic (append (car chunks) (fn-served-concat (cdr chunks)))
           :exec (fn-ag-append (car chunks) (fn-served-concat (cdr chunks))))
    nil))

(defun fn-served-run (conn chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (let* ((here (fn-served-step conn (car chunks)))
             (tail (fn-served-run (fn-served-result-conn here) (cdr chunks))))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    ;; An empty run is an empty read: the same base case the concatenation
    ;; theorem below reduces to, with no record eta law needed to see it.
    (fn-served-step conn nil)))

; The three projections the host is allowed to take of an effect list.  The
; first two were fn-reader-effect-octets and fn-reader-close-effectsp in
; :program-mode host Lisp; concatenating a reply stream is a decision, and
; ACL2 owns it.  The third is the submission the host owes a durable attempt.

(defun fn-served-reply-octets (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (mbe :logic (append (if (and (consp (car effects))
                                   (equal (car (car effects)) :reply)
                                   (consp (cdr (car effects))))
                              (car (cdr (car effects)))
                            nil)
                          (fn-served-reply-octets (cdr effects)))
           :exec (fn-ag-append (if (and (consp (car effects))
                                        (equal (car (car effects)) :reply)
                                        (consp (cdr (car effects))))
                                   (car (cdr (car effects)))
                                 nil)
                               (fn-served-reply-octets (cdr effects))))
    nil))

(defun fn-served-closingp (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (or (equal (car effects) (fn-nntp-close-effect))
          (fn-served-closingp (cdr effects)))
    nil))

; RFC 4642 section 2.2.2: the host owes a TLS handshake once this effect is
; in the read's effect list.  It is the third projection the host takes of a
; served read, beside the reply octets and the close, and it is a QUESTION
; about the effects ACL2 emitted, never a decision the host makes: the book
; has already refused a second STARTTLS, refused one with no certificate and
; put the connection into the handshake
; (fn-auth-starttls-effect-only-with-382, books/nntp-auth.lisp).
(defun fn-served-starttlsp (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (or (equal (car effects) (fn-auth-starttls-effect))
          (fn-served-starttlsp (cdr effects)))
    nil))

; The FIRST submission in the list, and a `(:submit nil)' is not one.  The
; last conjunct matters: fn-served-dispatch appends the effect only when the
; dispatcher produced a submission, so no read ever carries `(:submit nil)',
; but without the conjunct fn-served-submission-of-append below is FALSE on
; a list that does -- it would return nil for the left half and then the
; right half's submission for the append.  The host reads this projection to
; decide what it owes a durable attempt, so the two must agree on every
; list, not only on the reachable ones.
(defun fn-served-submission (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (and (consp (car effects))
               (equal (car (car effects)) :submit)
               (consp (cdr (car effects)))
               (car (cdr (car effects))))
          (car (cdr (car effects)))
        (fn-served-submission (cdr effects)))
    nil))

; DEFECT REPAIRED 2026-09-20 (w6/peering-inbound-2): without the
; fn-served-effectsp hypothesis this is FALSE.  Counterexample:
; left = ((:submit nil)), right = ((:submit 5)).  fn-served-submission
; stops at the first :submit and returns its payload, so the left scan
; yields nil and the appended scan also yields nil, while the right-hand
; side yields 5.  fn-served-submit-effectp requires the payload to be an
; fn-inj-injectedp or an fn-peer-submissionp, and neither holds of nil, so
; on a typed effect list -- the only kind the served path produces -- a
; :submit effect always carries a non-nil submission and the equality
; holds.  The hypothesis is discharged at the one use site below from
; fn-served-step-effects-are-typed.
(defthm fn-served-submission-of-append
  (implies (fn-served-effectsp left)
           (equal (fn-served-submission (append left right))
                  (if (fn-served-submission left)
                      (fn-served-submission left)
                    (fn-served-submission right))))
  :hints (("Goal" :in-theory (e/d (fn-served-effectsp fn-served-effectp
                                   fn-served-submit-effectp)
                                  ((:d fn-inj-injectedp)
                                   (:d fn-peer-submissionp))))))

; The host's durable observation, fed back as one more served input.  The
; connection is unchanged; the reply is fn-nntp-post-outcome's, which is the
; only place 240 exists (fn-post-outcome-240-only-for-a-durable-observation).

(defun fn-served-post-outcome (conn completion)
  (declare (xargs :guard t))
  (fn-served-make-result
   conn
   (fn-post-result-effects
    (fn-nntp-post-outcome (fn-peer-session-base (fn-served-conn-session conn))
                         completion))))

; A definitional restatement linking the host's entry to the nntp-post
; theorems: :rule-classes nil, never a registry event.
(defthm fn-served-post-outcome-effects-by-definition
  (equal (fn-served-result-effects (fn-served-post-outcome conn completion))
         (fn-post-result-effects
          (fn-nntp-post-outcome (fn-peer-session-base (fn-served-conn-session conn))
                         completion)))
  :rule-classes nil)

(defthm fn-served-post-outcome-effects-are-typed
  (fn-served-effectsp
   (fn-served-result-effects (fn-served-post-outcome conn completion)))
  :hints (("Goal" :in-theory (disable fn-nntp-post-outcome fn-served-effectp
                                      (:d fn-served-effectsp)))))

; The owner's transit port, after fn-peer-transfer and the durable attempt:
; the submission the :submit effect carried, the decision fn-peer-transfer
; returned, and the completion the store reported (:durable, :refused,
; :uncertain, or nil when no attempt ran).  The reply is the RFC table of
; specs/peering.md section 2.2; an uncertain outcome is 400 (TAKETHIS) or
; 436 (IHAVE) and the close effect.  The connection is unchanged.
(defun fn-served-transit-outcome (conn submission decision completion)
  (declare (xargs :guard t))
  (fn-served-make-result
   conn
   (fn-post-result-effects
    (fn-peer-transit-outcome (fn-served-conn-session conn) submission decision
                             completion))))

(defthm fn-served-transit-outcome-effects-are-typed
  (implies (fn-peer-submissionp submission)
           (fn-served-effectsp
            (fn-served-result-effects
             (fn-served-transit-outcome conn submission decision completion))))
  :hints (("Goal" :in-theory (e/d (fn-peer-transit-outcome)
                                  (fn-peer-transit-outcome-effects
                                   fn-served-effectp fn-peer-submissionp
                                   (:d fn-served-effectsp))))))

; Opening a connection: the one place the whole-archive projection recognizer
; runs (fn-nntp-open-session records its verdict in the session and no command
; recomputes it).  The greeting is RFC 3977 section 5.1.1's code for what
; this connection may do: 200 when its pinned configuration allows posting
; and 201 when it does not.  The same bit decides the POST capability label
; (section 5.2.2, fn-nntp-capability-lines) and MODE READER (section 5.3.2),
; and it is the bit fn-nntp-post-step reads before answering a POST command,
; so the three can never disagree.

(defconst *fn-served-greeting*
  '(50 48 49 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109
    101 110 116 97 108 32 114 101 97 100 101 114 32 114 101 97 100 121 13 10))

(defconst *fn-served-greeting-posting*
  '(50 48 48 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109
    101 110 116 97 108 32 115 101 114 118 101 114 32 114 101 97 100 121 13
    10))

(defun fn-served-greeting (config)
  (declare (xargs :guard t))
  (if (fn-inj-config-allow config)
      *fn-served-greeting-posting*
    *fn-served-greeting*))

; `acfg' is the connection's AUTHINFO/STARTTLS policy
; (books/nntp-auth.lisp fn-auth-configp): what the operator configured, read
; once here and pinned, never per command.  Anything that is not a
; configuration opens the profile that requires nothing and offers nothing
; (fn-auth-open-config), which is what every served theorem and transcript
; written before this book carried authentication means.  `tlsp' is nil: a
; connection that is already inside TLS is the implicit-TLS listener and the
; host says so with the (:tls-established) event, never this entry.
(defun fn-served-open (archive line-limit body-limit config observation
                               injection acfg)
  (declare (xargs :guard t))
  (fn-served-make-result
   (fn-served-make-conn (fn-wire-initial-state line-limit body-limit)
                        (fn-auth-open-session archive nil nil nil acfg nil)
                        archive config observation injection)
   (list (fn-nntp-reply-effect (fn-served-greeting config)))))

; A peer connection (specs/peering.md section 1.1): the host resolved the
; source to a peer name at :open and hands the node and configuration the
; offer decision reads; both are checked once here under their recognizers
; (fn-auth-open-session) and never per command.
(defun fn-served-open-peer (archive line-limit body-limit config observation
                                    injection peer node cfg)
  (declare (xargs :guard t))
  (fn-served-make-result
   (fn-served-make-conn (fn-wire-initial-state line-limit body-limit)
                        (fn-auth-open-session archive peer node cfg
                                              (fn-auth-open-config) nil)
                        archive config observation injection)
   (list (fn-nntp-reply-effect (fn-served-greeting config)))))

(defthm fn-served-open-is-a-connection
  (implies (and (posp line-limit) (posp body-limit))
           (fn-served-connp
            (fn-served-result-conn
             (fn-served-open archive line-limit body-limit config observation
                             injection acfg))))
  :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                  (fn-wire-statep fn-wire-initial-state
                                   fn-auth-open-session
                                   fn-auth-session-consistentp))
           :use ((:instance fn-wire-initial-state-is-state)
                 (:instance fn-auth-open-session-is-consistent
                            (peer nil) (node nil) (cfg nil) (tlsp nil))))))

(defthm fn-served-open-peer-is-a-connection
  (implies (and (posp line-limit) (posp body-limit))
           (fn-served-connp
            (fn-served-result-conn
             (fn-served-open-peer archive line-limit body-limit config
                                  observation injection peer node cfg))))
  :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                  (fn-wire-statep fn-wire-initial-state
                                   fn-auth-open-session
                                   fn-auth-session-consistentp))
           :use ((:instance fn-wire-initial-state-is-state)
                 (:instance fn-auth-open-session-is-consistent
                            (acfg (fn-auth-open-config)) (tlsp nil))))))

(defthm fn-served-concat-is-an-octet-list
  (implies (fn-served-chunk-listp chunks)
           (fn-wire-octet-listp (fn-served-concat chunks)))
  :hints (("Goal" :induct (fn-served-chunk-listp chunks))))

; -----------------------------------------------------------------------------
; Keystone 1: the carried invariant is preserved by one read

(defthm fn-served-step-preserves-connp
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp octets))
           (fn-served-connp (fn-served-result-conn (fn-served-step conn octets))))
  :hints (("Goal" :in-theory (disable fn-served-feed fn-wire-statep
                                      fn-served-connp))))

(defthm fn-served-run-preserves-connp
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (fn-served-connp (fn-served-result-conn (fn-served-run conn chunks))))
  :hints (("Goal" :induct (fn-served-run conn chunks)
           :in-theory (disable fn-served-step fn-served-connp))))

; -----------------------------------------------------------------------------
; Keystone 2: the refusal enumeration
;
; fn-served-effectsp is the closed enumeration: every effect of a served read
; is a reply with fn-nntp-replyp octets, the begin-article marker, the close
; effect, or the submission of an injected article.  A read produces nothing
; else -- no exception, no untyped value, no fifth outcome.

(defthm fn-served-step-effects-are-typed
  (implies (fn-served-connp conn)
           (fn-served-effectsp (fn-served-result-effects (fn-served-step conn octets))))
  :hints (("Goal" :in-theory (disable fn-served-feed fn-wire-statep
                                      fn-served-connp fn-served-effectp
                                      (:d fn-served-effectsp)))))

(defthm fn-served-run-effects-are-typed
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (fn-served-effectsp (fn-served-result-effects (fn-served-run conn chunks))))
  :hints (("Goal" :induct (fn-served-run conn chunks)
           :in-theory (disable fn-served-step fn-served-connp
                               fn-served-effectp (:d fn-served-effectsp)))))

; The enumeration read off fn-served-effectp itself.  A definitional
; restatement: :rule-classes nil, never a registry event.
(defthm fn-served-typed-effect-enumeration-by-definition
  (implies (fn-served-effectp effect)
           (or (and (equal (car effect) :reply)
                    (fn-octet-listp (car (cdr effect)))
                    (fn-nntp-replyp (car (cdr effect))))
               (equal effect (fn-nntp-begin-article-effect))
               (equal effect (fn-nntp-close-effect))
               (and (equal (car effect) :submit)
                    (or (fn-inj-injectedp (car (cdr effect)))
                        (fn-peer-submissionp (car (cdr effect)))))
               (equal effect (fn-auth-starttls-effect))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nntp-effectp)
                                  (fn-nntp-replyp fn-inj-injectedp
                                   fn-peer-submissionp fn-octet-listp)))))

; -----------------------------------------------------------------------------
; Keystone 3: partition independence
;
; A fold over bytes splits over an append of its input by its shape alone:
; feeding left then right is feeding their concatenation, whatever the bytes
; and whatever the dispatcher did between them.  Nothing about the wire is
; needed, because the wire never sees more than one byte at a time.  The close
; effect sits on the transition edge, so a read of a closed wire contributes
; nothing and the law lifts to fn-served-step.

(local
 (defthm fn-served-append-is-associative
   (equal (append (append a b) c) (append a (append b c)))))

; A fed result is its own reconstruction: both branches of fn-served-feed
; return a constructed result.  Local: the append law below needs it in its
; base case, and no includer needs an eta law.
(local
 (defthm fn-served-feed-reconstructs
   (equal (fn-served-make-result
           (fn-served-result-conn (fn-served-feed conn octets))
           (fn-served-result-effects (fn-served-feed conn octets)))
          (fn-served-feed conn octets))
   :hints (("Goal" :expand ((fn-served-feed conn octets))
            :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                                fn-wire-statep)))))

(defthm fn-served-feed-of-append
  (equal (fn-served-feed conn (append left right))
         (fn-served-make-result
          (fn-served-result-conn
           (fn-served-feed (fn-served-result-conn (fn-served-feed conn left))
                           right))
          (append
           (fn-served-result-effects (fn-served-feed conn left))
           (fn-served-result-effects
            (fn-served-feed (fn-served-result-conn (fn-served-feed conn left))
                            right)))))
  :hints (("Goal" :induct (fn-served-feed conn left)
           :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep))))

(local
 (defthm fn-served-feed-of-closed-wire
   (implies (fn-served-closed-wirep (fn-served-conn-wire conn))
            (equal (fn-served-feed conn octets)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-served-feed conn octets))))))

; The handshake's counterpart of the law above, and the proof that the
; second stopping condition costs the append law nothing.
(defthm fn-served-feed-of-handshaking-connection
  (implies (fn-served-tls-handshakingp conn)
           (equal (fn-served-feed conn octets)
                  (fn-served-make-result conn nil)))
  :hints (("Goal" :expand ((fn-served-feed conn octets)))))

; The whole of the RFC 4642 section 2.2 claim at the served layer: once the
; 382 is out, nothing else in this read is answered and nothing else in it
; is submitted.  The subject is fn-served-step, which is what
; books/owner.lisp fn-own-read calls once per socket read and what
; tools/run_owner.py Owner.serve calls once per recv.
(defthm fn-served-step-of-handshaking-connection-is-a-no-op
  (implies (fn-served-tls-handshakingp conn)
           (and (equal (fn-served-result-effects
                        (fn-served-step conn octets))
                       nil)
                (equal (fn-served-result-conn (fn-served-step conn octets))
                       conn)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-served-feed fn-wire-statep
                               fn-served-tls-handshakingp
                               fn-served-feed-of-handshaking-connection)
           :use ((:instance fn-served-feed-of-handshaking-connection)))))

(defthm fn-served-step-partition-independence
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (equal (fn-served-step conn (append left right))
                  (fn-served-make-result
                   (fn-served-result-conn
                    (fn-served-step
                     (fn-served-result-conn (fn-served-step conn left)) right))
                   (append
                    (fn-served-result-effects (fn-served-step conn left))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-result-conn (fn-served-step conn left))
                      right))))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((fn-served-closed-wirep
                    (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-feed conn left)))))
           :in-theory (disable fn-served-feed fn-wire-statep fn-served-connp
                               fn-served-feed-preserves-wire-statep
                               fn-served-feed-preserves-connp)
           :use ((:instance fn-served-feed-preserves-wire-statep
                            (octets left))
                 (:instance fn-served-connp-is-wire-state (c conn))))))

; The law the host needs: however the network cut the stream, the connection
; and the effect sequence after the whole run are those of one read of the
; concatenation.  Chunk boundaries are invisible.

(defthm fn-served-run-is-the-concatenated-step
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (equal (fn-served-run conn chunks)
                  (fn-served-step conn (fn-served-concat chunks))))
  :hints (("Goal" :induct (fn-served-run conn chunks)
           :in-theory (disable fn-served-step fn-served-connp
                               fn-served-feed fn-wire-statep)
           :expand ((fn-served-concat chunks)))))

(defthm fn-served-reply-stream-is-partition-independent
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp one)
                (fn-served-chunk-listp two)
                (equal (fn-served-concat one) (fn-served-concat two)))
           (equal (fn-served-reply-octets
                   (fn-served-result-effects (fn-served-run conn one)))
                  (fn-served-reply-octets
                   (fn-served-result-effects (fn-served-run conn two)))))
  :hints (("Goal"
           :in-theory (disable fn-served-run fn-served-step fn-served-connp
                               fn-served-concat fn-served-reply-octets
                               fn-served-run-is-the-concatenated-step)
           :use ((:instance fn-served-run-is-the-concatenated-step (chunks one))
                 (:instance fn-served-run-is-the-concatenated-step (chunks two))))))

; -----------------------------------------------------------------------------
; Keystone 3b: pipelining across the POST body (RFC 3977 section 3.5)
;
; Section 3.5 lets a client send a command before the previous reply arrives,
; and requires the server neither to discard data nor to lose synchronisation.
; Partition independence above settles the byte-boundary half of that: the
; network may cut the stream anywhere.  It does NOT settle the framing half,
; which is what POST introduces.  Between the 340 and the terminator the wire
; is in article mode; an octet arriving in the same read AFTER the terminator
; must be framed as a command and not swallowed into the body.
;
; The load-bearing fact is about the framer: a byte that completes an article
; leaves the wire in command mode, in the same call, so the fold's next byte
; is framed as a command with nothing in between.  Everything else is the
; append law.
;
; The subject is fn-served-step, which is what host/owner-host.lisp
; `fn-own-read' calls once per socket read (books/owner.lisp fn-own-read,
; fn-own-read-is-served-step-on-pinned-prefix); tools/run_owner.py
; `Owner.serve' performs exactly one such call per recv.

(defthm fn-wire-article-event-resumes-command-mode
  (implies (and (fn-wire-statep wire-state)
                (consp (fn-wire-result-events (fn-wire-feed-byte wire-state byte)))
                (equal (car (car (fn-wire-result-events
                                  (fn-wire-feed-byte wire-state byte))))
                       :article))
           (equal (fn-wire-state-mode
                   (fn-wire-result-state (fn-wire-feed-byte wire-state byte)))
                  :command))
  ; The recognizer stays closed (opening it puts eight field conjuncts in
  ; every branch of fn-wire-feed-byte); only the step and the two
  ; constructors open.  fn-wire-article-event is the dev name of what this
  ; hint used to call fn-wire-event-article.
  :hints (("Goal" :in-theory (e/d (fn-wire-step-vocabulary)
                                  ((:d fn-wire-state-mode)
                                   (:d fn-wire-octet-listp)
                                   (:d fn-wire-octet-linesp)
                                   ; the result accessors stay closed: their
                                   ; record lemmas say an eventless result
                                   ; has no events, which is what dismisses
                                   ; every branch that emits none
                                   (:d fn-wire-result-state)
                                   (:d fn-wire-result-events))))))

; The reply stream of a read is the concatenation of the reply streams of its
; effect list's halves.  A list-shape lemma, exported because the pipelining
; statement below is read in terms of it.
(defthm fn-served-reply-octets-of-append
  (equal (fn-served-reply-octets (append left right))
         (append (fn-served-reply-octets left)
                 (fn-served-reply-octets right))))

; The pipelining statement the host needs.  A read carrying a POST block (the
; command line, the body and its terminator) immediately followed by another
; command produces exactly the reply octets of the two delivered separately,
; and reaches the same connection.  A corollary of
; fn-served-step-partition-independence and the two lemmas above, named as
; one: no octet of `later' is lost to the article body and none is
; reattributed to the POST.
(defthm fn-served-pipelined-read-is-the-sequential-reply
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp post-block)
                (fn-wire-octet-listp later))
           (and (equal (fn-served-result-conn
                        (fn-served-step conn (append post-block later)))
                       (fn-served-result-conn
                        (fn-served-step
                         (fn-served-result-conn (fn-served-step conn post-block))
                         later)))
                (equal (fn-served-reply-octets
                        (fn-served-result-effects
                         (fn-served-step conn (append post-block later))))
                       (append
                        (fn-served-reply-octets
                         (fn-served-result-effects
                          (fn-served-step conn post-block)))
                        (fn-served-reply-octets
                         (fn-served-result-effects
                          (fn-served-step
                           (fn-served-result-conn
                            (fn-served-step conn post-block))
                           later)))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-served-step fn-served-connp
                               fn-served-reply-octets
                               fn-served-step-partition-independence)
           :use ((:instance fn-served-step-partition-independence
                            (left post-block) (right later))))))

; The submission a pipelined read carries is the one the POST block earned:
; the later command cannot add or remove a submission, because a submission
; leaves only from the (:article lines) event the terminator framed.
(defthm fn-served-pipelined-read-submission-is-the-post-block-submission
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp post-block)
                (fn-wire-octet-listp later)
                (not (fn-served-submission
                      (fn-served-result-effects
                       (fn-served-step
                        (fn-served-result-conn (fn-served-step conn post-block))
                        later)))))
           (equal (fn-served-submission
                   (fn-served-result-effects
                    (fn-served-step conn (append post-block later))))
                  (fn-served-submission
                   (fn-served-result-effects
                    (fn-served-step conn post-block)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-served-step fn-served-connp
                               fn-served-submission
                               fn-served-step-partition-independence)
           :use ((:instance fn-served-step-partition-independence
                            (left post-block) (right later))
                 (:instance fn-served-step-effects-are-typed
                            (octets post-block))
                 (:instance fn-served-submission-of-append
                            (left (fn-served-result-effects
                                   (fn-served-step conn post-block)))
                            (right (fn-served-result-effects
                                    (fn-served-step
                                     (fn-served-result-conn
                                      (fn-served-step conn post-block))
                                     later))))))))

; -----------------------------------------------------------------------------
; Keystone 4: work per read
;
; The number of dispatcher steps one read performs is at most the length of the
; read: each byte frames at most one event (fn-wire-feed-byte-emits-at-most-
; one-event, books/wire-invariants.lisp:78) and the fold dispatches each event
; once.

(local
 (defthm fn-served-feed-byte-events-at-most-one-linear
   (<= (len (fn-wire-result-events (fn-wire-feed-byte wire-state byte))) 1)
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance fn-wire-feed-byte-emits-at-most-one-event))
            :expand ((len (fn-wire-result-events
                           (fn-wire-feed-byte wire-state byte))))
            :in-theory (disable fn-wire-feed-byte
                                fn-wire-feed-byte-emits-at-most-one-event)))))

(defun fn-served-feed-steps (conn octets)
  (declare (xargs :guard (fn-wire-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn)))
      0
    (let* ((fed (fn-wire-feed-byte (fn-served-conn-wire conn) (car octets)))
           (here (fn-served-dispatch-events
                  (fn-served-make-conn (fn-wire-result-state fed)
                                       (fn-served-conn-session conn)
                                       (fn-served-conn-archive conn)
                                       (fn-served-conn-config conn)
                                       (fn-served-conn-observation conn)
                                       (fn-served-conn-injection conn))
                  (fn-wire-result-events fed))))
      (+ (len (fn-wire-result-events fed))
         (fn-served-feed-steps (fn-served-result-conn here) (cdr octets))))))

(verify-guards fn-served-feed-steps
  :hints (("Goal" :in-theory (disable fn-served-dispatch-events
                                      fn-wire-feed-byte fn-wire-statep))))

(defthm fn-served-feed-steps-bounded-by-chunk-length
  (<= (fn-served-feed-steps conn octets) (len octets))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-feed-steps conn octets)
           :in-theory (disable fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep))))

(defun fn-served-step-nntp-steps (conn octets)
  (declare (xargs :guard t))
  (if (not (fn-wire-statep (fn-served-conn-wire conn)))
      0
    (fn-served-feed-steps conn octets)))

(defthm fn-served-step-nntp-steps-is-bounded
  (implies (fn-served-connp conn)
           (<= (fn-served-step-nntp-steps conn octets) (len octets)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-served-feed-steps fn-wire-statep
                                      fn-served-connp))))

; OPEN, recorded rather than weakened.  A served read costs
;
;     (fn-served-step-nntp-steps conn octets) <= (len octets)
;
; dispatcher steps, and the framing work per octet is constant
; (fn-wire-feed-byte, bounded retained input by
; fn-wire-feed-byte-retained-input-is-bounded, books/wire.lisp).  The cost of
; ONE fn-auth-step is not yet a theorem: the worst commands are LISTGROUP
; over a range and LIST ACTIVE with a wildmat, which are linear in the pinned
; archive's articles and groups and in the wildmat budget of
; books/wildmat-work.lisp, and an article body costs fn-inj-decide over the
; body, bounded by the configured size.  Closing this needs the instrumented
; twin of packet P3 / M6 (specs/node-functionality.md sections 3.2 and 5.2): a
; fn-served-step-cost that returns the step and a natural, and
;
;   (defthm fn-served-step-cost-is-bounded
;     (implies (fn-served-connp conn)
;              (<= (fn-served-step-cost conn octets)
;                  (* *fn-served-cost-k*
;                     (+ 1 (len octets)
;                        (fn-wire-state-line-limit (fn-served-conn-wire conn))
;                        (fn-inj-config-max-octets (fn-served-conn-config conn))
;                        (len (fn-state-groups (fn-served-conn-archive conn)))
;                        (len (fn-state-articles (fn-served-conn-archive conn))))))))
;
; No book claims that bound today.
;
; ALSO OPEN: the byte fold makes the fn-wire-octet-listp hypotheses of
; fn-served-step-preserves-connp and fn-served-step-partition-independence,
; and the fn-served-connp hypothesis of fn-served-step-nntp-steps-is-bounded,
; unnecessary (their proofs above do not use them).  The statements are kept
; as the served-path lane stated them; the next lane that touches this book
; should delete those hypotheses and the two probes recorded for them in
; tests/acl2/served-tests.lisp.

; -----------------------------------------------------------------------------
; Export theory
;
; What leaves enabled: the keystones, the record lemmas, the forward shape
; rules, the list-recursive vocabulary the proofs above induct on
; (fn-served-effectsp, fn-served-chunk-listp, fn-served-concat,
; fn-served-reply-octets, fn-served-closingp, fn-served-submission,
; fn-served-dispatch-events) and the fold laws.  Withdrawn: the connection
; recognizer (already withdrawn above), the effect recognizers, the
; transitions and the fold projections, so a book above computes with them
; and never inherits their unfolding.

(deftheory fn-served-vocabulary
  '(fn-served-closed-wirep fn-served-tls-handshakingp fn-served-starttlsp
    fn-served-submit-effectp fn-served-effectp
    fn-served-dispatch fn-served-feed fn-served-step fn-served-run
    fn-served-greeting fn-served-open fn-served-open-peer fn-served-post-outcome
    fn-served-transit-outcome
    fn-served-feed-steps fn-served-step-nntp-steps))

(in-theory (disable fn-served-vocabulary))
