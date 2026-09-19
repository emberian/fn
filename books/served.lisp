; The served path of the NNTP reader, in logic mode.
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
; `fn-served-step' is one socket read.  The host now performs exactly one call
; of it per read and keeps no protocol state of its own, so the subject of
; every theorem below is the function host/reader-host.lisp:104 calls.
;
; What is proved here, each lifted from a named keystone rather than reproved:
;
;   fn-served-step-preserves-connp          fn-wire-drive-preserves-statep
;                                           fn-nntp-finite-trace-preserves-
;                                             consistent-session
;   fn-served-step-effects-are-typed        fn-nntp-step-effects-well-formed
;   fn-served-step-partition-independence   fn-wire-drive-partition-independence
;   fn-served-run-is-the-concatenated-step  the two above, by induction
;   fn-served-reply-stream-is-partition-independent   the corollary the host
;                                           needs: the reply octets depend only
;                                           on the concatenated input, not on
;                                           how the network cut it
;   fn-served-step-nntp-steps-is-bounded    fn-wire-next-strictly-consumes
;
; OPEN (no theorem here): the cost of one `fn-nntp-step' is not yet bounded by
; a closed form.  See the obligation recorded at the end of this book.

(in-package "ACL2")
(include-book "wire-invariants")
(include-book "nntp-effects")

; -----------------------------------------------------------------------------
; Local record lemmas for the nntp result record
;
; books/nntp-session.lisp builds the result with `fn-nntp-make-result' and
; withdraws the constructor and the accessors at the nntp-effects export event
; without leaving accessor-of-constructor lemmas behind.  These three are that
; missing pair, kept local: no `-of-' equality about another cluster's record
; leaves this book.

(local
 (defthm fn-served-nntp-session-of-make-result
   (equal (fn-nntp-result-session (fn-nntp-make-result session effects))
          session)
   :hints (("Goal" :in-theory (enable fn-nntp-result-session
                                      fn-nntp-make-result)))))

(local
 (defthm fn-served-nntp-effects-of-make-result
   (equal (fn-nntp-result-effects (fn-nntp-make-result session effects))
          effects)
   :hints (("Goal" :in-theory (enable fn-nntp-result-effects
                                      fn-nntp-make-result)))))

(local
 (defthm fn-served-nntp-result-eta
   (implies (consp result)
            (equal (fn-nntp-make-result (fn-nntp-result-session result)
                                        (fn-nntp-result-effects result))
                   result))
   :hints (("Goal" :in-theory (enable fn-nntp-result-session
                                      fn-nntp-result-effects
                                      fn-nntp-make-result)))))

; -----------------------------------------------------------------------------
; The connection record: wire framing state, NNTP session, pinned archive
;
; The archive is the immutable snapshot the connection was opened against.  It
; is a field of the connection, not a global, because a served step must not be
; able to observe a later commit: that is the pinned-prefix discipline of
; specs/node-functionality.md section 1.1 with the version pin still to come.

(defun fn-served-conn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))

(defun fn-served-conn-wire (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-served-conn-session (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-served-conn-archive (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-served-make-conn (wire session archive)
  (declare (xargs :guard t))
  (list wire session archive))

(defthm fn-served-conn-shapep-of-fn-served-make-conn
  (fn-served-conn-shapep (fn-served-make-conn wire session archive)))

(defthm fn-served-conn-wire-of-fn-served-make-conn
  (equal (fn-served-conn-wire (fn-served-make-conn wire session archive))
         wire))

(defthm fn-served-conn-session-of-fn-served-make-conn
  (equal (fn-served-conn-session (fn-served-make-conn wire session archive))
         session))

(defthm fn-served-conn-archive-of-fn-served-make-conn
  (equal (fn-served-conn-archive (fn-served-make-conn wire session archive))
         archive))

(defthm fn-served-conn-shapep-forward-shape
  (implies (fn-served-conn-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-served-conn-shapep) (:d fn-served-conn-wire)
                    (:d fn-served-conn-session) (:d fn-served-conn-archive)
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
   (equal (equal (fn-served-make-conn w1 s1 a1) (fn-served-make-conn w2 s2 a2))
          (and (equal w1 w2) (equal s1 s2) (equal a1 a2)))
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
; the served path: fn-served-step branches on nothing.  It is the hypothesis
; the keystones below carry and the step preserves (proof-style section 4).  It
; is deliberately not guard verified: it is specification vocabulary, and
; fn-nntp-session-consistentp, which walks the pinned archive, is not
; executable on a served read by design.

(defun fn-served-connp (c)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-served-conn-shapep c)
       (fn-wire-statep (fn-served-conn-wire c))
       (fn-nntp-session-consistentp (fn-served-conn-session c)
                                    (fn-served-conn-archive c))))

(defthm fn-served-connp-forward-shape
  (implies (fn-served-connp c) (and (consp c) (true-listp c)))
  :rule-classes :forward-chaining)

(defthm fn-served-connp-is-wire-state
  (implies (fn-served-connp c)
           (fn-wire-statep (fn-served-conn-wire c))))

(defthm fn-served-connp-is-consistent-session
  (implies (fn-served-connp c)
           (fn-nntp-session-consistentp (fn-served-conn-session c)
                                        (fn-served-conn-archive c))))

(in-theory (disable fn-served-connp))

; -----------------------------------------------------------------------------
; One wire event at a time, over the events one read produced
;
; fn-nntp-run-session (books/nntp-invariants.lisp) already folds the sessions.
; This fold also accumulates the effects, in order; the bridge theorem below
; says its session component is exactly fn-nntp-run-session, so the session
; keystones are cited rather than reproved.

(defun fn-served-nntp-run (session archive env events)
  (declare (xargs :guard t))
  (if (consp events)
      (let* ((here (fn-nntp-step session archive env (car events)))
             (tail (fn-served-nntp-run (fn-nntp-result-session here)
                                       archive env (cdr events))))
        (fn-nntp-make-result
         (fn-nntp-result-session tail)
         (mbe :logic (append (fn-nntp-result-effects here)
                             (fn-nntp-result-effects tail))
              :exec (fn-ag-append (fn-nntp-result-effects here)
                                  (fn-nntp-result-effects tail)))))
    (fn-nntp-make-result session nil)))

; A read that framed no event runs no dispatcher step.  Local: a definitional
; branch restatement, kept as a rewrite for the proofs below and never
; exported.
(local
 (defthm fn-served-nntp-run-of-no-events
   (implies (not (consp events))
            (equal (fn-served-nntp-run session archive env events)
                   (fn-nntp-make-result session nil)))))

(local
 (defthm fn-served-nntp-run-is-consp
   (consp (fn-served-nntp-run session archive env events))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (e/d (fn-nntp-make-result)
                                   (fn-nntp-step))))))

(defthm fn-served-nntp-run-session-is-nntp-run-session
  (equal (fn-nntp-result-session (fn-served-nntp-run session archive env events))
         (fn-nntp-run-session session archive env events))
  :hints (("Goal" :induct (fn-served-nntp-run session archive env events)
           :in-theory (disable fn-nntp-step fn-nntp-session-consistentp
                               fn-nntp-projectionp))))

(defthm fn-served-nntp-run-preserves-consistent-session
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-session-consistentp
            (fn-nntp-result-session (fn-served-nntp-run session archive env events))
            archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-finite-trace-preserves-consistent-session))
           :in-theory (disable fn-nntp-run-session fn-served-nntp-run
                               fn-nntp-session-consistentp fn-nntp-projectionp
                               fn-nntp-finite-trace-preserves-consistent-session))))

; Effect typing over the fold.  fn-nntp-effectsp is list-recursive vocabulary,
; so the append closure is an induction over it; the per-event fact is
; fn-nntp-step-effects-well-formed, cited, not reproved.

(defthm fn-served-nntp-effectsp-of-append
  (implies (and (fn-nntp-effectsp left) (fn-nntp-effectsp right))
           (fn-nntp-effectsp (append left right)))
  :hints (("Goal" :induct (fn-nntp-effectsp left)
           :in-theory (disable fn-nntp-effectp))))

(local
 (defthm fn-served-close-effect-is-typed
   (fn-nntp-effectsp (list (fn-nntp-close-effect)))
   :hints (("Goal" :in-theory (enable fn-nntp-effectsp fn-nntp-effectp
                                      fn-nntp-close-effect)))))

(defthm fn-served-nntp-run-effects-are-typed
  (implies (fn-nntp-session-consistentp session archive)
           (fn-nntp-effectsp
            (fn-nntp-result-effects (fn-served-nntp-run session archive env events))))
  :hints (("Goal" :induct (fn-served-nntp-run session archive env events)
           :in-theory (disable fn-nntp-step fn-nntp-effectp
                               fn-nntp-session-consistentp
                               fn-nntp-projectionp))))

; -----------------------------------------------------------------------------
; One socket read
;
; `env' is the reader environment of this read (fn-nntp-env, books/
; nntp-responses.lisp): one clock observation and the group-creation facts,
; supplied by the host per read and shared by every event the read framed.
; It is carried, never inspected, here; fn-nntp-step is its only consumer.
;
; fn-wire-drive is the adapter's chunk loop (books/wire-invariants.lisp:353);
; the fold above is the dispatcher run over the events it produced.  The close
; effect is appended on the transition edge only: a read that finds the wire
; already closed is a no-op, which is what makes the partition law below
; unconditional and what the host does (it stops reading after a close).

(defun fn-served-closed-wirep (wire)
  (declare (xargs :guard t))
  (equal (fn-wire-state-mode wire) :closed))

(defun fn-served-step (conn env octets)
  (declare (xargs :guard t))
  (let* ((wire (fn-served-conn-wire conn))
         (archive (fn-served-conn-archive conn))
         (drive (fn-wire-drive wire octets))
         (wire2 (fn-wire-result-state drive))
         (run (fn-served-nntp-run (fn-served-conn-session conn) archive env
                                  (fn-wire-result-events drive))))
    (fn-served-make-result
     (fn-served-make-conn wire2 (fn-nntp-result-session run) archive)
     (mbe :logic (append (fn-nntp-result-effects run)
                         (if (and (not (fn-served-closed-wirep wire))
                                  (fn-served-closed-wirep wire2))
                             (list (fn-nntp-close-effect))
                           nil))
          :exec (fn-ag-append (fn-nntp-result-effects run)
                              (if (and (not (fn-served-closed-wirep wire))
                                       (fn-served-closed-wirep wire2))
                                  (list (fn-nntp-close-effect))
                                nil))))))

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

(defun fn-served-run (conn env chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (let* ((here (fn-served-step conn env (car chunks)))
             (tail (fn-served-run (fn-served-result-conn here) env (cdr chunks))))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    ;; An empty run is an empty read: the same base case the concatenation
    ;; theorem below reduces to, with no record eta law needed to see it.
    (fn-served-step conn env nil)))

; The two projections the host is allowed to take of an effect list.  They were
; fn-reader-effect-octets and fn-reader-close-effectsp in :program-mode host
; Lisp; concatenating a reply stream is a decision, and ACL2 owns it.

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

; Opening a connection: the one place the whole-archive projection recognizer
; runs (fn-nntp-open-session records its verdict in the session and no command
; recomputes it).  The greeting is RFC 3977 section 5.1.1's 201 response for a
; server that does not permit posting.

(defconst *fn-served-greeting*
  '(50 48 49 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109
    101 110 116 97 108 32 114 101 97 100 101 114 32 114 101 97 100 121 13 10))

(defun fn-served-open (archive line-limit body-limit)
  (declare (xargs :guard t))
  (fn-served-make-result
   (fn-served-make-conn (fn-wire-initial-state line-limit body-limit)
                        (fn-nntp-open-session archive)
                        archive)
   (list (fn-nntp-reply-effect *fn-served-greeting*))))

(defthm fn-served-open-is-a-connection
  (implies (and (posp line-limit) (posp body-limit))
           (fn-served-connp
            (fn-served-result-conn (fn-served-open archive line-limit body-limit))))
  :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                  (fn-wire-statep fn-wire-initial-state
                                   fn-nntp-open-session
                                   fn-nntp-session-consistentp
                                   fn-nntp-projectionp))
           :use ((:instance fn-wire-initial-state-is-state)
                 (:instance fn-nntp-open-session-is-consistent)))))

(defthm fn-served-concat-is-an-octet-list
  (implies (fn-served-chunk-listp chunks)
           (fn-wire-octet-listp (fn-served-concat chunks)))
  :hints (("Goal" :induct (fn-served-chunk-listp chunks))))

; -----------------------------------------------------------------------------
; Keystone 1: the carried invariant is preserved by one read

(defthm fn-served-step-preserves-connp
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp octets))
           (fn-served-connp (fn-served-result-conn (fn-served-step conn env octets))))
  :hints (("Goal"
           :in-theory (e/d (fn-served-connp)
                           (fn-wire-statep fn-wire-drive
                            fn-served-nntp-run
                            fn-nntp-session-consistentp fn-nntp-projectionp
                            fn-wire-drive-preserves-statep
                            fn-served-nntp-run-preserves-consistent-session))
           :use ((:instance fn-wire-drive-preserves-statep
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-served-nntp-run-preserves-consistent-session
                            (session (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (events (fn-wire-result-events
                                     (fn-wire-drive (fn-served-conn-wire conn)
                                                    octets))))
                 (:instance fn-served-connp-is-wire-state (c conn))
                 (:instance fn-served-connp-is-consistent-session (c conn))))))

(defthm fn-served-run-preserves-connp
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (fn-served-connp (fn-served-result-conn (fn-served-run conn env chunks))))
  :hints (("Goal" :induct (fn-served-run conn env chunks)
           :in-theory (disable fn-served-step fn-served-connp))))

; -----------------------------------------------------------------------------
; Keystone 2: the refusal enumeration
;
; fn-nntp-effectsp is the closed enumeration: every effect of a served read is
; either (:reply octets) with fn-nntp-replyp octets, or the close effect.  A
; read produces nothing else -- no exception, no untyped value, no third
; outcome.

(defthm fn-served-step-effects-are-typed
  (implies (fn-served-connp conn)
           (fn-nntp-effectsp (fn-served-result-effects (fn-served-step conn env octets))))
  :hints (("Goal"
           :in-theory (disable fn-served-nntp-run fn-wire-drive
                               fn-nntp-effectp fn-nntp-session-consistentp
                               fn-nntp-projectionp fn-wire-statep
                               fn-served-nntp-run-effects-are-typed)
           :use ((:instance fn-served-connp-is-consistent-session (c conn))
                 (:instance fn-served-nntp-run-effects-are-typed
                            (session (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (events (fn-wire-result-events
                                     (fn-wire-drive (fn-served-conn-wire conn)
                                                    octets))))))))

(defthm fn-served-run-effects-are-typed
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (fn-nntp-effectsp (fn-served-result-effects (fn-served-run conn env chunks))))
  :hints (("Goal" :induct (fn-served-run conn env chunks)
           :in-theory (disable fn-served-step fn-served-connp
                               fn-nntp-effectp))))

; The enumeration read off fn-nntp-effectp itself.  A definitional restatement:
; :rule-classes nil, never a registry event.
(defthm fn-served-typed-effect-is-reply-or-close-by-definition
  (implies (fn-nntp-effectp effect)
           (or (and (equal (car effect) :reply)
                    (fn-octet-listp (car (cdr effect)))
                    (fn-nntp-replyp (car (cdr effect))))
               (equal effect (fn-nntp-close-effect))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nntp-effectp) (fn-nntp-replyp)))))

; -----------------------------------------------------------------------------
; Keystone 3: partition independence
;
; fn-wire-drive-partition-independence (books/wire-invariants.lisp:580) says
; the framing is blind to how the network cut the stream.  Lifting it through
; the dispatcher fold needs the fold to split over an append of events, and
; needs the close effect to sit on the transition edge so that a read of a
; closed wire contributes nothing.

(local
 (defthm fn-served-append-is-associative
   (equal (append (append a b) c) (append a (append b c)))))

; The session fold splits over an append of events; the fn-nntp-run-session
; sibling of the theorem below.  Local: books/nntp-invariants.lisp owns
; fn-nntp-run-session and should carry this law when it needs it.
(local
 (defthm fn-served-nntp-run-session-of-append
  (equal (fn-nntp-run-session session archive env (append left right))
         (fn-nntp-run-session (fn-nntp-run-session session archive left)
                              archive env right))
  :hints (("Goal" :induct (fn-nntp-run-session session archive env left)
           :in-theory (disable fn-nntp-step fn-nntp-session-consistentp
                               fn-nntp-projectionp)))))

(defthm fn-served-nntp-run-of-append
  (equal (fn-served-nntp-run session archive env (append left right))
         (fn-nntp-make-result
          (fn-nntp-result-session
           (fn-served-nntp-run
            (fn-nntp-result-session (fn-served-nntp-run session archive env left))
            archive env right))
          (append
           (fn-nntp-result-effects (fn-served-nntp-run session archive env left))
           (fn-nntp-result-effects
            (fn-served-nntp-run
             (fn-nntp-result-session (fn-served-nntp-run session archive env left))
             archive env right)))))
  :hints (("Goal" :induct (fn-served-nntp-run session archive env left)
           :in-theory (disable fn-nntp-step fn-nntp-session-consistentp
                               fn-nntp-projectionp
                               fn-served-nntp-run-session-is-nntp-run-session
                               fn-served-nntp-run-session-of-append))))

(local
 (defthm fn-served-drive-of-closed-mode
   (implies (fn-served-closed-wirep wire-state)
            (equal (fn-wire-drive wire-state octets)
                   (fn-wire-make-result wire-state nil)))
   :hints (("Goal" :use ((:instance fn-wire-drive-closed-is-noop))
            :in-theory (disable fn-wire-drive-closed-is-noop fn-wire-drive)))))

(defthm fn-served-step-partition-independence
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp left)
                (fn-wire-octet-listp right))
           (equal (fn-served-step conn env (append left right))
                  (fn-served-make-result
                   (fn-served-result-conn
                    (fn-served-step
                     (fn-served-result-conn (fn-served-step conn env left)) env right))
                   (append
                    (fn-served-result-effects (fn-served-step conn env left))
                    (fn-served-result-effects
                     (fn-served-step
                      (fn-served-result-conn (fn-served-step conn env left)) env
                      right))))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal (fn-wire-state-mode
                           (fn-wire-result-state
                            (fn-wire-drive (fn-served-conn-wire conn) left)))
                          :closed))
           :in-theory (disable fn-wire-drive fn-served-nntp-run fn-wire-statep
                               fn-wire-feed-proper fn-wire-drive-is-feed-proper
                               fn-nntp-session-consistentp fn-nntp-projectionp
                               fn-wire-drive-partition-independence
                               fn-wire-drive-preserves-statep
                               fn-served-nntp-run-of-append
                               fn-served-nntp-run-session-is-nntp-run-session
                               fn-served-connp
                               fn-nntp-effectp fn-nntp-effectsp)
           :use ((:instance fn-wire-drive-partition-independence
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-wire-drive-preserves-statep
                            (wire-state (fn-served-conn-wire conn))
                            (octets left))
                 (:instance fn-served-nntp-run-of-append
                            (session (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (left (fn-wire-result-events
                                   (fn-wire-drive (fn-served-conn-wire conn) left)))
                            (right (fn-wire-result-events
                                    (fn-wire-drive
                                     (fn-wire-result-state
                                      (fn-wire-drive (fn-served-conn-wire conn) left))
                                     right))))
                 (:instance fn-served-connp-is-wire-state (c conn))))))

; The law the host needs: however the network cut the stream, the connection
; and the effect sequence after the whole run are those of one read of the
; concatenation.  Chunk boundaries are invisible.

(defthm fn-served-run-is-the-concatenated-step
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp chunks))
           (equal (fn-served-run conn env chunks)
                  (fn-served-step conn env (fn-served-concat chunks))))
  :hints (("Goal" :induct (fn-served-run conn env chunks)
           :in-theory (disable fn-served-step fn-served-connp
                               fn-wire-drive fn-wire-statep
                               fn-served-nntp-run)
           :expand ((fn-served-concat chunks)))))

(defthm fn-served-reply-stream-is-partition-independent
  (implies (and (fn-served-connp conn)
                (fn-served-chunk-listp one)
                (fn-served-chunk-listp two)
                (equal (fn-served-concat one) (fn-served-concat two)))
           (equal (fn-served-reply-octets
                   (fn-served-result-effects (fn-served-run conn env one)))
                  (fn-served-reply-octets
                   (fn-served-result-effects (fn-served-run conn env two)))))
  :hints (("Goal"
           :in-theory (disable fn-served-run fn-served-step fn-served-connp
                               fn-served-concat fn-served-reply-octets
                               fn-served-run-is-the-concatenated-step)
           :use ((:instance fn-served-run-is-the-concatenated-step (chunks one))
                 (:instance fn-served-run-is-the-concatenated-step (chunks two))))))

; -----------------------------------------------------------------------------
; Keystone 4: work per read
;
; The number of dispatcher steps one read performs is at most the length of the
; read.  fn-wire-next-strictly-consumes (books/wire-invariants.lisp:311) is the
; progress fact and fn-wire-next-preserves-statep (:154) carries the invariant
; through the loop; each turn of fn-wire-drive emits at most one event.

; fn-wire-next-strictly-consumes is a rewrite rule; the bound below is
; arithmetic, so it needs the same fact as a linear rule.  Local: the wire
; cluster owns the progress fact and should carry this rule class if another
; book ever needs it.
(local
 (defthm fn-served-next-strictly-consumes-linear
   (implies (and (fn-wire-statep wire-state)
                 (not (equal (fn-wire-state-mode wire-state) :closed))
                 (consp octets))
            (< (len (fn-wire-next-unconsumed (fn-wire-next wire-state octets)))
               (len octets)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-wire-next-strictly-consumes))
            :in-theory (disable fn-wire-next fn-wire-statep
                                fn-wire-state-mode fn-wire-next-unconsumed
                                fn-wire-next-strictly-consumes)))))

(defthm fn-served-drive-events-bounded-by-chunk-length
  (implies (fn-wire-statep wire-state)
           (<= (len (fn-wire-result-events (fn-wire-drive wire-state octets)))
               (len octets)))
  :rule-classes :linear
  :hints (("Goal"
           :induct (fn-wire-drive wire-state octets)
           :expand ((fn-wire-drive wire-state octets))
           :in-theory (e/d () (fn-wire-next fn-wire-statep fn-wire-state-mode
                               fn-wire-drive)
                           ((:induction fn-wire-drive))))))

(defun fn-served-step-nntp-steps (conn octets)
  (declare (xargs :guard t))
  (len (fn-wire-result-events (fn-wire-drive (fn-served-conn-wire conn) octets))))

(defthm fn-served-step-nntp-steps-is-bounded
  (implies (fn-served-connp conn)
           (<= (fn-served-step-nntp-steps conn octets) (len octets)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (disable fn-wire-drive fn-wire-statep
                               fn-served-drive-events-bounded-by-chunk-length)
           :use ((:instance fn-served-drive-events-bounded-by-chunk-length
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-served-connp-is-wire-state (c conn))))))

; OPEN, recorded rather than weakened.  A served read costs
;
;     (fn-served-step-nntp-steps conn octets) <= (len octets)
;
; dispatcher steps, and the framing work per octet is constant
; (fn-wire-feed-byte, bounded retained input by
; fn-wire-feed-byte-retained-input-is-bounded, books/wire.lisp:441).  The cost
; of ONE fn-nntp-step is not yet a theorem: the worst commands are LISTGROUP
; over a range and LIST ACTIVE with a wildmat, which are linear in the pinned
; archive's articles and groups and in the wildmat budget of
; books/wildmat-work.lisp.  Closing this needs the instrumented twin of packet
; P3 / M6 (specs/node-functionality.md sections 3.2 and 5.2): a
; fn-served-step-cost that returns the step and a natural, and
;
;   (defthm fn-served-step-cost-is-bounded
;     (implies (fn-served-connp conn)
;              (<= (fn-served-step-cost conn octets)
;                  (* *fn-served-cost-k*
;                     (+ 1 (len octets)
;                        (fn-wire-state-line-limit (fn-served-conn-wire conn))
;                        (len (fn-state-groups (fn-served-conn-archive conn)))
;                        (len (fn-state-articles (fn-served-conn-archive conn))))))))
;
; No book claims that bound today.

; -----------------------------------------------------------------------------
; Export theory
;
; What leaves enabled: the four keystones, the record lemmas, the two forward
; shape rules, the list-recursive vocabulary the proofs above induct on
; (fn-served-chunk-listp, fn-served-concat, fn-served-reply-octets,
; fn-served-closingp, fn-served-nntp-run) and the bridge to
; fn-nntp-run-session.  Withdrawn: the connection recognizer (already
; withdrawn above), the transitions and the fold projections, so a book above
; computes with them and never inherits their unfolding.

(deftheory fn-served-vocabulary
  '(fn-served-closed-wirep fn-served-step fn-served-run
    fn-served-open fn-served-step-nntp-steps))

(in-theory (disable fn-served-vocabulary))
