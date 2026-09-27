; fn: one-pass served receive result plus physical prefix ownership.
;
; A socket observation may contain a STARTTLS command line and early TLS
; bytes.  This fold uses fn-served-feed-byte, the same framing/dispatch byte
; transition as fn-served-feed, and returns both the ordinary served result
; and how many observed octets that result consumed before the connection
; became handshaking or closed.  No parser or served transition runs twice.
;
; PKT-600 (lane transit-pipelining, PRF-213, NNT-044): the fold also stops
; after the octet whose dispatch emitted a submission.  A streaming peer
; pipelines TAKETHIS and a client may pipeline POST (RFC 4644 section 2.5,
; RFC 3977 section 3.5), so one socket read can carry two complete articles;
; the owner takes one submission per read (fn-own-finish-read), and the fold
; used to walk on and emit the second, which nothing took.  Now the read
; yields after the first article, the host commits it and answers it, and
; feeds the unconsumed suffix as the next read (host/native/owner.lisp, the
; `retained' offset of the serve loop).  What this costs the reference is
; stated below: the counted read IS fn-served-step over the consumed prefix
; (fn-served-step-counted-result-is-step-of-consumed-prefix), iterating it to
; exhaustion IS fn-served-step over the whole read (fn-served-drain-is-step),
; so the commands and articles consumed from a stream do not depend on where
; the network or this yield cut it (fn-served-drain-run-is-boundary-
; independent), each yield carries at most one submission
; (fn-served-step-counted-carries-at-most-one-submission) and the one the
; owner takes per yield are all of them (fn-served-drain-takes-every-
; submission).

(in-package "ACL2")
(include-book "served")

; (:fn-served-counted consumed served-result).
(defun fn-served-counted-make (consumed result)
  (declare (xargs :guard t))
  (list :fn-served-counted consumed result))

(defun fn-served-counted-consumed (counted)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr counted)))

(defun fn-served-counted-result (counted)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr counted))))

(defun fn-served-feed-counted (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-wire-fast-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let ((here (fn-served-feed-byte conn (car octets) fn-arena)))
      ;; PKT-600: yield after the octet that completed a submission; the rest
      ;; of the read is the next read's input.
      (if (fn-served-submission (fn-served-result-effects here))
          (fn-served-counted-make
           1 (fn-served-make-result (fn-served-result-conn here)
                                    (fn-served-result-effects here)))
        (let* ((tail (fn-served-feed-counted
                      (fn-served-result-conn here) (cdr octets) fn-arena))
               (tail-result (fn-served-counted-result tail)))
          (fn-served-counted-make
           (+ 1 (fn-served-counted-consumed tail))
           (fn-served-make-result
            (fn-served-result-conn tail-result)
            (mbe :logic (append (fn-served-result-effects here)
                                (fn-served-result-effects tail-result))
                 :exec (fn-ag-append (fn-served-result-effects here)
                                     (fn-served-result-effects tail-result))))))))))

(defthm fn-served-feed-counted-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-served-feed-counted conn octets fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-served-feed-counted conn octets fn-arena)
           :in-theory (enable fn-served-feed-counted
                              fn-served-counted-make
                              fn-served-counted-consumed))))

(verify-guards fn-served-feed-counted
  :hints (("Goal"
           :in-theory (disable fn-served-feed-byte fn-wire-fast-statep
                               fn-served-counted-consumed
                               fn-served-feed-byte-preserves-fast-statep)
           :use ((:instance fn-served-feed-byte-preserves-fast-statep
                            (byte (car octets)))))))

(local
 (defthm fn-served-dispatch-events-effects-are-a-true-list
   (true-listp (fn-served-result-effects (fn-served-dispatch-events conn events fn-arena)))
   :hints (("Goal" :induct (fn-served-dispatch-events conn events fn-arena)
            :in-theory (disable fn-served-dispatch)))))

(local
 (defthm fn-served-feed-byte-effects-are-a-true-list
   (true-listp (fn-served-result-effects (fn-served-feed-byte conn byte fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-served-feed-byte)
                                   (fn-served-dispatch-events fn-wire-feed-byte))))))

(local
 (defthm fn-served-counted-accessors-of-make
   (and (equal (fn-served-counted-consumed (fn-served-counted-make consumed result))
               consumed)
        (equal (fn-served-counted-result (fn-served-counted-make consumed result))
               result))
   :hints (("Goal" :in-theory (enable fn-served-counted-make fn-served-counted-consumed
                                      fn-served-counted-result)))))

; The counted fold's result is the ordinary fold over exactly the octets it
; consumed.  (Before PKT-600 the two folds consumed the same octets and this
; was `fn-served-feed-counted-result-is-feed' over the whole read.)
(defthm fn-served-feed-counted-result-is-feed-of-consumed-prefix
  (equal (fn-served-counted-result
          (fn-served-feed-counted conn octets fn-arena))
         (fn-served-feed conn
                         (take (fn-served-counted-consumed
                                (fn-served-feed-counted conn octets fn-arena))
                               octets) fn-arena))
  :hints (("Goal"
           :induct (fn-served-feed-counted conn octets fn-arena)
           :expand ((:free (x) (fn-served-feed x nil fn-arena)))
           :in-theory (e/d (fn-served-feed-counted fn-served-feed take)
                           (fn-served-counted-make
                            fn-served-counted-result
                            fn-served-counted-consumed
                            fn-served-feed-byte fn-served-dispatch-events
                            fn-wire-feed-byte fn-wire-statep)))))

(defthm fn-served-feed-counted-consumed-is-bounded
  (<= (fn-served-counted-consumed
       (fn-served-feed-counted conn octets fn-arena))
      (len octets))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-feed-counted conn octets fn-arena)
           :in-theory (enable fn-served-feed-counted
                              fn-served-counted-make
                              fn-served-counted-consumed))))

; Common transition under the fixed-spine/scalar execution invariant.
(defun fn-served-step-counted-core (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard
                  (fn-wire-fast-statep (fn-served-conn-wire conn))))
  (let* ((wire (fn-served-conn-wire conn))
         (fed (fn-served-feed-counted conn octets fn-arena))
         (result (fn-served-counted-result fed))
         (wire2 (fn-served-conn-wire (fn-served-result-conn result))))
    (fn-served-counted-make
     (fn-served-counted-consumed fed)
     (fn-served-make-result
      (fn-served-result-conn result)
      (mbe :logic
           (append (fn-served-result-effects result)
                   (if (and (not (fn-served-closed-wirep wire))
                            (fn-served-closed-wirep wire2))
                       (list (fn-nntp-close-effect))
                     nil))
           :exec
           (fn-ag-append
            (fn-served-result-effects result)
            (if (and (not (fn-served-closed-wirep wire))
                     (fn-served-closed-wirep wire2))
                (list (fn-nntp-close-effect))
              nil)))))))

; Total checked reference, retaining the historical malformed-wire no-op.
(defun fn-served-step-counted (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (not (fn-wire-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-served-step-counted-core conn octets fn-arena)))

; Production entry: only the fixed spine and scalars are checked per read.
(defun fn-served-step-counted-fast (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (not (fn-wire-fast-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-served-step-counted-core conn octets fn-arena)))

(defthm fn-served-step-counted-fast-is-reference
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (equal (fn-served-step-counted-fast conn octets fn-arena)
                  (fn-served-step-counted conn octets fn-arena)))
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted-fast
                              fn-served-step-counted)
           :use ((:instance fn-wire-statep-implies-fast-statep
                            (x (fn-served-conn-wire conn)))))))

; The called counted transition returns the exact ordinary served result of
; the octets it consumed.  KEYSTONE (PRF-213): the subject is the reference of
; the transition the host calls (fn-served-step-counted-fast, equal to it by
; fn-served-step-counted-fast-is-reference, under host/owner-host.lisp
; fn-owner-chunk-span through books/served-span.lisp).  No hypothesis.
(defthm fn-served-step-counted-result-is-step-of-consumed-prefix
  (equal (fn-served-counted-result
          (fn-served-step-counted conn octets fn-arena))
         (fn-served-step conn
                         (take (fn-served-counted-consumed
                                (fn-served-step-counted conn octets fn-arena))
                               octets) fn-arena))
  :hints (("Goal"
           :in-theory (e/d (fn-served-step-counted
                            fn-served-step-counted-core
                            fn-served-counted-make
                            fn-served-counted-result
                            fn-served-counted-consumed
                            fn-served-step)
                           (fn-served-feed-counted-result-is-feed-of-consumed-prefix))
           :use ((:instance fn-served-feed-counted-result-is-feed-of-consumed-prefix)))))

; The served invariant survives one read of ANY octets: the byte fold
; preserves it unconditionally (fn-served-feed-preserves-connp), and the
; octet-list hypothesis of fn-served-step-preserves-connp is the one its own
; book records as unnecessary.  Stated here because the prefix a yielding read
; consumed is a `take', not a named octet list.
(defthm fn-served-step-preserves-connp-of-any-input
  (implies (fn-served-connp conn)
           (fn-served-connp (fn-served-result-conn (fn-served-step conn octets fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-served-step)
                                  (fn-served-feed fn-wire-statep fn-served-connp))
           :use ((:instance fn-served-feed-preserves-connp)
                 (:instance fn-served-connp-is-wire-state (c conn))))))

(defthm fn-served-step-counted-fast-preserves-connp
  (implies (and (fn-served-connp conn)
                (fn-wire-octet-listp octets))
           (fn-served-connp
            (fn-served-result-conn
             (fn-served-counted-result
              (fn-served-step-counted-fast conn octets fn-arena)))))
  :hints (("Goal"
           :use ((:instance fn-served-step-counted-fast-is-reference)
                 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                 (:instance fn-served-step-preserves-connp-of-any-input
                            (octets (take (fn-served-counted-consumed
                                           (fn-served-step-counted conn octets fn-arena))
                                          octets))))
           :in-theory (disable fn-served-step-counted-fast-is-reference
                               fn-served-step-counted-result-is-step-of-consumed-prefix
                               fn-served-step-preserves-connp-of-any-input
                               fn-served-step-preserves-connp
                               fn-served-step-counted-fast
                               fn-served-step-counted
                               fn-served-step
                               fn-served-connp))))

(defthm fn-served-step-counted-fast-consumed-is-bounded
  (<= (fn-served-counted-consumed
       (fn-served-step-counted-fast conn octets fn-arena))
      (len octets))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted-fast
                              fn-served-step-counted-core
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-bounded)))))

(defthm fn-served-step-counted-fast-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-served-step-counted-fast conn octets fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted-fast
                              fn-served-step-counted-core
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-natural)))))

(defthm fn-served-step-counted-consumed-is-bounded
  (<= (fn-served-counted-consumed
       (fn-served-step-counted conn octets fn-arena))
      (len octets))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-bounded)))))

(defthm fn-served-step-counted-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-served-step-counted conn octets fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable fn-served-step-counted
                              fn-served-counted-make
                              fn-served-counted-consumed)
           :use ((:instance fn-served-feed-counted-consumed-is-natural)))))

(local
 (defthm fn-served-tls-take-nthcdr-reconstructs
   (implies (and (natp n) (<= n (len xs)))
            (equal (append (take n xs) (nthcdr n xs)) xs))
   :hints (("Goal" :induct (take n xs)
            :in-theory (enable take nthcdr)))))

; The returned count partitions the physical observation without loss or
; duplication.  The suffix is transport input, never another NNTP parse.
(defthm fn-served-tls-prefix-suffix-accounting
  (let ((count (fn-served-counted-consumed
                (fn-served-step-counted conn octets fn-arena))))
    (equal (append (take count octets) (nthcdr count octets)) octets))
  :hints (("Goal"
           :use ((:instance fn-served-tls-take-nthcdr-reconstructs
                            (n (fn-served-counted-consumed
                                (fn-served-step-counted conn octets fn-arena)))
                            (xs octets))
                 (:instance fn-served-step-counted-consumed-is-bounded)
                 (:instance fn-served-step-counted-consumed-is-natural))
           :in-theory (disable fn-served-tls-take-nthcdr-reconstructs
                               fn-served-step-counted-consumed-is-bounded
                               fn-served-step-counted-consumed-is-natural
                               fn-served-step-counted
                               fn-served-counted-consumed))))

(in-theory (disable fn-served-counted-make
                    fn-served-counted-consumed
                    fn-served-counted-result
                    fn-served-feed-counted
                    fn-served-step-counted-core
                    fn-served-step-counted-fast
                    fn-served-step-counted))

; -----------------------------------------------------------------------------
; PKT-600: a pipelined stream loses no submission (PRF-213, NNT-044).
;
; The list of every submission an effect list carries, in order.  The owner
; takes the FIRST (fn-served-submission, read by fn-own-finish-read); the
; theorems below say a yielding read carries at most one, and that the ones
; taken read by read are all the stream's.  Specification vocabulary: the
; host never calls it.

(defun fn-served-submissions (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (and (consp (car effects))
               (equal (car (car effects)) :submit)
               (consp (cdr (car effects)))
               (car (cdr (car effects))))
          (cons (car (cdr (car effects)))
                (fn-served-submissions (cdr effects)))
        (fn-served-submissions (cdr effects)))
    nil))

(defthm fn-served-submissions-of-append
  (equal (fn-served-submissions (append left right))
         (append (fn-served-submissions left)
                 (fn-served-submissions right))))

; What the owner takes is the head of this list: a definitional restatement,
; :rule-classes nil, never a registry event.
(defthm fn-served-submission-is-the-first-submission-by-definition
  (equal (fn-served-submission effects)
         (car (fn-served-submissions effects)))
  :rule-classes nil)

(local
 (defthm fn-served-submissions-empty-without-a-submission
   (implies (not (fn-served-submission effects))
            (equal (fn-served-submissions effects) nil))))

(local
 (defthm fn-served-submissions-of-at-most-one
   (implies (<= (len (fn-served-submissions effects)) 1)
            (equal (fn-served-submissions effects)
                   (if (fn-served-submission effects)
                       (list (fn-served-submission effects))
                     nil)))
   :rule-classes nil))

(local
 (defthm fn-served-auth-effect-is-not-a-submit
   (implies (fn-auth-effectp effect)
            (not (equal (car effect) :submit)))
   :hints (("Goal" :in-theory (enable fn-auth-effectp fn-nntp-effectp
                                      fn-nntp-close-effect fn-nntp-begin-article-effect
                                      fn-auth-starttls-effect)))))

(local
 (defthm fn-served-submissions-of-auth-effects
   (implies (fn-auth-effectsp effects)
            (equal (fn-served-submissions effects) nil))
   :hints (("Goal" :induct (fn-auth-effectsp effects)
            :in-theory (e/d (fn-auth-effectsp)
                            (fn-auth-effectp
                             fn-served-submissions-empty-without-a-submission))))))

; One dispatch emits the authenticated step's effects, which are never a
; submission (fn-auth-step-pinned-effects-well-formed), and at most the one
; :submit fn-served-dispatch appends.
(local
 (defthm fn-served-dispatch-core-carries-at-most-one-submission
   (implies (fn-served-connp conn)
            (<= (len (fn-served-submissions
                      (fn-served-result-effects (fn-served-dispatch-core conn event fn-arena))))
                1))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (e/d (fn-served-dispatch-core fn-served-submit-effect)
                            (fn-auth-step-pinned fn-served-connp fn-auth-effectsp
                             fn-post-offeredp fn-auth-session-consistentp
                             fn-wire-begin-article-with-line-limit
                             fn-wire-article-line-limit
                             fn-served-connp-is-consistent-session
                             fn-served-connp-is-group-correspondence
                             fn-served-connp-is-pinned-trie-correspondence
                             fn-auth-step-pinned-effects-well-formed))
            :use ((:instance fn-served-connp-is-consistent-session (c conn))
                  (:instance fn-served-connp-is-group-correspondence (c conn))
                  (:instance fn-served-connp-is-pinned-trie-correspondence (c conn))
                  (:instance fn-auth-step-pinned-effects-well-formed
                             (as (fn-served-conn-session conn))
                             (archive (fn-served-conn-archive conn))
                             (index (fn-served-conn-pinned-index conn))
                             (verdicts (fn-served-conn-verdicts conn))
                             (config (fn-served-conn-config conn))
                             (observation (fn-served-conn-observation conn))
                             (injection (fn-served-conn-injection conn))
                             (wire-event event)))))))

; NNT-042: on a GROUP or LISTGROUP line the dispatch's effects are the
; dispatch proper's over the re-pinned connection, itself a connection
; (books/served.lisp fn-served-repin-preserves-connp); otherwise it is the
; dispatch proper.
(local
 (defthm fn-served-dispatch-carries-at-most-one-submission
   (implies (fn-served-connp conn)
            (<= (len (fn-served-submissions
                      (fn-served-result-effects (fn-served-dispatch conn event fn-arena))))
                1))
   :rule-classes :linear
   :hints (("Goal"
            :cases ((fn-served-advance-eventp event))
            :use ((:instance fn-served-dispatch-core-carries-at-most-one-submission)
                  (:instance fn-served-dispatch-core-carries-at-most-one-submission
                             (conn (fn-served-repin conn)))
                  (:instance fn-served-repin-preserves-connp))
            :in-theory (e/d (fn-served-dispatch-effects-are-the-repinned-dispatch-effects
                             fn-served-dispatch-without-advance-is-core)
                            (fn-served-dispatch fn-served-dispatch-core fn-served-connp
                             fn-served-repin fn-served-advance-eventp
                             fn-served-dispatch-core-carries-at-most-one-submission
                             fn-served-repin-preserves-connp))))))

(local
 (defthm fn-served-tls-fed-conn-is-a-connection
   (implies (fn-served-connp conn)
            (fn-served-connp
             (fn-served-make-conn-group-indexed
              (fn-wire-result-state
               (fn-wire-feed-byte (fn-served-conn-wire conn) byte))
              (fn-served-conn-session conn)
              (fn-served-conn-archive conn)
              (fn-served-conn-config conn)
              (fn-served-conn-observation conn)
              (fn-served-conn-injection conn)
              (fn-served-conn-verdicts conn)
              (fn-served-conn-index conn)
              (fn-served-conn-group-index conn)
              (fn-served-conn-control conn))))
   :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                   (fn-wire-feed-byte fn-wire-statep
                                    fn-auth-session-consistentp))))))

(local
 (defthm fn-served-feed-byte-preserves-connp
   (implies (fn-served-connp conn)
            (fn-served-connp
             (fn-served-result-conn (fn-served-feed-byte conn byte fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-served-feed-byte)
                                   (fn-served-dispatch-events fn-wire-feed-byte
                                    fn-served-connp))))))

(local
 (defthm fn-served-feed-byte-carries-at-most-one-submission
   (implies (fn-served-connp conn)
            (<= (len (fn-served-submissions
                      (fn-served-result-effects (fn-served-feed-byte conn byte fn-arena))))
                1))
   :rule-classes :linear
   :hints (("Goal"
            :in-theory (e/d (fn-served-feed-byte)
                            (fn-served-dispatch fn-wire-feed-byte fn-served-connp
                             fn-wire-feed-byte-emits-at-most-one-event))
            :use ((:instance fn-wire-feed-byte-emits-at-most-one-event
                             (wire-state (fn-served-conn-wire conn))))
            :cases ((consp (fn-wire-result-events
                            (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))))))

(local
 (defthm fn-served-feed-counted-carries-at-most-one-submission
   (implies (fn-served-connp conn)
            (<= (len (fn-served-submissions
                      (fn-served-result-effects
                       (fn-served-counted-result
                        (fn-served-feed-counted conn octets fn-arena)))))
                1))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-served-feed-counted conn octets fn-arena)
            :in-theory (e/d (fn-served-feed-counted)
                            (fn-served-counted-make
                             fn-served-counted-result fn-served-counted-consumed
                             fn-served-feed-counted-result-is-feed-of-consumed-prefix
                             fn-served-feed-byte fn-served-connp))))))

; KEYSTONE (PRF-213): one yielding read carries at most one submission, so
; the owner's one take per read (fn-own-finish-read's fn-served-submission)
; is all of it.  The hypothesis is the served invariant; the host's read is
; this transition by fn-served-step-counted-fast-is-reference.
(defthm fn-served-step-counted-carries-at-most-one-submission
  (implies (fn-served-connp conn)
           (<= (len (fn-served-submissions
                     (fn-served-result-effects
                      (fn-served-counted-result
                       (fn-served-step-counted conn octets fn-arena)))))
               1))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-served-step-counted fn-served-step-counted-core
                                   fn-nntp-close-effect)
                                  (fn-served-feed-counted fn-served-connp
                                   fn-served-counted-make fn-served-counted-result
                                   fn-served-counted-consumed
                                   fn-served-feed-counted-result-is-feed-of-consumed-prefix
                                   fn-served-connp-is-wire-state))
           :use ((:instance fn-served-connp-is-wire-state (c conn))))))

; -----------------------------------------------------------------------------
; The resumable step and the host loop that drives it.
;
; host/native/owner.lisp's serve loop calls the read (through
; fn-owner-chunk-span) on [offset, end) of the octets it received, commits
; and answers the one submission it yielded, and calls it again on
; [offset + consumed, end) until the read is spent, the connection closes,
; or it hands the transport to TLS.  fn-served-drain is that loop over the
; reference transition; fn-served-drain-run is the loop over the socket's
; reads in arrival order.  Specification of the host loop, not called.

(local
 (defthm fn-served-tls-len-of-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(defun fn-served-drain (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :verify-guards nil
                  :measure (len octets)
                  :hints (("Goal" :in-theory (disable fn-served-step-counted)))))
  (let* ((counted (fn-served-step-counted conn octets fn-arena))
         (k (fn-served-counted-consumed counted))
         (result (fn-served-counted-result counted)))
    (if (or (zp k) (<= (len octets) k))
        result
      (let ((tail (fn-served-drain (fn-served-result-conn result)
                                   (nthcdr k octets) fn-arena)))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (append (fn-served-result-effects result)
                 (fn-served-result-effects tail)))))))

(defun fn-served-drain-run (conn chunks fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp chunks)
      (let* ((here (fn-served-drain conn (car chunks) fn-arena))
             (tail (fn-served-drain-run (fn-served-result-conn here)
                                        (cdr chunks) fn-arena)))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (append (fn-served-result-effects here)
                 (fn-served-result-effects tail))))
    (fn-served-drain conn nil fn-arena)))

; The submissions the owner takes, one per yield, in order.
(defun fn-served-drain-taken (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :verify-guards nil
                  :measure (len octets)
                  :hints (("Goal" :in-theory (disable fn-served-step-counted)))))
  (let* ((counted (fn-served-step-counted conn octets fn-arena))
         (k (fn-served-counted-consumed counted))
         (result (fn-served-counted-result counted))
         (one (fn-served-submission (fn-served-result-effects result))))
    (if (or (zp k) (<= (len octets) k))
        (if one (list one) nil)
      (append (if one (list one) nil)
              (fn-served-drain-taken (fn-served-result-conn result)
                                     (nthcdr k octets) fn-arena)))))

; A read that consumed nothing met a closed wire, a handshaking session or an
; empty read; one read of the whole input is then the same no-op.
(local
 (defthm fn-served-feed-counted-consumed-zero-is-a-no-op
   (implies (equal (fn-served-counted-consumed (fn-served-feed-counted conn octets fn-arena)) 0)
            (equal (fn-served-feed conn octets fn-arena)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-served-feed conn octets fn-arena)
                            (fn-served-feed-counted conn octets fn-arena))
            :in-theory (e/d ()
                            (fn-served-counted-make fn-served-counted-consumed
                             fn-served-counted-result
                             fn-served-feed-counted-result-is-feed-of-consumed-prefix
                             fn-served-feed-byte))))))

(local
 (defthm fn-served-step-of-nothing
   (equal (fn-served-step conn nil fn-arena)
          (fn-served-make-result conn nil))
   :hints (("Goal" :in-theory (enable fn-served-step fn-served-feed)))))

(local
 (defthm fn-served-step-counted-consumed-zero
   (implies (equal (fn-served-counted-consumed (fn-served-step-counted conn octets fn-arena)) 0)
            (and (equal (fn-served-step conn octets fn-arena)
                        (fn-served-make-result conn nil))
                 (equal (fn-served-counted-result (fn-served-step-counted conn octets fn-arena))
                        (fn-served-make-result conn nil))))
   :hints (("Goal" :in-theory (e/d (fn-served-step-counted fn-served-step-counted-core
                                    fn-served-counted-make fn-served-counted-consumed
                                    fn-served-counted-result fn-served-step)
                                   (fn-served-feed fn-served-feed-counted
                                    fn-served-feed-counted-result-is-feed-of-consumed-prefix))
            :expand ((fn-served-feed conn nil fn-arena))
            :use ((:instance fn-served-feed-counted-consumed-zero-is-a-no-op)
                  (:instance fn-served-feed-counted-result-is-feed-of-consumed-prefix))))))

(local
 (defthm fn-served-tls-take-of-len
   (implies (and (equal n (len xs)) (true-listp xs))
            (equal (take n xs) xs))))

(local
 (defthm fn-served-feed-of-true-list-fix
   (equal (fn-served-feed conn (true-list-fix octets) fn-arena)
          (fn-served-feed conn octets fn-arena))
   :hints (("Goal" :induct (fn-served-feed conn octets fn-arena)
            :in-theory (e/d (fn-served-feed true-list-fix)
                            (fn-served-feed-byte))))))

(local
 (defthm fn-served-step-of-true-list-fix
   (equal (fn-served-step conn (true-list-fix octets) fn-arena)
          (fn-served-step conn octets fn-arena))
   :hints (("Goal" :in-theory (e/d (fn-served-step) (fn-served-feed))))))

(local
 (defthm fn-served-tls-take-len-is-true-list-fix
   (equal (take (len xs) xs) (true-list-fix xs))
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-served-tls-append-take-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (append (take n xs) (nthcdr n xs)) xs))))

(local
 (defthm fn-served-tls-feed-of-closed-wire
   (implies (fn-served-closed-wirep (fn-served-conn-wire conn))
            (equal (fn-served-feed conn octets fn-arena)
                   (fn-served-make-result conn nil)))
   :hints (("Goal" :expand ((fn-served-feed conn octets fn-arena))))))

; The step's close effect is on the edge of the wire's closing, so one read of
; a concatenation is the read of its prefix then of its suffix, whatever the
; octets (fn-served-feed-of-append, no hypothesis).
(local
 (defthm fn-served-step-of-append-any
   (equal (fn-served-step conn (append left right) fn-arena)
          (fn-served-make-result
           (fn-served-result-conn
            (fn-served-step (fn-served-result-conn (fn-served-step conn left fn-arena)) right fn-arena))
           (append (fn-served-result-effects (fn-served-step conn left fn-arena))
                   (fn-served-result-effects
                    (fn-served-step (fn-served-result-conn (fn-served-step conn left fn-arena))
                                    right fn-arena)))))
   :hints (("Goal"
            :do-not-induct t
            :cases ((fn-served-closed-wirep
                     (fn-served-conn-wire
                      (fn-served-result-conn (fn-served-feed conn left fn-arena)))))
            :in-theory (e/d (fn-served-step)
                            (fn-served-feed fn-wire-statep))
            :use ((:instance fn-served-feed-preserves-wire-statep (octets left)))))))

;; One yield and the rest: the read of the whole input is the read of the
;; prefix the counted step consumed, then the read of the suffix.
(local
 (defthm fn-served-step-splits-at-the-yield
   (let* ((counted (fn-served-step-counted conn octets fn-arena))
          (k (fn-served-counted-consumed counted))
          (result (fn-served-counted-result counted)))
     (equal (fn-served-step conn octets fn-arena)
            (fn-served-make-result
             (fn-served-result-conn
              (fn-served-step (fn-served-result-conn result) (nthcdr k octets) fn-arena))
             (append (fn-served-result-effects result)
                     (fn-served-result-effects
                      (fn-served-step (fn-served-result-conn result)
                                      (nthcdr k octets) fn-arena))))))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d ()
                            (fn-served-step fn-served-step-counted
                             fn-served-step-of-append-any
                             fn-served-tls-append-take-nthcdr
                             fn-served-step-counted-result-is-step-of-consumed-prefix))
            :use ((:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                  (:instance fn-served-step-counted-consumed-is-bounded)
                  (:instance fn-served-step-of-append-any
                             (left (take (fn-served-counted-consumed
                                          (fn-served-step-counted conn octets fn-arena))
                                         octets))
                             (right (nthcdr (fn-served-counted-consumed
                                             (fn-served-step-counted conn octets fn-arena))
                                            octets)))
                  (:instance fn-served-tls-append-take-nthcdr
                             (n (fn-served-counted-consumed
                                 (fn-served-step-counted conn octets fn-arena)))
                             (xs octets)))))))

; KEYSTONE (PRF-213): the resumable step driven to exhaustion is one read of
; the whole input.  No hypothesis: the yield after a submission changes where
; the host re-enters, never what is framed or answered.
(defthm fn-served-drain-is-step
  (equal (fn-served-drain conn octets fn-arena)
         (fn-served-step conn octets fn-arena))
  :hints (("Goal" :induct (fn-served-drain conn octets fn-arena)
           :in-theory (e/d () (fn-served-step fn-served-step-counted)))
          ("Subgoal *1/2" :use ((:instance fn-served-step-splits-at-the-yield)))
          ("Subgoal *1/1" :use ((:instance fn-served-step-splits-at-the-yield)
                                (:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                                (:instance fn-served-step-counted-consumed-is-bounded)))))

(local
 (defthm fn-served-drain-run-is-run
   (equal (fn-served-drain-run conn chunks fn-arena)
          (fn-served-run conn chunks fn-arena))
   :hints (("Goal" :induct (fn-served-drain-run conn chunks fn-arena)
            :in-theory (e/d (fn-served-run) (fn-served-drain fn-served-step))))))

(local
 (defthm fn-served-run-is-the-concatenated-step-any
   (equal (fn-served-run conn chunks fn-arena)
          (fn-served-step conn (fn-served-concat chunks) fn-arena))
   :hints (("Goal" :induct (fn-served-run conn chunks fn-arena)
            :in-theory (e/d (fn-served-run fn-served-concat)
                            (fn-served-step))))))

; KEYSTONE (PRF-213, the boundary-independence theorem): the connection and
; the effect sequence the host loop reaches over a stream of reads are one
; read of their concatenation.  No hypothesis: the served fold ignores what
; it cannot frame and the close effect is on the closing edge, so the
; octet-list and invariant premises of fn-served-run-is-the-concatenated-step
; are not needed here.
(defthm fn-served-drain-run-is-the-concatenated-step
  (equal (fn-served-drain-run conn chunks fn-arena)
         (fn-served-step conn (fn-served-concat chunks) fn-arena))
  :hints (("Goal"
           :in-theory (disable fn-served-drain-run fn-served-run fn-served-step
                               fn-served-concat))))

; So two streams with the same octets consume the same commands and articles
; in the same order and answer them alike, wherever the network cut them and
; wherever a submission made a read yield.
(defthm fn-served-drain-run-is-boundary-independent
  (implies (equal (fn-served-concat one) (fn-served-concat two))
           (equal (fn-served-drain-run conn one fn-arena)
                  (fn-served-drain-run conn two fn-arena)))
  :hints (("Goal" :in-theory (disable fn-served-drain-run fn-served-step
                                      fn-served-concat))))

; KEYSTONE (PRF-213, no loss): the submissions the owner takes, one per
; yield, are every submission one read of the whole input carries, in order.
; Before PKT-600 the read took the first and dropped the rest.
(defthm fn-served-drain-takes-every-submission
  (implies (fn-served-connp conn)
           (equal (fn-served-drain-taken conn octets fn-arena)
                  (fn-served-submissions
                   (fn-served-result-effects (fn-served-step conn octets fn-arena)))))
  :hints (("Goal" :induct (fn-served-drain-taken conn octets fn-arena)
           :in-theory (e/d ()
                           (fn-served-step fn-served-step-counted fn-served-connp
                            fn-served-step-counted-carries-at-most-one-submission)))
          ("Subgoal *1/3" :use ((:instance fn-served-step-splits-at-the-yield)
                 (:instance fn-served-step-counted-carries-at-most-one-submission)
                 (:instance fn-served-submissions-of-at-most-one
                            (effects (fn-served-result-effects
                                      (fn-served-counted-result
                                       (fn-served-step-counted conn octets fn-arena)))))
                 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                 (:instance fn-served-step-counted-consumed-is-bounded)
                 (:instance fn-served-step-preserves-connp-of-any-input
                            (octets (take (fn-served-counted-consumed
                                           (fn-served-step-counted conn octets fn-arena))
                                          octets)))))
          ("Subgoal *1/2" :use ((:instance fn-served-step-splits-at-the-yield)
                 (:instance fn-served-step-counted-carries-at-most-one-submission)
                 (:instance fn-served-submissions-of-at-most-one
                            (effects (fn-served-result-effects
                                      (fn-served-counted-result
                                       (fn-served-step-counted conn octets fn-arena)))))
                 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                 (:instance fn-served-step-counted-consumed-is-bounded)
                 (:instance fn-served-step-preserves-connp-of-any-input
                            (octets (take (fn-served-counted-consumed
                                           (fn-served-step-counted conn octets fn-arena))
                                          octets)))))
          ("Subgoal *1/1" :use ((:instance fn-served-step-splits-at-the-yield)
                 (:instance fn-served-step-counted-carries-at-most-one-submission)
                 (:instance fn-served-submissions-of-at-most-one
                            (effects (fn-served-result-effects
                                      (fn-served-counted-result
                                       (fn-served-step-counted conn octets fn-arena)))))
                 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix)
                 (:instance fn-served-step-counted-consumed-is-bounded)
                 (:instance fn-served-step-preserves-connp-of-any-input
                            (octets (take (fn-served-counted-consumed
                                           (fn-served-step-counted conn octets fn-arena))
                                          octets)))))))

(in-theory (disable fn-served-drain fn-served-drain-run fn-served-drain-taken))
