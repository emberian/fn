; fn: the served step with the live node's invariant carried, not re-evaluated.
;
; Every served event tested the session recognizer (fn-auth-step-pinned's
; first branch, fn-peer-step-pinned's first branch) and every read tested it
; twice more (fn-own-finish-read's fn-own-conn-boundedp).  The peer session
; recognizer conjoins fn-node-statep of the node the owner swaps in
; (fn-own-conn-live-session), which is O(N^2) in the archive (the article
; list's duplicate check and the binding/pin cross-checks, books/node.lisp).
; A profile of STAT on the native owner at N = 120 attributed 91% of its time
; to those four evaluations (planning/evidence/served-path-cost-2026-09-24.md).
;
; The owner already carries that invariant: fn-own-relation conjoins
; fn-snt-relation, hence fn-sn-statep, hence fn-node-statep of the store's
; node.  This book is the served transition parameterized by a node `live'
; known to satisfy fn-node-statep.  Its only difference from the reference
; is the node conjunct of the session recognizer: `(or (equal node live)
; (fn-node-statep node))', which is fn-node-statep whenever `live' is one and
; costs one pointer comparison when the session holds that very node.  Each
; definition here is proved EQUAL to its reference under (fn-node-statep
; live), with no other hypothesis, so every theorem about the reference is a
; theorem about this one on those states.  No branch is dropped.
;
; The step functions also take `trie' and `arts', the owner view's
; Message-ID trie and the article list it indexes, and hand them to the peer
; arm (fn-pgc-peer-arm, books/peer-guard-carried.lisp), whose IHAVE/CHECK
; history test answers from the trie and whose guard names no node
; recognizer, so a peer event tests the session's node by the same pointer
; comparison a reader event does.  Their equations add the
; premise (fn-midx-correspondencep trie arts), which the owner carries
; (fn-scar-view-indexedp, books/owner-served-carried.lisp).

(in-package "ACL2")
(include-book "served-tls-prefix")
(include-book "peer-offer-indexed")
(include-book "peer-guard-carried")

(defun fn-scar-node-statep (node live)
  (declare (xargs :guard t))
  (or (equal node live) (fn-node-statep node)))

(defthm fn-scar-node-statep-is-node-statep
  (implies (fn-node-statep live)
           (equal (fn-scar-node-statep node live)
                  (fn-node-statep node)))
  :hints (("Goal" :in-theory (enable fn-scar-node-statep))))

(defun fn-scar-peer-sessionp (x live)
  (declare (xargs :guard t))
  (and (fn-peer-session-shapep x)
       (fn-post-sessionp (fn-peer-session-base x))
       (or (and (null (fn-peer-session-peer x))
                (or (and (null (fn-peer-session-node x))
                         (null (fn-peer-session-cfg x)))
                    (and (fn-scar-node-statep (fn-peer-session-node x) live)
                         (fn-cfgp (fn-peer-session-cfg x)))))
           (and (stringp (fn-peer-session-peer x))
                (fn-scar-node-statep (fn-peer-session-node x) live)
                (fn-cfgp (fn-peer-session-cfg x))))
       (fn-peer-transferp (fn-peer-session-transfer x))
       (natp (fn-peer-session-inflight x))))

(defthm fn-scar-peer-sessionp-is-peer-sessionp
  (implies (fn-node-statep live)
           (equal (fn-scar-peer-sessionp x live)
                  (fn-peer-sessionp x)))
  :hints (("Goal" :in-theory (e/d (fn-scar-peer-sessionp fn-peer-sessionp)
                                  (fn-scar-node-statep fn-node-statep)))))

(defun fn-scar-auth-sessionp (x live)
  (declare (xargs :guard t))
  (and (fn-auth-session-shapep x)
       (fn-scar-peer-sessionp (fn-auth-session-base x) live)
       (fn-auth-configp (fn-auth-session-config x))
       (or (null (fn-auth-session-pending x))
           (and (consp (fn-auth-session-pending x))
                (true-listp (fn-auth-session-pending x))
                (fn-nntp-printable-tokenp (fn-auth-session-pending x))))
       (or (null (fn-auth-session-subject x))
           (fn-prin-idp (fn-auth-session-subject x)))
       (booleanp (fn-auth-session-tlsp x))
       (booleanp (fn-auth-session-handshakingp x))))

(defthm fn-scar-auth-sessionp-is-auth-sessionp
  (implies (fn-node-statep live)
           (equal (fn-scar-auth-sessionp x live)
                  (fn-auth-sessionp x)))
  :hints (("Goal" :in-theory (e/d (fn-scar-auth-sessionp fn-auth-sessionp)
                                  (fn-scar-peer-sessionp fn-peer-sessionp
                                   fn-node-statep)))))

; The carried session test is the peer arm's guard: a peer session that
; passes it satisfies fn-pgc-peer-sessionp, whose node conjunct is gone.
(defthm fn-scar-peer-sessionp-gives-pgc-peer-sessionp
  (implies (and (fn-scar-peer-sessionp x live) (fn-peer-session-peer x))
           (fn-pgc-peer-sessionp x))
  :hints (("Goal" :in-theory (enable fn-scar-peer-sessionp
                                     fn-pgc-peer-sessionp))))

; A reader session (no peer) is served by the POST-composed step without a
; further recognizer.  A peer session goes to fn-pgc-peer-arm
; (books/peer-guard-carried.lisp), the reference's peer branches with the
; IHAVE/CHECK history test indexed and no session recognizer of its own: its
; guard is fn-pgc-peer-sessionp, which the carried test above implies, so the
; session's node is tested once per event by a pointer comparison against
; `live' and never by fn-node-statep when the session holds the owner's node.
(defun fn-scar-peer-step-pinned
    (ps live trie arts archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-scar-peer-sessionp)))))
  (cond
   ((not (fn-scar-peer-sessionp ps live)) (fn-post-make-result ps nil nil))
   ((null (fn-peer-session-peer ps))
    (fn-peer-delegate-pinned ps archive index verdicts config observation
                             injection wire-event))
   (t (fn-pgc-peer-arm ps trie arts archive index verdicts config
                       observation injection wire-event))))

(defthm fn-scar-peer-step-pinned-is-peer-step-pinned
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-peer-step-pinned ps live trie arts archive index verdicts config
                                            observation injection wire-event)
                  (fn-peer-step-pinned ps archive index verdicts config
                                       observation injection wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-scar-peer-step-pinned fn-peer-step-pinned)
                                  (fn-midx-correspondencep fn-scar-peer-sessionp fn-peer-sessionp
                                   fn-node-statep fn-peer-delegate-pinned
                                   fn-peer-step fn-peer-command fn-pgc-peer-arm)))))

(defun fn-scar-auth-delegate-pinned
    (as live trie arts archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t))
  (let ((r (fn-scar-peer-step-pinned
            (fn-auth-session-base as) live trie arts archive index verdicts config
            observation injection wire-event)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r)
                         (fn-post-result-submission r))))

(defthm fn-scar-auth-delegate-pinned-is-auth-delegate-pinned
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config observation injection wire-event)
                  (fn-auth-delegate-pinned as archive index verdicts config observation injection wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-scar-auth-delegate-pinned fn-auth-delegate-pinned)
                                  (fn-midx-correspondencep fn-scar-peer-step-pinned fn-peer-step-pinned fn-node-statep)))))

(defun fn-scar-auth-step-pinned
    (as live trie arts archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t))
  (cond
   ((not (fn-scar-auth-sessionp as live)) (fn-post-make-result as nil nil))
   ((fn-auth-tls-eventp wire-event) (fn-auth-tls-established as))
   ((fn-auth-session-handshakingp as) (fn-post-make-result as nil nil))
   ((and (consp wire-event)
         (equal (car wire-event) :command)
         (consp (cdr wire-event))
         (null (cdr (cdr wire-event)))
         (fn-nntp-command-inputp (car (cdr wire-event))))
    (let ((tokens (fn-nntp-tokenize (car (cdr wire-event)))))
      (if (and (consp tokens)
               (fn-nntp-keyword-tokenp (car tokens))
               (fn-nntp-command-arguments-at-mostp tokens))
          (let ((r (fn-auth-command as config (car tokens) (cdr tokens))))
            (if r r
              (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config
                                        observation injection wire-event)))
        (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config observation
                                  injection wire-event))))
   (t (fn-scar-auth-delegate-pinned as live trie arts archive index verdicts config observation
                                injection wire-event))))

(defthm fn-scar-auth-step-pinned-is-auth-step-pinned
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-auth-step-pinned as live trie arts archive index verdicts config observation injection wire-event)
                  (fn-auth-step-pinned as archive index verdicts config observation injection wire-event)))
  :hints (("Goal" :in-theory (e/d (fn-scar-auth-step-pinned fn-auth-step-pinned)
                                  (fn-midx-correspondencep fn-scar-auth-sessionp fn-auth-sessionp fn-scar-auth-delegate-pinned fn-auth-delegate-pinned fn-auth-command fn-auth-tls-established fn-node-statep)))))

(defun fn-scar-dispatch (conn event live trie arts)
  (declare (xargs :guard t))
  (let* ((r (fn-scar-auth-step-pinned (fn-served-conn-session conn) live trie arts
                               (fn-served-conn-archive conn)
                               (fn-served-conn-pinned-index conn)
                               (fn-served-conn-verdicts conn)
                               (fn-served-conn-config conn)
                               (fn-served-conn-observation conn)
                               (fn-served-conn-injection conn)
                               event))
         (effects (fn-post-result-effects r))
         (submission (fn-post-result-submission r))
         (wire (fn-served-conn-wire conn))
         (wire2 (if (fn-post-offeredp effects)
                    (fn-wire-result-state
                     (fn-wire-begin-article-with-line-limit
                      wire (fn-wire-article-line-limit wire)))
                  wire)))
    (fn-served-make-result
     (fn-served-make-conn-group-indexed wire2 (fn-post-result-session r)
                          (fn-served-conn-archive conn)
                          (fn-served-conn-config conn)
                          (fn-served-conn-observation conn)
                          (fn-served-conn-injection conn)
                          (fn-served-conn-verdicts conn)
                          (fn-served-conn-index conn)
                          (fn-served-conn-group-index conn))
     (mbe :logic (append effects
                         (if submission
                             (list (fn-served-submit-effect submission))
                           nil))
          :exec (fn-ag-append effects
                              (if submission
                                  (list (fn-served-submit-effect submission))
                                nil))))))

(defthm fn-scar-dispatch-is-served-dispatch
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-dispatch conn event live trie arts)
                  (fn-served-dispatch conn event)))
  :hints (("Goal" :in-theory (e/d (fn-scar-dispatch fn-served-dispatch)
                                  (fn-midx-correspondencep fn-scar-auth-step-pinned fn-auth-step-pinned fn-node-statep)))))

(defun fn-scar-dispatch-events (conn events live trie arts)
  (declare (xargs :guard t))
  (if (consp events)
      (let* ((here (fn-scar-dispatch conn (car events) live trie arts))
             (tail (fn-scar-dispatch-events (fn-served-result-conn here)
                                              (cdr events) live trie arts)))
        (fn-served-make-result
         (fn-served-result-conn tail)
         (mbe :logic (append (fn-served-result-effects here)
                             (fn-served-result-effects tail))
              :exec (fn-ag-append (fn-served-result-effects here)
                                  (fn-served-result-effects tail)))))
    (fn-served-make-result conn nil)))

(defthm fn-scar-dispatch-events-is-served-dispatch-events
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-dispatch-events conn events live trie arts)
                  (fn-served-dispatch-events conn events)))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (e/d (fn-scar-dispatch-events fn-served-dispatch-events)
                           (fn-midx-correspondencep fn-scar-dispatch fn-served-dispatch fn-node-statep)))))

; The wire half of one carried dispatch is the reference's, whatever `live'
; is: the guard of the carried fold needs it without the node premise.
(defthm fn-scar-dispatch-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scar-dispatch conn event live trie arts)))))
  :hints (("Goal"
           :in-theory (disable fn-wire-fast-statep
                               fn-wire-begin-article-with-line-limit
                               fn-wire-article-line-limit
                               fn-scar-auth-step-pinned fn-post-offeredp
                               fn-wire-begin-article-with-line-limit-preserves-fast-statep)
           :use ((:instance fn-wire-begin-article-with-line-limit-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn))
                            (article-line-limit
                             (fn-wire-article-line-limit
                              (fn-served-conn-wire conn))))))))

(defthm fn-scar-dispatch-events-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scar-dispatch-events conn events live trie arts)))))
  :hints (("Goal" :induct (fn-scar-dispatch-events conn events live trie arts)
           :in-theory (disable fn-scar-dispatch fn-wire-fast-statep))))

(defun fn-scar-feed-byte (conn byte live trie arts)
  (declare (xargs :guard (fn-wire-fast-statep (fn-served-conn-wire conn))))
  (let ((fed (fn-wire-feed-byte (fn-served-conn-wire conn) byte)))
    (fn-scar-dispatch-events
     (fn-served-make-conn-group-indexed (fn-wire-result-state fed)
                          (fn-served-conn-session conn)
                          (fn-served-conn-archive conn)
                          (fn-served-conn-config conn)
                          (fn-served-conn-observation conn)
                          (fn-served-conn-injection conn)
                          (fn-served-conn-verdicts conn)
                          (fn-served-conn-index conn)
                          (fn-served-conn-group-index conn))
     (fn-wire-result-events fed) live trie arts)))

(defthm fn-scar-feed-byte-is-served-feed-byte
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-feed-byte conn byte live trie arts)
                  (fn-served-feed-byte conn byte)))
  :hints (("Goal" :in-theory (e/d (fn-scar-feed-byte fn-served-feed-byte)
                                  (fn-midx-correspondencep fn-scar-dispatch-events fn-served-dispatch-events fn-wire-feed-byte fn-node-statep)))))


(defthm fn-scar-feed-byte-preserves-fast-statep
  (implies (fn-wire-fast-statep (fn-served-conn-wire conn))
           (fn-wire-fast-statep
            (fn-served-conn-wire
             (fn-served-result-conn (fn-scar-feed-byte conn byte live trie arts)))))
  :hints (("Goal"
           :in-theory (e/d (fn-scar-feed-byte)
                           (fn-served-feed-byte-preserves-fast-statep
                            fn-served-feed-byte fn-scar-dispatch-events
                            fn-wire-feed-byte fn-wire-fast-statep))
           :use ((:instance fn-wire-feed-byte-preserves-fast-statep
                            (wire-state (fn-served-conn-wire conn)))
                 (:instance fn-scar-dispatch-events-preserves-fast-statep
                            (conn
                             (fn-served-make-conn-group-indexed
                              (fn-wire-result-state
                               (fn-wire-feed-byte
                                (fn-served-conn-wire conn) byte))
                              (fn-served-conn-session conn)
                              (fn-served-conn-archive conn)
                              (fn-served-conn-config conn)
                              (fn-served-conn-observation conn)
                              (fn-served-conn-injection conn)
                              (fn-served-conn-verdicts conn)
                              (fn-served-conn-index conn)
                              (fn-served-conn-group-index conn)))
                            (events
                             (fn-wire-result-events
                              (fn-wire-feed-byte
                               (fn-served-conn-wire conn) byte))))))))

(defun fn-scar-feed-counted (conn octets live trie arts)
  (declare (xargs :guard (fn-wire-fast-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-tls-handshakingp conn))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (let* ((here (fn-scar-feed-byte conn (car octets) live trie arts))
           (tail (fn-scar-feed-counted
                  (fn-served-result-conn here) (cdr octets) live trie arts))
           (tail-result (fn-served-counted-result tail)))
      (fn-served-counted-make
       (+ 1 (fn-served-counted-consumed tail))
      (fn-served-make-result
        (fn-served-result-conn tail-result)
        (mbe :logic (append (fn-served-result-effects here)
                            (fn-served-result-effects tail-result))
             :exec (fn-ag-append (fn-served-result-effects here)
                                 (fn-served-result-effects tail-result))))))))

(defthm fn-scar-feed-counted-consumed-is-natural
  (natp (fn-served-counted-consumed
         (fn-scar-feed-counted conn octets live trie arts)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-scar-feed-counted conn octets live trie arts)
           :in-theory (e/d (fn-scar-feed-counted
                            fn-served-counted-make
                            fn-served-counted-consumed)
                           (fn-scar-feed-byte)))))

(verify-guards fn-scar-feed-counted
  :hints (("Goal"
           :in-theory (disable fn-scar-feed-byte fn-wire-fast-statep
                               fn-served-counted-consumed
                               fn-scar-feed-byte-preserves-fast-statep)
           :use ((:instance fn-scar-feed-byte-preserves-fast-statep
                            (byte (car octets)))))))

(defthm fn-scar-feed-counted-is-served-feed-counted
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-feed-counted conn octets live trie arts)
                  (fn-served-feed-counted conn octets)))
  :hints (("Goal" :induct (fn-served-feed-counted conn octets)
           :in-theory (e/d (fn-scar-feed-counted fn-served-feed-counted)
                           (fn-midx-correspondencep fn-scar-feed-byte fn-served-feed-byte
                            fn-node-statep)))))

(defun fn-scar-step-counted-core (conn octets live trie arts)
  (declare (xargs :guard
                  (fn-wire-fast-statep (fn-served-conn-wire conn))))
  (let* ((wire (fn-served-conn-wire conn))
         (fed (fn-scar-feed-counted conn octets live trie arts))
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

(defthm fn-scar-step-counted-core-is-served-step-counted-core
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-step-counted-core conn octets live trie arts)
                  (fn-served-step-counted-core conn octets)))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-counted-core fn-served-step-counted-core)
                                  (fn-midx-correspondencep fn-scar-feed-counted fn-served-feed-counted fn-node-statep)))))

(defun fn-scar-step-counted-fast (conn octets live trie arts)
  (declare (xargs :guard t))
  (if (not (fn-wire-fast-statep (fn-served-conn-wire conn)))
      (fn-served-counted-make 0 (fn-served-make-result conn nil))
    (fn-scar-step-counted-core conn octets live trie arts)))


(defthm fn-scar-step-counted-fast-is-served-step-counted-fast
  (implies (and (fn-node-statep live)
                (fn-midx-correspondencep trie arts))
           (equal (fn-scar-step-counted-fast conn octets live trie arts)
                  (fn-served-step-counted-fast conn octets)))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-counted-fast fn-served-step-counted-fast)
                                  (fn-midx-correspondencep fn-scar-step-counted-core fn-served-step-counted-core fn-node-statep)))))

; Withdraw the carried definitions: a book above reaches them through the
; equations, not by opening them.
(in-theory (disable fn-scar-node-statep fn-scar-peer-sessionp
                    fn-scar-auth-sessionp fn-scar-peer-step-pinned
                    fn-scar-auth-delegate-pinned fn-scar-auth-step-pinned
                    fn-scar-dispatch fn-scar-dispatch-events fn-scar-feed-byte
                    fn-scar-feed-counted fn-scar-step-counted-core
                    fn-scar-step-counted-fast))
