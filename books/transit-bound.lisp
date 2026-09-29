; fn: a transit article is bounded by the operator's profile before its
; verdict (fuzz-nntp F2, 2026-09-27; AGENTS.md "Bound the work and allocation
; one request may cause before consuming it"; D27).
;
; A peer that streamed a TAKETHIS article (or IHAVE's after 335) without end
; took the owner from 236 MiB to 3.94 GiB and was neither refused nor closed:
; the transit connection's wire body limit was the peer record's
; inbound-max-octets, which `peer add' fills with the record codec's payload
; ceiling (4 GiB), while a reader's POST met the profile's article bound A.
; books/owner.lisp `fn-own-peer-body-limit' is now the smaller of the two,
; and books/peer-inbound.lisp `fn-peer-transfer-unreceived-effects' refuses
; the cut article by name (437 / 439) and closes.
;
; The chain, host entry first:
;   host/native/owner.lisp accept -> fn-owner-open-peer (host/owner-host.lisp)
;     -> fn-own-open-peer: the connection's wire opens with body limit
;        fn-own-peer-body-limit <= fn-own-body-limit, which after
;        fn-osb-install (the profile install every run path performs) is the
;        profile's A (fn-tb-open-peer-body-limit-is-the-profile-bound).
;   every read: fn-own-read -> fn-served-step.  The step never changes the
;     wire's body limit (fn-tb-served-step-keeps-the-body-limit) and keeps
;     fn-wire-statep (fn-served-step-preserves-connp), whose conjunct is
;     retained body octets <= body limit; the retained partial line is
;     within the line limit, which in article mode is the body limit plus
;     one (fn-wire-article-line-limit).
;   KEYSTONE fn-tb-served-run-retains-at-most-the-body-limit: however the
;     peer's octets are cut into reads, the completed lines a connection
;     holds before its verdict never exceed the limit it was opened with,
;     and everything it holds (fn-wire-held-octets: the completed lines and
;     the current line) never exceeds that limit and the line ceiling.
;
; The representation's cost per octet: since lane chunked-body (B6) the wire
; holds an article in flight as packed blocks (books/body-chunks.lisp), about
; one octet of heap an octet, where the octet lists it replaced cost sixteen.

(in-package "ACL2")
(include-book "owner-served-bound")

; -----------------------------------------------------------------------------
; The wire never changes its body limit.

(defthm fn-tb-wire-close-keeps-the-body-limit
  (equal (fn-wire-state-body-limit
          (fn-wire-result-state (fn-wire-close w reason)))
         (fn-wire-state-body-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-close))))

(defthm fn-tb-wire-after-line-keeps-the-body-limit
  (equal (fn-wire-state-body-limit
          (fn-wire-result-state (fn-wire-after-line w line)))
         (fn-wire-state-body-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-after-line))))

(defthm fn-tb-wire-feed-byte-keeps-the-body-limit
  (equal (fn-wire-state-body-limit
          (fn-wire-result-state (fn-wire-feed-byte w byte)))
         (fn-wire-state-body-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-take-octet))))

(defthm fn-tb-wire-begin-article-keeps-the-body-limit
  (equal (fn-wire-state-body-limit
          (fn-wire-result-state
           (fn-wire-begin-article-with-line-limit w article-line-limit)))
         (fn-wire-state-body-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-begin-article-with-line-limit))))
;
; -----------------------------------------------------------------------------
; Nor does the served step: the dispatcher changes the wire only to enter
; article mode, which keeps the limit.

(defmacro fn-tb-limit (conn)
  `(fn-wire-state-body-limit (fn-served-conn-wire ,conn)))

(defthm fn-tb-dispatch-core-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-dispatch-core conn event fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch-core)
                                  (fn-auth-step-pinned fn-post-offeredp
                                   fn-wire-begin-article-with-line-limit
                                   fn-wire-article-line-limit)))))

(defthm fn-tb-dispatch-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-dispatch conn event fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch)
                                  (fn-served-dispatch-core
                                   fn-served-selectedp fn-served-repin)))))

(defthm fn-tb-dispatch-events-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-dispatch-events conn events fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events fn-arena)
           :in-theory (e/d (fn-served-dispatch-events)
                           (fn-served-dispatch)))))

(defthm fn-tb-feed-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-feed conn octets fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :induct (fn-served-feed conn octets fn-arena)
           :in-theory (e/d (fn-served-feed fn-served-feed-byte)
                           (fn-served-dispatch-events fn-wire-feed-byte
                            fn-served-closed-wirep fn-served-haltedp)))))

(defthm fn-tb-served-step-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-step conn octets fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :in-theory (e/d (fn-served-step)
                                  (fn-served-feed fn-wire-statep
                                   fn-served-closed-wirep)))))

(defthm fn-tb-served-run-keeps-the-body-limit
  (equal (fn-tb-limit (fn-served-result-conn
                       (fn-served-run conn chunks fn-arena)))
         (fn-tb-limit conn))
  :hints (("Goal" :induct (fn-served-run conn chunks fn-arena)
           :in-theory (e/d (fn-served-run) (fn-served-step)))))
;
; The retained partial line: its ceiling is the line limit, which only the
; dispatcher's switch to article mode moves, and only to the body limit plus
; one.  So a connection's line ceiling never grows past the larger of the
; one it opened with and the body limit plus one.

(defun fn-tb-wire-ceiling (w)
  (declare (xargs :guard t))
  (max (nfix (fn-wire-state-line-limit w))
       (+ 1 (nfix (fn-wire-state-body-limit w)))))

(defmacro fn-tb-line-ceiling (conn)
  `(fn-tb-wire-ceiling (fn-served-conn-wire ,conn)))

(defthm fn-tb-wire-close-keeps-the-line-limit
  (equal (fn-wire-state-line-limit
          (fn-wire-result-state (fn-wire-close w reason)))
         (fn-wire-state-line-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-close))))

(defthm fn-tb-wire-after-line-keeps-the-line-limit
  (equal (fn-wire-state-line-limit
          (fn-wire-result-state (fn-wire-after-line w line)))
         (fn-wire-state-line-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-after-line))))

(defthm fn-tb-wire-feed-byte-keeps-the-line-limit
  (equal (fn-wire-state-line-limit
          (fn-wire-result-state (fn-wire-feed-byte w byte)))
         (fn-wire-state-line-limit w))
  :hints (("Goal" :in-theory (enable fn-wire-feed-byte fn-wire-take-octet))))

(defthm fn-tb-dispatch-core-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-dispatch-core conn event fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch-core
                                   fn-wire-begin-article-with-line-limit
                                   fn-wire-article-line-limit)
                                  (fn-auth-step-pinned fn-post-offeredp
                                   fn-wire-begin-article-admissiblep)))))

(defthm fn-tb-dispatch-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-dispatch conn event fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch)
                                  (fn-served-dispatch-core fn-tb-wire-ceiling
                                   fn-served-selectedp fn-served-repin))
           :use ((:instance fn-tb-dispatch-core-line-ceiling)
                 (:instance fn-tb-dispatch-core-line-ceiling
                            (conn (fn-served-repin conn)))))
))

(defthm fn-tb-dispatch-events-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-dispatch-events conn events fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-dispatch-events conn events fn-arena)
           :in-theory (e/d (fn-served-dispatch-events)
                           (fn-served-dispatch fn-tb-wire-ceiling)))))

(defthm fn-tb-wire-feed-byte-keeps-the-ceiling
  (equal (fn-tb-wire-ceiling (fn-wire-result-state (fn-wire-feed-byte w byte)))
         (fn-tb-wire-ceiling w))
  :hints (("Goal" :in-theory (e/d (fn-tb-wire-ceiling) (fn-wire-feed-byte)))))

(defthm fn-tb-feed-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-feed conn octets fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-feed conn octets fn-arena)
           :in-theory (e/d (fn-served-feed fn-served-feed-byte)
                           (fn-served-dispatch-events fn-wire-feed-byte
                            fn-tb-wire-ceiling
                            fn-served-closed-wirep fn-served-haltedp)))))

(defthm fn-tb-served-step-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-step conn octets fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-served-step)
                                  (fn-served-feed fn-wire-statep fn-tb-wire-ceiling
                                   fn-served-closed-wirep)))))

(defthm fn-tb-served-run-line-ceiling
  (<= (fn-tb-line-ceiling (fn-served-result-conn
                           (fn-served-run conn chunks fn-arena)))
      (fn-tb-line-ceiling conn))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-served-run conn chunks fn-arena)
           :in-theory (e/d (fn-served-run) (fn-served-step fn-tb-wire-ceiling)))))

;; The wire invariant (whose conjunct is retained body <= body limit) holds
;; after every read, whatever the octets: fn-served-feed-preserves-wire-statep
;; lifted to the step and the run.
(defthm fn-tb-served-step-preserves-wire-statep
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep (fn-served-conn-wire
                            (fn-served-result-conn (fn-served-step conn octets fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-served-step)
                                  (fn-served-feed fn-wire-statep
                                   fn-served-closed-wirep)))))

(defthm fn-tb-served-run-preserves-wire-statep
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (fn-wire-statep (fn-served-conn-wire
                            (fn-served-result-conn (fn-served-run conn chunks fn-arena)))))
  :hints (("Goal" :induct (fn-served-run conn chunks fn-arena)
           :in-theory (e/d (fn-served-run) (fn-served-step fn-wire-statep)))))

; KEYSTONE.  The subject is fn-served-run, which by
; fn-served-run-is-the-concatenated-step is fn-served-step over the
; concatenated reads; books/owner.lisp fn-own-read calls fn-served-step once
; per socket read.  However a peer's octets are cut into reads, and whatever
; they are, what the connection retains of an article in flight -- the
; completed lines and the partial one -- is within the body limit it opened
; with and the line ceiling: nothing is retained past them, the wire closes
; instead.  The one hypothesis is the wire invariant every opened connection
; starts with (fn-wire-initial-state-is-state).
(defthm fn-tb-served-run-retains-at-most-the-body-limit
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (let ((w (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-run conn chunks fn-arena)))))
             (and (<= (fn-wire-state-body-size w)
                      (fn-tb-limit conn))
                  (<= (fn-wire-held-octets w)
                      (+ (fn-tb-limit conn) (fn-tb-line-ceiling conn))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-tb-wire-ceiling)
                           (fn-served-run fn-wire-statep
                            fn-tb-served-run-line-ceiling
                            fn-tb-served-run-preserves-wire-statep
                            fn-wire-statep-held-octets-bound
                            fn-wire-held-octets))
           :use ((:instance fn-tb-served-run-preserves-wire-statep)
                 (:instance fn-tb-served-run-line-ceiling)
                 (:instance fn-tb-served-run-keeps-the-body-limit)
                 (:instance fn-wire-statep
                            (x (fn-served-conn-wire
                                (fn-served-result-conn
                                 (fn-served-run conn chunks fn-arena)))))
                 (:instance fn-wire-statep-held-octets-bound
                            (x (fn-served-conn-wire
                                (fn-served-result-conn
                                 (fn-served-run conn chunks fn-arena)))))))))

; KEYSTONE (lane chunked-body-2, B6b).  Mid-article the connection holds at
; most the body limit and one octet -- the completed lines and the current
; one together (books/wire.lisp fn-wire-line-room closes :body-overlimit at
; the octet that dooms the line).  This is the wire's term of the article
; credit (books/heap-store-figure.lisp fn-heap-article-reserve-octets).
(defthm fn-tb-served-run-holds-at-most-the-body-limit-mid-article
  (implies (fn-wire-statep (fn-served-conn-wire conn))
           (let ((w (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-run conn chunks fn-arena)))))
             (implies (equal (fn-wire-state-mode w) :article)
                      (<= (fn-wire-held-octets w)
                          (+ 1 (fn-wire-state-body-limit w))))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable fn-served-run fn-wire-statep fn-wire-held-octets
                               fn-tb-served-run-preserves-wire-statep
                               fn-wire-statep-article-holds-at-most-the-body-limit)
           :use ((:instance fn-tb-served-run-preserves-wire-statep)
                 (:instance fn-wire-statep-article-holds-at-most-the-body-limit
                            (x (fn-served-conn-wire
                                (fn-served-result-conn
                                 (fn-served-run conn chunks fn-arena)))))))))

; -----------------------------------------------------------------------------
; The limit a transit connection opens with.  The subject is fn-own-open-peer,
; which host/owner-host.lisp fn-owner-open-peer calls at accept for a
; connection the source address resolved to a peer record.

(defthm fn-tb-open-peer-wire-is-the-peer-body-limit
  (implies (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
           (equal (fn-own-conn-wire
                   (car (fn-own-conns (cdr (fn-own-open-peer o peer cfg acfg)))))
                  (fn-wire-initial-state
                   *fn-nntp-max-initial-line-octets*
                   (fn-own-peer-body-limit
                    o (fn-cfg-peer-find peer (fn-cfg-peers (fn-cfg-value cfg)))))))
  :hints (("Goal" :in-theory (e/d (fn-own-open-peer
                                   fn-served-open-peer-group-indexed
                                   fn-served-open-peer-indexed
                                   fn-served-pin-group-index
                                   fn-own-conn-wire)
                                  (fn-own-peer-body-limit
                                   fn-wire-initial-state
                                   fn-auth-open-session
                                   fn-served-greeting)))))

; KEYSTONE.  After the profile install every run path performs
; (fn-osb-install, host/owner-host.lisp fn-owner-install-profile), a transit
; connection opens with a body limit no larger than the profile's article
; bound A -- the bound a reader's POST meets -- whatever the peer record's
; inbound-max-octets says.  With fn-tb-served-run-retains-at-most-the-body-
; limit: no transit request retains more than A octets of article before its
; verdict.
(defthm fn-tb-open-peer-body-limit-is-the-profile-bound
  (implies (and (fn-bs-profile-admittedp profile)
                (equal o2 (mv-nth 1 (fn-osb-install o profile)))
                (< (len (fn-own-conns o2)) (nfix (fn-own-max-conns o2))))
           (<= (fn-wire-state-body-limit
                (fn-own-conn-wire
                 (car (fn-own-conns (cdr (fn-own-open-peer o2 peer cfg acfg))))))
               (fn-bs-profile-max-article-octets profile)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-wire-initial-state)
                                  (fn-own-open-peer fn-osb-install
                                   fn-own-peer-body-limit-is-within-the-profile-bound
                                   fn-osb-install-serves-the-profile-bound
                                   fn-bs-profile-admittedp
                                   fn-bs-profile-max-article-octets))
           :use ((:instance fn-osb-install-serves-the-profile-bound)
                 (:instance fn-own-peer-body-limit-is-within-the-profile-bound
                            (o o2)
                            (record (fn-cfg-peer-find
                                     peer (fn-cfg-peers (fn-cfg-value cfg)))))))))
