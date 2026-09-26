;; PKT-175 / PRF-168 (NNT-036): the served HDR :fn-enrollment reply stated
;; over the function the host calls.
;;
;; Host path (reader), as for HDR :fn-verified (books/owner-verdict-read) and
;; HDR :fn-control (books/owner-control-read): host/native/owner.lisp
;; (fnn-owner-action 'fn-owner-chunk ...) runs host/owner-host.lisp
;; fn-owner-chunk, that is fn-ocfg-read-tls-prefix, equal to fn-ocfg-read by
;; fn-ocfg-read-tls-prefix-is-full-read (books/owner-tls-prefix), whose reply
;; is (car (fn-own-read ...)).  fn-own-read builds the served connection from
;; the owner connection -- its pinned archive, verdicts, Message-ID trie,
;; buckets and control pin -- and runs the byte fold fn-served-step down to
;; the pinned dispatcher fn-nntp-archive-command-pinned (books/nntp.lisp),
;; whose :FN-ENROLLMENT arm is fn-nntp-enrollment-hdr-response
;; (books/nntp-enrollment.lisp).
;;
;; The keystone: one read framing `HDR :fn-enrollment <msgid>' answers one
;; line whose item is the enrollment, in the connection's pinned keyring
;; view, of the principal the connection's pinned verdict for that
;; Message-ID names.  The keyring view is the one the view was committed
;; with (fn-own-view-keyring, set by fn-own-refresh from the idle Store's
;; fn-sn-keyring-snapshots; fn-own-view-control pins it); the second theorem
;; closes that chain for a reader opened after a durable completion.
;;
;; The verdict is not re-evaluated and the current Store is not consulted on
;; the served path: the historical verdict, the current enrollment, historical
;; local acceptance and current administrative authority stay separate facts
;; (planning/handoff-2026-09-25-fable-mandate.md section 5.4).
(in-package "ACL2")
(include-book "owner-control-read")

;; The dispatcher arm: over a Message-ID the pinned trie holds, the pinned
;; dispatcher answers the enrollment line.
(defthm fn-nntp-hdr-fn-enrollment-is-the-pinned-enrollment
  (let ((msgid (fn-nntp-token-string (cadr args))))
    (implies (and (fn-nntp-keywordp keyword "HDR")
                  (consp args) (consp (cdr args)) (null (cddr args))
                  (fn-nntp-keywordp (car args) ":FN-ENROLLMENT")
                  (fn-nntp-message-id-tokenp (cadr args))
                  (fn-octet-listp (cadr args))
                  (consp (fn-midx-lookup msgid (fn-gidx-pin-trie index))))
             (equal (fn-nntp-archive-command-pinned
                     session archive index verdicts env keyword args)
                    (fn-nntp-multi
                     session (fn-nntp-hdr-initial nil)
                     (list (fn-nntp-hdr-line
                            (fn-nntp-decimal-field 0)
                            (fn-enr-item (fn-stx-reader-lookup msgid verdicts)
                                         (fn-gidx-pin-control index))))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-keywordp)
                                  (fn-nntp-single fn-nntp-multi fn-nntp-upcase-keyword
                                   fn-enr-item fn-midx-lookup fn-stx-reader-lookup
                                   fn-nntp-hdr-line fn-nntp-decimal-field
                                   fn-nntp-string-octets fn-gidx-pin-control
                                   fn-gidx-pin-trie fn-nntp-token-string
                                   fn-nntp-message-id-tokenp fn-octet-listp))
           :use ((:instance fn-nntp-enrollment-hdr-response-is-the-pinned-enrollment)))))

;; PRF-168 KEYSTONE over the host-called reader port (host/owner-host.lisp
;; fn-owner-chunk).  Uses fn-own-read-archive-command-is-the-pinned-dispatcher
;; (books/owner-control-read) as a lemma.
(defthm fn-own-read-hdr-fn-enrollment-is-the-pinned-enrollment
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-own-conn-live-session o conn))
         (ns (fn-post-session-base
              (fn-peer-session-base (fn-auth-session-base as))))
         (tokens (fn-nntp-tokenize line))
         (msgid (fn-nntp-token-string (caddr tokens))))
    (implies (and conn
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-octl-reader-hyps as tokens line)
                  (consp (cddr tokens)) (null (cdddr tokens))
                  (fn-nntp-keywordp (car tokens) "HDR")
                  (fn-nntp-keywordp (cadr tokens) ":FN-ENROLLMENT")
                  (fn-nntp-message-id-tokenp (caddr tokens))
                  (fn-octet-listp (caddr tokens))
                  (fn-own-conn-group-index conn)
                  (consp (fn-midx-lookup msgid (fn-own-conn-index conn))))
             (equal (car (fn-own-read o id (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-multi
                      ns (fn-nntp-hdr-initial nil)
                      (list (fn-nntp-hdr-line
                             (fn-nntp-decimal-field 0)
                             (fn-enr-item
                              (fn-stx-reader-lookup msgid (fn-own-conn-verdicts conn))
                              (fn-own-conn-control conn)))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-own-read-archive-command-is-the-pinned-dispatcher)
                 (:instance fn-octl-pinned-index-of-served-conn
                  (conn (fn-own-find-conn id (fn-own-conns o))))
                 (:instance fn-nntp-hdr-fn-enrollment-is-the-pinned-enrollment
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base
                              (fn-served-conn-session
                               (fn-octl-served-conn
                                o (fn-own-find-conn id (fn-own-conns o))))))))
                  (archive (fn-served-conn-archive
                            (fn-octl-served-conn
                             o (fn-own-find-conn id (fn-own-conns o)))))
                  (index (fn-served-conn-pinned-index
                          (fn-octl-served-conn
                           o (fn-own-find-conn id (fn-own-conns o)))))
                  (verdicts (fn-served-conn-verdicts
                             (fn-octl-served-conn
                              o (fn-own-find-conn id (fn-own-conns o)))))
                  (env (fn-nntp-env
                        (fn-served-conn-observation
                         (fn-octl-served-conn
                          o (fn-own-find-conn id (fn-own-conns o))))
                        nil
                        (and (fn-inj-config-allow
                              (fn-served-conn-config
                               (fn-octl-served-conn
                                o (fn-own-find-conn id (fn-own-conns o)))))
                             t)))
                  (keyword (car (fn-nntp-tokenize line)))
                  (args (cdr (fn-nntp-tokenize line))))
                 (:instance fn-auth-fold-enrollment-hdr-response-has-no-offer
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base
                              (fn-own-conn-live-session
                               o (fn-own-find-conn id (fn-own-conns o)))))))
                  (archive (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o))))
                  (index (fn-served-conn-pinned-index
                          (fn-octl-served-conn
                           o (fn-own-find-conn id (fn-own-conns o)))))
                  (verdicts (fn-own-conn-verdicts (fn-own-find-conn id (fn-own-conns o))))
                  (args (cdr (fn-nntp-tokenize line)))))
           :in-theory (e/d (fn-octl-reply fn-octl-served-conn)
                           (fn-own-read-archive-command-is-the-pinned-dispatcher
                            fn-octl-pinned-index-of-served-conn
                            fn-nntp-hdr-fn-enrollment-is-the-pinned-enrollment
                            fn-auth-fold-enrollment-hdr-response-has-no-offer
                            fn-nntp-archive-command-pinned
                            fn-served-conn-pinned-index
                            fn-own-read fn-served-step fn-own-conn-live-session
                            fn-own-conn-wire fn-own-conn-archive fn-own-conn-config
                            fn-own-conn-observation fn-own-conn-verdicts
                            fn-own-conn-index fn-own-conn-group-index
                            fn-own-conn-control fn-own-conn-session fn-own-find-conn
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-multi fn-enr-item fn-stx-reader-lookup
                            fn-midx-lookup fn-nntp-hdr-line
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-message-id-tokenp
                            fn-nntp-archive-keywordp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp fn-octet-listp)))))

;; The keyring view a fresh reader pins is the Store's after the durable
;; completion it was opened after: with fn-hls-finish-identity-current-
;; enrollment (books/hybrid-lifecycle-store-invariants) this closes the chain
;; from a durable kind-3 enrollment or revocation to the served item.
;; Host lines: host/owner-host.lisp fn-owner-finish runs
;; (fn-owner-step (list :complete) state); fn-owner-open runs fn-ocfg-open.
(defthm fn-own-reader-opened-after-completion-pins-the-finished-keyring
  (implies (and (fn-sn-completion-enabledp (fn-own-store o))
                (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o))))
           (let* ((o2 (cdr (fn-own-open (fn-own-step o '(:complete)) acfg)))
                  (conn (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o2))))
             (and conn
                  (fn-enr-pin-has-keyring-p (fn-own-conn-control conn))
                  (equal (fn-enr-pin-keyring (fn-own-conn-control conn))
                         (fn-sn-keyring-snapshots
                          (fn-sn-finish (fn-own-store o)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-snt-finish-image (s (fn-own-store o))))
           :in-theory (e/d (fn-own-step fn-own-complete fn-own-refresh
                            fn-own-open fn-own-store-idlep fn-snt-idle-phasep)
                           (fn-snt-finish-image fn-sn-finish fn-sn-completion-enabledp
                            fn-own-view-make-group-indexed fn-own-conn-make-group-indexed
                            fn-own-conn-control fn-own-view-control
                            fn-enr-pin-has-keyring-p fn-enr-pin-keyring
                            fn-served-open-group-indexed fn-midx-refresh
                            fn-gidx-build)))))
