; Witnesses and teeth for books/owner-agent.lisp.
;
; The keystones and the host lines that call their subjects:
;
;   fn-oag-post-config-agent-is-the-path-identity
;     fn-oag-post-config, called by host/owner-host.lisp fn-owner-post-config
;   fn-oag-open-pins-the-owner-config
;     fn-ocfg-open, called by host/owner-host.lisp fn-owner-open
;   fn-oag-served-post-names-the-pinned-agent
;     fn-ocfg-read-tls-prefix, called by host/owner-host.lisp fn-owner-chunk
;
; Each has a reachable witness below, built the way the host builds it: a
; replayed configuration history whose second record is the
; `policy set path-identity' delta the native operator writes, an owner
; configured with fn-oag-post-config of it, a reader connection opened by
; fn-ocfg-open, and one socket read carrying POST and an article through
; fn-ocfg-read-tls-prefix.  Each hypothesis has a `must-fail' of the
; statement without it, original hints kept, and beside it the evaluated
; value that refutes the weaker statement -- except the served-invariant
; premise of the read keystone, for which no refuting value is known; see
; the note there.

(in-package "ACL2")
(include-book "../../books/owner-agent")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The configuration: the default record, then `policy set path-identity'.

(defconst *oat-identity* "hbox.ember.software")
(defconst *oat-record2*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-set-policy "path-identity" *oat-identity*))
                      *fn-cfg-default-stamp*))
(defconst *oat-cfg*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record* *oat-record2*)))
(defconst *oat-cfg-unset*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))

(assert-event (fn-cfgp *oat-cfg*))
(assert-event (equal (fn-oag-identity *oat-cfg*) *oat-identity*))
(assert-event (fn-oag-identity-setp *oat-cfg*))
(assert-event (not (fn-oag-identity-setp *oat-cfg-unset*)))
(assert-event (equal (fn-cnode-served-of *oat-cfg*) '("fn.letters" "fn.test")))

; -----------------------------------------------------------------------------
; Keystone 1: the installed agent is the path-identity.

(defconst *oat-post-config* (fn-oag-post-config *oat-cfg* 32768))
(assert-event (fn-inj-configp *oat-post-config*))
(assert-event (equal (fn-inj-config-agent *oat-post-config*)
                     (fn-record-string-octets *oat-identity*)))

; Without the slot the agent is the `.invalid' fallback, not the (empty)
; policy text.
(assert-event (equal (fn-inj-config-agent (fn-oag-post-config *oat-cfg-unset* 32768))
                     *fn-oag-unset-agent*))
(assert-event (not (equal (fn-inj-config-agent
                           (fn-oag-post-config *oat-cfg-unset* 32768))
                          (fn-record-string-octets
                           (fn-oag-identity *oat-cfg-unset*)))))
(must-fail
 (defthm oat-post-config-without-identity-setp
   (equal (fn-inj-config-agent (fn-oag-post-config *oat-cfg-unset* 32768))
          (fn-record-string-octets (fn-oag-identity *oat-cfg-unset*)))
   :hints (("Goal" :in-theory (disable fn-oag-identity)))))

; -----------------------------------------------------------------------------
; The owner, configured the way fn-owner-recover configures it, a clock
; observed, and one reader connection.

(defconst *oat-owner0*
  (fn-own-configure (fn-own-start (fn-sn-initial '("fn.letters" "fn.test")
                                                 (fn-cfg-capacity
                                                  (fn-cfg-value *oat-cfg*)))
                                  4)
                    *oat-post-config*))
(defconst *oat-oc0*
  (fn-ocfg-step (fn-ocfg-make *oat-owner0* *oat-cfg* nil nil)
                (list :observe (fn-clock-observation 5000000 1790000000000 0 t))))
(assert-event (fn-ocfg-statep *oat-oc0*))
(assert-event (not (fn-own-find-conn (fn-own-next-id (fn-ocfg-owner *oat-oc0*))
                                     (fn-own-conns (fn-ocfg-owner *oat-oc0*)))))

; Keystone 2: the new connection pins the owner's configuration, and so the
; path-identity (fn-oag-configured-open-pins-the-path-identity).
(defconst *oat-oc1* (cdr (fn-ocfg-open *oat-oc0* nil)))
(defconst *oat-id* (fn-own-next-id (fn-ocfg-owner *oat-oc0*)))
(defconst *oat-conn*
  (fn-own-find-conn *oat-id* (fn-own-conns (fn-ocfg-owner *oat-oc1*))))
(assert-event (consp *oat-conn*))
(assert-event (equal (fn-own-conn-config *oat-conn*) *oat-post-config*))
(assert-event (equal (fn-inj-config-agent (fn-own-conn-config *oat-conn*))
                     (fn-record-string-octets *oat-identity*)))

; Without freshness: an owner that already holds a connection under the next
; identifier, at its connection bound, refuses the open, and the connection
; found under that identifier is the old one with its own configuration.
(defconst *oat-other-config*
  (fn-inj-make-config t (fn-record-string-octets "other.example.invalid")
                      nil 32768))
(defconst *oat-stale-owner*
  (let ((o (fn-ocfg-owner *oat-oc1*)))
    (fn-own-make (fn-own-store o) (fn-own-view o)
                 (list (fn-own-conn-make 0 (fn-own-conn-version *oat-conn*)
                                         (fn-own-conn-frontier *oat-conn*)
                                         (fn-own-conn-wire *oat-conn*)
                                         (fn-own-conn-session *oat-conn*)
                                         (fn-own-conn-archive *oat-conn*)
                                         *oat-other-config*
                                         (fn-own-conn-observation *oat-conn*)))
                 0 1 (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                 (fn-own-facts o) *oat-post-config* (fn-own-queue o)
                 (fn-own-inflight o) (fn-own-feeds o))))
(defconst *oat-stale-oc* (fn-ocfg-make *oat-stale-owner* *oat-cfg* nil nil))
(defconst *oat-stale-found*
  (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner
                                     (cdr (fn-ocfg-open *oat-stale-oc* nil))))))
(assert-event (consp *oat-stale-found*))
(assert-event (not (equal (fn-own-conn-config *oat-stale-found*)
                          (fn-own-config *oat-stale-owner*))))
(must-fail
 (defthm oat-open-without-freshness
   (let* ((oc *oat-stale-oc*)
          (o (fn-ocfg-owner oc))
          (id (fn-own-next-id o))
          (conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner
                                                     (cdr (fn-ocfg-open oc nil)))))))
     (implies conn
              (equal (fn-own-conn-config conn) (fn-own-config o))))
   :hints (("Goal" :in-theory (e/d (fn-ocfg-open)
                                   (fn-own-open fn-own-reader-context
                                    fn-oag-own-open-pins-the-owner-config))
            :use ((:instance fn-oag-own-open-pins-the-owner-config
                             (o (fn-ocfg-owner *oat-stale-oc*))
                             (acfg nil)))))))

; -----------------------------------------------------------------------------
; Keystone 3: one socket read, POST and an article, through the transition
; host/owner-host.lisp fn-owner-chunk calls.

(defconst *oat-post-read*
  (append '(80 79 83 84 13 10)
          (fn-record-string-octets "From: poster@example.invalid")
          '(13 10)
          (fn-record-string-octets "Subject: hello")
          '(13 10)
          (fn-record-string-octets "Newsgroups: fn.letters")
          '(13 10 13 10)
          (fn-record-string-octets "Hello, news.")
          '(13 10 46 13 10)))
(defconst *oat-served-conn*
  (fn-own-tls-served-conn (fn-ocfg-owner *oat-oc1*) *oat-conn*))
(assert-event (fn-served-connp *oat-served-conn*))
(defconst *oat-read* (fn-ocfg-read-tls-prefix *oat-oc1* *oat-id* *oat-post-read*))
(defconst *oat-submission*
  (fn-served-submission (fn-own-tls-result-effects *oat-read*)))
(assert-event (fn-inj-injectedp *oat-submission*))
(assert-event
 (fn-inj-infixp (fn-inj-injection-info-line (fn-record-string-octets *oat-identity*))
                (fn-inj-decision-octets *oat-submission*)))
(assert-event
 (fn-inj-infixp (fn-record-string-octets "Injection-Info: hbox.ember.software")
                (fn-inj-decision-octets *oat-submission*)))
; The article is the one the owner queued for the writer.
(defun oat-queued-decisionp (d subs)
  (and (consp subs)
       (or (equal (fn-own-sub-decision (car subs)) d)
           (oat-queued-decisionp d (cdr subs)))))
(assert-event
 (oat-queued-decisionp *oat-submission*
                       (fn-own-queue (fn-ocfg-owner
                                      (fn-own-tls-result-owner *oat-read*)))))
; The Injection-Info names this node and no other agent.
(assert-event
 (not (fn-inj-infixp (fn-inj-injection-info-line *fn-oag-unset-agent*)
                     (fn-inj-decision-octets *oat-submission*))))

; The premise.  fn-served-connp of the connection's served state is the
; invariant fn-served-step carries (books/served.lisp) and the owner does not
; (books/owner-tls-prefix.lisp; PRF-006): the proof uses it to type the
; dispatcher's own effects and, through fn-served-step-counted-fast-is-
; reference, to equate the counted read with fn-served-step.  No value is
; known on which the conclusion fails without it -- every :submit the served
; path builds comes from fn-auth-step's result -- so this `must-fail' shows
; only that the proof needs the premise, not that the conclusion does, and it
; is the one general-claim tooth in this book for that reason.
(must-fail
 (defthm oat-read-without-served-invariant
   (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
     (fn-oag-names-agentp
      (fn-served-submission
       (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets)))
      (fn-inj-config-agent (fn-own-conn-config conn))))
   :hints (("Goal"
            :in-theory (e/d (fn-ocfg-read-tls-prefix fn-own-tls-make-result
                             fn-own-tls-result-effects)
                            (fn-own-read-tls-prefix fn-served-connp
                             fn-oag-names-agentp fn-served-submission
                             fn-own-tls-served-conn
                             fn-oag-read-tls-prefix-submission-names-the-pinned-agent))
            :use ((:instance fn-oag-read-tls-prefix-submission-names-the-pinned-agent
                             (o (fn-ocfg-owner oc))))))))
