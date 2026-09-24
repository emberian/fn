;; fn: the owner's re-pin after a durable POST, with the session invariant carried.
;
; host/owner-host.lisp fn-owner-outcome calls fn-own-outcome
; (books/owner.lisp), and on a :durable completion that re-pins the posting
; connection through fn-own-advance -> fn-own-advance-result, which tests the
; rebuilt connection with fn-own-conn-boundedp.  That conjoins
; fn-auth-sessionp -> fn-peer-sessionp -> fn-node-statep of the node the
; session carries: O(N^2) in the archive, 17 percent of POST CPU at N = 120
; (planning/evidence/commit-path-cost-2026-09-24.md, finding 2).
;
; The rebuilt session is the old one with only its innermost post session
; replaced: fn-auth-with-base over fn-peer-with-base keeps the peer, the node,
; the configuration, the transfer and the in-flight count.  The node tested
; is the very node the OLD session carried, and the old session is one the
; owner already holds: every open connection satisfies fn-own-conn-boundedp
; under both owner relations (fn-own-relation through fn-own-conns-okp,
; fn-ocl-relation through fn-ocl-conns-historyp), hence fn-auth-sessionp of
; its session.  So the served-path lane's carried recognizer
; (fn-scar-conn-boundedp, books/owner-served-carried.lisp) is passed the old
; session's node as `live': the node conjunct is one pointer comparison.
;
; Every definition below is its reference with fn-own-conn-boundedp replaced
; by fn-scar-conn-boundedp at that node, and is proved EQUAL to the reference
; when the connection found holds a session (fn-acar-conn-sessionp); the
; owner relations carry that premise, and the commit between the take and
; the outcome keeps the connections (fn-acar-own-finish-keeps-conns).
; host/owner-host.lisp fn-owner-outcome calls fn-acar-own-outcome.

(in-package "ACL2")
(include-book "owner-served-carried")
(include-book "owner-commit-carried")

; The node the connection's session carries.
(defun fn-acar-session-node (conn)
  (declare (xargs :guard t))
  (fn-peer-session-node (fn-auth-session-base (fn-own-conn-session conn))))

; The premise: the connection the id names, if any, holds a session.
(defun fn-acar-conn-sessionp (o id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (or (null conn)
        (fn-auth-sessionp (fn-own-conn-session conn)))))

; -----------------------------------------------------------------------------
; The recognizer of a rebuilt session, at the old session's node.

(local
 (defthm fn-acar-peer-with-base-fields
   (and (equal (fn-peer-session-base (fn-peer-with-base ps b)) b)
        (equal (fn-peer-session-peer (fn-peer-with-base ps b))
               (fn-peer-session-peer ps))
        (equal (fn-peer-session-node (fn-peer-with-base ps b))
               (fn-peer-session-node ps))
        (equal (fn-peer-session-cfg (fn-peer-with-base ps b))
               (fn-peer-session-cfg ps))
        (equal (fn-peer-session-transfer (fn-peer-with-base ps b))
               (fn-peer-session-transfer ps))
        (equal (fn-peer-session-inflight (fn-peer-with-base ps b))
               (fn-peer-session-inflight ps))
        (fn-peer-session-shapep (fn-peer-with-base ps b)))
   :hints (("Goal" :in-theory (enable fn-peer-with-base fn-peer-make-session
                                      fn-peer-session-base fn-peer-session-peer
                                      fn-peer-session-node fn-peer-session-cfg
                                      fn-peer-session-transfer
                                      fn-peer-session-inflight
                                      fn-peer-session-shapep)))))

(defthm fn-acar-scar-peer-sessionp-at-own-node
  (implies (fn-peer-sessionp ps)
           (equal (fn-scar-peer-sessionp (fn-peer-with-base ps b)
                                         (fn-peer-session-node ps))
                  (fn-peer-sessionp (fn-peer-with-base ps b))))
  :hints (("Goal" :in-theory (e/d (fn-scar-peer-sessionp fn-peer-sessionp
                                   fn-scar-node-statep)
                                  (fn-peer-with-base fn-node-statep
                                   fn-post-sessionp fn-cfgp
                                   fn-peer-transferp)))))

(local
 (defthm fn-acar-auth-with-base-fields
   (and (equal (fn-auth-session-base (fn-auth-with-base as b)) b)
        (equal (fn-auth-session-config (fn-auth-with-base as b))
               (fn-auth-session-config as))
        (equal (fn-auth-session-pending (fn-auth-with-base as b))
               (fn-auth-session-pending as))
        (equal (fn-auth-session-subject (fn-auth-with-base as b))
               (fn-auth-session-subject as))
        (equal (fn-auth-session-tlsp (fn-auth-with-base as b))
               (fn-auth-session-tlsp as))
        (equal (fn-auth-session-handshakingp (fn-auth-with-base as b))
               (fn-auth-session-handshakingp as))
        (fn-auth-session-shapep (fn-auth-with-base as b)))
   :hints (("Goal" :in-theory (enable fn-auth-with-base)))))

; KEYSTONE (the recognizer).  A session rebuilt from a held session by
; replacing its innermost post session is recognized by the carried
; recognizer at the held session's node exactly when it is recognized by
; fn-auth-sessionp.
(defthm fn-acar-scar-auth-sessionp-of-rebuilt-session
  (implies (fn-auth-sessionp as)
           (equal (fn-scar-auth-sessionp
                   (fn-auth-with-base
                    as (fn-peer-with-base (fn-auth-session-base as) b))
                   (fn-peer-session-node (fn-auth-session-base as)))
                  (fn-auth-sessionp
                   (fn-auth-with-base
                    as (fn-peer-with-base (fn-auth-session-base as) b)))))
  :hints (("Goal" :in-theory (e/d (fn-scar-auth-sessionp fn-auth-sessionp)
                                  (fn-auth-with-base fn-peer-with-base
                                   fn-scar-peer-sessionp fn-peer-sessionp
                                   fn-auth-configp fn-prin-idp
                                   fn-nntp-printable-tokenp)))))

; -----------------------------------------------------------------------------
; The advance and the outcome, carried.

(defun fn-acar-own-advance-result (o id)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (if conn
        (let* ((view (fn-own-view o))
               (archive (fn-own-view-archive view))
               (old (fn-own-conn-session conn))
               (pold (fn-auth-session-base old))
               (told (fn-peer-session-base pold))
               (base (fn-post-session-base told))
               (session (fn-auth-with-base
                         old
                         (fn-peer-with-base
                          pold
                          (fn-post-make-session
                           (fn-nntp-set-cursor (fn-nntp-open-session archive)
                                               (fn-nntp-session-group base)
                                               (fn-nntp-session-current base))
                           (fn-post-session-awaiting told)))))
               (next (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                       (fn-own-view-version view)
                                       (fn-own-view-frontier view)
                                       (fn-own-conn-wire conn)
                                       session archive
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-view-verdicts view)
                                       (fn-own-view-index view)
                                       (fn-own-view-group-index view))))
          (if (fn-scar-conn-boundedp next (fn-sn-groups (fn-own-store o))
                                     (fn-acar-session-node conn))
              (cons :advanced
                    (fn-own-set-conns o
                                      (fn-own-replace-conn next
                                                           (fn-own-conns o))))
            (cons :refused o)))
      (cons :absent o))))

(defthm fn-acar-own-advance-result-is-own-advance-result
  (implies (fn-acar-conn-sessionp o id)
           (equal (fn-acar-own-advance-result o id)
                  (fn-own-advance-result o id)))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result
                                   fn-own-advance-result
                                   fn-acar-conn-sessionp
                                   fn-scar-conn-boundedp fn-own-conn-boundedp
                                   fn-acar-session-node)
                                  (fn-scar-auth-sessionp fn-auth-sessionp
                                   fn-auth-with-base fn-peer-with-base
                                   fn-own-set-conns fn-own-replace-conn
                                   fn-own-conn-make-group-indexed
                                   fn-nntp-open-session fn-nntp-set-cursor
                                   fn-post-make-session)))))

(defun fn-acar-own-outcome (o id word)
  (declare (xargs :guard t))
  (let ((conn (fn-own-find-conn id (fn-own-conns o)))
        (sub (fn-own-inflight o)))
    (if (and conn sub (equal (fn-own-sub-id sub) id))
        (let* ((completion (fn-own-outcome-completion o word))
               (next (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                 (fn-own-next-id o) (fn-own-max-conns o)
                                 (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                 (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                                 (fn-own-config o) (fn-own-queue o) nil
                                 (if (equal completion :durable)
                                     (fn-own-feed-durable o sub)
                                   (fn-own-feeds o)))))
          (cons (fn-served-result-effects
                 (fn-served-post-outcome
                  (fn-served-make-conn-group-indexed (fn-own-conn-wire conn)
                                       (fn-own-conn-session conn)
                                       (fn-own-conn-archive conn)
                                       (fn-own-conn-config conn)
                                       (fn-own-conn-observation conn)
                                       (fn-own-clock o)
                                       (fn-own-conn-verdicts conn)
                                       (fn-own-conn-index conn)
                                       (fn-own-conn-group-index conn))
                  (fn-own-outcome-rendering o word)))
                (if (equal completion :durable)
                    (cdr (fn-acar-own-advance-result next id))
                  next)))
      (cons nil o))))

; The function host/owner-host.lisp fn-owner-outcome calls: the reference
; outcome whenever the connection the id names holds a session.
(defthm fn-acar-own-outcome-is-own-outcome
  (implies (fn-acar-conn-sessionp o id)
           (equal (fn-acar-own-outcome o id word)
                  (fn-own-outcome o id word)))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-outcome fn-own-outcome
                                   fn-own-advance fn-acar-conn-sessionp)
                                  (fn-acar-own-advance-result
                                   fn-own-advance-result
                                   fn-auth-sessionp
                                   fn-own-outcome-completion
                                   fn-own-outcome-rendering
                                   fn-own-feed-durable
                                   fn-served-post-outcome))
           :use ((:instance fn-acar-own-advance-result-is-own-advance-result
                  (o (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (fn-own-outcome-completion o word) :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)))))))))


; -----------------------------------------------------------------------------
; The premise is carried, not evaluated.

; Every open connection holds a session under the configured owner's
; relation (fn-ocl-conns-historyp conjoins fn-own-conn-boundedp) and under
; the owner relation (fn-own-conns-okp conjoins it too).
(defthm fn-acar-ocl-history-conn-holds-session
  (implies (fn-ocl-conn-historyp oc conn)
           (fn-auth-sessionp (fn-own-conn-session conn)))
  :hints (("Goal" :in-theory (e/d (fn-ocl-conn-historyp fn-own-conn-boundedp)
                                  (fn-auth-sessionp fn-node-statep fn-cpr-replay
                                   fn-cst-replay-node fn-own-take)))))
(defthm fn-acar-found-conn-of-ocl-history-is-bounded
  (implies (and (fn-ocl-conns-historyp oc conns)
                (fn-own-find-conn id conns))
           (fn-auth-sessionp (fn-own-conn-session (fn-own-find-conn id conns))))
  :hints (("Goal" :induct (fn-own-find-conn id conns)
           :in-theory (e/d (fn-ocl-conns-historyp fn-own-find-conn)
                           (fn-auth-sessionp fn-ocl-conn-historyp)))))
(defthm fn-acar-found-conn-of-okp-is-bounded
  (implies (and (fn-own-conns-okp conns groups capacity records)
                (fn-own-find-conn id conns))
           (fn-auth-sessionp (fn-own-conn-session (fn-own-find-conn id conns))))
  :hints (("Goal" :induct (fn-own-find-conn id conns)
           :in-theory (e/d (fn-own-conns-okp fn-own-find-conn fn-own-conn-okp
                            fn-own-conn-boundedp)
                           (fn-auth-sessionp fn-node-statep
                            fn-own-prefix-archive)))))
(defthm fn-acar-ocl-relation-carries-conn-sessionp
  (implies (fn-ocl-relation oc)
           (fn-acar-conn-sessionp (fn-ocfg-owner oc) id))
  :hints (("Goal" :in-theory (e/d (fn-ocl-relation fn-acar-conn-sessionp)
                                  (fn-auth-sessionp fn-ocl-conns-historyp
                                   fn-cst-relation fn-ocl-config-historyp
                                   fn-ocl-view-configp fn-ocl-view-historyp)))))
(defthm fn-acar-relation-carries-conn-sessionp
  (implies (fn-own-relation o)
           (fn-acar-conn-sessionp o id))
  :hints (("Goal" :in-theory (e/d (fn-own-relation fn-acar-conn-sessionp)
                                  (fn-auth-sessionp fn-own-conns-okp
                                   fn-snt-relation fn-own-view-okp)))))
(defthm fn-acar-own-finish-keeps-conns
  (equal (fn-own-conns (cdr (fn-ccar-own-finish o cfg)))
         (fn-own-conns o))
  :hints (("Goal" :in-theory (e/d (fn-own-finish fn-own-complete
                                   fn-own-refresh-keeps-fields)
                                  (fn-sn-finish fn-own-refresh
                                   fn-sn-completion-enabledp)))))

(defthm fn-acar-conn-sessionp-after-own-finish
  (equal (fn-acar-conn-sessionp (cdr (fn-ccar-own-finish o cfg)) id)
         (fn-acar-conn-sessionp o id))
  :hints (("Goal" :in-theory (e/d (fn-acar-conn-sessionp)
                                  (fn-auth-sessionp fn-ccar-own-finish-is-own-finish)))))

; KEYSTONE for host/owner-host.lisp fn-owner-outcome: under the configured
; owner's relation the carried outcome is the reference outcome, for every
; connection identifier and every observed word.
(defthm fn-acar-own-outcome-is-reference-under-ocl-relation
  (implies (fn-ocl-relation oc)
           (equal (fn-acar-own-outcome (fn-ocfg-owner oc) id word)
                  (fn-own-outcome (fn-ocfg-owner oc) id word)))
  :hints (("Goal" :in-theory (disable fn-acar-conn-sessionp fn-ocl-relation))))

; The same across the commit that precedes the outcome on the host's path
; (fn-owner-finish-submission installs (cdr (fn-ccar-own-finish ...))): the
; commit keeps the connections, so the premise the relation gave before it
; holds after it without the relation being re-established there.
(defthm fn-acar-own-outcome-after-commit-is-reference
  (implies (fn-ocl-relation oc)
           (equal (fn-acar-own-outcome
                   (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg)) id word)
                  (fn-own-outcome
                   (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg)) id word)))
  :hints (("Goal" :in-theory (disable fn-acar-conn-sessionp fn-ocl-relation
                                      fn-ccar-own-finish-is-own-finish))))

(defthm fn-acar-own-outcome-is-reference-under-relation
  (implies (fn-own-relation o)
           (equal (fn-acar-own-outcome o id word)
                  (fn-own-outcome o id word)))
  :hints (("Goal" :in-theory (disable fn-acar-conn-sessionp fn-own-relation))))

(in-theory (disable fn-acar-own-advance-result fn-acar-own-outcome
                    fn-acar-conn-sessionp))
