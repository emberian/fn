; owner-number-bound-join.lisp -- RFC 3977 section 6's article-number bound
; (fn-onb-boundp, books/owner-number-bound.lisp) carried at every host entry
; that carries the catalog join (fn-sjh-okp-at-*, the served-catalog-join-host
; books) (lane join-f2-8, 2026-09-29; PRF-958, PKT-615's follow-up, NNT-057).
;
; This book owns the prefix `fn-onbj-' (docs/prefixes.md).  One
; fn-onbj-boundp-at-X per fn-sjh-okp-at-X, stated over the same host-called
; function.

(in-package "ACL2")

(include-book "served-catalog-join-host-views")
(include-book "served-catalog-join-host-open")
(include-book "owner-number-bound")

(local (in-theory (disable (tau-system))))
(local (in-theory (disable fn-onb-boundp fn-onb-store-boundp)))
(defthm fn-onbj-arm-begin
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-begin o id)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-begin-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-begin o id)))))))

(defthm fn-onbj-arm-take
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-take-submission o)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-take-submission-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-take-submission o)))))))

(defthm fn-onbj-arm-control-submit
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-control-submit o msgid groups octets)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-control-submit-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-control-submit o msgid groups octets)))))))

(defthm fn-onbj-arm-operator-submit
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-operator-submit o msgid groups octets stored)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-operator-submit-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-operator-submit o msgid groups octets stored)))))))

(defthm fn-onbj-arm-bp-transit-submit
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-bp-transit-submit-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))))))

(defthm fn-onbj-arm-observe
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-observe o obs)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-observe-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-observe o obs)))))))

(defthm fn-onbj-arm-declare-group
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-declare-group o name)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-declare-group-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-declare-group o name)))))))

(defthm fn-onbj-arm-configure
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-configure o config)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-configure-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-configure o config)))))))

(defthm fn-onbj-arm-control-outcome
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-control-outcome o word)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-control-outcome-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-control-outcome o word)))))))

(defthm fn-onbj-arm-bp-transit-outcome
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-bp-transit-outcome o word)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-bp-transit-outcome-keeps-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-bp-transit-outcome o word)))))))

(defthm fn-onbj-arm-tick
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-own-tick o obs))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-tick-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-own-tick o obs))))))))

(defthm fn-onbj-arm-tick-peer
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-own-tick-peer o peer obs))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-tick-peer-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-own-tick-peer o peer obs))))))))

(defthm fn-onbj-arm-feeds
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-feeds-reconfigure o cfg)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-feeds-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-feeds-reconfigure o cfg)))))))

(defthm fn-onbj-arm-feed-connect
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-feed-connect o peer conn form)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-feed-connect-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-feed-connect o peer conn form)))))))

(defthm fn-onbj-arm-feed-lost
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-feed-lost o peer obs)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-feed-lost-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-feed-lost o peer obs)))))))

(defthm fn-onbj-arm-feed-recover
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-feed-recover o peer entries)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-feed-recover-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-feed-recover o peer entries)))))))

(defthm fn-onbj-arm-feed-reply
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-own-feed-reply o peer octets obs fn-arena))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-feed-reply-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-own-feed-reply o peer octets obs fn-arena))))))))

(defthm fn-onbj-arm-with-feeds
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-with-feeds o feeds)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-with-feeds-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-with-feeds o feeds)))))))

(defthm fn-onbj-arm-advance
  (implies (fn-onb-boundp o) (fn-onb-boundp (fn-own-advance o id)))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-advance-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-advance o id)))))))

(defthm fn-onbj-arm-outcome
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-own-outcome o id word))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-outcome-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-own-outcome o id word))))))))

(defthm fn-onbj-arm-acar-outcome
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-acar-own-outcome o id word))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-acar-outcome-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-acar-own-outcome o id word))))))))

(defthm fn-onbj-arm-transit-outcome
  (implies (fn-onb-boundp o) (fn-onb-boundp (cdr (fn-own-transit-outcome o id kind reason word))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-arm-transit-outcome-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view (o2 (cdr (fn-own-transit-outcome o id kind reason word))))))))

(defthm fn-onbj-boundp-of-ocfg-step-owner-event
  (implies (and (fn-onb-boundp (fn-ocfg-owner oc))
                (member-equal (car event)
                              '(:begin :take :control-submit :operator-submit :bp-transit-submit
                                :observe :declare-group :configure :control-outcome :bp-transit-outcome
                                :outcome :transit-outcome :feeds :feed-conn :feed-lost :feed-replay
                                :tick :tick-peer :feed-octets :reconfigure)))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-step oc event fn-arena))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-sjh-ocfg-owner-of-with-owner
                         fn-sjh-arm-ocfg-reconfigure-owner member-equal (:e member-equal) car-cons cdr-cons
                         fn-onbj-arm-begin fn-onbj-arm-take fn-onbj-arm-control-submit
                         fn-onbj-arm-operator-submit fn-onbj-arm-bp-transit-submit
                         fn-onbj-arm-observe fn-onbj-arm-declare-group
                         fn-onbj-arm-configure fn-onbj-arm-control-outcome
                         fn-onbj-arm-bp-transit-outcome fn-onbj-arm-outcome
                         fn-onbj-arm-transit-outcome fn-onbj-arm-feeds
                         fn-onbj-arm-feed-connect fn-onbj-arm-feed-lost
                         fn-onbj-arm-feed-recover fn-onbj-arm-tick
                         fn-onbj-arm-tick-peer fn-onbj-arm-feed-reply)
                       (theory 'minimal-theory)))))

; KEYSTONE: fn-owner-begin installs fn-pout-begin's owner.
(defthm fn-onbj-boundp-at-owner-begin
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-begin oc id fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-pout-begin) (fn-ocfg-step fn-onb-boundp fn-pout-begin-admitsp))
           :use ((:instance fn-onbj-boundp-of-ocfg-step-owner-event (event (list :begin id)))))))

; KEYSTONE: fn-owner-declare-group installs fn-pout-declare-group's owner.
(defthm fn-onbj-boundp-at-owner-declare-group
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-declare-group oc name fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-pout-declare-group) (fn-ocfg-step fn-onb-boundp fn-pout-declare-group-admitsp))
           :use ((:instance fn-onbj-boundp-of-ocfg-step-owner-event (event (list :declare-group name)))))))

; KEYSTONE: fn-owner-observe installs fn-ocfg-observe.
(defthm fn-onbj-boundp-at-owner-observe
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-observe oc obs))))
  :hints (("Goal" :in-theory '(fn-ocfg-observe fn-sjh-ocfg-owner-of-with-owner fn-onbj-arm-observe))))

; KEYSTONE: fn-owner-reconfigure-unstage installs fn-psrv-unstage, which
; keeps the owner (fn-sjh-okp-at-owner-unstage).
(defthm fn-onbj-boundp-at-owner-unstage
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-psrv-unstage oc))))
  :hints (("Goal" :in-theory '(fn-sjh-okp-at-owner-unstage))))

; KEYSTONE: fn-owner-install-node-secret installs fn-own-with-node-secret.
(defthm fn-onbj-boundp-at-owner-node-secret
  (implies (fn-onb-boundp o)
           (fn-onb-boundp (fn-own-with-node-secret o ring)))
  :hints (("Goal" :in-theory (e/d (fn-own-with-node-secret) (fn-onb-boundp))
           :use ((:instance fn-onb-boundp-of-same-store-and-view (o2 (fn-own-with-node-secret o ring)))))))

; KEYSTONE: fn-owner-install-profile installs fn-osb-install's owner.
(defthm fn-onbj-boundp-at-owner-install-profile
  (implies (fn-onb-boundp o)
           (fn-onb-boundp (mv-nth 1 (fn-osb-install o profile))))
  :hints (("Goal" :in-theory (e/d (fn-osb-install fn-onbj-arm-configure)
                                  (fn-onb-boundp fn-own-configure fn-bs-profile-admittedp fn-osb-config)))))

; KEYSTONE: fn-owner-outcome installs fn-apc-own-outcome's owner
; (fn-apc-own-outcome-is-acar-own-outcome under the carries fn-owner-take wrote).
(defthm fn-onbj-boundp-at-owner-outcome
  (implies (and (fn-icar-carryp icar) (fn-apc-p carry)
                (fn-onb-boundp o))
           (fn-onb-boundp (cdr (fn-apc-own-outcome o id word icar carry))))
  :hints (("Goal" :in-theory '(fn-apc-own-outcome-is-acar-own-outcome fn-onbj-arm-acar-outcome))))

; The connection events keep the store and the view.
(defthm fn-onbj-boundp-of-ocfg-conn-event
  (implies (and (fn-onb-boundp (fn-ocfg-owner oc))
                (member-equal (car event) '(:open :open-peer :advance :close :fault)))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-step oc event fn-arena))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-ocfg-conn-event-keeps-store-and-view)
                 (:instance fn-onb-boundp-of-same-store-and-view
                            (o (fn-ocfg-owner oc)) (o2 (fn-ocfg-owner (fn-ocfg-step oc event fn-arena))))))))

; KEYSTONE: fn-owner-open-peer installs fn-ocfg-open-peer's owner.
(defthm fn-onbj-boundp-at-owner-open-peer
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step) (fn-onb-boundp fn-ocfg-open-peer fn-ocfg-open fn-ocfg-advance
                                                  fn-ocfg-close fn-ocfg-fault fn-ocfg-read fn-ocfg-read-step
                                                  fn-ocfg-reconfigure fn-ocfg-complete fn-ocfg-pass))
           :use ((:instance fn-onbj-boundp-of-ocfg-conn-event (event (list :open-peer peer nil acfg)))))))

; -----------------------------------------------------------------------------
; The store's io steps (host/owner-host.lisp fn-owner-io): the store steps,
; the view stays, the refresh keeps the bound.

; An owner over a bounded store with the owner's view, refreshed, is bounded.
(defthm fn-onbj-boundp-of-refresh-with-store
  (implies (and (fn-onb-boundp o) (fn-onb-store-boundp s))
           (fn-onb-boundp
            (fn-own-refresh
             (fn-own-make s (fn-own-view o)
                          (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                          (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                          (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                          (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))
  :hints (("Goal" :in-theory (e/d (fn-onb-boundp) (fn-own-refresh fn-onb-store-boundp fn-nntp-nexts-boundedp))
           :use ((:instance fn-onb-boundp-of-refresh
                            (o (fn-own-make s (fn-own-view o)
                                            (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                                            (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
                                            (fn-own-facts o) (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                                            (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))))))

(defthm fn-onbj-store-boundp-when-boundp
  (implies (fn-onb-boundp o) (fn-onb-store-boundp (fn-own-store o)))
  :hints (("Goal" :in-theory (enable fn-onb-boundp))))

(defthm fn-onbj-boundp-of-own-store-io
  (implies (fn-onb-boundp o)
           (fn-onb-boundp (fn-own-store-step o (list :io operation result))))
  :hints (("Goal" :in-theory (e/d (fn-own-store-step fn-snrt-step fn-snt-step)
                                  (fn-own-refresh fn-sn-io))
           :use ((:instance fn-onb-store-boundp-of-io (s (fn-own-store o)))
                 (:instance fn-onbj-boundp-of-refresh-with-store (s (fn-sn-io (fn-own-store o) operation result)))))))

(defthm fn-onbj-boundp-of-ocfg-io
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-step oc (list :store (list :io operation result)) fn-arena))))
  :hints (("Goal" :in-theory '(fn-sjh-ocfg-store-step-owner fn-onbj-boundp-of-own-store-io))))

(defthm fn-onbj-boundp-of-ocfg-io-run
  (implies (and (fn-sjh-io-eventsp events)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-run oc events fn-arena))))
  :hints (("Goal" :induct (fn-ocfg-run oc events fn-arena)
           :in-theory (e/d (fn-ocfg-run fn-sjh-io-eventsp)
                           (fn-ocfg-step fn-sjh-io-eventp)))
          ("Subgoal *1/1" :use ((:instance fn-sjh-io-eventp-shape (e (car events)))
                                (:instance fn-onbj-boundp-of-ocfg-io
                                           (operation (cadr (cadr (car events))))
                                           (result (caddr (cadr (car events)))))))))

; KEYSTONE (fn-owner-io :log-reserve).
(defthm fn-onbj-boundp-at-owner-log-reserve
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-olr-ocfg-reserve oc))))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-reserve-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-onbj-boundp-of-ocfg-io-run (events *fn-sjh-log-reserve-events*))))))

; KEYSTONE (fn-owner-io :log-order).
(defthm fn-onbj-boundp-at-owner-log-order
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-olr-ocfg-order oc))))
  :hints (("Goal" :in-theory (union-theories '(fn-olr-ocfg-order-is-the-file-route-by-definition
                                               fn-ocfg-run car-cons cdr-cons (:e fn-sjh-io-eventsp)
                                               (:e consp) (:e car) (:e cdr))
                                             (theory 'minimal-theory))
           :use ((:instance fn-onbj-boundp-of-ocfg-io-run (events *fn-sjh-log-order-events*))))))
; KEYSTONE (fn-owner-open, no capture): fn-ocar-ocfg-open at the working view
; keeps the store and the view (fn-sjh-op-ocar-ocfg-open-facts2).
(defthm fn-onbj-boundp-at-owner-open
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-op-ocar-ocfg-open-facts2 (fn-arena nil) (fn-cat nil) (n 0))
                 (:instance fn-onb-boundp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))))))

; KEYSTONE (fn-owner-open, a capture held): opened at the captured reader
; view (fn-ocfg-at-reader-view), the working view put back
; (fn-ocfg-with-view): the store is the owner's, the view the working one.
(defthm fn-onbj-boundp-at-owner-open-captured
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner
                           (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))
                                              (fn-own-view (fn-ocfg-owner oc))))))
  :hints (("Goal" :in-theory (union-theories '(fn-ocfg-at-reader-view fn-ocv-reader-view
                                               fn-ocfg-with-view-keeps-the-rest)
                                             (theory 'minimal-theory))
           :use ((:instance fn-sjh-op-ocar-ocfg-open-facts2 (fn-arena nil) (fn-cat nil) (n 0)
                            (oc (fn-ocfg-with-view oc (car views))))
                 (:instance fn-sjh-op-ocar-ocfg-open-facts2 (fn-arena nil) (fn-cat nil) (n 0))
                 (:instance fn-onb-boundp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner
                                 (fn-ocfg-with-view (cdr (fn-ocar-ocfg-open (fn-ocfg-at-reader-view oc views) acfg))
                                                    (fn-own-view (fn-ocfg-owner oc))))))))))

; KEYSTONE (fn-owner-exposure-open): a refused accept keeps the owner, an
; admitted one opens a reader (fn-ocar-ocfg-open) or a peer (fn-ocfg-open-peer).
(defthm fn-onbj-boundp-at-owner-exposure-open
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-exp-open-ocfg (fn-ocar-exp-open oc xs lim acfg peer address now)))))
  :hints (("Goal" :in-theory (e/d (fn-ocar-exp-open fn-exp-open-ocfg fn-exp-at)
                                  (fn-ocar-ocfg-open fn-ocfg-open-peer fn-onb-boundp fn-exp-admit-decision
                                   fn-exp-register fn-exp-pinned-acfg fn-exp-with fn-exp-counters-bump
                                   fn-exp-line))
           :use ((:instance fn-onbj-boundp-at-owner-open (acfg (fn-exp-pinned-acfg acfg lim)))
                 (:instance fn-onbj-boundp-at-owner-open-peer (acfg (fn-exp-pinned-acfg acfg lim)))))))

(defthm fn-onbj-read-step-keeps-store-and-view
  (let ((o2 (car (cdr (fn-own-read-step-full o id event fn-arena)))))
    (and (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-view o2) (fn-own-view o))))
  :hints (("Goal" :in-theory (enable fn-own-read-step-full))))

; KEYSTONE (the served connection's wire events outside a read:
; host/owner-host.lisp fn-owner-tls-established and host/native-admin-host.lisp
; fn-owner-account-outcome, both fn-ocfg-read-step): the store and the view stay.
(defthm fn-onbj-boundp-at-owner-read-step
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (cdr (fn-ocfg-read-step oc id event fn-arena)))))
  :hints (("Goal" :in-theory '(fn-sjh-rs-ocfg-read-step-owner)
           :use ((:instance fn-onbj-read-step-keeps-store-and-view (o (fn-ocfg-owner oc)))
                 (:instance fn-onb-boundp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (car (cdr (fn-own-read-step-full (fn-ocfg-owner oc) id event fn-arena)))))))))
; -----------------------------------------------------------------------------
; The served read (host/owner-host.lisp fn-owner-chunk-span-at: fn-mca-read-
; span).  Every branch keeps the store and the view: the serve itself under
; the catalog join's premises (fn-sjh-rd-orr-keeps), the shed, the allowance,
; the refusal marks and the close by their fields.

(defthm fn-onbj-rd-orr
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner (fn-own-tls-result-owner
                                          (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))))
  :hints (("Goal" :in-theory '(fn-sjh-views-okp)
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-sjh-rd-orr-keeps)
                 (:instance fn-onb-boundp-of-same-store-and-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-own-tls-result-owner
                                                (fn-orr-read-span oc views id i end cache fn-octets fn-arena fn-cat)))))))))

(defthm fn-onbj-rd-with-allow
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-rd-with-allow-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))))))))

(defthm fn-onbj-rd-with-refused
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-rd-with-refused-fields)
                 (:instance fn-onb-boundp-of-same-store-and-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem))))))))

(defthm fn-onbj-rd-shed
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-otm-shed-ocfg oc id))))
  :hints (("Goal" :in-theory '(fn-otm-shed-ocfg fn-onbj-rd-with-refused fn-onbj-rd-with-allow))))

(defthm fn-onbj-rd-unshed
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-otm-unshed-ocfg oc id allow))))
  :hints (("Goal" :in-theory '(fn-otm-unshed-ocfg fn-onbj-rd-with-refused fn-onbj-rd-with-allow))))

(defthm fn-onbj-rd-otm
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner (fn-own-tls-result-owner
                                          (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))))
  :hints (("Goal" :in-theory (union-theories '(fn-scj-otm-read-span-owner fn-onbj-rd-unshed)
                                             (theory 'minimal-theory))
           :use ((:instance fn-onbj-rd-orr)
                 (:instance fn-onbj-rd-orr (oc (fn-otm-shed-ocfg oc id)))
                 (:instance fn-onbj-rd-shed)
                 (:instance fn-sjh-rd-okp-of-shed)
                 (:instance fn-sjh-rd-shed-view)
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-shed-ocfg oc id))))))))

(defthm fn-onbj-rd-owner-closed
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-oas-owner-closed oc id))))
  :hints (("Goal" :cases ((fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
           :in-theory (union-theories '(fn-sjh-rd-owner-closed-owner fn-sjh-rd-set-conns-fields)
                                      (theory 'minimal-theory)))
          ("Subgoal 1"
           :use ((:instance fn-onb-boundp-of-same-store-and-view
                            (o (fn-ocfg-owner oc))
                            (o2 (fn-own-set-conns (fn-ocfg-owner oc)
                                                  (fn-own-replace-conn
                                                   (fn-oas-conn-closed (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                                                   (fn-own-conns (fn-ocfg-owner oc))))))))))

(defun-nx fn-onbj-rd-result-okp (r)
  (fn-onb-boundp (fn-ocfg-owner (fn-own-tls-result-owner r))))

(defthm fn-onbj-rd-close-result
  (implies (fn-onbj-rd-result-okp r)
           (fn-onbj-rd-result-okp (fn-oas-close-result r id)))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp fn-oas-close-result fn-scj-tls-result-owner-of-make
                               fn-onbj-rd-owner-closed))))

(defthm fn-onbj-rd-whole-refusal
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onbj-rd-result-okp (fn-oas-whole-refusal oc id i end)))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp fn-oas-whole-refusal fn-scj-tls-result-owner-of-make
                               fn-onbj-rd-owner-closed))))

(defthm fn-onbj-rd-tiers
  (implies (and (fn-onb-boundp (fn-ocfg-owner oc))
                (fn-onbj-rd-result-okp r1))
           (fn-onbj-rd-result-okp (fn-oas-tiers oc r1 id i end slots)))
  :hints (("Goal" :in-theory '(fn-oas-tiers fn-onbj-rd-close-result fn-onbj-rd-whole-refusal))))

(defthm fn-onbj-rd-otm-result
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onbj-rd-result-okp (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp fn-onbj-rd-otm))))

(defthm fn-onbj-rd-posting-off
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onbj-rd-result-okp (fn-oas-posting-off-read oc views id i end cache s fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp fn-oas-posting-off-read fn-scj-tls-result-owner-of-make
                               fn-onbj-rd-with-allow)
           :use ((:instance fn-onbj-rd-otm (oc (fn-otm-owner-with-allow oc id nil)))
                 (:instance fn-onbj-rd-with-allow (allow nil))
                 (:instance fn-sjh-rd-okp-of-with-allow (allow nil))
                 (:instance fn-sjh-rd-with-allow-view (allow nil))
                 (:instance fn-sjh-rd-views-okp-of-same-view (o (fn-ocfg-owner oc))
                            (o2 (fn-ocfg-owner (fn-otm-owner-with-allow oc id nil))))))))

(defthm fn-onbj-rd-oas
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onbj-rd-result-okp (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-oas-read-span fn-onbj-rd-otm-result fn-onbj-rd-posting-off fn-onbj-rd-tiers))))

(defthm fn-onbj-rd-shut-read
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onbj-rd-result-okp (fn-mca-shut-read oc id i end)))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp fn-mca-shut-read fn-scj-tls-result-owner-of-make
                               fn-onbj-rd-owner-closed))))

(defthm fn-onbj-rd-refused-read
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onbj-rd-result-okp (fn-mca-refused-read oc views id i end cache s fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(fn-mca-refused-read fn-onbj-rd-posting-off fn-onbj-rd-close-result))))

(defthm fn-onbj-rd-mca
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onbj-rd-result-okp (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                        fn-octets fn-arena fn-cat))))
  :hints (("Goal" :in-theory '(fn-mca-read-span car-cons fn-onbj-rd-oas fn-onbj-rd-refused-read
                               fn-onbj-rd-shut-read))))

; KEYSTONE (the bound across the host's served read).  host/owner-host.lisp
; fn-owner-chunk-span-at installs the owner of (car (fn-mca-read-span ...)),
; under the catalog join's premises (fn-sjh-okp-at-owner-chunk-span's).
(defthm fn-onbj-boundp-at-owner-chunk-span
  (implies (and (fn-gacc-okp cache) (fn-scol-okp fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner
                           (fn-own-tls-result-owner
                            (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                   fn-octets fn-arena fn-cat))))))
  :hints (("Goal" :in-theory '(fn-onbj-rd-result-okp) :use ((:instance fn-onbj-rd-mca)))))

; The column premise carried (fn-sjh-colsp gives fn-scol-okp).
(defthm fn-onbj-boundp-at-owner-chunk-span-carried
  (implies (and (fn-gacc-okp cache) (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-views-okp views (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner
                           (fn-own-tls-result-owner
                            (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                   fn-octets fn-arena fn-cat))))))
  :hints (("Goal" :in-theory '(fn-sjh-colsp-gives-scol-okp)
           :use ((:instance fn-onbj-boundp-at-owner-chunk-span)))))

; The views carried too (fn-sjh-viewsp gives fn-sjh-views-okp).
(defthm fn-onbj-boundp-at-owner-chunk-span-fully-carried
  (implies (and (fn-gacc-okp cache) (fn-sjh-colsp pending fn-arena fn-cat)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-sjh-viewsp views (fn-ocfg-owner oc) fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner
                           (fn-own-tls-result-owner
                            (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                                   fn-octets fn-arena fn-cat))))))
  :hints (("Goal" :in-theory '(fn-sjh-viewsp-gives-views-okp)
           :use ((:instance fn-onbj-boundp-at-owner-chunk-span-carried)))))

; The captured open with the views carried: the bound needs no view premise
; (fn-onbj-boundp-at-owner-open-captured), the same host function.
