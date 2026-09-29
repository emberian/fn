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
(defthm fn-onbj-inflight-fitp-when-ready
  (implies (equal (fn-sf-phase (fn-sn-files s)) :ready)
           (fn-onb-inflight-fitp s))
  :hints (("Goal" :in-theory (enable fn-onb-inflight-fitp fn-sf-record-phasep))))

(defthm fn-onbj-store-boundp-of-known-abort
  (implies (fn-onb-store-boundp s)
           (fn-onb-store-boundp (fn-sn-known-abort s)))
  :hints (("Goal" :cases ((fn-sn-known-abort-enabledp s))
           :in-theory (e/d (fn-onb-store-boundp fn-cstp-sn-update-fields)
                           (fn-onb-node-boundp fn-sn-known-abort-enabledp fn-sn-known-abort-files
                            fn-node-complete fn-replay-advance-txid fn-sn-statep)))
          ("Subgoal 2" :in-theory (enable fn-sn-known-abort))
          ("Subgoal 1" :in-theory (e/d (fn-onb-store-boundp fn-cstp-sn-update-fields fn-sn-known-abort)
                                       (fn-onb-node-boundp fn-sn-known-abort-enabledp fn-sn-known-abort-files
                                        fn-node-complete fn-replay-advance-txid fn-sn-statep))
           :use ((:instance fn-pout-known-abort-reaches-ready)
                 (:instance fn-onbj-inflight-fitp-when-ready (s (fn-sn-known-abort s)))))))

(defthm fn-onbj-store-boundp-of-refuse-reservation
  (implies (fn-onb-store-boundp s)
           (fn-onb-store-boundp (fn-sn-refuse-reservation s txid)))
  :hints (("Goal" :in-theory (e/d (fn-onb-store-boundp fn-sn-refuse-reservation fn-sn-refuse-reservation-enabledp
                                   fn-sf-refuse-reservation fn-cstp-sn-update-fields)
                                  (fn-onb-node-boundp fn-replay-advance-txid fn-sn-statep fn-sf-statep fn-node-statep))
           :use ((:instance fn-onbj-inflight-fitp-when-ready
                            (s (fn-sn-refuse-reservation s txid)))))))

(defthm fn-onbj-boundp-of-ocfg-known-abort
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-step oc (list :store (list :known-abort)) fn-arena))))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-ocfg-store-step-owner fn-own-store-step fn-snrt-step
                                               fn-onbj-boundp-of-refresh-with-store fn-onbj-store-boundp-when-boundp
                                               fn-onbj-store-boundp-of-known-abort car-cons (:e car))
                                             (theory 'minimal-theory)))))

(defthm fn-onbj-boundp-of-ocfg-refuse-reservation
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-ocfg-step oc (list :store (list :refuse-reservation txid)) fn-arena))))
  :hints (("Goal" :in-theory (union-theories '(fn-sjh-ocfg-store-step-owner fn-own-store-step fn-snrt-step
                                               fn-onbj-boundp-of-refresh-with-store fn-onbj-store-boundp-when-boundp
                                               fn-onbj-store-boundp-of-refuse-reservation car-cons cdr-cons (:e car))
                                             (theory 'minimal-theory)))))

; KEYSTONE: host/owner-host.lisp fn-owner-known-abort installs
; fn-pout-known-abort's owner (the store back at :ready).
(defthm fn-onbj-boundp-at-owner-known-abort
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-known-abort oc fn-arena)))))
  :hints (("Goal" :in-theory (union-theories '(fn-pout-known-abort mv-nth car-cons cdr-cons (:e zp) (:e binary-+))
                                      (theory 'minimal-theory))
           :use ((:instance fn-onbj-boundp-of-ocfg-known-abort)))))

; KEYSTONE: host/owner-host.lisp fn-owner-refuse-reservation installs
; fn-pout-refuse-reservation's owner.
(defthm fn-onbj-boundp-at-owner-refuse-reservation
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena)))))
  :hints (("Goal" :in-theory (union-theories '(fn-pout-refuse-reservation mv-nth car-cons cdr-cons (:e zp) (:e binary-+))
                                      (theory 'minimal-theory))
           :use ((:instance fn-onbj-boundp-of-ocfg-refuse-reservation (txid (+ -1 (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc))))))))))
; -----------------------------------------------------------------------------
; The completions (host/owner-host.lisp fn-owner-finish, the article and
; submission finishes): the Store's finish keeps the bound
; (fn-onb-store-boundp-of-finish, unconditional), the view stays, the
; refresh keeps it.

(defthm fn-onbj-boundp-of-refresh-make
  (implies (and (fn-onb-store-boundp s)
                (fn-nntp-nexts-boundedp (fn-state-nexts (fn-own-view-archive v))))
           (fn-onb-boundp (fn-own-refresh (fn-own-make s v c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13))))
  :hints (("Goal" :in-theory (e/d (fn-onb-boundp) (fn-own-refresh fn-onb-store-boundp fn-nntp-nexts-boundedp))
           :use ((:instance fn-onb-boundp-of-refresh
                            (o (fn-own-make s v c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13)))))))

(defthm fn-onbj-boundp-of-own-complete
  (implies (fn-onb-boundp o)
           (fn-onb-boundp (fn-own-complete o)))
  :hints (("Goal" :in-theory (e/d (fn-own-complete) (fn-own-refresh fn-sn-finish fn-sn-completion-enabledp
                                                     fn-nntp-nexts-boundedp))
           :use ((:instance fn-onb-store-boundp-of-finish (s (fn-own-store o)))
                 (:instance fn-onbj-store-boundp-when-boundp)
                 (:instance fn-onb-boundp)))))

(defthm fn-onbj-boundp-of-ccar-own-complete-enabled
  (implies (and (fn-onb-boundp o)
                (fn-ccar-completion-enabledp (fn-own-store o)))
           (fn-onb-boundp (fn-ccar-own-complete-enabled o)))
  :hints (("Goal" :in-theory '(fn-ccar-own-complete)
           :use ((:instance fn-ccar-own-complete-is-own-complete)
                 (:instance fn-onbj-boundp-of-own-complete)))))

(defthm fn-onbj-boundp-of-ccar-ocfg-complete
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-ccar-ocfg-complete oc))))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-ocfg-complete fn-ccar-own-complete-is-own-complete
                                               fn-onbj-boundp-of-own-complete fn-ocfg-owner-of-fn-ocfg-make)
                                             (theory 'minimal-theory)))))

; KEYSTONE: host/owner-host.lisp fn-owner-finish installs
; fn-rix-ocfg-complete's owner, which is the carried completion's over the
; owner's history (fn-rix-ocfg-complete-is-ccar-ocfg-complete).  Both
; fn-sjh-okp-at-owner-finish-no-row's and -finish-identity's owners.
(defthm fn-onbj-boundp-at-owner-finish
  (implies (and (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc)))
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner (fn-rix-ocfg-complete oc fn-hist))))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete-is-ccar-ocfg-complete fn-onbj-boundp-of-ccar-ocfg-complete))))

; KEYSTONE: the article finish (fn-ccar-own-finish): the owner, or its
; enabled completion.
(defthm fn-onbj-boundp-at-host-article-finish
  (implies (fn-onb-boundp o)
           (fn-onb-boundp (cdr (fn-ccar-own-finish o cfg fn-arena))))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-own-finish fn-onbj-boundp-of-ccar-own-complete-enabled car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

; KEYSTONE: host/owner-host.lisp's submission finish installs
; fn-apc-own-finish's owner, the article finish's under the parse carry and
; the owner's history (fn-apc-own-finish-is-ccar-own-finish).
(defthm fn-onbj-boundp-at-owner-finish-submission
  (implies (and (fn-apc-p carry)
                (fn-hist-of-storep fn-hist (fn-own-store o))
                (fn-onb-boundp o))
           (fn-onb-boundp (cdr (fn-apc-own-finish o cfg fn-arena fn-hist carry))))
  :hints (("Goal" :in-theory '(fn-apc-own-finish-is-ccar-own-finish fn-onbj-boundp-at-host-article-finish))))
; -----------------------------------------------------------------------------
; The prepares.  The identity prepare's bound is fn-onb-boundp-at-owner-
; prepare-identity (no premise: both fn-sjh-okp-at-owner-prepare-identity-
; sealed's and -unsealed's owner).  The article prepare's premise, the view's
; identity index (fn-pidx-view-okp), is the host's: the owner relation and
; the catalog join's indexed view give it (fn-pidx-view-okp-of-live-owner).

; KEYSTONE: host/owner-host.lisp fn-owner-prepare-buffer installs
; fn-pout-prepare-article's owner.
(defthm fn-onbj-boundp-at-owner-prepare-buffer
  (implies (and (fn-prc-carryp carry)
                (fn-ocl-relation oc)
                (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (fn-onb-boundp (fn-ocfg-owner oc)))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-pout-prepare-article oc record budget carry)))))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-sjh-okp-unfolds (o (fn-ocfg-owner oc)))
                 (:instance fn-pidx-view-okp-of-live-owner)
                 (:instance fn-onb-boundp-at-owner-prepare-buffer)))))
; -----------------------------------------------------------------------------
; The live configuration's completion (host/owner-host.lisp
; fn-owner-reconfigure-complete: fn-oclc-publish).  The carried configure
; installs a node over the same watermarks, a group new to the domain
; starting at 1 (fn-cnode-extend-nexts), with nothing pending, and keeps the
; store's files (at :ready).

(defthm fn-onbj-next-number-bounded
  (implies (fn-nntp-nexts-boundedp nexts)
           (and (natp (fn-next-number g nexts))
                (<= (fn-next-number g nexts) *fn-nntp-max-article-number*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-next-number fn-nntp-nexts-boundedp))))

(defthm fn-onbj-extend-nexts-bounded
  (implies (fn-nntp-nexts-boundedp nexts)
           (fn-nntp-nexts-boundedp (fn-cnode-extend-nexts names nexts)))
  :hints (("Goal" :in-theory (e/d (fn-cnode-extend-nexts fn-nntp-nexts-boundedp) (fn-next-number))
           :induct (fn-cnode-extend-nexts names nexts))
          ("Subgoal *1/1" :use ((:instance fn-onbj-next-number-bounded (g (car names)))))))

(defthm fn-onbj-node-boundp-of-oclc-advance
  (implies (fn-onb-node-boundp node)
           (fn-onb-node-boundp (fn-oclc-advance node txid)))
  :hints (("Goal" :in-theory (e/d (fn-oclc-advance fn-onb-node-boundp) (fn-nntp-nexts-boundedp fn-snb-groups-fitp
                                                                        fn-oclc-advance-okp)))))

(defthm fn-onbj-node-boundp-of-oclc-apply
  (implies (fn-onb-node-boundp (fn-cnode-node cn))
           (fn-onb-node-boundp (fn-cnode-node (fn-oclc-apply cn record))))
  :hints (("Goal" :in-theory (e/d (fn-oclc-apply fn-onb-node-boundp)
                                  (fn-nntp-nexts-boundedp fn-snb-groups-fitp fn-cnode-carried-acceptablep
                                   fn-cfg-apply-record fn-cnode-domain-of fn-cnode-extend-nexts)))))

(defthm fn-onbj-store-boundp-of-oclc-configure
  (implies (fn-onb-store-boundp st)
           (fn-onb-store-boundp (mv-nth 0 (fn-oclc-configure st config record))))
  :hints (("Goal" :in-theory (e/d (fn-oclc-configure fn-onb-store-boundp fn-cpo-install fn-sn-with-configuration
                                   fn-sn-node fn-sn-files)
                                  (fn-onb-node-boundp fn-oclc-advance fn-oclc-apply fn-cnode-carried-acceptablep
                                   fn-oclc-advance-okp fn-oclc-install-okp fn-cfg-recordp))
           :use ((:instance fn-onbj-inflight-fitp-when-ready
                            (s (mv-nth 0 (fn-oclc-configure st config record))))
                 (:instance fn-sjh-rc-configure-store-fields (s st))))))

(defthm fn-onbj-boundp-of-oclc-complete
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (fn-oclc-complete oc))))
  :hints (("Goal" :in-theory (union-theories '(fn-oclc-complete fn-ocfg-owner-of-fn-ocfg-make fn-ocl-owner-with-store)
                                             (theory 'minimal-theory))
           :use ((:instance fn-onbj-store-boundp-when-boundp (o (fn-ocfg-owner oc)))
                 (:instance fn-onbj-store-boundp-of-oclc-configure
                            (st (fn-own-store (fn-ocfg-owner oc))) (config (fn-ocfg-config oc))
                            (record (fn-ocfg-staged oc)))
                 (:instance fn-onbj-boundp-of-refresh-with-store
                            (o (fn-ocfg-owner oc))
                            (s (mv-nth 0 (fn-oclc-configure (fn-own-store (fn-ocfg-owner oc))
                                                            (fn-ocfg-config oc) (fn-ocfg-staged oc)))))))))

; KEYSTONE (the live configuration's completion).  host/owner-host.lisp
; fn-owner-reconfigure-complete installs fn-oclc-publish's owner: refused or
; recovery-required, the owner it was given; durable, the configured owner
; over the carried configure's store.  No premise beyond the bound before.
(defthm fn-onbj-boundp-at-owner-reconfigure-complete
  (implies (fn-onb-boundp (fn-ocfg-owner oc))
           (fn-onb-boundp (fn-ocfg-owner (mv-nth 1 (fn-oclc-publish oc generation max-octets)))))
  :hints (("Goal" :in-theory (e/d (fn-oclc-publish fn-sjh-ocfg-owner-of-with-owner fn-onbj-arm-configure
                                   fn-onbj-boundp-of-oclc-complete)
                                  (fn-oclc-complete fn-own-configure fn-oag-post-config
                                   fn-cfg-record-generation fn-ocfg-with-owner)))))
; -----------------------------------------------------------------------------
; The opens (install, recover, full open: host/owner-host.lisp
; fn-owner-install-extended).  The host installs an owner only when
; fn-onb-open-okp holds (KEYSTONE fn-onb-boundp-when-open-okp gives
; fn-onb-boundp there, whichever open built it).  At an idle store -- every
; open's (fn-sjh-okp-at-install's premise) -- the check is exactly the
; bound: the open refuses a store by name only when a watermark is past it.

; KEYSTONE: at an idle store the open's check is the bound.
(defthm fn-onbj-open-okp-is-boundp-when-idle
  (implies (fn-own-store-idlep (fn-own-store o))
           (equal (fn-onb-open-okp o) (fn-onb-boundp o)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-store-idlep fn-snt-idle-phasep fn-sf-record-phasep)
                                  (fn-onb-open-okp fn-onb-boundp))
           :use ((:instance fn-onb-open-okp-is-boundp-outside-a-transaction)))))
