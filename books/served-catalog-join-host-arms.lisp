; served-catalog-join-host-arms.lisp -- the catalog join carried across the
; host's owner entries that touch neither the store's history nor the view
; (lane join-f2-2, 2026-09-29; PRF-302).
;
; Every entry below installs an owner whose store and view are the owner's
; own: the configured owner step's events other than the store's, the
; completion and the connection events (fn-sjh-okp-of-ocfg-step-owner-event),
; and the host's own wrappers over them (begin, declare-group, observe,
; unstage, node secret, profile, outcome, open-peer).  For each, fn-sjh-okp
; with the same pending row: the catalog invariant and the pinned versions are
; sca-join-4's per-arm lemmas (books/served-catalog-join-frame-conns.lisp,
; -frame-store.lisp), the store-side facts (S, LINK, the seen history) read
; only the store and the view, which the arm keeps (fn-sjh-arm-*-keeps-store-
; and-view).

(in-package "ACL2")

(include-book "served-catalog-join-host-complete")
(include-book "owner-served-bound") ; fn-osb-install: the profile the host installs

(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The frames: a step that keeps the store, the view and the connections keeps
; fn-sjh-okp outright.

(defthm fn-sjh-okp-of-same-fields
  (implies (and (fn-sjh-okp o pending fn-arena fn-cat)
                (equal (fn-own-store o2) (fn-own-store o))
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-own-conns o2) (fn-own-conns o)))
           (fn-sjh-okp o2 pending fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-sjh-okp-of-same-store-and-view fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-scjs-invp-of-same-fields)
                 (:instance fn-scjs-versionsp-of-same-fields)
                 (:instance fn-sjh-okp-unfolds)))))


(defthm fn-sjh-arm-okp-of-own-begin
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-begin o id) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-begin-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-begin o id)))))))

(defthm fn-sjh-arm-okp-of-own-take
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-take-submission o) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-take-submission-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-take-submission o)))))))

(defthm fn-sjh-arm-okp-of-own-control-submit
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-control-submit o msgid groups octets) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-control-submit-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-control-submit o msgid groups octets)))))))

(defthm fn-sjh-arm-okp-of-own-operator-submit
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-operator-submit o msgid groups octets stored) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-operator-submit-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-operator-submit o msgid groups octets stored)))))))

(defthm fn-sjh-arm-okp-of-own-bp-transit-submit
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-bp-transit-submit o cfg peer msgid octets id subject) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-bp-transit-submit-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-bp-transit-submit o cfg peer msgid octets id subject)))))))

(defthm fn-sjh-arm-okp-of-own-observe
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-observe o obs) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-observe-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-observe o obs)))))))

(defthm fn-sjh-arm-okp-of-own-declare-group
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-declare-group o name) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-declare-group-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-declare-group o name)))))))

(defthm fn-sjh-arm-okp-of-own-configure
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-configure o config) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-configure-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-configure o config)))))))

(defthm fn-sjh-arm-okp-of-own-control-outcome
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-control-outcome o word) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-control-outcome-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-control-outcome o word)))))))

(defthm fn-sjh-arm-okp-of-own-bp-transit-outcome
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-bp-transit-outcome o word) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory nil
           :use ((:instance fn-scjs-bp-transit-outcome-keeps-fields)
                 (:instance fn-sjh-okp-of-same-fields (o2 (fn-own-bp-transit-outcome o word)))))))

; -----------------------------------------------------------------------------
; The arms that move connections: the store and the view stay.

(defthm fn-sjh-arm-with-feeds-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-with-feeds o feeds)) (fn-own-store o))
       (equal (fn-own-view (fn-own-with-feeds o feeds)) (fn-own-view o)))
  :hints (("Goal" :in-theory (enable fn-own-with-feeds))))

(defthm fn-sjh-arm-advance-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-advance o id)) (fn-own-store o))
       (equal (fn-own-view (fn-own-advance o id)) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-advance-result fn-own-set-conns)
                                  (fn-own-replace-conn fn-own-conn-make-group-indexed fn-own-find-conn)))))

(defthm fn-sjh-arm-outcome-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-own-outcome o id word))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-outcome o id word))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-outcome)
                                  (fn-own-advance fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-result-effects fn-served-make-conn-group-indexed)))))

(defthm fn-sjh-arm-acar-advance-result-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-acar-own-advance-result o id))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-acar-own-advance-result o id))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result fn-own-set-conns)
                                  (fn-own-replace-conn fn-own-conn-make-group-indexed fn-own-find-conn)))))

(defthm fn-sjh-arm-acar-outcome-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-acar-own-outcome o id word))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-acar-own-outcome o id word))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-outcome)
                                  (fn-acar-own-advance-result fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-make-conn-group-indexed)))))


(defthm fn-sjh-arm-tick-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-own-tick o obs))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-tick o obs))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-tick fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-tick)))))

(defthm fn-sjh-arm-tick-peer-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-own-tick-peer o peer obs))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-tick-peer o peer obs))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-tick-peer fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-tick-peer)))))

(defthm fn-sjh-arm-feeds-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-feeds-reconfigure o cfg)) (fn-own-store o))
       (equal (fn-own-view (fn-own-feeds-reconfigure o cfg)) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-feeds-reconfigure fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds)))))

(defthm fn-sjh-arm-feed-connect-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-feed-connect o peer conn form)) (fn-own-store o))
       (equal (fn-own-view (fn-own-feed-connect o peer conn form)) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-put)))))

(defthm fn-sjh-arm-feed-lost-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-feed-lost o peer obs)) (fn-own-store o))
       (equal (fn-own-view (fn-own-feed-lost o peer obs)) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-lost fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-put)))))

(defthm fn-sjh-arm-feed-recover-keeps-store-and-view
  (and (equal (fn-own-store (fn-own-feed-recover o peer entries)) (fn-own-store o))
       (equal (fn-own-view (fn-own-feed-recover o peer entries)) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-recover fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-put)))))

(defthm fn-sjh-arm-feed-reply-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-own-feed-reply o peer octets obs fn-arena))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-feed-reply o peer octets obs fn-arena))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reply fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-with-feeds fn-own-feed-put fn-feed-observe fn-own-feed-parse-response fn-own-feed-article fn-handle-bytes fn-own-feed-entry-of fn-own-feed-entry-feed fn-own-feed-inflight-msgid fn-feed-queue fn-own-feed-entry-record)))))

(defthm fn-sjh-arm-transit-outcome-keeps-store-and-view
  (and (equal (fn-own-store (cdr (fn-own-transit-outcome o id kind reason word))) (fn-own-store o))
       (equal (fn-own-view (cdr (fn-own-transit-outcome o id kind reason word))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-transit-outcome fn-sjh-arm-with-feeds-keeps-store-and-view
                                   fn-sjh-arm-advance-keeps-store-and-view)
                                  (fn-own-advance fn-own-outcome-completion fn-own-transit-refused fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering fn-served-result-effects fn-served-make-conn-group-indexed)))))

(defthm fn-sjh-arm-okp-of-own-tick
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-own-tick o obs)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-tick-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-tick)
                 (:instance fn-scj-versions-atmost-of-own-tick)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-own-tick o obs))))))))

(defthm fn-sjh-arm-okp-of-own-tick-peer
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-own-tick-peer o peer obs)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-tick-peer-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-tick-peer)
                 (:instance fn-scj-versions-atmost-of-own-tick-peer)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-own-tick-peer o peer obs))))))))

(defthm fn-sjh-arm-okp-of-own-feeds
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-feeds-reconfigure o cfg) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-feeds-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-feeds-reconfigure)
                 (:instance fn-scj-versions-atmost-of-own-feeds-reconfigure)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-feeds-reconfigure o cfg)))))))

(defthm fn-sjh-arm-okp-of-own-feed-connect
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-feed-connect o peer conn form) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-feed-connect-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-feed-connect)
                 (:instance fn-scj-versions-atmost-of-own-feed-connect)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-feed-connect o peer conn form)))))))

(defthm fn-sjh-arm-okp-of-own-feed-lost
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-feed-lost o peer obs) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-feed-lost-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-feed-lost)
                 (:instance fn-scj-versions-atmost-of-own-feed-lost)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-feed-lost o peer obs)))))))

(defthm fn-sjh-arm-okp-of-own-feed-recover
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-feed-recover o peer entries) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-feed-recover-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-feed-recover)
                 (:instance fn-scj-versions-atmost-of-own-feed-recover)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-feed-recover o peer entries)))))))

(defthm fn-sjh-arm-okp-of-own-feed-reply
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-own-feed-reply o peer octets obs fn-arena)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-feed-reply-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-feed-reply)
                 (:instance fn-scj-versions-atmost-of-own-feed-reply)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-own-feed-reply o peer octets obs fn-arena))))))))

(defthm fn-sjh-arm-okp-of-own-with-feeds
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-with-feeds o feeds) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-with-feeds-keeps-store-and-view)
                 (:instance fn-scj-invp-of-own-with-feeds)
                 (:instance fn-scj-versions-atmost-of-own-with-feeds)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-with-feeds o feeds)))))))

(defthm fn-sjh-arm-okp-of-own-advance
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-advance o id) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-advance-keeps-store-and-view)
                 (:instance fn-scjs-advance-keeps-invp)
                 (:instance fn-scjs-advance-keeps-versions)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (fn-own-advance o id)))))))

(defthm fn-sjh-arm-okp-of-own-outcome
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-own-outcome o id word)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-outcome-keeps-store-and-view)
                 (:instance fn-scjs-outcome-keeps-invp)
                 (:instance fn-scjs-outcome-keeps-versions)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-own-outcome o id word))))))))

(defthm fn-sjh-arm-okp-of-own-acar-outcome
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-acar-own-outcome o id word)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-acar-outcome-keeps-store-and-view)
                 (:instance fn-scjs-acar-own-outcome-keeps-invp)
                 (:instance fn-scjs-acar-own-outcome-keeps-versions)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-acar-own-outcome o id word))))))))

(defthm fn-sjh-arm-okp-of-own-transit-outcome
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (cdr (fn-own-transit-outcome o id kind reason word)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-sjh-versionsp-is-versions-okp)
           :use ((:instance fn-sjh-okp-unfolds)
                 (:instance fn-sjh-arm-transit-outcome-keeps-store-and-view)
                 (:instance fn-scjs-transit-outcome-keeps-invp)
                 (:instance fn-scjs-transit-outcome-keeps-versions)
                 (:instance fn-sjh-okp-of-same-store-and-view (o2 (cdr (fn-own-transit-outcome o id kind reason word))))))))

;; The configuration staging (:reconfigure) keeps the owner.
(defthm fn-sjh-arm-ocfg-reconfigure-owner
  (equal (fn-ocfg-owner (fn-ocfg-reconfigure oc id deltas)) (fn-ocfg-owner oc))
  :hints (("Goal" :in-theory (enable fn-ocfg-reconfigure))))

; KEYSTONE (the configured owner step's other events).  host/owner-host.lisp
; fn-owner-step installs fn-ocfg-step of the event: :reconfigure
; (fn-owner-reconfigure-deltas-admitted), :take (fn-owner-take),
; :control-submit, :operator-submit, :feed-replay, :control-outcome,
; :bp-transit-outcome, :feeds, :feed-conn; with the connection events
; (fn-sjh-okp-of-ocfg-conn-event) and the store's (the -host books) this is
; every event fn-owner-step is given.  fn-sjh-okp with the same pending row.
(defthm fn-sjh-okp-of-ocfg-step-owner-event
  (implies (and (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
                (member-equal (car event)
                              '(:begin :take :control-submit :operator-submit :bp-transit-submit
                                :observe :declare-group :configure :control-outcome :bp-transit-outcome
                                :outcome :transit-outcome :feeds :feed-conn :feed-lost :feed-replay
                                :tick :tick-peer :feed-octets :reconfigure)))
           (fn-sjh-okp (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)) pending fn-arena fn-cat))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-ocfg-step fn-ocfg-pass fn-own-step fn-sjh-ocfg-owner-of-with-owner
                         fn-sjh-arm-ocfg-reconfigure-owner member-equal (:e member-equal) car-cons cdr-cons
                         fn-sjh-arm-okp-of-own-begin fn-sjh-arm-okp-of-own-take fn-sjh-arm-okp-of-own-control-submit
                         fn-sjh-arm-okp-of-own-operator-submit fn-sjh-arm-okp-of-own-bp-transit-submit
                         fn-sjh-arm-okp-of-own-observe fn-sjh-arm-okp-of-own-declare-group
                         fn-sjh-arm-okp-of-own-configure fn-sjh-arm-okp-of-own-control-outcome
                         fn-sjh-arm-okp-of-own-bp-transit-outcome fn-sjh-arm-okp-of-own-outcome
                         fn-sjh-arm-okp-of-own-transit-outcome fn-sjh-arm-okp-of-own-feeds
                         fn-sjh-arm-okp-of-own-feed-connect fn-sjh-arm-okp-of-own-feed-lost
                         fn-sjh-arm-okp-of-own-feed-recover fn-sjh-arm-okp-of-own-tick
                         fn-sjh-arm-okp-of-own-tick-peer fn-sjh-arm-okp-of-own-feed-reply)
                       (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The host's own wrappers.  Each KEYSTONE is stated over the function the
; host/owner-host.lisp entry named in its comment installs.

; KEYSTONE: fn-owner-begin installs fn-pout-begin's owner.
(defthm fn-sjh-okp-at-owner-begin
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (mv-nth 1 (fn-pout-begin oc id fn-arena))) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-pout-begin) (fn-ocfg-step fn-sjh-okp fn-pout-begin-admitsp))
           :use ((:instance fn-sjh-okp-of-ocfg-step-owner-event (event (list :begin id)))))))

; KEYSTONE: fn-owner-declare-group installs fn-pout-declare-group's owner.
(defthm fn-sjh-okp-at-owner-declare-group
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (mv-nth 1 (fn-pout-declare-group oc name fn-arena))) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-pout-declare-group) (fn-ocfg-step fn-sjh-okp fn-pout-declare-group-admitsp))
           :use ((:instance fn-sjh-okp-of-ocfg-step-owner-event (event (list :declare-group name)))))))

; KEYSTONE: fn-owner-observe installs fn-ocfg-observe (the clock reading
; before every socket read).
(defthm fn-sjh-okp-at-owner-observe
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (fn-ocfg-observe oc obs)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-ocfg-observe fn-sjh-ocfg-owner-of-with-owner fn-sjh-arm-okp-of-own-observe))))

; KEYSTONE: fn-owner-reconfigure-unstage installs fn-psrv-unstage, which
; keeps the owner.
(defthm fn-sjh-okp-at-owner-unstage
  (equal (fn-ocfg-owner (fn-psrv-unstage oc)) (fn-ocfg-owner oc))
  :hints (("Goal" :in-theory (enable fn-psrv-unstage))))

; KEYSTONE: fn-owner-install-node-secret installs fn-own-with-node-secret.
(defthm fn-sjh-okp-at-owner-node-secret
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (fn-own-with-node-secret o ring) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-with-node-secret) (fn-sjh-okp))
           :use ((:instance fn-sjh-okp-of-same-fields (o2 (fn-own-with-node-secret o ring)))))))

; KEYSTONE: fn-owner-install-profile installs fn-osb-install's owner.
(defthm fn-sjh-okp-at-owner-install-profile
  (implies (fn-sjh-okp o pending fn-arena fn-cat)
           (fn-sjh-okp (mv-nth 1 (fn-osb-install o profile)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-osb-install fn-sjh-arm-okp-of-own-configure)
                                  (fn-sjh-okp fn-own-configure fn-bs-profile-admittedp fn-osb-config)))))

; KEYSTONE: fn-owner-posting-configure installs fn-own-configure's owner
; (fn-sjh-arm-okp-of-own-configure above).

; KEYSTONE: fn-owner-outcome installs fn-apc-own-outcome's owner, which is
; fn-acar-own-outcome's under the intent and parse carries fn-owner-take
; wrote (fn-apc-own-outcome-is-acar-own-outcome).
(defthm fn-sjh-okp-at-owner-outcome
  (implies (and (fn-icar-carryp icar) (fn-apc-p carry)
                (fn-sjh-okp o pending fn-arena fn-cat))
           (fn-sjh-okp (cdr (fn-apc-own-outcome o id word icar carry)) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory '(fn-apc-own-outcome-is-acar-own-outcome fn-sjh-arm-okp-of-own-acar-outcome))))

; KEYSTONE: fn-owner-transit-outcome installs fn-own-transit-outcome's owner
; (fn-sjh-arm-okp-of-own-transit-outcome above); fn-owner-feed-install-port-
; result installs fn-own-with-feeds (fn-sjh-arm-okp-of-own-with-feeds).

; KEYSTONE: fn-owner-open-peer installs fn-ocfg-open-peer's owner, the
; configured step's (:open-peer PEER _ ACFG).
(defthm fn-sjh-okp-at-owner-open-peer
  (implies (fn-sjh-okp (fn-ocfg-owner oc) pending fn-arena fn-cat)
           (fn-sjh-okp (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))) pending fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step) (fn-sjh-okp fn-ocfg-open-peer fn-ocfg-open fn-ocfg-advance
                                                  fn-ocfg-close fn-ocfg-fault fn-ocfg-read fn-ocfg-read-step
                                                  fn-ocfg-reconfigure fn-ocfg-complete fn-ocfg-pass))
           :use ((:instance fn-sjh-okp-of-ocfg-conn-event (event (list :open-peer peer nil acfg)))))))
