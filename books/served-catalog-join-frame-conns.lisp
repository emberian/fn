; served-catalog-join-frame-conns.lisp -- the owner transitions that change
; CONNECTIONS (and not the store's history) keep the catalog invariant
; fn-scj-invp with the catalog untouched (lane sca-join-4, sub-lane F-conn,
; 2026-09-27; PRF-302, step 4 of the join's discharge).
;
; fn-scj-invp (books/served-catalog-join-conns.lisp) reads the owner's view,
; its store and its connection list, nothing else.  Every arm here keeps the
; view and the store (fn-scj-invp-of-frame), so what is left is the
; connection list: a sublist (close, fault), the same list (the feed arms,
; the tick, the carried outcome's completion record), a record whose pin
; fields are unchanged (fn-own-reader-context), or a record pinned to the
; CURRENT view (open, open-peer, advance).  KEYSTONE for the last:
; fn-scj-conn-pinp-of-view-pinned -- a connection record whose version,
; archive, index, group index and control are the view's is pinned over the
; catalog exactly when the view is live over it (fn-scj-live-okp), which
; fn-scj-invp carries.  No arm needs an owner-relation hypothesis: the only
; one each keeps is fn-scj-invp of the owner before.
;
; Note on the carried advance (books/owner-advance-carried.lisp): neither
; fn-own-advance-result nor fn-acar-own-advance-result refreshes the view;
; both re-pin the connection to the view as it is.  The refresh on the host's
; outcome path is the commit's (fn-scj-invp-of-refresh, the frame book).

(in-package "ACL2")

(include-book "served-catalog-join-frame")

(defun-nx fn-scj-view-pinned-connp (conn view)
  (and (equal (fn-own-conn-version conn) (fn-own-view-version view))
       (equal (fn-own-conn-archive conn) (fn-own-view-archive view))
       (equal (fn-own-conn-index conn) (fn-own-view-index view))
       (equal (fn-own-conn-group-index conn) (fn-own-view-group-index view))
       (equal (fn-own-conn-control conn) (fn-own-view-control view))))

; KEYSTONE: a record pinned to the view is pinned over the catalog exactly
; when the view is live over it.
(defthm fn-scj-conn-pinp-of-view-pinned
  (implies (fn-scj-view-pinned-connp conn view)
           (equal (fn-scj-conn-pinp conn fn-arena fn-cat)
                  (fn-scj-live-okp view fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scj-view-pinned-connp fn-scj-conn-pinp fn-scj-conn-pinned-index
                                   fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp)
                                  (fn-scr-catalogp fn-scr-view-of)))))

(defthm fn-scj-conn-pinp-of-view-conn
  (equal (fn-scj-conn-pinp
          (fn-own-conn-make-group-indexed
           id (fn-own-view-version view) frontier wire session (fn-own-view-archive view)
           config observation verdicts (fn-own-view-index view)
           (fn-own-view-group-index view) (fn-own-view-control view))
          fn-arena fn-cat)
         (fn-scj-live-okp view fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-conn-pinp-of-view-pinned
                                   (conn (fn-own-conn-make-group-indexed
                                          id (fn-own-view-version view) frontier wire session
                                          (fn-own-view-archive view) config observation verdicts
                                          (fn-own-view-index view) (fn-own-view-group-index view)
                                          (fn-own-view-control view)))))
           :in-theory (e/d (fn-scj-view-pinned-connp) (fn-own-conn-make-group-indexed)))))

(defthm fn-scj-conn-pinp-of-conn-fields
  (equal (fn-scj-conn-pinp
          (fn-own-conn-make-group-indexed
           id (fn-own-conn-version conn) frontier wire session (fn-own-conn-archive conn)
           config observation verdicts (fn-own-conn-index conn)
           (fn-own-conn-group-index conn) (fn-own-conn-control conn))
          fn-arena fn-cat)
         (fn-scj-conn-pinp conn fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-conn-pinp fn-scj-conn-pinned-index)
                                  (fn-own-conn-make-group-indexed fn-scr-catalogp fn-scr-view-of)))))

(defthm fn-scj-conns-pinp-of-cons
  (equal (fn-scj-conns-pinp (cons conn conns) fn-arena fn-cat)
         (and (fn-scj-conn-pinp conn fn-arena fn-cat)
              (fn-scj-conns-pinp conns fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scj-conns-pinp) (fn-scj-conn-pinp)))))

(defthm fn-scj-conns-pinp-of-remove-conn
  (implies (fn-scj-conns-pinp conns fn-arena fn-cat)
           (fn-scj-conns-pinp (fn-own-remove-conn id conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-remove-conn id conns)
           :in-theory (e/d (fn-own-remove-conn fn-scj-conns-pinp) (fn-scj-conn-pinp)))))

(defthm fn-scj-conns-pinp-of-replace-conn
  (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                (fn-scj-conn-pinp conn fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-replace-conn conn conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (e/d (fn-own-replace-conn fn-scj-conns-pinp) (fn-scj-conn-pinp)))))

; The frame: a step that keeps the view and the store keeps the invariant
; exactly when its connections stay pinned.
(defthm fn-scj-invp-of-frame
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (equal (fn-own-view o2) (fn-own-view o))
                (equal (fn-own-store o2) (fn-own-store o))
                (fn-scj-conns-pinp (fn-own-conns o2) fn-arena fn-cat))
           (fn-scj-invp o2 fn-arena fn-cat))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scj-invp fn-scj-vvp)
                                  (fn-scj-joinp fn-scj-rows-invp fn-scj-live-okp fn-scj-conns-pinp)))))

(defthm fn-scj-invp-gives-live-okp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-scj-invp))))

(defthm fn-scj-invp-gives-conns-pinp
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-scj-invp))))

(defthm fn-scj-invp-of-own-open
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-open o acfg)) fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-invp-of-frame (o2 (cdr (fn-own-open o acfg)))))
           :in-theory (e/d (fn-own-open) (fn-served-open-group-indexed fn-own-conn-make-group-indexed
                                          fn-scj-live-okp fn-scj-conn-pinp fn-own-body-limit fn-own-view-group-index fn-own-view-index fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-invp-of-own-open-peer
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-open-peer o peer cfg acfg)) fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-invp-of-frame (o2 (cdr (fn-own-open-peer o peer cfg acfg)))))
           :in-theory (e/d (fn-own-open-peer)
                           (fn-served-open-peer-group-indexed fn-own-conn-make-group-indexed
                            fn-scj-live-okp fn-scj-conn-pinp fn-own-peer-body-limit
                            fn-cfg-peer-find fn-own-view-group-index fn-own-view-index
                            fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-invp-of-own-close
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-close o id) fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-invp-of-frame (o2 (fn-own-close o id))))
           :in-theory (e/d (fn-own-close) (fn-scj-conns-pinp fn-own-remove-conn fn-own-remove-subs)))))

(defthm fn-scj-invp-of-own-fault
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-fault o id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-fault) (fn-own-close fn-own-fault-effects)))))

(defthm fn-scj-invp-of-own-set-conns
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (fn-scj-conns-pinp conns fn-arena fn-cat))
           (fn-scj-invp (fn-own-set-conns o conns) fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-invp-of-frame (o2 (fn-own-set-conns o conns))))
           :in-theory (e/d (fn-own-set-conns) (fn-scj-conns-pinp)))))

(defthm fn-scj-invp-of-own-reader-context
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-reader-context o id cfg) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context)
                                  (fn-own-set-conns fn-own-conn-make-group-indexed fn-scj-conn-pinp
                                   fn-scj-conns-pinp fn-own-find-conn fn-own-replace-conn
                                   fn-auth-with-base fn-peer-open-session fn-cfgp
                                   fn-own-conn-version fn-own-conn-archive fn-own-conn-index
                                   fn-own-conn-group-index fn-own-conn-control)))))

(defthm fn-scj-invp-of-own-advance-result
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-advance-result o id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-advance-result)
                                  (fn-own-set-conns fn-own-conn-make-group-indexed fn-scj-conn-pinp
                                   fn-scj-conns-pinp fn-own-find-conn fn-own-replace-conn
                                   fn-own-conn-boundedp fn-scj-live-okp
                                   fn-auth-with-base fn-peer-with-base fn-post-make-session
                                   fn-nntp-set-cursor fn-nntp-open-session
                                   fn-own-view-group-index fn-own-view-index
                                   fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-invp-of-own-advance
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-advance o id) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-advance) (fn-own-advance-result)))))

(defthm fn-scj-invp-of-acar-own-advance-result
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-acar-own-advance-result o id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-advance-result)
                                  (fn-own-set-conns fn-own-conn-make-group-indexed fn-scj-conn-pinp
                                   fn-scj-conns-pinp fn-own-find-conn fn-own-replace-conn
                                   fn-scar-conn-boundedp fn-scj-live-okp fn-acar-session-node
                                   fn-auth-with-base fn-peer-with-base fn-post-make-session
                                   fn-nntp-set-cursor fn-acar-open-session
                                   fn-own-view-group-index fn-own-view-index
                                   fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-invp-of-own-with-feeds
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-with-feeds o feeds) fn-arena fn-cat))
  :hints (("Goal" :use ((:instance fn-scj-invp-of-frame (o2 (fn-own-with-feeds o feeds))))
           :in-theory (e/d (fn-own-with-feeds) (fn-scj-conns-pinp)))))

(defthm fn-scj-invp-of-own-feeds-reconfigure
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-feeds-reconfigure o cfg) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feeds-reconfigure) (fn-own-with-feeds fn-own-feed-reconfigure)))))

(defthm fn-scj-invp-of-own-feed-connect
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-feed-connect o peer conn form) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect) (fn-own-with-feeds fn-own-feed-put)))))

(defthm fn-scj-invp-of-own-feed-lost
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-feed-lost o peer obs) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-lost) (fn-own-with-feeds fn-own-feed-lost-one)))))

(defthm fn-scj-invp-of-own-feed-recover
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (fn-own-feed-recover o peer entries) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-recover) (fn-own-with-feeds fn-own-feed-put fn-feed-replay)))))

(defthm fn-scj-invp-of-own-feed-reply
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-feed-reply o peer octets obs)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reply)
                                  (fn-own-with-feeds fn-own-feed-put fn-feed-observe
                                   fn-own-feed-parse-response fn-own-feed-article)))))

(defthm fn-scj-invp-of-own-tick
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-tick o obs)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-tick) (fn-own-with-feeds fn-own-feed-tick)))))

(defthm fn-scj-invp-of-own-tick-peer
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-own-tick-peer o peer obs)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-tick-peer) (fn-own-with-feeds fn-own-feed-tick-peer)))))

; The carried outcome (host/owner-host.lisp fn-owner-outcome): the
; completion record keeps the view, the store and the connections, and a
; durable completion then advances the connection to the view.
(defthm fn-scj-invp-of-acar-own-outcome
  (implies (fn-scj-invp o fn-arena fn-cat)
           (fn-scj-invp (cdr (fn-acar-own-outcome o id word)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-acar-own-outcome)
                                  (fn-acar-own-advance-result fn-own-outcome-completion
                                   fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering
                                   fn-served-make-conn-group-indexed fn-scj-conns-pinp))
           :use ((:instance fn-scj-invp-of-frame
                            (o2 (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (fn-own-outcome-completion o word) :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o))))))))

; The configured owner's connection arms (books/owner-config.lisp fn-ocfg-step).
(defthm fn-scj-invp-of-ocfg-open
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open)
                                  (fn-own-open fn-own-reader-context fn-own-find-conn
                                   fn-ocfg-pin-add fn-auth-config-with-accounts)))))

(defthm fn-scj-invp-of-ocfg-open-peer
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg))) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open-peer fn-ocfg-with-owner)
                                  (fn-own-open-peer fn-auth-config-with-accounts)))))

(defthm fn-scj-invp-of-ocfg-close
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (fn-ocfg-close oc id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-close) (fn-own-close fn-ocfg-pin-remove)))))

(defthm fn-scj-invp-of-ocfg-fault
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (cdr (fn-ocfg-fault oc id))) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-fault) (fn-own-fault fn-ocfg-pin-remove)))))

(defthm fn-scj-invp-of-ocfg-advance
  (implies (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
           (fn-scj-invp (fn-ocfg-owner (fn-ocfg-advance oc id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-advance) (fn-own-advance-result fn-ocfg-pin-set)))))

; The model machines' connection events.
(defthm fn-scj-invp-of-own-step-conn-event
  (implies (and (fn-scj-invp o fn-arena fn-cat)
                (member (car event) '(:open :open-peer :advance :close :feeds :feed-conn
                                      :feed-lost :feed-replay :tick :tick-peer :feed-octets)))
           (fn-scj-invp (fn-own-step o event fn-arena) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-step)
                                  (fn-own-open fn-own-open-peer fn-own-advance fn-own-close
                                   fn-own-feeds-reconfigure fn-own-feed-connect fn-own-feed-lost
                                   fn-own-feed-recover fn-own-tick fn-own-tick-peer
                                   fn-own-feed-reply fn-own-read fn-own-read-step fn-own-begin
                                   fn-own-store-step fn-own-complete fn-own-reopen fn-own-observe
                                   fn-own-declare-group fn-own-configure fn-own-take-submission
                                   fn-own-control-submit fn-own-bp-transit-submit
                                   fn-own-operator-submit fn-own-outcome fn-own-control-outcome
                                   fn-own-bp-transit-outcome fn-own-transit-outcome)))))

(defthm fn-scj-invp-of-ocfg-step-conn-event
  (implies (and (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (member (car event) '(:open :open-peer :advance :close :fault)))
           (fn-scj-invp (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step)
                                  (fn-ocfg-open fn-ocfg-open-peer fn-ocfg-advance fn-ocfg-close
                                   fn-ocfg-fault fn-ocfg-read fn-ocfg-read-step fn-ocfg-reconfigure
                                   fn-ocfg-complete fn-ocfg-pass)))))
