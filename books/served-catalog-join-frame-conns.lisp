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
(include-book "served-catalog-join-pinned")
(include-book "served-catalog-join-read")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

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
           (fn-scj-invp (cdr (fn-own-feed-reply o peer octets obs fn-arena)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reply)
                                  (fn-own-with-feeds fn-own-feed-put fn-feed-observe
                                   fn-own-feed-parse-response fn-own-feed-article fn-handle-bytes fn-own-feed-entry-of fn-own-feed-entry-feed fn-own-feed-inflight-msgid fn-feed-queue fn-own-feed-entry-record)))))

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

; -----------------------------------------------------------------------------
; Every connection pinned at or below the view's version
; (fn-scj-conns-versions-atmostp, books/served-catalog-join-pinned.lisp: the
; bound fn-scj-conns-pinp-at-host-finish asks).  The same arms keep it with
; the arm's own view version: open, open-peer, advance and reader-context pin
; at the view's version or the record's own; close and fault remove; the
; others keep the list.

(defthm fn-scj-versions-atmost-of-remove-conn
  (implies (fn-scj-conns-versions-atmostp conns n)
           (fn-scj-conns-versions-atmostp (fn-own-remove-conn id conns) n))
  :hints (("Goal" :induct (fn-own-remove-conn id conns))))

(defthm fn-scj-versions-atmost-of-replace-conn
  (implies (and (fn-scj-conns-versions-atmostp conns n)
                (<= (nfix (fn-own-conn-version conn)) (nfix n)))
           (fn-scj-conns-versions-atmostp (fn-own-replace-conn conn conns) n))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns))))

(defthm fn-scj-versions-atmost-find-conn
  (implies (and (fn-scj-conns-versions-atmostp conns n)
                (fn-own-find-conn id conns))
           (<= (nfix (fn-own-conn-version (fn-own-find-conn id conns))) (nfix n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :induct (fn-own-find-conn id conns))))

(defthm fn-scj-versions-atmost-of-cons
  (equal (fn-scj-conns-versions-atmostp (cons conn conns) n)
         (and (<= (nfix (fn-own-conn-version conn)) (nfix n))
              (fn-scj-conns-versions-atmostp conns n))))

; The bound over an owner at its own view's version.  Stated over this name
; so that the arms compose (an arm's view is rewritten before a lemma about
; its connections could match); fn-scj-versions-okp is the bound
; fn-scj-conns-pinp-at-host-finish asks, by definition.
(defun-nx fn-scj-versions-okp (o)
  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version (fn-own-view o))))

(local (in-theory (disable fn-scj-conns-versions-atmostp)))

(defthm fn-scj-versions-atmost-of-own-open
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-open o acfg))))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-open) (fn-served-open-group-indexed fn-own-body-limit fn-own-view-group-index fn-own-view-index fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-versions-atmost-of-own-open-peer
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-open-peer o peer cfg acfg))))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-open-peer) (fn-served-open-peer-group-indexed fn-own-peer-body-limit fn-cfg-peer-find fn-own-view-group-index fn-own-view-index fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-versions-atmost-of-own-close
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-close o id)))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-close) (fn-own-remove-conn fn-own-remove-subs)))))

(defthm fn-scj-versions-atmost-of-own-fault
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-fault o id))))
  :hints (("Goal" :in-theory (e/d (fn-own-fault) (fn-own-close fn-own-fault-effects)))))

(defthm fn-scj-versions-atmost-of-own-reader-context
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-reader-context o id cfg)))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-reader-context fn-own-set-conns)
                                  (fn-own-find-conn fn-own-replace-conn fn-auth-with-base
                                   fn-peer-open-session fn-cfgp fn-own-conn-make-group-indexed
                                   fn-scj-versions-atmost-of-replace-conn fn-scj-versions-atmost-find-conn))
           :use ((:instance fn-scj-versions-atmost-find-conn
                            (conns (fn-own-conns o)) (n (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scj-versions-atmost-of-replace-conn
                            (conns (fn-own-conns o)) (n (fn-own-view-version (fn-own-view o)))
                            (conn (fn-own-conn-make-group-indexed
                                   (fn-own-conn-id (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-version (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-frontier (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-auth-with-base
                                    (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))
                                    (fn-peer-open-session (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o)))
                                                          nil (fn-sn-node (fn-own-store o)) cfg))
                                   (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-observation (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-verdicts (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-index (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-group-index (fn-own-find-conn id (fn-own-conns o)))
                                   (fn-own-conn-control (fn-own-find-conn id (fn-own-conns o))))))))))

(defthm fn-scj-versions-atmost-of-own-advance-result
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-advance-result o id))))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-advance-result fn-own-set-conns) (fn-own-find-conn fn-own-replace-conn fn-own-conn-boundedp fn-auth-with-base fn-peer-with-base fn-post-make-session fn-nntp-set-cursor fn-nntp-open-session fn-own-view-group-index fn-own-view-index fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-versions-atmost-of-own-advance
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-advance o id)))
  :hints (("Goal" :in-theory (e/d (fn-own-advance) (fn-own-advance-result)))))

(defthm fn-scj-versions-atmost-of-acar-own-advance-result
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-acar-own-advance-result o id))))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-acar-own-advance-result fn-own-set-conns) (fn-own-find-conn fn-own-replace-conn fn-scar-conn-boundedp fn-acar-session-node fn-auth-with-base fn-peer-with-base fn-post-make-session fn-nntp-set-cursor fn-acar-open-session fn-own-view-group-index fn-own-view-index fn-own-view-archive fn-own-view-version)))))

(defthm fn-scj-versions-atmost-of-own-with-feeds
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-with-feeds o feeds)))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp fn-own-with-feeds) ()))))

(defthm fn-scj-versions-atmost-of-own-feeds-reconfigure
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-feeds-reconfigure o cfg)))
  :hints (("Goal" :in-theory (e/d (fn-own-feeds-reconfigure) (fn-own-with-feeds fn-own-feed-reconfigure)))))

(defthm fn-scj-versions-atmost-of-own-feed-connect
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-feed-connect o peer conn form)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-connect) (fn-own-with-feeds fn-own-feed-put)))))

(defthm fn-scj-versions-atmost-of-own-feed-lost
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-feed-lost o peer obs)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-lost) (fn-own-with-feeds fn-own-feed-lost-one)))))

(defthm fn-scj-versions-atmost-of-own-feed-recover
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (fn-own-feed-recover o peer entries)))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-recover) (fn-own-with-feeds fn-own-feed-put fn-feed-replay)))))

(defthm fn-scj-versions-atmost-of-own-feed-reply
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-feed-reply o peer octets obs fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-own-feed-reply) (fn-own-with-feeds fn-own-feed-put fn-feed-observe fn-own-feed-parse-response fn-own-feed-article fn-handle-bytes fn-own-feed-entry-of fn-own-feed-entry-feed fn-own-feed-inflight-msgid fn-feed-queue fn-own-feed-entry-record)))))

(defthm fn-scj-versions-atmost-of-own-tick
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-tick o obs))))
  :hints (("Goal" :in-theory (e/d (fn-own-tick) (fn-own-with-feeds fn-own-feed-tick)))))

(defthm fn-scj-versions-atmost-of-own-tick-peer
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-own-tick-peer o peer obs))))
  :hints (("Goal" :in-theory (e/d (fn-own-tick-peer) (fn-own-with-feeds fn-own-feed-tick-peer)))))

(defthm fn-scj-versions-atmost-of-acar-own-outcome
  (implies (fn-scj-versions-okp o)
           (fn-scj-versions-okp (cdr (fn-acar-own-outcome o id word))))
  :hints (("Goal" :use ((:instance fn-scj-versions-atmost-of-acar-own-advance-result
                            (o (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                                  (fn-own-next-id o) (fn-own-max-conns o)
                                  (if (equal (fn-own-pending o) id) nil (fn-own-pending o))
                                  (fn-own-ledger-field o) (fn-own-clock o) (fn-own-facts o)
                                  (fn-own-config o) (fn-own-queue o) nil
                                  (if (equal (fn-own-outcome-completion o word) :durable)
                                      (fn-own-feed-durable o (fn-own-inflight o))
                                    (fn-own-feeds o)) (fn-own-node-secret o) (fn-own-refused o)))))
           :in-theory (e/d (fn-scj-versions-okp fn-acar-own-outcome) (fn-acar-own-advance-result fn-own-outcome-completion fn-own-feed-durable fn-served-post-outcome fn-own-post-rendering fn-served-make-conn-group-indexed)))))

(defthm fn-scj-versions-atmost-of-ocfg-open
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open) (fn-own-open fn-own-reader-context fn-own-find-conn fn-ocfg-pin-add fn-auth-config-with-accounts)))))

(defthm fn-scj-versions-atmost-of-ocfg-open-peer
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (cdr (fn-ocfg-open-peer oc peer acfg)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open-peer fn-ocfg-with-owner) (fn-own-open-peer fn-auth-config-with-accounts)))))

(defthm fn-scj-versions-atmost-of-ocfg-close
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (fn-ocfg-close oc id))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-close) (fn-own-close fn-ocfg-pin-remove)))))

(defthm fn-scj-versions-atmost-of-ocfg-fault
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (cdr (fn-ocfg-fault oc id)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-fault) (fn-own-fault fn-ocfg-pin-remove)))))

(defthm fn-scj-versions-atmost-of-ocfg-advance
  (implies (fn-scj-versions-okp (fn-ocfg-owner oc))
           (fn-scj-versions-okp (fn-ocfg-owner (fn-ocfg-advance oc id))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-advance) (fn-own-advance-result fn-ocfg-pin-set)))))


; The model machines' connection events keep the bound.
(defthm fn-scj-versions-atmost-of-own-step-conn-event
  (implies (and (fn-scj-versions-okp o)
                (member (car event) '(:open :open-peer :advance :close :feeds :feed-conn
                                      :feed-lost :feed-replay :tick :tick-peer :feed-octets)))
           (fn-scj-versions-okp (fn-own-step o event fn-arena)))
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

(defthm fn-scj-versions-atmost-of-ocfg-step-conn-event
  (implies (and (fn-scj-versions-okp (fn-ocfg-owner oc))
                (member (car event) '(:open :open-peer :advance :close :fault)))
           (fn-scj-versions-okp (fn-ocfg-owner (fn-ocfg-step oc event fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step)
                                  (fn-ocfg-open fn-ocfg-open-peer fn-ocfg-advance fn-ocfg-close
                                   fn-ocfg-fault fn-ocfg-read fn-ocfg-read-step fn-ocfg-reconfigure
                                   fn-ocfg-complete fn-ocfg-pass)))))

; -----------------------------------------------------------------------------
; The host's served read keeps the bound.  A read moves a served connection's
; pin nowhere or to its live view (books/served.lisp fn-served-step-pin-is-
; old-or-live, for the reference step); the carried span the host runs does
; the same, so a served connection whose pin and live view are at or below N
; stays so, layer by layer below (dispatch, byte, span), and the record the
; read writes back is pinned at or below the owner's view version.

(defun-nx fn-scj-sconn-atmostp (sconn n)
  (and (<= (nfix (fn-served-pinned-version (fn-served-conn-pinned sconn))) (nfix n))
       (implies (fn-served-conn-live sconn)
                (<= (nfix (fn-served-live-version (fn-served-conn-live sconn))) (nfix n)))))

(defthm fn-scj-sconn-atmostp-of-scar-dispatch-core
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn (fn-scar-dispatch-core conn event live trie arts fn-arena))
                                 n))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch-core fn-scj-sconn-atmostp
                                fn-served-result-conn-of-fn-served-make-result
                                fn-served-conn-fields-of-make-conn-live)
                              (theory 'minimal-theory)))))

(defthm fn-scj-sconn-atmostp-of-repin
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-repin conn) n))
  :hints (("Goal" :in-theory (e/d (fn-served-repin fn-scj-sconn-atmostp)
                                  (fn-served-make-conn-live fn-served-repin-session
                                   fn-served-pinned-make fn-served-pinned-version)))))

(defthm fn-scj-sconn-atmostp-of-with-wire
  (equal (fn-scj-sconn-atmostp (fn-served-conn-with-wire conn wire) n)
         (fn-scj-sconn-atmostp conn n))
  :hints (("Goal" :in-theory (e/d (fn-scj-sconn-atmostp) (fn-served-conn-with-wire)))))

(defthm fn-scj-sconn-atmostp-of-scar-dispatch
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn (fn-scar-dispatch conn event live trie arts fn-arena))
                                 n))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-dispatch fn-scj-sconn-atmostp-of-scar-dispatch-core
                                fn-scj-sconn-atmostp-of-repin fn-scj-sconn-atmostp-of-with-wire
                                fn-served-result-conn-of-fn-served-make-result)
                              (theory 'minimal-theory)))))

(defthm fn-scj-sconn-atmostp-of-scar-dispatch-events
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn
                                  (fn-scar-dispatch-events conn events live trie arts fn-arena))
                                 n))
  :hints (("Goal" :induct (fn-scar-dispatch-events conn events live trie arts fn-arena)
           :in-theory (union-theories
                       '(fn-scar-dispatch-events fn-scj-sconn-atmostp-of-scar-dispatch
                         fn-served-result-conn-of-fn-served-make-result)
                       (theory 'minimal-theory)))))

(defthm fn-scj-sconn-atmostp-of-scar-feed-byte
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn (fn-scar-feed-byte conn byte live trie arts fn-arena))
                                 n))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-scar-feed-byte fn-scj-sconn-atmostp-of-scar-dispatch-events
                                fn-scj-sconn-atmostp-of-with-wire)
                              (theory 'minimal-theory)))))

(defthm fn-scj-sconn-atmostp-of-scar-feed-span
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn
                                  (fn-served-counted-result
                                   (fn-scar-feed-span conn i end live trie arts fn-octets fn-arena)))
                                 n))
  :hints (("Goal" :induct (fn-scar-feed-span conn i end live trie arts fn-octets fn-arena)
           :in-theory (e/d (fn-scar-feed-span fn-served-counted-result fn-served-counted-make)
                           (fn-scj-sconn-atmostp fn-scar-feed-byte fn-served-submission
                            fn-scar-feed-span-is-feed-counted
                            fn-served-closed-wirep fn-served-haltedp)))))

(local (defthm fn-scj-fc-counted-result-of-make
  (equal (fn-served-counted-result (fn-served-counted-make n r)) r)
  :hints (("Goal" :in-theory (enable fn-served-counted-result fn-served-counted-make fn-ag-car fn-ag-cdr)))))

(defthm fn-scj-sconn-atmostp-of-scar-step-span-fast
  (implies (fn-scj-sconn-atmostp conn n)
           (fn-scj-sconn-atmostp (fn-served-result-conn
                                  (fn-served-counted-result
                                   (fn-scar-step-span-fast conn i end live trie arts fn-octets fn-arena)))
                                 n))
  :hints (("Goal" :in-theory (e/d (fn-scar-step-span-fast fn-scar-step-span-core)
                                  (fn-scj-sconn-atmostp fn-scar-feed-span fn-served-closed-wirep
                                   fn-scar-feed-span-is-feed-counted
                                   fn-scar-step-span-core-is-step-counted-core
                                   fn-scar-step-span-fast-is-step-counted-fast
                                   fn-wire-fast-statep)))))

; The served connection the owner builds: the record's pin and the view.
(defthm fn-scj-sconn-atmostp-of-tls-served-conn
  (implies (and (<= (nfix (fn-own-conn-version conn)) (nfix n))
                (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix n)))
           (fn-scj-sconn-atmostp (fn-own-tls-served-conn o conn) n))
  :hints (("Goal" :in-theory (e/d (fn-scj-sconn-atmostp fn-own-tls-served-conn fn-own-served-conn)
                                  (fn-served-make-conn-live fn-own-conn-live-session)))))

; The record the read writes back.
(defthm fn-scj-versions-atmost-of-scar-finish-read
  (implies (and (fn-scj-conns-versions-atmostp (fn-own-conns o) n)
                (<= (nfix (fn-served-pinned-version (fn-served-conn-pinned (fn-served-result-conn result))))
                    (nfix n)))
           (fn-scj-conns-versions-atmostp (fn-own-conns (cdr (fn-scar-finish-read o conn result live))) n))
  :hints (("Goal" :in-theory (e/d (fn-scar-finish-read fn-own-set-conns fn-own-enqueue)
                                  (fn-scar-conn-boundedp fn-own-conn-make-group-indexed
                                   fn-own-replace-conn fn-own-remove-conn fn-served-pinned-version
                                   fn-served-conn-pinned fn-served-result-conn nfix
                                   fn-scj-versions-atmost-of-replace-conn))
           :use ((:instance fn-scj-versions-atmost-of-replace-conn
                            (conns (fn-own-conns o))
                            (conn (let ((sconn (fn-served-result-conn result)))
                                    (fn-own-conn-make-group-indexed
                                     (fn-own-conn-id conn)
                                     (fn-served-pinned-version (fn-served-conn-pinned sconn))
                                     (fn-served-pinned-frontier (fn-served-conn-pinned sconn))
                                     (fn-served-conn-wire sconn) (fn-served-conn-session sconn)
                                     (fn-served-conn-archive sconn)
                                     (fn-own-conn-config conn) (fn-own-conn-observation conn)
                                     (fn-served-conn-verdicts sconn) (fn-served-conn-index sconn)
                                     (fn-served-conn-group-index sconn) (fn-served-conn-control sconn)))))))))

(defthm fn-scj-sconn-atmostp-pinned
  (implies (fn-scj-sconn-atmostp sconn n)
           (<= (nfix (fn-served-pinned-version (fn-served-conn-pinned sconn))) (nfix n)))
  :hints (("Goal" :in-theory (enable fn-scj-sconn-atmostp))))

; The host's carried read at an owner whose view and pins are at or below N
; leaves every pin at or below N and the view as it was.
(defthm fn-scj-versions-atmost-of-scar-own-read-span
  (implies (and (fn-scj-conns-versions-atmostp (fn-own-conns o) n)
                (<= (nfix (fn-own-view-version (fn-own-view o))) (nfix n)))
           (let ((o2 (fn-own-tls-result-owner (fn-scar-own-read-span o id i end fn-octets fn-arena))))
             (and (fn-scj-conns-versions-atmostp (fn-own-conns o2) n)
                  (equal (fn-own-view o2) (fn-own-view o)))))
  :hints (("Goal" :cases ((fn-own-find-conn id (fn-own-conns o)))
           :in-theory (e/d (fn-scar-own-read-span fn-own-tls-result-owner fn-own-tls-make-result)
                           (fn-scar-step-span-fast-is-step-counted-fast
                            fn-scar-own-read-span-is-own-read-tls-prefix
                            fn-scar-finish-read fn-scar-step-span-fast
                            fn-own-tls-served-conn fn-scj-sconn-atmostp
                            fn-scj-versions-atmost-find-conn fn-scj-sconn-atmostp-pinned nfix
                            fn-scj-versions-atmost-of-scar-finish-read
                            fn-scj-sconn-atmostp-of-tls-served-conn
                            fn-scj-sconn-atmostp-of-scar-step-span-fast)))
          ("Subgoal 1" :use ((:instance fn-scj-versions-atmost-find-conn (conns (fn-own-conns o)))
                             (:instance fn-scj-sconn-atmostp-of-tls-served-conn
                                        (conn (fn-own-find-conn id (fn-own-conns o))))
                             (:instance fn-scj-sconn-atmostp-of-scar-step-span-fast
                                        (conn (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
                                        (live (fn-sn-node (fn-own-store o)))
                                        (trie (fn-own-view-index (fn-own-view o)))
                                        (arts (fn-state-articles (fn-own-view-archive (fn-own-view o)))))
                             (:instance fn-scj-sconn-atmostp-pinned
                                        (sconn (fn-served-result-conn (fn-served-counted-result
                                         (fn-scar-step-span-fast
                                          (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o)))
                                          i end (fn-sn-node (fn-own-store o))
                                          (fn-own-view-index (fn-own-view o))
                                          (fn-state-articles (fn-own-view-archive (fn-own-view o)))
                                          fn-octets fn-arena)))))
                             (:instance fn-scj-versions-atmost-of-scar-finish-read
                                        (conn (fn-own-find-conn id (fn-own-conns o)))
                                        (live (fn-sn-node (fn-own-store o)))
                                        (result (fn-served-counted-result
                                         (fn-scar-step-span-fast
                                          (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o)))
                                          i end (fn-sn-node (fn-own-store o))
                                          (fn-own-view-index (fn-own-view o))
                                          (fn-state-articles (fn-own-view-archive (fn-own-view o)))
                                          fn-octets fn-arena))))))))

; The function the host calls under the catalog (fn-scr-own-read-span), at
; an owner carrying the invariant.
(defthm fn-scj-versions-atmost-of-scr-own-read-span
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp o fn-arena fn-cat)
                (fn-scar-view-indexedp o)
                (fn-scj-versions-okp o))
           (fn-scj-versions-okp (fn-own-tls-result-owner
                                 (fn-scr-own-read-span o id i end fn-octets fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-scj-versions-okp)
                                  (fn-scr-own-read-span fn-scar-own-read-span
                                   fn-scj-versions-atmost-of-scar-own-read-span))
           :use ((:instance fn-scr-own-read-span-is-scar-own-read-span)
                 (:instance fn-scj-invp-gives-owner-catalogp)
                 (:instance fn-scj-versions-atmost-of-scar-own-read-span
                            (n (fn-own-view-version (fn-own-view o))))))))

; KEYSTONE (the read entry, fn-orr-read-span: host/owner-host.lisp
; fn-owner-chunk-span).  With a capture held the read is at the captured
; view, and a GROUP re-pins to that view; the bound holds after the read when
; the captured view is live over the catalog (as the invariant's read
; keystone fn-scj-invp-of-orr-read-span asks) and at or below the working
; view's version (a capture is a view the owner held).
(defthm fn-scj-versions-atmost-of-orr-read-span
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scj-versions-okp (fn-ocfg-owner oc))
                (implies (consp views)
                         (and (fn-scj-live-okp (car views) fn-arena fn-cat)
                              (fn-scj-trie-indexedp (car views))
                              (<= (nfix (fn-own-view-version (car views)))
                                  (nfix (fn-own-view-version (fn-own-view (fn-ocfg-owner oc))))))))
           (fn-scj-versions-okp (fn-ocfg-owner (fn-own-tls-result-owner
                                                (fn-orr-read-span oc views id i end fn-octets fn-arena fn-cat)))))
  :hints (("Goal" :cases ((consp views))
           :in-theory (union-theories '(fn-scj-orr-read-span-owner fn-scj-scr-ocfg-read-span-owner)
                                      (theory 'minimal-theory)))
          ("Subgoal 2" :use ((:instance fn-scj-versions-atmost-of-scr-own-read-span (o (fn-ocfg-owner oc)))))
          ("Subgoal 1"
           :in-theory (union-theories '(fn-scj-orr-read-span-owner fn-scj-scr-ocfg-read-span-owner
                                        fn-scj-versions-okp fn-scj-trie-indexedp-is-view-indexedp)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-invp-conns (o (fn-ocfg-owner oc)))
                 (:instance fn-orr-with-view-fields (v (car views)))
                 (:instance fn-orr-with-view-fields
                            (oc (fn-own-tls-result-owner
                                 (fn-scr-ocfg-read-span (fn-ocfg-with-view oc (car views))
                                                        id i end fn-octets fn-arena fn-cat)))
                            (v (fn-own-view (fn-ocfg-owner oc))))
                 (:instance fn-scr-own-read-span-is-scar-own-read-span
                            (o (fn-ocfg-owner (fn-ocfg-with-view oc (car views)))))
                 (:instance fn-scj-owner-catalogp-of-conns-and-live
                            (o (fn-ocfg-owner (fn-ocfg-with-view oc (car views)))))
                 (:instance fn-scj-versions-atmost-of-scar-own-read-span
                            (o (fn-ocfg-owner (fn-ocfg-with-view oc (car views))))
                            (n (fn-own-view-version (fn-own-view (fn-ocfg-owner oc)))))))))
