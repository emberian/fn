; served-catalog-join-frame.lisp -- the owner steps that do not complete an
; article keep the catalog invariant with the catalog untouched (lane
; sca-join-4, 2026-09-27; PRF-302, step 4 of the join's discharge).
;
; The question step 4 had to settle: fn-ctl-refresh-visible's third arm
; recomputes the visible list when only the verdicts changed (raw unchanged),
; and nothing updates the catalog there.  Could an idle refresh move the
; owner's view while the catalog stays put -- a served-path divergence?
;
; No, and this book says why as theorems.  The view carries the store's
; acceptance articles and verdicts (VV, fn-scj-vvp; every idle refresh
; installs it, fn-scj-vvp-of-idle-refresh), and under VV the refresh takes
; the FIRST arm: the visible list stays (fn-scj-refresh-under-vvp).  So the
; view's articles move only when the store's acceptance articles or verdicts
; move, and they move together, only at a completion that accepts an
; article: every other completion keeps both (the identity completion of a
; keyring snapshot or a standalone verdict adds no verdict pair,
; fn-scj-identity-finish-keeps-verdicts; the others keep the node's
; articles).  The host routes every article completion through the
; catalog's T4-then-T2 (host/owner-host.lisp fn-owner-finish-submission,
; fn-owner-finish-identity; host/native/owner.lisp sets those callbacks
; exactly when ACL2 answered a seal), which step 2 covers.

(in-package "ACL2")

(include-book "served-catalog-join-conns")

; -----------------------------------------------------------------------------
; An identity completion that is not a signed composite adds no verdict.

(defthm fn-scj-identity-step-verdicts-of-snapshot-or-verdict
  (implies (and (or (fn-stxe-p r) (fn-stxk-p r))
                (not (fn-hstxa-p r)))
           (equal (fn-stxk-context-verdicts (fn-replay-identity-step ctx r))
                  (fn-stxk-context-verdicts ctx)))
  :hints (("Goal" :in-theory (e/d (fn-replay-identity-step fn-replay-identity-wire
                                   fn-stxk-apply-snapshot fn-stxk-apply-verdict fn-stxk-fault fn-stxk-context
                                   fn-stxk-context-verdicts)
                                  (fn-stxe-p fn-stxk-p fn-hstxa-p fn-stxk-find)))))

(defthm fn-scj-identity-context-verdicts
  (equal (fn-stxk-context-verdicts (fn-sn-identity-context s)) nil)
  :hints (("Goal" :in-theory (enable fn-sn-identity-context fn-stxk-context fn-stxk-context-verdicts))))

(defthm fn-scj-identity-finish-keeps-verdicts
  (implies (and (or (fn-stxe-p record) (fn-stxk-p record))
                (not (fn-hstxa-p record)))
           (equal (fn-sn-verdicts (fn-sn-finish-identity s files record node))
                  (fn-sn-verdicts s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish-identity fn-replay-verdict-pairs)
                                  (fn-replay-identity-step fn-sn-make-v6)))))

; -----------------------------------------------------------------------------
; The refresh under VV, field by field.

(defthm fn-scj-refresh-view-under-vvp
  (implies (and (fn-scj-vvp o) (fn-own-store-idlep (fn-own-store o)))
           (let* ((s (fn-own-store o)) (view (fn-own-view o))
                  (arts (fn-state-articles (fn-own-view-archive view))))
             (equal (fn-own-view (fn-own-refresh o))
                    (fn-own-view-make-visible
                     (len (fn-sf-records (fn-sn-files s)))
                     (fn-sf-frontier (fn-sn-files s))
                     (fn-ctl-visible-state-of (fn-node-acceptance (fn-sn-node s)) arts)
                     (fn-own-view-verdicts view)
                     (fn-own-view-index view)
                     (fn-gidx-refresh (fn-own-view-group-index view) arts arts)
                     (fn-own-view-withdrawals view)
                     (fn-own-view-raw view)
                     (fn-own-view-withdrawn view)
                     (fn-sn-keyring-snapshots s)))))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-scj-vvp fn-ctl-refresh-visible
                                   fn-ctl-refresh-withdrawals fn-ctl-refresh-withdrawn
                                   fn-midx-refresh)
                                  (fn-own-store-idlep fn-gidx-refresh fn-ctl-visible-articles
                                   fn-ctl-visible-add fn-ctl-articles-withdrawals fn-ctl-prepend
                                   fn-ctl-visible-state-of fn-own-view-make-visible)))))

(defthm fn-scj-take-append-nthcdr
  (implies (true-listp xs)
           (equal (append (fn-own-take n xs) (nthcdr n xs)) xs))
  :hints (("Goal" :induct (fn-own-take n xs) :in-theory (enable fn-own-take))))

(defthm fn-scj-take-of-len
  (implies (true-listp xs) (equal (fn-own-take (len xs) xs) xs))
  :hints (("Goal" :induct (len xs) :in-theory (enable fn-own-take))))

; The refreshed view is the live view again: its archive holds the same
; articles (under VV), its version is the history's length (every row's
; sequence is below it), its trie is the old one and its group index the
; old one or its build.  The one fact not read off the old view: the
; refreshed archive is a projection (its groups and next numbers are the
; store's acceptance's, which a configuration record may have changed).
(defthm fn-scj-live-okp-of-refresh
  (implies (and (fn-scj-vvp o)
                (fn-own-store-idlep (fn-own-store o))
                (fn-scj-joinp (fn-own-view o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat)
                (fn-scar-view-indexedp o)
                (<= (nfix (fn-own-view-version (fn-own-view o)))
                    (len (fn-sf-records (fn-sn-files (fn-own-store o)))))
                (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-refresh o)))))
           (fn-scj-live-okp (fn-own-view (fn-own-refresh o)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                   fn-scr-catalogp fn-scj-joinp fn-gidx-refresh
                                   fn-gidx-pin-correspondencep fn-scar-view-indexedp)
                                  (fn-own-refresh fn-own-store-idlep fn-scr-view-of
                                   fn-cat-view-articles fn-ctl-visible-state-of
                                   fn-own-view-make-visible fn-midx-correspondencep
                                   fn-nntp-projectionp fn-gidx-build fn-cnx-freshp))
           :use ((:instance fn-scj-view-of-when-seqs-below
                            (version (fn-own-view-version (fn-own-view o))))
                 (:instance fn-scj-view-of-when-seqs-below
                            (version (len (fn-sf-records (fn-sn-files (fn-own-store o))))))
                 (:instance fn-scj-seqs-below-monotone
                            (c fn-cat) (v1 (fn-own-view-version (fn-own-view o)))
                            (v2 (len (fn-sf-records (fn-sn-files (fn-own-store o))))))))))

(defthm fn-scj-refresh-keeps-conns
  (equal (fn-own-conns (fn-own-refresh o)) (fn-own-conns o))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of fn-own-view-make-visible)))))

; KEYSTONE (the refresh keeps the invariant with the catalog untouched).  A
; refresh whose store has appended, since the view, only records that load
; no catalog row keeps fn-scj-invp: not idle it is the identity; idle, VV
; makes it keep the visible list (the first arm of fn-ctl-refresh-visible),
; the history it has seen grows by row-less records only, the connections
; are untouched and the refreshed view is live over the catalog.
(defthm fn-scj-invp-of-refresh
  (let ((records (fn-sf-records (fn-sn-files (fn-own-store o))))
        (version (fn-own-view-version (fn-own-view o))))
    (implies (and (fn-scj-invp o fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (true-listp records)
                  (natp version)
                  (<= version (len records))
                  (fn-scj-no-rowsp (nthcdr version records))
                  (fn-nntp-projectionp (fn-own-view-archive (fn-own-view (fn-own-refresh o)))))
             (fn-scj-invp (fn-own-refresh o) fn-arena fn-cat)))
  :hints (("Goal" :cases ((fn-own-store-idlep (fn-own-store o))))
          ("Subgoal 1" :in-theory (e/d (fn-scj-invp fn-scj-joinp)
                                       (fn-own-refresh fn-own-store-idlep fn-scj-live-okp
                                        fn-scj-conns-pinp fn-scj-rows-invp fn-scj-vvp
                                        fn-own-view-make-visible fn-cat-view-articles
                                        fn-ctl-visible-state-of fn-gidx-refresh
                                        fn-scj-take-append-nthcdr))
           :use ((:instance fn-scj-vvp-of-idle-refresh)
                 (:instance fn-scj-refresh-under-vvp)
                 (:instance fn-scj-live-okp-of-refresh)
                 (:instance fn-scj-take-append-nthcdr
                            (n (fn-own-view-version (fn-own-view o)))
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-scj-rows-invp-of-no-rows
                            (c fn-cat)
                            (events (fn-own-take (fn-own-view-version (fn-own-view o))
                                                 (fn-sf-records (fn-sn-files (fn-own-store o)))))
                            (extra (nthcdr (fn-own-view-version (fn-own-view o))
                                           (fn-sf-records (fn-sn-files (fn-own-store o))))))
                 (:instance fn-scj-seqs-below-monotone
                            (c fn-cat) (v1 (fn-own-view-version (fn-own-view o)))
                            (v2 (len (fn-sf-records (fn-sn-files (fn-own-store o))))))))))
