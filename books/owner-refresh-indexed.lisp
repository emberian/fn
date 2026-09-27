; fn: the owner's refresh over the Store's event index (lane post-alloc-2,
; 2026-09-27).
;
; books/owner.lisp fn-own-refresh walks the Store's whole history on every
; refresh that sees an acceptance: `fn-ctl-refresh-withdrawals' finds the new
; article's row (and a cancel's target's) by `fn-ctl-row-event', and the
; view's record count is `(len records)'.  fn-own-refresh-ix is the same
; refresh reading both from the Store's event index `fn-sn-event-index':
; `fn-ctl-refresh-withdrawals-ix' (books/control-visible-indexed.lisp) and
; `fn-cei-count'.  Per refresh: one Message-ID trie walk per lookup and one
; sequence-trie read, instead of N events.
;
; KEYSTONE fn-own-refresh-ix-is-own-refresh: under the two facts the owner's
; Store carries, `fn-sn-statep' (every history is Store events: the rows'
; agreement, fn-ctl-rows-okp-of-sf-state) and `fn-ceis-indexedp' (the index
; is the index of the history; established at the host's open and preserved
; by every installed owner transition, books/owner-store-indexed.lisp
; fn-osi-live-owner-store-is-indexed), the twin is the reference.
;
; Host path: the refreshes an accepted POST reaches that see its acceptance
; are the completions, books/owner-commit-carried.lisp fn-ccar-own-complete-
; enabled (host/owner-host.lisp fn-owner-finish-submission ->
; fn-ccar-own-finish) and fn-ccar-ocfg-complete (host fn-owner-finish, the
; signed composite's completion).  Those call fn-own-refresh today; the
; one-line change there is fn-own-refresh -> fn-own-refresh-ix, with this
; keystone and the finish's preservation of both premises
; (fn-sn-finish-preserves-state, fn-ceis-finish-preserves-indexed).
(in-package "ACL2")
(include-book "owner")
(include-book "consumer-event-index-store-invariants")
(include-book "control-visible-indexed")
(include-book "store-node-invariants-base")

(defun fn-own-refresh-ix (o)
  (declare (xargs :guard t))
  (let ((s (fn-own-store o)))
    (if (fn-own-store-idlep s)
        (let* ((old-view (fn-own-view o))
               (acceptance (fn-node-acceptance (fn-sn-node s)))
               (raw (fn-state-articles acceptance))
               (old-raw (fn-own-view-raw old-view))
               (verdicts (fn-sn-verdicts s))
               (withdrawals (fn-ctl-refresh-withdrawals-ix
                             raw old-raw (fn-own-view-withdrawals old-view)
                             verdicts (fn-sf-records (fn-sn-files s))
                             (fn-sn-event-index s)
                             (fn-sn-config-history s)))
               (old-visible (fn-state-articles (fn-own-view-archive old-view)))
               (visible (fn-ctl-refresh-visible
                         raw old-raw old-visible withdrawals
                         (fn-own-view-verdicts old-view) verdicts))
               (archive (fn-ctl-visible-state-of acceptance visible))
               (withdrawn (fn-ctl-refresh-withdrawn
                           raw old-raw visible old-visible
                           (fn-own-view-withdrawn old-view)))
               (index (fn-midx-refresh
                       (fn-own-view-index old-view) old-visible visible)))
          (fn-own-make s
                     (fn-own-view-make-visible
                      (fn-cei-count (fn-sn-event-index s))
                      (fn-sf-frontier (fn-sn-files s))
                      archive verdicts index
                      (fn-gidx-refresh (fn-own-view-group-index old-view)
                                       old-visible visible)
                      withdrawals raw withdrawn
                      (fn-sn-keyring-snapshots s))
                     (fn-own-conns o) (fn-own-next-id o) (fn-own-max-conns o)
                     (fn-own-pending o) (fn-own-ledger o) (fn-own-clock o)
                     (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
                     (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))
      o)))

; The two premises the refresh reads, from the Store's.
(defthm fn-orix-store-rows-agree
  (implies (fn-sn-statep s)
           (fn-ctl-rows-okp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (disable fn-sn-statep fn-sf-statep fn-ctl-rows-okp))))

(defthm fn-orix-store-index-corresponds
  (implies (fn-ceis-indexedp s)
           (fn-cei-correspondencep (fn-sn-event-index s)
                                   (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (enable fn-ceis-indexedp))))

; KEYSTONE: the owner's refresh over the index is the owner's refresh.
; Subject: fn-own-refresh-ix, for the completions of
; books/owner-commit-carried.lisp (see the header).
(defthm fn-own-refresh-ix-is-own-refresh
  (implies (and (fn-sn-statep (fn-own-store o))
                (fn-ceis-indexedp (fn-own-store o)))
           (equal (fn-own-refresh-ix o) (fn-own-refresh o)))
  :hints (("Goal" :use ((:instance fn-orix-store-rows-agree (s (fn-own-store o)))
                        (:instance fn-orix-store-index-corresponds (s (fn-own-store o)))
                        (:instance fn-cei-count-of-correspondence
                                   (index (fn-sn-event-index (fn-own-store o)))
                                   (events (fn-sf-records (fn-sn-files (fn-own-store o))))))
           :in-theory (e/d (fn-own-refresh-ix fn-own-refresh)
                           (fn-sn-statep fn-ceis-indexedp fn-cei-correspondencep
                            fn-ctl-rows-okp fn-cei-count
                            fn-orix-store-rows-agree fn-orix-store-index-corresponds
                            fn-cei-count-of-correspondence
                            fn-ctl-refresh-withdrawals fn-ctl-refresh-withdrawals-ix
                            fn-ctl-refresh-visible fn-ctl-visible-state-of
                            fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                            fn-own-make fn-own-view-make-visible)))))

;; For the completions (books/owner-commit-carried.lisp
;; fn-ccar-own-complete-enabled refreshes the owner over the finished Store):
;; the finish keeps both premises (fn-sn-finish-preserves-state,
;; fn-ceis-finish-preserves-indexed), so over a Store that has them the
;; completion's refresh may read the index.  Under a completion gate
;; fn-sn-statep is already forward (fn-ccar-completion-enabled-implies-statep);
;; fn-ceis-indexedp is what the owner's relation adds
;; (books/owner-store-indexed.lisp fn-osi-live-owner-store-is-indexed).
(defthm fn-own-refresh-ix-of-finished-store-is-own-refresh
  (implies (and (fn-sn-statep s) (fn-ceis-indexedp s))
           (equal (fn-own-refresh-ix
                   (fn-own-make (fn-sn-finish s) view conns next-id max-conns pending
                                ledger clock facts config queue inflight feeds
                                node-secret refused))
                  (fn-own-refresh
                   (fn-own-make (fn-sn-finish s) view conns next-id max-conns pending
                                ledger clock facts config queue inflight feeds
                                node-secret refused))))
  :hints (("Goal" :use ((:instance fn-own-refresh-ix-is-own-refresh
                                   (o (fn-own-make (fn-sn-finish s) view conns next-id
                                                   max-conns pending ledger clock facts
                                                   config queue inflight feeds
                                                   node-secret refused)))
                        fn-sn-finish-preserves-state
                        fn-ceis-finish-preserves-indexed)
           :in-theory (e/d (fn-own-store-of-fn-own-make)
                           (fn-own-refresh-ix-is-own-refresh fn-sn-finish-preserves-state
                            fn-ceis-finish-preserves-indexed fn-own-refresh-ix
                            fn-own-refresh fn-sn-finish fn-sn-statep fn-ceis-indexedp
                            fn-own-make)))))

(in-theory (disable fn-own-refresh-ix))
