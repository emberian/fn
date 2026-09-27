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

; The same readers over the kernel state FILES instead of its history list:
; the history is held as a snoc-list (books/store-files.lisp), so reading
; (fn-sf-records files) conses it back; each -fx is its -ix with RECORDS =
; (fn-sf-records files) (its logic, by definition), and executes that read
; only on the arms that walk the history (a Message-ID the index does not
; answer, the recovery arm).  The POST's refresh reads none.
(defun fn-ctl-row-event-fx (m files index)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-row-event-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-row-event-ix m (fn-sf-records files) index)
       :exec (if (stringp m)
                 (let ((rs (fn-cei-msgid-records m index)))
                   (if (consp rs)
                       (let* ((r (car rs))
                              (e (fn-cei-get (fn-record-sequence r) index)))
                         (if (and e
                                  (equal (fn-ctl-event-row e) r)
                                  (not (member-equal r (cdr rs))))
                             e
                           (fn-ctl-row-event m (fn-sf-records files))))
                     nil))
               (fn-ctl-row-event m (fn-sf-records files)))))

(defun fn-ctl-row-control-fx (msgid files index)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-row-control-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-row-control-ix msgid (fn-sf-records files) index)
       :exec (let ((e (fn-ctl-row-event-fx msgid files index)))
               (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))))

(defun fn-ctl-article-plan-fx (a verdicts files index configs)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-article-plan-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-article-plan-ix a verdicts (fn-sf-records files) index configs)
       :exec (if (consp a)
                 (let* ((m (fn-article-msgid a))
                        (e (fn-ctl-row-event-fx m files index))
                        (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
                        (target (fn-ctl-control-target control)))
                   (if target
                       (fn-ctl-w-with-tlocks
                        (fn-ctl-withdrawal-plan
                         m (fn-ctl-lookup-verdict m verdicts) target
                         (fn-ctl-control-keys control)
                         (fn-ctl-config-at (fn-store-event-txid e) configs))
                        (fn-ctl-control-locks (fn-ctl-row-control-fx target files index)))
                     nil))
               nil)))

(defun fn-ctl-refresh-withdrawals-fx (new old ws verdicts files index configs)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-ctl-refresh-withdrawals-ix fn-ctl-article-withdrawals-ix fn-ctl-resolve-tlocks-ix)
                                                        (fn-cei-msgid-records fn-cei-get fn-ctl-row-event fn-ctl-event-row fn-held-facts fn-hf-control fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks fn-ctl-control-locks fn-ctl-lookup-verdict fn-ctl-config-at fn-ctl-articles-withdrawals fn-ctl-set-tlocks fn-ctl-targets-p fn-ctl-prepend fn-sf-records fn-ctl-control-target fn-ctl-control-keys fn-store-event-txid fn-article-msgid fn-ctl-withdrawalp))))))
  (mbe :logic (fn-ctl-refresh-withdrawals-ix new old ws verdicts (fn-sf-records files)
                                             index configs)
       :exec (cond ((equal new old) ws)
                   ((and (consp new) (equal (cdr new) old))
                    (fn-ctl-prepend
                     (let ((plan (fn-ctl-article-plan-fx (car new) verdicts files
                                                         index configs)))
                       (if (fn-ctl-withdrawalp plan) (list plan) nil))
                     (if (consp (car new))
                         (let ((m (fn-article-msgid (car new))))
                           (if (fn-ctl-targets-p ws m)
                               (fn-ctl-set-tlocks ws m (fn-ctl-control-locks
                                                        (fn-ctl-row-control-fx m files index)))
                             ws))
                       ws)))
                   (t (fn-ctl-articles-withdrawals new verdicts (fn-sf-records files)
                                                   configs)))))

(defun fn-own-refresh-ix (o)
  (declare (xargs :guard t))
  (let ((s (fn-own-store o)))
    (if (fn-own-store-idlep s)
        (let* ((old-view (fn-own-view o))
               (acceptance (fn-node-acceptance (fn-sn-node s)))
               (raw (fn-state-articles acceptance))
               (old-raw (fn-own-view-raw old-view))
               (verdicts (fn-sn-verdicts s))
               (withdrawals (fn-ctl-refresh-withdrawals-fx
                             raw old-raw (fn-own-view-withdrawals old-view)
                             verdicts (fn-sn-files s)
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
                     (fn-own-pending o) (fn-own-ledger-field o) (fn-own-clock o)
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
           :in-theory (e/d (fn-own-refresh-ix fn-own-refresh
                            fn-ctl-refresh-withdrawals-fx)
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

; -----------------------------------------------------------------------------
; The completions the host calls, over the indexed refresh (post-alloc-2).
; Each is its books/owner-commit-carried.lisp reference with fn-own-refresh
; replaced by fn-own-refresh-ix: the finished Store's new article's row and
; the view's count come from the event index, and the history (a snoc-list,
; books/store-files.lisp) is not consed back.  Equal to the reference under
; fn-ceis-indexedp of the owner's Store, which every owner the host holds
; carries (books/owner-store-indexed.lisp fn-osi-live-owner-store-is-indexed).
(include-book "owner-commit-carried")

(defun fn-rix-own-complete-enabled (o)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store o))
                              (fn-ccar-completion-enabledp (fn-own-store o)))))
  (let ((s (fn-own-store o)))
    (fn-own-refresh-ix
     (fn-own-make (fn-ccar-sn-finish-enabled s) (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) nil
                  (fn-sl-snoc (fn-own-ledger-field o) (fn-sf-completion (fn-sn-files s)))
                  (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                  (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
                  (fn-own-node-secret o) (fn-own-refused o)))))

(defthm fn-rix-own-complete-enabled-is-ccar
  (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                (fn-ceis-indexedp (fn-own-store o)))
           (equal (fn-rix-own-complete-enabled o)
                  (fn-ccar-own-complete-enabled o)))
  :hints (("Goal" :use ((:instance fn-ccar-sn-finish-is-sn-finish (s (fn-own-store o)))
                        (:instance fn-own-refresh-ix-of-finished-store-is-own-refresh
                                   (s (fn-own-store o))
                                   (view (fn-own-view o)) (conns (fn-own-conns o))
                                   (next-id (fn-own-next-id o))
                                   (max-conns (fn-own-max-conns o)) (pending nil)
                                   (ledger (fn-sl-snoc (fn-own-ledger-field o) (fn-sf-completion
                                                                (fn-sn-files (fn-own-store o)))))
                                   (clock (fn-own-clock o)) (facts (fn-own-facts o))
                                   (config (fn-own-config o)) (queue (fn-own-queue o))
                                   (inflight (fn-own-inflight o)) (feeds (fn-own-feeds o))
                                   (node-secret (fn-own-node-secret o))
                                   (refused (fn-own-refused o))))
           :in-theory (e/d (fn-rix-own-complete-enabled fn-ccar-own-complete-enabled
                            fn-ccar-sn-finish fn-ccar-completion-enabledp-is-reference)
                           (fn-ccar-sn-finish-is-sn-finish
                            fn-own-refresh-ix-of-finished-store-is-own-refresh
                            fn-own-refresh fn-own-refresh-ix fn-sn-finish fn-sn-statep
                            fn-ceis-indexedp fn-own-make fn-ccar-sn-finish-enabled
                            fn-sn-completion-enabledp)))))

;; PRF-277: the commit appends the ledger in O(1).  The ledger is held as a
;; snoc-list (books/owner.lisp fn-own-ledger-field); the completion the host
;; calls (fn-rix-own-finish, fn-rix-ocfg-complete) puts one pair on the field
;; with fn-sl-snoc -- one cons on a snoc form -- and the ledger it represents
;; is the old one with the pair appended, for every owner.
(defthm fn-own-refresh-ix-keeps-ledger-field
  (equal (fn-own-ledger-field (fn-own-refresh-ix o)) (fn-own-ledger-field o))
  :hints (("Goal" :in-theory (enable fn-own-refresh-ix))))

; KEYSTONE (representation): the executed field is the snoc of the old one.
(defthm fn-rix-own-complete-enabled-ledger-field
  (equal (fn-own-ledger-field (fn-rix-own-complete-enabled o))
         (fn-sl-snoc (fn-own-ledger-field o)
                     (fn-sf-completion (fn-sn-files (fn-own-store o)))))
  :hints (("Goal" :in-theory (e/d (fn-rix-own-complete-enabled)
                                  (fn-own-refresh-ix)))))

; KEYSTONE (model): the ledger it represents is the append.
(defthm fn-rix-own-complete-enabled-ledger
  (equal (fn-own-ledger (fn-rix-own-complete-enabled o))
         (append (fn-own-ledger o)
                 (list (fn-sf-completion (fn-sn-files (fn-own-store o))))))
  :hints (("Goal" :expand ((fn-own-ledger (fn-rix-own-complete-enabled o)))
           :in-theory (disable fn-rix-own-complete-enabled))))

(in-theory (disable fn-rix-own-complete-enabled))

; host/owner-host.lisp fn-owner-finish-submission calls this.
(defun fn-rix-own-finish (o cfg fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store o))))
  (if (fn-ccar-completion-enabledp (fn-own-store o))
      (cons (if (fn-ccar-completion-names-submission-p o cfg fn-arena) :durable :fault)
            (fn-rix-own-complete-enabled o))
    (cons :fault o)))

; KEYSTONE (host line): the indexed finish is the carried finish, hence
; fn-own-finish (fn-ccar-own-finish-is-own-finish), on every owner whose Store
; carries its event index.
(defthm fn-rix-own-finish-is-ccar-own-finish
  (implies (fn-ceis-indexedp (fn-own-store o))
           (equal (fn-rix-own-finish o cfg fn-arena)
                  (fn-ccar-own-finish o cfg fn-arena)))
  :hints (("Goal" :in-theory '(fn-rix-own-finish fn-ccar-own-finish
                               fn-rix-own-complete-enabled-is-ccar))))

(in-theory (disable fn-rix-own-finish))

(defun fn-rix-own-complete (o)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (if (fn-ccar-completion-enabledp (fn-own-store o))
      (fn-rix-own-complete-enabled o)
    o))

; host/owner-host.lisp fn-owner-finish calls this.
(defun fn-rix-ocfg-complete (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (let ((record (fn-ocfg-staged oc)))
    (if record
        (fn-ocfg-make
         (fn-ocfg-owner oc)
         (fn-ocfg-published-config (fn-ocfg-config oc) record)
         (fn-ocfg-pins oc) nil)
      (fn-ocfg-make (fn-rix-own-complete (fn-ocfg-owner oc))
                    (fn-ocfg-config oc) (fn-ocfg-pins oc) nil))))

; KEYSTONE (host line): the indexed configured completion is the carried one,
; hence fn-ocfg-step of (:complete) (fn-ccar-ocfg-complete-is-ocfg-step-complete).
(defthm fn-rix-ocfg-complete-is-ccar-ocfg-complete
  (implies (fn-ceis-indexedp (fn-own-store (fn-ocfg-owner oc)))
           (equal (fn-rix-ocfg-complete oc) (fn-ccar-ocfg-complete oc)))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete fn-ccar-ocfg-complete
                               fn-rix-own-complete fn-ccar-own-complete
                               fn-rix-own-complete-enabled-is-ccar))))

(in-theory (disable fn-rix-own-complete fn-rix-ocfg-complete))
