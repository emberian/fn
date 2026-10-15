; Recovery K1 tooth: real old body fails, reset body restores, empty control holds.
(in-package "ACL2")
(include-book "../../books/owner-readers-recovery")
(include-book "../../books/owner-retain-livep")
(include-book "../../host/owner-served-carried")
(local
 (defun fn-owner-install-extended-old (oc extended key fn-arena fn-cat fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist state)
                  :guard (or (equal oc :fault)
                             (not (fn-onb-open-okp (fn-ocfg-owner oc)))
                             (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                                  (fn-mpxt-keyp key)
                                  (equal (len key) *fn-mpxt-key-octets*))) :verify-guards nil))
  (cond
   ((equal oc :fault)
    (mv nil :fault fn-arena fn-cat fn-hist state))
   ; THE OPEN's number bound (books/owner-number-bound.lisp fn-onb-open-okp,
   ; KEYSTONE fn-onb-boundp-when-open-okp): a recovered owner whose
   ; watermarks pass RFC 3977 section 6's bound is a damaged Store, refused
   ; by name before anything is installed.  O(groups); the served path then
   ; carries the bound (fn-onb-boundp), never revalidating it.
   ((not (fn-onb-open-okp (fn-ocfg-owner oc)))
    (mv nil :article-numbers-damaged fn-arena fn-cat fn-hist state))
   (t
      (let* ((state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         ; Cold reset occurs before physical recovery under lifecycle exclusion.
         ; Preserve the epoch captured by the issued recovery source.
             (state (fn-owner-install-open-ocfg oc state))
             ; PRF-289: the carried obligation-id trie for the ledger the
             ; owner opens with (books/post-retain-carried.lisp
             ; fn-prc-refresh of nil; fn-prc-carryp-of-refresh), so the
             ; first POST's refresh is a delta, not a build.
             (state (fn-owner-retain-carry-put
                     (fn-prc-refresh nil (fn-node-retention
                                          (fn-sn-node
                                           (fn-own-store (fn-owner-core state)))))
                     state))
             ; Rebuilt exclusively by successful FNFD scans after
             ; authoritative store recovery.  It is a carried
             ; incremental fold, never a whole-journal rescan on a
             ; served event.
             (state (f-put-global 'fn-owner-feed-intents nil state))
             (state (f-put-global 'fn-owner-feed-pending 0 state))
             ; The persisted profile is handed back by
             ; fn-owner-install-profile after every recovery; until
             ; then the budget is 0 and every publication is
             ; :unaffordable (books/store-budget.lisp).
             (state (f-put-global 'fn-owner-store-profile nil state))
             ; PRF-284: its carried verdict with it (fn-pvc-carryp-when-atom).
             (state (f-put-global 'fn-owner-profile-carry nil state))
             ; Socket-only reply framers are recreated after
             ; authoritative recovery; their durable counterpart is
             ; the FNFD replay above, not this retained input.
             (state (f-put-global 'fn-owner-feed-inputs
                                  (fn-fc-table-initial-state) state))
             ; Preserve the capture serial exactly as the old installer did.
             ; Install the stripped base; all other eight fields become nil.
             (state (fn-ost-install-publication
                     (fn-opub-install (fn-ost-publication state)
                                      (fn-scka-strip-base extended)) state))
             ; The pending PreparedCommit of the catalog (fn-owner-prepare-buffer).
             (state (f-put-global 'fn-owner-cat-pending nil state))
             ; E (step 8): the catalog of the installed store's history, from
             ; empty (books/served-catalog-owner.lisp fn-sca-load-held-rows).
             (store (fn-own-store (fn-ocfg-owner oc))))
        ; The records flip: the store's history is its ROWS, interned into
        ; the arena by the open; the catalog commits those rows and reads no
        ; byte and seals nothing (fn-sca-load-held-rows).
        ; THE SWITCH: under the ring's key (fn-sca-load-held-rows-keyed-is-
        ; load-held-rows: the same catalog, the table keyed).  The visible-set
        ; test of each row reads a Message-ID trie built here from the view's
        ; visible list and dropped with the load (the view holds none).
        (let* ((state (fn-orc-writer-enter state))
               (fn-cat (fn-sca-load-held-rows-keyed key
                                                   (fn-sf-records (fn-sn-files store))
                                                   (fn-midx-build
                                                    (fn-state-articles
                                                     (fn-own-view-archive
                                                      (fn-own-view (fn-ocfg-owner oc)))))
                                                   fn-arena fn-cat)))
          (let (; Stage 2b: the history stobj IS the installed store's history
              ; (KEYSTONE fn-hist-load-is-the-history,
              ; books/history-columns.lisp): R is established here, at every
              ; install, and the budget readers below sync it forward
              ; (fn-hist-sync-after-run-is-the-history).  The salt is the
              ; store's recorded one (format 10: the genesis the open read,
              ; books/store-genesis.lisp fn-gen-verdict-salt, 32 bits by
              ; fn-gen-verdict-salt-is-32-bits); it keys only the Message-ID
              ; buckets, which no reader here consults yet.
                (fn-hist (fn-hist-load (fn-sf-records (fn-sn-files store))
                                       (fn-gen-verdict-salt
                                        (and (boundp-global 'fn-store-genesis state)
                                             (f-get-global 'fn-store-genesis state)))
                                       fn-hist)))
            (let ((state (fn-orc-writer-leave state)))
              (mv nil :recovering fn-arena fn-cat fn-hist state)))))))))
(local (defconst *b-k1-r-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*))))
(local (defconst *b-k1-r-opened* (fn-cpo-open-observed (list *fn-cfg-default-record*) 0 nil)))
(local (defconst *b-k1-r-store*
 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *b-k1-r-opened*)
  :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok)))
(local (defconst *b-k1-r-oc* (fn-ocfg-make (fn-own-start *b-k1-r-store* 4) *b-k1-r-config* nil nil)))
(local (defconst *b-k1-r-opened-1* (fn-cpo-open-observed (list *fn-cfg-default-record*) 1 nil)))
(local (defconst *b-k1-r-store-1*
 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *b-k1-r-opened-1*)
  :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok)))
(local (defconst *b-k1-r-oc-1* (fn-ocfg-make (fn-own-start *b-k1-r-store-1* 4) *b-k1-r-config* nil nil)))
(local (defun fn-b-k1-r-positive (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena state)
   (with-local-stobj fn-cat
    (mv-let (result fn-arena fn-cat state)
     (with-local-stobj fn-hist
      (mv-let (result fn-arena fn-cat fn-hist state)
       (let* ((state (fn-owner-install-ocfg *b-k1-r-oc* state))
        (state (fn-owner-retain-carry-put nil state))
        (state (fn-ost-install-readers (fn-ordr-initial) state)))
  (mv-let (erp word fn-arena fn-cat fn-hist state)
    (fn-owner-install-extended *b-k1-r-oc* nil (make-list 32 :initial-element 0)
                              fn-arena fn-cat fn-hist state)
    (declare (ignore erp))
    (let ((ok (and (equal word :recovering) (fn-owner-retain-statep state))))
      (prog2$ (cw "B-K1-RECOVERY-POSITIVE ~x0~%" ok)
              (mv ok fn-arena fn-cat fn-hist state)))))
       (mv result fn-arena fn-cat state)))
     (mv result fn-arena state)))
   (mv result state)))))
(make-event (mv-let (result state) (fn-b-k1-r-positive state) (value (list 'assert-event result))))
(local (defun fn-b-k1-r-old (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena state)
   (with-local-stobj fn-cat
    (mv-let (result fn-arena fn-cat state)
     (with-local-stobj fn-hist
      (mv-let (result fn-arena fn-cat fn-hist state)
       (let* ((state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
        (state (fn-owner-retain-carry-put nil state))
        (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc-1*)))
        (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
        (readers-before (fn-ost-readers state))
        (before (fn-owner-retain-statep state))
        (hyps (and (fn-onb-open-okp (fn-ocfg-owner *b-k1-r-oc*))
                   (fn-lgoc-invariantp *b-k1-r-oc*))))
  (mv-let (erp word fn-arena fn-cat fn-hist state)
    (fn-owner-install-extended-old *b-k1-r-oc* nil (make-list 32 :initial-element 0)
                              fn-arena fn-cat fn-hist state)
    (declare (ignore erp))
    (let* ((after (fn-owner-retain-statep state))
           (kept (equal (fn-owner-reader-views state) (list view)))
           (reset-instance (equal (fn-ost-readers state)
            (if (or (equal *b-k1-r-oc* :fault)
                    (not (fn-onb-open-okp (fn-ocfg-owner *b-k1-r-oc*))))
                readers-before (fn-ordr-initial))))
           (counterexample (and (not reset-instance) before hyps (equal word :recovering) kept (not after))))
      (prog2$
       (cw "B-K1-RECOVERY-COUNTEREXAMPLE ~x0 BEFORE=~x1 HYPS=~x2 WORD=~x3 AFTER=~x4 READERS-KEPT=~x5 CAPTURE-FRONTIER=~x6 STORE-FRONTIER=~x7~%"
           counterexample before hyps word after kept
           (fn-own-view-frontier view) (fn-sf-frontier (fn-sn-files (fn-owner-store state))))
       (mv counterexample fn-arena fn-cat fn-hist state)))))
       (mv result fn-arena fn-cat state)))
     (mv result fn-arena state)))
   (mv result state)))))
(make-event (mv-let (result state) (fn-b-k1-r-old state) (value (list 'assert-event result))))
(local (defun fn-b-k1-r-new (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena state)
   (with-local-stobj fn-cat
    (mv-let (result fn-arena fn-cat state)
     (with-local-stobj fn-hist
      (mv-let (result fn-arena fn-cat fn-hist state)
       (let* ((state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
        (state (fn-owner-retain-carry-put nil state))
        (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc-1*)))
        (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
        (readers-before (fn-ost-readers state))
        (before (fn-owner-retain-statep state))
        (hyps (and (fn-onb-open-okp (fn-ocfg-owner *b-k1-r-oc*))
                   (fn-lgoc-invariantp *b-k1-r-oc*))))
  (mv-let (erp word fn-arena fn-cat fn-hist state)
    (fn-owner-install-extended *b-k1-r-oc* nil (make-list 32 :initial-element 0)
                              fn-arena fn-cat fn-hist state)
    (declare (ignore erp))
    (let* ((after (fn-owner-retain-statep state))
           (kept (equal (fn-ost-readers state) (fn-ordr-initial)))
           (reset-instance (equal (fn-ost-readers state)
            (if (or (equal *b-k1-r-oc* :fault)
                    (not (fn-onb-open-okp (fn-ocfg-owner *b-k1-r-oc*))))
                readers-before (fn-ordr-initial))))
           ;; The retired preservation formula is FALSE here: the current
           ;; installer changes a nonempty readers record.
           (old-preservation (equal (fn-ost-readers state) readers-before))
           (counterexample (and reset-instance (not old-preservation)
                                before hyps (equal word :recovering) kept after)))
      (prog2$
       (cw "B-K1-RECOVERY-RESTORED ~x0 BEFORE=~x1 HYPS=~x2 WORD=~x3 AFTER=~x4 READERS-KEPT=~x5 CAPTURE-FRONTIER=~x6 STORE-FRONTIER=~x7~%"
           counterexample before hyps word after kept
           (fn-own-view-frontier view) (fn-sf-frontier (fn-sn-files (fn-owner-store state))))
       (mv counterexample fn-arena fn-cat fn-hist state)))))
       (mv result fn-arena fn-cat state)))
     (mv result fn-arena state)))
   (mv result state)))))
(make-event (mv-let (result state) (fn-b-k1-r-new state) (value (list 'assert-event result))))
(local (defconst *b-k1-r-damaged*
 (fn-ocfg-with-view *b-k1-r-oc*
  (fn-own-view-make 0 0
   (update-nth 1 (list (cons "fn.test" (+ 1 *fn-nntp-max-article-number*)))
    (fn-own-view-archive (fn-own-view (fn-ocfg-owner *b-k1-r-oc*))))))))
(local (defun fn-b-k1-r-fault (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena state)
   (with-local-stobj fn-cat
    (mv-let (result fn-arena fn-cat state)
     (with-local-stobj fn-hist
      (mv-let (result fn-arena fn-cat fn-hist state)
       (let* ((oc :fault)
              (state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
              (state (fn-owner-retain-carry-put nil state))
              (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc-1*)))
              (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
              (readers-before (fn-ost-readers state))
              (before (fn-owner-retain-statep state)))
        (mv-let (erp word fn-arena fn-cat fn-hist state)
         (fn-owner-install-extended oc nil (make-list 32 :initial-element 0)
                                   fn-arena fn-cat fn-hist state)
         (declare (ignore erp))
         (let* ((refusal (or (equal oc :fault) (not (fn-onb-open-okp (fn-ocfg-owner oc)))))
                (instance (equal (fn-ost-readers state)
                                 (if refusal readers-before (fn-ordr-initial))))
                (ok (and before refusal (equal word :fault) instance
                         (fn-owner-retain-statep state))))
          (prog2$ (cw "B-K1-REFUSAL-FAULT ~x0 INSTANCE=~x1 WORD=~x2~%" ok instance word)
                  (mv ok fn-arena fn-cat fn-hist state)))))
       (mv result fn-arena fn-cat state)))
     (mv result fn-arena state)))
   (mv result state)))))
(make-event (mv-let (result state) (fn-b-k1-r-fault state) (value (list 'assert-event result))))
(local (defun fn-b-k1-r-damaged (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena state)
   (with-local-stobj fn-cat
    (mv-let (result fn-arena fn-cat state)
     (with-local-stobj fn-hist
      (mv-let (result fn-arena fn-cat fn-hist state)
       (let* ((oc *b-k1-r-damaged*)
              (state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
              (state (fn-owner-retain-carry-put nil state))
              (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc-1*)))
              (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
              (readers-before (fn-ost-readers state))
              (before (fn-owner-retain-statep state)))
        (mv-let (erp word fn-arena fn-cat fn-hist state)
         (fn-owner-install-extended oc nil (make-list 32 :initial-element 0)
                                   fn-arena fn-cat fn-hist state)
         (declare (ignore erp))
         (let* ((refusal (or (equal oc :fault) (not (fn-onb-open-okp (fn-ocfg-owner oc)))))
                (instance (equal (fn-ost-readers state)
                                 (if refusal readers-before (fn-ordr-initial))))
                (ok (and before refusal (equal word :article-numbers-damaged) instance
                         (fn-owner-retain-statep state))))
          (prog2$ (cw "B-K1-REFUSAL-DAMAGED ~x0 INSTANCE=~x1 WORD=~x2~%" ok instance word)
                  (mv ok fn-arena fn-cat fn-hist state)))))
       (mv result fn-arena fn-cat state)))
     (mv result fn-arena state)))
   (mv result state)))))
(make-event (mv-let (result state) (fn-b-k1-r-damaged state) (value (list 'assert-event result))))
; Ground false OLD frames and positive NEW frames. Actual predicates, fresh arena.
(local (defun fn-b-k1-class-puts (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (ok fn-arena state)
   (let* ((state (fn-owner-install-ocfg *b-k1-r-oc* state))
          (state (fn-owner-retain-carry-put nil state))
          (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc*)))
          (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
          (before-ret (fn-owner-retain-retained-statep state))
          (before-live (fn-owner-retain-livep state fn-arena))
          (positive-hyps (and (not (equal 'b-frame-control 'fn-owner))
                              (not (equal 'b-frame-control 'fn-owner-retain-carry))
                              (not (equal 'b-frame-control 'fn-owner-reader-views))))
          (state (f-put-global 'b-frame-control 0 state))
          (positive-ret (and positive-hyps before-ret
                            (equal (fn-owner-retain-retained-statep state) before-ret)))
          (positive-live (and positive-hyps before-live
                             (equal (fn-owner-retain-livep state fn-arena) before-live)))
          (old-hyps (and (not (equal 'fn-owner-reader-views 'fn-owner))
                         (not (equal 'fn-owner-reader-views 'fn-owner-retain-carry))))
          (future (fn-own-view-make 1 0 (fn-own-view-archive view)))
          (state (f-put-global 'fn-owner-reader-views (fn-ordr-make (list future) nil) state))
          (ret-false (and old-hyps before-ret
                          (not (equal (fn-owner-retain-retained-statep state) before-ret))))
          (live-false (and old-hyps before-live
                           (not (equal (fn-owner-retain-livep state fn-arena) before-live))))
          (ok (and positive-ret positive-live ret-false live-false)))
    (prog2$ (cw "B-K1-CLASS-PUTS RET-OLD-FALSE=~x0 LIVE-OLD-FALSE=~x1 RET-NEW-POSITIVE=~x2 LIVE-NEW-POSITIVE=~x3 OLD-HYPS=~x4 NEW-HYPS=~x5~%"
                ret-false live-false positive-ret positive-live old-hyps positive-hyps)
            (mv ok fn-arena state)))
   (mv ok state)))))
(make-event (mv-let (ok state) (fn-b-k1-class-puts state)
              (value (list 'assert-event ok))))
(local (defun fn-b-k1-class-installs (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (let* ((state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
        (state (fn-owner-retain-carry-put nil state))
        (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc-1*)))
        (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
        (before (fn-owner-retain-retained-statep state))
        (new-hyps (and before (fn-lgoc-invariantp *b-k1-r-oc-1*)
                       (fn-osr-retainedp (fn-sbud-oc-store *b-k1-r-oc-1*))
                       (fn-captured-views-follow-ocfg (fn-owner-reader-views state) *b-k1-r-oc-1*)))
        (state (fn-owner-install-ocfg *b-k1-r-oc-1* state))
        (new-positive (and new-hyps (fn-owner-retain-retained-statep state)))
        (old-hyps (and (fn-owner-retain-retained-statep state)
                       (fn-lgoc-invariantp *b-k1-r-oc*)
                       (fn-osr-retainedp (fn-sbud-oc-store *b-k1-r-oc*))))
        (missing-capture (not (fn-captured-views-follow-ocfg (fn-owner-reader-views state) *b-k1-r-oc*)))
        (state (fn-owner-install-ocfg *b-k1-r-oc* state))
        (old-false (and old-hyps (not (fn-owner-retain-retained-statep state))))
        (ok (and new-positive old-false missing-capture)))
  (prog2$ (cw "B-K1-CLASS-INSTALL OLD-FALSE=~x0 OLD-HYPS=~x1 NEW-POSITIVE=~x2 NEW-HYPS=~x3 MISSING-CAPTURE=~x4~%"
              old-false old-hyps new-positive new-hyps missing-capture)
          (mv ok state)))))
(make-event (mv-let (ok state) (fn-b-k1-class-installs state)
              (value (list 'assert-event ok))))
; Whole open: ground full positive and removed-antecedent counterexample.
(local (defun fn-b-k1-open-controls (state)
 (declare (xargs :stobjs state :guard t :verify-guards nil))
 (let* ((state (fn-owner-install-ocfg *b-k1-r-oc* state))
        (state (fn-owner-retain-carry-put nil state))
        (view (fn-own-view (fn-ocfg-owner *b-k1-r-oc*)))
        (state (fn-ost-install-readers (fn-ordr-make (list view) nil) state))
        (antecedent (fn-owner-retain-retained-statep state)))
  (mv-let (erp id state) (fn-owner-open state)
   (declare (ignore erp id))
   (let* ((positive (and antecedent (fn-owner-retain-retained-statep state)))
          (state (fn-owner-install-ocfg *b-k1-r-oc* state))
          (state (fn-owner-retain-carry-put nil state))
          (future (fn-own-view-make 1 0 (fn-own-view-archive view)))
          (state (fn-ost-install-readers (fn-ordr-make (list future) nil) state))
          (removed-antecedent (not (fn-owner-retain-retained-statep state))))
    (mv-let (erp id state) (fn-owner-open state)
     (declare (ignore erp id))
     (let* ((removal (and removed-antecedent (not (fn-owner-retain-retained-statep state))))
            (ok (and positive removal)))
      (prog2$ (cw "B-K1-OPEN POSITIVE=~x0 REMOVAL=~x1~%" positive removal)
              (mv ok state)))))))))
(make-event (mv-let (ok state) (fn-b-k1-open-controls state)
              (value (list 'assert-event ok))))
