; Teeth for books/owner-prepare-served.lisp and
; books/owner-prepare-served-ocl.lisp (lane prepare-served, PKT-827 (d)): the
; served decision inside the prepare the host calls, the carried owner
; invariant across the retention prepare, the deferred record's order, the
; known abort and the configuration un-stage.  The witnesses are
; owner-log-ocl-tests' configured owner, its retired-group owner and its
; stale staged request, run through the host's own entries.
(in-package "ACL2")
(include-book "../../books/owner-prepare-served-ocl")
(include-book "owner-log-ocl-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun pst-carry (oc)
  ; The carry fn-owner-prepare-buffer passes: fn-prc-refresh of the global
  ; (NIL before the first POST) at the owner Store's retention ledger.
  (fn-prc-refresh nil (fn-node-retention (fn-sn-node (lgt-store oc)))))

; -----------------------------------------------------------------------------
; fn-psrv-prepare-preserves-invariant.  Reachable positive witness: at
; :reserved the article's group fn.letters is served; the host's prepare
; stages it (it is fn-prc-sbud-prepare there) and carries the invariant.
(defconst *pst-prepared* (fn-psrv-prepare *lgt-reserved* *acar-t-record* 1000000
                                          (pst-carry *lgt-reserved*)))
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(assert-event (fn-prc-carryp (pst-carry *lgt-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-reserved*)))

(assert-event (fn-psrv-event-servedp (fn-ocfg-config *lgt-reserved*) *acar-t-record*))
(assert-event (equal *pst-prepared* *lgt-prepared*))
(assert-event (equal (lgt-phase *pst-prepared*) :record-staged))
(assert-event (fn-lgoc-invariantp *pst-prepared*))

; THE RETIRED-GROUP WITNESS, refused by name.  control-quanta-2's
; *lgt-r-prepared*: fn.letters retired by a live completion (still in the
; Store's allocation domain), the owner carrying the invariant; the old
; prepare (fn-sbud-prepare / fn-prc-sbud-prepare, no served test) staged the
; article and broke fn-ocl-relation.  The host's prepare now leaves the
; owner unchanged, the invariant holds, and the word is :refused.
(defconst *pst-r-prepared* (fn-psrv-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                            (pst-carry *lgt-r-reserved*)))
(assert-event (fn-lgoc-invariantp *lgt-r-reserved*))
(assert-event (fn-prc-carryp (pst-carry *lgt-r-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-r-reserved*)))

(assert-event (not (fn-psrv-event-servedp (fn-ocfg-config *lgt-r-reserved*) *acar-t-record*)))
(assert-event (equal *pst-r-prepared* *lgt-r-reserved*))
(assert-event (fn-lgoc-invariantp *pst-r-prepared*))
(assert-event (equal (fn-psrv-refusal-kind *lgt-r-reserved* *acar-t-record* 1000000) :refused))
; The prepare without the served test still breaks it (the finding).
(assert-event (not (fn-lgoc-invariantp
                    (fn-prc-sbud-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                         (pst-carry *lgt-r-reserved*)))))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; off at :reserved; every other hypothesis holds; the staged article's topic
; step faults and the conclusion fails.
(assert-event (fn-prc-carryp (pst-carry *lgt-bad-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-bad-reserved*)))

(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp
                    (fn-psrv-prepare *lgt-bad-reserved* *acar-t-record* 1000000
                                     (pst-carry *lgt-bad-reserved*)))))
; -----------------------------------------------------------------------------
; fn-psrv-prepare-retention-preserves-invariant and the deferred order.
; Reachable positive witness: the retention event the host's
; fn-owner-prepare-retention builds at :reserved (an undertaking of one
; obligation) is staged by (:store (:prepare-retention E)) and the owner
; carries the invariant; the log route's order step publishes it (a
; deferred record: control-quanta-2's order theorem named the article only)
; and the owner reaches :completing carrying the invariant; the finish
; carries it back to :ready.
(defun pst-retention-event (oc)
  (let* ((s (lgt-store oc))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (fn-store-retention-event-make :undertake (fn-sn-identity-next s) txid txid
                                   "<obligation-1@fn.test>" "<subject-1@fn.test>"
                                   "evidence" 1)))
(defconst *pst-ret-event* (pst-retention-event *lgt-reserved*))
(defconst *pst-ret-staged*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-reserved* (list (list :store (list :prepare-retention *pst-ret-event*)))))
(assert-event (fn-store-retention-event-p *pst-ret-event*))
(assert-event (equal (lgt-phase *pst-ret-staged*) :record-staged))
(assert-event (equal (fn-sf-record-candidate (fn-sn-files (lgt-store *pst-ret-staged*)))
                     *pst-ret-event*))
(assert-event (fn-lgoc-invariantp *pst-ret-staged*))
(defconst *pst-ret-ordered* (fn-olr-ocfg-order *pst-ret-staged*))
(assert-event (not (fn-lgoc-article-stagedp (lgt-store *pst-ret-staged*))))
(assert-event (equal (lgt-phase *pst-ret-ordered*) :completing))
(assert-event (equal (len (fn-sf-records (fn-sn-files (lgt-store *pst-ret-ordered*)))) 3))
(assert-event (fn-lgoc-invariantp *pst-ret-ordered*))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; off at :reserved; the retention prepare (which does not read the topic
; prefix) stages the event, and the companion fails.
(defconst *pst-bad-ret-staged*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-bad-reserved* (list (list :store (list :prepare-retention *pst-ret-event*)))))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (equal (lgt-phase *pst-bad-ret-staged*) :record-staged))
(assert-event (not (fn-lgoc-invariantp *pst-bad-ret-staged*)))
; fn-psrv-log-order-preserves-invariant without the invariant: the corrupted
; staged retention, ordered, is not fn-ocl-relation.
(assert-event (not (fn-ocl-relation (fn-olr-ocfg-order *pst-bad-ret-staged*))))

; -----------------------------------------------------------------------------
; fn-psrv-known-abort-preserves-invariant.  Reachable positive witnesses: the
; staged article and the staged retention event, each known-aborted (the
; host's fn-owner-known-abort after a pre-publication Store refusal), reach
; :ready one transaction on and carry the invariant.
(defconst *pst-art-aborted*
  (in-arena-acar-t-ocfg-run *sr-arena* *pst-prepared* (list (list :store (list :known-abort)))))
(defconst *pst-ret-aborted*
  (in-arena-acar-t-ocfg-run *sr-arena* *pst-ret-staged* (list (list :store (list :known-abort)))))
(assert-event (equal (lgt-phase *pst-art-aborted*) :ready))
(assert-event (fn-lgoc-invariantp *pst-art-aborted*))
(assert-event (equal (lgt-phase *pst-ret-aborted*) :ready))
(assert-event (fn-lgoc-invariantp *pst-ret-aborted*))
(assert-event (equal (fn-sf-records (fn-sn-files (lgt-store *pst-ret-aborted*)))
                     (fn-sf-records (fn-sn-files (lgt-store *lgt-reserved*)))))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the corrupted
; staged retention, known-aborted, does not carry the invariant.
(assert-event (not (fn-lgoc-invariantp
                    (in-arena-acar-t-ocfg-run *sr-arena* *pst-bad-ret-staged* (list (list :store (list :known-abort)))))))

; -----------------------------------------------------------------------------
; fn-psrv-unstage-preserves-invariant.  Reachable witness: control-quanta-2's
; *lgt-stale* (a retirement staged against a Store whose frontier the
; refused reservation moved): the invariant holds and the authorization
; refuses.  Before the un-stage the staged record is the configuration lock:
; the owner refuses :begin.  The un-stage keeps the invariant and the owner,
; drops the record, and :begin is admitted again.
(assert-event (fn-lgoc-invariantp *lgt-stale*))
(assert-event (not (fn-oclc-live-authorizep *lgt-stale*)))
(assert-event (fn-ocfg-staged *lgt-stale*))
(defconst *pst-unstaged* (fn-psrv-unstage *lgt-stale*))
(assert-event (fn-lgoc-invariantp *pst-unstaged*))
(assert-event (not (fn-ocfg-staged *pst-unstaged*)))
(assert-event (equal (fn-ocfg-owner *pst-unstaged*) (fn-ocfg-owner *lgt-stale*)))
(assert-event (equal (fn-ocfg-config *pst-unstaged*) (fn-ocfg-config *lgt-stale*)))
(assert-event (equal (in-arena-acar-t-ocfg-run *sr-arena* *lgt-stale* (list '(:begin 0))) *lgt-stale*))
(assert-event (not (equal (in-arena-acar-t-ocfg-run *sr-arena* *pst-unstaged* (list '(:begin 0))) *pst-unstaged*)))
; Hypothesis fn-lgoc-invariantp: the corrupted-companion owner with the
; retirement staged; the un-stage keeps it corrupted.
(defconst *pst-bad-stale*
  (fn-ocfg-make (fn-ocfg-owner *lgt-bad-oc0*) (fn-ocfg-config *lgt-bad-oc0*)
                (fn-ocfg-pins *lgt-bad-oc0*) *lgt-retire*))
(assert-event (not (fn-lgoc-invariantp *pst-bad-stale*)))
(assert-event (not (fn-lgoc-invariantp (fn-psrv-unstage *pst-bad-stale*))))

; -----------------------------------------------------------------------------
; keystone-audit 2026-09-27: witnesses three PRF-290/299 events lacked.

; fn-psrv-rcon-io-preserves-invariant: reachable positive, the staged
; article's publication through the host's io entry (each operation
; fn-psrv-io-safep), carrying the invariant to :completing.
(defconst *pst-io-a* (fn-rcon-ocfg-io *pst-prepared* :record-file :ok))
(defconst *pst-io-b* (fn-rcon-ocfg-io *pst-io-a* :record-link :ok))
(defconst *pst-io-c* (fn-rcon-ocfg-io *pst-io-b* :record-directory :ok))
(assert-event
 (and (fn-lgoc-invariantp *pst-prepared*)
      (fn-psrv-io-safep :record-file) (fn-psrv-io-safep :record-link)
      (fn-psrv-io-safep :record-directory)
      (equal (lgt-phase *pst-io-a*) :record-data-durable)
      (fn-lgoc-invariantp *pst-io-a*)
      (equal (lgt-phase *pst-io-b*) :record-attempted)
      (fn-lgoc-invariantp *pst-io-b*)
      (equal (lgt-phase *pst-io-c*) :completing)
      (fn-lgoc-invariantp *pst-io-c*)))

; fn-psrv-deferred-record-dir-preserves-relation: reachable positive, the
; staged RETENTION event (not a held row) at :record-attempted, whose
; directory step keeps the Store relation.  Teeth for fn-cstp-carriedp
; (CORRUPTED, labelled): the topic-counter-corrupted owner's Store at the
; same point is fn-cst-relation but not carried, and the directory step
; breaks the relation.
(defconst *pst-ret-att*
  (lgt-store (fn-rcon-ocfg-io (fn-rcon-ocfg-io *pst-ret-staged* :record-file :ok)
                              :record-link :ok)))
(defconst *pst-bad-ret-att*
  (lgt-store (fn-rcon-ocfg-io (fn-rcon-ocfg-io *pst-bad-ret-staged* :record-file :ok)
                              :record-link :ok)))
(assert-event
 (and (fn-cst-relation *pst-ret-att*)
      (fn-cstp-carriedp *pst-ret-att*)
      (equal (fn-sf-phase (fn-sn-files *pst-ret-att*)) :record-attempted)
      (not (fn-held-p (fn-sf-record-candidate (fn-sn-files *pst-ret-att*))))
      (fn-cst-relation (fn-sn-io *pst-ret-att* :record-directory :ok))
      (equal (fn-sf-phase (fn-sn-files (fn-sn-io *pst-ret-att* :record-directory :ok)))
             :completing)))
(assert-event
 (and (fn-cst-relation *pst-bad-ret-att*)
      (not (fn-cstp-carriedp *pst-bad-ret-att*))
      (equal (fn-sf-phase (fn-sn-files *pst-bad-ret-att*)) :record-attempted)
      (not (fn-held-p (fn-sf-record-candidate (fn-sn-files *pst-bad-ret-att*))))
      (not (fn-cst-relation (fn-sn-io *pst-bad-ret-att* :record-directory :ok)))))

; fn-psrv-known-abort-preserves (the Store level): reachable positive, the
; staged retention event aborted to :ready keeping both relations; teeth
; for fn-cstp-carriedp (CORRUPTED, as above): carried fails after.
(assert-event
 (let ((s (lgt-store *pst-ret-staged*)))
   (and (fn-cst-relation s) (fn-cstp-carriedp s)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-known-abort s))) :ready)
        (fn-cst-relation (fn-sn-known-abort s))
        (fn-cstp-carriedp (fn-sn-known-abort s)))))
(assert-event
 (let ((s (lgt-store *pst-bad-ret-staged*)))
   (and (fn-cst-relation s) (not (fn-cstp-carriedp s))
        (not (fn-cstp-carriedp (fn-sn-known-abort s))))))

; fn-psrv-prepare-is-sbud-prepare-when-served (books/owner-prepare-served):
; reachable positive at :reserved (every hypothesis asserted above for
; *lgt-reserved*, and the view visible); teeth for fn-psrv-event-servedp:
; at the retired group (every other hypothesis holding, asserted above for
; *lgt-r-reserved*) the host's prepare leaves the owner and fn-sbud-prepare
; stages the article.
(assert-event
 (and (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *lgt-reserved*)))
      (equal (fn-psrv-prepare *lgt-reserved* *acar-t-record* 1000000
                              (pst-carry *lgt-reserved*))
             (fn-sbud-prepare *lgt-reserved* *acar-t-record* 1000000))))
(assert-event
 (and (fn-ocl-view-visiblep (fn-own-view (fn-ocfg-owner *lgt-r-reserved*)))
      (not (fn-psrv-event-servedp (fn-ocfg-config *lgt-r-reserved*) *acar-t-record*))
      (not (equal (fn-psrv-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                   (pst-carry *lgt-r-reserved*))
                  (fn-sbud-prepare *lgt-r-reserved* *acar-t-record* 1000000)))))

; =============================================================================
; Audit packet G2-P5 (lane audit-fixes).
; fn-psrv-deferred-record-dir-preserves-relation and
; fn-psrv-known-abort-preserves: removal of fn-cst-relation, CORRUPTED (the
; node advanced past the frontier; carried still holds).  At the deferred
; directory step the relation fails after; the known abort leaves a Store
; that is not related.
(defconst *pst-far-ret-att*
  (update-nth 3 (fn-replay-advance-txid (fn-sn-node *pst-ret-att*) 20) *pst-ret-att*))
(assert-event
 (and (not (fn-cst-relation *pst-far-ret-att*))
      (fn-cstp-carriedp *pst-far-ret-att*)
      (equal (fn-sf-phase (fn-sn-files *pst-far-ret-att*)) :record-attempted)
      (not (fn-held-p (fn-sf-record-candidate (fn-sn-files *pst-far-ret-att*))))
      (not (fn-cst-relation (fn-sn-io *pst-far-ret-att* :record-directory :ok)))))
(defconst *pst-far-ret-staged*
  (let ((s (lgt-store *pst-ret-staged*)))
    (update-nth 3 (fn-replay-advance-txid (fn-sn-node s) 20) s)))
(assert-event
 (and (not (fn-cst-relation *pst-far-ret-staged*))
      (fn-cstp-carriedp *pst-far-ret-staged*)
      (not (fn-cst-relation (fn-sn-known-abort *pst-far-ret-staged*)))))

; fn-psrv-prepare-preserves-invariant: no removal witness for fn-prc-carryp
; or the two index relations.  The finished owner reserved again, with a
; record reusing the committed obligation id (and its content and release
; ids) under a fresh Message-ID: the host's prepare with an INCOMPLETE carry
; (the ledger of the reservation, the trie before the commit: not carryp) is
; still refused at this owner (evaluated), as with the host's carry.  The
; carry tooth is at the node (post-retain-carried-tests
; prct-sn-prepare-without-carryp); a corrupted index turns the prepare into a
; refusal (owner-log-ocl-tests), never a staging the invariant rejects.
(defconst *pst-f-reserved* (fn-olr-ocfg-reserve *lgt-finished*))
(defconst *pst-pin-reuse*
  (fn-hrt-row-at
   (fn-record-make 3 9 9 "<pin-reuse@example>"
                   (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10 72 105 13 10)
                   '("fn.letters") "own-pin:<ocmt@example>" "own-content:<pin-reuse@example>"
                   "own-release:<pin-reuse@example>" 2 841000000)
   3))
(defconst *pst-short-carry*
  (cons (fn-node-retention (fn-sn-node (lgt-store *pst-f-reserved*)))
        (cdr (pst-carry *lgt-reserved*))))
(defconst *pst-pin-reuse-all*
  (fn-hrt-row-at
   (fn-record-make 3 9 9 "<pin-reuse@example>"
                   (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10 72 105 13 10)
                   '("fn.letters") "own-pin:<ocmt@example>" "own-content:<ocmt@example>"
                   "own-release:<ocmt@example>" 2 841000000)
   3))
(make-event
 `(defconst *pst-short-prepared*
    ',(with-guard-checking
       :none
       (list (fn-psrv-prepare *pst-f-reserved* *pst-pin-reuse* 1000000 *pst-short-carry*)
             (fn-psrv-prepare *pst-f-reserved* *pst-pin-reuse-all* 1000000 *pst-short-carry*)))))
(assert-event
 (and (fn-lgoc-invariantp *pst-f-reserved*)
      (not (fn-prc-carryp *pst-short-carry*))
      (not (fn-prc-has "own-pin:<ocmt@example>" (cdr *pst-short-carry*)))
      (fn-rii-knownp "own-pin:<ocmt@example>"
                     (fn-node-retention (fn-sn-node (lgt-store *pst-f-reserved*))))
      (equal (lgt-phase (car *pst-short-prepared*)) :reserved)
      (equal (lgt-phase (cadr *pst-short-prepared*)) :reserved)
      (fn-lgoc-invariantp (car *pst-short-prepared*))
      (equal (lgt-phase (fn-psrv-prepare *pst-f-reserved* (own-record 3 9 "<pin-reuse@example>")
                                         1000000 (pst-carry *pst-f-reserved*)))
             :record-staged)))

; -----------------------------------------------------------------------------
; RFC 3977 section 6's number bound (PKT-615, lane join-f2-615):
; fn-psrv-prepare-refuses-exhausted.  The witnesses are *lgt-reserved* with
; fn.letters' watermark set in its Store's node: a CONSTRUCTED boundary
; state (reaching it takes 2,147,483,646 articles in the group), labelled so.
(defun pst-with-next (oc group n)
  (let* ((o (fn-ocfg-owner oc))
         (s (fn-own-store o))
         (node (fn-sn-node s))
         (a (fn-node-acceptance node))
         (a2 (fn-make-state (fn-state-groups a)
                            (put-assoc-equal group n (fn-state-nexts a))
                            (fn-state-articles a) (fn-state-next-txid a)
                            (fn-state-pending a) (fn-state-fenced a)))
         (node2 (fn-node-make-state a2 (fn-node-retention node) (fn-node-stage node)
                                    (fn-node-bindings node))))
    (fn-ocfg-with-owner oc (fn-ocl-owner-with-store o (fn-sn-update s (fn-sn-files s) node2)))))

(defconst *pst-at-bound* (pst-with-next *lgt-reserved* "fn.letters" *fn-nntp-max-article-number*))
(defconst *pst-below-bound* (pst-with-next *lgt-reserved* "fn.letters" (1- *fn-nntp-max-article-number*)))

; Reachable positive witness of the number test: the configured owner's
; first POST fits (fn.letters' next number is small) and is staged.
(assert-event (fn-psrv-event-numberedp *lgt-reserved* *acar-t-record*))
(assert-event (equal (lgt-phase *pst-prepared*) :record-staged))

; Constructed boundary, positive: every hypothesis of the keystone holds
; (fn.letters served; its next number IS the bound, so the allocation would
; take the watermark past it) and so does every conclusion: the owner is
; unchanged and the word names the bound.
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *pst-at-bound*) *acar-t-record*))
(assert-event (not (fn-psrv-event-numberedp *pst-at-bound* *acar-t-record*)))
(assert-event (equal (fn-psrv-prepare *pst-at-bound* *acar-t-record* 1000000
                                      (pst-carry *pst-at-bound*))
                     *pst-at-bound*))
(assert-event (equal (fn-psrv-refusal-kind *pst-at-bound* *acar-t-record* 1000000)
                     :article-numbers-exhausted))
(assert-event (equal (fn-psrv-prepare-identity *pst-at-bound* *acar-t-record*) *pst-at-bound*))
(assert-event (equal (fn-psrv-identity-refusal-kind *pst-at-bound* *acar-t-record*)
                     :article-numbers-exhausted))
; One below: the last number the bound leaves (2,147,483,646; the watermark
; after it is 2,147,483,647) is admitted and staged.
(assert-event (fn-psrv-event-numberedp *pst-below-bound* *acar-t-record*))
(assert-event (equal (lgt-phase (fn-psrv-prepare *pst-below-bound* *acar-t-record* 1000000
                                                 (pst-carry *pst-below-bound*)))
                     :record-staged))

; Hypothesis removal, (not numberedp): at *lgt-reserved* the article is
; served (the retained hypothesis holds), the omitted one fails (it fits),
; and the conclusion fails: the prepare staged it.
(assert-event (and (fn-psrv-event-servedp (fn-ocfg-config *lgt-reserved*) *acar-t-record*)
                   (fn-psrv-event-numberedp *lgt-reserved* *acar-t-record*)
                   (not (equal *pst-prepared* *lgt-reserved*))))
; Hypothesis removal, servedp: the retired-group owner with fn.letters at the
; bound: (not numberedp) holds, servedp fails, and the word is :refused,
; not :article-numbers-exhausted (an unserved group names no number).
(defconst *pst-r-at-bound* (pst-with-next *lgt-r-reserved* "fn.letters" *fn-nntp-max-article-number*))
(assert-event (and (not (fn-psrv-event-numberedp *pst-r-at-bound* *acar-t-record*))
                   (not (fn-psrv-event-servedp (fn-ocfg-config *pst-r-at-bound*) *acar-t-record*))
                   (equal (fn-psrv-refusal-kind *pst-r-at-bound* *acar-t-record* 1000000) :refused)))
