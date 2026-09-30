; fn: a local article number, once observable, is never issued again across
; crashes (lane durability-bugs, row I3 item 2).
;
; The power-loss campaign (planning/evidence/power-loss-2026-09-26.md) saw
; the fresh POST after recovery take the local number an unacknowledged,
; lost in-flight POST had held in memory (258 cuts).  The ruling here
; (specs/nntp.md, "Local article numbers"): a number is ISSUED when some
; party outside the owner can observe it -- a reader's GROUP/LISTGROUP/
; OVER/ARTICLE n, a web page, a log line, a feed, a consumer, a 240 -- and
; every such observation is of the COMPLETED prefix, whose batch's barrier
; returned fenced (books/owner-reader-view.lisp KEYSTONE
; fn-ocvm-reader-view-is-the-completed-prefix; replies, log lines and feed
; resolutions leave in COMPLETE, fn-ocs-members-told-only-after-the-barrier;
; control, transit and consumer quanta are not admitted while a batch is
; open or in flight, fn-ocs-in-flight-admits-only-inspect-commit-and-reader).
; A number held only in the owner's memory is not issued, and RFC 3977
; section 6 asks the next SEQUENTIAL UNUSED number, so recovery handing it
; to the next article is the specified behaviour, not a defect.  A durable
; per-group reservation (no gaps closed, one more barrier per new block,
; one more record kind) was considered and rejected: it protects numbers no
; party could have seen.
;
; What this book proves is the other half: nothing ISSUED is issued again,
; over every crash the log admits.
;
;   KEYSTONE fn-ndur-replay-extension-keeps-every-number: for any Store
;   history XS and any history YS that extends it (fn-sf-prefixp) and opens
;   (fn-cst-replay-node, the configured replay recovery runs), every
;   (group . number) held in XS's replay is held by the SAME Message-ID in
;   YS's, and lies below YS's next number for its group.
;
;   KEYSTONE fn-ndur-recovery-keeps-every-visible-number: the subject is the
;   host's open (fn-cpo-open-observed; host/store-node-host.lisp
;   fn-store-sn-recover-rows calls fn-rii-sco-extend-open, equal to it by
;   books/replay-identity-index.lisp's keystones and
;   books/owner-checkpoint-open.lisp fn-sco-store-open-of-extended-capture;
;   the checkpoint open is the full one, fn-sn-recover-from-checkpoint-
;   equals-full-recover).  For a live configured owner whose view is at a
;   version no later than the FENCED count, and a recovered history that
;   extends the fenced prefix of the live history -- which is what the log's
;   crash theorem gives for every crash image (books/store-log-crash.lisp
;   fn-lg-batch-crash-is-a-prefix-under-a-crypto-trailer: the scan is
;   COMMITTED followed by a prefix of the batch in flight; the decode keeps
;   it a prefix, fn-ndur-decode-of-a-scanned-prefix) -- every number the
;   view shows is held by the same Message-ID after the open, below the
;   recovered next number.
;
;   KEYSTONE fn-ndur-prepare-never-allocates-below-the-watermark: the
;   acceptance prepare (fn-accept-prepare, the POST's allocation) never
;   stages a (group . number) below the state's next number; with the
;   previous keystone, the first POST after recovery takes a number above
;   every issued one, and books/owner-numbering.lisp's
;   fn-own-served-watermarks-never-decrease carries that to every later one.
;
;   KEYSTONE fn-ndur-crash-trace-never-reissues-a-number: over any crash
;   trace -- a list of epochs, each a history recovery opened, each
;   extending the previous one's visible prefix -- a number issued in the
;   first epoch is held by the same Message-ID in the last one and below its
;   next number.  So numbers issued are never re-issued across any number of
;   crashes.
;
;   KEYSTONE fn-ndur-recovery-never-reissues-a-logged-txid (PKT-835): every
;   record of a fenced prefix the recovered history extends has a txid below
;   the recovered next txid (the open's frontier), and the first prepare
;   stages that next txid (fn-ndur-prepare-stages-the-next-txid).  A txid
;   named only by a durable FNFD feed intent whose record was never logged
;   is not issued: the open decides that intent without reading its txid
;   (books/owner-feed-txid-reuse.lisp, PRF-269), so its reuse is a fresh
;   intent.
;
; Scope.  The histories are the Store's rows (held records, payload
; handles).  The live rows and the recovered rows of the fenced prefix are
; the same Store events up to their payload handles: a live arena that
; sealed a payload for a POST refused after its seal numbers later handles
; differently from the fresh intern at the open.  The numbering reads no
; payload: books/number-durability-handles.lisp proves the replay commutes
; with erasing handles and restates the two extension keystones with the
; premise up to handles (PKT-886).
; A crash inside a configuration write is the configuration program's; the
; configuration history is the same on both sides of a log cut.
; Teeth: tests/acl2/number-durability-tests.lisp.  PRF-903.
(in-package "ACL2")
(include-book "config-owner-live-complete")

(defun fn-ndur-holder (group number articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (if (fn-pair-memberp (cons group number) (fn-article-memberships (car articles)))
          (fn-article-msgid (car articles))
        (fn-ndur-holder group number (cdr articles)))
    nil))

(defun fn-ndur-tailp (x y)
  (declare (xargs :guard t))
  (or (equal x y)
      (and (consp y) (fn-ndur-tailp x (cdr y)))))

(defthm fn-ndur-holder-member
  (implies (fn-ndur-holder g n x)
           (fn-pair-memberp (cons g n) (fn-all-article-memberships x)))
  :hints (("Goal" :in-theory (enable fn-all-article-memberships))))

(defthm fn-ndur-tailp-transitive
  (implies (and (fn-ndur-tailp x y) (fn-ndur-tailp y z))
           (fn-ndur-tailp x z)))
(defthm fn-ndur-tailp-reflexive (fn-ndur-tailp x x))
(defthm fn-ndur-tail-memberships
  (implies (and (fn-ndur-tailp x y)
                (fn-pair-memberp p (fn-all-article-memberships x)))
           (fn-pair-memberp p (fn-all-article-memberships y)))
  :hints (("Goal" :in-theory (enable fn-all-article-memberships))))
(defthm fn-ndur-conflict-of-member
  (implies (and (fn-pair-memberp p ms)
                (fn-pair-memberp p (fn-all-article-memberships ys)))
           (fn-memberships-conflictsp ms ys))
  :hints (("Goal" :in-theory (enable fn-memberships-conflictsp fn-pair-memberp fn-pair-equalp))))
(defthm fn-ndur-holder-of-fresh-tail
  (implies (and (fn-ndur-tailp x y)
                (fn-articles-freshp y)
                (fn-ndur-holder g n x))
           (equal (fn-ndur-holder g n y) (fn-ndur-holder g n x)))
  :hints (("Goal" :induct (fn-ndur-tailp x y)
           :in-theory (enable fn-articles-freshp))))

(defthm fn-ndur-member-below-nexts
  (implies (and (fn-memberships-below-nextsp ms nexts)
                (fn-pair-memberp (cons g n) ms))
           (< n (fn-next-number g nexts)))
  :hints (("Goal" :in-theory (enable fn-memberships-below-nextsp fn-pair-memberp fn-pair-equalp))))
(defthm fn-ndur-holder-below-nexts
  (implies (and (fn-articles-below-nextsp articles nexts)
                (fn-ndur-holder g n articles))
           (< n (fn-next-number g nexts)))
  :hints (("Goal" :in-theory (enable fn-articles-below-nextsp))))

(defthm fn-ndur-accept-prepare-keeps-articles
  (equal (fn-state-articles (fn-accept-prepare s generation msgid payload groups stamp))
         (fn-state-articles s))
  :hints (("Goal" :in-theory (e/d (fn-accept-prepare) (fn-statep)))))
(defthm fn-ndur-accept-complete-grows
  (fn-ndur-tailp (fn-state-articles s)
                 (fn-state-articles (fn-accept-complete s txid generation status)))
  :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending fn-clear-pending)
                                  (fn-statep fn-pending-matchesp fn-next-number
                                   fn-advance-nexts)))))
(defthm fn-ndur-node-prepare-keeps-articles
  (equal (fn-state-articles (fn-node-acceptance
                             (fn-node-prepare s generation msgid payload groups
                                              obligation-id subject evidence charge stamp binding)))
         (fn-state-articles (fn-node-acceptance s)))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                  (fn-node-statep fn-accept-prepare fn-retain-admissiblep
                                   fn-retain-admit fn-node-make-stage)))))
(defthm fn-ndur-node-complete-grows
  (fn-ndur-tailp (fn-state-articles (fn-node-acceptance s))
                 (fn-state-articles (fn-node-acceptance
                                     (fn-node-complete s txid generation status))))
  :hints (("Goal" :in-theory (e/d (fn-node-complete)
                                  (fn-node-statep fn-accept-complete fn-node-pending-matchesp
                                   fn-ndur-tailp)))))
(defthm fn-ndur-replay-advance-keeps-articles
  (equal (fn-state-articles (fn-node-acceptance (fn-replay-advance-txid node txid)))
         (fn-state-articles (fn-node-acceptance node)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-txid))))

(defthm fn-ndur-node-complete-grows-chain
  (implies (fn-ndur-tailp x (fn-state-articles (fn-node-acceptance s)))
           (fn-ndur-tailp x (fn-state-articles (fn-node-acceptance
                                                (fn-node-complete s txid generation status)))))
  :hints (("Goal" :use fn-ndur-node-complete-grows
           :in-theory (disable fn-ndur-node-complete-grows fn-node-complete))))

(defthm fn-ndur-replay-apply-record-grows
  (implies (fn-node-statep (fn-replay-apply-record node record))
           (fn-ndur-tailp (fn-state-articles (fn-node-acceptance node))
                          (fn-state-articles (fn-node-acceptance
                                              (fn-replay-apply-record node record)))))
  :hints (("Goal" :in-theory (e/d (fn-replay-apply-record fn-replay-apply-retention-event
                                   fn-replay-complete-retention fn-replay-node-with-retention
                                   fn-replay-apply-identity-neutral)
                                  (fn-node-statep fn-store-event-p fn-store-event-sequence
                                   fn-record-p fn-stxe-p fn-stxk-p fn-stxa-p
                                   fn-store-retention-event-p fn-cpe-eventp
                                   fn-th-topic-eventp fn-replay-composite-record
                                   fn-hstxa-p fn-held-p fn-replay-composite-held
                                   fn-node-prepare fn-node-complete fn-node-pending-matchesp
                                   fn-retain-admissiblep fn-retain-admit fn-retain-release
                                   fn-retain-matching-releasep fn-retain-find-id
                                   fn-next-number fn-ndur-tailp)))))

(defun fn-ndur-cn-articles (cn)
  (declare (xargs :guard t :verify-guards nil))
  (fn-state-articles (fn-node-acceptance (fn-cnode-node cn))))

(defthm fn-ndur-cpr-apply-event-grows
  (implies (consp (fn-cpr-apply-event cn event))
           (fn-ndur-tailp (fn-ndur-cn-articles cn)
                          (fn-ndur-cn-articles (fn-cpr-apply-event cn event))))
  :hints (("Goal" :in-theory (e/d (fn-cpr-apply-event)
                                  (fn-replay-apply-record fn-cpr-event-servedp
                                   fn-cnode-statep fn-store-event-p fn-node-statep))
           :use ((:instance fn-ndur-replay-apply-record-grows
                            (node (fn-cnode-node cn)) (record event))))))

(defthm fn-ndur-cnode-apply-config-keeps-articles
  (equal (fn-ndur-cn-articles (fn-cnode-apply-config cn record ceiling))
         (fn-ndur-cn-articles cn))
  :hints (("Goal" :in-theory (e/d (fn-cnode-apply-config)
                                  (fn-cnode-statep fn-cnode-record-acceptablep
                                   fn-cnode-carried-acceptablep fn-cfg-apply-record)))))

(defthm fn-ndur-cnode-make-advance-articles
  (equal (fn-ndur-cn-articles (fn-cnode-make (fn-replay-advance-txid node txid) config))
         (fn-state-articles (fn-node-acceptance node))))

(defthm fn-ndur-cnode-make-advance-cn-articles
  (equal (fn-ndur-cn-articles (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn) txid)
                                             config))
         (fn-ndur-cn-articles cn)))

(defthm fn-ndur-cpr-loop-grows
  (implies (equal (fn-replay-result-kind
                   (fn-cpr-loop cn configs events cseq eseq))
                  :ok)
           (fn-ndur-tailp (fn-ndur-cn-articles cn)
                          (fn-ndur-cn-articles
                           (fn-replay-result-node
                            (fn-cpr-loop cn configs events cseq eseq)))))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cseq eseq)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-ndur-cn-articles fn-replay-advance-okp fn-cnode-carried-acceptablep
                            fn-ndur-cnode-make-advance-articles
                            fn-ndur-cpr-apply-event-grows fn-ndur-tailp-transitive))
           :expand ((fn-cpr-loop cn configs events cseq eseq)))
          ("Subgoal *1/11"
           :use ((:instance fn-cpr-apply-event-statep-iff-consp (event (car events)))
                 (:instance fn-ndur-cpr-apply-event-grows (event (car events)))
                 (:instance fn-ndur-tailp-transitive
                            (x (fn-ndur-cn-articles cn))
                            (y (fn-ndur-cn-articles (fn-cpr-apply-event cn (car events))))
                            (z (fn-ndur-cn-articles
                                (fn-replay-result-node
                                 (fn-cpr-loop (fn-cpr-apply-event cn (car events))
                                              configs (cdr events) cseq
                                              (+ 1 (nfix eseq)))))))))))

(defthm fn-ndur-cpr-loop-configs-only-keeps-articles
  (implies (and (not (consp events))
                (equal (fn-replay-result-kind
                        (fn-cpr-loop cn configs events cseq eseq))
                       :ok))
           (equal (fn-ndur-cn-articles
                   (fn-replay-result-node
                    (fn-cpr-loop cn configs events cseq eseq)))
                  (fn-ndur-cn-articles cn)))
  :hints (("Goal" :induct (fn-cpr-loop cn configs events cseq eseq)
           :in-theory (e/d (fn-cpr-loop)
                           (fn-cnode-statep fn-cnode-apply-config fn-cpr-apply-event
                            fn-cnode-record-acceptablep fn-store-event-p fn-cfg-recordp
                            fn-ndur-cn-articles fn-replay-advance-okp fn-cnode-carried-acceptablep
                            fn-ndur-cnode-make-advance-articles))
           :expand ((fn-cpr-loop cn configs events cseq eseq)))))

(defun fn-ndur-prefix-induct (cn configs xs ys cseq eseq)
  (declare (xargs :measure (+ (len configs) (len xs))
                  :hints (("Goal" :use ((:instance fn-cpr-config-firstp-has-config (events xs))) :in-theory (disable fn-cnode-apply-config fn-cpr-apply-event)))))
  (if (not (fn-cnode-statep cn))
      (list cn configs xs ys cseq eseq)
    (if (not (consp xs))
        (list cn configs xs ys cseq eseq)
      (if (fn-cpr-config-firstp configs xs)
          (fn-ndur-prefix-induct
           (fn-cnode-apply-config
            (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node cn)
                                                   (fn-cfg-record-txid (car configs)))
                           (fn-cnode-config cn))
            (car configs) (fn-cnode-line-ceiling))
           (cdr configs) xs ys (+ 1 (nfix cseq)) eseq)
        (fn-ndur-prefix-induct (fn-cpr-apply-event cn (car xs))
                               configs (cdr xs) (cdr ys) cseq (+ 1 (nfix eseq)))))))

(defthm fn-ndur-config-firstp-of-prefix
  (implies (and (fn-sf-prefixp xs ys) (consp xs))
           (equal (fn-cpr-config-firstp configs ys)
                  (fn-cpr-config-firstp configs xs)))
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp fn-sf-prefixp))))

(defthm fn-ndur-prefix-of-consp
  (implies (and (fn-sf-prefixp xs ys) (consp xs))
           (and (consp ys)
                (equal (car ys) (car xs))
                (fn-sf-prefixp (cdr xs) (cdr ys))))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))


(defthm fn-ndur-cpr-loop-ok-needs-statep
  (implies (not (fn-cnode-statep cn))
           (not (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok)))
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cseq eseq)))))

(defthm fn-ndur-cpr-loop-event-step
  (implies (and (consp events)
                (not (fn-cpr-config-firstp configs events))
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok))
           (equal (fn-cpr-loop cn configs events cseq eseq)
                  (fn-cpr-loop (fn-cpr-apply-event cn (car events))
                               configs (cdr events) cseq (+ 1 (nfix eseq)))))
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cseq eseq))
           :in-theory (disable fn-cnode-statep fn-cpr-apply-event fn-store-event-p))))

(defthm fn-ndur-cpr-loop-config-step
  (implies (and (fn-cpr-config-firstp configs events)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok))
           (equal (fn-cpr-loop cn configs events cseq eseq)
                  (fn-cpr-loop (fn-cnode-apply-config
                                (fn-cnode-make (fn-replay-advance-txid
                                                (fn-cnode-node cn)
                                                (fn-cfg-record-txid (car configs)))
                                               (fn-cnode-config cn))
                                (car configs) (fn-cnode-line-ceiling))
                               (cdr configs) events (+ 1 (nfix cseq)) eseq)))
  :hints (("Goal" :expand ((fn-cpr-loop cn configs events cseq eseq))
           :in-theory (disable fn-cnode-statep fn-cnode-apply-config fn-cfg-recordp
                               fn-cnode-record-acceptablep fn-cnode-carried-acceptablep
                               fn-replay-advance-okp (fn-cnode-line-ceiling)))))

(defthm fn-ndur-cpr-loop-event-step-ok
  (implies (and (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok)
                (equal e (+ 1 (nfix eseq)))
                (consp events)
                (not (fn-cpr-config-firstp configs events)))
           (equal (fn-replay-result-kind
                   (fn-cpr-loop (fn-cpr-apply-event cn (car events))
                                configs (cdr events) cseq e))
                  :ok))
  :hints (("Goal" :use fn-ndur-cpr-loop-event-step
           :in-theory (disable fn-ndur-cpr-loop-event-step fn-cpr-loop))))

(defthm fn-ndur-cpr-loop-config-step-ok
  (implies (and (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok)
                (equal c (+ 1 (nfix cseq)))
                (fn-cpr-config-firstp configs events))
           (equal (fn-replay-result-kind
                   (fn-cpr-loop (fn-cnode-apply-config
                                 (fn-cnode-make (fn-replay-advance-txid
                                                 (fn-cnode-node cn)
                                                 (fn-cfg-record-txid (car configs)))
                                                (fn-cnode-config cn))
                                 (car configs) (fn-cnode-line-ceiling))
                                (cdr configs) events c eseq))
                  :ok))
  :hints (("Goal" :use fn-ndur-cpr-loop-config-step
           :in-theory (disable fn-ndur-cpr-loop-config-step fn-cpr-loop))))

(defthm fn-ndur-cpr-loop-event-step-ok-of-prefix
  (implies (and (fn-sf-prefixp xs ys)
                (consp xs)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs ys cseq eseq)) :ok)
                (equal e (+ 1 (nfix eseq)))
                (not (fn-cpr-config-firstp configs xs)))
           (equal (fn-replay-result-kind
                   (fn-cpr-loop (fn-cpr-apply-event cn (car xs))
                                configs (cdr ys) cseq e))
                  :ok))
  :hints (("Goal" :use ((:instance fn-ndur-cpr-loop-event-step-ok (events ys))
                        fn-ndur-prefix-of-consp fn-ndur-config-firstp-of-prefix)
           :in-theory (disable fn-ndur-cpr-loop-event-step-ok fn-cpr-loop
                               fn-ndur-prefix-of-consp fn-ndur-config-firstp-of-prefix))))

(defthm fn-ndur-cpr-loop-config-step-ok-at
  (implies (and (equal (fn-replay-result-kind (fn-cpr-loop cn configs events cseq eseq)) :ok)
                (equal c (+ 1 (nfix cseq)))
                (equal k (fn-cnode-line-ceiling))
                (fn-cpr-config-firstp configs events))
           (equal (fn-replay-result-kind
                   (fn-cpr-loop (fn-cnode-apply-config
                                 (fn-cnode-make (fn-replay-advance-txid
                                                 (fn-cnode-node cn)
                                                 (fn-cfg-record-txid (car configs)))
                                                (fn-cnode-config cn))
                                 (car configs) k)
                                (cdr configs) events c eseq))
                  :ok))
  :hints (("Goal" :use fn-ndur-cpr-loop-config-step-ok
           :in-theory (disable fn-ndur-cpr-loop-config-step-ok fn-cpr-loop))))

(defthm fn-ndur-cpr-loop-prefix-grows
  (implies (and (fn-sf-prefixp xs ys)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs xs cseq eseq)) :ok)
                (equal (fn-replay-result-kind (fn-cpr-loop cn configs ys cseq eseq)) :ok))
           (fn-ndur-tailp (fn-ndur-cn-articles
                           (fn-replay-result-node (fn-cpr-loop cn configs xs cseq eseq)))
                          (fn-ndur-cn-articles
                           (fn-replay-result-node (fn-cpr-loop cn configs ys cseq eseq)))))
  :hints (("Goal" :induct (fn-ndur-prefix-induct cn configs xs ys cseq eseq)
           :in-theory (disable fn-cpr-loop fn-sf-prefixp fn-cnode-statep fn-cnode-apply-config
                               fn-cpr-apply-event fn-ndur-cn-articles fn-cpr-config-firstp
                               fn-cfg-recordp fn-replay-advance-okp))
          ("Subgoal *1/2"
           :use ((:instance fn-ndur-cpr-loop-configs-only-keeps-articles (events xs))
                 (:instance fn-ndur-cpr-loop-grows (events ys))))))

(defthm fn-ndur-cst-replay-node-statep
  (implies (fn-cst-replay-node configs events frontier)
           (fn-node-statep (fn-cst-replay-node configs events frontier)))
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node fn-cnode-statep)
                                  (fn-cpr-replay fn-node-statep))
           :use (fn-cpr-replay-ok-is-configured
                 (:instance fn-replay-advance-preserves-node-statep
                            (node (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events))))
                            (recorded-txid frontier))))))

(defthm fn-ndur-cst-replay-node-articles
  (implies (fn-cst-replay-node configs events frontier)
           (equal (fn-state-articles (fn-node-acceptance (fn-cst-replay-node configs events frontier)))
                  (fn-ndur-cn-articles (fn-replay-result-node (fn-cpr-replay configs events)))))
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node) (fn-cpr-replay fn-cnode-statep)))))

(defthm fn-ndur-cst-replay-node-ok
  (implies (fn-cst-replay-node configs events frontier)
           (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node) (fn-cpr-replay fn-cnode-statep)))))

(defthm fn-ndur-node-statep-facts
  (implies (fn-node-statep node)
           (and (fn-articles-freshp (fn-state-articles (fn-node-acceptance node)))
                (fn-articles-below-nextsp (fn-state-articles (fn-node-acceptance node))
                                          (fn-state-nexts (fn-node-acceptance node)))))
  :hints (("Goal" :in-theory (enable fn-node-statep fn-statep))))

(defthm fn-ndur-no-node-holds-no-number
  (not (fn-ndur-holder g n (fn-state-articles (fn-node-acceptance nil)))))

(defthm fn-ndur-replay-extension-keeps-every-number
  (implies (and (fn-sf-prefixp xs ys)
                (fn-cst-replay-node configs ys f2)
                (fn-ndur-holder g n (fn-state-articles
                                     (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
           (and (equal (fn-ndur-holder g n (fn-state-articles
                                            (fn-node-acceptance (fn-cst-replay-node configs ys f2))))
                       (fn-ndur-holder g n (fn-state-articles
                                            (fn-node-acceptance (fn-cst-replay-node configs xs f1)))))
                (< n (fn-next-number g (fn-state-nexts
                                        (fn-node-acceptance (fn-cst-replay-node configs ys f2)))))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-cst-replay-node configs xs f1)))
          ("Subgoal 1"
           :use ((:instance fn-ndur-cst-replay-node-ok (events xs) (frontier f1))
                 (:instance fn-ndur-cst-replay-node-ok (events ys) (frontier f2))
                 (:instance fn-ndur-cpr-loop-prefix-grows
                            (cn (fn-cnode-initial (fn-cfg-initial))) (cseq 0) (eseq 0))
                 (:instance fn-ndur-node-statep-facts
                            (node (fn-cst-replay-node configs ys f2)))
                 (:instance fn-ndur-holder-of-fresh-tail
                            (x (fn-state-articles (fn-node-acceptance (fn-cst-replay-node configs xs f1))))
                            (y (fn-state-articles (fn-node-acceptance (fn-cst-replay-node configs ys f2)))))
                 (:instance fn-ndur-holder-below-nexts
                            (articles (fn-state-articles (fn-node-acceptance (fn-cst-replay-node configs ys f2))))
                            (nexts (fn-state-nexts (fn-node-acceptance (fn-cst-replay-node configs ys f2))))))
           :in-theory (e/d (fn-cpr-replay)
                           (fn-cst-replay-node fn-cpr-loop fn-ndur-cpr-loop-prefix-grows
                            fn-ndur-node-statep-facts fn-ndur-holder-of-fresh-tail
                            fn-ndur-holder-below-nexts fn-ndur-cst-replay-node-ok fn-ndur-cn-articles fn-node-statep
                            fn-ndur-holder fn-sf-prefixp)))))

(include-book "store-open-bridge")
(include-book "store-recover-stream")

(defthm fn-ndur-host-open-config-history
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sn-config-history (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                  configs))
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-cpo-install fn-sn-open-okp)
                                  (fn-cpr-replay fn-replay-identity fn-cnode-statep fn-sn-statep)))))

(defthm fn-ndur-history-relation-node
  (implies (fn-cpo-history-relation st)
           (equal (fn-sn-node st)
                  (fn-cst-replay-node (fn-sn-config-history st)
                                      (fn-sf-records (fn-sn-files st))
                                      (fn-sf-frontier (fn-sn-files st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-history-relation fn-cst-replay-node)
                                  (fn-cpr-replay fn-cnode-statep fn-sn-statep)))))

(defthm fn-ndur-host-open-node-is-the-replay
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sn-node (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                  (fn-cst-replay-node configs events frontier)))
  :hints (("Goal" :do-not-induct t
           :use (fn-cpo-open-observed-success-has-history-relation
                 fn-sn-open-observed-success-exact-history-of-host-open
                 fn-ndur-host-open-config-history
                 (:instance fn-ndur-history-relation-node
                            (st (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defun fn-ndur-take-induct (v c xs)
  (if (and (posp v) (posp c) (consp xs))
      (fn-ndur-take-induct (1- v) (1- c) (cdr xs))
    (list v c xs)))

(defthm fn-ndur-take-prefix-of-take
  (implies (<= (nfix v) (nfix c))
           (fn-sf-prefixp (fn-own-take v xs) (fn-own-take c xs)))
  :hints (("Goal" :induct (fn-ndur-take-induct v c xs)
           :in-theory (enable fn-sf-prefixp fn-own-take))))

(defthm fn-ndur-prefixp-transitive
  (implies (and (fn-sf-prefixp xs ys) (fn-sf-prefixp ys zs))
           (fn-sf-prefixp xs zs))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))

(defthm fn-ndur-history-relation-replay-node-exists
  (implies (fn-cpo-history-relation st)
           (fn-cst-replay-node (fn-sn-config-history st)
                               (fn-sf-records (fn-sn-files st))
                               (fn-sf-frontier (fn-sn-files st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-history-relation fn-cst-replay-node fn-cnode-statep)
                                  (fn-cpr-replay fn-sn-statep))
           :use ((:instance fn-replay-advance-preserves-node-statep
                            (node (fn-cnode-node (fn-replay-result-node
                                                  (fn-cpr-replay (fn-sn-config-history st)
                                                                 (fn-sf-records (fn-sn-files st))))))
                            (recorded-txid (fn-sf-frontier (fn-sn-files st))))))))

(defthm fn-ndur-host-open-replay-node-exists
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-cst-replay-node configs events frontier))
  :hints (("Goal" :do-not-induct t
           :use (fn-cpo-open-observed-success-has-history-relation
                 fn-sn-open-observed-success-exact-history-of-host-open
                 fn-ndur-host-open-config-history
                 (:instance fn-ndur-history-relation-replay-node-exists
                            (st (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))))
           :in-theory (union-theories '() (theory 'minimal-theory)))))

(defthm fn-ndur-recovery-keeps-every-visible-number
  (let* ((st (fn-own-store o))
         (live (fn-sf-records (fn-sn-files st)))
         (raw (fn-own-view-raw (fn-own-view o)))
         (node (fn-sn-node (fn-sn-open-state
                            (fn-cpo-open-observed (fn-sn-config-history st)
                                                  frontier recovered))))
         (articles (fn-state-articles (fn-node-acceptance node))))
    (implies (and (fn-ocl-view-historyp o)
                  (<= (fn-own-view-version (fn-own-view o)) (nfix fenced))
                  (fn-sf-prefixp (fn-own-take fenced live) recovered)
                  (fn-sn-open-okp (fn-cpo-open-observed (fn-sn-config-history st)
                                                        frontier recovered))
                  (fn-ndur-holder g n raw))
             (and (equal (fn-ndur-holder g n articles) (fn-ndur-holder g n raw))
                  (< n (fn-next-number g (fn-state-nexts (fn-node-acceptance node)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ndur-replay-extension-keeps-every-number
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (xs (fn-own-take (fn-own-view-version (fn-own-view o))
                                             (fn-sf-records (fn-sn-files (fn-own-store o)))))
                            (ys recovered)
                            (f1 (fn-own-view-frontier (fn-own-view o)))
                            (f2 frontier))
                 (:instance fn-ndur-take-prefix-of-take
                            (v (fn-own-view-version (fn-own-view o)))
                            (c fenced)
                            (xs (fn-sf-records (fn-sn-files (fn-own-store o)))))
                 (:instance fn-ndur-prefixp-transitive
                            (xs (fn-own-take (fn-own-view-version (fn-own-view o))
                                             (fn-sf-records (fn-sn-files (fn-own-store o)))))
                            (ys (fn-own-take fenced (fn-sf-records (fn-sn-files (fn-own-store o)))))
                            (zs recovered))
                 (:instance fn-ndur-host-open-replay-node-exists
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (events recovered))
                 (:instance fn-ndur-host-open-node-is-the-replay
                            (configs (fn-sn-config-history (fn-own-store o)))
                            (events recovered)))
           :in-theory (e/d (fn-ocl-view-historyp)
                           (fn-ndur-replay-extension-keeps-every-number
                            fn-ndur-take-prefix-of-take fn-ndur-prefixp-transitive
                            fn-ndur-host-open-node-is-the-replay fn-ndur-host-open-replay-node-exists
                            fn-ndur-cst-replay-node-articles fn-cst-replay-node fn-cpo-open-observed fn-node-statep
                            fn-ndur-holder fn-own-take fn-sf-prefixp fn-sn-open-okp
                            fn-ctl-visible-state)))))

(defthm fn-ndur-at-watermark-member
  (implies (and (fn-memberships-at-watermarkp ms nexts)
                (fn-pair-memberp (cons g n) ms))
           (equal n (fn-next-number g nexts)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-memberships-at-watermarkp fn-pair-memberp fn-pair-equalp))))

(defthm fn-ndur-prepare-never-allocates-below-the-watermark
  (implies (and (fn-statep s)
                (< n (fn-next-number g (fn-state-nexts s))))
           (not (fn-pair-memberp (cons g n)
                                 (fn-pending-memberships
                                  (fn-state-pending
                                   (fn-accept-prepare s generation msgid payload groups stamp))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-allocate-at-watermark
                            (configured (fn-state-groups s)) (nexts (fn-state-nexts s)))
                 (:instance fn-ndur-at-watermark-member
                            (ms (fn-allocate-memberships groups (fn-state-nexts s)))
                            (nexts (fn-state-nexts s)))
                 (:instance fn-ndur-at-watermark-member
                            (ms (fn-pending-memberships (fn-state-pending s)))
                            (nexts (fn-state-nexts s))))
           :in-theory (e/d (fn-accept-prepare fn-selection-validp fn-statep fn-pendingp)
                           (fn-allocate-at-watermark fn-allocate-memberships
                            fn-memberships-at-watermarkp fn-next-number)))))

(defthm fn-ndur-decode-of-a-scanned-prefix
  (implies (and (true-listp committed)
                (not (equal (fn-srs-decode (append committed p)) :bad)))
           (and (not (equal (fn-srs-decode committed) :bad))
                (fn-sf-prefixp (fn-srs-decode committed)
                               (fn-srs-decode (append committed p)))))
  :hints (("Goal" :induct (true-listp committed)
           :in-theory (e/d (fn-srs-decode fn-sf-prefixp) (fn-store-event-decode-exact fn-rcon-wire-event-p)))))

; An EPOCH is (EVENTS . FRONTIER): the Store history a process ran on, from
; its recovery to its death.  A crash trace is a list of epochs, each
; opening (a configured replay exists) and each history extending the
; previous one's visible prefix: what K-recovery's premise gives per crash.
(defun fn-ndur-epoch-articles (configs epoch)
  (declare (xargs :guard t :verify-guards nil))
  (fn-state-articles (fn-node-acceptance
                      (fn-cst-replay-node configs (car epoch) (cdr epoch)))))

(defun fn-ndur-epoch-nexts (configs epoch)
  (declare (xargs :guard t :verify-guards nil))
  (fn-state-nexts (fn-node-acceptance
                   (fn-cst-replay-node configs (car epoch) (cdr epoch)))))

(defun fn-ndur-crash-tracep (configs epochs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp epochs)
      (and (fn-cst-replay-node configs (car (car epochs)) (cdr (car epochs)))
           (or (not (consp (cdr epochs)))
               (fn-sf-prefixp (car (car epochs)) (car (cadr epochs))))
           (fn-ndur-crash-tracep configs (cdr epochs)))
    t))

(defthm fn-ndur-replay-node-holder-below-nexts
  (implies (and (fn-cst-replay-node configs events frontier)
                (fn-ndur-holder g n (fn-state-articles
                                     (fn-node-acceptance (fn-cst-replay-node configs events frontier)))))
           (< n (fn-next-number g (fn-state-nexts
                                   (fn-node-acceptance (fn-cst-replay-node configs events frontier))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ndur-node-statep-facts
                            (node (fn-cst-replay-node configs events frontier)))
                 (:instance fn-ndur-holder-below-nexts
                            (articles (fn-state-articles (fn-node-acceptance (fn-cst-replay-node configs events frontier))))
                            (nexts (fn-state-nexts (fn-node-acceptance (fn-cst-replay-node configs events frontier))))))
           :in-theory (disable fn-cst-replay-node fn-ndur-node-statep-facts fn-ndur-holder-below-nexts
                               fn-ndur-cst-replay-node-articles fn-ndur-holder fn-node-statep))))

(defthm fn-ndur-crash-trace-of-epochs-keeps-numbers
  (implies (and (consp epochs)
                (fn-ndur-crash-tracep configs epochs)
                (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs))))
           (and (equal (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car (last epochs))))
                       (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs))))
                (< n (fn-next-number g (fn-ndur-epoch-nexts configs (car (last epochs)))))))
  :hints (("Goal" :induct (fn-ndur-crash-tracep configs epochs)
           :in-theory (e/d () (fn-cst-replay-node fn-ndur-holder fn-sf-prefixp
                               fn-ndur-cst-replay-node-articles)))
          (and stable-under-simplificationp
               '(:use ((:instance fn-ndur-replay-extension-keeps-every-number
                                  (xs (car (car epochs))) (f1 (cdr (car epochs)))
                                  (ys (car (cadr epochs))) (f2 (cdr (cadr epochs))))
                       (:instance fn-ndur-replay-node-holder-below-nexts
                                  (events (car (car epochs))) (frontier (cdr (car epochs)))))))))

(defthm fn-ndur-empty-history-holds-no-number
  (not (fn-ndur-holder g n (fn-state-articles
                            (fn-node-acceptance (fn-cst-replay-node configs nil frontier)))))
  :hints (("Goal" :cases ((fn-cst-replay-node configs nil frontier)))
          ("Subgoal 1"
           :use ((:instance fn-ndur-cpr-loop-configs-only-keeps-articles
                            (cn (fn-cnode-initial (fn-cfg-initial))) (events nil)
                            (cseq 0) (eseq 0))
                 (:instance fn-ndur-cst-replay-node-ok (events nil)))
           :in-theory (e/d (fn-cpr-replay) (fn-cpr-loop fn-ndur-cst-replay-node-ok
                                            fn-ndur-cpr-loop-configs-only-keeps-articles)))))
(defthm fn-ndur-crash-trace-never-reissues-a-number
  (implies (and (fn-ndur-crash-tracep configs epochs)
                (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs))))
           (and (equal (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car (last epochs))))
                       (fn-ndur-holder g n (fn-ndur-epoch-articles configs (car epochs))))
                (< n (fn-next-number g (fn-ndur-epoch-nexts configs (car (last epochs)))))))
  :hints (("Goal" :cases ((consp epochs)))
          ("Subgoal 2" :use ((:instance fn-ndur-empty-history-holds-no-number
                                        (frontier nil)))
           :in-theory (disable fn-ndur-empty-history-holds-no-number fn-cst-replay-node))
          ("Subgoal 1" :use fn-ndur-crash-trace-of-epochs-keeps-numbers
           :in-theory (disable fn-ndur-crash-trace-of-epochs-keeps-numbers))))

; -----------------------------------------------------------------------------
; Transaction ids (PKT-835).  A txid is issued when its record is logged and
; fenced; the open's frontier is above every logged txid, and the first
; prepare after the open stages the frontier.

(defthm fn-ndur-record-listp-txids-below-frontier
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (member-equal e records))
           (< (fn-store-event-txid e) frontier))
  :hints (("Goal" :in-theory (enable fn-sf-record-listp))))

(defthm fn-ndur-prefix-member
  (implies (and (fn-sf-prefixp xs ys) (member-equal e xs))
           (member-equal e ys))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))

(defthm fn-ndur-host-open-history-is-observed
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (fn-sn-observed-historyp frontier events))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-okp)
                                  (fn-cpr-replay fn-sn-observed-historyp fn-cnode-statep
                                   fn-sn-statep fn-replay-identity)))))

(defthm fn-ndur-cst-replay-node-next-txid
  (implies (fn-cst-replay-node configs events frontier)
           (equal (fn-state-next-txid (fn-node-acceptance (fn-cst-replay-node configs events frontier)))
                  frontier))
  :hints (("Goal" :in-theory (e/d (fn-cst-replay-node fn-replay-advance-txid fn-replay-advance-okp)
                                  (fn-cpr-replay fn-node-statep)))))

(defthm fn-ndur-recovery-never-reissues-a-logged-txid
  (let ((node (fn-sn-node (fn-sn-open-state (fn-cpo-open-observed configs frontier recovered)))))
    (implies (and (fn-sn-open-okp (fn-cpo-open-observed configs frontier recovered))
                  (fn-sf-prefixp fenced recovered)
                  (member-equal e fenced))
             (< (fn-store-event-txid e)
                (fn-state-next-txid (fn-node-acceptance node)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ndur-host-open-history-is-observed (events recovered))
                 (:instance fn-ndur-host-open-node-is-the-replay (events recovered))
                 (:instance fn-ndur-host-open-replay-node-exists (events recovered))
                 (:instance fn-ndur-prefix-member (xs fenced) (ys recovered))
                 (:instance fn-ndur-record-listp-txids-below-frontier
                            (records recovered) (sequence 0) (lower 0)))
           :in-theory (e/d (fn-sn-observed-historyp)
                           (fn-ndur-host-open-node-is-the-replay fn-ndur-host-open-replay-node-exists
                            fn-ndur-prefix-member fn-ndur-record-listp-txids-below-frontier
                            fn-cpo-open-observed fn-cst-replay-node fn-sn-open-okp
                            fn-sf-record-listp fn-sf-prefixp)))))

(defthm fn-ndur-prepare-stages-the-next-txid
  (implies (and (not (fn-state-pending s))
                (fn-state-pending (fn-accept-prepare s generation msgid payload groups stamp)))
           (equal (fn-pending-txid (fn-state-pending
                                    (fn-accept-prepare s generation msgid payload groups stamp)))
                  (fn-state-next-txid s)))
  :hints (("Goal" :in-theory (enable fn-accept-prepare))))
