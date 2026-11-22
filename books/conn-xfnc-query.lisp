; Peer request decision and subsequent wire rendering occupy separate NNTP
; turns. The completed durable registration remains in the held cursor row.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")

(fn2-csnapshot-op fn2-conn-xfnc-query (cursor generation verb) 2
 (b* (((mv status & & & & & & & & fn2-core)
       (fn2-xfnc-peer-request cursor generation verb 2048 fn2-core))
      (reason (fn2-xfnc-refusal-word status)))
   (mv status (if (unsigned-byte-p 8 reason) reason *fn2-cns-reason-unavailable*) fn2-core)))
(defthm fn2-conn-xfnc-query-reason-width
 (unsigned-byte-p 8 (mv-nth 1 (fn2-conn-xfnc-query cursor generation verb fn2-core))))
(in-theory (disable fn2-conn-xfnc-query))
(defcost fn2-conn-xfnc-query :answers t :bytes 4096
 :tables (fn2-core-reads fn2-core-ranges fn2-core-seeks fn2-core-succ-txns fn2-core-run-cursors fn2-core-run-paths
          fn2-core-fields fn2-core-machines fn2-core-control fn2-cursor-table fn2-cns-table fn2-core-pool)
 :doc "Drive one durable request turn and retain its wire disposition on the connection.")

(fn2-csnapshot-op fn2-conn-xfnc-result (cursor generation answer reason) 1
 (b* (((mv login & conn cgen) (fn2-xfnc-live-login cursor generation fn2-core))
      ((unless (eq login :ok)) (mv :access fn2-core)))
   (cond
    ((equal answer *fn2-conn-xfnc-answer-register*)
     (fn2-xfnc-register-reply cursor generation (fn2-cursor-row-peer-stream cursor fn2-core)
       (fn2-cursor-row-peer-consumer cursor fn2-core) (fn2-cursor-row-peer-epoch cursor fn2-core)
       (fn2-cursor-row-peer-version cursor fn2-core) (fn2-cursor-row-peer-view cursor fn2-core)
       (fn2-cursor-row-peer-position cursor fn2-core) fn2-core))
    ((equal answer *fn2-conn-xfnc-answer-uncertain*) (fn2-xfnc-reply-uncertain conn cgen fn2-core))
    ((and (equal answer *fn2-conn-xfnc-answer-refused*) (posp reason)
          (< reason (len *fn2-cns-reason-words*)))
     (fn2-xfnc-render-reply conn cgen 1 (fn2-cns-reason-word *fn2-cns-verb-read* reason)
                            0 0 0 0 0 0 0 fn2-core))
    (t (mv :state fn2-core)))))
(in-theory (disable fn2-conn-xfnc-result))
(defcost fn2-conn-xfnc-result :answers t :bytes 2048
 :tables (fn2-core-pool fn2-core-fields fn2-core-digests fn2-core-b3)
 :doc "Stage the held peer result into its exact live connection's TX after the decision turn.")

;; TX stays private across collection and final frame assembly. Only a
;; complete renderer success can enter the connection's ordinary SEND arm.
(fn2-csnapshot-op fn2-conn-xfnc-page-step (cursor generation stage) 1
 (cond
  ((equal stage *fn2-conn-xfnc-answer-collect*)
   (b* (((mv found revision) (fn2-core-ready-history-revision fn2-core))
        ((unless (and (eq found :ok) (posp revision))) (mv :unavailable fn2-core))
        ((mv status fn2-core) (fn2-xfnc-read-page-turn cursor generation revision 4096 fn2-core)))
     (cond ((eq status :ready) (mv :collected fn2-core))
           ((member-eq status '(:busy :exhausted)) (fn2-xfnc-page-fail cursor :dependency fn2-core))
           (t (mv status fn2-core)))))
  ((equal stage *fn2-conn-xfnc-answer-seal*) (fn2-xfnc-render-page-turn cursor generation fn2-core))
  (t (mv :state fn2-core))))
(in-theory (disable fn2-conn-xfnc-page-step))
(defcost fn2-conn-xfnc-page-step :answers t :bytes 4096 :descriptors 1
 :tables (fn2-core-reads fn2-core-ranges fn2-core-seeks fn2-core-succ-txns fn2-core-run-cursors
          fn2-core-run-paths fn2-core-fields fn2-core-fc fn2-core-pool fn2-core-b3 fn2-core-digests
          fn2-cursor-table fn2-core-csnapshot fn2-core-journal-lease fn2-core-event-read fn2-core-journal-members
          fn2-core-commit-root fn2-core-extents fn2-core-alloc-edges fn2-core-ops fn2-core-control
          fn2-core-mk fn2-core-fc-context)
 :doc "Collect or seal one bounded turn of a protected history page.")
