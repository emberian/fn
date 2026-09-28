; Witnesses and teeth for books/feed-restart-domain.lisp (lane time-bars,
; 2026-09-28; PRF-385).  The feed is REACHED from fn-feed-open through the
; transitions the host drives (fn-feed-enqueue, fn-feed-tick-step,
; fn-feed-observe) and the replay of the journal those transitions wrote.
(in-package "ACL2")
(include-book "../../books/feed-restart-domain")
; The live driver's records (the :restart event is fn-feed-restart there).
(include-book "../../books/feed-events")

(defconst *frd-peer* '(105 110 110))                       ; "inn"
(defconst *frd-a* '(60 97 64 102 110 62))                  ; "<a@fn>"
(defconst *frd-limits* (fn-feed-limits 4 1000 3 t))
(defconst *frd-contact* (fn-sched-contact "inn" 0 1000000000000))
; Run 1 has been up for three days: its monotonic clock reads 259,200,000 ms.
(defconst *frd-late* (fn-clock-observation 259200000 0 0 nil))
; Run 2, a new process: its clock starts near zero.
(defconst *frd-new* (fn-clock-observation 1500 0 0 nil))

(defconst *frd0* (fn-feed-enqueue (fn-feed-open *frd-peer* *frd-limits* *frd-contact* 7) *frd-a* 1))
; Run 1 offers the article (CHECK) and the peer says 431: back off from
; 259,200,000 ms.
(defconst *frd-offered* (nth 0 (mv-list 2 (fn-feed-tick-step *frd0* *frd-late*))))
(defconst *frd-backed*
  (nth 0 (mv-list 2 (fn-feed-observe *frd-offered* (fn-feed-response 431 *frd-a*) nil *frd-late*))))
(assert-event (fn-feedp *frd-backed*))
(assert-event (< 259200000 (fn-feed-backoff-until *frd-backed*)))
(assert-event (equal (fn-feed-state-of *frd-a* (fn-feed-queue *frd-backed*)) :queued))

; The restart (run 2 opens), then the reconnection.
(defconst *frd-restarted* (fn-feed-with-conn (fn-feed-restart *frd-backed*) 9))
; Positive witness of the keystone: the complete antecedent (a feed, a
; natural deadline) and every conclusion.
(assert-event (and (fn-feedp *frd-backed*)
                   (natp 5)
                   (equal (fn-feed-restart
                           (fn-feed-make (fn-feed-peer *frd-backed*) (fn-feed-limits-of *frd-backed*)
                                         (fn-feed-queue *frd-backed*) (fn-feed-contact *frd-backed*)
                                         5 (fn-feed-conn *frd-backed*)
                                         (fn-feed-next-attempt *frd-backed*)))
                          (fn-feed-restart *frd-backed*))
                   (equal (fn-feed-backoff-until (fn-feed-restart *frd-backed*)) 0)
                   (<= 0 (fn-clock-monotonic *frd-new*))))
; What it buys: run 2's first tick offers the article again (a CHECK: never a
; blind TAKETHIS), at a reading far below run 1's deadline.
(assert-event (equal (fn-feed-selection *frd-restarted* *frd-new*) *frd-a*))
; The attempt count, the semantic observation, crosses the restart.
(assert-event (equal (fn-feed-entry-attempts (fn-feed-find *frd-a* (fn-feed-queue *frd-restarted*)))
                     (fn-feed-entry-attempts (fn-feed-find *frd-a* (fn-feed-queue *frd-backed*)))))
; Tooth (the defect): the same feed reconnected WITHOUT the restart -- the
; old domain's deadline kept -- offers nothing at run 2's reading.
(assert-event (null (fn-feed-selection (fn-feed-with-conn *frd-backed* 9) *frd-new*)))

; The same through the journal, as the host opens: replay run 1's records,
; then the restart.
(defconst *frd-journal*
  (append (fn-feed-live-records *frd0* (list :tick *frd-late*))
          (fn-feed-live-records *frd-offered* (list :reply (fn-feed-response 431 *frd-a*) nil *frd-late*))))
(defconst *frd-replayed* (fn-feed-replay (fn-feed-durable-projection *frd0*) *frd-journal*))
(assert-event (< 259200000 (fn-feed-backoff-until *frd-replayed*)))
(assert-event (equal (fn-feed-selection (fn-feed-with-conn (fn-feed-restart *frd-replayed*) 9) *frd-new*)
                     *frd-a*))

; Hypothesis removal, (fn-feedp F): a value that is not a feed is returned
; unchanged by the restart, deadline and all (natp B holds; the conclusion
; fails).
(defconst *frd-bad* (fn-feed-make *frd-peer* *frd-limits* nil *frd-contact* 99 nil 0))
(assert-event (and (not (fn-feedp *frd-bad*))
                   (natp 5)
                   (equal (fn-feed-backoff-until (fn-feed-restart *frd-bad*)) 99)))
