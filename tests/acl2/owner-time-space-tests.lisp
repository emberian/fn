; Witnesses and teeth for the free space (PRF-359) and health's disk state
; (PRF-358) in books/owner-time-model.lisp (lane health-truth, 2026-09-28).
; Split from tests/acl2/owner-time-model-tests.lisp (its reached states and
; helpers are included, not re-run) to keep each test book under 10 s.
(in-package "ACL2")
(include-book "owner-time-model-tests")
; =============================================================================
; Lane health-truth (2026-09-28): the free space (PRF-359, PKT-872) and
; health's disk state (PRF-358, PKT-879).
;
; Reached: the idle owner of *otmt-s0*'s START (no barrier pending) records
; space observations at 20,000 ms: room (1,000,000 free, 100,000 needed),
; then full (5,000 free), then room again; and statvfs failing (nil).
(defun htt-space (s reading free need) (otmt-disk s :space reading (list free need)))
(defun htt-space-word (s reading free need) (otmt-disk-word s :space reading (list free need)))
(defconst *htt-need* (fn-otm-space-need 16777216 4096 1024))
(assert-event (equal *htt-need* (+ 4096 (* 2 16777216) 1024)))
; An unset `disk-reserve-octets' row is ACL2's 64 MiB default.
(assert-event (equal (fn-otm-space-need 16777216 4096 0) (+ 4096 (* 2 16777216) 67108864)))
(defconst *htt-idle* (otmt-at *otmt-s1a* 20000))
(assert-event (and (not (fn-otm-disk-pending (fn-otm-disk *htt-idle*)))
                   (fn-otm-space-due-p *htt-idle*)
                   (equal (fn-otm-admit-post *htt-idle*) :admit)))
(assert-event (equal (htt-space-word *htt-idle* 20000 100000000 *htt-need*) :none))
(defconst *htt-room* (htt-space *htt-idle* 20000 100000000 *htt-need*))
(assert-event (and (equal (fn-otm-mode *htt-room*) :ok)
                   (equal (fn-otm-admit-post *htt-room*) :admit)
                   (not (fn-otm-space-due-p *htt-room*))
                   (fn-otm-space-due-p (otmt-at *htt-room* 21000))
                   (equal (car (fn-otm-health-disk *htt-room*)) :clear)))
; Full: the word, the mode, the shed, the reason on every page.
(assert-event (equal (htt-space-word *htt-room* 20500 5000 *htt-need*) :became-full))
(defconst *htt-full* (htt-space *htt-room* 20500 5000 *htt-need*))
(assert-event (and (equal (fn-otm-mode *htt-full*) :full)
                   (fn-otm-full-p *htt-full*)
                   (equal (fn-otm-admit-post *htt-full*) :shed)
                   (equal (car (fn-otm-health-disk *htt-full*)) :held)
                   (fn-otm-full-line-p (fn-otm-space-line (fn-otm-space *htt-full*)))
                   (not (fn-otm-slow-line-p (fn-otm-disk-lines *htt-full*)))))
(assert-event (equal (fn-otm-space-line (fn-otm-space *htt-full*))
                     (otmt-text "disk full: free-octets=5000 need-octets=33559552 posts=try-later
")))
(assert-event (equal (fn-otm-post-command-reply *htt-full*)
                     (append (otmt-text "440 posting not permitted now; the disk is full (5000 octets free, 33559552 needed), try again later")
                             '(13 10))))
(assert-event (equal (fn-otm-shed-reply *htt-full*)
                     (append (otmt-text "441 posting failed; the disk is full (5000 octets free, 33559552 needed): nothing was stored, try again later")
                             '(13 10))))
(assert-event (equal (fn-otm-log-line *htt-full* :became-full)
                     (otmt-text "disk full: 5000 octets free, 33559552 needed; new posts are refused try-later until there is room")))
(assert-event (equal (cdr (fn-otm-health-disk *htt-full*))
                     (otmt-text " mode=full free-octets=5000 need-octets=33559552 posts=try-later")))
; A clock event, an issue and a return keep the space (and stay full).
(assert-event (and (fn-otm-full-p (otmt-at *htt-full* 30000))
                   (fn-otm-full-p (otmt-disk *htt-full* :issue 30000 0))))
; Recovery: an observation with room, no operator action.
(assert-event (equal (htt-space-word *htt-full* 21000 50000000 *htt-need*) :space-recovered))
(defconst *htt-back* (htt-space *htt-full* 21000 50000000 *htt-need*))
(assert-event (and (equal (fn-otm-admit-post *htt-back*) :admit)
                   (equal (fn-otm-mode *htt-back*) :ok)))
; Unobserved (statvfs gave nothing): never :full, the line says so.
(assert-event (equal (htt-space-word *htt-full* 21000 nil *htt-need*) :space-unobserved))
(defconst *htt-unobs* (htt-space *htt-full* 21000 nil *htt-need*))
(assert-event (and (equal (fn-otm-admit-post *htt-unobs*) :admit)
                   (not (fn-otm-sp-observedp (fn-otm-space *htt-unobs*)))
                   (fn-otm-space-due-p *htt-unobs*)))
; Full while a barrier is slow: the time's reason is the one named, the
; mode is the time's, and both lines are on the page.
(defconst *htt-slow-full* (htt-space *t2-slow* 12000 5000 *htt-need*))
(assert-event (and (equal (fn-otm-mode *htt-slow-full*) :slow)
                   (equal (fn-otm-admit-post *htt-slow-full*) :shed)
                   (equal (fn-otm-shed-reply *htt-slow-full*) (fn-otm-shed-reply *t2-slow*))
                   (fn-otm-slow-line-p (fn-otm-disk-lines *htt-slow-full*))
                   (fn-otm-full-line-p (fn-otm-space-line (fn-otm-space *htt-slow-full*)))))

; --- KEYSTONE fn-otm-admit-keeps-the-space-need, positive (*htt-room*: admitted,
; observed, free >= need) and the tooth: without the observation an
; unobserved space admits with free (0) below the need.
(assert-event (and (equal (fn-otm-admit-post *htt-room*) :admit)
                   (fn-otm-sp-observedp (fn-otm-space *htt-room*))
                   (<= (fn-otm-sp-need (fn-otm-space *htt-room*))
                       (fn-otm-sp-free (fn-otm-space *htt-room*)))))
(assert-event (and (equal (fn-otm-admit-post *htt-unobs*) :admit)
                   (not (fn-otm-sp-observedp (fn-otm-space *htt-unobs*)))
                   (< (fn-otm-sp-free (fn-otm-space *htt-unobs*))
                      (fn-otm-sp-need (fn-otm-space *htt-unobs*)))))
(must-fail-checked
 (defthm htt-tooth-admit-needs-the-observation
   (implies (equal (fn-otm-admit-post s) :admit)
            (<= (fn-otm-sp-need (fn-otm-space s)) (fn-otm-sp-free (fn-otm-space s))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post)))))

; --- fn-otm-full-sheds: positive *htt-full*; tooth: with room it admits.
(must-fail-checked
 (defthm htt-tooth-full-needs-below-the-need
   (implies (fn-otm-sp-observedp (fn-otm-space s))
            (equal (fn-otm-admit-post s) :shed))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post)))))

; --- fn-otm-space-recovers: positive *htt-back*; teeth: below the need it
; stays full; past the deadline (*t2-slow*) it stays shed.
(assert-event (equal (fn-otm-admit-post (htt-space *htt-full* 21000 100 *htt-need*)) :shed))
(assert-event (equal (fn-otm-admit-post (htt-space *t2-slow* 12000 50000000 *htt-need*)) :shed))
(must-fail-checked
 (defthm htt-tooth-recovers-needs-room
   (implies (not (fn-otm-disk-overdue-p (fn-otm-disk s) (max (fn-otm-now s) (nfix reading))))
            (equal (fn-otm-admit-post (mv-nth 1 (fn-otm-disk-event s :space reading (list free need))))
                   :admit))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post fn-otm-disk-event)))))
(must-fail-checked
 (defthm htt-tooth-recovers-needs-the-deadline
   (implies (<= (nfix need) free)
            (equal (fn-otm-admit-post (mv-nth 1 (fn-otm-disk-event s :space reading (list free need))))
                   :admit))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post fn-otm-disk-event)))))

; --- fn-otm-space-need-covers-two-batches: positive; a tooth per hypothesis
; (a third batch, or a batch over OMAX, eats into the reserve).
(assert-event (<= (+ 4096 1024) (- *htt-need* (+ 16777216 16777216))))
(assert-event (< (- *htt-need* (+ 16777216 16777217)) (+ 4096 1024)))
(must-fail-checked
 (defthm htt-tooth-two-batches-need-the-bound
   (implies (and (natp f) (<= (fn-otm-space-need omax reserve extra) f)
                 (natp b1) (natp b2) (<= b1 (nfix omax)))
            (<= (+ (nfix reserve) (fn-otm-space-extra-of-limit extra)) (- f (+ b1 b2))))
   :rule-classes nil))
(must-fail-checked
 (defthm htt-tooth-two-batches-need-the-need
   (implies (and (natp f) (natp b1) (natp b2) (<= b1 (nfix omax)) (<= b2 (nfix omax)))
            (<= (+ (nfix reserve) (fn-otm-space-extra-of-limit extra)) (- f (+ b1 b2))))
   :rule-classes nil))

; --- The restated slice-1 theorems' new hypothesis (not full): the full
; state is their counterexample.
(assert-event (and (fn-otm-disk-pending (fn-otm-disk *t2-stalled*))
                   (equal (fn-otm-admit-post
                           (otmt-disk (htt-space *t2-stalled* 15000 5000 *htt-need*) :return 40000 0))
                          :shed)))
(must-fail-checked
 (defthm htt-tooth-return-recovers-needs-room
   (implies (fn-otm-disk-pending (fn-otm-disk s))
            (equal (fn-otm-admit-post (mv-nth 1 (fn-otm-disk-event s :return reading arg))) :admit))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post fn-otm-disk-event)))))
(must-fail-checked
 (defthm htt-tooth-shed-only-past-the-deadline-needs-room
   (implies (equal (fn-otm-admit-post s) :shed)
            (fn-otm-disk-pending (fn-otm-disk s)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-otm-admit-post)))))

; --- KEYSTONE fn-otm-health-disk-held-iff-stalled-or-full, both directions at
; reached states: held in :stalled (the stall's duration on the line) and
; :full; clear in :ok and :slow (provisional, PKT-853 (b)).
(assert-event (and (equal (car (fn-otm-health-disk *t2-stalled*)) :held)
                   (equal (cdr (fn-otm-health-disk *t2-stalled*))
                          (otmt-text " mode=stalled pending-ms=5000 stall-ms=5000 members=uncertain posts=try-later"))
                   (equal (car (fn-otm-health-disk *t2-slow*)) :clear)
                   (equal (fn-otm-mode *t2-slow*) :slow)
                   (equal (car (fn-otm-health-disk *otmt-s1*)) :clear)))

; --- The journal carries the space: a run with :space events replays to
; agreement (fn-otm-journal-determines-the-decisions with the fifth kind).
(defconst *htt-steps*
  (list (list :event :space 20000 (list 100000000 *htt-need*))
        (list :event :space 20500 (list 5000 *htt-need*))
        (list :event :space 20600 (list nil *htt-need*))
        (list :event :space 21000 (list 50000000 *htt-need*))))
(defconst *htt-entries* (t2-run-entries *htt-idle* *htt-steps*))
(assert-event (equal (strip-cadrs *htt-entries*) '(6 6 6 6)))
(assert-event (equal (car (last *htt-entries*)) (list (+ 4 (fn-otm-jseq *htt-idle*)) 6 21000 50000000 *htt-need* 1 7)))
(assert-event (and (fn-otm-run-okp *htt-steps*)
                   (equal (t2-replay-verdict *htt-idle* (fn-otm-journal-read (fn-otm-jlines *htt-entries*)))
                          :agrees)
                   (equal (fn-otm-clock (t2-replay-state *htt-idle* (fn-otm-journal-read (fn-otm-jlines *htt-entries*))))
                          (fn-otm-clock (t2-run-state *htt-idle* *htt-steps*)))))
; Tooth: a journaled :space whose word is not what the event decides.
(assert-event (equal (t2-replay-verdict *htt-idle*
                                        (list (list (+ 1 (fn-otm-jseq *htt-idle*)) 6 20000 5000 *htt-need* 1 7)))
                     (list :diverged (+ 1 (fn-otm-jseq *htt-idle*)))))

; --- The served read at a full disk (PRF-323's path, reached): a POST
; command on the open connection is answered 440 with the space's reason,
; no article is offered.
(defconst *htt-open-full* (t2r-host-read *t2r-open* *orrt-views* 0 *t2r-post* *htt-full*))
(assert-event
 (let ((effects (fn-own-tls-result-effects *htt-open-full*)))
   (and (equal effects (list (fn-nntp-reply-effect (fn-otm-post-command-reply *htt-full*))))
        (not (fn-post-offeredp effects))
        (equal (fn-own-tls-result-consumed *htt-open-full*) (len *t2r-post*)))))
