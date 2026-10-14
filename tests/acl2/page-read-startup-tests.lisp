(in-package "ACL2")
(include-book "../../books/page-read-startup")
(include-book "../../books/defkeystone")

(defconst *prst-plan* (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256 (fn-prstartup-read-reserve 196677 4)))
(assert-event (and (fn-prstartup-planp *prst-plan*)
  (equal (fn-prstartup-file-capacity *prst-plan*) 256)
  (equal (fn-prstartup-cache-capacity *prst-plan*) 256)
  (equal (fn-prstartup-decoded-workers *prst-plan*) 4)
  (<= (fn-prstartup-required-heap 256 4 "/tmp/store") 268435456)))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256 (fn-prstartup-read-reserve 196677 4))) :refused))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 8 (fn-prstartup-read-reserve 196677 4))) :refused))
(assert-event (not (fn-prstartup-planp (update-nth 2 '(0 0 0 0 0) *prst-plan*))))
(assert-event (equal (fn-prstartup-decoded-workers (update-nth 2 '(0 0 0 0 0) *prst-plan*)) 0))
(assert-event (and (equal (fn-prstartup-status '(garbage)) :fault)
                  (equal (fn-prstartup-install-status :invalid-default-pool-plan) :fault)
                  (equal (fn-prstartup-install-status :invalid-resource-profile) :fault)
                  (equal (fn-prstartup-install-status :already-installed) :refused)))

; Literal positive and antecedent-removal teeth for the actual admitted plan.
(assert-event
 (and (equal (fn-prstartup-nth 0 *prst-plan*) :admitted)
      (natp (fn-prstartup-file-capacity *prst-plan*))
      (<= (max 8 (+ 1 (nfix 8))) (fn-prstartup-file-capacity *prst-plan*))
      (<= (fn-prstartup-file-capacity *prst-plan*) 256)
      (<= (fn-prstartup-required-heap (fn-prstartup-file-capacity *prst-plan*) 4 "/tmp/store")
          (nfix (- 536870912 (max 67108864 268435456))))))
(assert-event
 (let ((plan (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256 (fn-prstartup-read-reserve 196677 4))))
  (and (not (equal (fn-prstartup-nth 0 plan) :admitted))
       (not (<= (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) 4 "/tmp/store")
                1024)))))

; THE READS IN FLIGHT (lane pool-refusal, 2026-10-05).  KEYSTONES
; fn-prstartup-plan-holds-the-reads-in-flight and
; fn-prstartup-reserve-admits-a-read, their fields.  The extent of the
; peer catch-up native's profile (max-record-octets 196608): one checkpoint
; segment, 196677 octets; one read of it charges 393834 resident octets.
(defconst *prst-e* (fn-scc-segment-max-octets 196608))
(defconst *prst-d* (fn-prstartup-read-demand *prst-e*))
(defconst *prst-r* (fn-prstartup-read-reserve *prst-e* 4))
(assert-event (and (equal *prst-e* 196677) (equal *prst-d* 393834) (equal *prst-r* (+ (* 4 393834) (fn-cwq-queue-octets)))
                   (equal (fn-prstartup-read-extent *fn-bs-profile-development*)
                          (fn-scc-segment-max-octets (fn-bs-profile-max-record-octets
                                                      *fn-bs-profile-development*)))))
; A capture whose headroom past the smallest table is a read and a half (the
; native's: 22512946 octets of budget, under two reads past its table).
(defconst *prst-p* 67108864)
(defconst *prst-tight* (+ *prst-p* (fn-prstartup-required-heap 8 4 "/tmp/store")
                          (floor (* 3 *prst-d*) 2)))
(defconst *prst-old* (fn-prstartup-plan *prst-tight* *prst-p* *prst-p* "/tmp/store" 4 0 0 7 8 0))
(defconst *prst-new* (fn-prstartup-plan (+ *prst-tight* *prst-r*) *prst-p* *prst-p* "/tmp/store" 4 0 0 7 8 *prst-r*))
; One read of the extent in flight, the registrations at their quantum.
(defconst *prst-one*
 (list (+ (fn-prstartup-registration-reserve 8 "/tmp/store") *prst-d*) 0 8 1 1))
(defun prst-second (plan)
 (declare (xargs :mode :program))
 (mv-let (word next charged)
   (fn-prs-issue (fn-prstartup-nth 1 plan) (fn-prstartup-nth 2 plan) '(0 0 0 0 0) *prst-one*
                 1 18446744073709551615 (fn-prs-worker-demand *prst-e* 208 0 0))
   (declare (ignore next charged))
   word))
; Satisfiable: with the reserve the plan admits, holds its workers' reads,
; and admits the second read with one in flight.
(assert-event
 (and (fn-prstartup-planp *prst-new*)
      (equal (fn-prstartup-file-capacity *prst-new*) 8)
      (<= (+ (fn-prstartup-nth 0 (fn-prstartup-nth 2 *prst-new*))
             (fn-prstartup-registration-reserve 8 "/tmp/store") *prst-r*)
          (fn-prstartup-nth 0 (fn-prstartup-nth 1 *prst-new*)))
      (fn-prs-fundedp (fn-prstartup-nth 1 *prst-new*) (fn-prstartup-nth 2 *prst-new*)
                      '(0 0 0 0 0) *prst-one*)
      (equal (prst-second *prst-new*) :admitted)))
; Teeth: the plan without the reserve admits the same capture and then
; refuses that second read for the pool's octets (the catch-up native's
; fault); with the reserve the same capture is refused at startup, by name.
(assert-event
 (and (fn-prstartup-planp *prst-old*)
      (fn-prs-fundedp (fn-prstartup-nth 1 *prst-old*) (fn-prstartup-nth 2 *prst-old*)
                      '(0 0 0 0 0) *prst-one*)
      (equal (prst-second *prst-old*) :read-resources-unavailable)
      (not (<= (+ (fn-prstartup-nth 0 (fn-prstartup-nth 2 *prst-old*))
                  (fn-prstartup-registration-reserve 8 "/tmp/store") *prst-r*)
               (fn-prstartup-nth 0 (fn-prstartup-nth 1 *prst-old*))))
      (equal (fn-prstartup-plan *prst-tight* *prst-p* *prst-p* "/tmp/store" 4 0 0 7 8 *prst-r*)
             '(:refused :default-pool-read-headroom-unavailable))
      (stringp (fn-prstartup-refusal-line '(:refused :default-pool-read-headroom-unavailable)))))
; Teeth of the slot hypothesis: every slot busy refuses even with the reserve.
(assert-event
 (equal (car (mv-list 3 (fn-prs-issue (fn-prstartup-nth 1 *prst-new*) (fn-prstartup-nth 2 *prst-new*)
                                      '(0 0 0 0 0) (list 0 0 8 4 4)
                                      1 18446744073709551615 (fn-prs-worker-demand *prst-e* 208 0 0))))
        :read-resources-unavailable))
; The served run's DEFAULT pool (books/heap-command.lisp fn-mo-serve-pools) carries the reserve too.
(assert-event
 (equal (fn-prstartup-launch-extra *fn-bs-profile-development* 4 8 "/tmp/store")
        (+ (fn-prstartup-required-heap 9 4 "/tmp/store")
           (fn-prstartup-read-reserve (fn-prstartup-read-extent *fn-bs-profile-development*) 4))))
;; The cold-wait queue is part of the reserve (books/cold-read-wait.lisp
;; fn-cwq-queue-octets): a heap that held the reads in flight without it is
;; refused by name once it is charged, and the launcher's extra carries it.
(assert-event
 (let* ((old (* 4 (fn-prstartup-read-demand 196677)))
        (new (fn-prstartup-read-reserve 196677 4))
        (dyn (+ (fn-prstartup-required-heap 9 4 "/tmp/store") old)))
   (and (equal new (+ old (fn-cwq-queue-octets)))
        (< 0 (fn-cwq-queue-octets))
        (fn-prstartup-planp
         (fn-prstartup-plan dyn 0 0 "/tmp/store" 4 1048576 4194304 8 256 old))
        (equal (fn-prstartup-plan dyn 0 0 "/tmp/store" 4 1048576 4194304 8 256 new)
               '(:refused :default-pool-read-headroom-unavailable))
        (<= (fn-cwq-queue-octets)
            (fn-prstartup-launch-extra *fn-bs-profile-development* 4 8 "/tmp/store")))))
; TEETH-62 BEGIN
; The page-read-startup keystone with its teeth (TEETH CONTRACT v1).  It states its antecedent inside a `let'; its removal is a mutation.  The served run's launch and startup keystones are books/heap-command.lisp's and books/peer-flight-startup.lisp's (L-RUN-LAUNCH).
(defteeth fn-prstartup-admitted-capacity-is-funded
  :claim (() (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (implies (equal (fn-prstartup-nth 0 plan) :admitted) (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve)
            (fn-prstartup-available dynamic occupied protected))))))
  :subject fn-prstartup-plan
  :witness ((dynamic 536870912) (occupied 67108864) (protected 268435456) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 256) (reserve (fn-prstartup-read-reserve 196677 4)))
  :mutations ((without-admitted
               (:conclusion (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve)
            (fn-prstartup-available dynamic occupied protected)))))
               ((dynamic 1024) (occupied 0) (protected 0) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 256) (reserve (fn-prstartup-read-reserve 196677 4)))
               :fault "the antecedent dropped: (equal (fn-prstartup-nth 0 plan) :admitted)")
              (capacity-by-cache-limit
               (:conclusion (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (<= (fn-prstartup-file-capacity plan) (nfix cache-limit))))
               ((dynamic 536870912) (occupied 67108864) (protected 268435456) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 256) (reserve (fn-prstartup-read-reserve 196677 4)))
               :fault "the file capacity bounded by the cache limit, not the descriptor limit")
              (capacity-strictly-below-fd-limit
               (:conclusion (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (implies (equal (fn-prstartup-nth 0 plan) :admitted) (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (< (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve)
            (fn-prstartup-available dynamic occupied protected))))))
               ((dynamic 536870912) (occupied 67108864) (protected 268435456) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 256) (reserve (fn-prstartup-read-reserve 196677 4)))
               :fault "the descriptor-limit bound made strict: the plan takes the whole limit")
              (floor-one-above-minimum
               (:conclusion (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (implies (equal (fn-prstartup-nth 0 plan) :admitted) (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 9 (+ 2 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve)
            (fn-prstartup-available dynamic occupied protected))))))
               ((dynamic 536870912) (occupied 67108864) (protected 268435456) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 9) (reserve 0))
               :fault "the capacity floor raised by one: the minimum plan at fd-limit 9 is admitted at 9")
              (reserve-counted-twice
               (:conclusion (let ((plan (fn-prstartup-plan dynamic occupied protected root workers stack runtime cache-limit fd-limit reserve))) (implies (equal (fn-prstartup-nth 0 plan) :admitted) (and (natp (fn-prstartup-file-capacity plan))
        (<= (max 8 (+ 1 (nfix cache-limit))) (fn-prstartup-file-capacity plan))
        (<= (fn-prstartup-file-capacity plan) (nfix fd-limit))
        (<= (+ (fn-prstartup-required-heap (fn-prstartup-file-capacity plan) workers root) reserve reserve)
            (fn-prstartup-available dynamic occupied protected))))))
               ((dynamic 536870912) (occupied 67108864) (protected 268435456) (root "/tmp/store") (workers 4) (stack 1048576) (runtime 4194304) (cache-limit 8) (fd-limit 256) (reserve 200000000))
               :fault "the read reserve charged twice against the available heap")))
