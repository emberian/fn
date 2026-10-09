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

; A launcher that reserved only the protected figure has no default backing.
; The exact DEFAULT contribution makes the minimum selected pool affordable.
(defconst *prst-launch-base* '(:heap 256 "custom" 8192 1024 20))
(defconst *prst-launch*
 (fn-prstartup-extend-operation-reservation *prst-launch-base* :run nil "/tmp/store" 4 8
                                           '(83886080 . 67108864) '(8589934592) nil nil))
(assert-event
 (and (equal (fn-prstartup-nth 0 *prst-launch*) :heap)
      ; 259: the decoded worker's requested-window child is the profile's
      ; :read-window-octets (262144) since window-read 390408000, in
      ; fn-dwb-reusable-baseline-vector via fn-prstartup-baseline-heap.
      (equal (fn-prstartup-nth 1 *prst-launch*) 259)
      (equal (fn-prstartup-nth 4 *prst-launch*) 1024)
      (equal (fn-prstartup-nth 5 *prst-launch*) 20)
      (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 *prst-launch*)
             '(83886080 . 67108864) (fn-prstartup-nth 4 *prst-launch*) (fn-prstartup-nth 5 *prst-launch*))
          (fn-heap-machine-octets '(8589934592)))
      (equal (fn-prstartup-status
              (fn-prstartup-plan 268435456 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256 (fn-prstartup-read-reserve 196677 4))) :refused)
      (fn-prstartup-planp
       (fn-prstartup-plan (* 1048576 (fn-prstartup-nth 1 *prst-launch*)) 67108864 268435456
                           "/tmp/store" 4 1048576 4194304 8 256
                           (fn-prstartup-read-reserve (fn-prstartup-read-extent nil) 4)))))
(assert-event
 (and (equal (fn-prstartup-extend-operation-reservation *prst-launch-base* :status nil "/tmp/store" 4 8
                                                       '(83886080 . 67108864) '(8589934592) nil nil) *prst-launch-base*)
      (equal (fn-prstartup-extend-operation-reservation *prst-launch-base* :run '(complete) "/tmp/store" 4 8
                                                       '(83886080 . 67108864) '(8589934592) nil nil) *prst-launch-base*)))
; Literal removal of each machine-fit hypothesis; the other is retained.
(assert-event
 (let* ((cold '(complete))
        (d (fn-prstartup-extend-default-reservation *prst-launch-base* cold "/tmp/store" 4 8 100 nil nil nil)))
  (and cold (equal (fn-prstartup-nth 0 d) :heap)
       (not (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) 100
                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d)) (fn-heap-machine-octets nil))))))
(assert-event
 (let* ((cold nil)
        (d (fn-prstartup-extend-default-reservation *prst-launch-base* cold "/tmp/store" 4 8 100 nil nil nil)))
  (and (not cold) (not (equal (fn-prstartup-nth 0 d) :heap))
       (not (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) 100
                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d)) (fn-heap-machine-octets nil))))))

; Discriminating runtime trigger growth: naive 128+1 MiB spends collector room.
(assert-event
 (let* ((old (* 128 1048576)) (extra 1048576) (cap (* 64 1048576))
        (backing (- old (* 2 (fn-heap-nursery-trigger old cap))))
        (naive (+ old extra))
        (next (fn-heap-grow-runtime-dynamic old extra cap)))
  (and (< naive (+ backing extra (* 2 (fn-heap-nursery-trigger naive cap))))
       (<= (+ backing extra (* 2 (fn-heap-nursery-trigger next cap))) next)
       (<= (+ old extra) next))))

; Launcher and startup agree (cold-start, 2026-10-04; ADMISSION-RESERVES-NOT-REOPEN,
; 2026-10-08).  A run is sized for the FULL store, so the launcher's figure and
; the startup's protected allowance take the same (no) observation: a
; development store at exactly its launcher's DEFAULT-extended figure is
; admitted whatever the store on disk held, and a heap one MiB below the
; DECIDED figure is refused by name, for each preset
; (fn-prstartup-run-starts-at-the-decided-figure,
; fn-prstartup-run-refuses-below-the-decided-figure).
(defconst *prst-run-core* '(615110568 . 517243296))
; The host trigger the figures are taken at: books/profile-limits.lisp's :gc-nursery-mib
; (+fnn-gc-nursery-octets+), not a copy of its value.
(defconst *prst-nursery* (* 1048576 (fn-profile-limit :gc-nursery-mib)))
(defconst *prst-fresh* '(0 . 0))
(defconst *prst-run-machine* (list (* 24 1073741824)))
(defconst *prst-run*
 (fn-prstartup-extend-operation-reservation
  (fn-heap-reserve-operation-decide :run *fn-bs-profile-development* *prst-run-core*
                                    *prst-nursery* *prst-run-machine* 32 *prst-fresh*)
  :run nil "/tmp/store" 4 8 *prst-run-core* *prst-run-machine*
  *fn-bs-profile-development* *prst-fresh*))
(assert-event
 (let ((dyn (* 1048576 (fn-prstartup-nth 1 *prst-run*))))
  (and (equal (fn-prstartup-nth 0 *prst-run*) :heap)
       (fn-prstartup-planp
        (fn-prstartup-default-plan dyn (cdr *prst-run-core*) *fn-bs-profile-development*
                                   *prst-run-core* *prst-nursery* nil nil 32 "/tmp/store" 4 8 1024
                                   *prst-fresh*))
       ; the observation is not read: unobserved and a grown store alike
       (fn-prstartup-planp
        (fn-prstartup-default-plan dyn (cdr *prst-run-core*) *fn-bs-profile-development*
                                   *prst-run-core* *prst-nursery* nil nil 32 "/tmp/store" 4 8 1024
                                   nil))
       (fn-prstartup-planp
        (fn-prstartup-default-plan dyn (cdr *prst-run-core*) *fn-bs-profile-development*
                                   *prst-run-core* *prst-nursery* nil nil 32 "/tmp/store" 4 8 1024
                                   '(9437184)))
       (stringp (fn-prstartup-refusal-line '(:refused :default-pool-heap-not-held))))))

; The decided figure starts and one MiB below it is refused by name, at the
; trigger the host sets in that heap, for each preset (a 126 GiB machine).
(defun prst-decided-agrees (profile)
 (declare (xargs :mode :program))
 (let* ((machine (list (* 126288 1048576)))
        (decided (fn-heap-reserve-operation-decide :run profile *prst-run-core*
                                                   *prst-nursery* machine 32 nil))
        (dyn (* 1048576 (fn-prstartup-nth 1 decided)))
        (below (- dyn 1048576)))
  (and (equal (fn-prstartup-nth 0 decided) :heap)
       (equal (fn-heap-operation-figure-octets :run profile *prst-run-core* *prst-nursery* nil)
              (fn-heap-operation-figure-octets :run profile *prst-run-core* *prst-nursery*
                                               '(9437184 . 100)))
       (<= (fn-prstartup-protected profile *prst-run-core*
                                   (fn-heap-nursery-trigger dyn *prst-nursery*)
                                   nil 32 '(9437184))
           dyn)
       (< below
          (fn-prstartup-protected profile *prst-run-core*
                                  (fn-heap-nursery-trigger below *prst-nursery*)
                                  nil 32 '(9437184)))
       (equal (fn-prstartup-default-plan below (cdr *prst-run-core*) profile *prst-run-core*
                                         (fn-heap-nursery-trigger below *prst-nursery*)
                                         nil nil 32 "/tmp/store" 4 8 1024 '(9437184))
              '(:refused :default-pool-heap-not-held)))))
(assert-event (prst-decided-agrees *fn-bs-profile-development*))
(assert-event (prst-decided-agrees *fn-heap-small-profile*))
(assert-event (prst-decided-agrees *fn-bs-profile-scale*))

; KEYSTONE fn-prstartup-launch-admits-owner-protected, its fields
; (cold-start, 2026-10-04; scenarios-2 SCEN-INSTALLED-HEAP-NOT-HELD).
; Satisfiable: the extension above admits, and an owner whose image
; observation exceeds the probe's (same core file) passes its protected check
; at the heap it got.  Teeth: drop the core-file hypothesis (an owner core
; with a larger file) and the check fails at that heap; the base figure alone
; (no launch floor) fails for the larger owner observation, as on 6107ceb56.
(defconst *prst-owner-core* '(615110568 . 600000000))
(assert-event
 (let* ((dyn (* 1048576 (fn-prstartup-nth 1 *prst-run*)))
        (n (fn-heap-nursery-trigger dyn (* 1048576 (fn-profile-limit :gc-nursery-mib)))))
  (and (equal (fn-prstartup-nth 0 *prst-run*) :heap)
       (equal (fn-heap-core-file *prst-owner-core*) (fn-heap-core-file *prst-run-core*))
       (<= (fn-prstartup-protected *fn-bs-profile-development* *prst-owner-core* n nil 32 *prst-fresh*)
           dyn)
       (not (<= (fn-prstartup-protected *fn-bs-profile-development* '(1615110568 . 1600000000)
                                        n nil 32 *prst-fresh*)
                dyn)))))
(assert-event
 (let* ((base (fn-heap-reserve-operation-decide :run *fn-bs-profile-development* '(615110568 . 300000000)
                                                *prst-nursery* *prst-run-machine* 32 *prst-fresh*))
        (dyn (* 1048576 (fn-prstartup-nth 1 base))))
  (and (equal (fn-prstartup-nth 0 base) :heap)
       (not (<= (fn-prstartup-protected *fn-bs-profile-development* *prst-owner-core*
                  (fn-heap-nursery-trigger dyn *prst-nursery*) nil 32 *prst-fresh*)
                dyn)))))

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
; The launcher's served run grows by the reserve too.
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
; The two page-read-startup keystones with their teeth (TEETH CONTRACT v1).  The admitted-capacity keystone states its antecedent inside a `let'; its removal is a mutation.
(defteeth fn-prstartup-accepted-default-launch-fits-machine
  :claim (((no-cold (not cold)) (accepted (equal (fn-prstartup-nth 0
                        (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)) :heap)))
          (let ((d (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed)))
   (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) core
                                  (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d))
       (fn-heap-machine-octets observations))))
  :subject fn-prstartup-extend-default-reservation
  :witness ((base *prst-launch-base*) (cold nil) (root "/tmp/store") (workers 4) (cache-limit 8) (core '(83886080 . 67108864)) (observations '(8589934592)) (profile nil) (observed nil))
  :breaks ((no-cold ((base *prst-launch-base*) (cold '(complete)) (root "/tmp/store") (workers 4) (cache-limit 8) (core 100) (observations nil) (profile nil) (observed nil)))
           (accepted ((base *prst-launch-base*) (cold nil) (root "/tmp/store") (workers 4) (cache-limit 8) (core 100) (observations nil) (profile nil) (observed nil))))
  :mutations ((read-against-unobserved-machine
               (:conclusion (let ((d (fn-prstartup-extend-default-reservation base cold root workers cache-limit core observations profile observed))) (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 d) core (fn-prstartup-nth 4 d) (fn-prstartup-nth 5 d)) (fn-heap-machine-octets nil))))
               ((base *prst-launch-base*) (cold nil) (root "/tmp/store") (workers 4) (cache-limit 8) (core '(83886080 . 67108864)) (observations '(8589934592)) (profile nil) (observed nil))
               :fault "the bound read against an unobserved machine")))

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
