; Teeth for books/heap-reservation (lane image-floor, HST-025, extending
; PRF-198): the decisions on the lane's core and the OpenBSD VM's datasize,
; the keystone's reachable witness and, per hypothesis, a counterexample where
; the others hold and the conclusion fails, with the must-fail of the theorem
; without it; the exact refusal and heap-figure's refusals passed through;
; the report lines and the exit code.
(in-package "ACL2")
(include-book "../../books/heap-reservation")
(include-book "../../books/codec-attach")
(include-book "../../books/connection-budget")
(include-book "../../books/store-recover-stream")
(include-book "../../books/payload-arena-paged")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

(defconst *hrt-core* 192152584)              ; lane image-floor's fn-host.core
(defconst *hrt-nursery* (* 64 1024 1024))    ; +fnn-gc-nursery-octets+
(defconst *hrt-datasize* (* 1536 *fn-heap-mib*)) ; OpenBSD's default login class

(defun hrt-conclusion (profile core nursery observations connections)
  (declare (xargs :mode :program))
  (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
    (and (equal (fn-heap-decision-mb r)
                (fn-heap-decision-mb (fn-heap-decide profile core nursery observations)))
         (<= (+ *fn-heap-mux-loops* (fn-native-control-max-active-clients)
                *fn-heap-fixed-threads*)
             (fn-heap-reserve-threads r))
         (<= *fn-heap-stack-octets*
             (* 1024 (fn-heap-reserve-stack-kib r)))
         (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                (fn-heap-core-file core)
                (* (fn-heap-reserve-threads r)
                   (+ (* 1024 (fn-heap-reserve-stack-kib r))
                      *fn-heap-thread-runtime-octets*)))
             (fn-heap-machine-octets observations)))))

(defun hrt-hyps (profile core nursery observations connections)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-reserve-decide profile core nursery observations
                                            connections))
               :heap)))

; The small preset's reservation (reservation-after-flip; re-measured by
; reservation-figure): heap-figure's heap at the preset's bounds, 1,572 MB
; on this core since lane heap-bounds derived the records' term from the
; profile's limits (929 MB before, with the 12 KiB record constant that
; long headers exceeded), and 30 threads -- the
; 12 fixed, the 2 I/O loops, the 16 control clients -- of a 1 MiB stack
; each, whatever the connections (since connection-multiplexing a
; connection is no thread; the reservation counted 60 before this lane).
; On OpenBSD's 1,536 MiB datasize the preset's full store fits (1,044 MB
; with the core and the threads; lane heap-bounds' uncharged header term made
; it 1,906 MB, which did not, until lane heap-pool charged the header to the
; history budget), and so does its first run (heap-reservation's init
; judgement).
(defconst *hrt-4096* (list (* 4096 *fn-heap-mib*)))
(assert! (equal (fn-heap-stack-kib *fn-heap-small-profile*) 1024))
(assert! (equal (fn-heap-thread-count 32) 30))
(assert! (equal (fn-heap-thread-count 0) 30))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        *hrt-4096* 32)
                '(:heap 710 "small" 4096 1024 30)))
(assert! (equal (car (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core*
                                             *hrt-nursery* (list *hrt-datasize*) 32))
                :heap))
(assert! (equal (fn-heap-reserve-full-store-decide *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* (list *hrt-datasize*) 32)
                '(:heap 710 "small" 1536 1024 30)))
(assert! (<= (fn-heap-reservation-octets 710 *hrt-core* 1024 30)
             *hrt-datasize*))

; The threads push it past a machine the heap alone fits.
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     (list (* 800 *fn-heap-mib*))))
                :heap))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list (* 800 *fn-heap-mib*)) 32)
                (list :refused :machine-cannot-hold-threads
                      (fn-heap-mb-of (fn-heap-reservation-octets 710 *hrt-core* 1024 30))
                      800)))

; The default profile's 16 MiB article: the same stack; heap-figure refuses
; the profile first.
(assert! (equal (fn-heap-stack-kib *fn-bs-profile-defaults*) 1024))
(assert! (equal (car (fn-heap-reserve-decide *fn-bs-profile-defaults* *hrt-core*
                                             *hrt-nursery* (list 132000000000) 32))
                :refused))

; No store: heap-figure's store-less figure (1,024 MB, not the machine: PKT-686
; item 3), SBCL's default stack, one thread.
(assert! (equal (fn-heap-reserve-decide nil *hrt-core* *hrt-nursery*
                                        (list (* 2048 *fn-heap-mib*)) 32)
                '(:heap 1024 "none" 2048 2048 1)))

; The keystone: the reachable witness, then per hypothesis a counterexample
; where the others hold, it fails, the conclusion fails, and the must-fail
; of the theorem without it under the keystone's own theory, no induction.
(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-4096* 32)
                '(t t)))
(assert! (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-4096* 32))

; Without the admitted profile: no store is one thread, not the node's.
(assert! (equal (hrt-hyps nil *hrt-core* *hrt-nursery* (list *hrt-datasize*) 32)
                '(nil t)))
(assert! (not (hrt-conclusion nil *hrt-core* *hrt-nursery* (list *hrt-datasize*) 32)))
(must-fail-checked
 (defthm hrt-without-admitted
   (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
     (implies (equal (car r) :heap)
              (<= (+ *fn-heap-mux-loops* (fn-native-control-max-active-clients)
                     *fn-heap-fixed-threads*)
                  (fn-heap-reserve-threads r))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-heap-stack-kib fn-heap-thread-count
                             fn-heap-reservation-octets)
                            (fn-heap-reserve-decide fn-heap-decide
                             fn-bs-profile-admittedp fn-heap-machine-octets
                             fn-heap-decide-refuses-exactly-past-the-machine
                             fn-native-control-max-active-clients
                             fn-heap-mb-of))))))

; Without the accepted reservation: the thread refusal on 800 MB.
(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                          (list (* 800 *fn-heap-mib*)) 32)
                '(t nil)))
(assert! (not (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                              (list (* 800 *fn-heap-mib*)) 32)))
(must-fail-checked
 (defthm hrt-without-heap
   (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
     (implies (fn-bs-profile-admittedp profile)
              (<= (+ *fn-heap-mux-loops* (fn-native-control-max-active-clients)
                     *fn-heap-fixed-threads*)
                  (fn-heap-reserve-threads r))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-heap-stack-kib fn-heap-thread-count
                             fn-heap-reservation-octets)
                            (fn-heap-reserve-decide fn-heap-decide
                             fn-bs-profile-admittedp fn-heap-machine-octets
                             fn-heap-decide-refuses-exactly-past-the-machine
                             fn-native-control-max-active-clients
                             fn-heap-mb-of))))))

; A natural connection count is no longer a hypothesis: the threads do not
; depend on it (the weakened theorem was proved first).
(assert! (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-4096* 1/2))

; -----------------------------------------------------------------------------
; The refusal is exact at the boundary: the machine exactly the reservation
; is accepted, one octet less is refused.
(defconst *hrt-exact*
  (fn-heap-reservation-octets 710 *hrt-core* 1024 30))
(assert! (equal (car (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core*
                                             *hrt-nursery* (list *hrt-exact*) 32))
                :heap))
(assert! (equal (car (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core*
                                             *hrt-nursery* (list (1- *hrt-exact*)) 32))
                :refused))
; heap-figure's own refusals pass through.
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        nil 32)
                '(:refused :machine-memory-unobserved 0 0)))

; -----------------------------------------------------------------------------
; The lines the probe prints and the exit code.
(assert! (equal (fn-heap-reserve-report-line '(:heap 816 "small" 1536 1024 60))
                "heap=816 MB profile=small machine=1536 MB stack=1024 KB threads=60"))
(assert! (equal (fn-heap-reserve-report-line
                 '(:refused :machine-cannot-hold-threads 1300 900))
                "refused machine-cannot-hold-threads reservation=1300 MB machine=900 MB"))
(assert! (equal (fn-heap-reserve-report-line
                 '(:refused :machine-cannot-hold-profile 2671 2048))
                "refused machine-cannot-hold-profile heap=2671 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-threads 1300 900))
                1))
(assert! (equal (fn-heap-decision-exit-code '(:heap 816 "small" 1536 1024 60)) 0))

;; -----------------------------------------------------------------------------
; `init' (PKT-582 in gpt-6's wave-5 shape): the budget is the least of the
; physical memory less the OS's reserve (a quarter, at least 512 MiB), each
; limit and FN_INIT_BUDGET_MB; a capacity-free request takes the largest
; friend rung the budget holds, else small (conservative, PKT-707), or scale, development,
; small under FN_INIT_SIZING=largest; any other request is written as named,
; the line saying whether the budget holds it.  hbox (123 GiB): development,
; budget 94,464 MB; largest: scale.  Under MemoryMax=2G: small.  A 2 GiB
; machine: small within 1,536 MB.  The default mission (1 MiB articles, 8
; groups): under 2 GiB the 16 MiB rung with its fields, 1,851 MB (the
; stacks no longer grow with the article); under 1 GiB refused by name,
; never lowered (its small capacity's first run is 1,327 MB since the
; figure takes the measured 12 KiB a record: lane reservation-figure).
(defconst *hrt-bare* '(:default nil))
(defconst *hrt-mission* '(:default ((4 . 1048576) (5 . 8))))
(defconst *hrt-gib* (* 1024 *fn-heap-mib*))
(defconst *hrt-hbox* (* 123 *hrt-gib*))
(defconst *hrt-largest* '(108 97 114 103 101 115 116))
(defconst *hrt-2g* (list (* 2048 *fn-heap-mib*)))
(defconst *hrt-1g* (list (* 1024 *fn-heap-mib*)))
(defmacro hrt-init (request physical limits &optional budget sizing)
  `(fn-heap-init-decide ,request *hrt-core* *hrt-nursery* ,physical ,limits
                        ,budget ,sizing))
(assert! (equal (fn-heap-small-candidate *hrt-bare*) *fn-heap-small-request*))
(assert! (equal (fn-heap-os-reserve-octets (* 2 *hrt-gib*)) (* 512 *fn-heap-mib*)))
(assert! (equal (fn-heap-os-reserve-octets *hrt-hbox*) (floor *hrt-hbox* 4)))
(defconst *hrt-top* '(:development ((1 . 131072) (2 . 67108864) (3 . 196608)
                                      (5 . 16) (7 . 128))))
(assert! (equal (fn-heap-friend-candidate *hrt-bare* 67108864) *hrt-top*))
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil)
                (list :init *hrt-top* "custom" 3216 94464 :conservative t)))
; FN_INIT_SIZING=largest: the largest preset whose FULL store the budget
; holds -- scale since lane membership-budget: its memberships are charged
; to its 768 MiB history (at most H / 320 of them), so its full store's run
; is 10,914 MB where 4,096 records of up to 65,535 memberships each made
; 171,623 MB (reservation-after-flip).
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil nil *hrt-largest*)
                '(:init (:scale nil) "scale" 16226 94464 :largest t)))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) :init))
; Under a 2,048 MB budget the 32 MiB rung; a 2 GiB machine (1,536 MB after
; the OS's share: the OpenBSD friend's) the 16 MiB rung, a 3 GiB one the 32
; MiB rung.  (Lane heap-bounds' uncharged header term refused the 2 GiB
; machine even the small floor, 1,906 MB; lane heap-pool charges the header
; to the history budget.)
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*))
                (fn-heap-friend-candidate *hrt-bare* 33554432)))
(assert! (equal (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil)
                (list :init (fn-heap-friend-candidate *hrt-bare* 16777216) "custom" 1388 1536
                      :conservative t)))
(assert! (equal (hrt-init *hrt-bare* (* 3 *hrt-gib*) nil)
                (list :init (fn-heap-friend-candidate *hrt-bare* 33554432) "custom" 1997 2304
                      :conservative t)))
; FN_INIT_BUDGET_MB=4096 on hbox: development, within 4,096 MB.
(assert! (equal (nth 4 (hrt-init *hrt-bare* *hrt-hbox* nil '(52 48 57 54))) 4096))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* nil '(120))) :refused))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* nil nil '(120))) :refused))
; The mission's fields are kept: development with them on hbox, the small
; capacity with them under 2 GiB, refused under 1 GiB, never a lower article
; bound.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* nil))
                (fn-heap-friend-candidate *hrt-mission* 67108864)))
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*))
                (fn-heap-friend-candidate *hrt-mission* 16777216)))
(assert! (equal (fn-bs-profile-max-article-octets
                 (fn-bs-profile-resolve (fn-heap-small-candidate *hrt-mission*) nil))
                1048576))
(assert! (equal (nth 3 (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*)) 1483))
; Under 1 GiB the mission's small capacity's first run (1,327 MB) is refused
; by name, as under 512 MiB: never lowered.
(defconst *hrt-half* (list (* 512 *fn-heap-mib*)))
(assert! (equal (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*)
                '(:refused :init-budget-cannot-hold-profile 1153 1024 "custom"
                           :conservative)))
(assert! (equal (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)
                '(:refused :init-budget-cannot-hold-profile 1153 512 "custom"
                           :conservative)))
(assert! (equal (fn-heap-reserve-full-store-decide
                 (fn-bs-profile-resolve (fn-heap-small-candidate *hrt-mission*) nil)
                 *hrt-core* *hrt-nursery* *hrt-half* 32)
                '(:refused :machine-cannot-hold-profile 819 512)))
; An operator's request is written as named when the budget holds it; past
; the budget it is REFUSED by name with both numbers (ember, 2026-09-27
; 17:30Z; lane membership-budget), unless the operator names a target
; budget that holds it (FN_INIT_BUDGET_MB: a store made for another
; machine), when it is written with within-budget=no and the target; an
; invalid one is refused.
(defconst *hrt-target-16g* '(49 54 51 56 52))   ; FN_INIT_BUDGET_MB=16384
(defconst *hrt-target-4g* '(52 48 57 54))       ; FN_INIT_BUDGET_MB=4096
(assert! (equal (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*)
                '(:refused :init-budget-cannot-hold-profile 16226 2048 "scale"
                           :requested)))
(assert! (equal (fn-heap-init-decision-request (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*))
                nil))
(assert! (equal (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g* *hrt-target-16g*)
                '(:init (:scale nil) "scale" 16226 2048 :requested nil 16384)))
; A named target that does not hold it either: refused, the budget this
; machine and the target allow.
(assert! (equal (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g* *hrt-target-4g*)
                '(:refused :init-budget-cannot-hold-profile 16226 2048 "scale"
                           :requested)))
(assert! (equal (hrt-init '(:development ((1 . 100000))) *hrt-hbox* nil)
                '(:init (:development ((1 . 100000))) "custom" 3775 94464
                  :requested t)))
; The gate's profile (scale, T = 2^20, 4 KiB articles): 37,448 MB, held
; within hbox's 94,464 MB budget; under 2 GiB refused by name.
(assert! (equal (car (hrt-init '(:scale ((1 . 1048576) (4 . 4096))) *hrt-hbox* nil))
                :init))
(assert! (equal (car (hrt-init '(:scale ((1 . 1048576) (4 . 4096))) *hrt-hbox* *hrt-2g*))
                :refused))
(assert! (equal (car (hrt-init '(:default ((2 . 4096))) *hrt-hbox* nil)) :refused))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-bare* (* 3 *hrt-gib*) nil))
                "init: profile=custom sizing=conservative reservation=1997 MB budget=2304 MB within-budget=yes"))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil))
                "init: profile=custom sizing=conservative reservation=1388 MB budget=1536 MB within-budget=yes"))
(assert! (equal (fn-heap-init-report-line (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*))
                "refused init-budget-cannot-hold-profile profile=scale sizing=requested reservation=16226 MB budget=2048 MB"))
(assert! (equal (fn-heap-init-report-line (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*
                                                    *hrt-target-16g*))
                "init: profile=scale sizing=requested reservation=16226 MB budget=2048 MB within-budget=no target-budget=16384 MB"))
(assert! (equal (fn-heap-init-exit-code (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*)) 1))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*))
                "refused init-budget-cannot-hold-profile profile=custom sizing=conservative reservation=1153 MB budget=512 MB"))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)) 1))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) 0))

; A named budget below the machine init observes (finding R1 of the
; public-node rehearsal): init writes the store sized for the named budget
; and the host prints ACL2's warning naming both figures.  The rehearsal's
; case was init outside the unit's MemoryMax=1536M on hbox's figures with
; FN_INIT_BUDGET_MB=1536 named, and under MemoryMax=2G with 1500; since lane
; heap-bounds the small floor's first run is 1,906 MB, so a named 1,536 or
; 1,500 holds no candidate and init refuses (no note): the witnesses name
; 2,048 and 2,000.
(defconst *hrt-named-1536* '(49 53 51 54))    ; FN_INIT_BUDGET_MB=1536
(defconst *hrt-named-2048* '(50 48 52 56))    ; FN_INIT_BUDGET_MB=2048
(defconst *hrt-named-2000* '(50 48 48 48))    ; FN_INIT_BUDGET_MB=2000
(defconst *hrt-named-500* '(53 48 48))        ; FN_INIT_BUDGET_MB=500
(defconst *hrt-1536m* (list (* 1536 *fn-heap-mib*)))
(defmacro hrt-note (request physical limits budget)
  `(fn-heap-init-budget-note (hrt-init ,request ,physical ,limits ,budget)
                             ,physical ,limits ,budget))
(assert! (equal (hrt-note *hrt-bare* *hrt-hbox* nil *hrt-named-2048*)
                '(:named-budget-below-machine 2048 94464)))
(assert! (equal (hrt-note *hrt-bare* *hrt-hbox* *hrt-2g* *hrt-named-2000*)
                '(:named-budget-below-machine 2000 2048)))
(assert! (equal (fn-heap-init-budget-note-line
                 (hrt-note *hrt-bare* *hrt-hbox* nil *hrt-named-2048*))
                "warning init-budget-below-machine named-budget=2048 MB machine-budget=94464 MB: the store is sized for FN_INIT_BUDGET_MB, not this machine; run init under the service's memory limit, and give the service at least 2048 MB"))
; (A named 1,536 MB is accepted again since lane heap-pool: the 16 MiB rung.)
(assert! (equal (hrt-note *hrt-bare* *hrt-hbox* nil *hrt-named-1536*)
                '(:named-budget-below-machine 1536 94464)))
; As before: no named budget, init under the unit's own limit, the harness's
; 98,304 MB above hbox's 94,464 MB budget, and a refusal carry no note (and
; the host prints no line for NIL).
(assert! (null (hrt-note *hrt-bare* *hrt-hbox* nil nil)))
(assert! (null (hrt-note *hrt-bare* *hrt-hbox* *hrt-1536m* *hrt-named-1536*)))
(assert! (null (hrt-note *hrt-bare* *hrt-hbox* nil '(57 56 51 48 52))))
(assert! (null (hrt-note *hrt-mission* *hrt-hbox* nil *hrt-named-500*)))
(assert! (null (fn-heap-init-budget-note-line nil)))

; The keystone's teeth.  Hypotheses: the decision accepts, a budget is named,
; and it is below the machine init observes.
(defun hrt-note-conclusion (d physical limits budget-octets)
  (declare (xargs :mode :program))
  (let ((note (fn-heap-init-budget-note d physical limits budget-octets))
        (machine-mb (floor (fn-heap-init-machine-octets physical limits) *fn-heap-mib*)))
    (and (equal (car note) :named-budget-below-machine)
         (equal (nth 1 note) (nth 4 d))
         (equal (nth 2 note) machine-mb)
         (< (nth 4 d) machine-mb))))
(defun hrt-note-hyps (d physical limits budget-octets)
  (declare (xargs :mode :program))
  (let ((named (fn-heap-init-explicit-budget budget-octets)))
    (list (equal (car d) :init)
          (posp named)
          ; (nfix: the logic's floor of NIL is 0; program mode would fault)
          (< (floor (nfix named) *fn-heap-mib*)
             (floor (fn-heap-init-machine-octets physical limits) *fn-heap-mib*)))))
; Reachable: the rehearsal's init outside the unit's limit, every hypothesis
; and the conclusion (the store sized for 2,048 MB, the machine's 94,464).
(assert! (let ((d (hrt-init *hrt-bare* *hrt-hbox* nil *hrt-named-2048*)))
           (and (equal (hrt-note-hyps d *hrt-hbox* nil *hrt-named-2048*) '(t t t))
                (equal (nth 4 d) 2048)
                (hrt-note-conclusion d *hrt-hbox* nil *hrt-named-2048*))))
; Without "accepts": the mission under a named 500 MB is refused; a budget
; is named below the machine, and there is no note.
(assert! (let ((d (hrt-init *hrt-mission* *hrt-hbox* nil *hrt-named-500*)))
           (and (equal (hrt-note-hyps d *hrt-hbox* nil *hrt-named-500*) '(nil t t))
                (not (hrt-note-conclusion d *hrt-hbox* nil *hrt-named-500*)))))
; Without "named": the bare init under 2 GiB with FN_INIT_BUDGET_MB unset
; (the nil budget's 0 is below the machine): as before, no note.
(assert! (let ((d (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g* nil)))
           (and (equal (hrt-note-hyps d *hrt-hbox* *hrt-2g* nil) '(t nil t))
                (not (hrt-note-conclusion d *hrt-hbox* *hrt-2g* nil)))))
; Without "below": init run under the unit's own 2,048 MiB limit with the
; same budget named: accepted, named, no note.
(assert! (let ((d (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g* *hrt-named-2048*)))
           (and (equal (hrt-note-hyps d *hrt-hbox* *hrt-2g* *hrt-named-2048*)
                       '(t t nil))
                (not (hrt-note-conclusion d *hrt-hbox* *hrt-2g* *hrt-named-2048*)))))
(defmacro hrt-note-without (&rest hyps)
  `(must-fail-checked
    (defthm hrt-note-without-a-hypothesis
      (let* ((d (fn-heap-init-decide request core nursery physical limits
                                     budget-octets sizing-octets))
             (named (fn-heap-init-explicit-budget budget-octets))
             (machine-mb (floor (fn-heap-init-machine-octets physical limits)
                                *fn-heap-mib*))
             (note (fn-heap-init-budget-note d physical limits budget-octets)))
        (declare (ignorable named machine-mb))
        (implies (and ,@hyps)
                 (and (equal (car note) :named-budget-below-machine)
                      (equal (nth 1 note) (nth 4 d))
                      (equal (nth 2 note) machine-mb)
                      (< (nth 4 d) machine-mb))))
      :hints (("Goal" :do-not-induct t
               :in-theory (disable fn-heap-init-decide fn-heap-init-machine-octets
                                   fn-heap-init-explicit-budget
                                   fn-heap-init-observations fn-heap-machine-octets))))))
(hrt-note-without (posp named) (< (floor named *fn-heap-mib*) machine-mb))
(hrt-note-without (equal (car d) :init) (< (floor named *fn-heap-mib*) machine-mb))
(hrt-note-without (equal (car d) :init) (posp named))
; The formula: the default preset's figure (T = 2^32 - 1 records: the
; per-record term 2 x T x 12 KiB dominates; its memberships are at most
; H / 320 since lane membership-budget, where up to 4,096 groups a record
; made 11,383,456,834,754,682 octets).
(assert! (equal (fn-heap-figure-octets *fn-bs-profile-defaults* 0 0)
                63985032632474))

; The keystone's teeth.  Hypotheses: the decision accepts, and says held.
(defun hrt-init-conclusion (d core nursery physical limits budget-octets)
  (declare (xargs :mode :program))
  (let ((p (fn-bs-profile-resolve (fn-heap-init-decision-request d) nil))
        (budget (fn-heap-machine-octets
                 (fn-heap-init-observations
                  physical limits (fn-heap-init-explicit-budget budget-octets)))))
    (and (fn-bs-profile-admittedp p)
         (<= (fn-heap-init-reservation-octets p core nursery) budget)
         (or (not (posp (fn-heap-machine-octets (cons physical limits))))
             (equal (car (fn-heap-reserve-full-store-decide
                          p core nursery (cons physical limits)
                          (fn-heap-reserve-init-connections)))
                    :heap)))))
; Reachable: the bare init under MemoryMax=2G on hbox.
(assert! (let ((d (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)))
           (and (equal (car d) :init) (nth 6 d)
                (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-2g* nil))))
; Without "accepts": the mission's refusal under 1 GiB, whose conclusion fails.
(assert! (let ((d (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)))
           (and (not (equal (car d) :init))
                (not (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-half*
                                          nil)))))
(must-fail-checked
 (defthm hrt-init-fits-without-acceptance
   (let* ((d (fn-heap-init-decide request core nursery physical limits
                                  budget-octets sizing-octets))
          (p (fn-bs-profile-resolve (fn-heap-init-decision-request d) nil)))
     (implies (nth 6 d)
              (and (fn-bs-profile-admittedp p)
                   (<= (fn-heap-init-reservation-octets p core nursery)
                       (fn-heap-machine-octets
                        (fn-heap-init-observations
                         physical limits (fn-heap-init-explicit-budget budget-octets)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-init-decide fn-bs-profile-resolve
                                fn-bs-profile-admittedp
                                fn-heap-init-reservation-octets
                                fn-heap-machine-octets fn-heap-init-observations)))))
; Without "held": scale as the operator's request under 2 GiB with a named
; 16 GiB target is written for the target, not held here, and its 10,914 MB
; are over the 2,048 MB budget.
(assert! (let ((d (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g* *hrt-target-16g*)))
           (and (equal (car d) :init) (not (nth 6 d))
                (not (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-2g*
                                          nil)))))
(must-fail-checked
 (defthm hrt-init-fits-without-held
   (let* ((d (fn-heap-init-decide request core nursery physical limits
                                  budget-octets sizing-octets))
          (p (fn-bs-profile-resolve (fn-heap-init-decision-request d) nil)))
     (implies (equal (car d) :init)
              (<= (fn-heap-init-reservation-octets p core nursery)
                  (fn-heap-machine-octets
                   (fn-heap-init-observations
                    physical limits (fn-heap-init-explicit-budget budget-octets))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-init-decide fn-bs-profile-resolve
                                fn-bs-profile-admittedp
                                fn-heap-init-reservation-octets
                                fn-heap-machine-octets fn-heap-init-observations)))))

; honors-the-operators-request: reachable with '(:development ((1 . 100000)))
; (above, held) and '(:scale nil) under 2 GiB (not held, still written).
; Per hypothesis, a counterexample with the others holding:
;   machine-sized: the bare request under 2 GiB is written as small, not bare;
;   budget well-formed: FN_INIT_BUDGET_MB=x refuses the scale request;
;   sizing well-formed: FN_INIT_SIZING=x refuses it;
;   valid profile: H = 4096 under the default preset is refused.
(assert! (not (equal (fn-heap-init-decision-request (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*))
                     *hrt-bare*)))
(assert! (equal (car (hrt-init '(:scale nil) *hrt-hbox* nil '(120))) :refused))
(assert! (equal (car (hrt-init '(:scale nil) *hrt-hbox* nil nil '(120))) :refused))
(assert! (not (fn-heap-machine-sized-requestp '(:default ((2 . 4096))))))
(assert! (equal (car (fn-bs-profile-resolve '(:default ((2 . 4096))) nil)) :invalid))
(assert! (equal (car (hrt-init '(:default ((2 . 4096))) *hrt-hbox* nil)) :refused))
(defmacro hrt-honors-without (&rest hyps)
  `(must-fail-checked
    (defthm hrt-honors-without-a-hypothesis
      (implies (and ,@hyps)
               (let ((d (fn-heap-init-decide request core nursery physical
                                             limits budget-octets sizing-octets)))
                 (and (equal (car d) :init)
                      (equal (fn-heap-init-decision-request d) request))))
      :hints (("Goal" :do-not-induct t
               :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                   fn-heap-init-sizing fn-heap-reserve-init-choose
                                   fn-heap-init-candidates
                                   fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                   fn-heap-machine-sized-requestp))))))
(hrt-honors-without (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                    (not (equal (fn-heap-init-sizing sizing-octets) :bad))
                    (not (equal (car (fn-bs-profile-resolve request nil)) :invalid)))
(hrt-honors-without (not (fn-heap-machine-sized-requestp request))
                    (not (equal (fn-heap-init-sizing sizing-octets) :bad))
                    (not (equal (car (fn-bs-profile-resolve request nil)) :invalid)))
(hrt-honors-without (not (fn-heap-machine-sized-requestp request))
                    (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                    (not (equal (car (fn-bs-profile-resolve request nil)) :invalid)))
(hrt-honors-without (not (fn-heap-machine-sized-requestp request))
                    (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                    (not (equal (fn-heap-init-sizing sizing-octets) :bad)))

; sized-init-is-held: reachable with the bare request under 2 GiB (held).
; Without machine-sized: scale requested under 2 GiB is written, not held.
; Without acceptance: the mission refused under 1 GiB has no held flag.
(assert! (nth 6 (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)))
(assert! (not (nth 6 (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*))))
(defmacro hrt-held-without (&rest hyps)
  `(must-fail-checked
    (defthm hrt-held-without-a-hypothesis
      (implies (and ,@hyps)
               (nth 6 (fn-heap-init-decide request core nursery physical
                                           limits budget-octets sizing-octets)))
      :hints (("Goal" :do-not-induct t
               :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                   fn-heap-init-sizing fn-heap-init-chosen
                                   fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                   fn-heap-machine-sized-requestp))))))
(hrt-held-without (equal (car (fn-heap-init-decide request core nursery physical
                                                   limits budget-octets sizing-octets))
                         :init))
(hrt-held-without (fn-heap-machine-sized-requestp request))

; conservative-is-a-friend-rung: with FN_INIT_SIZING=largest on hbox the
; request is scale, which is no rung: the sizing hypothesis (NIL) is what
; excludes it.
(assert! (not (member-equal (fn-heap-init-decision-request
                             (hrt-init *hrt-bare* *hrt-hbox* nil nil *hrt-largest*))
                            (fn-heap-friend-ladder *hrt-bare* *fn-heap-friend-rungs*))))
(must-fail-checked
 (defthm hrt-conservative-without-the-sizing
   (let ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets sizing-octets)))
     (implies (and (fn-heap-machine-sized-requestp request)
                   (equal (car d) :init))
              (member-equal (fn-heap-init-decision-request d)
                            (fn-heap-friend-ladder request *fn-heap-friend-rungs*))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))

; largest-takes-scale-when-it-fits: under 2 GiB scale does not fit, and
; largest takes small there.
(assert! (not (fn-heap-reserve-acceptsp '(:scale nil) *hrt-core* *hrt-nursery*
                                        (fn-heap-init-observations *hrt-hbox* *hrt-2g* nil))))
(assert! (equal (fn-heap-init-decision-request
                 (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g* nil *hrt-largest*))
                *fn-heap-small-request*))
(must-fail-checked
 (defthm hrt-largest-without-scale-fitting
   (implies (and (fn-heap-machine-sized-requestp request)
                 (not (equal (fn-heap-init-explicit-budget budget-octets) :bad)))
            (equal (fn-heap-init-decision-request
                    (fn-heap-init-decide request core nursery physical limits
                                         budget-octets
                                         '(108 97 114 103 101 115 116)))
                   (fn-heap-preset-candidate :scale request)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-heap-preset-candidate
                                fn-bs-profile-resolve
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))

;; -----------------------------------------------------------------------------
; A request's article bound is held (fix-line-stack, 2026-09-27).  Batch AR's
; conservative sizing laid the request's A over development's R (which
; holds a 32 KiB article at 65,535 groups) and the small candidate's 8 MiB
; H: `init --max-article-octets 8388608' (tests/test_native_served_line_stack)
; was refused invalid-init-profile under hbox_native's 24 GiB and on hbox
; itself, and `--max-article-octets 4194304' (tests/test_native_bounds_join)
; fell to the small candidate, 8 MiB of history and 16 groups, whose 441
; "no capacity" stopped the 3 MiB POSTs.  The candidates now raise R to the
; article record and H to at least R.
(defconst *hrt-a8* '(:default ((4 . 8388608))))
(defconst *hrt-a4* '(:default ((4 . 4194304))))
(defconst *hrt-24g* (list (* 24 *hrt-gib*)))
(defun hrt-sized-at (d request budget-mb)
  (and (equal (car d) :init)
       (equal (fn-heap-init-decision-request d) request)
       (equal (nth 4 d) budget-mb)
       (equal (nth 5 d) :conservative)
       (equal (nth 6 d) t)))
; Since friend-blockers (PKT-707, batch AV) conservative sizing takes the
; largest friend rung the budget holds: under 24 GiB the top rung (64 MiB of
; history, 131,072 transactions) with R raised to the 8 MiB (4 MiB) article's
; record at 16 groups.
(assert! (hrt-sized-at (hrt-init *hrt-a8* *hrt-hbox* *hrt-24g*)
                       '(:development ((1 . 131072) (2 . 67108864) (3 . 8393867)
                                       (5 . 16) (7 . 128) (4 . 8388608)))
                       24576))
(assert! (hrt-sized-at (hrt-init *hrt-a4* *hrt-hbox* *hrt-24g*)
                       '(:development ((1 . 131072) (2 . 67108864) (3 . 4199563)
                                       (5 . 16) (7 . 128) (4 . 4194304)))
                       24576))
; On hbox without a limit: the same top rung.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-a8* *hrt-hbox* nil))
                '(:development ((1 . 131072) (2 . 67108864) (3 . 8393867)
                                (5 . 16) (7 . 128) (4 . 8388608)))))
; Under 3 GiB: the 16 MiB rung, R raised to the article's record (under 2 GiB
; even the small candidate's first run, 2,097 MB, is refused by name).
(assert! (equal (fn-heap-init-decision-request
                 (hrt-init *hrt-a8* *hrt-hbox* (list (* 3 *hrt-gib*))))
                '(:development ((1 . 65536) (2 . 33554432) (3 . 8393867) (5 . 16)
                                (7 . 128) (4 . 8388608)))))
; Each written profile keeps the request's A and resolves valid.
(assert! (equal (fn-bs-profile-max-article-octets
                 (fn-bs-profile-resolve
                  (fn-heap-init-decision-request (hrt-init *hrt-a8* *hrt-hbox* *hrt-24g*)) nil))
                8388608))
(assert! (fn-bs-profile-admittedp
          (fn-bs-profile-resolve
           (fn-heap-init-decision-request (hrt-init *hrt-a4* *hrt-hbox* *hrt-24g*)) nil)))
; Mutation: without the raise (the batch AR candidates) the same request
; failed the article relations by name.
(assert! (equal (fn-bs-profile-resolve '(:development ((4 . 8388608))) nil)
                '(:invalid :max-record-octets-below-the-article-record)))
(assert! (equal (fn-bs-profile-resolve
                 '(:development ((1 . 16384) (2 . 8388608) (3 . 8393867) (5 . 16)
                                 (7 . 128) (4 . 8388608))) nil)
                '(:invalid :max-history-octets-below-max-record-octets)))
; A candidate that already holds its article is returned unchanged (the
; bare and mission witnesses above are the same requests as before).
(assert! (equal (fn-heap-article-held '(:development nil)) '(:development nil)))
(assert! (equal (fn-heap-article-held '(:development ((4 . 1048576) (5 . 8))))
                '(:development ((4 . 1048576) (5 . 8)))))

; Teeth for fn-heap-article-held-holds-the-article-record.  Positive: the
; 8 MiB request, both hypotheses true, every conjunct of the conclusion.
(defun hrt-held-conclusion (request)
  (let* ((q (fn-heap-article-held request))
         (v (fn-bs-profile-set-fields (fn-bs-config-for-profile (car q)) (cadr q)))
         (v0 (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request))
                                       (cadr request))))
    (and (equal (car q) (car request))
         (not (equal v :bad))
         (<= (fn-record-encoded-octets-ceiling (fn-bs-pf 4 v) (fn-bs-pf 5 v))
             (fn-bs-pf 3 v))
         (<= (fn-bs-pf 3 v) (fn-bs-pf 2 v))
         (equal (fn-bs-pf 1 v) (fn-bs-pf 1 v0))
         (equal (fn-bs-pf 4 v) (fn-bs-pf 4 v0))
         (equal (fn-bs-pf 5 v) (fn-bs-pf 5 v0))
         (<= (fn-bs-pf 2 v0) (fn-bs-pf 2 v))
         (<= (fn-bs-pf 3 v0) (fn-bs-pf 3 v)))))
(defconst *hrt-dev-a8* '(:development ((4 . 8388608))))
(assert! (fn-bs-profile-requestp *hrt-dev-a8*))
(assert! (not (equal (fn-bs-profile-set-fields
                      (fn-bs-config-for-profile :development) '((4 . 8388608)))
                     :bad)))
(assert! (not (equal (fn-heap-article-held *hrt-dev-a8*) *hrt-dev-a8*)))
(assert! (hrt-held-conclusion *hrt-dev-a8*))
; Without the well-formed fields: a field index below 1 makes the values
; :bad (the omitted hypothesis false, the request still a request), and
; the conclusion fails.  The request hypothesis is kept: no counterexample
; is known without it.
(defconst *hrt-bad-field* '(:development ((0 . 5))))
(assert! (fn-bs-profile-requestp *hrt-bad-field*))
(assert! (equal (fn-bs-profile-set-fields (fn-bs-config-for-profile :development)
                                          '((0 . 5)))
                :bad))
(assert! (not (hrt-held-conclusion *hrt-bad-field*)))
(must-fail-checked
 (defthm hrt-held-without-the-fields
   (implies (and (fn-bs-profile-requestp request)
                 (equal request *hrt-bad-field*))
            (hrt-held-conclusion request))
   :hints (("Goal" :do-not-induct t))))
; Teeth for fn-heap-article-held-meets-the-article-relations: the 8 MiB
; request satisfies all three hypotheses and its candidate resolves to an
; admitted profile (neither relation fails); the unraised request is the
; mutation witness above.
(assert! (not (equal (car *hrt-dev-a8*) :current)))
(assert! (fn-bs-profile-admittedp
          (fn-bs-profile-resolve (fn-heap-article-held *hrt-dev-a8*) nil)))
; Its three hypotheses have no known counterexample (a request whose
; fields are :bad, or that is not a request, resolves to (:invalid
; :request)); a proof of the unconditional statement was not found, and a
; failed search is not a counterexample, so they are kept (PKT in the record).
; Audit packet G3-5 (lane audit-fixes): every non-request candidate tried
; still satisfies both conclusions -- a third element, an unknown preset, a
; dotted request, a dotted field list, the :current preset -- so no removal
; witness exists among them.  The unconditional :831 with a case split on the
; three hypotheses ran 100 s (17M steps) without a proof and was stopped;
; the hypotheses stay, recorded as untoothed (no counterexample known).
(assert! (and (hrt-held-conclusion '(:development ((4 . 8388608)) extra))
              (hrt-held-conclusion '(:foo ((4 . 8388608))))
              (hrt-held-conclusion '(:development ((4 . 8388608)) . x))
              (hrt-held-conclusion '(:development ((4 . 8388608) . x)))
              (hrt-held-conclusion '(:current ((4 . 8388608))))))
(assert! (and (not (fn-bs-profile-requestp '(:development ((4 . 8388608)) extra)))
              (not (fn-bs-profile-requestp '(:foo ((4 . 8388608)))))))
(assert! (equal (fn-bs-profile-resolve (fn-heap-article-held '(:current ((4 . 8388608)))) nil)
                '(:invalid :request)))
(assert! (equal (fn-bs-profile-resolve (fn-heap-article-held '(:development ((0 . 5)))) nil)
                '(:invalid :request)))
(assert! (fn-bs-profile-admittedp
          (fn-bs-profile-resolve (fn-heap-article-held '(:development ((4 . 8388608)) extra)) nil)))

; A run's connections: the structural owner bound (PRF-211) is held at the
; default 32; a smaller bound is kept.
(assert! (equal (fn-heap-reserve-run-connections (+ 1 *fn-cbor-max-uint*)) 32))
(assert! (equal (fn-heap-reserve-run-connections 5) 5))
(assert! (equal (fn-heap-reserve-run-connections nil) 0))

;; -----------------------------------------------------------------------------
;; PKT-707 keystones' teeth.
;; fn-heap-init-decide-conservative-is-a-friend-rung: the witness (hbox, the
;; top rung) and the hypothesis: an operator's request is written as named,
;; which is no rung.
(assert! (member-equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* nil))
                       (fn-heap-friend-ladder *hrt-mission* *fn-heap-friend-rungs*)))
(assert! (equal (car (hrt-init '(:development nil) *hrt-hbox* nil)) :init))
(assert! (not (member-equal (fn-heap-init-decision-request
                             (hrt-init '(:development nil) *hrt-hbox* nil))
                            (fn-heap-friend-ladder '(:development nil)
                                                   *fn-heap-friend-rungs*))))
(must-fail-checked
 (defthm hrt-rung-without-machine-sized
   (let ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets nil)))
     (implies (equal (car d) :init)
              (member-equal (fn-heap-init-decision-request d)
                            (fn-heap-friend-ladder request *fn-heap-friend-rungs*))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
;; fn-heap-init-decide-conservative-holds-the-floor: the witnesses (the top
;; rung on hbox, the floor on 2 GiB), and each hypothesis.
(assert! (equal (fn-heap-request-transactions (fn-heap-init-decision-request
                                               (hrt-init *hrt-mission* *hrt-hbox* nil)))
                131072))
(assert! (equal (fn-heap-request-history (fn-heap-init-decision-request
                                          (hrt-init *hrt-mission* *hrt-hbox* nil)))
                67108864))
(assert! (equal (fn-heap-request-transactions (fn-heap-init-decision-request
                                               (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil)))
                32768))
(assert! (equal (fn-bs-profile-max-transactions
                 (fn-bs-profile-resolve (fn-heap-init-decision-request
                                         (hrt-init *hrt-mission* *hrt-hbox* nil)) nil))
                131072))
;; Without the machine-sized request: development as named, 128 transactions.
(assert! (< (fn-heap-request-transactions (fn-heap-init-decision-request
                                           (hrt-init '(:development nil) *hrt-hbox* nil)))
            16384))
(must-fail-checked
 (defthm hrt-floor-without-machine-sized
   (let ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets nil)))
     (implies (equal (car d) :init)
              (<= 16384 (fn-heap-request-transactions
                         (fn-heap-init-decision-request d)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
;; Without acceptance: a refused init writes no request.
(assert! (equal (fn-heap-request-transactions (fn-heap-init-decision-request
                                               (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)))
                0))
(must-fail-checked
 (defthm hrt-floor-without-init
   (let ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets nil)))
     (implies (fn-heap-machine-sized-requestp request)
              (<= 16384 (fn-heap-request-transactions
                         (fn-heap-init-decision-request d)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
;; fn-heap-init-decide-conservative-takes-the-top-rung-when-it-fits: the
;; witness is hbox's; without the fit (2 GiB) another rung is written.
(assert! (not (equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*))
                     (fn-heap-friend-candidate *hrt-mission* 67108864))))
(must-fail-checked
 (defthm hrt-top-without-fit
   (implies (and (fn-heap-machine-sized-requestp request)
                 (not (equal (fn-heap-init-explicit-budget budget-octets) :bad)))
            (equal (fn-heap-init-decision-request
                    (fn-heap-init-decide request core nursery physical limits
                                         budget-octets nil))
                   (fn-heap-friend-candidate request 67108864)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
;; Without a usable budget word: refused.
(assert! (equal (car (hrt-init *hrt-mission* *hrt-hbox* nil '(120))) :refused))
(must-fail-checked
 (defthm hrt-top-without-budget
   (implies (and (fn-heap-machine-sized-requestp request)
                 (fn-heap-reserve-acceptsp
                  (fn-heap-friend-candidate request 67108864) core nursery
                  (fn-heap-init-observations physical limits
                                             (fn-heap-init-explicit-budget budget-octets))))
            (equal (fn-heap-init-decision-request
                    (fn-heap-init-decide request core nursery physical limits
                                         budget-octets nil))
                   (fn-heap-friend-candidate request 67108864)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
;; Without the machine-sized request: the operator's own is written.
(must-fail-checked
 (defthm hrt-top-without-machine-sized
   (implies (and (not (equal (fn-heap-init-explicit-budget budget-octets) :bad))
                 (fn-heap-reserve-acceptsp
                  (fn-heap-friend-candidate request 67108864) core nursery
                  (fn-heap-init-observations physical limits
                                             (fn-heap-init-explicit-budget budget-octets))))
            (equal (fn-heap-init-decision-request
                    (fn-heap-init-decide request core nursery physical limits
                                         budget-octets nil))
                   (fn-heap-friend-candidate request 67108864)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
                                fn-heap-friend-candidate
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))
; -----------------------------------------------------------------------------
; The operation's reservation (PKT-686): the compaction verbs reserve
; heap-figure's operation figure, every other command as before.
; fn-heap-reserve-operation-decide-holds-the-operation: a reachable witness
; (`store reclaim' of the small store on a 2 GiB machine), and per
; hypothesis (only the accepted reservation remains) a counterexample
; and the must-fail of the keystone without it.

(defun hrt-op-conclusion (action profile core nursery observations connections observed)
  (declare (xargs :mode :program))
  (let ((r (fn-heap-reserve-operation-decide action profile core nursery observations
                                             connections observed))
        (d (fn-heap-operation-decide action profile core nursery observations observed)))
    (and (equal (car d) :heap)
         (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
         (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                (fn-heap-core-file core)
                (* (fn-heap-reserve-threads r)
                   (+ (* 1024 (fn-heap-reserve-stack-kib r))
                      *fn-heap-thread-runtime-octets*)))
             (fn-heap-machine-octets observations)))))

(defun hrt-op-hyps (action profile core nursery observations connections observed)
  (declare (xargs :mode :program))
  (list (equal (car (fn-heap-reserve-operation-decide action profile core nursery
                                                      observations connections observed))
               :heap)))

; A serve-class command reserves exactly as before; `store reclaim' of the
; small store at H reserves heap-figure's 1,843 MB (on the OpenBSD guest's
; 195,856,696-octet core) and 28 threads beside it: 2,170 MB in all, so a
; 2 GiB machine refuses it by name (machine-cannot-hold-threads), as does
; OpenBSD's default datasize, where since lane heap-bounds (the records'
; term from the profile's limits) `run' is refused too, even of the empty
; store (1,782 MB with the threads); on 2 GiB `run' is accepted.  Observed at the
; measured 3,000-article store's 7,271,160 octets (item 1) it reserves
; 1,639 MB and fits 2 GiB; observed empty, 307 MB.
(assert! (equal (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* (list *hrt-datasize*) 32
                                                  '(0 . 0))
                '(:heap 568 "small" 1536 1024 30)))
(assert! (equal (car (fn-heap-reserve-operation-decide :run *fn-heap-small-profile*
                                                       *hrt-core* *hrt-nursery*
                                                       (list *hrt-datasize*) 32 nil))
                :heap))
(assert! (equal (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* *hrt-2g* 32 '(0 . 0))
                '(:heap 568 "small" 2048 1024 30)))
(assert! (equal (car (fn-heap-reserve-operation-decide :run *fn-heap-small-profile*
                                                       *hrt-core* *hrt-nursery*
                                                       *hrt-2g* 32 nil))
                :heap))
(defconst *hrt-2200* (list (* 2200 *fn-heap-mib*)))
(assert! (equal (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2200* 0 nil)
                '(:heap 1843 "small" 2200 1024 30)))
(assert! (equal (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2g* 0 nil)
                '(:refused :machine-cannot-hold-threads 2180 2048)))
(assert! (equal (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2g* 0 '(7271160 . 3000))
                '(:heap 1639 "small" 2048 1024 30)))
(assert! (equal (fn-heap-reserve-operation-decide :compact *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2g* 0 '(0 . 0))
                '(:heap 572 "small" 2048 1024 30)))
(assert! (equal (car (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile*
                                                       195856696 *hrt-nursery*
                                                       (list *hrt-datasize*) 0 nil))
                :refused))
; `fn --version' (no store) under the OpenBSD guest's 4 GiB datasize: 1,024
; MB and one thread beside the core, where the machine-wide heap died in mmap.
(defconst *hrt-4g* (list (* 4096 *fn-heap-mib*)))
(assert! (equal (fn-heap-reserve-operation-decide :none nil 195856696 *hrt-nursery*
                                                  *hrt-4g* 0 nil)
                '(:heap 1024 "none" 4096 2048 1)))

; The witnesses: the reclaim at H on 2,200 MiB, the observed reclaim on
; 2 GiB, and the store-less command (no profile hypothesis: PKT-686 item 3
; removed it after proving the weakened keystone).
(assert! (equal (hrt-op-hyps :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                             *hrt-2200* 0 nil)
                '(t)))
(assert! (hrt-op-conclusion :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                            *hrt-2200* 0 nil))
(assert! (equal (hrt-op-hyps :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                             *hrt-2g* 0 7271160)
                '(t)))
(assert! (hrt-op-conclusion :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                            *hrt-2g* 0 7271160))
(assert! (equal (hrt-op-hyps :none nil 195856696 *hrt-nursery* *hrt-4g* 0 nil) '(t)))
(assert! (hrt-op-conclusion :none nil 195856696 *hrt-nursery* *hrt-4g* 0 nil))

; Without the accepted reservation: the reclaim at H under OpenBSD's datasize.
(assert! (equal (hrt-op-hyps :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                             (list *hrt-datasize*) 0 nil)
                '(nil)))
(assert! (not (hrt-op-conclusion :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                                 (list *hrt-datasize*) 0 nil)))
(must-fail-checked
 (defthm hrt-op-without-heap
   (let ((r (fn-heap-reserve-operation-decide action profile core nursery
                                              observations connections observed))
         (d (fn-heap-operation-decide action profile core nursery observations
                                      observed)))
     (and (equal (car d) :heap)
          (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
          (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                 (nfix core)
                 (* (fn-heap-reserve-threads r)
                    (+ (* 1024 (fn-heap-reserve-stack-kib r))
                       *fn-heap-thread-runtime-octets*)))
              (fn-heap-machine-octets observations))))
   :hints (("Goal" :use ((:instance fn-heap-reserve-decide-is-reserve-of-heap-decide)
                         (:instance fn-heap-reserve-of-holds-the-decision
                                    (d (fn-heap-operation-decide action profile core
                                                                 nursery observations
                                                                 observed)))
                         (:instance fn-heap-reserve-of-holds-the-decision
                                    (d (fn-heap-decide profile core nursery observations)))
                         (:instance
                          fn-heap-operation-decide-of-a-serve-action-is-heap-decide))
            :in-theory (union-theories '(fn-heap-reserve-operation-decide
                                         (:executable-counterpart member-equal))
                                       (theory 'minimal-theory))))))

; -----------------------------------------------------------------------------
; Lane keystone-audit (2026-09-27): witnesses and teeth the PRF-198
; restatements lacked.

; fn-heap-init-decide-largest-takes-scale-when-it-fits: the reachable
; witness (every hypothesis and the conclusion).  On a 512 GiB machine the
; scale preset's first run fits, and FN_INIT_SIZING=largest writes it.
(defconst *hrt-512g* (* 512 *hrt-gib*))
(assert! (fn-heap-machine-sized-requestp *hrt-bare*))
(assert! (not (equal (fn-heap-init-explicit-budget nil) :bad)))
(assert! (fn-heap-reserve-acceptsp (fn-heap-preset-candidate :scale *hrt-bare*)
                                   *hrt-core* *hrt-nursery*
                                   (fn-heap-init-observations *hrt-512g* nil
                                                              (fn-heap-init-explicit-budget nil))))
(assert! (equal (fn-heap-init-decision-request
                 (hrt-init *hrt-bare* *hrt-512g* nil nil *hrt-largest*))
                (fn-heap-preset-candidate :scale *hrt-bare*)))
(assert! (equal (fn-heap-preset-candidate :scale *hrt-bare*) '(:scale nil)))
; Teeth (audit packet G3-4, lane audit-fixes), on the same 512 GiB machine.
; Without (fn-heap-machine-sized-requestp request): a development request
; is written as named, not as scale, though the scale candidate fits and the
; budget is not :bad.
(assert! (not (fn-heap-machine-sized-requestp '(:development nil))))
(assert! (fn-heap-reserve-acceptsp (fn-heap-preset-candidate :scale '(:development nil))
                                   *hrt-core* *hrt-nursery*
                                   (fn-heap-init-observations *hrt-512g* nil
                                                              (fn-heap-init-explicit-budget nil))))
(assert! (not (equal (fn-heap-init-decision-request
                      (hrt-init '(:development nil) *hrt-512g* nil nil *hrt-largest*))
                     (fn-heap-preset-candidate :scale '(:development nil)))))
; Without the budget hypothesis: FN_INIT_BUDGET_MB=x is :bad; the request is
; machine-sized and the candidate still fits the observations, but init
; refuses the budget by name and writes no scale request.
(assert! (equal (fn-heap-init-explicit-budget '(120)) :bad))
(assert! (fn-heap-reserve-acceptsp (fn-heap-preset-candidate :scale *hrt-bare*)
                                   *hrt-core* *hrt-nursery*
                                   (fn-heap-init-observations *hrt-512g* nil
                                                              (fn-heap-init-explicit-budget '(120)))))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-512g* nil '(120) *hrt-largest*)) :refused))
(assert! (not (equal (fn-heap-init-decision-request
                      (hrt-init *hrt-bare* *hrt-512g* nil '(120) *hrt-largest*))
                     (fn-heap-preset-candidate :scale *hrt-bare*))))

; fn-heap-reserve-full-store-accepted-is-within-the-machine.  Reachable: the
; small preset's first run on 2 GiB (both hypotheses, and 1,997,800,456
; octets within 2,147,483,648; OpenBSD's 1,536 MiB datasize held it before
; lane heap-bounds derived the records' term from the profile's limits).
(assert! (fn-bs-profile-admittedp *fn-heap-small-profile*))
(assert! (equal (car (fn-heap-reserve-full-store-decide *fn-heap-small-profile* *hrt-core*
                                                       *hrt-nursery* *hrt-2g*
                                                       (fn-heap-reserve-init-connections)))
                :heap))
(assert! (<= (fn-heap-init-reservation-octets *fn-heap-small-profile* *hrt-core* *hrt-nursery*)
             (fn-heap-machine-octets *hrt-2g*)))
; Without the admitted profile: no profile on a 500 MiB machine is accepted
; (the store-less figure, 310 MB), while the init reservation of no profile
; (569,639,944 octets) is past the machine.
(defconst *hrt-500m* (list (* 500 *fn-heap-mib*)))
(assert! (not (fn-bs-profile-admittedp nil)))
(assert! (equal (car (fn-heap-reserve-full-store-decide nil *hrt-core* *hrt-nursery* *hrt-500m*
                                                       (fn-heap-reserve-init-connections)))
                :heap))
(assert! (not (<= (fn-heap-init-reservation-octets nil *hrt-core* *hrt-nursery*)
                  (fn-heap-machine-octets *hrt-500m*))))
; Without the accepted decision: the small preset on 300 MiB is refused, and
; its reservation is past the machine.
(defconst *hrt-300m* (list (* 300 *fn-heap-mib*)))
(assert! (equal (car (fn-heap-reserve-full-store-decide *fn-heap-small-profile* *hrt-core*
                                                       *hrt-nursery* *hrt-300m*
                                                       (fn-heap-reserve-init-connections)))
                :refused))
(assert! (not (<= (fn-heap-init-reservation-octets *fn-heap-small-profile* *hrt-core*
                                                   *hrt-nursery*)
                  (fn-heap-machine-octets *hrt-300m*))))

; fn-heap-operation-decide-of-a-serve-action-is-heap-decide.  Reachable:
; `run' unobserved is heap-figure's decision.  Without "not an offline
; verb": the reclaim's figure (1,840 MB) is not the serve figure (1,736).
; Without "not init": init's first-run figure (668 MB) is not it either.
(assert! (equal (fn-heap-operation-decide :run *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                          *hrt-2g* nil)
                (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-2g*)))
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-2g*))
                :heap))
(assert! (member-equal :reclaim *fn-heap-list-actions*))
(assert! (not (equal (fn-heap-operation-decide :reclaim *fn-heap-small-profile* *hrt-core*
                                               *hrt-nursery* *hrt-4096* nil)
                     (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     *hrt-4096*))))
(assert! (not (member-equal :init *fn-heap-list-actions*)))
(assert! (not (equal (fn-heap-operation-decide :init *fn-heap-small-profile* *hrt-core*
                                               *hrt-nursery* *hrt-2g* nil)
                     (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     *hrt-2g*))))

; fn-heap-reserve-of-holds-the-decision.  Reachable: the small preset's
; decision on 4 GiB reserved (every conjunct of the conclusion).  Without
; the accepted reservation: heap-figure's accepted 1,045 MB on 1,300 MiB
; with the threads beside it is refused (machine-cannot-hold-threads), and the
; reservation's figure is past the machine.
(defun hrt-of-conclusion (d r core observations)
  (declare (xargs :mode :program))
  (and (equal (car d) :heap)
       (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
       (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
              (fn-heap-core-file core)
              (* (fn-heap-reserve-threads r)
                 (+ (* 1024 (fn-heap-reserve-stack-kib r))
                    *fn-heap-thread-runtime-octets*)))
           (fn-heap-machine-octets observations))))
(defconst *hrt-of-d* (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-4096*))
(defconst *hrt-of-r* (fn-heap-reserve-of *hrt-of-d* *fn-heap-small-profile* *hrt-core*
                                         *hrt-4096* 32))
(assert! (equal (car *hrt-of-r*) :heap))
(assert! (hrt-of-conclusion *hrt-of-d* *hrt-of-r* *hrt-core* *hrt-4096*))
;; Batch AW (reservation-figure's model), re-taken under membership-budget's
;; figure: the small preset's decision on 800 MiB is accepted (710 MB since
;; lane heap-pool; 1,572 MB under lane heap-bounds' uncharged header term,
;; 938 MB before it) and its reservation with the threads (1,044 MB) is not.
(defconst *hrt-1300m* (list (* 800 *fn-heap-mib*)))
(defconst *hrt-of-d2* (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery* *hrt-1300m*))
(defconst *hrt-of-r2* (fn-heap-reserve-of *hrt-of-d2* *fn-heap-small-profile* *hrt-core*
                                          *hrt-1300m* 32))
(assert! (equal (car *hrt-of-d2*) :heap))
(assert! (equal *hrt-of-r2* '(:refused :machine-cannot-hold-threads 1044 800)))
(assert! (not (<= (fn-heap-reservation-octets (fn-heap-decision-mb *hrt-of-d2*) *hrt-core*
                                              1024 30)
                  (fn-heap-machine-octets *hrt-1300m*))))

; fn-heap-reserve-decide-is-reserve-of-heap-decide (no hypothesis): both
; sides on the accepted 4 GiB decision and the refused 2 GiB one.
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        *hrt-4096* 32)
                *hrt-of-r*))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        *hrt-1300m* 32)
                *hrt-of-r2*))

; fn-heap-figure-octets-grows-with-history-and-record.  Reachable: the small
; preset below the defaults (all five hypotheses, and the figure grows).
(defun hrt-grow-hyps (p1 p2)
  (declare (xargs :mode :program))
  (list (<= (nfix (fn-bs-profile-max-history-octets p1))
            (nfix (fn-bs-profile-max-history-octets p2)))
        (<= (nfix (fn-bs-profile-max-transactions p1))
            (nfix (fn-bs-profile-max-transactions p2)))
        (<= (nfix (fn-bs-profile-max-record-octets p1))
            (nfix (fn-bs-profile-max-record-octets p2)))
        (<= (nfix (fn-bs-profile-field 15 p1)) (nfix (fn-bs-profile-field 15 p2)))
        (<= (nfix (fn-bs-profile-max-article-octets p1))
            (nfix (fn-bs-profile-max-article-octets p2)))))
(defun hrt-grow-conclusion (p1 p2)
  (declare (xargs :mode :program))
  (<= (fn-heap-figure-octets p1 *hrt-core* *hrt-nursery*)
      (fn-heap-figure-octets p2 *hrt-core* *hrt-nursery*)))
(defun hrt-small-with (fields)
  (declare (xargs :mode :program))
  (fn-bs-profile-resolve (list :development (append (cadr *fn-heap-small-request*) fields))
                         nil))
(assert! (equal (hrt-small-with nil) *fn-heap-small-profile*))
(assert! (equal (hrt-grow-hyps *fn-heap-small-profile* *fn-bs-profile-defaults*)
                '(t t t t t)))
(assert! (hrt-grow-conclusion *fn-heap-small-profile* *fn-bs-profile-defaults*))
; Per hypothesis, the small preset with that one field raised against the
; small preset: the other four hold, it fails, and the figure shrinks.
(assert! (equal (hrt-grow-hyps (hrt-small-with '((1 . 32768))) *fn-heap-small-profile*)
                '(t nil t t t)))
(assert! (not (hrt-grow-conclusion (hrt-small-with '((1 . 32768))) *fn-heap-small-profile*)))
; G is no longer a hypothesis (membership-budget: the figure does not read
; it; the memberships are bounded by H): raising it leaves the figure.
(assert! (equal (fn-heap-figure-octets (hrt-small-with '((5 . 32))) *hrt-core* *hrt-nursery*)
                (fn-heap-figure-octets *fn-heap-small-profile* *hrt-core* *hrt-nursery*)))
(assert! (equal (hrt-grow-hyps (hrt-small-with '((15 . 32768))) *fn-heap-small-profile*)
                '(t t t nil t)))
(assert! (not (hrt-grow-conclusion (hrt-small-with '((15 . 32768))) *fn-heap-small-profile*)))
; A (lane zero-copy-commit: the articles in flight): the small preset with a
; 64 KiB article limit against the small preset.
(assert! (equal (hrt-grow-hyps (hrt-small-with '((4 . 65536))) *fn-heap-small-profile*)
                '(t t t t nil)))
(assert! (not (hrt-grow-conclusion (hrt-small-with '((4 . 65536))) *fn-heap-small-profile*)))
; H and R (audit packet G3-3, lane audit-fixes): the capture-budget
; hypothesis is gone -- the book proves it from H and R
; (fn-heap-capture-budget-grows-with-history-and-record) -- so each now has
; its own single-hypothesis counterexample: H raised to 16 MiB, R to 2 MiB.
(assert! (equal (hrt-grow-hyps (hrt-small-with '((2 . 16777216))) *fn-heap-small-profile*)
                '(nil t t t t)))
(assert! (not (hrt-grow-conclusion (hrt-small-with '((2 . 16777216))) *fn-heap-small-profile*)))
(assert! (equal (hrt-grow-hyps (hrt-small-with '((3 . 2097152))) *fn-heap-small-profile*)
                '(t t nil t t)))
(assert! (not (hrt-grow-conclusion (hrt-small-with '((3 . 2097152))) *fn-heap-small-profile*)))
; The budget lemma itself: positive at the small preset against the
; defaults; removal of R (H equal, R raised) makes the budget grow the
; other way.
(assert! (<= (fn-ock-capture-budget *fn-heap-small-profile*)
             (fn-ock-capture-budget *fn-bs-profile-defaults*)))
(assert! (and (equal (fn-bs-profile-max-history-octets (hrt-small-with '((3 . 2097152))))
                     (fn-bs-profile-max-history-octets *fn-heap-small-profile*))
              (not (<= (fn-ock-capture-budget (hrt-small-with '((3 . 2097152))))
                       (fn-ock-capture-budget *fn-heap-small-profile*)))))
; Lane reservation-figure (2026-09-27).
;
; The figure's parameters are the runtime's: the open's chunk is the streamed
; replay's work quantum, the arena's page the paged arena's.
(assert! (equal *fn-heap-open-chunk-octets* *fn-srs-chunk-octets*))
(assert! (equal *fn-heap-arena-page-octets* *fn-arp-page*))

; The streamed open holds no copy of the history: over the scale preset's
; full store (H = 768 MiB, T = 4,096) the open's transient is 2,655 MB, under
; one list copy of H (12,288 MB); before, it was two list copies twice
; (64 H: 49,152 MB) and 16 KiB a record.
(defconst *hrt-scale-h* (fn-bs-profile-max-history-octets *fn-bs-profile-scale*))
(defconst *hrt-scale-t* (fn-bs-profile-max-transactions *fn-bs-profile-scale*))
(assert! (equal (fn-heap-mb-of (fn-heap-store-open-octets *fn-bs-profile-scale*
                                                          *hrt-scale-h* *hrt-scale-t*))
                2655))
(assert! (< (fn-heap-store-open-octets *fn-bs-profile-scale* *hrt-scale-h* *hrt-scale-t*)
            (* 16 *hrt-scale-h*)))

; The paged arena: a payload octet costs one octet, never three.
(assert! (equal (fn-heap-arena-octets 8388608) (+ 8388608 262144 (* 32 33))))
(assert! (< (fn-heap-arena-octets 805306368) (* 2 805306368)))

; The per-record terms cover the measured live state a record, less its
; payload (catalog-columns' record, section 4: at most 11.4 KB at 4 groups,
; 1,000 x 2 KiB, the arena's share taken out), at the groups measured and a
; header of 200 octets with a 40-octet Message-ID: the fixed part and the
; header charge's heap (4 a charged octet a copy, lane heap-pool).
(assert! (<= 11400 (+ *fn-heap-record-octets* (* 4 (fn-heap-record-charge 40 200))
                      (* 4 *fn-heap-membership-octets*))))

; THE GATE's profile (tools/throughput_gate.py: `init --profile scale
; --max-transactions 1048576 --max-article-octets 4096') at G = 65,535 groups
; an article (the scale preset's, the codec's ceiling).  Before lane
; membership-budget its state was 41,967,792 MB, all but 0.07 % of it the
; membership product 2 x T x 320 x G: no bound but G limited a store's
; memberships.  Now each membership is charged 320 octets of the history
; budget (books/store-budget.lisp `fn-sbud-record-octets-pays-the-memberships'),
; so a store holds at most H / 320 of them and the state no longer depends
; on G: the same figure at G = 16.
(defconst *hrt-gate* (fn-bs-profile-resolve
                      (fn-heap-article-held '(:scale ((1 . 1048576) (4 . 4096)))) nil))
(defconst *hrt-gate-16* (fn-bs-profile-resolve
                         (fn-heap-article-held '(:scale ((1 . 1048576) (4 . 4096) (5 . 16))))
                         nil))
(defun hrt-state (p)
  (fn-heap-store-state-octets p (fn-bs-profile-max-history-octets p)
                              (fn-bs-profile-max-transactions p)
                              (fn-heap-membership-bound p)))
(assert! (equal (fn-heap-mb-of (hrt-state *hrt-gate*)) 16689))
(assert! (equal (hrt-state *hrt-gate*) (hrt-state *hrt-gate-16*)))
; fn-heap-membership-term-is-at-most-twice-h, reachable: the gate's
; membership term is at most 2 H (1,536 MiB), where it was 2 x T x 320 x G.
(assert! (equal (fn-heap-membership-bound *hrt-gate*)
                (floor (fn-bs-profile-max-history-octets *hrt-gate*) 320)))
(assert! (<= (* 2 *fn-heap-membership-octets* (fn-heap-membership-bound *hrt-gate*))
             (* 2 (fn-bs-profile-max-history-octets *hrt-gate*))))
(assert! (< (* 2 *fn-heap-membership-octets* (fn-heap-membership-bound *hrt-gate*))
            (* 2 1048576 *fn-heap-membership-octets* 65535)))

; THE STATUS LINE: fn-heap-status-decide-is-the-launchers-run-reservation.
; Reachable witness: an observed small store on a 123 GiB machine, the
; launcher's run reservation at the configuration's bound 32 and at 5.
(defconst *hrt-big* (list (* 123 *hrt-gib*)))
(assert! (equal (fn-heap-status-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                       *hrt-big* '(7271160 . 3000))
                (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* *hrt-big*
                                                  (fn-heap-reserve-run-connections 32)
                                                  '(7271160 . 3000))))
(assert! (equal (fn-heap-status-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                       *hrt-big* '(7271160 . 3000))
                (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* *hrt-big*
                                                  (fn-heap-reserve-run-connections 5)
                                                  '(7271160 . 3000))))
(assert! (equal (fn-heap-reserve-report-line
                 (fn-heap-status-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        *hrt-big* '(7271160 . 3000)))
                "heap=677 MB profile=small machine=125952 MB stack=1024 KB threads=30"))
; The default mission's top rung (1 MiB articles) on this machine: the
; launcher's figure.  (The mutation this paragraph held, connection-budget's
; launch figure that `status' printed before lane reservation-figure, went
; with the function in lane zero-copy-commit: the figure itself now holds the
; articles in flight.)
(defconst *hrt-mission-top*
  (fn-bs-profile-resolve (fn-heap-friend-candidate *hrt-mission* 67108864) nil))
(assert! (equal (fn-heap-reserve-report-line
                 (fn-heap-status-decide *hrt-mission-top* *hrt-core* *hrt-nursery*
                                        *hrt-big* '(7271160 . 3000)))
                "heap=2614 MB profile=custom machine=125952 MB stack=1024 KB threads=30"))

; -----------------------------------------------------------------------------
; Lane membership-budget (2026-09-27).
;
; fn-heap-init-accepted-store-always-reopens (the coordinator's release
; blocker, friend-path packet A).  Reachable witness: the small profile on
; 2 GiB (OpenBSD's 1,536 MiB datasize before lane heap-bounds), which init's
; full-store decision accepts;
; every later run on that machine is accepted -- unobserved, an empty store,
; the measured 3,000-article store -- at the configuration's bound and at 5.
(defun hrt-reopens-hyps (p obs k)
  (declare (xargs :mode :program))
  (list (equal (car (fn-heap-reserve-full-store-decide p *hrt-core* *hrt-nursery* obs k))
               :heap)))
(defun hrt-reopens-conclusion (p obs k2 observed)
  (declare (xargs :mode :program))
  (equal (car (fn-heap-reserve-operation-decide :run p *hrt-core* *hrt-nursery* obs k2
                                                observed))
         :heap))
(defconst *hrt-dsz* *hrt-2g*)
(assert! (equal (fn-heap-reserve-full-store-decide *fn-heap-small-profile* *hrt-core*
                                                   *hrt-nursery* *hrt-dsz* 32)
                '(:heap 710 "small" 2048 1024 30)))
(assert! (equal (hrt-reopens-hyps *fn-heap-small-profile* *hrt-dsz* 32) '(t)))
(assert! (hrt-reopens-conclusion *fn-heap-small-profile* *hrt-dsz* 32 nil))
(assert! (hrt-reopens-conclusion *fn-heap-small-profile* *hrt-dsz* 32 '(0 . 0)))
(assert! (hrt-reopens-conclusion *fn-heap-small-profile* *hrt-dsz* 5 '(7271160 . 3000)))
; Without init's acceptance: the small profile on 1,024 MiB is refused by the
; full-store decision, and its unobserved run is refused too.
(defconst *hrt-1g-obs* (list (* 1024 *fn-heap-mib*)))
(assert! (equal (hrt-reopens-hyps *fn-heap-small-profile* *hrt-1g-obs* 32) '(nil)))
(assert! (not (hrt-reopens-conclusion *fn-heap-small-profile* *hrt-1g-obs* 32 nil)))
(must-fail-checked
 (defthm hrt-reopens-without-init-acceptance
   (equal (car (fn-heap-reserve-operation-decide :run p core nursery obs k2 observed))
          :heap)
   :rule-classes nil
   :hints (("Goal" :use fn-heap-init-accepted-store-always-reopens
            :in-theory (disable fn-heap-init-accepted-store-always-reopens
                                fn-heap-reserve-operation-decide
                                fn-heap-reserve-full-store-decide)))))
; MUTATION (before this lane): the empty store's first run was init's
; promise.  Here a machine that holds the small profile's empty-store run
; but not its full store's: the old promise was kept, the later run refused.
(defconst *hrt-mut-obs* (list (* 950 *fn-heap-mib*)))
(assert! (equal (car (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                       *hrt-nursery* *hrt-mut-obs* 32
                                                       '(0 . 0)))
                :heap))
(assert! (equal (hrt-reopens-hyps *fn-heap-small-profile* *hrt-mut-obs* 32) '(nil)))
(assert! (not (hrt-reopens-conclusion *fn-heap-small-profile* *hrt-mut-obs* 32 nil)))

; fn-heap-init-decide-refuses-the-operators-request-past-the-budget (ember's
; decision 2).  Its seven hypotheses and its conclusion, over hrt-init's
; arguments.
(defun hrt-refuse-hyps (request physical limits budget sizing)
  (declare (xargs :mode :program))
  (let* ((explicit (fn-heap-init-explicit-budget budget))
         (obs (fn-heap-init-observations physical limits explicit))
         (p (fn-bs-profile-resolve request nil)))
    (list (not (fn-heap-machine-sized-requestp request))
          (not (equal explicit :bad))
          (not (equal (fn-heap-init-sizing sizing) :bad))
          (not (equal (car p) :invalid))
          (posp (fn-heap-machine-octets obs))
          (not (fn-heap-reserve-acceptsp request *hrt-core* *hrt-nursery* obs))
          (not (fn-heap-init-target-holdsp p *hrt-core* *hrt-nursery* explicit)))))
(defun hrt-refuse-conclusion (request physical limits budget sizing)
  (declare (xargs :mode :program))
  (let* ((explicit (fn-heap-init-explicit-budget budget))
         (obs (fn-heap-init-observations physical limits explicit))
         (p (fn-bs-profile-resolve request nil))
         (d (fn-heap-init-decide request *hrt-core* *hrt-nursery* physical limits
                                 budget sizing)))
    (and (equal (car d) :refused)
         (equal (nth 1 d) :init-budget-cannot-hold-profile)
         (equal (nth 2 d)
                (fn-heap-mb-of (fn-heap-init-reservation-octets p *hrt-core* *hrt-nursery*)))
         (equal (nth 3 d) (floor (fn-heap-machine-octets obs) *fn-heap-mib*))
         (equal (fn-heap-init-decision-request d) nil))))
; Reachable witness: scale as the operator's request under 2 GiB.
(assert! (equal (hrt-refuse-hyps '(:scale nil) *hrt-hbox* *hrt-2g* nil nil) '(t t t t t t t)))
(assert! (hrt-refuse-conclusion '(:scale nil) *hrt-hbox* *hrt-2g* nil nil))
; Per hypothesis, the others holding, it fails and so does the conclusion.
; 1. A capacity-free request (bare init on hbox under 2 GiB: a friend rung).
(assert! (equal (hrt-refuse-hyps *hrt-bare* *hrt-hbox* *hrt-2g* nil nil) '(nil t t t t t t)))
(assert! (not (hrt-refuse-conclusion *hrt-bare* *hrt-hbox* *hrt-2g* nil nil)))
; 2. A malformed FN_INIT_BUDGET_MB: refused, but as invalid-init-budget.
(assert! (equal (hrt-refuse-hyps '(:scale nil) *hrt-hbox* *hrt-2g* '(120) nil)
                '(t nil t t t t t)))
(assert! (not (hrt-refuse-conclusion '(:scale nil) *hrt-hbox* *hrt-2g* '(120) nil)))
; 3. A malformed FN_INIT_SIZING: invalid-init-sizing.
(assert! (equal (hrt-refuse-hyps '(:scale nil) *hrt-hbox* *hrt-2g* nil '(120))
                '(t t nil t t t t)))
(assert! (not (hrt-refuse-conclusion '(:scale nil) *hrt-hbox* *hrt-2g* nil '(120))))
; 4. An invalid profile: invalid-init-profile.
(assert! (equal (hrt-refuse-hyps '(:default ((2 . 4096))) *hrt-hbox* *hrt-2g* nil nil)
                '(t t t nil t t t)))
(assert! (not (hrt-refuse-conclusion '(:default ((2 . 4096))) *hrt-hbox* *hrt-2g* nil nil)))
; 5. No memory observed: machine-memory-unobserved.
(assert! (equal (hrt-refuse-hyps '(:scale nil) nil nil nil nil) '(t t t t nil t t)))
(assert! (not (hrt-refuse-conclusion '(:scale nil) nil nil nil nil)))
(assert! (equal (nth 1 (hrt-init '(:scale nil) nil nil)) :machine-memory-unobserved))
; 6. The budget holds it (hbox): written.
(assert! (equal (hrt-refuse-hyps '(:scale nil) *hrt-hbox* nil nil nil) '(t t t t t nil t)))
(assert! (not (hrt-refuse-conclusion '(:scale nil) *hrt-hbox* nil nil nil)))
; 7. A named 16 GiB target holds it: written for the target.
(assert! (equal (hrt-refuse-hyps '(:scale nil) *hrt-hbox* *hrt-2g* *hrt-target-16g* nil)
                '(t t t t t t nil)))
(assert! (not (hrt-refuse-conclusion '(:scale nil) *hrt-hbox* *hrt-2g* *hrt-target-16g* nil)))
(defmacro hrt-refuse-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (let* ((explicit (fn-heap-init-explicit-budget budget-octets))
             (obs (fn-heap-init-observations physical limits explicit))
             (p (fn-bs-profile-resolve request nil))
             (d (fn-heap-init-decide request core nursery physical
                                     limits budget-octets sizing-octets)))
        (implies (and ,@hyps)
                 (and (equal (car d) :refused)
                      (equal (nth 1 d) :init-budget-cannot-hold-profile))))
      :hints (("Goal" :in-theory (disable fn-heap-reserve-acceptsp
                                          fn-bs-profile-resolve
                                          fn-heap-init-sizing
                                          fn-heap-reserve-init-choose
                                          fn-heap-init-candidates
                                          fn-heap-init-reservation-octets
                                          fn-heap-init-target-holdsp
                                          fn-heap-machine-octets
                                          fn-heap-init-observations
                                          fn-heap-init-explicit-budget
                                          fn-heap-profile-word
                                          fn-heap-machine-sized-requestp))))))
(hrt-refuse-must-fail hrt-refuse-without-operators-request
  (not (equal explicit :bad)) (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (not (equal (car p) :invalid)) (posp (fn-heap-machine-octets obs))
  (not (fn-heap-reserve-acceptsp request core nursery obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-budget-wellformed
  (not (fn-heap-machine-sized-requestp request))
  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (not (equal (car p) :invalid)) (posp (fn-heap-machine-octets obs))
  (not (fn-heap-reserve-acceptsp request core nursery obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-sizing-wellformed
  (not (fn-heap-machine-sized-requestp request)) (not (equal explicit :bad))
  (not (equal (car p) :invalid)) (posp (fn-heap-machine-octets obs))
  (not (fn-heap-reserve-acceptsp request core nursery obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-valid-profile
  (not (fn-heap-machine-sized-requestp request)) (not (equal explicit :bad))
  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (posp (fn-heap-machine-octets obs))
  (not (fn-heap-reserve-acceptsp request core nursery obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-observed-machine
  (not (fn-heap-machine-sized-requestp request)) (not (equal explicit :bad))
  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (not (equal (car p) :invalid))
  (not (fn-heap-reserve-acceptsp request core nursery obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-budget-refusal
  (not (fn-heap-machine-sized-requestp request)) (not (equal explicit :bad))
  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (not (equal (car p) :invalid)) (posp (fn-heap-machine-octets obs))
  (not (fn-heap-init-target-holdsp p core nursery explicit)))
(hrt-refuse-must-fail hrt-refuse-without-target-refusal
  (not (fn-heap-machine-sized-requestp request)) (not (equal explicit :bad))
  (not (equal (fn-heap-init-sizing sizing-octets) :bad))
  (not (equal (car p) :invalid)) (posp (fn-heap-machine-octets obs))
  (not (fn-heap-reserve-acceptsp request core nursery obs)))
