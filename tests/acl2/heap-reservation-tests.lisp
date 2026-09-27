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
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

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
; reservation-figure): heap-figure's heap at the preset's bounds, 1,045 MB
; on this core, and 30 threads -- the
; 12 fixed, the 2 I/O loops, the 16 control clients -- of a 1 MiB stack
; each, whatever the connections (since connection-multiplexing a
; connection is no thread; the reservation counted 60 before this lane).
; On OpenBSD's 1,536 MiB datasize the preset's full store fits (1,379 MB
; with the core and the threads), and so does its first run
; (heap-reservation's init judgement).
(defconst *hrt-4096* (list (* 4096 *fn-heap-mib*)))
(assert! (equal (fn-heap-stack-kib *fn-heap-small-profile*) 1024))
(assert! (equal (fn-heap-thread-count 32) 30))
(assert! (equal (fn-heap-thread-count 0) 30))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        *hrt-4096* 32)
                '(:heap 1045 "small" 4096 1024 30)))
(assert! (equal (car (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core*
                                             *hrt-nursery* (list *hrt-datasize*) 32))
                :heap))
(assert! (equal (fn-heap-reserve-first-run-decide *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* (list *hrt-datasize*) 32)
                '(:heap 993 "small" 1536 1024 30)))
(assert! (<= (fn-heap-reservation-octets 1045 *hrt-core* 1024 30)
             *hrt-datasize*))

; The threads push it past a machine the heap alone fits.
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     (list (* 1100 *fn-heap-mib*))))
                :heap))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list (* 1100 *fn-heap-mib*)) 32)
                (list :refused :machine-cannot-hold-threads
                      (fn-heap-mb-of (fn-heap-reservation-octets 1045 *hrt-core* 1024 30))
                      1100)))

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
(must-fail
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

; Without the accepted reservation: the thread refusal on 1,100 MB.
(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                          (list (* 1100 *fn-heap-mib*)) 32)
                '(t nil)))
(assert! (not (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                              (list (* 1100 *fn-heap-mib*)) 32)))
(must-fail
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
  (fn-heap-reservation-octets 1045 *hrt-core* 1024 30))
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
(defconst *hrt-mission* '(:default ((5 . 1048576) (6 . 8))))
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
(defconst *hrt-top* '(:development ((2 . 131072) (3 . 67108864) (4 . 196608)
                                      (6 . 16) (8 . 128))))
(assert! (equal (fn-heap-friend-candidate *hrt-bare* 67108864) *hrt-top*))
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil)
                (list :init *hrt-top* "custom" 5536 94464 :conservative t)))
; FN_INIT_SIZING=largest: the largest preset whose first run the budget
; holds -- development, since scale's first run is 171,623 MB (its 4,096
; records of up to 65,535 group memberships each, reservation-after-flip).
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil nil *hrt-largest*)
                '(:init (:development nil) "development" 7604 94464 :largest t)))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) :init))
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*))
                (fn-heap-friend-candidate *hrt-bare* 16777216)))
(assert! (equal (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil)
                (list :init *fn-heap-small-request* "small" 1327 1536
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
(assert! (equal (nth 3 (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*)) 1851))
; Under 1 GiB the mission's small capacity's first run (1,327 MB) is refused
; by name, as under 512 MiB: never lowered.
(defconst *hrt-half* (list (* 512 *fn-heap-mib*)))
(assert! (equal (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*)
                '(:refused :init-budget-cannot-hold-profile 1327 1024 "custom"
                           :conservative)))
(assert! (equal (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)
                '(:refused :init-budget-cannot-hold-profile 1327 512 "custom"
                           :conservative)))
(assert! (equal (fn-heap-reserve-first-run-decide
                 (fn-bs-profile-resolve (fn-heap-small-candidate *hrt-mission*) nil)
                 *hrt-core* *hrt-nursery* *hrt-half* 32)
                '(:refused :machine-cannot-hold-profile 993 512)))
; An operator's request is written as named, the line saying whether the
; budget holds it; an invalid one is refused.
(assert! (equal (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*)
                '(:init (:scale nil) "scale" 171623 2048 :requested nil)))
(assert! (equal (hrt-init '(:development ((2 . 100000))) *hrt-hbox* nil)
                '(:init (:development ((2 . 100000))) "custom" 4004769 94464
                  :requested nil)))
(assert! (equal (car (hrt-init '(:default ((3 . 4096))) *hrt-hbox* nil)) :refused))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil))
                "init: profile=small sizing=conservative reservation=1327 MB budget=1536 MB within-budget=yes"))
(assert! (equal (fn-heap-init-report-line (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*))
                "init: profile=scale sizing=requested reservation=171623 MB budget=2048 MB within-budget=no"))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*))
                "refused init-budget-cannot-hold-profile profile=custom sizing=conservative reservation=1327 MB budget=512 MB"))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-mission* *hrt-hbox* *hrt-half*)) 1))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) 0))
; The formula: the default preset's figure (T = 2^32 - 1 records of up to
; 4,096 groups each: the membership term dominates).
(assert! (equal (fn-heap-figure-octets *fn-bs-profile-defaults* 0 0)
                11383456834754682))

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
             (equal (car (fn-heap-reserve-first-run-decide
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
(must-fail
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
; Without "held": scale as the operator's request under 2 GiB is written,
; not held, and its 55,049 MB are over the 2,048 MB budget.
(assert! (let ((d (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*)))
           (and (equal (car d) :init) (not (nth 6 d))
                (not (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-2g*
                                          nil)))))
(must-fail
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

; honors-the-operators-request: reachable with '(:development ((2 . 100000)))
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
(assert! (not (fn-heap-machine-sized-requestp '(:default ((3 . 4096))))))
(assert! (equal (car (fn-bs-profile-resolve '(:default ((3 . 4096))) nil)) :invalid))
(assert! (equal (car (hrt-init '(:default ((3 . 4096))) *hrt-hbox* nil)) :refused))
(defmacro hrt-honors-without (&rest hyps)
  `(must-fail
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
  `(must-fail
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
(must-fail
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
(must-fail
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
(defconst *hrt-a8* '(:default ((5 . 8388608))))
(defconst *hrt-a4* '(:default ((5 . 4194304))))
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
                       '(:development ((2 . 131072) (3 . 67108864) (4 . 8393867)
                                       (6 . 16) (8 . 128) (5 . 8388608)))
                       24576))
(assert! (hrt-sized-at (hrt-init *hrt-a4* *hrt-hbox* *hrt-24g*)
                       '(:development ((2 . 131072) (3 . 67108864) (4 . 4199563)
                                       (6 . 16) (8 . 128) (5 . 4194304)))
                       24576))
; On hbox without a limit: the same top rung.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-a8* *hrt-hbox* nil))
                '(:development ((2 . 131072) (3 . 67108864) (4 . 8393867)
                                (6 . 16) (8 . 128) (5 . 8388608)))))
; Under 3 GiB: the 16 MiB rung, R raised to the article's record (under 2 GiB
; even the small candidate's first run, 2,097 MB, is refused by name).
(assert! (equal (fn-heap-init-decision-request
                 (hrt-init *hrt-a8* *hrt-hbox* (list (* 3 *hrt-gib*))))
                '(:development ((2 . 32768) (3 . 16777216) (4 . 8393867) (6 . 16)
                                (8 . 128) (5 . 8388608)))))
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
(assert! (equal (fn-bs-profile-resolve '(:development ((5 . 8388608))) nil)
                '(:invalid :max-record-octets-below-the-article-record)))
(assert! (equal (fn-bs-profile-resolve
                 '(:development ((2 . 16384) (3 . 8388608) (4 . 8393867) (6 . 16)
                                 (8 . 128) (5 . 8388608))) nil)
                '(:invalid :max-history-octets-below-max-record-octets)))
; A candidate that already holds its article is returned unchanged (the
; bare and mission witnesses above are the same requests as before).
(assert! (equal (fn-heap-article-held '(:development nil)) '(:development nil)))
(assert! (equal (fn-heap-article-held '(:development ((5 . 1048576) (6 . 8))))
                '(:development ((5 . 1048576) (6 . 8)))))

; Teeth for fn-heap-article-held-holds-the-article-record.  Positive: the
; 8 MiB request, both hypotheses true, every conjunct of the conclusion.
(defun hrt-held-conclusion (request)
  (let* ((q (fn-heap-article-held request))
         (v (fn-bs-profile-set-fields (fn-bs-config-for-profile (car q)) (cadr q)))
         (v0 (fn-bs-profile-set-fields (fn-bs-config-for-profile (car request))
                                       (cadr request))))
    (and (equal (car q) (car request))
         (not (equal v :bad))
         (<= (fn-record-encoded-octets-ceiling (fn-bs-pf 5 v) (fn-bs-pf 6 v))
             (fn-bs-pf 4 v))
         (<= (fn-bs-pf 4 v) (fn-bs-pf 3 v))
         (equal (fn-bs-pf 2 v) (fn-bs-pf 2 v0))
         (equal (fn-bs-pf 5 v) (fn-bs-pf 5 v0))
         (equal (fn-bs-pf 6 v) (fn-bs-pf 6 v0))
         (<= (fn-bs-pf 3 v0) (fn-bs-pf 3 v))
         (<= (fn-bs-pf 4 v0) (fn-bs-pf 4 v)))))
(defconst *hrt-dev-a8* '(:development ((5 . 8388608))))
(assert! (fn-bs-profile-requestp *hrt-dev-a8*))
(assert! (not (equal (fn-bs-profile-set-fields
                      (fn-bs-config-for-profile :development) '((5 . 8388608)))
                     :bad)))
(assert! (not (equal (fn-heap-article-held *hrt-dev-a8*) *hrt-dev-a8*)))
(assert! (hrt-held-conclusion *hrt-dev-a8*))
; Without the well-formed fields: a field index below 2 makes the values
; :bad (the omitted hypothesis false, the request still a request), and
; the conclusion fails.  The request hypothesis is kept: no counterexample
; is known without it.
(defconst *hrt-bad-field* '(:development ((1 . 5))))
(assert! (fn-bs-profile-requestp *hrt-bad-field*))
(assert! (equal (fn-bs-profile-set-fields (fn-bs-config-for-profile :development)
                                          '((1 . 5)))
                :bad))
(assert! (not (hrt-held-conclusion *hrt-bad-field*)))
(must-fail
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
(must-fail
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
                16384))
(assert! (equal (fn-bs-profile-max-transactions
                 (fn-bs-profile-resolve (fn-heap-init-decision-request
                                         (hrt-init *hrt-mission* *hrt-hbox* nil)) nil))
                131072))
;; Without the machine-sized request: development as named, 128 transactions.
(assert! (< (fn-heap-request-transactions (fn-heap-init-decision-request
                                           (hrt-init '(:development nil) *hrt-hbox* nil)))
            16384))
(must-fail
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
(must-fail
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
(must-fail
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
(must-fail
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
(must-fail
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
                (nfix core)
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
; OpenBSD's default datasize, where `run' is accepted.  Observed at the
; measured 3,000-article store's 7,271,160 octets (item 1) it reserves
; 1,639 MB and fits 2 GiB; observed empty, 307 MB.
(assert! (equal (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* (list *hrt-datasize*) 32
                                                  '(0 . 0))
                '(:heap 993 "small" 1536 1024 30)))
(assert! (equal (car (fn-heap-reserve-operation-decide :run *fn-heap-small-profile*
                                                       *hrt-core* *hrt-nursery*
                                                       (list *hrt-datasize*) 32 nil))
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
                '(:heap 997 "small" 2048 1024 30)))
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
(must-fail
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

; The per-record term covers the measured live state a record, less its
; payload (catalog-columns' record, section 4: at most 11.4 KB at 4 groups,
; 1,000 x 2 KiB, the arena's share taken out), at the groups measured.
(assert! (<= 11400 (+ *fn-heap-record-octets* (* 4 *fn-heap-membership-octets*))))

; THE GATE's profile (tools/throughput_gate.py: `init --profile scale
; --max-transactions 1048576 --max-article-octets 4096') at G = 65,535 groups
; an article (the scale preset's, the codec's ceiling): its state is 41,967,792
; MB, and the membership product 2 x T x 320 x G is all but 0.07 % of it.
; With G = 16 the same profile's state is 35,632 MB.  Not a double count: no
; bound but G limits a store's memberships (the history budget charges an
; article its payload, books/store-budget-stored.lisp).
(defconst *hrt-gate* (fn-bs-profile-resolve
                      (fn-heap-article-held '(:scale ((2 . 1048576) (5 . 4096)))) nil))
(defconst *hrt-gate-16* (fn-bs-profile-resolve
                         (fn-heap-article-held '(:scale ((2 . 1048576) (5 . 4096) (6 . 16))))
                         nil))
(defun hrt-state (p)
  (fn-heap-store-state-octets p (fn-bs-profile-max-history-octets p)
                              (fn-bs-profile-max-transactions p)))
(assert! (equal (fn-heap-mb-of (hrt-state *hrt-gate*)) 41967793))
(assert! (< (* 10000 (- (hrt-state *hrt-gate*)
                        (* 2 1048576 *fn-heap-membership-octets* 65535)))
            (* 7 (hrt-state *hrt-gate*))))
(assert! (equal (fn-heap-mb-of (hrt-state *hrt-gate-16*)) 35633))

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
                "heap=1015 MB profile=small machine=125952 MB stack=1024 KB threads=30"))
; MUTATION (the line `status' printed before): connection-budget's launch
; figure fills the machine with connections' heap parts.  For the default
; mission's top rung (1 MiB articles) on this machine it is 39,519 MB where
; the launcher reserves 4,662 MB -- the disagreement ops-fixes' sweep found
; (heap=37643 MB on a node reserving about 2.8 GB).
(defconst *hrt-mission-top*
  (fn-bs-profile-resolve (fn-heap-friend-candidate *hrt-mission* 67108864) nil))
(assert! (equal (fn-heap-reserve-report-line
                 (fn-heap-status-decide *hrt-mission-top* *hrt-core* *hrt-nursery*
                                        *hrt-big* '(7271160 . 3000)))
                "heap=4662 MB profile=custom machine=125952 MB stack=1024 KB threads=30"))
(assert! (equal (fn-heap-decision-mb
                 (fn-cbud-launch-decide
                  (fn-heap-operation-decide :run *hrt-mission-top* *hrt-core*
                                            *hrt-nursery* *hrt-big* '(7271160 . 3000))
                  *hrt-mission-top* *hrt-core* 30 (* 1024 1024) *hrt-big*))
                39519))
