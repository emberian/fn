; Teeth for books/heap-reservation (lane image-floor, HST-025, extending
; PRF-198): the decisions on the lane's core and the OpenBSD VM's datasize,
; the keystone's reachable witness and, per hypothesis, a counterexample where
; the others hold and the conclusion fails, with the must-fail of the theorem
; without it; the exact refusal and heap-figure's refusals passed through;
; the report lines and the exit code.
(in-package "ACL2")
(include-book "../../books/heap-reservation")
(include-book "../../books/codec-attach")
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
         (<= (+ connections (fn-native-control-max-active-clients)
                *fn-heap-fixed-threads*)
             (fn-heap-reserve-threads r))
         (<= *fn-heap-stack-octets*
             (* 1024 (fn-heap-reserve-stack-kib r)))
         (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                (nfix core)
                (* (fn-heap-reserve-threads r)
                   (+ (* 1024 (fn-heap-reserve-stack-kib r))
                      *fn-heap-thread-runtime-octets*)))
             (fn-heap-machine-octets observations)))))

(defun hrt-hyps (profile core nursery observations connections)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-reserve-decide profile core nursery observations
                                            connections))
               :heap)
        (natp connections)))

; -----------------------------------------------------------------------------
; The decisions.  The small preset on the OpenBSD datasize with the default
; 32 connections: heap-figure's 816 MB, 60 threads of a 1,024 KiB stack
; (the constant: served-line-iterative made the served path's stack need
; independent of the article), and the core once more: 1,300 MB in all.  With the old
; 64 MiB stacks the same threads reserved 4,080 MB beside the heap.
(assert! (equal (fn-heap-stack-kib *fn-heap-small-profile*) 1024))
(assert! (equal (fn-heap-thread-count 32) 60))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list *hrt-datasize*) 32)
                '(:heap 816 "small" 1536 1024 60)))
(assert! (< *hrt-datasize*
            (fn-heap-reservation-octets 816 *hrt-core* (* 64 1024) 60)))
; The threads push it past a machine the heap alone fits.
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     (list (* 900 *fn-heap-mib*))))
                :heap))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list (* 900 *fn-heap-mib*)) 32)
                '(:refused :machine-cannot-hold-threads 1300 900)))
; The default profile's 16 MiB article: the same stack; heap-figure refuses
; the profile first.
(assert! (equal (fn-heap-stack-kib *fn-bs-profile-defaults*) 1024))
(assert! (equal (car (fn-heap-reserve-decide *fn-bs-profile-defaults* *hrt-core*
                                             *hrt-nursery* (list 132000000000) 32))
                :refused))
; No store: heap-figure's machine-wide figure, SBCL's default stack, one thread.
(assert! (equal (fn-heap-reserve-decide nil *hrt-core* *hrt-nursery*
                                        (list (* 2048 *fn-heap-mib*)) 32)
                '(:heap 2048 "none" 2048 2048 1)))

; -----------------------------------------------------------------------------
; The keystone: the reachable witness, then per hypothesis a counterexample
; where the others hold, it fails, the conclusion fails, and the must-fail
; of the theorem without it under the keystone's own theory, no induction.

(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                          (list *hrt-datasize*) 32)
                '(t t t)))
(assert! (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                         (list *hrt-datasize*) 32))

; Without the admitted profile: no store is one thread, not the node's.
(assert! (equal (hrt-hyps nil *hrt-core* *hrt-nursery* (list *hrt-datasize*) 32)
                '(nil t t)))
(assert! (not (hrt-conclusion nil *hrt-core* *hrt-nursery* (list *hrt-datasize*) 32)))
(must-fail
 (defthm hrt-without-admitted
   (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
     (implies (and (equal (car r) :heap)
                   (natp connections))
              (<= (+ connections (fn-native-control-max-active-clients)
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

; Without the accepted reservation: the thread refusal on 900 MB.
(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                          (list (* 900 *fn-heap-mib*)) 32)
                '(t nil t)))
(assert! (not (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                              (list (* 900 *fn-heap-mib*)) 32)))
(must-fail
 (defthm hrt-without-heap
   (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (natp connections))
              (<= (+ connections (fn-native-control-max-active-clients)
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

; Without a natural connection count: half a connection is counted as none.
(assert! (equal (hrt-hyps *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                          (list *hrt-datasize*) 1/2)
                '(t t nil)))
(assert! (not (hrt-conclusion *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                              (list *hrt-datasize*) 1/2)))
(must-fail
 (defthm hrt-without-natp-connections
   (let ((r (fn-heap-reserve-decide profile core nursery observations connections)))
     (implies (and (fn-bs-profile-admittedp profile)
                   (equal (car r) :heap))
              (<= (+ connections (fn-native-control-max-active-clients)
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

; -----------------------------------------------------------------------------
; The refusal is exact at the boundary: the machine exactly the reservation
; is accepted, one octet less is refused.
(defconst *hrt-exact*
  (fn-heap-reservation-octets 816 *hrt-core* 1024 60))
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
; limit and FN_INIT_BUDGET_MB; a capacity-free request takes development when
; the budget holds it, else small (conservative), or scale, development,
; small under FN_INIT_SIZING=largest; any other request is written as named,
; the line saying whether the budget holds it.  hbox (123 GiB): development,
; budget 94,464 MB; largest: scale.  Under MemoryMax=2G: small.  A 2 GiB
; machine: small within 1,536 MB.  The default mission (1 MiB articles, 8
; groups): under 2 GiB the small capacity with its fields, 1,327 MB (the
; stacks no longer grow with the article); under 1 GiB refused by name,
; never lowered.
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
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil)
                '(:init (:development nil) "development" 2969 94464 :conservative t)))
(assert! (equal (hrt-init *hrt-bare* *hrt-hbox* nil nil *hrt-largest*)
                '(:init (:scale nil) "scale" 55049 94464 :largest t)))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) :init))
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*))
                *fn-heap-small-request*))
(assert! (equal (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil)
                (list :init *fn-heap-small-request* "small" 1300 1536 :conservative t)))
; FN_INIT_BUDGET_MB=4096 on hbox: development, within 4,096 MB.
(assert! (equal (nth 4 (hrt-init *hrt-bare* *hrt-hbox* nil '(52 48 57 54))) 4096))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* nil '(120))) :refused))
(assert! (equal (car (hrt-init *hrt-bare* *hrt-hbox* nil nil '(120))) :refused))
; The mission's fields are kept: development with them on hbox, the small
; capacity with them under 2 GiB, refused under 1 GiB, never a lower article
; bound.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* nil))
                '(:development ((5 . 1048576) (6 . 8)))))
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*))
                (fn-heap-small-candidate *hrt-mission*)))
(assert! (equal (fn-bs-profile-max-article-octets
                 (fn-bs-profile-resolve (fn-heap-small-candidate *hrt-mission*) nil))
                1048576))
(assert! (equal (nth 3 (hrt-init *hrt-mission* *hrt-hbox* *hrt-2g*)) 1327))
(assert! (equal (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*)
                '(:refused :init-budget-cannot-hold-profile 1327 1024 "custom"
                           :conservative)))
(assert! (equal (fn-heap-reserve-decide
                 (fn-bs-profile-resolve (fn-heap-small-candidate *hrt-mission*) nil)
                 *hrt-core* *hrt-nursery* *hrt-1g* 32)
                '(:refused :machine-cannot-hold-threads 1327 1024)))
; An operator's request is written as named, the line saying whether the
; budget holds it; an invalid one is refused.
(assert! (equal (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*)
                '(:init (:scale nil) "scale" 55049 2048 :requested nil)))
(assert! (equal (hrt-init '(:development ((2 . 100000))) *hrt-hbox* nil)
                '(:init (:development ((2 . 100000))) "custom" 2969 94464 :requested t)))
(assert! (equal (car (hrt-init '(:default ((3 . 4096))) *hrt-hbox* nil)) :refused))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-bare* (* 2 *hrt-gib*) nil))
                "init: profile=small sizing=conservative reservation=1300 MB budget=1536 MB within-budget=yes"))
(assert! (equal (fn-heap-init-report-line (hrt-init '(:scale nil) *hrt-hbox* *hrt-2g*))
                "init: profile=scale sizing=requested reservation=55049 MB budget=2048 MB within-budget=no"))
(assert! (equal (fn-heap-init-report-line (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*))
                "refused init-budget-cannot-hold-profile profile=custom sizing=conservative reservation=1327 MB budget=1024 MB"))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*)) 1))
(assert! (equal (fn-heap-init-exit-code (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)) 0))
; The formula: the default preset's figure is its lists, 32 x (2H + R +
; 3 x the header bound, field 17: 16,384 in the defaults).
(assert! (equal (fn-heap-figure-octets *fn-bs-profile-defaults* 0 0)
                (+ (* 32 (+ (* 2 1099511627776) 67108864 (* 3 16384)))
                   (* 2 (fn-ock-capture-budget *fn-bs-profile-defaults*)))))

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
             (equal (car (fn-heap-reserve-decide p core nursery (cons physical limits)
                                                 (fn-heap-reserve-init-connections)))
                    :heap)))))
; Reachable: the bare init under MemoryMax=2G on hbox.
(assert! (let ((d (hrt-init *hrt-bare* *hrt-hbox* *hrt-2g*)))
           (and (equal (car d) :init) (nth 6 d)
                (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-2g* nil))))
; Without "accepts": the mission's refusal under 1 GiB, whose conclusion fails.
(assert! (let ((d (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*)))
           (and (not (equal (car d) :init))
                (not (hrt-init-conclusion d *hrt-core* *hrt-nursery* *hrt-hbox* *hrt-1g*
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
(assert! (not (nth 6 (hrt-init *hrt-mission* *hrt-hbox* *hrt-1g*))))
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

; conservative-is-development-or-small: reachable on hbox (development) and
; under 2 GiB (small); with FN_INIT_SIZING=largest on hbox the request is
; scale, which is neither: the sizing hypothesis (NIL) is what excludes it.
(assert! (not (member-equal (fn-heap-init-decision-request
                             (hrt-init *hrt-bare* *hrt-hbox* nil nil *hrt-largest*))
                            (list '(:development nil)
                                  (fn-heap-small-candidate *hrt-bare*)))))
(must-fail
 (defthm hrt-conservative-without-the-sizing
   (let ((d (fn-heap-init-decide request core nursery physical limits
                                 budget-octets sizing-octets)))
     (implies (and (fn-heap-machine-sized-requestp request)
                   (equal (car d) :init))
              (member-equal (fn-heap-init-decision-request d)
                            (list (fn-heap-preset-candidate :development request)
                                  (fn-heap-small-candidate request)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-preset-candidate
                                fn-heap-reserve-init-choose
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
(assert! (equal (hrt-init *hrt-a8* *hrt-hbox* *hrt-24g*)
                '(:init (:development ((5 . 8388608) (3 . 25494326) (4 . 25494326)))
                        "custom" 3015 24576 :conservative t)))
(assert! (equal (hrt-init *hrt-a4* *hrt-hbox* *hrt-24g*)
                '(:init (:development ((5 . 4194304) (3 . 25165824) (4 . 21300022)))
                        "custom" 2857 24576 :conservative t)))
; On hbox without a limit: the same development candidates.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-a8* *hrt-hbox* nil))
                '(:development ((5 . 8388608) (3 . 25494326) (4 . 25494326)))))
; Under 2 GiB: the small candidate, H raised to its record.
(assert! (equal (fn-heap-init-decision-request (hrt-init *hrt-a8* *hrt-hbox* *hrt-2g*))
                '(:development ((2 . 16384) (3 . 8393867) (4 . 8393867) (6 . 16)
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
   (implies (fn-bs-profile-requestp request)
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
