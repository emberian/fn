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
                            (list (list :development (cadr (true-list-fix request)))
                                  (fn-heap-small-candidate request)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-small-candidate fn-heap-reserve-init-choose
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
                   (list :scale (cadr (true-list-fix request)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp fn-bs-profile-resolve
                                fn-heap-init-reservation-octets fn-heap-machine-octets
                                fn-heap-init-observations fn-heap-init-explicit-budget
                                fn-heap-profile-word fn-heap-mb-of
                                fn-heap-machine-sized-requestp)))))

; A run's connections: the structural owner bound (PRF-211) is held at the
; default 32; a smaller bound is kept.
(assert! (equal (fn-heap-reserve-run-connections (+ 1 *fn-cbor-max-uint*)) 32))
(assert! (equal (fn-heap-reserve-run-connections 5) 5))
(assert! (equal (fn-heap-reserve-run-connections nil) 0))

; -----------------------------------------------------------------------------
; The operation's reservation (PKT-686): the compaction verbs reserve
; heap-figure's operation figure, every other command as before.
; fn-heap-reserve-operation-decide-holds-the-operation: a reachable witness
; (`store reclaim' of the small store on a 2 GiB machine), and per
; hypothesis a counterexample where the other holds and the conclusion
; fails, with the must-fail of the keystone without it.

(defun hrt-op-conclusion (action profile core nursery observations connections)
  (declare (xargs :mode :program))
  (let ((r (fn-heap-reserve-operation-decide action profile core nursery observations
                                             connections))
        (d (fn-heap-operation-decide action profile core nursery observations)))
    (and (equal (car d) :heap)
         (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
         (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                (nfix core)
                (* (fn-heap-reserve-threads r)
                   (+ (* 1024 (fn-heap-reserve-stack-kib r))
                      *fn-heap-thread-runtime-octets*)))
             (fn-heap-machine-octets observations)))))

(defun hrt-op-hyps (action profile core nursery observations connections)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (equal (car (fn-heap-reserve-operation-decide action profile core nursery
                                                      observations connections))
               :heap)))

; A serve-class command reserves exactly as before; `store reclaim' of the
; small store reserves heap-figure's 1,843 MB (on the OpenBSD guest's
; 195,856,696-octet core) and 28 threads beside it: 2,170 MB in all, so a
; 2 GiB machine refuses it by name (machine-cannot-hold-threads), as does
; OpenBSD's default datasize, where `run' is accepted.
(assert! (equal (fn-heap-reserve-operation-decide :run *fn-heap-small-profile* *hrt-core*
                                                  *hrt-nursery* (list *hrt-datasize*) 32)
                (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list *hrt-datasize*) 32)))
(assert! (equal (car (fn-heap-reserve-operation-decide :run *fn-heap-small-profile*
                                                       *hrt-core* *hrt-nursery*
                                                       (list *hrt-datasize*) 32))
                :heap))
(defconst *hrt-2200* (list (* 2200 *fn-heap-mib*)))
(assert! (equal (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2200* 0)
                '(:heap 1843 "small" 2200 1024 28)))
(assert! (equal (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile* 195856696
                                                  *hrt-nursery* *hrt-2g* 0)
                '(:refused :machine-cannot-hold-threads 2170 2048)))
(assert! (equal (car (fn-heap-reserve-operation-decide :reclaim *fn-heap-small-profile*
                                                       195856696 *hrt-nursery*
                                                       (list *hrt-datasize*) 0))
                :refused))

; The witness.
(assert! (equal (hrt-op-hyps :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                             *hrt-2200* 0)
                '(t t)))
(assert! (hrt-op-conclusion :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                            *hrt-2200* 0))

(defmacro hrt-op-must-fail (name &rest hyps)
  `(must-fail
    (defthm ,name
      (let ((r (fn-heap-reserve-operation-decide action profile core nursery
                                                 observations connections))
            (d (fn-heap-operation-decide action profile core nursery observations)))
        (implies (and ,@hyps)
                 (and (equal (car d) :heap)
                      (equal (fn-heap-decision-mb r) (fn-heap-decision-mb d))
                      (<= (+ (* *fn-heap-mib* (fn-heap-decision-mb r))
                             (nfix core)
                             (* (fn-heap-reserve-threads r)
                                (+ (* 1024 (fn-heap-reserve-stack-kib r))
                                   *fn-heap-thread-runtime-octets*)))
                          (fn-heap-machine-octets observations)))))
      :hints (("Goal" :cases ((member-equal action '(:compact :reclaim)))
               :use ((:instance fn-heap-reserve-decide-is-reserve-of-heap-decide))
               :in-theory (e/d (fn-heap-reservation-octets fn-heap-reserve-threads
                                fn-heap-reserve-stack-kib)
                               (fn-heap-decide fn-heap-operation-decide
                                fn-heap-reserve-decide
                                fn-bs-profile-admittedp fn-heap-machine-octets
                                fn-heap-decide-refuses-exactly-past-the-machine
                                fn-native-control-max-active-clients
                                fn-heap-mb-of fn-heap-stack-kib fn-heap-thread-count)))))))

; Without the admitted profile: no store, whose figure is the machine, so
; the heap, the core and a thread exceed it.
(assert! (equal (hrt-op-hyps :reclaim nil 195856696 *hrt-nursery* *hrt-2g* 0)
                '(nil t)))
(assert! (not (hrt-op-conclusion :reclaim nil 195856696 *hrt-nursery* *hrt-2g* 0)))
(hrt-op-must-fail hrt-op-without-admitted
                  (equal (car r) :heap))

; Without the accepted reservation: the reclaim under OpenBSD's datasize.
(assert! (equal (hrt-op-hyps :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                             (list *hrt-datasize*) 0)
                '(t nil)))
(assert! (not (hrt-op-conclusion :reclaim *fn-heap-small-profile* 195856696 *hrt-nursery*
                                 (list *hrt-datasize*) 0)))
(hrt-op-must-fail hrt-op-without-heap
                  (fn-bs-profile-admittedp profile))
