(in-package "ACL2")
(include-book "../../books/page-read-startup")

(defconst *prst-plan* (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256))
(assert-event (and (fn-prstartup-planp *prst-plan*)
  (equal (fn-prstartup-file-capacity *prst-plan*) 256)
  (equal (fn-prstartup-cache-capacity *prst-plan*) 256)
  (equal (fn-prstartup-decoded-workers *prst-plan*) 4)
  (<= (fn-prstartup-required-heap 256 4 "/tmp/store") 268435456)))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256)) :refused))
(assert-event (equal (fn-prstartup-status (fn-prstartup-plan 536870912 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 8)) :refused))
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
 (let ((plan (fn-prstartup-plan 1024 0 0 "/tmp/store" 4 1048576 4194304 8 256)))
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
      (equal (fn-prstartup-nth 1 *prst-launch*) 257)
      (equal (fn-prstartup-nth 4 *prst-launch*) 1024)
      (equal (fn-prstartup-nth 5 *prst-launch*) 20)
      (<= (fn-heap-reservation-octets (fn-prstartup-nth 1 *prst-launch*)
             '(83886080 . 67108864) (fn-prstartup-nth 4 *prst-launch*) (fn-prstartup-nth 5 *prst-launch*))
          (fn-heap-machine-octets '(8589934592)))
      (equal (fn-prstartup-status
              (fn-prstartup-plan 268435456 67108864 268435456 "/tmp/store" 4 1048576 4194304 8 256)) :refused)
      (fn-prstartup-planp
       (fn-prstartup-plan (* 1048576 (fn-prstartup-nth 1 *prst-launch*)) 67108864 268435456
                           "/tmp/store" 4 1048576 4194304 8 256))))
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

; Launcher and startup agree (cold-start, 2026-10-04).  The launcher sizes a
; run by the store on disk (books/heap-figure.lisp, lane
; reservation-after-flip); the startup's protected allowance takes the same
; observation.  A development store, freshly made, at exactly its launcher's
; DEFAULT-extended figure is admitted; with the unobserved bound (what every
; launched node of d5b0b9100 carried) the same heap is refused, by name.
(defconst *prst-run-core* '(615110568 . 517243296))
(defconst *prst-fresh* '(0 . 0))
(defconst *prst-run-machine* (list (* 24 1073741824)))
(defconst *prst-run*
 (fn-prstartup-extend-operation-reservation
  (fn-heap-reserve-operation-decide :run *fn-bs-profile-development* *prst-run-core*
                                    (* 64 1048576) *prst-run-machine* 32 *prst-fresh*)
  :run nil "/tmp/store" 4 8 *prst-run-core* *prst-run-machine*
  *fn-bs-profile-development* *prst-fresh*))
(assert-event
 (let ((dyn (* 1048576 (fn-prstartup-nth 1 *prst-run*))))
  (and (equal (fn-prstartup-nth 0 *prst-run*) :heap)
       (fn-prstartup-planp
        (fn-prstartup-default-plan dyn (cdr *prst-run-core*) *fn-bs-profile-development*
                                   *prst-run-core* (* 64 1048576) nil nil 32 "/tmp/store" 4 8 1024
                                   *prst-fresh*))
       (equal (fn-prstartup-default-plan dyn (cdr *prst-run-core*) *fn-bs-profile-development*
                                         *prst-run-core* (* 64 1048576) nil nil 32 "/tmp/store" 4 8 1024
                                         nil)
              '(:refused :default-pool-heap-not-held))
       (stringp (fn-prstartup-refusal-line '(:refused :default-pool-heap-not-held))))))

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
                                                (* 64 1048576) *prst-run-machine* 32 *prst-fresh*))
        (dyn (* 1048576 (fn-prstartup-nth 1 base))))
  (and (equal (fn-prstartup-nth 0 base) :heap)
       (not (<= (fn-prstartup-protected *fn-bs-profile-development* *prst-owner-core*
                  (fn-heap-nursery-trigger dyn (* 64 1048576)) nil 32 *prst-fresh*)
                dyn)))))
