; Teeth for books/heap-reservation (lane image-floor, HST-017, extending
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
         (<= (+ *fn-heap-stack-base-octets*
                (* *fn-heap-stack-octets-per-line*
                   (fn-heap-article-lines-bound profile)))
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
; 32 connections: heap-figure's 814 MB, 60 threads of a 1,192 KiB stack
; (512 KiB + 40 x (16,384 + 1,024) lines), and the core once more: 1,308 MB in all.  With the old
; 64 MiB stacks the same threads reserved 4,080 MB beside the heap.
(assert! (equal (fn-heap-stack-kib *fn-heap-small-profile*) 1192))
(assert! (equal (fn-heap-thread-count 32) 60))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list *hrt-datasize*) 32)
                '(:heap 814 "small" 1536 1192 60)))
(assert! (< *hrt-datasize*
            (fn-heap-reservation-octets 814 *hrt-core* (* 64 1024) 60)))
; The threads push it past a machine the heap alone fits.
(assert! (equal (car (fn-heap-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                     (list (* 900 *fn-heap-mib*))))
                :heap))
(assert! (equal (fn-heap-reserve-decide *fn-heap-small-profile* *hrt-core* *hrt-nursery*
                                        (list (* 900 *fn-heap-mib*)) 32)
                '(:refused :machine-cannot-hold-threads 1308 900)))
; The default profile's 16 MiB article: heap-figure refuses it first.
(assert! (equal (fn-heap-stack-kib *fn-bs-profile-defaults*) 328232))
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
                             fn-heap-article-lines-bound fn-heap-mb-of))))))

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
                             fn-heap-article-lines-bound fn-heap-mb-of))))))

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
                             fn-heap-article-lines-bound fn-heap-mb-of))))))

; -----------------------------------------------------------------------------
; The refusal is exact at the boundary: the machine exactly the reservation
; is accepted, one octet less is refused.
(defconst *hrt-exact*
  (fn-heap-reservation-octets 814 *hrt-core* 1192 60))
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
(assert! (equal (fn-heap-reserve-report-line '(:heap 814 "small" 1536 1192 60))
                "heap=814 MB profile=small machine=1536 MB stack=1192 KB threads=60"))
(assert! (equal (fn-heap-reserve-report-line
                 '(:refused :machine-cannot-hold-threads 1308 900))
                "refused machine-cannot-hold-threads reservation=1308 MB machine=900 MB"))
(assert! (equal (fn-heap-reserve-report-line
                 '(:refused :machine-cannot-hold-profile 2671 2048))
                "refused machine-cannot-hold-profile heap=2671 MB machine=2048 MB"))
(assert! (equal (fn-heap-decision-exit-code
                 '(:refused :machine-cannot-hold-threads 1308 900))
                1))
(assert! (equal (fn-heap-decision-exit-code '(:heap 814 "small" 1536 1192 60)) 0))

; -----------------------------------------------------------------------------
; A bare `init' (PKT-582): the largest preset whose reservation the machine
; holds.  2 GiB: small; 24 GiB (hbox_native's default cgroup): development;
; 132 GB: scale.  The operator's own request is kept.
(defconst *hrt-bare* '(:default nil))
(assert! (equal (fn-heap-reserve-init-request *hrt-bare* *hrt-core* *hrt-nursery*
                                              (list (* 2048 *fn-heap-mib*)))
                *fn-heap-small-request*))
(assert! (equal (fn-heap-reserve-init-request *hrt-bare* *hrt-core* *hrt-nursery*
                                              (list (* 24 1024 *fn-heap-mib*)))
                '(:development nil)))
(assert! (equal (fn-heap-reserve-init-request *hrt-bare* *hrt-core* *hrt-nursery*
                                              (list 132000000000))
                '(:scale nil)))
(assert! (equal (fn-heap-reserve-init-request '(:default ((3 . 4096))) *hrt-core*
                                              *hrt-nursery* (list 132000000000))
                '(:default ((3 . 4096)))))

; The keystone's witness: 2 GiB holds small, and init's choice is accepted.
(assert! (fn-heap-reserve-acceptsp *fn-heap-small-request* *hrt-core* *hrt-nursery*
                                   (list (* 2048 *fn-heap-mib*))))
(assert! (fn-heap-reserve-acceptsp
          (fn-heap-reserve-init-request *hrt-bare* *hrt-core* *hrt-nursery*
                                        (list (* 2048 *fn-heap-mib*)))
          *hrt-core* *hrt-nursery* (list (* 2048 *fn-heap-mib*))))
; Without it: 512 MiB holds no preset; init writes small, which it refuses.
(assert! (not (fn-heap-reserve-acceptsp *fn-heap-small-request* *hrt-core* *hrt-nursery*
                                        (list (* 512 *fn-heap-mib*)))))
(assert! (not (fn-heap-reserve-acceptsp
               (fn-heap-reserve-init-request *hrt-bare* *hrt-core* *hrt-nursery*
                                             (list (* 512 *fn-heap-mib*)))
               *hrt-core* *hrt-nursery* (list (* 512 *fn-heap-mib*)))))
(must-fail
 (defthm hrt-init-without-small-fitting
   (fn-heap-reserve-acceptsp
    (fn-heap-reserve-init-request '(:default nil) core nursery observations)
    core nursery observations)
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp)))))
; Scale's witness and its hypothesis: 24 GiB does not hold scale, and init
; does not take it.
(assert! (fn-heap-reserve-acceptsp '(:scale nil) *hrt-core* *hrt-nursery*
                                   (list 132000000000)))
(assert! (not (fn-heap-reserve-acceptsp '(:scale nil) *hrt-core* *hrt-nursery*
                                        (list (* 24 1024 *fn-heap-mib*)))))
(must-fail
 (defthm hrt-init-scale-without-scale-fitting
   (equal (fn-heap-reserve-init-request '(:default nil) core nursery observations)
          '(:scale nil))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-heap-reserve-acceptsp)))))
