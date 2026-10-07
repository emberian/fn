(in-package "ACL2")
(include-book "../../books/peer-flight-startup")
(defconst *pfrst-peer* '(32768 65536 2 1 32768 20))
(defconst *pfrst-core* '(83886080 . 67108864))
(defconst *pfrst-plan*
 (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                     "/tmp/store" 4 8 256 *pfrst-peer* nil))
(assert-event
 (and (fn-prstartup-planp *pfrst-plan*)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                                                *pfrst-plan* *pfrst-peer* nil)) :hold)
      (equal (+ (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan* nil)
                (fn-pfr-at 0 *pfrst-peer*)) 268435456)))
(assert-event
 (equal (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                            "/tmp/store" 4 8 256 nil nil)
        (fn-prstartup-default-plan 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                   "/tmp/store" 4 8 256 nil)))
(assert-event
 (and (equal (fn-prstartup-status
  (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                       "/tmp/store" 4 8 256 '(bad) nil)) :refused)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0 nil *pfrst-peer* nil)) :refused)))

(assert-event
 (and (fn-pfr-operation-observes-p :run)
      (not (fn-pfr-operation-observes-p :status))
      (equal (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               *pfrst-plan* *pfrst-peer* nil)
             (list 268435456
                   (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan* nil)
                   *pfrst-peer* (fn-heap-stack-octets nil) *fn-heap-thread-runtime-octets*))
      (not (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               nil *pfrst-peer* nil))))

(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (yes (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list need) nil))
        (no (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list (1- need)) nil)))
  (and (equal (car yes) :hold)
       (equal (cadr yes) (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
                          *pfrst-plan* *pfrst-peer* nil))
       (equal no '(:refused :peer-native-reservation-not-held)))))

; A policy file changed after launch cannot add a second unfunded worker.
(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (changed (update-nth 3 2 *pfrst-peer*))
        (grant (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed (list need) nil)))
  (and (fn-pfr-policy-p changed)
       (equal (car (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed nil)) :hold)
       (equal grant '(:refused :peer-native-reservation-not-held))
       (stringp (fn-prstartup-peer-native-refusal-line grant)))))

; Launcher and startup agree with a peer flight profile (cold-start,
; 2026-10-04): the run the launcher reserves for a fresh development store
; with this peer allowance is admitted and its native grant held at exactly
; that figure for the same store observation; the unobserved bound refuses.
; The host trigger the figures are taken at: books/profile-limits.lisp's :gc-nursery-mib
; (+fnn-gc-nursery-octets+), not a copy of its value.
(defconst *pfrst-nursery* (* 1048576 (fn-profile-limit :gc-nursery-mib)))
(defconst *pfrst-run-core* '(615110568 . 517243296))
(defconst *pfrst-fresh* '(0 . 0))
(defconst *pfrst-machine* (list (* 24 1073741824)))
(defconst *pfrst-flight* (list (* 8 1048576) (* 512 1048576) 2 1 (* 64 1048576) (expt 2 50)))
(defconst *pfrst-run*
 (fn-pfr-extend-operation-reservation
  (fn-prstartup-extend-operation-reservation
   (fn-heap-reserve-operation-decide :run *fn-bs-profile-development* *pfrst-run-core*
                                     *pfrst-nursery* *pfrst-machine* 32 *pfrst-fresh*)
   :run nil "/tmp/store" 4 8 *pfrst-run-core* *pfrst-machine*
   *fn-bs-profile-development* *pfrst-fresh*)
  :run *pfrst-flight* *pfrst-run-core* *pfrst-machine*))
(assert-event
 (let* ((dyn (* 1048576 (fn-prstartup-nth 1 *pfrst-run*)))
        (plan (fn-prstartup-default-plan-with-peer
               dyn (cdr *pfrst-run-core*) *fn-bs-profile-development* *pfrst-run-core*
               *pfrst-nursery* nil nil 32 "/tmp/store" 4 8 1024 *pfrst-flight* *pfrst-fresh*)))
  (and (equal (fn-prstartup-nth 0 *pfrst-run*) :heap)
       (fn-prstartup-planp plan)
       (equal (car (fn-prstartup-peer-native-grant
                    dyn *fn-bs-profile-development* *pfrst-run-core* *pfrst-nursery* nil 32
                    plan *pfrst-flight* *pfrst-machine* *pfrst-fresh*))
              :hold)
       (equal (fn-prstartup-status
               (fn-prstartup-default-plan-with-peer
                dyn (cdr *pfrst-run-core*) *fn-bs-profile-development* *pfrst-run-core*
                *pfrst-nursery* nil nil 32 "/tmp/store" 4 8 1024 *pfrst-flight* nil))
              :refused))))

; KEYSTONE fn-prstartup-peer-launch-admits-owner-protected, its fields
; (cold-start, 2026-10-04; w-peer cls2/cls3 on 6107ceb56).  w-peer's store:
; init --max-transactions 16384 --max-history-octets 67108864
; --max-record-octets 196608 --max-article-octets 32768
; --max-groups-per-article 16 --max-open-suffix 128, peer flight profile
; 8MiB,512MiB,2,1,64MiB,2^50.  A probe whose own usage is 214.6 MB answers
; 1509 without the launch floor (DEFAULT extension skipped), and an owner
; whose usage is 18 MB larger needs 1526: the figures of the hand repro.
(defconst *pfrst-wp-profile*
 (update-nth 7 128 (update-nth 5 16 (update-nth 3 196608
  (fn-bs-profile-preset 16384 67108864 32768)))))
(defconst *pfrst-wp-probe-core* '(615110568 . 214600000))
(defconst *pfrst-wp-owner-core* '(615110568 . 232600000))
(defconst *pfrst-wp-base*
 (fn-heap-reserve-operation-decide :run *pfrst-wp-profile* *pfrst-wp-probe-core*
                                   *pfrst-nursery* *pfrst-machine* 32 *pfrst-fresh*))
(defconst *pfrst-wp-run*
 (fn-pfr-extend-operation-reservation
  (fn-prstartup-extend-operation-reservation *pfrst-wp-base*
   :run nil "/tmp/store" 4 8 *pfrst-wp-probe-core* *pfrst-machine*
   *pfrst-wp-profile* *pfrst-fresh*)
  :run *pfrst-flight* *pfrst-wp-probe-core* *pfrst-machine*))
(defun pfrst-wp-owner-need (dyn core)
 (declare (xargs :guard t :verify-guards nil))
 (fn-prstartup-protected-with-peer
  *pfrst-wp-profile* core
  (fn-heap-nursery-trigger dyn (* 1048576 (fn-profile-limit :gc-nursery-mib)))
  nil 32 *pfrst-flight* *pfrst-fresh*))
; Satisfiable: the profile is valid, the launcher answers :heap with the
; peer, and the owner (same core file, larger usage) is admitted there:
; its protected check, its DEFAULT plan and its native peer grant.
(assert-event
 (let* ((dyn (* 1048576 (fn-prstartup-nth 1 *pfrst-wp-run*)))
        (nursery (fn-heap-nursery-trigger dyn (* 1048576 (fn-profile-limit :gc-nursery-mib))))
        (plan (fn-prstartup-default-plan-with-peer
               dyn (cdr *pfrst-wp-owner-core*) *pfrst-wp-profile* *pfrst-wp-owner-core*
               nursery nil nil 32 "/tmp/store" 4 8 1024 *pfrst-flight* *pfrst-fresh*)))
  (and (fn-bs-profile-validp *pfrst-wp-profile*)
       (fn-pfr-policy-p *pfrst-flight*)
       (equal (fn-prstartup-nth 0 *pfrst-wp-run*) :heap)
       ;; 1891 before the pool's read reserve (lane pool-refusal): the
       ;; served run now also holds its workers' reads in flight.
       (equal (fn-prstartup-nth 1 *pfrst-wp-run*) 1783)
       (equal (fn-heap-core-file *pfrst-wp-owner-core*) (fn-heap-core-file *pfrst-wp-probe-core*))
       (<= (pfrst-wp-owner-need dyn *pfrst-wp-owner-core*) dyn)
       (fn-prstartup-planp plan)
       (equal (car (fn-prstartup-peer-native-grant
                    dyn *pfrst-wp-profile* *pfrst-wp-owner-core* nursery nil 32
                    plan *pfrst-flight* *pfrst-machine* *pfrst-fresh*))
              :hold))))
; Teeth: without the DEFAULT extension's launch floor the peer figure is
; 6107ceb56's figure (1509 at the 64 MiB trigger, 1397 at the 8 MiB trigger
; since MEM-007), and the owner refuses it (it needs 1414, was 1526); an owner
; core with a larger file (the core-file hypothesis dropped) fails at 1783
; (was 1893).
(assert-event
 (let* ((old (fn-pfr-extend-operation-reservation *pfrst-wp-base* :run *pfrst-flight*
                                                   *pfrst-wp-probe-core* *pfrst-machine*))
        (dyn-old (* 1048576 (fn-prstartup-nth 1 old)))
        (dyn (* 1048576 (fn-prstartup-nth 1 *pfrst-wp-run*))))
  (and (equal (fn-prstartup-nth 0 old) :heap)
       (equal (fn-prstartup-nth 1 old) 1397)
       (not (<= (pfrst-wp-owner-need dyn-old *pfrst-wp-owner-core*) dyn-old))
       (<= (pfrst-wp-owner-need (* 1048576 1414) *pfrst-wp-owner-core*) (* 1048576 1414))
       (not (<= (pfrst-wp-owner-need (* 1048576 1413) *pfrst-wp-owner-core*) (* 1048576 1413)))
       (not (<= (pfrst-wp-owner-need dyn '(1615110568 . 1600000000)) dyn)))))
