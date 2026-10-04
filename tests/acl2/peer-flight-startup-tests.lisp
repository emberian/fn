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
(defconst *pfrst-run-core* '(615110568 . 517243296))
(defconst *pfrst-fresh* '(0 . 0))
(defconst *pfrst-machine* (list (* 24 1073741824)))
(defconst *pfrst-flight* (list (* 8 1048576) (* 512 1048576) 2 1 (* 64 1048576) (expt 2 50)))
(defconst *pfrst-run*
 (fn-pfr-extend-operation-reservation
  (fn-prstartup-extend-operation-reservation
   (fn-heap-reserve-operation-decide :run *fn-bs-profile-development* *pfrst-run-core*
                                     (* 64 1048576) *pfrst-machine* 32 *pfrst-fresh*)
   :run nil "/tmp/store" 4 8 *pfrst-run-core* *pfrst-machine*)
  :run *pfrst-flight* *pfrst-run-core* *pfrst-machine*))
(assert-event
 (let* ((dyn (* 1048576 (fn-prstartup-nth 1 *pfrst-run*)))
        (plan (fn-prstartup-default-plan-with-peer
               dyn (cdr *pfrst-run-core*) *fn-bs-profile-development* *pfrst-run-core*
               (* 64 1048576) nil nil 32 "/tmp/store" 4 8 1024 *pfrst-flight* *pfrst-fresh*)))
  (and (equal (fn-prstartup-nth 0 *pfrst-run*) :heap)
       (fn-prstartup-planp plan)
       (equal (car (fn-prstartup-peer-native-grant
                    dyn *fn-bs-profile-development* *pfrst-run-core* (* 64 1048576) nil 32
                    plan *pfrst-flight* *pfrst-machine* *pfrst-fresh*))
              :hold)
       (equal (fn-prstartup-status
               (fn-prstartup-default-plan-with-peer
                dyn (cdr *pfrst-run-core*) *fn-bs-profile-development* *pfrst-run-core*
                (* 64 1048576) nil nil 32 "/tmp/store" 4 8 1024 *pfrst-flight* nil))
              :refused))))
