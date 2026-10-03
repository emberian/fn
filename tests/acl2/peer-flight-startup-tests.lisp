(in-package "ACL2")
(include-book "../../books/peer-flight-startup")
(defconst *pfrst-peer* '(32768 65536 2 1 32768 20))
(defconst *pfrst-core* '(83886080 . 67108864))
(defconst *pfrst-plan*
 (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                     "/tmp/store" 4 8 256 *pfrst-peer*))
(assert-event
 (and (fn-prstartup-planp *pfrst-plan*)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                                                *pfrst-plan* *pfrst-peer*)) :hold)
      (equal (+ (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan*)
                (fn-pfr-at 0 *pfrst-peer*)) 268435456)))
(assert-event
 (equal (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                            "/tmp/store" 4 8 256 nil)
        (fn-prstartup-default-plan 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                   "/tmp/store" 4 8 256)))
(assert-event
 (and (equal (fn-prstartup-status
  (fn-prstartup-default-plan-with-peer 268435456 67108864 nil *pfrst-core* 0 nil nil 0
                                       "/tmp/store" 4 8 256 '(bad))) :refused)
      (equal (fn-pfr-at 0 (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0 nil *pfrst-peer*)) :refused)))

(assert-event
 (and (fn-pfr-operation-observes-p :run)
      (not (fn-pfr-operation-observes-p :status))
      (equal (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               *pfrst-plan* *pfrst-peer*)
             (list 268435456
                   (fn-prstartup-peer-protected nil *pfrst-core* 0 nil 0 *pfrst-plan*)
                   *pfrst-peer* (fn-heap-stack-octets nil) *fn-heap-thread-runtime-octets*))
      (not (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
               nil *pfrst-peer*))))

(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (yes (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list need)))
        (no (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* *pfrst-peer* (list (1- need)))))
  (and (equal (car yes) :hold)
       (equal (cadr yes) (fn-prstartup-peer-native-capture 268435456 nil *pfrst-core* 0 nil 0
                          *pfrst-plan* *pfrst-peer*))
       (equal no '(:refused :peer-native-reservation-not-held)))))

; A policy file changed after launch cannot add a second unfunded worker.
(assert-event
 (let* ((need (fn-heap-reservation-octets 256 *pfrst-core* (fn-heap-stack-kib nil)
                    (+ (fn-heap-thread-count 0) 1)))
        (changed (update-nth 3 2 *pfrst-peer*))
        (grant (fn-prstartup-peer-native-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed (list need))))
  (and (fn-pfr-policy-p changed)
       (equal (car (fn-prstartup-peer-grant 268435456 nil *pfrst-core* 0 nil 0
                    *pfrst-plan* changed)) :hold)
       (equal grant '(:refused :peer-native-reservation-not-held))
       (stringp (fn-prstartup-peer-native-refusal-line grant)))))
