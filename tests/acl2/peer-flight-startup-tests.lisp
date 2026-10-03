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
