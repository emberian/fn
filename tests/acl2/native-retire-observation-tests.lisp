; PRF-1263 reachable operator decision witnesses, no owner-stop claim.
(in-package "ACL2")
(include-book "../../books/native-retire")

(defconst *nrot-request* (fn-nret-request-argv 10))
(assert-event (equal (fn-nret-observation-budget-ticks *nrot-request* 1000) 70000))

; Expiry positives assert the complete antecedent and conclusion; :held is
; reachable if the control listener closes before the store owner releases.
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (natp 70100) (posp 1000)
      (member-equal :live '(:live :held))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 1000)
          (- (nfix 70100) (nfix 100)))
      (equal (fn-nret-observation-step *nrot-request* 100 70100 1000 :live)
             :uncertain)))
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (natp 70101) (posp 1000)
      (member-equal :held '(:live :held))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 1000)
          (- (nfix 70101) (nfix 100)))
      (equal (fn-nret-observation-step *nrot-request* 100 70101 1000 :held)
             :uncertain)))

; Remove expiry: still live, one tick before the boundary, conclusion fails.
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (natp 70099) (posp 1000)
      (member-equal :live '(:live :held))
      (not (<= (fn-nret-observation-budget-ticks *nrot-request* 1000)
               (- (nfix 70099) (nfix 100))))
      (not (equal (fn-nret-observation-step *nrot-request* 100 70099 1000 :live)
                  :uncertain))))
; Remove live/held: the deadline holds, but stopped permits report inspection.
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (natp 70100) (posp 1000)
      (not (member-equal :offline '(:live :held)))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 1000)
          (- (nfix 70100) (nfix 100)))
      (not (equal (fn-nret-observation-step *nrot-request* 100 70100 1000 :offline)
                  :uncertain))))

; Request removal: retain every clock/liveness/deadline premise; malformed
; request faults rather than claiming the command's observation expired.
(assert-event
 (and (not (fn-nret-request nil)) (natp 100) (natp 70100) (posp 1000)
      (member-equal :live '(:live :held))
      (<= (fn-nret-observation-budget-ticks nil 1000) (- 70100 100))
      (not (equal (fn-nret-observation-step nil 100 70100 1000 :live) :uncertain))))
; Clock-start removal.
(assert-event
 (and (fn-nret-request *nrot-request*) (not (natp -100)) (natp 70000) (posp 1000)
      (member-equal :live '(:live :held))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 1000) (- 70000 -100))
      (not (equal (fn-nret-observation-step *nrot-request* -100 70000 1000 :live)
                  :uncertain))))
; Current clock removal.
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (not (natp 140201/2)) (posp 1000)
      (member-equal :live '(:live :held))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 1000) (- 140201/2 100))
      (not (equal (fn-nret-observation-step *nrot-request* 100 140201/2 1000 :live)
                  :uncertain))))
; Rate removal.
(assert-event
 (and (fn-nret-request *nrot-request*) (natp 100) (natp 70100) (not (posp 0))
      (member-equal :live '(:live :held))
      (<= (fn-nret-observation-budget-ticks *nrot-request* 0) (- 70100 100))
      (not (equal (fn-nret-observation-step *nrot-request* 100 70100 0 :live)
                  :uncertain))))

; Stopped positive and removal witness for the report theorem's antecedent.
(assert-event
 (and (equal (fn-nret-observation-step *nrot-request* 100 100 1000 :stale) :report)
      (member-equal :stale '(:offline :stale))))
(assert-event
 (and (not (equal (fn-nret-observation-step *nrot-request* 100 100 1000 :live) :report))
      (not (member-equal :live '(:offline :stale)))))

; Invalid external observation/request/clock inputs do not imply stopped.
(assert-event (equal (fn-nret-observation-step nil 100 100 1000 :offline) :fault))
(assert-event (equal (fn-nret-observation-step *nrot-request* 100 100 0 :offline) :fault))
(assert-event (equal (fn-nret-observation-step *nrot-request* 100 99 1000 :offline) :fault))
(assert-event (equal (fn-nret-observation-step *nrot-request* 100 100 1000 :unknown) :fault))
