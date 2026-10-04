; PRF-1130: literal witnesses for the selected credential and actual plans.
(in-package "ACL2")
(include-book "../../books/peer-pull")
(include-book "must-fail-checked")

(defconst *ppat-base*
  (list (fn-cfg-row-make "reader" "path-identity" "reader.example" 0)
        (fn-cfg-row-make "reader" "transport-nntp" "127.0.0.1" 119)
        (fn-cfg-row-make "reader" "inbound-groups" "fn.*" 1048576)
        (fn-cfg-row-make "reader" "inbound-inflight" "" 4)
        (fn-cfg-row-make "reader" "pull-interval" "" 60)
        (fn-cfg-row-make "reader" "outbound-auth-profile" "feed.fnauth" 1)))
(defconst *ppat-row* (fn-pull-auth-row "reader" "reader.fnauth" nil))
(defconst *ppat-dedicated*
  (fn-pcb-extend-rows *ppat-base* (list *ppat-row*)))

; Unconditional extension theorem: a nonempty prior group with a different
; outbound credential selects exactly the dedicated credential and policy.
(assert-event (consp *ppat-base*))
(assert-event
 (equal (fn-pull-auth-of-rows
         (fn-pcb-extend-rows *ppat-base* (list *ppat-row*)))
        (if (equal "reader.fnauth" "") nil
          (list :authinfo "reader.fnauth" (if nil t nil)))))
(assert-event (equal (fn-pull-auth-of-rows *ppat-base*)
                     '(:authinfo "feed.fnauth" t)))
(assert-event (equal (fn-pull-auth-of-rows *ppat-dedicated*)
                     '(:authinfo "reader.fnauth" nil)))
; Replacement also works without any outbound row.
(assert-event
 (equal (fn-pull-auth-of-rows
         (fn-pcb-extend-rows (take 5 *ppat-base*) (list *ppat-row*)))
        '(:authinfo "reader.fnauth" nil)))
; Present empty profile is explicitly anonymous, including with an old
; dedicated row and a nonempty outbound policy in the same group.
(assert-event
 (equal (fn-pull-auth-of-rows
         (fn-pcb-extend-rows *ppat-dedicated*
                             (list (fn-pull-auth-row "reader" "" t))))
        nil))
(assert-event
 (equal (fn-pull-auth-of-rows
         (fn-pcb-extend-rows *ppat-dedicated*
                             (list (fn-pull-auth-row "reader" "new.fnauth" t))))
        '(:authinfo "new.fnauth" t)))

; Actual host-called entry, full literal antecedent and conclusion.
(defconst *ppat-plan* (car (fn-pull-plans *ppat-dedicated*)))
(assert-event (consp *ppat-plan*))
(assert-event (member-equal *ppat-plan* (fn-pull-plans *ppat-dedicated*)))
(assert-event
 (fn-pull-plan-credential-sourcep *ppat-plan*
                                  (fn-cfg-peer-names *ppat-dedicated*)
                                  *ppat-dedicated*))
(assert-event (equal (fn-pull-plan-auth *ppat-plan*)
                     '(:authinfo "reader.fnauth" nil)))
(defconst *ppat-anonymous*
  (fn-pcb-extend-rows *ppat-dedicated*
                      (list (fn-pull-auth-row "reader" "" nil))))
(defconst *ppat-anonymous-plan* (car (fn-pull-plans *ppat-anonymous*)))
(assert-event (consp *ppat-anonymous-plan*))
(assert-event (member-equal *ppat-anonymous-plan* (fn-pull-plans *ppat-anonymous*)))
(assert-event
 (fn-pull-plan-credential-sourcep *ppat-anonymous-plan*
                                  (fn-cfg-peer-names *ppat-anonymous*)
                                  *ppat-anonymous*))
(assert-event (equal (fn-pull-plan-auth *ppat-anonymous-plan*) nil))
; Hypothesis removal: membership fails and the conclusion fails.  There
; are no retained hypotheses.  This forged plan is not a corrupted state.
(defconst *ppat-forged*
  (list (fn-record-string-octets "reader")
        (fn-record-string-octets "127.0.0.1") 119
        (fn-record-string-octets "fn.*") 60000 '(:clear)
        '(:authinfo "feed.fnauth" t) *fn-pull-default-unavailable-rounds*))
(assert-event (not (member-equal *ppat-forged*
                                (fn-pull-plans *ppat-dedicated*))))
(assert-event
 (not (fn-pull-plan-credential-sourcep
       *ppat-forged* (fn-cfg-peer-names *ppat-dedicated*) *ppat-dedicated*)))
(must-fail-checked
 (assert-event
  (fn-pull-plan-credential-sourcep
   *ppat-forged* (fn-cfg-peer-names *ppat-dedicated*) *ppat-dedicated*)))
; Mutation witness: the previous shared-only selector gives the wrong
; credential on this reachable nonempty plan.
(assert-event
 (not (equal (fn-pull-plan-auth *ppat-plan*)
             (fn-pull-auth-of-rows *ppat-base*))))
