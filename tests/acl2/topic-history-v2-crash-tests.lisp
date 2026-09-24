; A v2 administrator-generation anchor through the mixed E2/T10/topic Store,
; its modeled crash/recovery transition, and the observed-open entry point.
(in-package "ACL2")
(include-book "../../books/topic-history-store-invariants")
(include-book "consumer-topic-store-tests")
(include-book "std/testing/must-fail" :dir :system)

; The fixture is a real completed Store trace: consumer bootstrap/register,
; T10 enrollment and exact-source acceptance, admin install, v2 anchor, and
; report admission.  The nine-field anchor binds the install at sequence 4.
(assert-event (equal (len *cts-anchor*) 9))
(assert-event (equal (fn-th-at 8 *cts-anchor*) 4))
(assert-event (fn-sti-livep *cts-admitted*))
(assert-event (equal (fn-th-at 0 (fn-sn-topic *cts-admitted*)) :ok))
(assert-event (equal (fn-cp-nth 7
                      (fn-cp-find '(3)
                       (fn-cp-nth 5 (fn-sn-consumer *cts-admitted*)))) 0))

; A generation change with the same administrator ID is not eligible, and
; the actual topic preparation cannot stage it for durable publication.
(defconst *thv2-wrong-anchor* (update-nth 8 9 *cts-anchor*))
(assert-event (equal (fn-th-at 0
                      (fn-th-prefix-step (fn-sn-topic *cts-installed*)
                                         *thv2-wrong-anchor*))
                     :fault))
(assert-event (equal (fn-sn-prepare-topic
                      (thsn-reserve *cts-installed*) *thv2-wrong-anchor*)
                     (thsn-reserve *cts-installed*)))
(must-fail
 (assert-event
  (not (equal (fn-sn-prepare-topic
               (thsn-reserve *cts-installed*) *thv2-wrong-anchor*)
              (thsn-reserve *cts-installed*)))))

; Crash and recovery are the actual Store transition arms.  The recovered
; physical history must pass the observed topic check and reconstruct the
; same topic and consumer projections, including the unchanged ACK.
(make-event `(defconst *thv2-crashed*
               ',(fn-snrt-step *cts-admitted* '(:crash :old :absent))))
(assert-event (equal (fn-sf-phase (fn-sn-files *thv2-crashed*)) :replaying))
(make-event `(defconst *thv2-recovered*
               ',(fn-snrt-step *thv2-crashed* '(:recover))))
(assert-event (equal (fn-sf-phase (fn-sn-files *thv2-recovered*)) :recovering))
(assert-event (fn-sn-observed-topic-okp
               (fn-sf-records (fn-sn-files *thv2-recovered*))))
(assert-event (equal (fn-sn-topic *thv2-recovered*)
                     (fn-th-prefix-project
                      (fn-sf-records (fn-sn-files *thv2-recovered*)))))
(assert-event (equal (fn-sn-topic *thv2-recovered*)
                     (fn-sn-topic *cts-admitted*)))
(assert-event (equal (fn-sn-consumer *thv2-recovered*)
                     (fn-sn-consumer *cts-admitted*)))

(make-event `(defconst *thv2-open*
               ',(fn-sn-open-observed
                  '("fn.test") 32 8
                  (fn-sf-records (fn-sn-files *thv2-recovered*)))))
(assert-event (fn-sn-open-okp *thv2-open*))
(assert-event (equal (fn-sn-topic (fn-sn-open-state *thv2-open*))
                     (fn-sn-topic *cts-admitted*)))
(assert-event (equal (fn-cp-nth 7
                      (fn-cp-find '(3)
                       (fn-cp-nth 5
                        (fn-sn-consumer (fn-sn-open-state *thv2-open*))))) 0))

; A syntactically valid but unadmitted v2 anchor in the physical directory
; cannot borrow the real install's ID with a different generation.
(defconst *thv2-bad-history*
  (update-nth 5 *thv2-wrong-anchor*
              (fn-sf-records (fn-sn-files *cts-admitted*))))
(assert-event (not (fn-sn-observed-topic-okp *thv2-bad-history*)))
(assert-event (not (fn-sn-open-okp
                    (fn-sn-open-observed '("fn.test") 32 8
                                         *thv2-bad-history*))))
