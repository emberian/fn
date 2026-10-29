; T10's teeth (fn2-core-state-bounded) and its per-child table.
; Positive: tiny and concrete cores initialized twice agree; a short echo and
; scribe run through the real executor (turns, outbox acknowledgements,
; posted accept results and clock observations) leaves the measure unchanged
; after every step. Negative: one child array resized after init changes it.
; Run: sh fn2/tools/certify.sh tests/owed-d-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-d")

(defun fn2-od-ack-all (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (mv-let (code fn2-ops) (fn2-outbox-ack (fn2-outbox-queued fn2-ops) fn2-ops)
      (declare (ignore code)) fn2-ops)
    fn2-core))
(defun fn2-od-clock (now fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops) (fn2-post-clock now now 1 fn2-ops) fn2-core))
; Complete the first submitted Accept, if any, with a fresh capability.
(defun fn2-od-accept (k fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (if (and (< 0 (fn2-ops-rows fn2-ops))
             (equal (fn2-op-kind 0 fn2-ops) *fn2-action-accept*)
             (equal (fn2-op-phase 0 fn2-ops) *fn2-op-phase-submitted*))
        (fn2-post-result 0 0 (fn2-op-gen 0 fn2-ops) *fn2-event-accept-result*
                         *fn2-outcome-done* 0 0 k 9 fn2-ops)
      fn2-ops)
    fn2-core))

(in-theory (disable fn2-turn fn2-od-ack-all fn2-od-accept fn2-od-clock fn2-core-resident-measure
                    fn2-init-executor fn2-core-init))
; Every step keeps the measure.
(defun fn2-od-run (left m0 fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv t fn2-core)
    (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
         (ok1 (equal (fn2-core-resident-measure fn2-core) m0))
         (fn2-core (fn2-od-ack-all fn2-core))
         (ok2 (equal (fn2-core-resident-measure fn2-core) m0))
         (fn2-core (fn2-od-accept left fn2-core))
         (fn2-core (fn2-od-clock left fn2-core))
         (ok3 (equal (fn2-core-resident-measure fn2-core) m0))
         ((unless (and ok1 ok2 ok3)) (mv nil fn2-core)))
      (fn2-od-run (- left 1) m0 fn2-core))))

(defun fn2-od-profile-check (profile)
  (declare (xargs :verify-guards nil))
  (let ((m1 (with-local-stobj fn2-core
              (mv-let (m fn2-core) (let ((fn2-core (fn2-core-init profile fn2-core)))
                                     (mv (fn2-core-resident-measure fn2-core) fn2-core)) m)))
        (m2 (with-local-stobj fn2-core
              (mv-let (m fn2-core)
                (let* ((fn2-core (fn2-init-executor profile :echo t fn2-core))
                       (m0 (fn2-core-resident-measure fn2-core)))
                  (mv-let (ok fn2-core) (fn2-od-run 40 m0 fn2-core)
                    (mv (and ok m0) fn2-core)))
                m))))
    (and (posp m1) (equal m1 m2))))

(defun fn2-core-test-state-bounded ()
  (declare (xargs :verify-guards nil))
  (and (fn2-od-profile-check *fn2-profile-tiny*)
       (fn2-od-profile-check *fn2-profile-concrete*)
       (fn2-od-profile-check *fn2-profile-tiny-near-limit*)))

; A pool byte array grown after init: the statement's equality refuses it.
(defun fn2-core-test-state-bounded-negative ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core)
      (let* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
             (m0 (fn2-core-resident-measure fn2-core))
             (fn2-core (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
                         (fn2-pool)
                         (resize-fn2-pool-data (+ 1 (fn2-pool-data-length fn2-pool)) fn2-pool)
                         fn2-core)))
        (mv (not (equal (fn2-core-resident-measure fn2-core) m0)) fn2-core))
      ok)))

(fn2-assert-owed-teeth fn2-core-state-bounded)

; The printed table: per child, rows and bytes, for tiny and concrete.
(defun fn2-od-table (profile)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (r fn2-core)
      (let ((fn2-core (fn2-core-init profile fn2-core)))
        (mv (list (fn2-core-resident-breakdown fn2-core) (fn2-core-resident-measure fn2-core)) fn2-core))
      r)))
(defconst *fn2-od-tiny* (fn2-od-table *fn2-profile-tiny*))
(defconst *fn2-od-concrete* (fn2-od-table *fn2-profile-concrete*))
(value-triple (cw "~%T10 RESIDENT tiny ~x0~%T10 RESIDENT concrete ~x1~%T10 UNMEASURED ~x2~%" *fn2-od-tiny* *fn2-od-concrete* *fn2-resident-refused*))
