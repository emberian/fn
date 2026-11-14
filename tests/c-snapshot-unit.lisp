(in-package "ACL2")
(include-book "../books/executor")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-csu-profile*
 (put-assoc-equal :groups '(("snapshot.test" . 7))
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :large-upload-windows 1
    (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096) (4 . 65536)) *fn2-profile-tiny*)))))

(defun fn2-csu-poll (fuel token fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel 0 0 fn2-core)
  (mv-let (code cut event fn2-core) (fn2-csnapshot-poll token 7 0 1 fn2-core)
   (if (eq code :more) (fn2-csu-poll (- fuel 1) token fn2-core)
    (mv code cut event fn2-core)))))

; Fixture fuel cannot make a partial traversal pass: DONE and the complete
; source counts are asserted. The production cursor has no such horizon.
(defun fn2-csu-sources (fuel token overlays runs fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv nil overlays runs fn2-core)
  (b* (((mv code row sid & entries fn2-core) (fn2-csnapshot-next token 7 0 1 fn2-core))
       ((when (eq code :done)) (mv t overlays runs fn2-core))
       ((when (eq code :overlay))
        (b* (((mv decoded & fn2-core) (fn2-csnapshot-overlay-entry token 7 0 1 row 0 0 fn2-core)))
         (if (and (eq decoded :ok) (= sid *fn2-groups-sid*) (= entries 1))
             (fn2-csu-sources (- fuel 1) token (+ 1 overlays) runs fn2-core)
           (mv nil overlays runs fn2-core))))
       ((when (eq code :run))
        (b* (((mv info & & & first & & fn2-core) (fn2-csnapshot-run-info token 7 0 1 row fn2-core))
             ((mv page slot gen kind owner generation off len & fn2-core)
              (fn2-csnapshot-run-page token 7 0 1 row first 0 4096 fn2-core))
             (owned (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (owned)
                      (eq (fn2-pool-workspace-code slot gen kind owner generation fn2-pool) :ok) owned)))
         (if (and (eq info :ok) (eq page :ok) owned (= off 0) (= len 4096)
                  (= sid *fn2-groups-sid*) (= entries 1))
             (fn2-csu-sources (- fuel 1) token overlays (+ 1 runs) fn2-core)
           (mv nil overlays runs fn2-core))))
       ((unless (eq code :more)) (mv nil overlays runs fn2-core)))
   (fn2-csu-sources (- fuel 1) token overlays runs fn2-core))))

(defun fn2-csu-turns (fuel fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) fn2-core
  (b* (((mv & & & & fn2-core) (fn2-turn fn2-core)))
   (fn2-csu-turns (- fuel 1) fn2-core))))

(defun fn2-csu-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-csu-profile* :null nil fn2-core))
      ; Actual successor declaration leaves unadmitted OPEN work. Closing
      ; staging must preserve it without waiting for it to publish.
      ((mv put fn2-core) (fn2-successor-put 0 0 *fn2-groups-sid* :insert fn2-core))
      ((mv begun token fn2-core) (fn2-csnapshot-begin 7 0 1 fn2-core))
      ((mv closed & fn2-core) (fn2-successor-stage 0 fn2-core))
      ((mv held cut event fn2-core) (fn2-csu-poll 20 token fn2-core))
      ((mv wrong & & fn2-core) (fn2-csnapshot-poll token 7 0 2 fn2-core))
      ((mv busy & fn2-core) (fn2-csnapshot-begin 7 0 1 fn2-core))
      ((mv seal fn2-core) (fn2-sealer-step 4096 fn2-core))
      ((mv genesis fn2-core) (fn2-groups-genesis *fn2-csu-profile* fn2-core))
      ; Exercise the real scheduler while held: it must not retire the source
      ; or stop the parked sealer for the snapshot's BUSY answer.
      (fn2-core (fn2-csu-turns 20 fn2-core))
      ((mv complete overlays runs fn2-core) (fn2-csu-sources 200 token 0 0 fn2-core))
      ((mv denied fn2-core) (fn2-csnapshot-release token 7 0 2 fn2-core))
      ((mv released fn2-core) (fn2-csnapshot-release token 7 0 1 fn2-core))
      ((mv resumed & fn2-core) (fn2-successor-stage 0 fn2-core))
      ((unless (and (eq put :ok) (eq begun :ok) (eq closed :full) (eq held :held)
                    (= cut 0) (= event 0) (eq wrong :owner) (eq busy :busy)
                    (eq seal :busy) (eq genesis :full) complete (= overlays 1) (= runs 0)
                    (eq denied :owner) (eq released :ok) (not (eq resumed :full))
                    (not (fn2-core-stopped-p fn2-core))))
       (mv nil fn2-core))
      ; Thaw lets the real sealer replace the frozen overlay with its run.
      (fn2-core (fn2-csu-turns 400 fn2-core))
      ((mv again next-token fn2-core) (fn2-csnapshot-begin 7 0 1 fn2-core))
      ((mv stale fn2-core) (fn2-csnapshot-release token 7 0 1 fn2-core))
      ((mv next-held & & fn2-core) (fn2-csu-poll 20 next-token fn2-core))
      ((mv done overlays runs fn2-core) (fn2-csu-sources 200 next-token 0 0 fn2-core))
      ((mv finish fn2-core) (fn2-csnapshot-release next-token 7 0 1 fn2-core)))
  (mv (and (eq again :ok) (< token next-token) (eq stale :owner)
           (eq next-held :held) done (= overlays 0) (= runs 1) (eq finish :ok)
           (not (fn2-core-stopped-p fn2-core))) fn2-core)))
(defun fn2-csu-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-csu-body fn2-core) answer)))
(assert-event (fn2-csu-test))
