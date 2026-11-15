; Source-only control for the actual held empty cut. This exercises boot,
; snapshot admission and the peer reader; it constructs no checkpoint state.
(in-package "ACL2")
(include-book "../books/executor")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-phe-profile*
 (put-assoc-equal :history-id 257
  (put-assoc-equal :history-incarnation 65537
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096) (4 . 65536))
    *fn2-profile-tiny*))))

(defun fn2-phe-poll (fuel token fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel 0 0 fn2-core)
  (mv-let (code cut event fn2-core) (fn2-csnapshot-poll token 7 0 1 fn2-core)
   (if (eq code :more) (fn2-phe-poll (- fuel 1) token fn2-core)
    (mv code cut event fn2-core)))))

(defun fn2-phe-view (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-event-read (fn2-core-event-read fn2-core))
             (fn2-csnapshot (fn2-core-csnapshot fn2-core))
             (fn2-mk (fn2-core-mk fn2-core)) (fn2-fc (fn2-core-fc fn2-core))) (view)
  (list (fn2-event-read-phase 0 fn2-event-read)
        (fn2-event-read-token 0 fn2-event-read)
        (fn2-event-read-commit 0 fn2-event-read)
        (fn2-event-read-cut-commit 0 fn2-event-read)
        (fn2-event-read-cut-event 0 fn2-event-read)
        (fn2-event-read-next-event 0 fn2-event-read)
        (fn2-event-read-history 0 fn2-event-read)
        (fn2-event-read-history-incarnation 0 fn2-event-read)
        (fn2-mk-size (fn2-b-event-row (fn2-fc-rows fn2-fc)) fn2-mk)
        (fn2-csnapshot-phase 0 fn2-csnapshot)) view))

(defun fn2-phe-body (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-phe-profile* :null nil fn2-core))
      ((mv rc reader rgen fn2-core) (fn2-core-reserve 2 7 0 1 fn2-core))
      ((mv dc directory dgen fn2-core) (fn2-core-reserve 2 7 0 1 fn2-core))
      ((mv sc scratch sgen fn2-core) (fn2-core-reserve 0 7 0 1 fn2-core))
      ((mv begun token fn2-core) (fn2-csnapshot-begin 7 0 1 fn2-core))
      ((mv held cut event fn2-core) (fn2-phe-poll 200 token fn2-core))
      ((mv wrong fn2-core)
       (fn2-peer-history-open-core (+ 1 token) 0 reader rgen directory dgen
        *fn2-checkpoint-map-entries-start* scratch sgen 7 0 1 fn2-core))
      (before (fn2-phe-view fn2-core))
      ((mv opened fn2-core)
       (fn2-peer-history-open-core token 0 reader rgen directory dgen
        *fn2-checkpoint-map-entries-start* scratch sgen 7 0 1 fn2-core))
      (complete (fn2-phe-view fn2-core))
      ((mv closed fn2-core) (fn2-peer-history-close token 7 0 1 fn2-core))
      (after (fn2-phe-view fn2-core))
      ((mv rr fn2-core) (fn2-core-release reader rgen 7 0 1 fn2-core))
      ((mv dr fn2-core) (fn2-core-release directory dgen 7 0 1 fn2-core))
      ((mv sr fn2-core) (fn2-core-release scratch sgen 7 0 1 fn2-core)))
   (mv (and (eq rc :ok) (eq dc :ok) (eq sc :ok) (eq begun :ok)
            (eq held :held) (equal cut 0) (equal event 0)
            (eq wrong :snapshot) (equal (car before) *fn2-event-read-phase-idle*)
            (eq opened :complete)
            (equal complete (list *fn2-event-read-phase-complete* token 0 0 0 1 257 65537 0
                                  *fn2-csnapshot-phase-held*))
            (eq closed :ok) (equal (car after) *fn2-event-read-phase-idle*)
            (equal (cadr after) 0) (equal (nth 9 after) *fn2-csnapshot-phase-idle*)
            (eq rr :ok) (eq dr :ok) (eq sr :ok)
            (not (fn2-core-stopped-p fn2-core))) fn2-core)))

(defun fn2-phe-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core) (fn2-phe-body fn2-core) answer)))
(assert-event (fn2-phe-test))
