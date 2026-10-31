; Layer C1c: the sealer machine in the served core (machines-c-sealer.lisp).
; The real executor over the tiny profile with a group directory: genesis
; publishes the groups overlay (frozen) and leaves the sealer's row parked
; on :sealable; the grant service's fifth source wakes it, its :sealing arm
; seals the overlay into a run through the engine (one 64 KiB page under the
; sealer's row as owner) and installs it, retiring the overlay; the row
; parks again. Every group then answers through the run leg of the lookup.
; Without the checker row 3 + :large-upload-windows in the profile
; (C-SEAL-NO-ROW, until B5-4a) the row is stopped and the overlay stays.
; Backpressure has no wake until M2's eviction, so it stops the core by
; name instead of parking the row (controls at the end): no 256-byte slot
; for the hash workspace at the pick (:sealer-full), no 64 KiB page
; workspace in the build (:sealer-full), every cache row held by another
; page (:sealer-cache), no free installed-run row at install
; (:sealer-full).
; Run: sh fn2/tools/certify.sh tests/sealer-machine-unit.lisp
(in-package "ACL2")
(include-book "../books/executor")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-smu-groups* '(("comp.lang.lisp" . 7) ("alt.test" . 9) ("misc.misc" . 11)))
;; :format-slots is derived (B5-4a: 4 + the windows), so the checker row
;; 3 + windows exists in every profile.
(defconst *fn2-smu-profile*
 (put-assoc-equal :groups *fn2-smu-groups*
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :large-upload-windows 1
     (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096) (4 . 65536)) *fn2-profile-tiny*)))))
(defconst *fn2-smu-norow*
 (put-assoc-equal :groups *fn2-smu-groups*
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096) (4 . 65536)) *fn2-profile-tiny*))))

(defun fn2-smu-turns (n fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp n) fn2-core
  (mv-let (status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)
   (declare (ignore nobs nvisits nactions))
   (if (eq status :stop) fn2-core (fn2-smu-turns (- n 1) fn2-core)))))
;; (schema run entries filter) of each live run; the overlay phases.
(defun fn2-smu-runs (r k fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
 (if (zp k) nil
  (let ((row (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core)))
              (v) (if (< (nfix r) (fn2-run-installed-rows fn2-run-installed))
                      (and (equal (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-live*)
                           (list (fn2-run-installed-schema r fn2-run-installed) (fn2-run-installed-run r fn2-run-installed)
                                 (fn2-run-installed-entries r fn2-run-installed) (fn2-run-installed-filter r fn2-run-installed)))
                    :end)
              v)))
   (cond ((eq row :end) nil) (row (cons row (fn2-smu-runs (+ 1 (nfix r)) (- k 1) fn2-core)))
         (t (fn2-smu-runs (+ 1 (nfix r)) (- k 1) fn2-core))))))
(defun fn2-smu-phases (o k fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
 (if (zp k) nil
  (let ((p (stobj-let ((fn2-overlays (fn2-core-overlays fn2-core)))
            (v) (if (< (nfix o) (fn2-overlays-rows fn2-overlays)) (fn2-overlays-phase o fn2-overlays) :end) v)))
   (if (eq p :end) nil (cons p (fn2-smu-phases (+ 1 (nfix o)) (- k 1) fn2-core))))))
(defun fn2-smu-row (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core)))
  (list (fn2-machine-phase id fn2-core) (fn2-machine-wait-reason id fn2-core))))
;; Look a group up through the transaction-0 lookup until it answers.
(defun fn2-smu-write (bytes slot gen off fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
   (if (eq code :ok) (fn2-smu-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-smu-drive (fuel slot gen len fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (code group fn2-core) (fn2-group-lookup 0 slot gen 0 len 5 1 1 4096 fn2-core)
   (if (eq code :more) (fn2-smu-drive (- fuel 1) slot gen len fn2-core) (mv code group fn2-core)))))
(defun fn2-smu-chars (cs) (declare (xargs :verify-guards nil)) (if (atom cs) nil (cons (char-code (car cs)) (fn2-smu-chars (cdr cs)))))
(defun fn2-smu-lookup (name fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      (octets (fn2-smu-chars (coerce name 'list)))
      ((mv & fn2-core) (fn2-smu-write octets slot gen 0 fn2-core))
      ((mv code group fn2-core) (fn2-smu-drive 40 slot gen (len octets) fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core)))
  (mv (list code group) fn2-core)))

(defun fn2-smu-run (profile n fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor profile :null nil fn2-core))
      (before (list (fn2-smu-runs 0 64 fn2-core) (fn2-smu-phases 0 1 fn2-core) (fn2-smu-row fn2-core)))
      (fn2-core (fn2-smu-turns n fn2-core))
      (after (list (fn2-smu-runs 0 64 fn2-core) (fn2-smu-phases 0 1 fn2-core) (fn2-smu-row fn2-core)
                   (fn2-exec-status fn2-core) (fn2-core-stop-reason fn2-core)))
      ((mv l1 fn2-core) (fn2-smu-lookup "comp.lang.lisp" fn2-core))
      ((mv l2 fn2-core) (fn2-smu-lookup "misc.misc" fn2-core))
      ((mv l3 fn2-core) (fn2-smu-lookup "alt.tests" fn2-core)))
  (mv (list before after (list l1 l2 l3)) fn2-core)))
(defun fn2-smu-result (profile n)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-smu-run profile n fn2-core) r)))

(assert-event (equal *fn2-sealer-kind* *fn2-idc-owner-kind*))
;; With the checker row: before, no run, the groups overlay frozen, the row
;; parked on :sealable; after, one groups run of three entries (no filter),
;; the overlay free, the row parked again, the executor idle and nothing
;; stopped; the lookups
;; answer from the run. (Evaluated in assert-event, not defconst: the grant
;; source's attachment is ignored in a defconst's evaluation.)
(defun fn2-smu-check (got want)
 (declare (xargs :verify-guards nil))
 (or (equal got want) (cw "sealer machine: got ~x0~%" got)))
(assert-event
 (fn2-smu-check (fn2-smu-result *fn2-smu-profile* 400)
                `((nil (,*fn2-overlay-phase-frozen*) (,*fn2-sealer-state-sealing* ,*fn2-wait-sealable*))
                  (((8 1 3 0)) (,*fn2-overlay-phase-free*) (,*fn2-sealer-state-sealing* ,*fn2-wait-sealable*) :idle ,*fn2-stop-reason-none*)
                  ((:ok 7) (:ok 11) (:absent 0)))))
;; The row cannot be missing: the default windows (16) give 20 format slots,
;; and a profile naming fewer slots than 4 + windows is refused.
(assert-event
 (and (equal (fn2-b-format-slots *fn2-smu-norow*) 20)
      (equal (fn2-b-format-slots *fn2-smu-profile*) 5)
      (fn2-core-profilep *fn2-smu-profile*)
      (not (fn2-core-profilep (put-assoc-equal :format-slots 4 *fn2-smu-profile*)))))

;; Backpressure controls. After genesis, take away one resource, then run:
;; the core stops with the named reason, the sealer's row is :stopped and
;; the groups overlay is not retired (frozen).
(defun fn2-smu-exhaust (fuel class fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) fn2-core
  (mv-let (code slot gen fn2-core) (fn2-core-reserve class 5 1 1 fn2-core)
   (declare (ignore slot gen))
   (if (eq code :ok) (fn2-smu-exhaust (- fuel 1) class fn2-core) fn2-core))))
(defun fn2-smu-hold-cache (i n fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
 (if (>= (nfix i) (nfix n)) fn2-core
  (let ((fn2-core (stobj-let ((fn2-run-cache (fn2-core-run-cache fn2-core)))
                   (fn2-run-cache)
                   (if (< (nfix i) (fn2-run-cache-rows fn2-run-cache))
                       (fn2-run-cache-put (nfix i) (state *fn2-run-cache-state-ready*) (unit 999999))
                     fn2-run-cache)
                   fn2-core)))
   (fn2-smu-hold-cache (+ 1 (nfix i)) n fn2-core))))
(defun fn2-smu-hold-runs (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-run-installed (fn2-core-run-installed fn2-core)))
  (fn2-run-installed)
  (if (< 0 (fn2-run-installed-rows fn2-run-installed))
      (fn2-run-installed-put 0 (state *fn2-run-installed-state-live*) (schema 99) (run 999999))
    fn2-run-installed)
  fn2-core))
(defun fn2-smu-pressure (what profile fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor profile :null nil fn2-core))
      (fn2-core (case what
                  (:hash (fn2-smu-exhaust 64 1 fn2-core))
                  (:page (fn2-smu-exhaust 64 3 fn2-core))
                  (:cache (fn2-smu-hold-cache 0 2 fn2-core))
                  (otherwise (fn2-smu-hold-runs fn2-core))))
      (fn2-core (fn2-smu-turns 400 fn2-core)))
  (mv (list (fn2-exec-status fn2-core) (fn2-core-stop-reason fn2-core) (car (fn2-smu-row fn2-core))
            (fn2-smu-phases 0 1 fn2-core))
      fn2-core)))
(defun fn2-smu-pressure-result (what profile)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-smu-pressure what profile fn2-core) r)))
(defconst *fn2-smu-small*
 (put-assoc-equal :run-cache 2 (put-assoc-equal :identity-runs 1 *fn2-smu-profile*)))
(assert-event
 (fn2-smu-check (list (fn2-smu-pressure-result :hash *fn2-smu-profile*)
                      (fn2-smu-pressure-result :page *fn2-smu-profile*)
                      (fn2-smu-pressure-result :cache *fn2-smu-small*)
                      (fn2-smu-pressure-result :runs *fn2-smu-small*))
                `((:stop ,*fn2-stop-reason-sealer-full* ,*fn2-sealer-state-stopped* (,*fn2-overlay-phase-frozen*))
                  (:stop ,*fn2-stop-reason-sealer-full* ,*fn2-sealer-state-stopped* (,*fn2-overlay-phase-frozen*))
                  (:stop ,*fn2-stop-reason-sealer-cache* ,*fn2-sealer-state-stopped* (,*fn2-overlay-phase-frozen*))
                  (:stop ,*fn2-stop-reason-sealer-full* ,*fn2-sealer-state-stopped* (,*fn2-overlay-phase-frozen*)))))
;; The small profile without the pressure still seals (the controls' teeth).
(assert-event
 (fn2-smu-check (cadr (fn2-smu-result *fn2-smu-small* 400))
                `(((8 1 3 0)) (,*fn2-overlay-phase-free*) (,*fn2-sealer-state-sealing* ,*fn2-wait-sealable*) :idle ,*fn2-stop-reason-none*)))
