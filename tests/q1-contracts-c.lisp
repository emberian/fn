; Q1's honest classification for layer C's kinds (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 3): the independent contract of fn2-sealer. The served core, from genesis with a group
; directory, seals the groups overlay into a run and retires it. The oracle reads the resident view
; after every turn (the installed runs and the overlay phases, as C's fn2-manifest-replacement-atomic
; reads them at every cut of the engine) and the answers of the group lookup through the run leg,
; against the profile's own directory (C's fn2-sealer-run-equals-overlay: every lookup answers as the
; overlay did). Nothing on the checking side calls a sealer handler; the views and the lookup are
; tests/sealer-machine-unit's readers.
(in-package "ACL2")
(include-book "sealer-machine-unit")

(defun fn2-q1s-profile (groups)
  (declare (xargs :verify-guards nil))
  (put-assoc-equal :groups groups *fn2-smu-profile*))
(defun fn2-q1s-view (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (list (fn2-smu-runs 0 64 fn2-core) (fn2-smu-phases 0 1 fn2-core)))
; Turns, recording the resident view whenever it changes (newest first).
(defun fn2-q1s-turns (n views fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv views fn2-core)
    (mv-let (status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)
      (declare (ignore nobs nvisits nactions))
      (let* ((view (fn2-q1s-view fn2-core))
             (views (if (equal view (car views)) views (cons view views))))
        (if (eq status :stop) (mv views fn2-core) (fn2-q1s-turns (- n 1) views fn2-core))))))
(defun fn2-q1s-lookups (names fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom names) (mv nil fn2-core)
    (mv-let (answer fn2-core) (fn2-smu-lookup (car names) fn2-core)
      (mv-let (rest fn2-core) (fn2-q1s-lookups (cdr names) fn2-core)
        (mv (cons answer rest) fn2-core)))))
; (views row status stop answers) for the directory GROUPS and the lookups of NAMES.
(defun fn2-sealer-served (groups names)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor (fn2-q1s-profile groups) :null nil fn2-core))
           ((mv views fn2-core) (fn2-q1s-turns 400 (list (fn2-q1s-view fn2-core)) fn2-core))
           (row (fn2-smu-row fn2-core)) (status (fn2-exec-status fn2-core)) (stop (fn2-core-stop-reason fn2-core))
           ((mv answers fn2-core) (fn2-q1s-lookups names fn2-core)))
        (mv (list (reverse views) row status stop answers) fn2-core))
      result)))
; The directory's own answer for NAME (the overlay's: its number, or absent).
(defun fn2-q1s-spec (names groups)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (let ((g (assoc-equal (car names) groups))) (if g (list :ok (cdr g)) (list :absent 0)))
          (fn2-q1s-spec (cdr names) groups))))
(defun fn2-q1s-names (groups) (declare (xargs :verify-guards nil)) (append (strip-cars groups) (list "no.such.group")))
; The views a seal of the groups overlay may show: before (no run, the overlay frozen) and after
; (one groups run, schema 8, run 1, its N entries, no filter; the overlay free); nothing else.
(defun fn2-q1s-views-ok (views n)
  (declare (xargs :verify-guards nil))
  (equal views (list (list nil (list *fn2-overlay-phase-frozen*))
                     (list (list (list 8 1 n 0)) (list *fn2-overlay-phase-free*)))))
(defun fn2-q1s-result-ok (r groups)
  (declare (xargs :verify-guards nil))
  (and (fn2-q1s-views-ok (nth 0 r) (len groups))
       (equal (nth 1 r) (list *fn2-sealer-state-sealing* *fn2-wait-sealable*))
       (equal (nth 2 r) :idle) (equal (nth 3 r) *fn2-stop-reason-none*)
       (equal (nth 4 r) (fn2-q1s-spec (fn2-q1s-names groups) groups))))
(defun fn2-q1s-ok (groups)
  (declare (xargs :verify-guards nil))
  (fn2-q1s-result-ok (fn2-sealer-served groups (fn2-q1s-names groups)) groups))
(defconst *fn2-q1s-directories*
  (list *fn2-smu-groups*
        '(("local.test" . 1))
        '(("a.one" . 2) ("b.two" . 3) ("c.three" . 5) ("d.four" . 8) ("e.five" . 13))))
(defthm-owed fn2-sealer-seals-the-directory (groups)
  (implies (member-equal groups *fn2-q1s-directories*)
           (fn2-q1s-ok groups))
  :schema :invariant :claim :semantic
  :teeth (fn2-sealer-seals-positive fn2-sealer-seals-negative)
  :doc "For each fixture group directory, the served core from genesis seals the groups overlay into one run of the directory's entries and retires the overlay with no turn showing both or neither; the sealer row parks on :sealable, the executor is idle and nothing stopped; every group lookup through the run answers as the directory does (its number; absent for a name not in it).")
(defun fn2-q1s-all (dirs)
  (declare (xargs :verify-guards nil))
  (or (atom dirs)
      (and (or (fn2-q1s-ok (car dirs))
               (cw "SEALER CONTRACT ~x0 FAIL ~x1~%" (car dirs) (fn2-sealer-served (car dirs) (fn2-q1s-names (car dirs)))))
           (fn2-q1s-all (cdr dirs)))))
; Positive: the three directories.
(defun fn2-sealer-seals-positive ()
  (declare (xargs :verify-guards nil))
  (fn2-q1s-all *fn2-q1s-directories*))
; Negative: the conclusion refuses a wrong seal: the unit directory's run seen beside its still
; frozen overlay (a fact in two places), a run one entry short, and a lookup answering a group's
; number for the absent name.
(defun fn2-sealer-seals-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((g *fn2-smu-groups*) (r (fn2-sealer-served g (fn2-q1s-names g)))
         (fr *fn2-overlay-phase-frozen*) (fe *fn2-overlay-phase-free*))
    (and (fn2-q1s-result-ok r g)
         (not (fn2-q1s-result-ok (update-nth 0 (list (list nil (list fr)) (list (list (list 8 1 3 0)) (list fr))
                                                     (list (list (list 8 1 3 0)) (list fe))) r) g))
         (not (fn2-q1s-result-ok (update-nth 0 (list (list nil (list fr)) (list (list (list 8 1 2 0)) (list fe))) r) g))
         (not (fn2-q1s-result-ok (update-nth 4 (update-nth 3 '(:ok 7) (nth 4 r)) r) g)))))

(fn2-assert-owed-teeth fn2-sealer-seals-the-directory)
(value-triple (cw "Q1 CONTRACTS C: sealer teeth PASS~%"))
