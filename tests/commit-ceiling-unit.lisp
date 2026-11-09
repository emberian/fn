; The journal-only commit ceiling, measured. N separate one-member keyed
; batches (fn2-commit-admit-keyed, okind 0) each run to a drained row
; through the executor's turn (fn2-turn via fn2-b-turn) and the simulated
; device (no faults); then batch N+1 is attempted. The record per profile:
; how many batches finished, admission's answer for the next one, the root
; frontiers (proposed, installed, published, root rows), the allocator's
; totals, the extents carrying an installed-root edge, the commit rows'
; phases, the free 4 KiB workspaces, and fn2-alloc-reserve's answer on the
; exhausted state. This measures the bound; it does not change it.
; Run: tools/box_certify_bb2.sh commit-ceiling -j 8 tests/commit-ceiling-unit.lisp
(in-package "ACL2")
(include-book "../sim/check-recovery")
(include-book "../sim/commit-history")
(include-book "../books/node-profile")
(include-book "std/util/bstar" :dir :system)

(local (defthm fn2-ccu-countdown
 (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left))) :rule-classes nil))
(local (defthm fn2-ccu-count-op (o-p (nfix left)) :rule-classes nil))

; One adapter action or one executor turn per step until row ID is :free with
; nothing queued, in flight or posted: :done, :stop (the core stopped),
; :stuck (an idle turn changed nothing) or :fuel.
(defun fn2-ccu-drive (fuel id fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)
  :hints (("Goal" :use ((:instance fn2-ccu-countdown (left fuel)) (:instance fn2-ccu-count-op (left fuel))) :in-theory nil))))
 (b* (((when (zp fuel)) (mv :fuel fn2-core fn2-sim fn2-own))
      ((when (= 1 (fn2-exec-stop fn2-core))) (mv :stop fn2-core fn2-sim fn2-own))
      (posted (fn2-b-rec-posted fn2-core))
      (outbox (consp (fn2-b-outbox fn2-core)))
      (flight (fn2-b-rec-flight (fn2-sim-rows fn2-sim) fn2-sim))
      ((when (and (= (fn2-machine-phase id fn2-core) *fn2-commit-state-free*)
                  (not posted) (not outbox) (not flight)))
       (mv :done fn2-core fn2-sim fn2-own)))
  (cond
   ((and (not posted) outbox)
    (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix 1 0 fn2-core fn2-sim fn2-own)))
     (fn2-ccu-drive (- fuel 1) id fn2-core fn2-sim fn2-own)))
   ((and (not posted) flight)
    (b* ((fn2-sim (fn2-sim-clock (fn2-sim-due flight fn2-sim) *fn2-fault-none* fn2-sim))
         (fn2-sim (fn2-sim-environment flight *fn2-fault-none* 1 fn2-sim))
         ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-complete flight *fn2-fault-none* 1 fn2-core fn2-sim fn2-own)))
     (fn2-ccu-drive (- fuel 1) id fn2-core fn2-sim fn2-own)))
   (t (b* ((before (fn2-machine-phase id fn2-core))
           ((mv status & fn2-core) (fn2-b-turn fn2-core)))
       (if (and (not posted) (eq status :idle) (= before (fn2-machine-phase id fn2-core))
                (not (consp (fn2-b-outbox fn2-core))))
           (mv :stuck fn2-core fn2-sim fn2-own)
         (fn2-ccu-drive (- fuel 1) id fn2-core fn2-sim fn2-own)))))))

(defun fn2-ccu-frontiers (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (f)
  (list :proposed (fn2-commit-root-proposed 0 fn2-commit-root)
        :installed (fn2-commit-root-installed 0 fn2-commit-root)
        :published (fn2-commit-root-published 0 fn2-commit-root)
        :root-rows (fn2-commit-root-rows fn2-commit-root)) f))

; Extents carrying an installed-root edge, and the sum of those edges.
(defun fn2-ccu-installed (n fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil :measure (nfix n)))
 (if (zp n) (mv 0 0)
  (mv-let (k sum) (fn2-ccu-installed (- n 1) fn2-extents)
   (let ((c (nfix (fn2-extents-installed-root (- n 1) fn2-extents))))
    (mv (if (< 0 c) (+ 1 k) k) (+ c sum))))))
; Extents allocated to the commit kind (the journal's), by owner kind.
(defun fn2-ccu-owned (n kind fn2-extents)
 (declare (xargs :stobjs fn2-extents :verify-guards nil :measure (nfix n)))
 (if (zp n) 0
  (+ (if (and (equal (fn2-extents-state (- n 1) fn2-extents) *fn2-extent-state-allocated*)
              (equal (fn2-extents-owner-kind (- n 1) fn2-extents) kind)) 1 0)
     (fn2-ccu-owned (- n 1) kind fn2-extents))))

(defun fn2-ccu-allocator (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (r)
  (mv-let (rows edges) (fn2-ccu-installed (fn2-extents-rows fn2-extents) fn2-extents)
   (list :extents (fn2-extents-rows fn2-extents)
         :free (fn2-alloc-total-free fn2-extents) :reserved (fn2-alloc-total-reserved fn2-extents)
         :allocated (fn2-alloc-total-allocated fn2-extents) :retired (fn2-alloc-total-retired fn2-extents)
         :commit-owned (fn2-ccu-owned (fn2-extents-rows fn2-extents) *fn2-commit-kind* fn2-extents)
         :installed-root-extents rows :installed-root-edges edges
         :pressure (fn2-alloc-pressure fn2-extents)))
  r))

(defun fn2-ccu-free-4k (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
  (count) (fn2-pool-free-count (fn2-pool-class-for 4096 fn2-pool) fn2-pool) count))

(defun fn2-ccu-rows (a b fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (list :phases (list (fn2-machine-phase a fn2-core) (fn2-machine-phase b fn2-core))
       :free-4k (fn2-ccu-free-4k fn2-core)
       :outbox (len (fn2-b-outbox fn2-core))
       :stop (fn2-stop-reason-code->keyword (fn2-core-stop-reason fn2-core))))

; Admit one-member keyed batches and drive each to a drained row, at most
; LEFT of them. (mv finished answer free fn2-core fn2-sim fn2-own): ANSWER
; is the first admission that did not answer :ok, or the drive status that
; ended the run; FREE the free 4 KiB workspaces after each batch, newest first.
(defun fn2-ccu-batches (left finished free fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix left)
  :hints (("Goal" :use (fn2-ccu-countdown fn2-ccu-count-op) :in-theory nil))))
 (if (zp left) (mv finished :left free fn2-core fn2-sim fn2-own)
  (b* (((mv & & & mode) (fn2-commit-frontier fn2-core))
       ((mv code id & & fn2-core) (fn2-commit-admit-keyed 1 mode 0 0 0 fn2-core))
       ((unless (eq code :ok)) (mv finished code free fn2-core fn2-sim fn2-own))
       (fn2-core (fn2-exec-wake id fn2-core))
       ((mv drive fn2-core fn2-sim fn2-own) (fn2-ccu-drive 20000 id fn2-core fn2-sim fn2-own))
       ((unless (eq drive :done)) (mv finished (list :drive drive id) free fn2-core fn2-sim fn2-own)))
   (fn2-ccu-batches (- left 1) (+ 1 (nfix finished)) (cons (fn2-ccu-free-4k fn2-core) free)
                    fn2-core fn2-sim fn2-own))))

;; The device spans every extent the profile's allocator can name, as
;; sim/session.lisp's *fn2-ss-sim-profile* does. The small profile is B's
;; commit fixture (fn2-b-test-profile of tiny: a 4 KiB pool class added,
;; since tiny has none) at SLOTS extents; the node profile is taken as is.
(defun fn2-ccu-sectors (profile)
 (declare (xargs :verify-guards nil))
 (put-assoc-equal :sim-sectors
  (ceiling (* (fn2-b-capacity :extent-slots 16 profile) *fn2-commit-extent-bytes*) *fn2-format-sector-bytes*)
  profile))
(defun fn2-ccu-small-profile (slots)
 (declare (xargs :verify-guards nil))
 (fn2-b-test-profile (fn2-ccu-sectors (put-assoc-equal :extent-slots slots *fn2-profile-tiny*)) 0))
(defconst *fn2-ccu-node-profile* (fn2-ccu-sectors *fn2-node-profile*))

(defun fn2-ccu-case (profile limit fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor profile :null nil fn2-core))
      ((mv epoch fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      (fn2-sim (fn2-sim-init 20261109 :none "commit-ceiling" profile fn2-sim))
      (fn2-own (fn2-own-init profile fn2-own))
      (before (list (fn2-ccu-allocator fn2-core) (fn2-ccu-rows a b fn2-core)))
      ((mv finished answer free fn2-core fn2-sim fn2-own) (fn2-ccu-batches limit 0 nil fn2-core fn2-sim fn2-own))
      (frontiers (fn2-ccu-frontiers fn2-core))
      (allocator (fn2-ccu-allocator fn2-core))
      (rows (fn2-ccu-rows a b fn2-core))
      ; The allocator asked directly on the exhausted state: whether the
      ; root-capacity refusal masks an allocator refusal.
      ((mv reserve pressure fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code pressure fn2-extents)
        (mv-let (code pressure e ep c fn2-extents) (fn2-alloc-reserve fn2-extents)
         (declare (ignore e ep c)) (mv code pressure fn2-extents))
        (mv code pressure fn2-core))))
  (mv (list :epoch epoch :extent-slots (fn2-b-capacity :extent-slots 16 profile)
            :finished finished :next answer :frontiers frontiers
            :allocator allocator :rows rows :reserve reserve :reserve-pressure pressure
            :free-4k-per-batch (reverse free) :before before)
      fn2-core fn2-sim fn2-own)))

(defun fn2-ccu-run (profile limit)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (with-local-stobj fn2-sim
    (mv-let (answer fn2-core fn2-sim)
     (with-local-stobj fn2-own
      (mv-let (answer fn2-core fn2-sim fn2-own) (fn2-ccu-case profile limit fn2-core fn2-sim fn2-own)
       (mv answer fn2-core fn2-sim)))
     (mv answer fn2-core)))
   answer)))

;; N is the profile's :extent-slots: batch N+1 is refused :exhausted by the
;; root directory (N+1 rows indexed by absolute batch number), and the
;; allocator under it is already all-live (every extent a journal batch's,
;; each pinned by one installed-root edge), so its own answer is :no-space.
;; Every row drained: both commit rows :free, the outbox empty, no stop, and
;; the free 4 KiB workspaces the same after every batch (the node profile's
;; init holds two of its 16 KiB class, one released during the first batch:
;; not the commit kind's; a commit leak would lower the count batch by batch).
(defun fn2-ccu-expected (n r)
 (declare (xargs :verify-guards nil))
 (let ((before (cadr (member-eq :before r))))
  (and (equal (cadr (member-eq :epoch r)) :ok)
       (equal (cadr (member-eq :extent-slots r)) n)
       (equal (cadr (member-eq :finished r)) n)
       (equal (cadr (member-eq :next r)) :exhausted)
       (equal (cadr (member-eq :frontiers r)) (list :proposed n :installed n :published n :root-rows (+ 1 n)))
       (equal (cadr (member-eq :allocator r))
              (list :extents n :free 0 :reserved 0 :allocated n :retired 0 :commit-owned n
                    :installed-root-extents n :installed-root-edges n :pressure :all-live))
       (equal (car before)
              (list :extents n :free n :reserved 0 :allocated 0 :retired 0 :commit-owned 0
                    :installed-root-extents 0 :installed-root-edges 0 :pressure :ok))
       (let ((rows (cadr (member-eq :rows r))) (free (cadr (member-eq :free-4k-per-batch r))))
        (and (equal (cadr (member-eq :phases rows)) (list *fn2-commit-state-free* *fn2-commit-state-free*))
             (equal (cadr (member-eq :outbox rows)) 0)
             (equal (cadr (member-eq :stop rows)) :none)
             (equal (len free) n)
             (equal free (make-list n :initial-element (cadr (member-eq :free-4k rows))))
             (<= (cadr (member-eq :free-4k (cadr before))) (car free))))
       (equal (cadr (member-eq :reserve r)) :no-space)
       (equal (cadr (member-eq :reserve-pressure r)) :all-live))))

(make-event `(defconst *fn2-ccu-small* ',(fn2-ccu-run (fn2-ccu-small-profile 16) 64)))
(make-event `(defconst *fn2-ccu-small-5* ',(fn2-ccu-run (fn2-ccu-small-profile 5) 64)))
(make-event `(defconst *fn2-ccu-node* ',(fn2-ccu-run *fn2-ccu-node-profile* 512)))
(value-triple (cw "COMMIT-CEILING small ~x0~%COMMIT-CEILING small-5 ~x1~%COMMIT-CEILING node ~x2~%"
                  *fn2-ccu-small* *fn2-ccu-small-5* *fn2-ccu-node*))
(assert-event (fn2-ccu-expected 16 *fn2-ccu-small*))
(assert-event (fn2-ccu-expected 5 *fn2-ccu-small-5*))
(assert-event (fn2-ccu-expected 128 *fn2-ccu-node*))
;; teeth: the check refuses the run read as one batch short, a next answer
;; other than :exhausted, and an installed-root edge fewer
(defun fn2-ccu-set (key value plist)
 (declare (xargs :verify-guards nil))
 (cond ((atom plist) nil)
       ((eq (car plist) key) (list* key value (cddr plist)))
       (t (list* (car plist) (cadr plist) (fn2-ccu-set key value (cddr plist))))))
(assert-event (not (fn2-ccu-expected 15 *fn2-ccu-small*)))
(assert-event (not (fn2-ccu-expected 16 (fn2-ccu-set :next :no-space *fn2-ccu-small*))))
(assert-event (not (fn2-ccu-expected 16
 (fn2-ccu-set :allocator (fn2-ccu-set :installed-root-edges 15 (cadr (member-eq :allocator *fn2-ccu-small*)))
  *fn2-ccu-small*))))
