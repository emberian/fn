; The ordinary :closing arm issues a second descriptor before either
; terminal arrives. Exercise the generated arm against an actual queued
; Connect, then check the descriptor-budget refusal on the same source.
(in-package "ACL2")
(include-book "../books/peer-pull-plan")
(include-book "../books/machines-a-costs")

(make-event
 (mv-let (errs conts runs)
  (fn2-arms-arms 'fn2-peer-pull
    (list (assoc-eq :closing (fn2-machine-declared 'fn2-peer-pull :arms (w state))))
    nil nil nil nil nil :children (w state) nil)
  (declare (ignore conts))
  (if errs (er soft 'fn2-pull-closing "~x0" errs)
    (value (cons 'progn runs)))))

(defun fn2-pull-actual-cancel (enough fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control) :verify-guards nil))
 (b* ((fn2-peer-pull (fn2-peer-pull-init 1 fn2-peer-pull))
      (fn2-peer-pull (fn2-peer-pull-initialize-rows 1 1 0 7 fn2-peer-pull))
      (fn2-machines (fn2-machines-columns-init 1 fn2-machines))
      (fn2-machines (fn2-machines-put 0 (kind 6) (slot 0)))
      (fn2-pool (fn2-pool-init '((3 . 1024)) 1 100 fn2-pool))
      (fn2-ops (fn2-ops-init *fn2-profile-tiny* fn2-ops))
      (fn2-control (fn2-control-init *fn2-profile-tiny* fn2-control))
      ((mv conn target tg fn2-pool fn2-ops fn2-control)
       (fn2-issue-connect *fn2-peer-family-inet* 119 2130706433 0 0 0 6 0 7 1 fn2-pool fn2-ops fn2-control))
      (fn2-peer-pull (fn2-peer-pull-put 0 (phase *fn2-peer-pull-state-closing*)
                                       (pending 1) (op target) (op-gen tg)))
      ((mv & & descriptors & fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control)
       (fn2-peer-pull-run-closing-children 0 0 6 0 (if enough 100 0)
          fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control))
      (c (fn2-ops-out-sloti 1 fn2-ops)))
   (mv (and (eq conn :ok) (equal (fn2-control-stop fn2-control) 0)
            (if enough (and (equal descriptors 1) (equal (fn2-ops-queued fn2-ops) 2)
                             (equal (fn2-ops-kind c fn2-ops) *fn2-action-cancel*)
                             (equal (fn2-ops-cancel-slot c fn2-ops) target)
                             (equal (fn2-ops-cancel-gen c fn2-ops) tg)
                             (equal (fn2-peer-pull-pending 0 fn2-peer-pull) 2))
              (and (equal descriptors 0) (equal (fn2-ops-queued fn2-ops) 1)
                   (equal (fn2-peer-pull-pending 0 fn2-peer-pull) 1))))
       fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control)))

(defun fn2-pull-actual-cancel-test (enough)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-peer-pull
  (mv-let (ok fn2-peer-pull)
   (with-local-stobj fn2-machines
    (mv-let (ok fn2-peer-pull fn2-machines)
     (with-local-stobj fn2-pool
      (mv-let (ok fn2-peer-pull fn2-machines fn2-pool)
       (with-local-stobj fn2-ops
        (mv-let (ok fn2-peer-pull fn2-machines fn2-pool fn2-ops)
         (with-local-stobj fn2-control
          (mv-let (ok fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control)
           (fn2-pull-actual-cancel enough fn2-peer-pull fn2-machines fn2-pool fn2-ops fn2-control)
           (mv ok fn2-peer-pull fn2-machines fn2-pool fn2-ops)))
         (mv ok fn2-peer-pull fn2-machines fn2-pool)))
       (mv ok fn2-peer-pull fn2-machines)))
     (mv ok fn2-peer-pull)))
   ok)))

(assert-event (fn2-pull-actual-cancel-test t))
(assert-event (fn2-pull-actual-cancel-test nil))
