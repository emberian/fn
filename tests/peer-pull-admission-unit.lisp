; Exercise the generated pull reservation on its four actual child tables.
(in-package "ACL2")
(include-book "../books/peer-pull-kind")

(defun fn2-pull-take-control (enough fn2-peer-pull fn2-machines fn2-pool fn2-control)
 (declare (xargs :stobjs (fn2-peer-pull fn2-machines fn2-pool fn2-control) :verify-guards nil))
 (b* ((fn2-peer-pull (fn2-peer-pull-init 1 fn2-peer-pull))
      (fn2-peer-pull (fn2-peer-pull-initialize-rows 1 1 0 7 fn2-peer-pull))
      (fn2-machines (fn2-machines-columns-init 1 fn2-machines))
      (fn2-machines (fn2-machines-put 0 (kind 6) (slot 0)))
      (fn2-machines (update-fn2-machines-connection-counti 0 1 fn2-machines))
      (fn2-machines (update-fn2-machines-admission-creditsi 0 1 fn2-machines))
      (fn2-machines (update-fn2-machines-free-headi 0 0 fn2-machines))
      (fn2-control (fn2-control-init *fn2-profile-tiny* fn2-control))
      (fn2-pool (fn2-pool-init (list (cons (if enough 3 2) 1024)) 1 100 fn2-pool))
      ((mv code id gen fn2-peer-pull fn2-machines fn2-pool fn2-control)
       (fn2-machine-take-fn2-peer-pull-children *fn2-none* 12 3 1 1 77 10 5
        20 2 3 1 *fn2-peer-family-inet* 119 2130706433 0 0 0 1000 0 6
        fn2-peer-pull fn2-machines fn2-pool fn2-control))
      (rx (fn2-peer-pull-rx-slot 0 fn2-peer-pull)) (tx (fn2-peer-pull-tx-slot 0 fn2-peer-pull))
      (private (fn2-peer-pull-secret-slot 0 fn2-peer-pull)))
   (mv
    (and (equal (fn2-control-stop fn2-control) 0)
         (if enough
             (and (eq code :ok) (equal id 0) (equal gen 7)
                  (equal (fn2-peer-pull-phase 0 fn2-peer-pull) *fn2-peer-pull-state-stage*)
                  (equal (fn2-peer-pull-ctl-gen 0 fn2-peer-pull) 3)
                  (equal (fn2-peer-pull-remote-view 0 fn2-peer-pull) 3)
                  (equal (fn2-peer-pull-consumer 0 fn2-peer-pull) 5)
                  (not (equal rx tx)) (not (equal tx private)) (not (equal rx private))
                  (eq (fn2-pool-workspace-code rx (fn2-peer-pull-rx-gen 0 fn2-peer-pull) 6 id gen fn2-pool) :ok)
                  (eq (fn2-pool-workspace-code tx (fn2-peer-pull-tx-gen 0 fn2-peer-pull) 6 id gen fn2-pool) :ok)
                  (eq (fn2-pool-workspace-code private (fn2-peer-pull-secret-gen 0 fn2-peer-pull) 6 id gen fn2-pool) :ok)
                  (equal (fn2-pool-class-countsi 0 fn2-pool) 0)
                  (equal (fn2-machines-active-counti 0 fn2-machines) 1)
                  (equal (fn2-machines-admission-creditsi 0 fn2-machines) 0)
                  (equal (fn2-machines-wake-id fn2-machines) id))
           (and (eq code :pool) (equal id *fn2-none*) (equal gen 0)
                (equal (fn2-pool-class-countsi 0 fn2-pool) 2)
                (equal (fn2-peer-pull-phase 0 fn2-peer-pull) *fn2-peer-pull-state-free*)
                (equal (fn2-machines-active-counti 0 fn2-machines) 0)
                (equal (fn2-machines-admission-creditsi 0 fn2-machines) 1)
                (equal (fn2-machines-free-headi 0 fn2-machines) 0))))
    fn2-peer-pull fn2-machines fn2-pool fn2-control)))

(defun fn2-pull-take-test (enough)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-peer-pull
  (mv-let (ok fn2-peer-pull)
   (with-local-stobj fn2-machines
    (mv-let (ok fn2-peer-pull fn2-machines)
     (with-local-stobj fn2-pool
      (mv-let (ok fn2-peer-pull fn2-machines fn2-pool)
       (with-local-stobj fn2-control
        (mv-let (ok fn2-peer-pull fn2-machines fn2-pool fn2-control)
         (fn2-pull-take-control enough fn2-peer-pull fn2-machines fn2-pool fn2-control)
         (mv ok fn2-peer-pull fn2-machines fn2-pool)))
       (mv ok fn2-peer-pull fn2-machines)))
     (mv ok fn2-peer-pull)))
   ok)))

(assert-event (fn2-pull-take-test t))
(assert-event (fn2-pull-take-test nil))
