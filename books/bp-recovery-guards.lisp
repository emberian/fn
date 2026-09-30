; Guard composition for the actual recovery event called by fnn-bps-open.
; The replay refinement remains in bp-held-projection. No host input is
; whole-state revalidated to establish these execution prerequisites.
(in-package "ACL2")
(include-book "bp-held-projection")
(include-book "bp-node-fragment-guards")
(include-book "bp-node-progress-guards")

(local
 (defthm fn-bprg-nth-is-nth
  (implies (natp n) (equal (fn-bpn-nth n xs) (nth n xs)))
  :hints (("Goal" :induct (fn-bpn-nth n xs)
           :in-theory (enable fn-bpn-nth nth fn-cbor-ag-car)))))
(local
 (defthm fn-bprg-stored-values-recordp
  (implies (fn-bpnf-stored-from-values values)
           (fn-bpnf-stored-recordp (fn-bpnf-stored-from-values values)))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-stored-from-values) (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-stored-unframe-recordp
  (implies (fn-bpnf-stored-record-unframe octets)
           (fn-bpnf-stored-recordp (fn-bpnf-stored-record-unframe octets)))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-stored-record-unframe fn-bprg-stored-values-recordp)
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-stored-record-frontier
  (implies (fn-bpnf-stored-recordp record)
           (and (natp (fn-bpn-nth 1 record)) (natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bprg-nth-is-nth fn-bpnf-stored-recordp fn-frame-natp natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-delivery-frontier
  (let ((r (fn-bpah-delivery-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpah-delivery-unframe fn-bpah-delivery-from-values fn-bpah-delivery-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-delete-frontier
  (let ((r (fn-bpnf-delete-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-delete-unframe fn-bpnf-delete-from-values fn-bpn-report-delete-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-dispatch-frontier
  (let ((r (fn-bpnp-dispatch-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-dispatch-unframe fn-bpnp-dispatch-from-values fn-bpnp-dispatch-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-conflict-frontier
  (let ((r (fn-bpnf-conflict-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-conflict-unframe fn-bpnf-conflict-from-values fn-bpnf-conflict-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-attempt-frontier
  (let ((r (fn-bpnp-attempt-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-attempt-unframe fn-bpnp-attempt-from-values fn-bpnp-forward-attempt-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-result-frontier
  (let ((r (fn-bpnp-result-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-result-unframe fn-bpnp-result-from-values fn-bpnp-forward-result-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-deferral-frontier
  (let ((r (fn-bpnp-deferral-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-deferral-unframe fn-bpnp-deferral-from-values fn-bpnp-deferral-recordp
               fn-bprg-nth-is-nth fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-family-atp-frontier
  (implies (fn-bpnf-family-record-atp record)
           (and (natp (fn-bpn-nth 1 record)) (natp (fn-bpn-nth 2 record))))
  :hints (("Goal" :in-theory
           (e/d (fn-bpnf-family-record-atp fn-bpnf-family-recordp
                 fn-bpnf-family-record fn-frame-natp fn-bprg-nth-is-nth)
                (fn-cbor-octet-listp fn-clock-observationp))))))
(local
 (defthm fn-bprg-family-frontier
  (let ((r (fn-bpnf-family-replay-unframe octets)))
   (implies r (and (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-family-replay-unframe fn-bpnf-family-unframe fn-bpnf-family-v1-unframe fn-bpnf-family-from-values fn-bpnf-family-v1-from-values fn-bpnf-family-recordp fn-bprg-family-atp-frontier
               fn-frame-natp fn-bpn-machine-u64p natp (natp))
             (theory 'minimal-theory))))))

(local
 (defthm fn-bprg-row-record-has-frontier
  (let ((r (fn-bpnf-family-replay-row-record row)))
   (implies r
            (and (fn-bpnf-replay-rowp row)
                 (natp (fn-bpn-nth 1 r)) (natp (fn-bpn-nth 2 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-family-replay-row-record
               fn-bprg-stored-unframe-recordp fn-bprg-stored-record-frontier
               fn-bprg-delivery-frontier fn-bprg-delete-frontier
               fn-bprg-dispatch-frontier fn-bprg-conflict-frontier
               fn-bprg-attempt-frontier fn-bprg-result-frontier
               fn-bprg-deferral-frontier fn-bprg-family-frontier)
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-rowp-is-consp
  (implies (fn-bpnf-replay-rowp row) (consp row))
  :hints (("Goal" :expand ((len row))
           :in-theory (enable fn-bpnf-replay-rowp)))))

(local
 (defthm fn-bprg-held-octets-natural
  (natp (fn-bpnf-held-octets held))
  :hints (("Goal" :induct (fn-bpnf-held-octets held)
           :in-theory (enable fn-bpnf-held-octets)))
  :rule-classes (:rewrite :type-prescription)))

(local
 (defthm fn-bprg-delivery-not-stored
  (not (equal (car (fn-bpah-delivery-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpah-delivery-unframe fn-bpah-delivery-from-values fn-bpah-delivery-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-delete-not-stored
  (not (equal (car (fn-bpnf-delete-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-delete-unframe fn-bpnf-delete-from-values fn-bpn-report-delete-with-intent car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-dispatch-not-stored
  (not (equal (car (fn-bpnp-dispatch-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-dispatch-unframe fn-bpnp-dispatch-from-values fn-bpnp-dispatch-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-conflict-not-stored
  (not (equal (car (fn-bpnf-conflict-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-conflict-unframe fn-bpnf-conflict-from-values fn-bpnf-conflict-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-attempt-not-stored
  (not (equal (car (fn-bpnp-attempt-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-attempt-unframe fn-bpnp-attempt-from-values fn-bpnp-forward-attempt-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-result-not-stored
  (not (equal (car (fn-bpnp-result-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-result-unframe fn-bpnp-result-from-values fn-bpnp-forward-result-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-deferral-not-stored
  (not (equal (car (fn-bpnp-deferral-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnp-deferral-unframe fn-bpnp-deferral-from-values fn-bpnp-deferral-record car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-family-not-stored
  (not (equal (car (fn-bpnf-family-replay-unframe octets)) :bpnf-stored))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-family-replay-unframe fn-bpnf-family-unframe fn-bpnf-family-v1-unframe fn-bpnf-family-from-values fn-bpnf-family-v1-from-values fn-bpnf-family-record fn-bpnf-family-record-at car-cons (car))
             (theory 'minimal-theory))))))
(local
 (defthm fn-bprg-stored-row-has-bundle
  (let ((r (fn-bpnf-family-replay-row-record row)))
   (implies (equal (car r) :bpnf-stored)
            (fn-bpb-bundlep (fn-bpnf-held-bundle (fn-bpn-nth 3 r)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-bpnf-family-replay-row-record
               fn-bprg-stored-unframe-recordp
               fn-bpnf-stored-recordp-held-bundle-is-a-bundle
               fn-bprg-delivery-not-stored fn-bprg-delete-not-stored
               fn-bprg-dispatch-not-stored fn-bprg-conflict-not-stored
               fn-bprg-attempt-not-stored fn-bprg-result-not-stored
               fn-bprg-deferral-not-stored fn-bprg-family-not-stored (car))
             (theory 'minimal-theory))))))

(verify-guards fn-bphp-replay-rows
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-bprg-row-record-has-frontier (row (car rows)))
                (:instance fn-bprg-stored-row-has-bundle (row (car rows)))
                (:instance fn-bpn-state-field-types-for-guard (st base)))
          :in-theory
          (e/d (fn-bpnf-state fn-bpnf-state-with-arrival fn-bpnf-base
                fn-bpn-machine-limitp)
               (fn-bpn-machine-statep fn-bpn-machine-recordp
                fn-bpn-machine-state-max-jobs fn-bpn-machine-state-max-octets
                fn-bpnf-family-replay-row-record fn-bpnf-replay-rowp
                fn-bpnf-replay-pair-afterp fn-bpnf-stored-record-name
                fn-bpnf-receive-decision fn-bpah-apply-delivery
                fn-bpnf-family-apply-at fn-bpn-report-apply-delete
                fn-bpnp-dispatch-apply fn-bpnp-attempt-apply
                fn-bpnp-forward-result-apply fn-bpnp-deferral-apply
                fn-bpnf-conflict-apply fn-bpnf-held-octets
                fn-bpnf-held-wire fn-bpnf-held-bundle
                fn-bpnf-held-arrival-frontier)))))

(verify-guards fn-bphp-replay-from
 :hints (("Goal" :in-theory
          (union-theories
           '(fn-bpnr-checkpointp fn-bpnr-checkpoint-prior
             fn-bpnr-checkpoint-next-arrival fn-bprg-nth-is-nth
             (natp) null not)
           (theory 'minimal-theory)))))
(verify-guards fn-bphp-recover-auto-event
 :hints (("Goal" :in-theory
          (disable fn-bphp-replay-from fn-bpn-machine-statep))))
