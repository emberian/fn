; Named immutable launch coordinates beside the live capacity.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "defrecord")
(include-book "heap-command")
(include-book "runtime-contract-host-pool")
(fn-defrecord fn-menv
 :constructor (fn-menv-make resident output peer workers cache-limit root bp-terms core nursery)
 :fields ((fn-menv-resident t) (fn-menv-output t) (fn-menv-peer t) (fn-menv-workers t)
          (fn-menv-cache-limit t) (fn-menv-root t) (fn-menv-bp-terms t)
          (fn-menv-core t) (fn-menv-nursery t)))
(defun fn-adm-installed-lease-octets (profile cfg quantum)
 (declare (xargs :guard t))
 (let ((c (fn-hl-rtc-config profile cfg quantum 1 0 0)))
  (* (fn-rtc-npool c) (fn-rtc-capl c))))

; The slot/mstate arrays and buffer metadata are permanent too. Their
; original fixed connection term remains charged beside the octet bank.
(defun fn-adm-installed-lease-allocation (profile cfg quantum)
 (declare (xargs :guard t))
 (+ (fn-adm-installed-lease-octets profile cfg quantum)
    (* (fn-mm-cfg-connections cfg) (fn-mm-connection-fixed profile cfg))))

; The first search sizes the physical bank. Its allocation is a floor under
; the reader charge, which already covers that bank (HL4), never an addition.
(defun fn-adm-lease-startup-bank-cfg (profile img cfg limit tot)
  (declare (xargs :guard t))
  (let ((public (fn-adm-capacity profile img cfg limit tot)))
    (fn-adm-cfg-at cfg (if (natp public) (1+ public) 0))))

(defun fn-adm-lease-startup-cfg (profile img cfg limit tot quantum)
 (declare (xargs :guard t))
 (update-nth 14
  (if (natp quantum)
   (fn-adm-installed-lease-allocation profile
    (fn-adm-lease-startup-bank-cfg profile img cfg limit tot) quantum) 0)
  (true-list-fix cfg)))

(local (defthm m25-fix-update-by-definition
 (equal (true-list-fix (update-nth n v xs)) (update-nth n v (true-list-fix xs)))
 :hints (("Goal" :induct (update-nth n v xs)
                 :in-theory (union-theories '(update-nth true-list-fix zp nfix natp car-cons cdr-cons default-car default-cdr)
                                           (theory 'minimal-theory))))))

(local (defthm m25-fix-fix-by-definition
 (equal (true-list-fix (true-list-fix xs)) (true-list-fix xs))
 :hints (("Goal" :induct (true-list-fix xs)
  :in-theory (union-theories '(true-list-fix car-cons cdr-cons default-car default-cdr)
                            (theory 'minimal-theory))))))

; The bank projection changes only field 14. These equalities are wiring.
(local (defthm m25-bank-floor-fields-by-definition
 (and
  (equal (fn-mm-cfg-connections (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-connections cfg))
  (equal (fn-mm-cfg-tlsp (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-tlsp cfg))
  (equal (fn-mm-cfg-trigger (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-trigger cfg))
  (equal (fn-mm-cfg-pub-trigger (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-pub-trigger cfg))
  (equal (fn-mm-cfg-reclaim-live-p (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-reclaim-live-p cfg))
  (equal (fn-mm-cfg-cache (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-cache cfg))
  (equal (fn-mm-cfg-cold (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-cold cfg))
  (equal (fn-mm-cfg-handshakes (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-handshakes cfg))
  (equal (fn-mm-cfg-over-window (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-over-window cfg))
  (equal (fn-mm-cfg-server-octets (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-server-octets cfg))
  (equal (fn-mm-cfg-holders (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-holders cfg))
  (equal (fn-mm-cfg-rho (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-rho cfg))
  (equal (fn-mm-cfg-config (update-nth 14 b (true-list-fix cfg))) (fn-mm-cfg-config cfg))
  (equal (fn-mm-cfg-bank-floor (update-nth 14 b (true-list-fix cfg))) (nfix b)))
 :hints (("Goal" :in-theory (union-theories
  '(m25-fix-update-by-definition m25-fix-fix-by-definition nth-update-nth (:executable-counterpart nfix) fn-mm-cfg-bank-floor fn-mm-nat fn-mm-cfg-connections fn-mm-cfg-tlsp fn-mm-cfg-trigger fn-mm-cfg-pub-trigger fn-mm-cfg-reclaim-live-p fn-mm-cfg-cache fn-mm-cfg-cold fn-mm-cfg-handshakes fn-mm-cfg-over-window fn-mm-cfg-server-octets fn-mm-cfg-holders fn-mm-cfg-rho fn-mm-cfg-config)
  (theory 'minimal-theory))))))

(local (defthm m25-bank-floor-terms-by-definition
 (and
  (equal (fn-mm-base img (update-nth 14 b (true-list-fix cfg))) (fn-mm-base img cfg))
  (equal (fn-mm-owner tot (update-nth 14 b (true-list-fix cfg))) (fn-mm-owner tot cfg))
  (equal (fn-mm-inflight profile (update-nth 14 b (true-list-fix cfg))) (fn-mm-inflight profile cfg))
  (equal (fn-mm-maintenance tot (update-nth 14 b (true-list-fix cfg))) (fn-mm-maintenance tot cfg))
  (equal (fn-mm-collector live (update-nth 14 b (true-list-fix cfg))) (fn-mm-collector live cfg))
  (equal (fn-mm-connection-fixed profile (update-nth 14 b (true-list-fix cfg))) (fn-mm-connection-fixed profile cfg))
  (equal (fn-mm-large-pool profile (update-nth 14 b (true-list-fix cfg))) (fn-mm-large-pool profile cfg))
  (equal (fn-mm-reopen-need profile img (update-nth 14 b (true-list-fix cfg)) tot) (fn-mm-reopen-need profile img cfg tot)))
 :hints (("Goal" :in-theory (union-theories
  '(m25-bank-floor-fields-by-definition fn-mm-base fn-mm-owner fn-mm-payload-octets fn-mm-inflight
    fn-mm-cold-reads fn-mm-maintenance fn-mm-collector fn-mm-connection-fixed fn-mm-large-pool
    fn-mm-large-reply fn-mm-over-window-octets fn-mm-over-window-fit fn-mm-nov-line-octets
    fn-mm-reopen-need fn-mm-reopen-live fn-mm-checkpoint-load-octets)
  (theory 'minimal-theory))))))

(local (defthm m25-bank-floor-does-not-raise-live
 (implies (<= (nfix b) (fn-mm-connections profile cfg))
  (<= (fn-mm-live profile (update-nth 14 b (true-list-fix cfg)) tot) (fn-mm-live profile cfg tot)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
  '(fn-mm-live fn-mm-connections max m25-bank-floor-fields-by-definition m25-bank-floor-terms-by-definition)
  (theory 'minimal-theory))))))

(local (defthm m25-bank-floor-keeps-a-holding-gate
 (implies (and (<= (nfix b) (fn-mm-connections profile cfg)) (fn-mm-gate-p profile img cfg limit tot))
  (fn-mm-gate-p profile img (update-nth 14 b (true-list-fix cfg)) limit tot))
 :hints (("Goal" :in-theory (union-theories
  '(fn-mm-gate-p fn-mm-sum nfix natp m25-bank-floor-terms-by-definition)
  (theory 'minimal-theory))
  :use (m25-bank-floor-does-not-raise-live
        (:instance fn-mm-collector-monotone
         (a (fn-mm-live profile (update-nth 14 b (true-list-fix cfg)) tot)) (b (fn-mm-live profile cfg tot)))
        fn-mm-live-natp (:instance fn-mm-live-natp (cfg (update-nth 14 b (true-list-fix cfg)))))))))

(local (defthm m25-bank-floor-and-reader-projections-commute-by-definition
 (equal (fn-adm-cfg-at (update-nth 14 b (true-list-fix cfg)) k)
        (update-nth 14 b (true-list-fix (fn-adm-cfg-at cfg k))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-adm-cfg-at m25-fix-update-by-definition m25-fix-fix-by-definition
    update-nth car-cons cdr-cons default-car default-cdr
    (:executable-counterpart zp) (:executable-counterpart nfix))
  (theory 'minimal-theory))))))

(defthm fn-adm-installed-lease-allocation-within-connections
 (<= (fn-adm-installed-lease-allocation profile cfg quantum) (fn-mm-connections profile cfg))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
  '(fn-adm-installed-lease-allocation fn-adm-installed-lease-octets fn-mm-connections max)
  (theory 'minimal-theory))
  :use ((:instance fn-hl-leased-pool-within-the-large-term (q quantum) (nstatic 1) (qfixed 0) (capf 0))))))

(defthm fn-adm-lease-startup-keeps-its-bank-readers
  (<= (fn-adm-installed-capacity profile img cfg limit tot)
      (fn-adm-installed-capacity profile img
                                 (fn-adm-lease-startup-cfg profile img cfg limit tot quantum)
                                 limit tot))
  :rule-classes nil
  :hints (("Goal" :cases ((natp quantum)) :in-theory (union-theories
   '(fn-adm-public-readers-cfg fn-adm-lease-startup-cfg fn-adm-lease-startup-bank-cfg fn-adm-installed-capacity nfix natp
     (:type-prescription fn-adm-installed-lease-allocation) (:type-prescription fn-mm-connections)
     (:type-prescription fn-mm-cfg-connections)
     m25-bank-floor-fields-by-definition m25-bank-floor-and-reader-projections-commute-by-definition)
   (theory 'minimal-theory))
   :use ((:instance m25-bank-floor-keeps-a-holding-gate
          (cfg (fn-adm-lease-startup-bank-cfg profile img cfg limit tot)) (b 0))
         fn-adm-installed-capacity-is-proved-or-zero
         (:instance fn-adm-installed-capacity-is-proved-or-zero
          (cfg (fn-adm-lease-startup-cfg profile img cfg limit tot quantum)))
         (:instance fn-adm-installed-lease-allocation-within-connections
          (cfg (fn-adm-lease-startup-bank-cfg profile img cfg limit tot)))
         (:instance m25-bank-floor-keeps-a-holding-gate
          (cfg (fn-adm-lease-startup-bank-cfg profile img cfg limit tot))
          (b (fn-adm-installed-lease-allocation profile (fn-adm-lease-startup-bank-cfg profile img cfg limit tot) quantum)))
         (:instance fn-adm-capacity-is-the-most
          (cfg (fn-adm-lease-startup-cfg profile img cfg limit tot quantum))
          (j (fn-adm-installed-capacity profile img cfg limit tot)))))))
