; fn -- Q16 (a) (lane online-reclaim-5): the swapped owner serves a POST.
;
; The installing reclaim pass (books/owner-reclaim-pass.lisp) swaps in the
; owner the full open of the rewritten history installs
; (fn-orcp-rebuild-is-the-full-open).  That owner is the open's owner BEFORE
; its recovery barriers: its Store is in phase :recovering
; (books/store-open-bridge.lisp fn-sn-open-observed-not-ready-before-the-
; barriers-of-host-open), and the writer's take (books/owner.lisp
; fn-own-take-submission) takes nothing outside :ready.  Served as it was, the
; swapped owner answered every read and queued every POST forever: the
; composed-boundary defect native-orp4 found (the POST after the swap never
; got its final reply).  The open delivers the three recovery barriers
; (host/native/owner.lisp fnn-owner-install, fnn-store-recovery-barriers,
; through fn-owner-io -> fn-rcon-ocfg-io); the swap now delivers the same
; three in the same quantum (fnn-owner-reclaim-pass).  The keystone: after
; them the swapped owner is :ready and takes a queued submission exactly when
; the live owner's queue, pipeline and staging would let it.

(in-package "ACL2")
(include-book "owner-reclaim-conns")
(include-book "store-open-bridge")
(include-book "records-concrete-owner")

; N :ok recovery-barrier observations, each as the host delivers it
; (fnn-owner-observe :recovery-barrier :ok -> fn-owner-io -> fn-rcon-ocfg-io).
(defun fn-orrd-barriers (oc n)
  (declare (xargs :guard (natp n) :verify-guards nil :measure (nfix n)))
  (if (zp n)
      oc
    (fn-orrd-barriers (fn-rcon-ocfg-io oc :recovery-barrier :ok) (1- n))))

; What the swap quantum leaves served: the swapped configuration after the
; open's barrier count of :ok barriers.
(defun fn-orrd-ready-ocfg (live-oc rebuilt-oc)
  (declare (xargs :guard t :verify-guards nil))
  (fn-orrd-barriers (fn-orcp-swapped-ocfg live-oc rebuilt-oc)
                    *fn-sf-recovery-barrier-count*))

; The writer's take takes the queue's head (fn-ocfg-step's :take arm, then
; fn-own-take-submission): nothing staged, nothing in flight or pending, a
; queued submission, the Store :ready.
(defun fn-orrd-takesp (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (not (fn-ocfg-staged oc))
         (null (fn-own-inflight o))
         (consp (fn-own-queue o))
         (null (fn-own-pending o))
         (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready))))

; The same test without the phase: what the live owner's pipeline allows.
(defun fn-orrd-pipeline-takesp (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (not (fn-ocfg-staged oc))
         (null (fn-own-inflight o))
         (consp (fn-own-queue o))
         (null (fn-own-pending o)))))

; -----------------------------------------------------------------------------
; The barrier step keeps everything the take reads but the Store.

(local
 (defthm fn-orrd-io-owner-fields
   (let ((o2 (fn-ocfg-owner (fn-rcon-ocfg-io oc :recovery-barrier :ok))))
     (and (equal (fn-own-store o2)
                 (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) :recovery-barrier :ok))
          (equal (fn-own-queue o2) (fn-own-queue (fn-ocfg-owner oc)))
          (equal (fn-own-inflight o2) (fn-own-inflight (fn-ocfg-owner oc)))
          (equal (fn-own-pending o2) (fn-own-pending (fn-ocfg-owner oc)))))
   :hints (("Goal" :in-theory (e/d (fn-rcon-ocfg-io fn-rcon-own-store-io fn-own-refresh)
                                   (fn-rcon-ocfg-io-is-ocfg-step))))))

(local
 (defthm fn-orrd-io-staged
   (equal (fn-ocfg-staged (fn-rcon-ocfg-io oc :recovery-barrier :ok))
          (fn-ocfg-staged oc))
   :hints (("Goal" :in-theory (e/d (fn-rcon-ocfg-io) (fn-rcon-ocfg-io-is-ocfg-step))))))

(local
 (defthm fn-orrd-barriers-fields
   (let ((o2 (fn-ocfg-owner (fn-orrd-barriers oc n))))
     (and (equal (fn-own-store o2)
                 (fn-sn-observed-rebarrier (fn-own-store (fn-ocfg-owner oc)) n))
          (equal (fn-own-queue o2) (fn-own-queue (fn-ocfg-owner oc)))
          (equal (fn-own-inflight o2) (fn-own-inflight (fn-ocfg-owner oc)))
          (equal (fn-own-pending o2) (fn-own-pending (fn-ocfg-owner oc)))
          (equal (fn-ocfg-staged (fn-orrd-barriers oc n)) (fn-ocfg-staged oc))))
   :hints (("Goal" :induct (fn-orrd-barriers oc n)
                   :in-theory (enable fn-orrd-barriers fn-sn-observed-rebarrier)))))

; -----------------------------------------------------------------------------
; The rebuilt owner's Store is the host open's state before its barriers.

; The configured open answers :ok only by fn-sn-open-ok of a state it checked
; (books/config-observed.lisp): fn-ock-install's :ok test is fn-sn-open-okp.
(local (defthm fn-orrd-cpo-ok-kind-is-okp
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)
           (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-okp)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity fn-replay-identity-loop
                 fn-stx-index-of-store fn-sn-statep fn-cnode-statep
                 fn-sn-observed-seed fn-replay-advance-txid fn-sn-with-configuration
                 fn-sn-observed-historyp fn-cpe-projection-replay
                 fn-th-prefix-project fn-cei-build fn-cpo-install
                 fn-sn-update-replayed fn-bs-recovered-kernel fn-sn-with-event-index
                 fn-sn-with-topic fn-sn-with-consumer))))))

(local (defthm fn-orrd-store-of-refresh
  (equal (fn-own-store (fn-own-refresh o)) (fn-own-store o))
  :hints (("Goal" :in-theory (enable fn-own-refresh)))))

(defthm fn-orrd-rebuilt-store-is-the-open
  (let ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns))))
    (implies (not (equal rebuilt-oc :fault))
             (and (fn-sn-open-okp (fn-cpo-open-observed configs frontier rows))
                  (equal (fn-own-store (fn-ocfg-owner rebuilt-oc))
                         (fn-sn-open-state (fn-cpo-open-observed configs frontier rows))))))
  :rule-classes nil
  :hints (("Goal" :use (fn-orcp-rebuild-is-the-full-open)
                  :in-theory (e/d (fn-ock-recover-full fn-ock-install fn-own-configure fn-own-start)
                                  (fn-orcp-rebuild fn-cpo-open-observed fn-cpr-replay
                                   fn-own-refresh fn-sn-open-okp)))))

(local (defthm fn-orrd-swapped-fields
  (let ((next (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))
    (and (equal (fn-own-store (fn-ocfg-owner next)) (fn-own-store (fn-ocfg-owner rebuilt-oc)))
         (equal (fn-own-queue (fn-ocfg-owner next)) (fn-own-queue (fn-ocfg-owner live-oc)))
         (equal (fn-own-inflight (fn-ocfg-owner next)) (fn-own-inflight (fn-ocfg-owner live-oc)))
         (equal (fn-own-pending (fn-ocfg-owner next)) (fn-own-pending (fn-ocfg-owner live-oc)))
         (equal (fn-ocfg-staged next) (fn-ocfg-staged live-oc))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-ocfg fn-orcp-swapped-owner fn-orcp-swap-base
                                   fn-own-set-conns)
                                  (fn-orcp-repin-conns fn-orcp-pins-at))))))

(defthm fn-orrd-swapped-ready-phase
  (let ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns))))
    (implies (equal (fn-orcp-swap-decision word live-oc rebuilt-oc) :swap)
             (equal (fn-sf-phase (fn-sn-files (fn-own-store
                                               (fn-ocfg-owner
                                                (fn-orrd-ready-ocfg live-oc rebuilt-oc)))))
                    :ready)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-orcn-admitted-swap-rebuild-installed
                                   (rebuilt-oc (cadr (fn-orcp-rebuild rows configs
                                                                      frontier max-conns))))
                        fn-orrd-rebuilt-store-is-the-open
                        (:instance fn-sn-open-observed-barriers-open-ready-of-host-open
                                   (events rows)))
                  :in-theory (e/d (fn-orrd-ready-ocfg)
                                  (fn-sn-open-observed-barriers-open-ready-of-host-open
                                   fn-orcp-rebuild fn-orcp-swap-decision fn-orcp-swapped-ocfg
                                   fn-cpo-open-observed fn-sn-open-okp fn-orrd-barriers
                                   fn-sn-observed-rebarrier)))))

; KEYSTONE (composed; the POST after the swap).  Over the pass's rebuild,
; when the swap decision answers :swap, the owner the swap quantum leaves
; served (the swapped configuration after the open's three :ok recovery
; barriers, host/native/owner.lisp fnn-owner-reclaim-pass) is :ready, keeps
; the live queue, and its writer takes a queued submission exactly when the
; live owner's pipeline would -- the queue's head, as before the swap.
(defthm fn-orrd-a-post-after-the-swap-is-taken-as-before
  (let* ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns)))
         (ready (fn-orrd-ready-ocfg live-oc rebuilt-oc))
         (live (fn-ocfg-owner live-oc)))
    (implies (equal (fn-orcp-swap-decision word live-oc rebuilt-oc) :swap)
             (and (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner ready))))
                         :ready)
                  (equal (fn-own-queue (fn-ocfg-owner ready)) (fn-own-queue live))
                  (equal (fn-orrd-takesp ready) (fn-orrd-pipeline-takesp live-oc))
                  (implies (fn-orrd-pipeline-takesp live-oc)
                           (let ((taken (fn-ocfg-owner (fn-ocfg-step ready '(:take) fn-arena))))
                             (and (equal (fn-own-pending taken)
                                         (fn-own-sub-id (car (fn-own-queue live))))
                                  (equal (fn-own-queue taken) (cdr (fn-own-queue live)))))))))
  :rule-classes nil
  :hints (("Goal" :use (fn-orrd-swapped-ready-phase)
                  :in-theory (e/d (fn-orrd-ready-ocfg fn-orrd-takesp fn-orrd-pipeline-takesp
                                   fn-ocfg-step fn-ocfg-pass fn-own-step fn-own-take-submission)
                                  (fn-orcp-rebuild fn-orcp-swap-decision fn-orcp-swapped-ocfg
                                   fn-orrd-barriers fn-sn-observed-rebarrier)))))

; The defect native-orp4 found, as a theorem: the swapped configuration
; served WITHOUT the barriers is :recovering, and its writer's take is the
; identity on the owner -- every POST queued after the swap waits forever.
(defthm fn-orrd-the-swap-without-the-barriers-never-takes
  (let* ((rebuilt-oc (cadr (fn-orcp-rebuild rows configs frontier max-conns)))
         (next (fn-orcp-swapped-ocfg live-oc rebuilt-oc)))
    (implies (equal (fn-orcp-swap-decision word live-oc rebuilt-oc) :swap)
             (and (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner next))))
                         :recovering)
                  (not (fn-orrd-takesp next))
                  (equal (fn-ocfg-owner (fn-ocfg-step next '(:take) fn-arena))
                         (fn-ocfg-owner next)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-orcn-admitted-swap-rebuild-installed
                                   (rebuilt-oc (cadr (fn-orcp-rebuild rows configs
                                                                      frontier max-conns))))
                        fn-orrd-rebuilt-store-is-the-open
                        (:instance fn-sn-open-observed-not-ready-before-the-barriers-of-host-open
                                   (events rows)))
                  :in-theory (e/d (fn-orrd-takesp fn-ocfg-step fn-ocfg-pass fn-own-step
                                   fn-own-take-submission)
                                  (fn-sn-open-observed-not-ready-before-the-barriers-of-host-open
                                   fn-orcp-rebuild fn-orcp-swap-decision fn-orcp-swapped-ocfg
                                   fn-cpo-open-observed fn-sn-open-okp))
                  :expand ((fn-sn-observed-rebarrier
                                            (fn-sn-open-state (fn-cpo-open-observed configs frontier rows)) 0)))))

(in-theory (disable fn-orrd-barriers fn-orrd-ready-ocfg fn-orrd-takesp fn-orrd-pipeline-takesp))
