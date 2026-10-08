; One pipeline dispatcher, two kernel representations. Only the projection
; (existing fn-lgc count, not committed history) belongs in the native host.
(in-package "ACL2")
(include-book "owner-commit-durability-steps")
(local (in-theory (disable (tau-system))))

(defun fn-lgk-pipe-project (p)
  (fn-lgk-pipe-make (fn-lgk-pipe-kernel-view (fn-lgk-pipe-ks p))
                    (fn-lgk-pipe-behind p)))
(defun fn-ocp-gc-history-count (h)
  (if (natp h) h (len h)))
(defun fn-ocp-gc-project (x)
  (list (fn-lgk-pipe-project (nth 0 x)) (nth 1 x) (nth 2 x)
        (fn-ocp-gc-history-count (nth 3 x))
        (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x) (nth 8 x) (nth 9 x)
        (nth 10 x) (nth 11 x) (nth 12 x) (nth 13 x) (nth 14 x)))

(defthm fn-lgk-pipe-kernel-view-idempotent
  (equal (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-view ks))
         (fn-lgk-pipe-kernel-view ks))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-kernel-view))))
(defthm fn-lgk-pipe-kernel-view-fields
  (let ((q (fn-lgk-pipe-kernel-view ks)))
    (and (equal (fn-lgk-last q) (fn-lgk-last ks))
         (equal (fn-lgk-frontier q) (fn-lgk-frontier ks))
         (equal (fn-lgk-next-txid q) (fn-lgk-next-txid ks))
         (equal (fn-lgk-batch q) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight q) (fn-lgk-inflight ks))
         (equal (fn-lgk-acked q) (fn-lgk-acked ks))
         (equal (fn-lgk-phase q) (fn-lgk-phase ks))))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-kernel-view fn-lgc-of fn-lgc-make
                   fn-lgk-last fn-lgk-frontier fn-lgk-next-txid
                   fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase nth))))
(defthm fn-lgk-pipe-project-fields
  (and (equal (fn-lgk-pipe-ks (fn-lgk-pipe-project p))
              (fn-lgk-pipe-kernel-view (fn-lgk-pipe-ks p)))
       (equal (fn-lgk-pipe-behind (fn-lgk-pipe-project p))
              (if (fn-lgk-pipe-behind p) t nil))
       (equal (fn-lgk-pipe-d (fn-lgk-pipe-project p)) (fn-lgk-pipe-d p))
       (equal (fn-lgk-pipe-acked (fn-lgk-pipe-project p)) (fn-lgk-pipe-acked p)))
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-pipe-project fn-lgk-pipe-ks fn-lgk-pipe-behind
                  fn-lgk-pipe-d fn-lgk-pipe-acked fn-lgk-pipe-kernel-count)
                (fn-lgk-pipe-kernel-view fn-lgk-acked fn-lgc-count)))))
(defthm fn-lgk-pipe-project-idempotent
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-project p)) (fn-lgk-pipe-project p))
  :hints (("Goal" :in-theory (e/d (fn-lgk-pipe-ks fn-lgk-pipe-behind nth)
                                  (fn-lgk-pipe-kernel-view)))))
(defthm fn-ocp-gc-project-idempotent
  (equal (fn-ocp-gc-project (fn-ocp-gc-project x)) (fn-ocp-gc-project x))
  :hints (("Goal" :in-theory (e/d (update-nth nth) (fn-lgk-pipe-project)))))

(defthm fn-lgk-pipe-kernel-view-is-counted
  (fn-lgk-pipe-countedp (fn-lgk-pipe-kernel-view ks))
  :hints (("Goal" :in-theory (e/d (fn-lgk-pipe-kernel-view)
                                  (fn-lgk-pipe-countedp fn-lgc-of)))))
(local
 (defthm fn-lgk-pipe-kernel-operations-keep-representation
   (and (equal (fn-lgk-pipe-countedp (fn-lgk-pipe-kernel-fence ks unit))
               (fn-lgk-pipe-countedp ks))
        (equal (fn-lgk-pipe-countedp (fn-lgk-pipe-kernel-append ks unit extent))
               (fn-lgk-pipe-countedp ks))
        (equal (fn-lgk-pipe-countedp (fn-lgk-pipe-kernel-fail ks))
               (fn-lgk-pipe-countedp ks)))
   :hints (("Goal" :in-theory
            (e/d (fn-lgk-pipe-countedp fn-lgk-pipe-kernel-fence
                   fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fail
                   fn-lgk-fence fn-lgk-append fn-lgk-fence-failed fn-lgc-fence
                   fn-lgc-append fn-lgc-fence-failed fn-lgk-make fn-lgc-make
                   fn-lgk-committed fn-lgc-count nth)
                 (fn-lgk-fitsp fn-lgc-fitsp fn-lg-log fn-lg-last-trailer
                  fn-lgc-log-len fn-lgc-last-trailer))))))
(defthm fn-lgk-pipe-kernel-fence-view
  (equal (fn-lgk-pipe-kernel-fence (fn-lgk-pipe-kernel-view ks) unit)
         (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-fence ks unit)))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :use fn-lgk-pipe-kernel-operations-keep-representation
           :in-theory (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-fence)
                            (fn-lgk-pipe-kernel-operations-keep-representation
                             fn-lgk-pipe-countedp fn-lgk-fence fn-lgc-fence fn-lgc-of)))))
(defthm fn-lgk-pipe-kernel-append-view
  (equal (fn-lgk-pipe-kernel-append (fn-lgk-pipe-kernel-view ks) unit extent)
         (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-append ks unit extent)))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :use fn-lgk-pipe-kernel-operations-keep-representation
           :in-theory (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-append)
                            (fn-lgk-pipe-kernel-operations-keep-representation
                             fn-lgk-pipe-countedp fn-lgk-append fn-lgc-append fn-lgc-of)))))
(defthm fn-lgk-pipe-kernel-fail-view
  (equal (fn-lgk-pipe-kernel-fail (fn-lgk-pipe-kernel-view ks))
         (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-fail ks)))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :use fn-lgk-pipe-kernel-operations-keep-representation
           :in-theory (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-fail)
                            (fn-lgk-pipe-kernel-operations-keep-representation
                             fn-lgk-pipe-countedp fn-lgk-fence-failed fn-lgc-fence-failed fn-lgc-of)))))

(defthm fn-lgk-pipe-kernel-consume-view
  (equal (fn-lgk-pipe-kernel-consume (fn-lgk-pipe-kernel-view ks) txid)
         (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-consume ks txid)))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :in-theory (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-consume
                             fn-lgk-pipe-countedp fn-olr-consume-to fn-lgc-consume-to
                             fn-lgk-committed fn-lgc-of fn-lgc-count nth fn-lgc-make
                             fn-lgk-last fn-lgk-frontier fn-lgk-next-txid
                             fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase)
                            (fn-lgk-prepare fn-lgc-prepare)))))

(local (in-theory
 (disable nth len true-listp update-nth
          fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp fn-lgk-pipe-kernel-consume fn-lgk-pipe-ks fn-lgk-pipe-behind
          fn-lgk-pipe-project fn-lgk-fence fn-lgk-append fn-lgc-of
          fn-lgc-fence fn-lgc-append fn-lgk-fence-failed fn-lgc-fence-failed
          fn-lgk-phase fn-lgk-batch fn-lgk-inflight fn-lgk-frontier
          fn-lgk-last fn-lgu-acknowledge fn-lgk-pipe-kernel-octets-is-the-kernel-plan)))

(defthm fn-lgk-pipe-kernel-octets-view
  (equal (fn-lgk-pipe-kernel-octets (fn-lgk-pipe-kernel-view ks) unit)
         (fn-lgk-pipe-kernel-octets ks unit))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-kernel-octets))))
(defthm fn-lgk-pipe-kernel-fitsp-view
  (equal (fn-lgk-pipe-kernel-fitsp (fn-lgk-pipe-kernel-view ks) unit extent)
         (fn-lgk-pipe-kernel-fitsp ks unit extent))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-kernel-fitsp))))
(defthm fn-lgk-pipe-kernel-ack-of-view
  (equal (fn-lgk-pipe-kernel-ack (fn-lgk-pipe-kernel-view ks) n)
         (fn-lgu-acknowledge (fn-lgk-pipe-kernel-view ks) (nfix n)))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-kernel-ack))))
(defthm fn-lgk-pipe-fence-project
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-fence p unit))
         (fn-lgk-pipe-fence (fn-lgk-pipe-project p) unit))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-project fn-lgk-pipe-fence fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(defthm fn-lgk-pipe-fail-project
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-fail p))
         (fn-lgk-pipe-fail (fn-lgk-pipe-project p)))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-project fn-lgk-pipe-fail fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(defthm fn-lgk-pipe-ack-project
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-ack p n))
         (fn-lgk-pipe-ack (fn-lgk-pipe-project p) n))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-project fn-lgk-pipe-ack fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(defthm fn-lgk-pipe-consume-project
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-consume p txid))
         (fn-lgk-pipe-consume (fn-lgk-pipe-project p) txid))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-project fn-lgk-pipe-consume fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(defthm fn-lgk-behind-admitsp-project
  (equal (fn-lgk-behind-admitsp (fn-lgk-pipe-project p) unit extent)
         (fn-lgk-behind-admitsp p unit extent))
  :hints (("Goal" :in-theory (enable fn-lgk-behind-admitsp fn-lgk-pipe-ks
                                    fn-lgk-pipe-project fn-lgk-pipe-behind))))
(defthm fn-lgk-behind-write-project
  (equal (fn-lgk-behind-write (fn-lgk-pipe-project p) unit)
         (fn-lgk-behind-write p unit))
  :hints (("Goal" :in-theory (enable fn-lgk-behind-write fn-lgk-pipe-ks
                                    fn-lgk-pipe-project fn-lgk-pipe-behind))))
(defthm fn-lgk-behind-state-project
  (equal (fn-lgk-pipe-project (fn-lgk-behind-state p unit extent))
         (fn-lgk-behind-state (fn-lgk-pipe-project p) unit extent))
  :hints (("Goal" :in-theory
           (enable fn-lgk-behind-state fn-lgk-pipe-project fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(defthm fn-lgk-behind-effect-project
  (equal (fn-lgk-behind-effect (fn-lgk-pipe-project p) unit extent)
         (fn-lgk-behind-effect p unit extent))
  :hints (("Goal" :in-theory (enable fn-lgk-behind-effect))))

(local
 (defthm fn-lgk-pipe-kernel-take-keeps-representation
   (equal (fn-lgk-pipe-countedp
           (cadr (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)))
          (fn-lgk-pipe-countedp ks))
   :hints (("Goal" :in-theory
            (e/d (fn-lgk-pipe-kernel-take fn-lgk-pipe-countedp fn-lgc-take fn-olr-take
                    fn-lgc-prepare fn-lgk-prepare fn-lgc-make fn-lgk-make
                    fn-lgc-count fn-lgk-committed nth)
             (fn-olr-entry-octets fn-lgk-next-txid fn-lgk-phase
              fn-lgc-next-txid fn-lgc-phase fn-lg-pack-len))))))
(defthm fn-lgk-pipe-kernel-take-view
  (let ((a (fn-lgk-pipe-kernel-take (fn-lgk-pipe-kernel-view ks)
                                   record txid count octets bmax omax unit))
        (b (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)))
    (and (equal (car a) (car b))
         (equal (cadr a) (fn-lgk-pipe-kernel-view (cadr b)))
         (equal (caddr a) (caddr b))))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :use (fn-lgk-pipe-kernel-take-keeps-representation fn-lgc-take-refines)
           :in-theory
           (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-take)
                (fn-lgk-pipe-kernel-take-keeps-representation
                 fn-lgc-take fn-olr-take fn-lgc-take-refines)))))
(defthm fn-olr-gc-profile-fitp-view
  (equal (fn-olr-gc-profile-fitp (fn-lgk-pipe-kernel-view ks) record bmax omax unit)
         (fn-olr-gc-profile-fitp ks record bmax omax unit))
  :hints (("Goal" :in-theory (enable fn-olr-gc-profile-fitp))))
(defthm fn-lgk-pipe-take-project
  (let ((a (fn-lgk-pipe-take (fn-lgk-pipe-project p)
                            record txid count octets bmax omax unit))
        (b (fn-lgk-pipe-take p record txid count octets bmax omax unit)))
    (and (equal (car a) (car b))
         (equal (cadr a) (fn-lgk-pipe-project (cadr b)))
         (equal (caddr a) (caddr b))))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-take fn-lgk-pipe-project fn-lgk-pipe-ks fn-lgk-pipe-behind))))

(defthm fn-olr-gc-prepare-project
  (and (equal (mv-nth 0 (fn-olr-gc-prepare (fn-lgk-pipe-project p) records bmax omax unit))
              (mv-nth 0 (fn-olr-gc-prepare p records bmax omax unit)))
       (equal (mv-nth 1 (fn-olr-gc-prepare (fn-lgk-pipe-project p) records bmax omax unit))
              (fn-lgk-pipe-project (mv-nth 1 (fn-olr-gc-prepare p records bmax omax unit)))))
  :hints (("Goal" :induct (fn-olr-gc-prepare p records bmax omax unit)
           :expand ((fn-olr-gc-prepare p records bmax omax unit)
                    (fn-olr-gc-prepare (fn-lgk-pipe-project p) records bmax omax unit))
           :in-theory (e/d ((:induction fn-olr-gc-prepare))
                            ((:definition fn-olr-gc-prepare) fn-lgk-pipe-take fn-lgk-next-txid fn-lg-pack-len)))))

(defthm fn-ocp-gc-history-count-extend
  (implies (true-listp records)
    (equal (fn-ocp-gc-history-count (fn-ocp-gc-history-extend h records))
           (fn-ocp-gc-history-extend (fn-ocp-gc-history-count h) records)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ocp-gc-history-count fn-ocp-gc-history-extend true-listp len))))
(defthm fn-ocp-gc-project-field
  (implies (and (natp i) (< i 15))
    (equal (nth i (fn-ocp-gc-project x))
           (cond ((equal i 0) (fn-lgk-pipe-project (nth 0 x)))
                 ((equal i 3) (fn-ocp-gc-history-count (nth 3 x)))
                 (t (nth i x)))))
  :hints (("Goal" :cases ((equal i 0) (equal i 1) (equal i 2) (equal i 3) (equal i 4)
                          (equal i 5) (equal i 6) (equal i 7) (equal i 8) (equal i 9)
                          (equal i 10) (equal i 11) (equal i 12) (equal i 13) (equal i 14))
           :in-theory (enable nth))))
(defthm fn-ocp-gc-project-update
  (implies (and (natp i) (< i 15))
    (equal (fn-ocp-gc-project (update-nth i v x))
           (update-nth i (cond ((equal i 0) (fn-lgk-pipe-project v))
                                ((equal i 3) (fn-ocp-gc-history-count v))
                                (t v))
                       (fn-ocp-gc-project x))))
  :hints (("Goal" :cases ((equal i 0) (equal i 1) (equal i 2) (equal i 3) (equal i 4)
                          (equal i 5) (equal i 6) (equal i 7) (equal i 8) (equal i 9)
                          (equal i 10) (equal i 11) (equal i 12) (equal i 13) (equal i 14))
           :in-theory (e/d (nth update-nth) (fn-ocp-gc-history-count)))))

(defthm fn-lgk-pipe-project-of-make
  (equal (fn-lgk-pipe-project (fn-lgk-pipe-make ks behind))
         (fn-lgk-pipe-make (fn-lgk-pipe-kernel-view ks) behind))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-project fn-lgk-pipe-make fn-lgk-pipe-ks fn-lgk-pipe-behind))))
(local (in-theory
 (disable fn-ocp-gc-project fn-ocp-gc-history-count fn-ocp-gc-history-extend
          fn-lgk-pipe-make fn-olr-gc-prepare fn-lgc-append-admitsp fn-lgk-pipe-take
          fn-ocp-gc-event-state fn-ocp-gc-event-action fn-ocp-gc-pick
          fn-ocp-gc-finish-state fn-ocp-gc-finish-action fn-ocp-gc-finish-event
          fn-otm-held-event fn-otm-held
          fn-ocvm-step fn-ocvm-w fn-ocvm-c fn-ocvm-a fn-ocvm-b fn-ocvm-views
          fn-ocv-reader-view fn-ocs-member-releases fn-oqw-start fn-oqw-step
          fn-lgk-pipe-fence fn-lgk-pipe-fail fn-lgk-pipe-ack fn-lgk-behind-state
          fn-lgk-behind-effect fn-lgk-behind-admitsp fn-lgk-pipe-d)))

(defthm fn-ocp-gc-stop-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-stop x))
         (fn-ocp-gc-stop (fn-ocp-gc-project x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-stop))))
(defthm fn-ocp-gc-io-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-io x nextp word))
         (fn-ocp-gc-io (fn-ocp-gc-project x) nextp word))
  :hints (("Goal" :cases ((not nextp))
           :in-theory (e/d (fn-ocp-gc-io) (fn-ocp-gc-stop)))))
(defthm fn-ocp-gc-collect-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-collect x))
         (fn-ocp-gc-collect (fn-ocp-gc-project x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-collect))))
(defthm fn-ocp-gc-advance-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-advance x))
         (fn-ocp-gc-advance (fn-ocp-gc-project x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-advance fn-ocp-gc-project))))
(defthm fn-ocp-gc-begin-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-begin x nextp))
         (fn-ocp-gc-begin (fn-ocp-gc-project x) nextp))
  :hints (("Goal" :cases ((not nextp)) :in-theory (enable fn-ocp-gc-begin))))
(defthm fn-ocp-gc-reserve-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-reserve x nextp txid))
         (fn-ocp-gc-reserve (fn-ocp-gc-project x) nextp txid))
  :hints (("Goal" :cases ((not nextp))
           :in-theory (e/d (fn-ocp-gc-reserve) (fn-lgk-pipe-consume)))))
(defthm fn-ocp-gc-take-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-take x nextp record txid))
         (fn-ocp-gc-take (fn-ocp-gc-project x) nextp record txid))
  :hints (("Goal" :cases ((not nextp))
           :in-theory (e/d (fn-ocp-gc-take true-listp)
                            (fn-ocvm-make fn-lgk-pipe-take)))))
(defthm fn-ocp-gc-member-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-member x nextp outcome))
         (fn-ocp-gc-member (fn-ocp-gc-project x) nextp outcome))
  :hints (("Goal" :cases ((not nextp)) :in-theory (enable fn-ocp-gc-member))))
(defthm fn-ocp-gc-seal-extent-project
  (equal (fn-ocp-gc-seal-extent (fn-ocp-gc-project x)) (fn-ocp-gc-seal-extent x))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-seal-extent) (fn-lgc-append-len)))))
(defthm fn-ocp-gc-seal-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-seal x nextp frames))
         (fn-ocp-gc-seal (fn-ocp-gc-project x) nextp frames))
  :hints (("Goal" :cases ((not nextp))
           :in-theory (e/d (fn-ocp-gc-seal) (fn-ocp-gc-seal-extent)))))

(local
 (defthm fn-ocp-gc-seal-projected-fields
  (implies (member-equal i '(1 2 4 5 6 7 8 9 10 11 12 13 14))
    (equal (nth i (fn-ocp-gc-seal (fn-ocp-gc-project x) nil frames))
           (nth i (fn-ocp-gc-seal x nil frames))))
  :hints (("Goal" :use ((:instance fn-ocp-gc-seal-project (nextp nil)))
           :in-theory (e/d (fn-ocp-gc-project nth)
                            (fn-ocp-gc-seal fn-ocp-gc-seal-project))))))

(defthm fn-ocp-gc-seal-held-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-seal-held x frames))
         (fn-ocp-gc-seal-held (fn-ocp-gc-project x) frames))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-seal-held) (fn-ocp-gc-seal)))))

(defthm fn-ocp-gc-append-issue-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-append-issue x))
         (fn-ocp-gc-append-issue (fn-ocp-gc-project x)))
  :hints (("Goal" :in-theory (enable fn-ocp-gc-append-issue))))
(defthm fn-ocp-gc-gate-project
  (equal (fn-ocp-gc-project (fn-ocp-gc-gate x event))
         (fn-ocp-gc-gate (fn-ocp-gc-project x) event))
  :hints (("Goal" :in-theory
           (e/d (fn-ocp-gc-gate) (fn-otm-next fn-otm-observe fn-otm-disk-step fn-otm-note-step)))))
(defthm fn-ocp-gc-host-step-commutes-with-projection
  (equal (fn-ocp-gc-project (fn-ocp-gc-host-step x event))
         (fn-ocp-gc-host-step (fn-ocp-gc-project x) event))
  :hints (("Goal" :in-theory (e/d (fn-ocp-gc-host-step)
                                ( fn-ocp-gc-io fn-ocp-gc-collect fn-ocp-gc-advance
                                 fn-ocp-gc-begin fn-ocp-gc-reserve fn-ocp-gc-take
                                 fn-ocp-gc-member fn-ocp-gc-seal fn-ocp-gc-seal-held fn-ocp-gc-stop
                                 fn-ocp-gc-append-issue fn-ocp-gc-gate)))))
