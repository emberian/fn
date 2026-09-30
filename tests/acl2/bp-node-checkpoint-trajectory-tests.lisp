(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-trajectory")
(include-book "bp-node-checkpoint-trailer-tests")

(defun-nx fn-bpcktt-started ()
  (mv-nth 1 (fn-bpck-digest-start (fn-bpckt-job) (create-pgs-digest-state))))
(defun-nx fn-bpcktt-before-read ()
  (mv-nth 1 (fn-bpck-digest-step (fn-bpckt-job) nil (fn-bpcktt-started))))
(defun-nx fn-bpcktt-first-read ()
  (let ((job (fn-bpckt-job)) (cursor (fn-bpcktt-before-read)))
    (fn-bpnrc-prefix (pgs-dcb-read-demand (+ 14 (fn-bpn-nth 8 job)) cursor)
      (fn-bpnrc-suffix (pgs-dcb-next-byte-offset cursor) (cadr (fn-bpckt-emitted))))))

(defthm fn-bpcktt-start-positive
  (let ((job (fn-bpckt-job)))
    (and (fn-bpck-ready-sourcep job)
         (equal (mv-nth 0 (fn-bpck-digest-start job (create-pgs-digest-state))) :started)
         (fn-bpck-frame-digest-invariantp job (fn-bpcktt-started))))
  :hints (("Goal" :use ((:instance fn-bpck-digest-start-establishes-exact-source-invariant
                                   (job (fn-bpckt-job))
                                   (pgs-digest-state (create-pgs-digest-state))))
    :in-theory (e/d (fn-bpck-ready-sourcep fn-bpckt-job fn-bpckt-emitted fn-bpcktt-started
                      fn-bpck-frame-prefix fn-bpcke-prefix)
                     (fn-bpck-digest-start fn-bpck-frame-digest-invariantp))))
  :rule-classes nil)

(defthm fn-bpcktt-step-positive
  (let ((job (fn-bpckt-job)) (cursor (fn-bpcktt-before-read)) (octets (fn-bpcktt-first-read)))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (pgs-dcs-blockp (fn-b3-words 16 octets) (fn-bpck-frame-prefix job) cursor)
         (fn-bpck-frame-digest-invariantp job
           (mv-nth 1 (fn-bpck-digest-step job octets cursor)))))
  :hints (("Goal" :in-theory
    (enable fn-bpcktt-before-read fn-bpcktt-first-read fn-bpcktt-started
            fn-bpckt-job fn-bpckt-emitted fn-bpck-frame-prefix fn-bpcke-prefix
            fn-bpck-frame-digest-invariantp pgs-dcs-invariantp pgs-dcs-blockp
            pgs-dbd-domainp pgs-dcd-domainp pgs-dcs-counterp pgs-dcs-counter-framesp
            pgs-dbd-framesp pgs-dcd-framesp pgs-dcs-phasep pgs-dcr-denote
            pgs-dcr-current pgs-dcr-span)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

(defthm fn-bpcktt-missing-ready-counterexample
  (let ((job (update-nth 11 :none (fn-bpckt-job))))
    (and (not (fn-bpck-ready-sourcep job))
         (not (equal (mv-nth 0 (fn-bpck-digest-start job (create-pgs-digest-state)))
                     :started))))
  :hints (("Goal" :in-theory (enable fn-bpckt-job fn-bpckt-emitted
                                     fn-bpck-ready-sourcep fn-bpck-digest-start)))
  :rule-classes nil)

(defthm fn-bpcktt-missing-canonical-read-counterexample
  (let ((job (fn-bpckt-job)) (cursor (fn-bpcktt-before-read))
        (octets (make-list 64 :initial-element 0)))
    (and (fn-bpck-frame-digest-invariantp job cursor)
         (not (pgs-dcs-blockp (fn-b3-words 16 octets) (fn-bpck-frame-prefix job) cursor))
         (not (fn-bpck-frame-digest-invariantp job
                 (mv-nth 1 (fn-bpck-digest-step job octets cursor))))))
  :hints (("Goal" :in-theory
    (enable fn-bpcktt-before-read fn-bpcktt-started fn-bpckt-job fn-bpckt-emitted
            fn-bpck-frame-prefix fn-bpcke-prefix fn-bpck-frame-digest-invariantp
            pgs-dcs-invariantp pgs-dcs-blockp pgs-dbd-domainp pgs-dcd-domainp
            pgs-dcs-counterp pgs-dcs-counter-framesp pgs-dbd-framesp pgs-dcd-framesp
            pgs-dcs-phasep pgs-dcr-denote pgs-dcr-current pgs-dcr-span)
    :expand ((:free (out msg cursor) (pgs-dcr-fold 0 out msg cursor)))))
  :rule-classes nil)

; Corrupted capture authority, with the canonical source block retained.
(defthm fn-bpcktt-corrupted-capture-invariant-counterexample
  (let ((job (fn-bpckt-job))
        (cursor (update-pgs-dc-capture :bad (fn-bpcktt-before-read)))
        (octets (fn-bpcktt-first-read)))
    (and (pgs-dcs-blockp (fn-b3-words 16 octets) (fn-bpck-frame-prefix job) cursor)
         (not (fn-bpck-frame-digest-invariantp job cursor))
         (not (fn-bpck-frame-digest-invariantp job
                 (mv-nth 1 (fn-bpck-digest-step job octets cursor))))))
  :hints (("Goal" :in-theory
    (enable fn-bpcktt-before-read fn-bpcktt-first-read fn-bpcktt-started
            fn-bpckt-job fn-bpckt-emitted fn-bpck-frame-prefix fn-bpcke-prefix
            fn-bpck-frame-digest-invariantp pgs-dcs-blockp pgs-dcr-span)))
  :rule-classes nil)

(defthm fn-bpcktt-write-history-ready-positive
  (let ((job (fn-bpckt-job)) (emitted (cadr (fn-bpckt-emitted))))
    (and (fn-bpcke-invariantp job emitted)
         (equal (fn-bpn-nth 6 job) :digest-finish)
         (equal (fn-bpn-nth 11 job) :private)
         (posp (fn-bpn-nth 8 job))
         (<= (fn-bpn-nth 8 job) *fn-bpc-max-uint*)
         (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job)))
         (fn-bpck-ready-sourcep job)))
  :hints (("Goal" :in-theory (enable fn-bpckt-job fn-bpckt-emitted fn-bpcke-invariantp
                                     fn-bpck-ready-sourcep fn-bpck-frame-prefix fn-bpcke-prefix)))
  :rule-classes nil)
