; INTERNAL ordinary output pairing over the actual seventh receiver slot.
; Public OUTGOING source/factory still returns NIL. DEMAND below is canonical
; internal evaluator output owed by that future producer, never native data.
; No constructor, runtime allowance, all-alias return or GC claim is supplied.
(in-package "ACL2")
(include-book "receiver-output-issuer")
(include-book "reader-output-storage")
(include-book "page-read-counter-transaction")

(defun fn-rxo-storage-freshp (fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t :verify-guards nil))
 (and (eq (fn-ros-phase fn-output-storage) :empty)
      (null (fn-ros-job fn-output-storage))
      (null (fn-ros-source fn-output-storage))
      (null (fn-ros-native-borrow fn-output-storage))
      (null (fn-ros-local-receipt fn-output-storage))
      (stobj-let ((fn-octets (fn-ros-octets fn-output-storage)))
       (empty) (equal (fn-octets-len fn-octets) 0) empty)))

; Initial window only. Subsequent windows require an actual returned storage
; receipt; this primitive cannot reset/rearm a nonempty slot or actor.
; MODE stays fenced through child issue and slot publication, then restores
; only after the retained immediate counter receipt finishes successfully.
(defun fn-rxo-reserve-initial-current
 (episode demand fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
                 :guard t :verify-guards nil))
 (cond
  ((not (eq (fn-prp-mode fn-page-read-pool) :served))
   (mv :output-reservation-recovery nil fn-receiver-turn fn-page-read-pool fn-output-storage))
  ((or (fn-rxt-output-bundle fn-receiver-turn)
       (not (fn-rxo-storage-freshp fn-output-storage)))
   (mv :output-busy nil fn-receiver-turn fn-page-read-pool fn-output-storage))
  ((not (and (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
   (mv :unavailable-output-demand nil fn-receiver-turn fn-page-read-pool fn-output-storage))
  (t
   (mv-let (word source preOC RC step)
    (fn-owner-rx-turn-response-result episode fn-rx-provider fn-receiver-turn fn-page-read-pool)
    (declare (ignore preOC RC step))
    (if (not (eq word :response-result))
     (mv :unavailable-response nil fn-receiver-turn fn-page-read-pool fn-output-storage)
     (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
            (nonce (fn-prl-nth 2 ledger))
            (parser (fn-rxt-job fn-receiver-turn))
            (intent (list :reader-output-install-intent episode source nonce demand parser nil)))
      (mv-let (prepare-word prepared fn-page-read-pool)
       (fn-owner-page-read-counter-prepare nonce :receiver-output intent fn-page-read-pool)
       (if (not (eq prepare-word :counter-preparing))
        (mv prepare-word nil fn-receiver-turn fn-page-read-pool fn-output-storage)
        (let ((fn-receiver-turn (update-fn-rxt-output-bundle intent fn-receiver-turn)))
         (mv-let (reserve-word next-ledger fn-output-storage)
          (fn-ros-reserve-internal episode 0 source demand ledger fn-output-storage)
          (if (not (eq reserve-word :reserved))
           ; Staging is already an effect. Preserve both intents rather than
           ; report an unchanged refusal or silently retry the issuer.
           (mv :output-reservation-recovery nil fn-receiver-turn fn-page-read-pool fn-output-storage)
           (let ((token (fn-ros-current-token fn-output-storage)))
            (mv-let (apply-word receipt fn-page-read-pool)
             (fn-owner-page-read-counter-apply next-ledger prepared fn-page-read-pool)
             (if (not (eq apply-word :counter-publishing))
              (mv :output-reservation-recovery nil fn-receiver-turn fn-page-read-pool fn-output-storage)
              (let* ((bundle (list :reader-response-roots parser nil
                                   (fn-ros-job fn-output-storage)))
                     (fn-receiver-turn (update-fn-rxt-output-bundle bundle fn-receiver-turn)))
               (mv-let (finish-word fn-page-read-pool)
                (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
                (if (eq finish-word :published)
                 (mv :output-reserved token fn-receiver-turn fn-page-read-pool fn-output-storage)
                 (mv :output-reservation-recovery nil fn-receiver-turn fn-page-read-pool fn-output-storage))))))))))))))))))
(verify-guards fn-rxo-storage-freshp)
(verify-guards fn-rxo-reserve-initial-current)

(encapsulate ()
 (local (defthm fn-rxo-prepare-word-local
  (not (equal (car (fn-owner-page-read-counter-prepare nonce kind continuation fn-page-read-pool))
              :output-reserved))
  :hints (("Goal" :in-theory (enable fn-owner-page-read-counter-prepare)))))
 (local (defthm fn-rxo-nth-update-local
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j v x))
          (if (equal i j) v (nth i x))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))
 (defthm fn-rxo-initial-reservation-establishes-current-job-pairing
  (let* ((result (fn-rxo-reserve-initial-current episode demand fn-rx-provider
                    fn-receiver-turn fn-page-read-pool fn-output-storage))
         (bundle (fn-rxt-output-bundle (mv-nth 2 result)))
         (actor (mv-nth 4 result)))
   (implies (eq (mv-nth 0 result) :output-reserved)
    (and (fn-rxt-fixed-widthp bundle 4)
         (eq (fn-prl-nth 0 bundle) :reader-response-roots)
         (null (fn-prl-nth 2 bundle))
         (equal (fn-prl-nth 3 bundle) (fn-ros-job actor))
         (equal (mv-nth 1 result) (fn-ros-current-token actor)))))
  :hints (("Goal" :in-theory (e/d
   (fn-rxo-reserve-initial-current fn-rxt-fixed-widthp fn-ros-current-token fn-prl-nth)
   (fn-rxo-storage-freshp fn-owner-rx-turn-response-result fn-owner-page-read-counter-prepare
    fn-owner-page-read-counter-apply fn-owner-page-read-counter-finish fn-ros-reserve-internal
    fn-owner-page-read-ledger fn-prs-vectorp fn-prl-build))))
  :rule-classes nil))

; INTERNAL maintained pair, established by reserve-initial-current and kept
; by paired-current-step below. Token/source equality is a bounded logical
; selector under that carried association, not proof of host object identity.
(defun fn-rxo-current-pairp
 (token fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)))
 (let* ((bundle (fn-rxt-output-bundle fn-receiver-turn))
        (episode (fn-prl-nth 1 token)))
  (and (fn-rog-window-tokenp token)
       (fn-owner-rx-turn-response-currentp episode fn-rx-provider fn-receiver-turn fn-page-read-pool)
       (fn-rxt-fixed-widthp bundle 4)
       (eq (fn-prl-nth 0 bundle) :reader-response-roots)
       (null (fn-prl-nth 2 bundle))
       (fn-rog-jobp (fn-prl-nth 3 bundle))
       (equal token (fn-prl-nth 4 (fn-prl-nth 3 bundle)))
       (equal token (fn-ros-current-token fn-output-storage))
       (equal episode (fn-prl-nth 1 (fn-ros-job fn-output-storage)))
       (equal (fn-ros-source fn-output-storage) (fn-rxt-source fn-receiver-turn)))))

; No install action here: actual backing C->U promotion and the paid storage
; factory remain separate missing joins. PREPARE allocates no backing, OBSERVE
; transports the typed I/O observation, DETACH emits only the local receipt.
; Native return observation is owned by the real alias-drop epilogue, and is
; not fabricated by this parent. Every action preserves storage/source debt.
(defun fn-rxo-paired-current-step
 (token action IOword count fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage)))
 (cond
  ((not (fn-rxo-current-pairp token fn-rx-provider fn-receiver-turn fn-page-read-pool fn-output-storage))
   (mv :retained-output nil fn-receiver-turn fn-page-read-pool fn-output-storage))
  ((not (or (and (eq action :prepare) (eq (fn-ros-phase fn-output-storage) :reserved))
            (and (eq action :observe) (eq (fn-ros-phase fn-output-storage) :native-borrowed))
            (and (eq action :detach) (eq (fn-ros-phase fn-output-storage) :native-return-observed))))
   (mv :retained-output nil fn-receiver-turn fn-page-read-pool fn-output-storage))
  (t
   (let* ((bundle (fn-rxt-output-bundle fn-receiver-turn))
          (ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (continuation (list :reader-output-step token action bundle
                         (fn-ros-job fn-output-storage) (fn-ros-source fn-output-storage))))
    (mv-let (prepare-word prepared fn-page-read-pool)
     (fn-owner-page-read-counter-prepare (fn-prl-nth 3 token) :receiver-output-step continuation fn-page-read-pool)
     (if (not (eq prepare-word :counter-preparing))
      (mv :output-step-recovery nil fn-receiver-turn fn-page-read-pool fn-output-storage)
      (let ((fn-receiver-turn (update-fn-rxt-output-bundle continuation fn-receiver-turn)))
       (mv-let (word observation fn-output-storage)
        (cond
         ((eq action :prepare)
          (mv-let (word fn-output-storage) (fn-ros-prepare-current token fn-output-storage)
           (mv word nil fn-output-storage)))
         ((eq action :observe) (fn-ros-observe-current token IOword count fn-output-storage))
         (t (fn-ros-storage-detach token fn-output-storage)))
        (mv-let (apply-word receipt fn-page-read-pool)
         (fn-owner-page-read-counter-apply ledger prepared fn-page-read-pool)
         (if (not (eq apply-word :counter-publishing))
          (mv :output-step-recovery observation fn-receiver-turn fn-page-read-pool fn-output-storage)
          (let* ((next-bundle (list :reader-response-roots (fn-prl-nth 1 bundle) nil
                                 (fn-ros-job fn-output-storage)))
                 (fn-receiver-turn (update-fn-rxt-output-bundle next-bundle fn-receiver-turn)))
           (mv-let (finish-word fn-page-read-pool)
            (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
            (mv (if (eq finish-word :published) word :output-step-recovery)
                observation fn-receiver-turn fn-page-read-pool fn-output-storage)))))))))))))

(encapsulate ()
 (local (defthm fn-rxo-current-nth-update-local
  (implies (and (natp i) (natp j))
   (equal (nth i (update-nth j v x)) (if (equal i j) v (nth i x))))
  :hints (("Goal" :in-theory (enable nth update-nth)))))
 (defthm fn-rxo-current-step-publishes-actual-job-preserves-parser-root
  (let* ((out (fn-rxo-paired-current-step token action IOword count fn-rx-provider
                 fn-receiver-turn fn-page-read-pool fn-output-storage))
         (bundle (fn-rxt-output-bundle (mv-nth 2 out)))
         (old-bundle (fn-rxt-output-bundle fn-receiver-turn)))
   (implies (member-eq (mv-nth 0 out)
               '(:constructing :writing :wait :drained :cancelled :storage-local-returned))
    (and (equal (fn-prl-nth 3 bundle) (fn-ros-job (mv-nth 4 out)))
         (equal (fn-prl-nth 1 bundle) (fn-prl-nth 1 old-bundle))
         (null (fn-prl-nth 2 bundle))
         (eq (fn-prl-nth 0 bundle) :reader-response-roots))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d
   (fn-rxo-paired-current-step fn-prl-nth)
   (fn-rxo-current-pairp fn-owner-page-read-ledger
    fn-owner-page-read-counter-prepare fn-owner-page-read-counter-apply
    fn-owner-page-read-counter-finish fn-ros-prepare-current
    fn-ros-observe-current fn-ros-storage-detach))))))
