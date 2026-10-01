; Concrete per-response output storage, not a global holder directory.
; The internal reservation uses the real shared PRS OLD NEXT. A registered
; source producer and whole-runtime allowance must precede these operations;
; neither is supplied by this book and public OUTGOING remains unavailable.
(in-package "ACL2")
(include-book "reader-output-job")
(include-book "octets-stobj")

(defstobj fn-output-storage
 (fn-ros-job :type t :initially nil)
 (fn-ros-source :type t :initially nil)
 (fn-ros-phase :type t :initially :empty)
 (fn-ros-native-borrow :type t :initially nil)
 (fn-ros-local-receipt :type t :initially nil)
 (fn-ros-octets :type fn-octets)
 :inline t)

; INTERNAL registered factory action. No native job/source/demand setter.
; Concrete actor/child constructor and retained capacity are separately owed
; in the selected installed factory's high-water allowance.
(defun fn-ros-reserve-internal (episode serial source demand ledger fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (eq (fn-ros-phase fn-output-storage) :empty))
  (mv :busy ledger fn-output-storage)
  (mv-let (word job ledger)
   (fn-rog-reserve-issued-current episode serial :fn-output-storage demand nil ledger)
   (if (not (eq word :reserved)) (mv word ledger fn-output-storage)
    (let* ((fn-output-storage (update-fn-ros-job job fn-output-storage))
           (fn-output-storage (update-fn-ros-source source fn-output-storage))
           (fn-output-storage (update-fn-ros-phase :reserved fn-output-storage)))
     (mv :reserved ledger fn-output-storage))))))

(defun fn-ros-current-token (fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (fn-prl-nth 4 (fn-ros-job fn-output-storage)))

; The output factory's owned child is selected by the concrete parent, not
; by a host-provided array or identity. This begins the existing installation
; fence; the actual bounded renderer fills this child before install-current.
(defun fn-ros-prepare-current (token fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :reserved)
               (equal token (fn-ros-current-token fn-output-storage))))
  (mv :retained fn-output-storage)
  (mv-let (word job) (fn-rog-prepare-current token (fn-ros-job fn-output-storage))
   (if (not (eq word :constructing)) (mv word fn-output-storage)
    (let* ((fn-output-storage (update-fn-ros-job job fn-output-storage))
           (fn-output-storage (update-fn-ros-phase :constructing fn-output-storage)))
     (mv word fn-output-storage))))))

; INTERNAL completion of the actual owned child. The total is its maintained
; fill count, never a host count or LEN of the entire logical response.
(defun fn-ros-install-current (token window-plan fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :constructing)
               (equal token (fn-ros-current-token fn-output-storage))))
  (mv :retained fn-output-storage)
  (let ((total (stobj-let ((fn-octets (fn-ros-octets fn-output-storage)))
                (total) (fn-octets-len fn-octets) total)))
   (mv-let (word job)
    (fn-rog-install-current token total window-plan (fn-ros-job fn-output-storage))
    (if (not (eq word :installed)) (mv word fn-output-storage)
     (let* ((fn-output-storage (update-fn-ros-job job fn-output-storage))
            (fn-output-storage (update-fn-ros-phase :store-owned fn-output-storage)))
      (mv word fn-output-storage)))))))

; A single native output borrower. Repeating acquisition cannot create an
; unregistered second alias; the host transports the exact issued token.
(defun fn-ros-native-acquire (token fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :store-owned)
               (equal token (fn-ros-current-token fn-output-storage))))
  (mv :retained fn-output-storage)
  (let* ((fn-output-storage (update-fn-ros-native-borrow token fn-output-storage))
         (fn-output-storage (update-fn-ros-phase :native-borrowed fn-output-storage)))
   (mv :native-borrowed fn-output-storage))))

; Actual transport observation preserves the storage borrow and all charges.
(defun fn-ros-observe-current (token word count fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :native-borrowed)
               (equal token (fn-ros-native-borrow fn-output-storage))))
  (mv :retained nil fn-output-storage)
  (mv-let (word offset job)
   (fn-rog-observe-current token word count (fn-ros-job fn-output-storage))
   (let ((fn-output-storage (update-fn-ros-job job fn-output-storage)))
    (mv word offset fn-output-storage)))))

; This is a typed host I/O event, not proof that CL aliases vanished. Only the
; selected native epilogue after actual private/result alias drops may invoke
; it. That caller/refinement is open; ATS :left and socket drain do not call it.
(defun fn-ros-native-return-observed (token fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :native-borrowed)
               (equal token (fn-ros-native-borrow fn-output-storage))
               (equal token (fn-ros-current-token fn-output-storage))
               (member-eq (fn-prl-nth 3 (fn-ros-job fn-output-storage))
                          '(:drained :cancelled))))
  (mv :retained fn-output-storage)
  (let* ((fn-output-storage (update-fn-ros-native-borrow nil fn-output-storage))
         (fn-output-storage (update-fn-ros-phase :native-return-observed fn-output-storage)))
   (mv :native-return-observed fn-output-storage))))

; Actual local storage epilogue. Intent precedes the first physical mutation.
; Publish a receipt before clearing the retained job's plan/result roots.
; An escape leaves :detaching (never a reusable or source-returnable phase).
; The claim and storage identity stay charged/rooted for the distinct physical
; last-borrow join and eventual coupled release. This emits NO :returned job.
(local
 (defthm fn-ros-width-implies-true-list
  (implies (fn-rog-widthp x n) (true-listp x))
  :hints (("Goal" :induct (fn-rog-widthp x n)
            :in-theory (enable fn-rog-widthp)))))

(local
 (defthm fn-ros-update-preserves-true-list
  (implies (true-listp xs) (true-listp (update-nth n value xs)))
  :hints (("Goal" :induct (update-nth n value xs)))))

(defun fn-ros-storage-detach (token fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t
  :guard-hints (("Goal" :in-theory
   (e/d (fn-rog-jobp) (fn-rog-widthp fn-rog-window-tokenp
                          fn-rog-episodep fn-prs-vectorp update-nth))))))
 (if (not (and (eq (fn-ros-phase fn-output-storage) :native-return-observed)
               (null (fn-ros-native-borrow fn-output-storage))
               (equal token (fn-ros-current-token fn-output-storage))
               (fn-rog-jobp (fn-ros-job fn-output-storage))
               (member-eq (fn-prl-nth 3 (fn-ros-job fn-output-storage))
                          '(:drained :cancelled))))
  (mv :retained nil fn-output-storage)
  (let* ((job (fn-ros-job fn-output-storage))
         (fn-output-storage (update-fn-ros-phase :detaching fn-output-storage)))
   (stobj-let ((fn-octets (fn-ros-octets fn-output-storage)))
    (fn-octets) (fn-octets-clear fn-octets)
    (let* ((receipt (list :outgoing-storage-local-return
                     (fn-prl-nth 1 job) (fn-prl-nth 2 job)
                     (fn-prl-nth 3 token) token (fn-prl-nth 6 job)
                     (fn-ros-source fn-output-storage) :detached))
           (fn-output-storage (update-fn-ros-local-receipt receipt fn-output-storage))
           (job (update-nth 10 nil (update-nth 9 nil job)))
           (fn-output-storage (update-fn-ros-job job fn-output-storage))
           (fn-output-storage (update-fn-ros-phase :storage-local-returned fn-output-storage)))
     (mv :storage-local-returned receipt fn-output-storage))))))

; Proof-only logical observation. No host callback materializes this list.
(defun-nx fn-ros-storage-trace (fn-output-storage)
 (declare (xargs :stobjs fn-output-storage :guard t :verify-guards nil))
 (stobj-let ((fn-octets (fn-ros-octets fn-output-storage)))
  (trace) (fn-octets-list fn-octets) trace))

(local
 (defthm fn-ros-prl-nth-is-nth
  (implies (natp n) (equal (fn-prl-nth n xs) (nth n xs)))
  :hints (("Goal" :induct (fn-prl-nth n xs)
           :in-theory (enable fn-prl-nth nth)))))

(defthm fn-ros-actual-detach-clears-owned-storage-retains-charge-and-source
 (let* ((answer (fn-ros-storage-detach token fn-output-storage))
        (next (mv-nth 2 answer))
        (before-job (fn-ros-job fn-output-storage))
        (after-job (fn-ros-job next)))
  (implies (eq (mv-nth 0 answer) :storage-local-returned)
   (and (equal (fn-ros-storage-trace next) nil)
        (equal (fn-prl-nth 5 after-job) (fn-prl-nth 5 before-job))
        (equal (fn-prl-nth 4 after-job) (fn-prl-nth 4 before-job))
        (equal (fn-prl-nth 6 after-job) (fn-prl-nth 6 before-job))
        (equal (fn-ros-source next) (fn-ros-source fn-output-storage))
        (equal (fn-prl-nth 9 after-job) nil)
        (equal (fn-prl-nth 10 after-job) nil)
        (equal (mv-nth 1 answer) (fn-ros-local-receipt next))
        (equal (mv-nth 1 answer)
          (list :outgoing-storage-local-return
           (fn-prl-nth 1 before-job) (fn-prl-nth 2 before-job)
           (fn-prl-nth 3 token) token (fn-prl-nth 6 before-job)
           (fn-ros-source fn-output-storage) :detached)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
  (e/d (fn-ros-storage-detach fn-ros-storage-trace fn-octets-clear
        fn-octets-list fn-ros-phase fn-ros-native-borrow fn-ros-job
        fn-ros-source fn-ros-local-receipt fn-ros-octets fn-prl-nth)
       (fn-rog-jobp fn-ros-current-token fn-output-storagep
        update-nth nth-add1)))))
