;; fn: K0 before initialisation (lane k0-recovery, PKT-086 remainder).
;;
;; fn-bs-store-relation needs config.json and the allocation frontier, so it
;; does not describe a store the initializer has not finished.  The pre-init
;; relation fn-bs-k0i-pre-init-relation says what such a store is: the kernel
;; is the initial state, and the :root directory has no allocation-frontier
;; entry, durable or pending.  Its meaning is
;; fn-bs-k0i-pre-init-crash-image-is-uninitialised: every crash image of it
;; has no frontier entry and its scan faults, so a reopen finds no store and
;; initialisation runs again (the existing-image and history-retry programs
;; of byte-store-initializer).
;;
;; fn-bs-k0i-step-preserves-pre-init: every step kind the initializers use,
;; :mkdir and :link-eexist included, with ANY outcome, keeps the pre-init
;; relation unless it names the frontier in :root (fn-bs-k0i-step-inputp).
;; fn-bs-k0i-run-keeps-pre-init lifts it to every pair of any run of such
;; steps.  So every pair of the fresh initializer before its frontier
;; publication, with any outcomes (fn-bs-k0i-current-init-prefix-keeps-pre-init,
;; from the empty store), and every pair of the existing-config publication
;; (:link-eexist onto config.json) are pre-init.
;;
;; The join: fn-bs-k0i-current-init-program-splits writes the fresh program
;; as that prefix, the frontier publication, and the final fences, and
;; fn-bsi-current-init-program-establishes-relation relates its last pair to
;; the initial kernel.  NOT proved: the pairs of the frontier publication
;; from its link to the end (the pending frontier entry's two resolutions,
;; pre-init when dropped and related when landed).
(in-package "ACL2")
(include-book "byte-store-initializer")
(defun fn-bs-k0i-pre-init-relation (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal ks (fn-sf-initial-state))
       (not (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
       (not (fn-bs-ops-for-name (fn-bs-pending bs) :root *fn-bs-scan-frontier-name*))))
(defthm fn-bs-k0i-pre-init-crash-image-is-uninitialised
  (implies (and (fn-bs-k0i-pre-init-relation bs ks) (fn-bs-crash-imagep bs image))
           (and (not (fn-bs-lookup image :root *fn-bs-scan-frontier-name*))
                (not (fn-bs-scan-okp (fn-bs-scan-store image)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-crash-keeps-untouched-entry (s bs) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir (ops (fn-bs-pending bs)) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 (:instance fn-bs-quiet-lookup-is-durable-entry (s image) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-scan-store fn-bs-scan-okp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-crash-keeps-untouched-entry fn-bs-crash-imagep fn-bs-lookup fn-bs-durable-entry
                            fn-bs-ops-for-name fn-bs-ops-for-dir fn-bs-quiet-lookup-is-durable-entry
                            fn-bs-crash-image-is-quiet fn-bs-content fn-bs-names fn-bs-read-records)))))
(defthm fn-bs-k0i-ops-for-name-of-append
  (equal (fn-bs-ops-for-name (append a b) dir name)
         (append (fn-bs-ops-for-name a dir name) (fn-bs-ops-for-name b dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name))))
(defthm fn-bs-k0i-ops-for-name-of-not-for-ino
  (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-ino ops ino) dir name) (fn-bs-ops-for-name ops dir name))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name fn-bs-ops-not-for-ino))))
(defthm fn-bs-k0i-ops-for-name-of-not-for-dir
  (implies (not (fn-bs-ops-for-name ops dir name))
           (not (fn-bs-ops-for-name (fn-bs-ops-not-for-dir ops d) dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0i-ops-for-name-of-tear-write
  (equal (fn-bs-ops-for-name (fn-bs-tear-write op sel i unit) dir name) nil)
  :hints (("Goal" :induct (fn-bs-tear-write op sel i unit)
           :in-theory (e/d (fn-bs-tear-write fn-bs-ops-for-name) (fn-bs-unit-count floor nfix fn-bs-take nthcdr)))))
(defthm fn-bs-k0i-ops-for-name-of-crash-select
  (implies (not (fn-bs-ops-for-name ops dir name))
           (not (fn-bs-ops-for-name (fn-bs-crash-select ops choices unit) dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-crash-select fn-bs-ops-for-name))))
(defthm fn-bs-k0i-ops-for-name-of-ops-for-dir
  (implies (not (fn-bs-ops-for-name ops dir name))
           (not (fn-bs-ops-for-name (fn-bs-ops-for-dir ops d) dir name)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name fn-bs-ops-for-dir))))
(defthm fn-bs-k0i-ops-for-name-of-ops-for-ino
  (equal (fn-bs-ops-for-name (fn-bs-ops-for-ino ops ino) dir name) nil)
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-name fn-bs-ops-for-ino))))
(defthm fn-bs-k0i-apply-untouched-entry
  (implies (and dir name (not (fn-bs-ops-for-name ops dir name)))
           (equal (cdr (assoc-equal name (cdr (assoc-equal dir (mv-nth 1 (fn-bs-apply-ops inodes dirs ops))))))
                  (cdr (assoc-equal name (cdr (assoc-equal dir dirs))))))
  :hints (("Goal" :use ((:instance fn-bs-apply-entries-entry-is-entry-after)
                        (:instance fn-bs-entry-after-through-ops-for-name (old (cdr (assoc-equal name (cdr (assoc-equal dir dirs)))))))
           :expand ((fn-bs-entry-after nil (cdr (assoc-equal name (cdr (assoc-equal dir dirs)))) dir name))
           :in-theory (e/d (fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-entries-entry-is-entry-after fn-bs-apply-ops
                            fn-bs-apply-entries fn-bs-ops-for-name))))
  )
(defun fn-bs-k0i-names-frontierp (dir name)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal dir :root) (equal name *fn-bs-scan-frontier-name*)))
(defun fn-bs-k0i-step-inputp (step)
  (declare (xargs :guard t :verify-guards nil))
  (case (car step)
    ((:cut :write-all :fsync-file :fsync-dir) t)
    ((:create :unlink :mkdir) (not (fn-bs-k0i-names-frontierp (nth 1 step) (nth 2 step))))
    ((:link :link-eexist) (not (fn-bs-k0i-names-frontierp (nth 3 step) (nth 4 step))))
    (:rename (and (not (fn-bs-k0i-names-frontierp (nth 1 step) (nth 2 step)))
                  (not (fn-bs-k0i-names-frontierp (nth 3 step) (nth 4 step)))))
    (otherwise nil)))
(defthm fn-bs-k0i-step-preserves-pre-init
  (implies (and (fn-bs-k0i-pre-init-relation bs ks) (fn-bs-k0i-step-inputp step))
           (fn-bs-k0i-pre-init-relation (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity))
                                        (mv-nth 2 (fn-bs-step bs ks step outcome groups capacity))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-link fn-bs-rename fn-bs-unlink fn-bs-mkdir fn-bs-durable-entry
                            fn-bs-k0i-names-frontierp)
                           (fn-bs-apply-ops fn-bs-lookup fn-bs-crash-select fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-take)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-link fn-bs-rename fn-bs-unlink fn-bs-mkdir fn-bs-durable-entry
                            fn-bs-k0i-names-frontierp fn-bs-ops-for-name)
                           (fn-bs-apply-ops fn-bs-lookup fn-bs-crash-select fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-take))))))
(defun fn-bs-k0i-steps-inputp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (fn-bs-k0i-step-inputp (car steps)) (fn-bs-k0i-steps-inputp (cdr steps)))
    t))
(defun fn-bs-k0i-run-pre-init-p (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (fn-bs-k0i-pre-init-relation (car (car pairs)) (cdr (car pairs)))
           (fn-bs-k0i-run-pre-init-p (cdr pairs)))
    t))
(defthm fn-bs-k0i-run-keeps-pre-init
  (implies (and (fn-bs-k0i-pre-init-relation bs ks) (fn-bs-k0i-steps-inputp steps))
           (fn-bs-k0i-run-pre-init-p (fn-bs-run bs ks steps outcomes groups capacity)))
  :hints (("Goal" :induct (fn-bs-run bs ks steps outcomes groups capacity)
           :in-theory (e/d (fn-bs-run fn-bs-k0i-run-pre-init-p fn-bs-k0i-steps-inputp)
                           (fn-bs-step fn-bs-k0i-pre-init-relation fn-bs-k0i-step-inputp)))
          ("Subgoal *1/2" :use ((:instance fn-bs-k0i-step-preserves-pre-init (step (car steps))
                                 (outcome (if (consp outcomes) (car outcomes) :ok))))
           :in-theory (e/d (fn-bs-run fn-bs-k0i-run-pre-init-p fn-bs-k0i-steps-inputp)
                           (fn-bs-step fn-bs-k0i-pre-init-relation fn-bs-k0i-step-inputp fn-bs-k0i-step-preserves-pre-init)))))
(defun fn-bs-k0i-current-init-prefix (config config-record config-stage record-stage)
  (declare (xargs :guard t :verify-guards nil))
  (append (take 18 (fn-bsi-current-init-program config config-record nil config-stage record-stage nil))
          (fn-bsi-publish-steps "init-config-" config-stage :root *fn-bs-config-name* config)
          (fn-bsi-publish-steps "init-history-" record-stage :config *fn-bsi-config-record-name* config-record)
          (list (list :fsync-dir :config) (list :cut "init-config-history-fenced"))))
(defthm fn-bs-k0i-current-init-program-splits
  (equal (fn-bsi-current-init-program config config-record frontier config-stage record-stage frontier-stage)
         (append (fn-bs-k0i-current-init-prefix config config-record config-stage record-stage)
                 (fn-bsi-publish-steps "init-frontier-" frontier-stage :root *fn-bs-frontier-name* frontier)
                 (fn-bsi-final-fences)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bsi-current-init-program fn-bs-k0i-current-init-prefix))))
(defthm fn-bs-k0i-empty-store-is-pre-init
  (fn-bs-k0i-pre-init-relation *fn-bs-empty-store* (fn-sf-initial-state)))
(defthm fn-bs-k0i-current-init-prefix-keeps-pre-init
  (fn-bs-k0i-run-pre-init-p
   (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
              (fn-bs-k0i-current-init-prefix config config-record config-stage record-stage)
              outcomes groups capacity))
  :hints (("Goal" :use ((:instance fn-bs-k0i-run-keeps-pre-init (bs *fn-bs-empty-store*) (ks (fn-sf-initial-state))
                         (steps (fn-bs-k0i-current-init-prefix config config-record config-stage record-stage))))
           :in-theory (e/d (fn-bs-k0i-current-init-prefix fn-bsi-current-init-program fn-bsi-publish-steps
                            fn-bs-k0i-steps-inputp fn-bs-k0i-step-inputp)
                           (fn-bs-run fn-bs-k0i-run-pre-init-p fn-bs-k0i-run-keeps-pre-init fn-bs-k0i-pre-init-relation)))))
(defthm fn-bs-k0i-existing-config-publication-keeps-pre-init
  (implies (fn-bs-k0i-pre-init-relation bs ks)
           (fn-bs-k0i-run-pre-init-p
            (fn-bs-run bs ks (fn-bsi-publish-existing-steps label stage :root *fn-bs-config-name* octets)
                       outcomes groups capacity)))
  :hints (("Goal" :use ((:instance fn-bs-k0i-run-keeps-pre-init
                         (steps (fn-bsi-publish-existing-steps label stage :root *fn-bs-config-name* octets))))
           :in-theory (e/d (fn-bsi-publish-existing-steps fn-bs-k0i-steps-inputp fn-bs-k0i-step-inputp)
                           (fn-bs-run fn-bs-k0i-run-pre-init-p fn-bs-k0i-run-keeps-pre-init fn-bs-k0i-pre-init-relation)))))
