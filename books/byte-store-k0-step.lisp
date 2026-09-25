; fn: the general per-step K0 (T16's model side, lane k0-general-step).
;
; fn-bs-step-preserves-k0-coverage: from any byte state COVERED by the
; kernel (related to it, or a pending committed-history rename both of whose
; resolutions are related, fn-bs-k0-coveredp), any step of the byte language
; whose precondition fn-bs-k0-step-inputp holds, with ANY outcome the
; environment chooses, leaves a covered pair; a syscall leaves the kernel as
; it was, an observation moves it to its successor.  Every crash image of a
; covered state is a crash image of a related state
; (fn-bs-k0-covered-crash-image-is-a-related-image), so every crash image
; after the step is related to the kernel or to its successor.  A program
; built from these steps is covered at every cut by construction: the cut is
; the identity (fn-bs-k0c-cut-step-is-identity).
;
; Step kinds covered and the precondition each needs (all outside the
; recovery window, (not (fn-bs-replay-visiblep ks))):
;   :cut          none beyond coverage.
;   :create       dir :staging, a typed name; any outcome.
;   :write-all    typed octets; the target inode is not an authority inode
;                 (D2); any outcome (a short write is its prefix's write).
;   :fsync-file   the target is a natural, non-authority inode, no pending
;                 :root or :transactions entry; :ok or a well-formed crash
;                 selection of that file's writes.
;   :fsync-dir    :staging with :ok; :transactions with :ok in phase
;                 :record-attempted with the link pending (the record
;                 barrier); :root over a pending marker rename, any outcome
;                 (lands or drops it).
;   :unlink       outside :root and :transactions; any outcome.
;   :rename       :staging to the committed-history marker name, root quiet,
;                 source present: covered, any outcome; :staging to the
;                 allocation frontier, root and transactions quiet, source
;                 fenced and allocated and decoding to the kernel's frontier
;                 candidate, kernel in a frontier-new-visible phase with
;                 durable frontier and records its own: related, any outcome.
;   :link         :staging to the next transaction name, transactions quiet,
;                 source fenced and allocated and reading as the kernel's
;                 record candidate, kernel record-present-visible with
;                 durable records its own; any outcome.
;   :observe      the frontier observations that claim no commit, the record
;                 program's (:record-file :ok) and (:record-link :ok), the
;                 record link and record directory error arms, core completion
;                 and emit success; (:record-dir :ok) and (:frontier-dir :ok)
;                 with their directory-committed premise.
; The step precondition carries the relation (or, for the root barrier, the
; marker-pending coverage), so the theorem has no separate coverage
; hypothesis.
; NOT covered, named: :mkdir and :link-eexist (initialization only; the init
; program has its own theorem), the error outcomes of the :staging and
; :transactions barriers, the root barrier over a pending frontier rename,
; and every step in the recovery window.  The per-cut theorems that follow
; from this one are in byte-store-k0-step-bridge.
(in-package "ACL2")
(include-book "byte-store-k0-step-lemmas")

(defthm fn-bs-k0s-covered-of-relation
  (implies (fn-bs-store-relation bs ks) (fn-bs-k0-coveredp bs ks))
  :hints (("Goal" :in-theory '(fn-bs-k0-coveredp))))
; The record program's two :ok observations (lane k0-corollaries): each moves
; the kernel between two phases whose crash images and pending-entry
; conditions agree, so neither needs a byte-state premise.
(defthm fn-sf-record-file-result-ok-preserves-store-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-record-file-result ks :ok)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-record-file-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-sf-record-link-result-ok-preserves-store-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-record-link-result ks :ok)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-link-result-preserves-state (s ks) (result :ok)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-record-link-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defun fn-bs-k0-observation-inputp (bs ks event)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-bs-frontier-noncommit-observationp event)
      (member-equal event '((:record-file :ok) (:record-link :ok) (:record-link :error) (:record-dir :error)))
      (and (consp event) (member-equal (car event) '(:core-completion :emit-success)))
      (and (equal event '(:record-dir :ok))
           (equal (fn-sf-phase ks) :record-attempted)
           (fn-bs-record-directory-committedp bs ks))
      (and (equal event '(:frontier-dir :ok))
           (equal (fn-sf-phase ks) :frontier-attempted)
           (fn-bs-frontier-directory-committedp bs ks))))
(defun fn-bs-k0-step-inputp (bs ks step outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d1 (nth 1 step)) (n2 (nth 2 step)) (d3 (nth 3 step)) (n4 (nth 4 step)))
    (and
     (not (fn-bs-replay-visiblep ks))
     (case (car step)
       (:cut (fn-bs-k0-coveredp bs ks))
       (:observe (and (fn-bs-store-relation bs ks) (fn-bs-k0-observation-inputp bs ks d1)))
       (:create (and (fn-bs-store-relation bs ks) (equal d1 :staging) (fn-bs-namep n2)))
       (:write-all (and (fn-bs-store-relation bs ks) (fn-cbor-octet-listp d3)
                        (not (member-equal (fn-bs-lookup bs d1 n2) (fn-bs-authority-inode-list bs)))))
       (:fsync-file (let ((x (fn-bs-lookup bs d1 n2)))
                      (and (fn-bs-store-relation bs ks) (natp x)
                           (not (member-equal x (fn-bs-authority-inode-list bs)))
                           (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                           (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                           (or (equal outcome :ok)
                               (fn-bs-crash-choicesp (cdr outcome) (fn-bs-ops-for-ino (fn-bs-pending bs) x)
                                                     (fn-bs-unit bs))))))
       (:fsync-dir (or (and (fn-bs-store-relation bs ks) (equal d1 :staging) (equal outcome :ok))
                       (and (fn-bs-store-relation bs ks) (equal d1 :transactions) (equal outcome :ok)
                            (equal (fn-sf-phase ks) :record-attempted)
                            (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
                       (and (equal d1 :root) (fn-bs-k0s-marker-pendingp bs ks))))
       (:unlink (and (fn-bs-store-relation bs ks) (not (member-equal d1 '(:root :transactions)))))
       (:rename (and (fn-bs-store-relation bs ks) (equal d1 :staging) (equal d3 :root)
                     (let ((ino (fn-bs-lookup bs :staging n2)))
                       (or (and (equal n4 *fn-bs-history-marker-name*)
                                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                                (fn-bs-inop ino))
                           (and (equal n4 *fn-bs-frontier-name*)
                                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                                (fn-bs-namep n2) (fn-bs-inop ino) (fn-bs-fencedp bs ino)
                                (consp (assoc-equal ino (fn-bs-inodes bs)))
                                (fn-sf-frontier-new-visiblep ks)
                                (not (fn-sf-record-present-visiblep ks))
                                (equal (fn-bs-frontier-decode (fn-bs-durable-content bs ino))
                                       (fn-sf-frontier-candidate ks))
                                (equal (fn-bs-durable-frontier bs) (fn-sf-frontier ks))
                                (equal (fn-bs-durable-records bs) (fn-sf-records ks)))))))
       (:link (and (fn-bs-store-relation bs ks) (equal d1 :staging) (equal d3 :transactions)
                   (let ((ino (fn-bs-lookup bs :staging n2)))
                     (and (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                          (fn-bs-fencedp bs ino)
                          (consp (assoc-equal ino (fn-bs-inodes bs)))
                          (equal n4 (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                          (fn-sf-record-present-visiblep ks)
                          (equal (fn-bs-durable-records bs) (fn-sf-records ks))
                          (equal (fn-bs-record-of (fn-bs-durable bs) ino) (fn-sf-record-candidate ks))))))
       (otherwise nil)))))
(defthm fn-bs-k0s-observation-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-k0-observation-inputp bs ks event))
           (fn-bs-store-relation bs (fn-sf-dispatch ks event g c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-frontier-noncommit-observation-preserves-relation (outcome :ok) (groups g) (capacity c))
                 fn-sf-record-file-result-ok-preserves-store-relation fn-sf-record-link-result-ok-preserves-store-relation
                 fn-bs-record-link-error-preserves-relation fn-bs-record-dir-error-preserves-relation
                 fn-bs-record-directory-commit-observation-preserves-relation
                 fn-bs-frontier-directory-commit-observation-preserves-relation
                 (:instance fn-bs-core-completion-preserves-relation (sequence (cadr event)) (txid (caddr event)))
                 (:instance fn-bs-emit-success-preserves-relation (sequence (cadr event)) (txid (caddr event))))
           :in-theory (e/d (fn-sf-dispatch) (fn-bs-store-relation fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result fn-sf-frontier-dir-result fn-sf-record-link-result fn-sf-record-file-result
                            fn-sf-record-dir-result fn-sf-core-completion fn-sf-emit-success
                            fn-bs-record-directory-committedp fn-bs-frontier-directory-committedp)))))
(defthm fn-bs-k0s-step-create-covered
  (implies (and (equal (car step) :create) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-create-preserves-relation (b bs) (k ks) (stage (nth 2 step))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-write-all-covered
  (implies (and (equal (car step) :write-all) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-write-preserves-relation (b bs) (k ks) (octets (nth 3 step)) (ino (fn-bs-lookup bs (nth 1 step) (nth 2 step)))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-fsync-file-covered
  (implies (and (equal (car step) :fsync-file) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-fsync-file-preserves-relation (b bs) (k ks) (x (fn-bs-lookup bs (nth 1 step) (nth 2 step)))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-fsync-dir-covered
  (implies (and (equal (car step) :fsync-dir) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0-staging-fence-preserves-relation (b bs) (k ks)) (:instance fn-bs-k8-pending-link-fence-preserves-relation) (:instance fn-bs-k0s-marker-barrier-resolves (m bs)))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation fn-bs-k0s-fsync-dir-ok-is-fence)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-unlink-covered
  (implies (and (equal (car step) :unlink) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-unlink-preserves-relation (b bs) (k ks) (dir (nth 1 step)) (name (nth 2 step))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-rename-covered
  (implies (and (equal (car step) :rename) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-marker-rename-covered (b bs) (k ks) (stage (nth 2 step))) (:instance fn-bs-k0s-frontier-rename-preserves-relation (b bs) (k ks) (stage (nth 2 step))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-k0s-step-link-covered
  (implies (and (equal (car step) :link) (fn-bs-k0-step-inputp bs ks step outcome))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :expand ((:free (o) (fn-bs-step bs ks step o groups capacity)))
           :use ((:instance fn-bs-k0s-link-preserves-relation (b bs) (k ks) (stage (nth 2 step)) (name (nth 4 step))))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed
                            fn-bs-marker-rename-dropped fn-bs-lookup fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-dir fn-bs-rename fn-bs-link fn-bs-unlink fn-bs-k0-observation-inputp
                            fn-bs-authority-inode-list fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable fn-bs-record-of fn-bs-durable-content fn-bs-durable-frontier
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped fn-bs-fence-dir fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target fn-bs-lookup))))))
(defthm fn-bs-step-preserves-k0-coverage
  (implies (fn-bs-k0-step-inputp bs ks step outcome)
           (let ((bs1 (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)))
                 (ks1 (mv-nth 2 (fn-bs-step bs ks step outcome groups capacity))))
             (and (fn-bs-k0-coveredp bs1 ks1)
                  (or (equal ks1 ks) (equal (car step) :observe)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (car step) :observe) (equal (car step) :cut) (equal (car step) :create)
                   (equal (car step) :write-all) (equal (car step) :fsync-file) (equal (car step) :fsync-dir)
                   (equal (car step) :unlink) (equal (car step) :rename) (equal (car step) :link))
           :use (fn-bs-k0s-step-create-covered fn-bs-k0s-step-write-all-covered fn-bs-k0s-step-fsync-file-covered
                 fn-bs-k0s-step-fsync-dir-covered fn-bs-k0s-step-unlink-covered fn-bs-k0s-step-rename-covered
                 fn-bs-k0s-step-link-covered
                 (:instance fn-bs-k0s-observe-step-any (g groups) (c capacity))
                 (:instance fn-bs-k0s-observation-preserves-relation (event (nth 1 step)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-cut-step-is-identity (o outcome) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-k0s-covered-of-relation)
                           (fn-bs-step fn-bs-k0-step-inputp fn-bs-k0s-observe-step fn-bs-k0c-cut-step-is-identity
                            fn-bs-store-relation fn-bs-k0-coveredp fn-sf-dispatch fn-bs-k0-observation-inputp)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-k0s-covered-of-relation fn-bs-k0-step-inputp)
                           (fn-bs-step fn-bs-k0s-observe-step fn-bs-k0c-cut-step-is-identity
                            fn-bs-store-relation fn-bs-k0-coveredp fn-sf-dispatch fn-bs-k0-observation-inputp
                            fn-bs-k0s-marker-pendingp fn-bs-lookup fn-bs-authority-inode-list))))))
