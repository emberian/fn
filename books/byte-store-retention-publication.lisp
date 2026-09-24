; K0: the actual ACL2-authored retention event passes through the same
; immutable Store frame, transaction name, and P-RECORD byte program as an
; article.  The publication theorem below does not assume record-inputp.
(in-package "ACL2")
(include-book "store-retention-codec-invariants")
(include-book "byte-store-record-provenance")
(include-book "byte-store-record-fence")

(local
 (defthm fn-bsrp-retention-is-a-store-event
   (implies (fn-store-retention-event-p event)
            (fn-store-event-p event))
   :hints (("Goal" :in-theory (enable fn-store-event-p)))))

(local
 (defthm fn-bsrp-retention-encoding-is-canonical
   (implies (fn-store-retention-event-p event)
            (equal (fn-store-event-encode event)
                   (fn-store-retention-event-encode event)))
   :hints (("Goal" :use fn-srci-retention-is-not-article
            :in-theory (e/d (fn-store-event-encode)
                            (fn-record-p fn-store-retention-event-p))))))

(local
 (defthm fn-bsrp-retention-payload-fits-frame
   (implies (fn-store-retention-event-p event)
            (and (fn-cbor-octet-listp (fn-store-event-encode event))
                 (fn-cbor-at-mostp (fn-store-event-encode event)
                                   *fn-frame-max-store-payload*)))
   :hints (("Goal" :do-not-induct t
            :use (fn-bsrp-retention-encoding-is-canonical
                  fn-srci-retention-encoding-is-octets
                  fn-srci-retention-encoding-bounded
                  (:instance fn-cbor-octet-listp-implies-true-listp
                   (xs (fn-store-retention-event-encode event)))
                  (:instance fn-cbor-at-mostp-from-length
                   (xs (fn-store-retention-event-encode event))
                   (bound *fn-frame-max-store-payload*)))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(natp))))))

(defthm fn-bsrp-retention-host-arguments-are-typed-record-input
  (implies (and (fn-store-retention-event-p event)
                (equal (fn-sf-phase ks) :record-staged)
                (equal (fn-sf-record-candidate ks) event)
                (fn-bs-namep stage))
           (fn-bs-record-inputp
            ks stage
            (fn-bs-txn-name (fn-store-event-sequence event))
            (append
             (fn-frame-store-protected (fn-store-event-encode event))
             (fn-frame-trailer
              (fn-frame-store-protected (fn-store-event-encode event))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bsrp-retention-payload-fits-frame
                 fn-bsrp-retention-is-a-store-event
                 fn-srci-store-retention-event-round-trip
                 (:instance fn-bs-k0-host-frame-is-octets
                  (payload (fn-store-event-encode event)))
                 (:instance fn-bs-k0-host-frame-decodes-event
                  (payload (fn-store-event-encode event))))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-record-of-octets fn-store-event-encode
                            fn-store-event-decode-exact
                            fn-frame-store-protected fn-frame-trailer)))))

(defthm fn-bsrp-retention-host-arguments-reach-related-attempted-cut
  (implies
   (and (fn-bs-store-relation bs ks)
        (fn-store-retention-event-p event)
        (equal (fn-sf-phase ks) :record-staged)
        (equal (fn-sf-record-candidate ks) event)
        (fn-bs-namep stage)
        (not (fn-bs-lookup bs :staging stage)))
   (let ((payload (fn-store-event-encode event))
         (name (fn-bs-txn-name (fn-store-event-sequence event))))
     (let ((frame (append
                   (fn-frame-store-protected payload)
                   (fn-frame-trailer (fn-frame-store-protected payload)))))
       (fn-bs-store-relation
        (car (nth 10 (fn-bs-run bs ks
                                (fn-bs-record-program stage name frame)
                                nil groups capacity)))
        (cdr (nth 10 (fn-bs-run bs ks
                                (fn-bs-record-program stage name frame)
                                nil groups capacity)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bsrp-retention-host-arguments-are-typed-record-input
                 (:instance fn-bs-k0-record-attempted-cut-establishes-relation
                  (frame (append
                          (fn-frame-store-protected (fn-store-event-encode event))
                          (fn-frame-trailer
                           (fn-frame-store-protected (fn-store-event-encode event)))))
                  (name (fn-bs-txn-name (fn-store-event-sequence event)))))
           :in-theory (theory 'minimal-theory))))

; A failing transaction-directory fsync is step 12 of the actual native
; P-RECORD sequence.  The interpreter stops before the :record-dir callback;
; native fnn-publish reports :error and returns an uncertain outcome.
(defun fn-bsrp-record-dir-error-outcomes (choice)
  (append '(:ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok)
          (list (list :eio choice))))

(local
 (defthm fn-bsrp-fsync-dir-eio-result
   (equal (mv-nth 0 (fn-bs-fsync-dir s :transactions
                                   (list :eio choice)))
          :eio)
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir)))))

(local
 (defthm fn-bsrp-fsync-dir-apply-is-fence
   (implies (equal (fn-bs-ops-for-dir (fn-bs-pending s) :transactions)
                   (list (list :set-entry :transactions name ino)))
            (equal (mv-nth 1 (fn-bs-fsync-dir s :transactions
                                             '(:eio :apply)))
                   (fn-bs-fence-dir s :transactions)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                               fn-bs-crash-select)))))

(local
 (defthm fn-bsrp-drop-selects-no-directory-ops
   (equal (fn-bs-crash-select (fn-bs-ops-for-dir ops dir)
                              '(:drop) unit)
          nil)
   :hints (("Goal" :induct (fn-bs-ops-for-dir ops dir)
            :in-theory (enable fn-bs-ops-for-dir fn-bs-crash-select)))))

(local
 (defthm fn-bsrp-fsync-dir-drop-keeps-durable-entry
   (equal (fn-bs-durable-entry
           (mv-nth 1 (fn-bs-fsync-dir s :transactions '(:eio :drop)))
           :transactions name)
          (fn-bs-durable-entry s :transactions name))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-bs-fsync-dir fn-bs-crash-select
                               fn-bs-durable-entry fn-bs-apply-ops)))))

(local
 (defthm fn-bsrp-fsync-dir-drop-keeps-durable-tables
   (and (equal (fn-bs-inodes
                (mv-nth 1 (fn-bs-fsync-dir s :transactions '(:eio :drop))))
               (fn-bs-inodes s))
        (equal (fn-bs-dirs
                (mv-nth 1 (fn-bs-fsync-dir s :transactions '(:eio :drop))))
               (fn-bs-dirs s)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-bs-fsync-dir fn-bs-apply-ops)))))

(local
 (defthm fn-bsrp-fsync-dir-eio-quiets-transactions
   (fn-bs-dir-quietp
    (mv-nth 1 (fn-bs-fsync-dir s :transactions (list :eio choice)))
    :transactions)
   :hints (("Goal"
            :use ((:instance fn-bs-ops-for-dir-of-ops-not-for-dir
                   (ops (fn-bs-pending s)) (dir :transactions)))
            :in-theory (enable fn-bs-fsync-dir fn-bs-dir-quietp)))))

(defthm fn-bsrp-record-dir-eio-run-has-actual-failed-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ok-run (fn-bs-run bs ks
                                      (fn-bs-record-program stage name frame)
                                      nil groups capacity))
                  (error-run (fn-bs-run bs ks
                                         (fn-bs-record-program stage name frame)
                                         (fn-bsrp-record-dir-error-outcomes choice)
                                         groups capacity))
                  (attempt (nth 10 ok-run))
                  (failed (nth 11 error-run)))
             (and (equal (len error-run) 12)
                  (equal (nth 10 error-run) attempt)
                  (equal (car failed)
                         (mv-nth 1 (fn-bs-fsync-dir (car attempt)
                                                    :transactions
                                                    (list :eio choice))))
                  (equal (cdr failed) (cdr attempt)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bsrp-fsync-dir-eio-result
                  (s (car (nth 10
                               (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity)))))
                 fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                 fn-bs-k0-record-attempted-cut-establishes-relation)
           :in-theory (e/d (fn-bsrp-record-dir-error-outcomes
                            fn-bs-record-program fn-bs-run fn-bs-step)
                           (fn-bs-statep fn-bs-store-relation
                            fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-link fn-bs-fsync-dir fn-bs-lookup
                            fn-bs-fence-file fn-bs-fence-dir)))))

(local
 (defthm fn-bsrp-attempted-cut-is-record-attempted
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (fn-sf-phase
                    (cdr (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity))))
                   :record-attempted))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                  fn-bs-store-relation-unfolds
                  (:instance fn-sf-record-file-result-preserves-state
                   (s ks) (result :ok))
                  (:instance fn-sf-record-link-result-preserves-state
                   (s (fn-sf-record-file-result ks :ok)) (result :ok)))
            :in-theory (e/d (fn-bs-record-inputp
                             fn-sf-record-file-result
                             fn-sf-record-link-result)
                            (fn-bs-run fn-bs-record-program
                             fn-bs-store-relation fn-sf-statep))))))

(defthm fn-bsrp-record-directory-eio-applied-cut-fences-related-attempt
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ok-run (fn-bs-run bs ks
                                      (fn-bs-record-program stage name frame)
                                      nil groups capacity))
                  (attempt (nth 10 ok-run))
                  (run (fn-bs-run bs ks
                                  (fn-bs-record-program stage name frame)
                                  (fn-bsrp-record-dir-error-outcomes :apply)
                                  groups capacity))
                  (failed (nth 11 run)))
             (and (equal (len run) 12)
                  (fn-bs-store-relation (car failed) (cdr attempt))
                  (equal (fn-bs-durable-records (car failed))
                         (append (fn-bs-durable-records (car attempt))
                                 (list (fn-sf-record-candidate (cdr attempt)))))
                  (fn-bs-dir-quietp (car failed) :transactions)
                  (fn-sf-fencedp
                   (fn-sf-record-dir-result (cdr failed) :error)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bsrp-record-dir-eio-run-has-actual-failed-cut
                  (choice :apply))
                 fn-bsrp-attempted-cut-is-record-attempted
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k0-attempted-cut-has-one-issued-transaction-link
                 (:instance fn-bs-store-relation-unfolds
                  (bs (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bsrp-fsync-dir-apply-is-fence
                  (s (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (ino (fn-bs-next-ino bs)))
                 (:instance fn-bsrp-fsync-dir-eio-quiets-transactions
                  (s (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (choice :apply))
                 (:instance fn-bs-k8-pending-link-fence-preserves-relation
                  (bs (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bs-k8-pending-link-fence-durable-records
                  (bs (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))))
           :in-theory (e/d (fn-sf-record-dir-result fn-sf-fencedp)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-fsync-dir
                            fn-bs-durable-records fn-bs-fence-dir
                            fn-bs-lookup fn-sf-statep fn-bs-dir-quietp)))))

(defthm fn-bsrp-record-directory-eio-dropped-cut-keeps-old-prefix-and-fences
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ok-run (fn-bs-run bs ks
                                      (fn-bs-record-program stage name frame)
                                      nil groups capacity))
                  (attempt (nth 10 ok-run))
                  (run (fn-bs-run bs ks
                                  (fn-bs-record-program stage name frame)
                                  (fn-bsrp-record-dir-error-outcomes :drop)
                                  groups capacity))
                  (failed (nth 11 run)))
             (and (equal (len run) 12)
                  (equal (fn-bs-durable-records (car failed))
                         (fn-bs-durable-records (car attempt)))
                  (equal (fn-bs-durable-entry (car failed)
                                              :transactions name)
                         (fn-bs-durable-entry (car attempt)
                                              :transactions name))
                  (fn-bs-dir-quietp (car failed) :transactions)
                  (fn-sf-fencedp
                   (fn-sf-record-dir-result (cdr failed) :error)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bsrp-record-dir-eio-run-has-actual-failed-cut
                  (choice :drop))
                 fn-bsrp-attempted-cut-is-record-attempted
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 (:instance fn-bs-store-relation-unfolds
                  (bs (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bsrp-fsync-dir-drop-keeps-durable-tables
                  (s (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bs-k0-same-transaction-tables-durable-records
                  (a (mv-nth 1 (fn-bs-fsync-dir
                                (car (nth 10 (fn-bs-run bs ks
                                                            (fn-bs-record-program stage name frame)
                                                            nil groups capacity)))
                                :transactions '(:eio :drop))))
                  (b (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bsrp-fsync-dir-drop-keeps-durable-entry
                  (s (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
                 (:instance fn-bsrp-fsync-dir-eio-quiets-transactions
                  (s (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity))))
                  (choice :drop)))
           :in-theory (e/d (fn-sf-record-dir-result fn-sf-fencedp)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-fsync-dir
                            fn-bs-durable-records fn-bs-fence-dir
                            fn-bs-lookup fn-sf-statep fn-bs-dir-quietp)))))
