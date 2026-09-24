; K0 byte provenance through the configured owner: books/byte-store-record-provenance
; includes this book after its byte-store and Store-node parts.
(in-package "ACL2")
(include-book "byte-store-record-provenance-node")
(local (in-theory (enable fn-bs-k6-created-stage-lookup-without-namep
                           fn-bs-k6-fresh-create-returns-ok
                           fn-bs-k6-write-created-inode-returns-ok-without-namep
                           fn-bs-k6-write-keeps-lookup
                           fn-bs-k6-lookup-is-entry-after
                           fn-bs-k6-file-fence-keeps-valid-name-lookup
                           fn-bs-k6-created-stage-lookup
                           fn-bs-k0-append-associative
                           fn-bs-k6-empty-true-list
                           fn-bs-k6-state-next-ino-is-fenced
                           fn-bs-k6-take-all
                           fn-bs-k0-durable-state-content-is-durable-content
                           fn-bs-k6-filter-inode-writes-keeps-dir-ops
                           fn-bs-k6-file-fence-pending-is-filter
                           fn-bs-k6-filter-writes-keeps-entry-after
                           fn-bs-k0-all-fencedp-append
                           fn-bs-k0-inode-list-knownp-append
                           fn-bs-k0-frontier-rename-returns-ok)))

; The shared native service binds fnn-observe to fnn-owner-observe
; (host/native/owner.lisp:718).  It calls the program-mode fn-owner-io
; (host/owner-host.lisp:299), which submits exactly this event through
; fn-ocfg-step.  Expose the Store-node projection of that called path.
(include-book "owner-config")
(include-book "owner-invariants")

(defthm fn-bs-k0-owner-io-store-is-node-io
  (equal (fn-own-store
          (fn-ocfg-owner
           (fn-ocfg-step oc (list :store (list :io operation result)))))
         (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-ocfg-with-owner
                            fn-own-step fn-own-store-step fn-snrt-step
                            fn-snt-step fn-own-refresh-keeps-fields)
                           (fn-own-refresh fn-sn-io fn-ocfg-make
                            fn-own-make)))))

(defthm fn-bs-k0-owner-frontier-calls-match-byte-run
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :ok))))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file-pair (nth 12 run))
          (return-pair (nth 14 run)))
     (and (equal (fn-sn-files (fn-own-store (fn-ocfg-owner oc3)))
                 (cdr file-pair))
          (equal (car return-pair) (car file-pair))
          (equal (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))
                 (cdr return-pair))
          (fn-bs-store-relation
           (car return-pair)
           (fn-sn-files (fn-own-store (fn-ocfg-owner oc4))))
          (equal (fn-sf-phase
                  (fn-sn-files (fn-own-store (fn-ocfg-owner oc4))))
                 :reserved))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-native-call-sequence-matches-run
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory (union-theories
                       '(fn-bs-k0-owner-io-store-is-node-io)
                       (theory 'minimal-theory)))))

; P-FRONTIER's root-directory fsync can report EIO after the queued
; replacement has landed.  The host observes :frontier-directory :error and
; returns an indeterminate, fenced result; it does not acknowledge the new
; durable frontier.  This schedule chooses :apply explicitly.  :drop is also
; physically legal and is witnessed in the test book; neither syscall error
; nor this theorem implies a particular recovered frontier.
(defun fn-bs-k0-root-error-outcomes (choice)
  (declare (xargs :guard t :verify-guards nil))
  (list :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok
        (list :eio choice)))

(local
 (defthm fn-bs-k0-root-eio-apply-is-fence
   (implies (and (equal (fn-bs-ops-for-dir (fn-bs-pending b) :root)
                        (list op))
                 (not (equal (car op) :write)))
            (equal (mv-nth 1 (fn-bs-fsync-dir b :root '(:eio :apply)))
                   (fn-bs-fence-dir b :root)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                               fn-bs-crash-select)))))

(local
 (defthm fn-bs-k0-frontier-root-eio-apply-is-successful-byte-fence
   (implies (and (fn-bs-dir-quietp file :root)
                 (fn-bs-inop (fn-bs-lookup file :staging stage)))
            (equal
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root '(:eio :apply)))
             (fn-bs-fence-dir
              (mv-nth 1 (fn-bs-rename file :staging stage :root
                                      *fn-bs-frontier-name* :ok)) :root)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-root-eio-apply-is-fence
                              (b (mv-nth 1 (fn-bs-rename file :staging stage
                                                          :root *fn-bs-frontier-name* :ok)))
                              (op (list :set-entry :root *fn-bs-frontier-name*
                                        (fn-bs-lookup file :staging stage)))))
            :in-theory (e/d (fn-bs-rename fn-bs-ops-for-dir-of-append
                             fn-bs-dir-quietp)
                            (fn-bs-fsync-dir fn-bs-fence-dir fn-bs-lookup))))))

(local
 (defthm fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                                   nil groups capacity))
                   (file (car (nth 6 run))))
              (equal (mv-nth 1
                      (fn-bs-fsync-dir
                       (mv-nth 1 (fn-bs-rename file :staging stage :root
                                               *fn-bs-frontier-name* :ok))
                       :root '(:eio :apply)))
                     (car (nth 12 run)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-file-cut-authority-quiet
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-observation-source-is-new-inode
                  fn-bs-k0-frontier-dir-cut-is-fence
                  (:instance fn-bs-k6-state-next-ino-is-inop)
                  (:instance fn-bs-k0-frontier-root-eio-apply-is-successful-byte-fence
                   (file (car (nth 6 (fn-bs-run bs ks
                                (fn-bs-frontier-program stage octets)
                                nil groups capacity))))))
            :in-theory (e/d (fn-bs-dir-quietp fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program fn-bs-statep
                             fn-bs-store-relation fn-bs-lookup fn-bs-fsync-dir
                             fn-bs-rename fn-bs-fence-dir fn-bs-inop))))))

(defthm fn-bs-k0-frontier-node-root-eio-applied-fences-related-state
  (implies
   (and (fn-sn-statep s)
        (fn-bs-store-relation bs (fn-sn-files s))
        (fn-bs-frontier-inputp (fn-sn-files s) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((ks (fn-sn-files s))
          (run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file (car (nth 6 run)))
          (failed (mv-nth 1 (fn-bs-fsync-dir
                             (mv-nth 1 (fn-bs-rename file :staging stage
                                                     :root *fn-bs-frontier-name* :ok))
                             :root '(:eio :apply))))
          (s3 (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                      :frontier-file :ok)
                        :frontier-replace :ok))
          (s4 (fn-sn-io s3 :frontier-directory :error)))
     (and (equal failed (car (nth 12 run)))
          (fn-bs-store-relation failed (fn-sn-files s4))
          (equal (fn-sf-phase (fn-sn-files s4)) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-sf-frontier-candidate (fn-sn-files s3))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-native-call-sequence-matches-run)
                 (:instance fn-bs-k0-frontier-dir-cut-establishes-relation
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-dir-cut-committedp
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-frontier-dir-error-preserves-relation
                  (bs (car (nth 12 (fn-bs-run bs (fn-sn-files s)
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity))))
                  (ks (cdr (nth 12 (fn-bs-run bs (fn-sn-files s)
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity)))))
                 (:instance fn-bs-native-io-is-byte-observation
                  (s (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                       :frontier-file :ok)
                                 :frontier-replace :ok))
                  (operation :frontier-directory) (result :error))
                 (:instance fn-sn-io-preserves-state
                  (operation :start-frontier) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io s :start-frontier :ok))
                  (operation :frontier-file) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io (fn-sn-io s :start-frontier :ok)
                               :frontier-file :ok))
                  (operation :frontier-replace) (result :ok)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-frontier-dir-result fn-sf-fencedp)
                           (fn-bs-run fn-bs-frontier-program fn-sn-io
                            fn-bs-store-relation fn-bs-durable-frontier)))))

(defthm fn-bs-k0-frontier-eio-applied-run-has-actual-failed-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (car (nth 12
                  (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                             (fn-bs-k0-root-error-outcomes :apply)
                             groups capacity)))
            (car (nth 12
                  (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                             nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-replace-cut-is-rename
                 fn-bs-k0-frontier-rename-returns-ok
                 fn-bs-k0-frontier-file-observation-source-is-new-inode)
           :in-theory (e/d (fn-bs-k0-root-error-outcomes
                            fn-bs-frontier-program fn-bs-run fn-bs-step)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-rename fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup
                            fn-bs-statep fn-bs-store-relation)))))

(local
 (defthm fn-bs-k0-owner-frontier-root-eio-applied-fences-related-state
   (implies
    (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
         (fn-bs-store-relation bs
                               (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
         (fn-bs-frontier-inputp
          (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
         (not (fn-bs-lookup bs :staging stage)))
    (let* ((s (fn-own-store (fn-ocfg-owner oc)))
           (run (fn-bs-run bs (fn-sn-files s)
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))
           (file (car (nth 6 run)))
           (renamed (mv-nth 1 (fn-bs-rename file :staging stage :root
                                             *fn-bs-frontier-name* :ok)))
           (result (mv-nth 0 (fn-bs-fsync-dir renamed :root '(:eio :apply))))
           (failed (mv-nth 1 (fn-bs-fsync-dir renamed :root '(:eio :apply))))
           (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
           (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
           (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
           (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
           (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
           (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
      (and (equal result :eio)
           (equal failed (car (nth 12 run)))
           (fn-bs-store-relation failed k4)
           (equal (fn-sf-phase k4) :fenced-frontier)
           (equal (fn-bs-durable-frontier failed)
                  (fn-sf-frontier-candidate k3)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-frontier-node-root-eio-applied-fences-related-state
                   (s (fn-own-store (fn-ocfg-owner oc)))))
            :in-theory (union-theories
                        '(fn-bs-k0-owner-io-store-is-node-io fn-bs-fsync-dir)
                        (theory 'minimal-theory))))))

; The public K0 error bridge names the actual owner callback and the actual
; failing byte-program cut.  It promises a recovery fence, not reservation.
(defthm fn-bs-k0-owner-frontier-root-eio-applied-run-fences-related-state
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          (fn-bs-k0-root-error-outcomes :apply)
                          groups capacity))
          (failed (car (nth 12 run)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
          (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
          (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
     (and (fn-bs-store-relation failed k4)
          (equal (fn-sf-phase k4) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-sf-frontier-candidate k3)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-owner-frontier-root-eio-applied-fences-related-state)
                 (:instance fn-bs-k0-frontier-eio-applied-run-has-actual-failed-cut
                  (ks (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           :in-theory (theory 'minimal-theory))))

; The other legal outcome of the single pending root entry leaves the old
; durable directory intact.  The source-directory deletion is still pending;
; the error does not turn it into a successful frontier publication.
(local
 (defthm fn-bs-k0-ops-not-for-dir-when-quiet
   (implies (and (true-listp ops)
                 (not (fn-bs-ops-for-dir ops dir)))
            (equal (fn-bs-ops-not-for-dir ops dir) ops))
   :hints (("Goal" :induct (fn-bs-ops-for-dir ops dir)
            :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))

(local
 (defthm fn-bs-k0-ops-not-for-dir-of-append
   (equal (fn-bs-ops-not-for-dir (append a b) dir)
          (append (fn-bs-ops-not-for-dir a dir)
                  (fn-bs-ops-not-for-dir b dir)))
   :hints (("Goal" :induct (len a)
            :in-theory (enable fn-bs-ops-not-for-dir)))))

(local
 (defthm fn-bs-k0-root-eio-drop-after-rename
   (implies (and (fn-bs-statep file)
                 (fn-bs-inop (fn-bs-lookup file :staging stage))
                 (equal (fn-bs-ops-for-dir (fn-bs-pending file) :root) nil))
            (equal
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root '(:eio :drop)))
             (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                         (fn-bs-dirs file)
                         (append (fn-bs-pending file)
                                 (list (list :del-entry :staging stage)))
                         (fn-bs-next-ino file))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-op-listp-implies-true-listp
                             (x (fn-bs-pending file))))
            :in-theory (e/d (fn-bs-rename fn-bs-fsync-dir
                              fn-bs-crash-select fn-bs-apply-ops
                              fn-bs-ops-for-dir-of-append
                              fn-bs-k0-ops-not-for-dir-of-append
                              fn-bs-k0-ops-not-for-dir-when-quiet
                              fn-bs-ops-not-for-dir fn-bs-statep)
                            (fn-bs-lookup fn-bs-inop))))))

(local
 (defthm fn-bs-k0-staging-delete-keeps-fencedp
   (equal (fn-bs-fencedp
           (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                       (fn-bs-dirs file)
                       (append (fn-bs-pending file)
                               (list (list :del-entry :staging stage)))
                       (fn-bs-next-ino file)) ino)
          (fn-bs-fencedp file ino))
   :hints (("Goal" :in-theory (enable fn-bs-fencedp fn-bs-ops-for-ino-of-append
                                     fn-bs-ops-for-ino)))))

(local
 (defthm fn-bs-k0-staging-delete-keeps-all-fencedp
   (equal (fn-bs-all-fencedp
           (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                       (fn-bs-dirs file)
                       (append (fn-bs-pending file)
                               (list (list :del-entry :staging stage)))
                       (fn-bs-next-ino file)) xs)
          (fn-bs-all-fencedp file xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-all-fencedp)))))

(local
 (defthm fn-bs-k0-staging-delete-keeps-known-list
   (equal (fn-bs-inode-list-knownp
           (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                       (fn-bs-dirs file)
                       (append (fn-bs-pending file)
                               (list (list :del-entry :staging stage)))
                       (fn-bs-next-ino file)) xs)
          (fn-bs-inode-list-knownp file xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-inode-list-knownp)))))

(local
 (defthm fn-bs-k0-related-authority-known
   (implies (fn-bs-store-relation file k)
            (fn-bs-authority-knownp file))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-store-relation)))))

(local
 (defthm fn-bs-k0-staging-delete-transports-relation
   (implies (and (fn-bs-store-relation file k)
                 (not (fn-bs-replay-visiblep k))
                 (fn-bs-namep stage)
                 (equal (fn-bs-ops-for-dir (fn-bs-pending file) :root) nil)
                 (equal (fn-bs-ops-for-dir (fn-bs-pending file) :transactions) nil)
                 (fn-bs-statep
                  (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                              (fn-bs-dirs file)
                              (append (fn-bs-pending file)
                                      (list (list :del-entry :staging stage)))
                              (fn-bs-next-ino file))))
            (fn-bs-store-relation
             (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                         (fn-bs-dirs file)
                         (append (fn-bs-pending file)
                                 (list (list :del-entry :staging stage)))
                         (fn-bs-next-ino file))
             k))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-store-relation-unfolds (bs file) (ks k))
                  (:instance fn-bs-k0-related-authority-known
                   (file file) (k k))
                  (:instance fn-bs-k0-same-transaction-tables-durable-records
                   (a file)
                   (b (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                                  (fn-bs-dirs file)
                                  (append (fn-bs-pending file)
                                          (list (list :del-entry :staging stage)))
                                  (fn-bs-next-ino file))))
                  (:instance fn-bs-k0-quiet-projection-transports-relation
                   (bs file)
                   (file (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                                     (fn-bs-dirs file)
                                     (append (fn-bs-pending file)
                                             (list (list :del-entry :staging stage)))
                                     (fn-bs-next-ino file)))))
            :in-theory (e/d (fn-bs-ops-for-dir-of-append
                              fn-bs-k0-pending-entry-targets-of-append
                              fn-bs-ops-for-ino-of-append
                              fn-bs-authority-inode-list
                              fn-bs-authority-fencedp
                              fn-bs-authority-knownp
                              fn-bs-pending-entry-targets
                              fn-bs-all-fencedp fn-bs-inode-list-knownp
                              fn-bs-fencedp fn-bs-durable-entry
                              fn-bs-durable-content fn-bs-durable-frontier)
                            (fn-bs-store-relation fn-bs-durable-records))))))

(local
 (defthm fn-bs-k0-root-eio-drop-preserves-statep
   (implies (and (fn-bs-statep file)
                 (fn-bs-namep stage)
                 (fn-bs-inop (fn-bs-lookup file :staging stage))
                 (equal (fn-bs-ops-for-dir (fn-bs-pending file) :root) nil))
            (fn-bs-statep
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root '(:eio :drop)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-rename-preserves-statep
                             (s file) (sdir :staging) (sname stage)
                             (ddir :root) (dname *fn-bs-frontier-name*)
                             (outcome :ok))
                  (:instance fn-bs-fsync-dir-preserves-statep
                   (s (mv-nth 1 (fn-bs-rename file :staging stage :root
                                             *fn-bs-frontier-name* :ok)))
                   (dir :root) (outcome '(:eio :drop))))
            :in-theory (e/d (fn-bs-rename fn-bs-ops-for-dir-of-append
                              fn-bs-crash-choicesp fn-bs-crash-choicep)
                            (fn-bs-statep fn-bs-fsync-dir fn-bs-lookup
                             fn-bs-rename-preserves-statep
                             fn-bs-fsync-dir-preserves-statep))))))

(local
 (defthm fn-bs-k0-frontier-file-related-to-attempted-kernel
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (fn-bs-store-relation
             (car (nth 6 (fn-bs-run bs ks
                             (fn-bs-frontier-program stage octets)
                             nil groups capacity)))
             (cdr (nth 12 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-file-observation-establishes-relation
                  fn-bs-k0-frontier-file-cut-kernel-is-file-observation
                  fn-bs-k0-frontier-dir-cut-kernel-is-replace-observation
                  (:instance fn-bs-frontier-replace-result-preserves-relation
                   (bs (car (nth 6 (fn-bs-run bs ks
                                      (fn-bs-frontier-program stage octets)
                                      nil groups capacity))))
                   (ks (cdr (nth 6 (fn-bs-run bs ks
                                       (fn-bs-frontier-program stage octets)
                                       nil groups capacity))))
                   (result :ok)))
            :in-theory (disable fn-bs-run fn-bs-frontier-program
                                fn-bs-store-relation
                                fn-sf-frontier-replace-result)))))
(local
 (defthm fn-bs-k0-frontier-root-eio-drop-is-staging-delete
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((run (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity))
                   (file (car (nth 6 run))))
              (equal
               (mv-nth 1 (fn-bs-fsync-dir
                          (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                  *fn-bs-frontier-name* :ok))
                          :root '(:eio :drop)))
               (fn-bs-make (fn-bs-unit file) (fn-bs-inodes file)
                           (fn-bs-dirs file)
                           (append (fn-bs-pending file)
                                   (list (list :del-entry :staging stage)))
                           (fn-bs-next-ino file)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k6-state-next-ino-is-inop
                  fn-bs-k0-frontier-file-cut-statep
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-observation-source-is-new-inode
                  fn-bs-k0-frontier-file-cut-authority-quiet
                  (:instance fn-bs-k0-root-eio-drop-after-rename
                   (file (car (nth 6 (fn-bs-run bs ks
                                           (fn-bs-frontier-program stage octets)
                                           nil groups capacity))))))
            :in-theory (e/d (fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program fn-bs-statep
                             fn-bs-fsync-dir fn-bs-rename fn-bs-lookup))))))
(local
 (defthm fn-bs-k0-frontier-root-eio-drop-preserves-relation
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((run (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity))
                   (file (car (nth 6 run)))
                   (k3 (cdr (nth 12 run)))
                   (failed (mv-nth 1 (fn-bs-fsync-dir
                              (mv-nth 1 (fn-bs-rename file :staging stage
                                                      :root *fn-bs-frontier-name* :ok))
                              :root '(:eio :drop)))))
              (fn-bs-store-relation failed k3)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k6-state-next-ino-is-inop
                  fn-bs-k0-frontier-file-cut-statep
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-observation-source-is-new-inode
                  fn-bs-k0-frontier-file-cut-authority-quiet
                  fn-bs-k0-frontier-file-related-to-attempted-kernel
                  fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                  fn-bs-k0-frontier-root-eio-drop-is-staging-delete
                  (:instance fn-bs-k0-root-eio-drop-preserves-statep
                   (file (car (nth 6 (fn-bs-run bs ks
                                           (fn-bs-frontier-program stage octets)
                                           nil groups capacity)))))
                  (:instance fn-bs-k0-staging-delete-transports-relation
                   (file (car (nth 6 (fn-bs-run bs ks
                                           (fn-bs-frontier-program stage octets)
                                           nil groups capacity))))
                   (k (cdr (nth 12 (fn-bs-run bs ks
                                              (fn-bs-frontier-program stage octets)
                                              nil groups capacity))))))
            :in-theory (e/d (fn-bs-frontier-inputp fn-bs-replay-visiblep)
                            (fn-bs-run fn-bs-frontier-program fn-bs-statep
                             fn-bs-store-relation fn-bs-fsync-dir fn-bs-rename
                             fn-bs-lookup))))))
(local
 (defthm fn-bs-k0-frontier-root-eio-drop-keeps-old-frontier
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((run (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity))
                   (file (car (nth 6 run)))
                   (failed (mv-nth 1 (fn-bs-fsync-dir
                              (mv-nth 1 (fn-bs-rename file :staging stage
                                                      :root *fn-bs-frontier-name* :ok))
                              :root '(:eio :drop)))))
              (equal (fn-bs-durable-frontier failed)
                     (fn-bs-durable-frontier bs))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-root-eio-drop-is-staging-delete
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-cut-keeps-old-frontier)
            :in-theory (e/d (fn-bs-durable-frontier fn-bs-durable-content
                              fn-bs-durable-entry)
                            (fn-bs-run fn-bs-frontier-program fn-bs-store-relation
                             fn-bs-fsync-dir fn-bs-rename fn-bs-lookup))))))

(local
 (defthm fn-bs-k0-root-eio-choice-result-is-eio
   (equal (mv-nth 0 (fn-bs-fsync-dir b :root (list :eio choice))) :eio)
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir)))))

(defthm fn-bs-k0-frontier-eio-dropped-run-has-actual-failed-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ok-run (fn-bs-run bs ks
                                      (fn-bs-frontier-program stage octets)
                                      nil groups capacity))
                  (file (car (nth 6 ok-run)))
                  (error-run (fn-bs-run bs ks
                                         (fn-bs-frontier-program stage octets)
                                         (fn-bs-k0-root-error-outcomes :drop)
                                         groups capacity)))
             (and (equal (len error-run) 13)
                  (equal (car (nth 12 error-run))
                         (mv-nth 1 (fn-bs-fsync-dir
                                    (mv-nth 1
                                            (fn-bs-rename file :staging stage
                                                          :root *fn-bs-frontier-name* :ok))
                                    :root '(:eio :drop)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-replace-cut-is-rename
                 fn-bs-k0-frontier-rename-returns-ok
                 fn-bs-k0-frontier-file-observation-source-is-new-inode
                 fn-bs-k0-frontier-root-eio-drop-is-staging-delete
                 fn-bs-k6-state-next-ino-is-inop)
           :in-theory (e/d (fn-bs-k0-root-error-outcomes
                            fn-bs-frontier-program fn-bs-run fn-bs-step)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-rename fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup fn-bs-statep
                            fn-bs-store-relation)))))
(defthm fn-bs-k0-frontier-node-root-eio-dropped-fences-related-state
  (implies
   (and (fn-sn-statep s)
        (fn-bs-store-relation bs (fn-sn-files s))
        (fn-bs-frontier-inputp (fn-sn-files s) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((ks (fn-sn-files s))
          (run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file (car (nth 6 run)))
          (failed (mv-nth 1 (fn-bs-fsync-dir
                             (mv-nth 1 (fn-bs-rename file :staging stage
                                                     :root *fn-bs-frontier-name* :ok))
                             :root '(:eio :drop))))
          (s3 (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                      :frontier-file :ok)
                        :frontier-replace :ok))
          (s4 (fn-sn-io s3 :frontier-directory :error)))
     (and (fn-bs-store-relation failed (fn-sn-files s4))
          (equal (fn-sf-phase (fn-sn-files s4)) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-bs-durable-frontier bs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-native-call-sequence-matches-run)
                 (:instance fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-root-eio-drop-preserves-relation
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-root-eio-drop-keeps-old-frontier
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-frontier-dir-error-preserves-relation
                  (bs (mv-nth 1 (fn-bs-fsync-dir
                         (mv-nth 1 (fn-bs-rename
                          (car (nth 6 (fn-bs-run bs (fn-sn-files s)
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity)))
                          :staging stage :root *fn-bs-frontier-name* :ok))
                         :root '(:eio :drop))))
                  (ks (fn-sn-files
                       (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                             :frontier-file :ok)
                                 :frontier-replace :ok))))
                 (:instance fn-bs-native-io-is-byte-observation
                  (s (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                       :frontier-file :ok)
                                 :frontier-replace :ok))
                  (operation :frontier-directory) (result :error))
                 (:instance fn-sn-io-preserves-state
                  (operation :start-frontier) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io s :start-frontier :ok))
                  (operation :frontier-file) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io (fn-sn-io s :start-frontier :ok)
                               :frontier-file :ok))
                  (operation :frontier-replace) (result :ok)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-frontier-dir-result fn-sf-fencedp)
                           (fn-bs-run fn-bs-frontier-program fn-sn-io
                            fn-bs-store-relation fn-bs-durable-frontier)))))
(defthm fn-bs-k0-owner-frontier-root-eio-dropped-run-fences-related-state
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          (fn-bs-k0-root-error-outcomes :drop)
                          groups capacity))
          (failed (car (nth 12 run)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
          (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
     (and (equal (len run) 13)
          (fn-bs-store-relation failed k4)
          (equal (fn-sf-phase k4) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-bs-durable-frontier bs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-node-root-eio-dropped-fences-related-state
                  (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-bs-k0-frontier-eio-dropped-run-has-actual-failed-cut
                  (ks (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           :in-theory (union-theories
                       '(fn-bs-k0-owner-io-store-is-node-io)
                       (theory 'minimal-theory)))))
(local
 (defthm fn-bs-k0-root-eio-nonapply-is-drop
   (implies (and (fn-bs-inop (fn-bs-lookup file :staging stage))
                 (equal (fn-bs-ops-for-dir (fn-bs-pending file) :root) nil)
                 (not (equal choice :apply)))
            (equal
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root (list :eio choice)))
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root '(:eio :drop)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-rename fn-bs-fsync-dir
                              fn-bs-ops-for-dir-of-append
                              fn-bs-crash-select fn-bs-apply-ops)
                            (fn-bs-lookup))))) )
(defthm fn-bs-k0-frontier-eio-choice-run-has-actual-failed-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ok-run (fn-bs-run bs ks
                                      (fn-bs-frontier-program stage octets)
                                      nil groups capacity))
                  (file (car (nth 6 ok-run)))
                  (error-run (fn-bs-run bs ks
                                         (fn-bs-frontier-program stage octets)
                                         (fn-bs-k0-root-error-outcomes choice)
                                         groups capacity)))
             (and (equal (len error-run) 13)
                  (equal (car (nth 12 error-run))
                         (mv-nth 1 (fn-bs-fsync-dir
                                    (mv-nth 1
                                            (fn-bs-rename file :staging stage
                                                          :root *fn-bs-frontier-name* :ok))
                                    :root (list :eio choice)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-replace-cut-is-rename
                 fn-bs-k0-frontier-rename-returns-ok
                 fn-bs-k0-frontier-file-observation-source-is-new-inode
                 fn-bs-k6-state-next-ino-is-inop)
           :in-theory (e/d (fn-bs-k0-root-error-outcomes
                            fn-bs-frontier-program fn-bs-run fn-bs-step)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-rename fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup fn-bs-statep
                            fn-bs-store-relation)))))
(local
 (defthm fn-bs-k0-frontier-eio-nonapply-run-is-drop-cut
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage))
                 (not (equal choice :apply)))
            (equal
             (car (nth 12 (fn-bs-run bs ks
                                     (fn-bs-frontier-program stage octets)
                                     (fn-bs-k0-root-error-outcomes choice)
                                     groups capacity)))
             (car (nth 12 (fn-bs-run bs ks
                                     (fn-bs-frontier-program stage octets)
                                     (fn-bs-k0-root-error-outcomes :drop)
                                     groups capacity)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-file-cut-statep
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-observation-source-is-new-inode
                  fn-bs-k0-frontier-file-cut-authority-quiet
                  fn-bs-k6-state-next-ino-is-inop
                  fn-bs-k0-frontier-eio-choice-run-has-actual-failed-cut
                  fn-bs-k0-frontier-eio-dropped-run-has-actual-failed-cut
                  (:instance fn-bs-k0-root-eio-nonapply-is-drop
                   (file (car (nth 6 (fn-bs-run bs ks
                                           (fn-bs-frontier-program stage octets)
                                           nil groups capacity))))))
            :in-theory (e/d (fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program fn-bs-lookup
                             fn-bs-store-relation fn-bs-fsync-dir fn-bs-rename))))))
; A single EIO at the root barrier admits either namespace result.  The model
; interprets any non-:apply selector as :drop; only :apply and :drop are
; supported physical entry choices.  This stronger all-selector theorem has
; no redundant choice hypothesis.
(defthm fn-bs-k0-owner-frontier-root-eio-choice-run-fences-related-state
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          (fn-bs-k0-root-error-outcomes choice)
                          groups capacity))
          (failed (car (nth 12 run)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
          (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
          (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
     (and (equal (len run) 13)
          (fn-bs-store-relation failed k4)
          (equal (fn-sf-phase k4) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (if (equal choice :apply)
                     (fn-sf-frontier-candidate k3)
                   (fn-bs-durable-frontier bs))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((equal choice :apply))
           :use ((:instance fn-bs-k0-owner-frontier-root-eio-applied-run-fences-related-state)
                 (:instance fn-bs-k0-owner-frontier-root-eio-dropped-run-fences-related-state)
                 (:instance fn-bs-k0-frontier-eio-choice-run-has-actual-failed-cut
                  (ks (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                 (:instance fn-bs-k0-frontier-eio-nonapply-run-is-drop-cut
                  (ks (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           :in-theory (union-theories
                       '(fn-bs-k0-root-error-outcomes)
                       (theory 'minimal-theory)))))
