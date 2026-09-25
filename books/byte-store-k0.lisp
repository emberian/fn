;; fn: K0 at the campaign's cut coordinates (P10, lane p10-k0).
;;
;; The general `fn-bs-step-preserves-k0-coverage' is NOT proved here and
;; is not claimed.  What this book proves is K0 restricted to cut
;; coordinates, from an ARBITRARY related state (retained history allowed),
;; under each program's typed input contract and an absent staging name:
;;
;;   fn-bs-k0c-cut-pair-is-previous-pair  every program, every state: the pair
;;       at a :cut step is the pair of the step before it, so a death at a
;;       cut leaves exactly the preceding syscall/observation state.
;;   P-FRONTIER  frontier-staged-durable, frontier-durable, frontier-reserved
;;       (from the pair-6/12/14 keystones in byte-store-record-provenance).
;;   P-RECORD    record-staged-durable, record-linked, record-attempted
;;       (provenance), record-durable, record-completing.
;;   P-FINISH    every pair (finish-consumed, finish-durable).
;;
;;   Lane p10-k0-b's cuts and error arms are in books/byte-store-k0-staging.
;;
;; OPEN, named and not claimed: every P-RECOVER cut (recover-replayed,
;; recover-barrier x5) and the entry theorem they need (the relation from
;; fn-sn-open-observed's scanned image); recovery-stage-unlinked is covered
;; only given a related state at sweep entry (byte-store-keystones,
;; fn-bs-recover-sweep-keeps-relation-at-every-cut); the issued-link error
;; arm; the checkpoint phase machines.  No host line calls these byte-model
;; programs; tools/native_program_check.py is their tie to the host.
(in-package "ACL2")
(include-book "byte-store-record-provenance")
(include-book "byte-store-record-fence")
(defun fn-bs-k0c-ind (k bs ks steps outs g c)
  (declare (xargs :measure (acl2-count steps) :verify-guards nil))
  (if (or (zp k) (atom steps)) (list bs ks outs g c)
    (mv-let (r bs1 ks1) (fn-bs-step bs ks (car steps) (if (consp outs) (car outs) :ok) g c)
      (declare (ignore r))
      (fn-bs-k0c-ind (1- k) bs1 ks1 (cdr steps) (cdr outs) g c))))
(defthm fn-bs-k0c-cut-step-is-identity
  (implies (equal (car step) :cut)
           (equal (fn-bs-step bs ks step o g c) (list :ok bs ks)))
  :hints (("Goal" :in-theory (enable fn-bs-step))))
(defthm fn-bs-k0c-cut-pair-is-previous-pair
  (implies (and (natp k)
                (equal (car (nth (1+ k) steps)) :cut)
                (consp (nth (1+ k) (fn-bs-run bs ks steps outs g c))))
           (equal (nth (1+ k) (fn-bs-run bs ks steps outs g c))
                  (nth k (fn-bs-run bs ks steps outs g c))))
  :hints (("Goal" :induct (fn-bs-k0c-ind k bs ks steps outs g c)
           :expand ((fn-bs-run bs ks steps outs g c)
                    (:free (b k2 o) (fn-bs-run b k2 (cdr steps) o g c)))
           :in-theory (e/d (nth) (fn-bs-run fn-bs-step)))))
(defthm fn-bs-k0c-ok-kinds-return-ok
  (implies (member-equal (car step) '(:observe :cut :fsync-file :fsync-dir))
           (equal (mv-nth 0 (fn-bs-step bs ks step :ok g c)) :ok))
  :hints (("Goal" :in-theory (enable fn-bs-step fn-bs-fsync-file fn-bs-fsync-dir))))
(defthm fn-bs-k0c-run-nth-consp-step-forward
  (implies (and (natp k)
                (consp (nth k (fn-bs-run bs ks steps nil g c)))
                (member-equal (car (nth k steps)) '(:observe :cut :fsync-file :fsync-dir))
                (consp (nthcdr (1+ k) steps)))
           (consp (nth (1+ k) (fn-bs-run bs ks steps nil g c))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-k0c-ind k bs ks steps nil g c)
           :expand ((fn-bs-run bs ks steps nil g c)
                    (:free (b k2) (fn-bs-run b k2 (cdr steps) nil g c)))
           :in-theory (e/d (nth nthcdr) (fn-bs-run fn-bs-step)))))
(defthm fn-bs-k0c-nth-succ
  (implies (and (natp k) (consp (nth (1+ k) (fn-bs-run bs ks steps nil g c))))
           (equal (nth (1+ k) (fn-bs-run bs ks steps nil g c))
                  (cons (mv-nth 1 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                              (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                              (nth (1+ k) steps) :ok g c))
                        (mv-nth 2 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                              (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                              (nth (1+ k) steps) :ok g c)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-k0c-ind k bs ks steps nil g c)
           :expand ((fn-bs-run bs ks steps nil g c)
                    (:free (b k2) (fn-bs-run b k2 (cdr steps) nil g c)))
           :in-theory (e/d (nth) (fn-bs-run fn-bs-step)))))
(defthm fn-bs-k0c-related-pair-is-consp
  (implies (fn-bs-store-relation (car x) (cdr x)) (consp x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-store-relation fn-bs-statep fn-bs-shapep))))
(in-theory (disable fn-bs-k0c-cut-pair-is-previous-pair))
(defthm fn-bs-k0-frontier-staged-durable-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 7 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-observation-establishes-relation
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 6) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair
                  (k 6) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-frontier-program) (fn-bs-run fn-bs-store-relation fn-bs-frontier-inputp)))))
(defmacro fn-bs-k0-cut-after-related-pair (name program inputp k prev)
  `(defthm ,name
     (implies (and (fn-bs-store-relation bs ks)
                   ,inputp
                   (not (fn-bs-lookup bs :staging stage)))
              (let ((p (nth ,(1+ k) (fn-bs-run bs ks ,program nil groups capacity))))
                (fn-bs-store-relation (car p) (cdr p))))
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use (,prev
                    (:instance fn-bs-k0c-related-pair-is-consp
                     (x (nth ,k (fn-bs-run bs ks ,program nil groups capacity))))
                    (:instance fn-bs-k0c-run-nth-consp-step-forward
                     (k ,k) (steps ,program) (g groups) (c capacity))
                    (:instance fn-bs-k0c-cut-pair-is-previous-pair
                     (k ,k) (steps ,program) (outs nil) (g groups) (c capacity)))
              :in-theory (e/d (fn-bs-frontier-program fn-bs-record-program)
                              (fn-bs-run fn-bs-store-relation fn-bs-frontier-inputp
                               fn-bs-record-inputp))))))
(fn-bs-k0-cut-after-related-pair fn-bs-k0-frontier-durable-cut-relation
  (fn-bs-frontier-program stage octets) (fn-bs-frontier-inputp ks stage octets)
  12 fn-bs-k0-frontier-dir-cut-establishes-relation)
(fn-bs-k0-cut-after-related-pair fn-bs-k0-frontier-reserved-cut-relation
  (fn-bs-frontier-program stage octets) (fn-bs-frontier-inputp ks stage octets)
  14 fn-bs-k0-frontier-reserved-cut-establishes-relation)
(defthm fn-bs-k0-record-attempted-kernel-phase
  (implies (and (fn-sf-statep ks) (fn-bs-record-inputp ks stage name frame))
           (equal (fn-sf-phase (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :ok))
                  :record-attempted))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok)))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-record-link-result fn-sf-record-file-result)
                           (fn-sf-statep)))))
(defthm fn-bs-k0-record-fence-pair-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 11 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                 fn-bs-k0-attempted-cut-has-one-issued-transaction-link
                 fn-bs-k0-record-attempted-kernel-phase
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-nth-succ
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k8-pending-link-fence-preserves-relation
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-bs-fsync-dir)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-inputp fn-bs-fence-dir
                            fn-sf-record-link-result fn-sf-record-file-result)))))
(fn-bs-k0-cut-after-related-pair fn-bs-k0-record-durable-cut-relation
  (fn-bs-record-program stage name frame) (fn-bs-record-inputp ks stage name frame)
  11 fn-bs-k0-record-fence-pair-relation)
(defun fn-bs-record-directory-committedp (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-dir-quietp bs :transactions)
       (equal (fn-bs-durable-records bs)
              (append (fn-sf-records ks) (list (fn-sf-record-candidate ks))))))
(defthm fn-bs-record-directory-commit-observation-preserves-relation
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (fn-bs-record-directory-committedp bs ks))
           (and (fn-bs-store-relation bs (fn-sf-record-dir-result ks :ok))
                (equal (fn-sf-phase (fn-sf-record-dir-result ks :ok)) :completing)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-dir-result-preserves-state (s ks) (result :ok)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-bs-dir-quietp fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-record-dir-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-bs-k0-record-pair-11-is-transaction-fence
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p10 (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
                 (p11 (nth 11 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (and (consp p11)
                  (equal p11 (cons (fn-bs-fence-dir (car p10) :transactions) (cdr p10))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-attempted-cut-establishes-relation
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-nth-succ
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-bs-fsync-dir)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-inputp fn-bs-fence-dir)))))
(defthm fn-bs-k0-record-completing-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (and (fn-bs-store-relation (car p) (cdr p))
                  (equal (fn-sf-phase (cdr p)) :completing))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-pair-11-is-transaction-fence
                 fn-bs-k0-record-fence-pair-relation
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                 fn-bs-k0-attempted-cut-has-one-issued-transaction-link
                 fn-bs-k0-record-attempted-kernel-phase
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-store-relation-window-unfolds
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-pending-matches-phase-unfolds
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k8-pending-link-fence-durable-records
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-record-directory-commit-observation-preserves-relation
                  (bs (car (nth 11 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 11) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair
                  (k 11) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 12) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-nth-succ
                  (k 12) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-run-nth-consp-step-forward
                  (k 13) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair
                  (k 13) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch fn-bs-record-directory-committedp
                            fn-bs-dir-quietp fn-bs-fence-dir fn-bs-ops-for-dir-of-ops-not-for-dir
                            fn-bs-replay-visiblep)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-inputp
                            fn-sf-record-link-result fn-sf-record-file-result fn-sf-record-dir-result
                            fn-bs-durable-records fn-bs-pending-matches-phase fn-bs-apply-ops
                            ;; The :use instances name every (nth k run) this
                            ;; proof reads; opening nth, and the NNTP and wire
                            ;; rules that fire on any consp goal, only searched
                            ;; (2.4 s -> 1.6 s, persvati REPL).
                            nth member-equal fn-bs-ops-not-for-dir
                            fn-nntp-article-idp-is-consp
                            fn-snrt-new-success-is-actual-matching-durable-completion
                            fn-wire-next-loop-event-needs-input fn-wire-next-event-needs-input
                            fn-nntp-newnews-candidate-is-projectable
                            fn-nntp-available-number-article-is-projectable)))))
(defun fn-bs-finish-inputp (ks sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-sf-phase ks) :completing)
       (equal (cons sequence txid) (fn-sf-completion ks))))
(defthm fn-bs-core-completion-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-core-completion ks sequence txid)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-core-completion-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-core-completion)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-bs-emit-success-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-emit-success ks sequence txid)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-emit-success-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-emit-success)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-bs-k0-finish-program-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-run-relatedp
            (fn-bs-run bs ks (fn-bs-finish-program sequence txid) nil groups capacity)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-core-completion-preserves-relation
                 (:instance fn-bs-emit-success-preserves-relation
                  (ks (fn-sf-core-completion ks sequence txid))))
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-finish-program fn-bs-step fn-sf-dispatch fn-bs-run-relatedp)
                           (fn-bs-store-relation fn-sf-core-completion fn-sf-emit-success)))))
(defthm fn-bs-k0-finish-program-reaches-ready
  (implies (and (fn-sf-statep ks) (fn-bs-finish-inputp ks sequence txid))
           (let ((run (fn-bs-run bs ks (fn-bs-finish-program sequence txid) nil groups capacity)))
             (and (equal (len run) 4)
                  (equal (fn-sf-phase (cdr (nth 3 run))) :ready))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sf-core-completion-preserves-state (s ks)))
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-finish-program fn-bs-step fn-sf-dispatch fn-bs-finish-inputp
                            fn-sf-core-completion fn-sf-emit-success)
                           (fn-sf-statep)))))
(defthm fn-bs-k0-record-run-linked-shape
  (implies (consp (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (equal (cdr (nth 8 run)) (fn-sf-record-file-result ks :ok))
                  (equal (car (nth 8 run)) (car (nth 10 run)))
                  (equal (cdr (nth 10 run))
                         (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :ok))
                  (equal (nth 6 run) (nth 5 run))
                  (equal (car (nth 5 run)) (car (nth 4 run)))
                  (equal (cdr (nth 4 run)) ks))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                            fn-bs-link fn-bs-unlink fn-bs-lookup
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result)))))
(defthm fn-bs-k0-kernel-transport
  (implies (and (fn-bs-store-relation bs ks)
                (fn-sf-statep ks2)
                (not (fn-bs-replay-visiblep ks))
                (not (fn-bs-replay-visiblep ks2))
                (equal (fn-sf-frontier ks2) (fn-sf-frontier ks))
                (equal (fn-sf-records ks2) (fn-sf-records ks))
                (equal (fn-sf-record-candidate ks2) (fn-sf-record-candidate ks))
                (equal (fn-sf-frontier-candidate ks2) (fn-sf-frontier-candidate ks))
                (iff (fn-sf-frontier-new-visiblep ks2) (fn-sf-frontier-new-visiblep ks))
                (iff (fn-sf-record-present-visiblep ks2) (fn-sf-record-present-visiblep ks)))
           (fn-bs-store-relation bs ks2))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation fn-sf-crash-imagep fn-bs-pending-matches-phase)
                                  (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                                   fn-bs-authority-fencedp fn-bs-authority-knownp
                                   fn-bs-ops-for-dir fn-bs-replay-visiblep
                                   fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                                   fn-bs-durable-records fn-bs-durable-frontier)))))
(defthm fn-bs-k0-record-linked-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k0-record-run-linked-shape
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok))
                 (:instance fn-bs-k0-kernel-transport
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :ok))
                  (ks2 (fn-sf-record-file-result ks :ok))))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-record-file-result fn-sf-record-link-result
                            fn-bs-replay-visiblep fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)
                           (fn-bs-run fn-bs-store-relation fn-sf-statep fn-bs-record-program)))))
(local
 (defthm fn-bs-k0t-pending-entry-targets-of-append
  (equal (fn-bs-pending-entry-targets (append a b))
         (append (fn-bs-pending-entry-targets a)
                 (fn-bs-pending-entry-targets b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-bs-pending-entry-targets)))))
(local
 (defthm fn-bs-k0t-all-fencedp-of-append
   (equal (fn-bs-all-fencedp bs (append a b))
          (and (fn-bs-all-fencedp bs a) (fn-bs-all-fencedp bs b)))
   :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-all-fencedp)))))
(local
 (defthm fn-bs-k0t-known-of-append
   (equal (fn-bs-inode-list-knownp bs (append a b))
          (and (fn-bs-inode-list-knownp bs a) (fn-bs-inode-list-knownp bs b)))
   :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-inode-list-knownp)))))
(local
 (defun fn-bs-k0t-fenced-in (p xs)
   (if (consp xs)
       (and (null (fn-bs-ops-for-ino p (car xs))) (fn-bs-k0t-fenced-in p (cdr xs)))
     t)))
(local
 (defthm fn-bs-k0t-all-fencedp-is-fenced-in
   (equal (fn-bs-all-fencedp bs xs) (fn-bs-k0t-fenced-in (fn-bs-pending bs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-all-fencedp fn-bs-fencedp)))))
(local
 (defthm fn-bs-k0t-fenced-in-of-append-list
   (equal (fn-bs-k0t-fenced-in p (append a b))
          (and (fn-bs-k0t-fenced-in p a) (fn-bs-k0t-fenced-in p b)))))
(local
 (defthm fn-bs-k0t-fenced-in-ignores-entry-op
   (equal (fn-bs-k0t-fenced-in (append p (list (list :set-entry dir name ino))) xs)
          (fn-bs-k0t-fenced-in p xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local
 (defun fn-bs-k0t-knownp-in (inodes xs)
   (if (consp xs)
       (and (consp (assoc-equal (car xs) inodes)) (fn-bs-k0t-knownp-in inodes (cdr xs)))
     t)))
(local
 (defthm fn-bs-k0t-known-list-is-knownp-in
   (equal (fn-bs-inode-list-knownp bs xs) (fn-bs-k0t-knownp-in (fn-bs-inodes bs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp)))))
(local
 (defthm fn-bs-k0t-knownp-in-of-append
   (equal (fn-bs-k0t-knownp-in i (append a b))
          (and (fn-bs-k0t-knownp-in i a) (fn-bs-k0t-knownp-in i b)))))
(defthm fn-bs-k0-drop-pending-transaction-link-transports-relation
  (implies (and (fn-bs-store-relation
                 (fn-bs-make (fn-bs-unit b5) (fn-bs-inodes b5) (fn-bs-dirs b5)
                             (append (fn-bs-pending b5)
                                     (list (list :set-entry :transactions name ino)))
                             (fn-bs-next-ino b5))
                 k)
                (fn-bs-statep b5)
                (not (fn-bs-ops-for-dir (fn-bs-pending b5) :transactions))
                (not (fn-bs-replay-visiblep k)))
           (fn-bs-store-relation b5 k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-pending-entry-targets fn-bs-ops-for-dir-of-append
                            fn-bs-durable fn-bs-durable-entry fn-bs-durable-names fn-bs-statep fn-bs-shapep
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-content)
                           (fn-bs-read-records fn-bs-record-of
                            fn-sf-crash-imagep fn-sf-statep fn-bs-replay-visiblep
                            fn-bs-contiguous-namesp fn-bs-fencedp fn-bs-inode-list-knownp
                            fn-bs-all-fencedp)))))
(defthm fn-bs-k0-record-run-link-pair-shape
  (implies (consp (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
           (let* ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))
                  (b5 (car (nth 5 run))))
             (and (equal (car (nth 8 run))
                         (fn-bs-make (fn-bs-unit b5) (fn-bs-inodes b5) (fn-bs-dirs b5)
                                     (append (fn-bs-pending b5)
                                             (list (list :set-entry :transactions name
                                                         (fn-bs-lookup b5 :staging stage))))
                                     (fn-bs-next-ino b5)))
                  (equal (cdr (nth 5 run)) (fn-sf-record-file-result ks :ok))
                  (equal (nth 6 run) (nth 5 run)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch fn-bs-link)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                            fn-bs-unlink fn-bs-lookup fn-bs-inop
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result)))))
(defthm fn-bs-k0-record-staged-durable-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k0-record-linked-cut-relation
                 fn-bs-k0-record-run-link-pair-shape fn-bs-k0-record-run-linked-shape
                 fn-bs-store-relation-unfolds
                 fn-bs-k6-related-input-file-cut-has-no-transaction-pending
                 fn-bs-k0-record-file-cut-statep
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0-drop-pending-transaction-link-transports-relation
                  (b5 (car (nth 5 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (fn-sf-record-file-result ks :ok))
                  (ino (fn-bs-lookup (car (nth 5 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))) :staging stage))))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-record-file-result fn-bs-replay-visiblep)
                           (fn-bs-run fn-bs-store-relation fn-sf-statep fn-bs-record-program
                            fn-bs-statep fn-bs-lookup fn-bs-make)))))

;; Building block for the open frontier-replaced / frontier-attempted cuts:
;; issuing the frontier rename on a related, authority-quiet state whose
;; fenced staging inode decodes to the kernel's candidate keeps the relation
;; for any :frontier-data-durable / :frontier-attempted-shaped kernel.  What
;; remains is its premise at the actual pair 6: root/transactions quiet there
;; is proved only as a LOCAL lemma of byte-store-record-provenance
;; (fn-bs-k0-frontier-file-cut-authority-quiet).
(local (defthm fn-bs-k0t-writes-knownp-of-append
  (equal (fn-bs-writes-knownp (append a b) i)
         (and (fn-bs-writes-knownp a i) (fn-bs-writes-knownp b i)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-writes-knownp)))))
(local (defthm fn-bs-k0t-writes-nonemptyp-of-append
  (equal (fn-bs-writes-nonemptyp (append a b))
         (and (fn-bs-writes-nonemptyp a) (fn-bs-writes-nonemptyp b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-writes-nonemptyp)))))
(local (defthm fn-bs-k0t-fenced-in-ignores-rename-ops
   (equal (fn-bs-k0t-fenced-in (append p (list (list :set-entry dir name ino)
                                                (list :del-entry sdir sname))) xs)
          (fn-bs-k0t-fenced-in p xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-fencedp-ignores-rename-ops
   (equal (fn-bs-fencedp (fn-bs-make u i d (append p (list (list :set-entry dir name ino)
                                                          (list :del-entry sdir sname))) n) x)
          (fn-bs-fencedp (fn-bs-make u i d p n) x))
   :hints (("Goal" :in-theory (enable fn-bs-fencedp fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-fencedp-of-own-fields
   (implies (fn-bs-statep b)
            (equal (fn-bs-fencedp (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                              (fn-bs-pending b) (fn-bs-next-ino b)) x)
                   (fn-bs-fencedp b x)))
   :hints (("Goal" :in-theory (enable fn-bs-fencedp)))))
(defthm fn-bs-k0-add-pending-frontier-rename-transports-relation
  (implies (and (fn-bs-store-relation b6 k6)
                (fn-sf-statep k)
                (not (fn-bs-replay-visiblep k))
                (not (fn-bs-replay-visiblep k6))
                (not (fn-bs-ops-for-dir (fn-bs-pending b6) :root))
                (not (fn-bs-ops-for-dir (fn-bs-pending b6) :transactions))
                (fn-bs-inop ino)
                (fn-bs-fencedp b6 ino)
                (consp (assoc-equal ino (fn-bs-inodes b6)))
                (fn-bs-dir-idp sdir) (not (equal sdir :root)) (not (equal sdir :transactions))
                (fn-bs-namep sname)
                (fn-sf-frontier-new-visiblep k)
                (not (fn-sf-record-present-visiblep k))
                (equal (fn-bs-frontier-decode (fn-bs-durable-content b6 ino))
                       (fn-sf-frontier-candidate k))
                (equal (fn-bs-durable-frontier b6) (fn-sf-frontier k))
                (equal (fn-bs-durable-records b6) (fn-sf-records k)))
           (fn-bs-store-relation
            (fn-bs-make (fn-bs-unit b6) (fn-bs-inodes b6) (fn-bs-dirs b6)
                        (append (fn-bs-pending b6)
                                (list (list :set-entry :root *fn-bs-frontier-name* ino)
                                      (list :del-entry sdir sname)))
                        (fn-bs-next-ino b6))
            k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b6) (ks k6)) (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending b6))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-pending-entry-targets fn-bs-ops-for-dir-of-append
                            fn-bs-durable fn-bs-durable-entry fn-bs-durable-names fn-bs-statep fn-bs-shapep
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-content
                            fn-sf-crash-imagep fn-bs-op-listp-of-append fn-bs-ops-for-dir
                            fn-bs-writes-knownp fn-bs-writes-nonemptyp fn-bs-opp fn-bs-op-listp fn-bs-entry-valuep fn-bs-namep fn-bs-fencedp)
                           (fn-bs-read-records fn-bs-record-of fn-sf-statep fn-bs-replay-visiblep
                            fn-bs-contiguous-namesp fn-bs-inode-list-knownp
                            fn-bs-all-fencedp fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-k8-name-absent-from-list-has-no-entry
                            fn-nntp-article-idp-is-consp
                            fn-snrt-new-success-is-actual-matching-durable-completion
                            fn-wire-next-loop-event-needs-input fn-wire-next-event-needs-input
                            fn-nntp-newnews-candidate-is-projectable
                            fn-nntp-available-number-article-is-projectable)))))
