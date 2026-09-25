;; fn: K0 at the cuts of the two root-rename programs (lane k0-rest, PKT-080).
;;
;; The state checkpoint (fn-bs-scp-program, store-checkpoint.fnsc) and the
;; profile upgrade (fn-bs-profile-program, config.json) are create,
;; write-all and fsync-file on a fresh staging name, a rename onto one :root
;; name, and the root barrier, with no kernel observation.  Keystone:
;; fn-bs-step-preserves-k0-coverage (byte-store-k0-step), whose coverage is
;; generic over the root name (fn-bs-k0s-root-rename-pendingp).  From a related
;; entry pair outside the recovery window with :root and :transactions quiet,
;; a name for the stage that is absent, and typed octets (and, for
;; config.json, octets that pass fn-bs-config-okp), fn-bs-k0r-pairs-by-step
;; derives by the keystone alone: the three stage cuts related, the replaced
;; cut covered (a pending root rename both of whose resolutions are related),
;; the durable cut related.  The kernel does not move.  Then:
;;   fn-bs-k0-state-checkpoint-cuts-relation-by-step
;;   fn-bs-k0-profile-cuts-relation-by-step
;; state it at each program's five cuts, and
;;   fn-bs-step-at-state-checkpoint-pairs-preserves-k0-coverage
;;   fn-bs-step-at-profile-pairs-preserves-k0-coverage
;; state that every step of the program, from the pair the successful run
;; reaches before it, with ANY outcome the environment chooses (the fsync of
;; the stage with :ok or a well-formed crash selection of its writes), leaves
;; a covered pair and the kernel unchanged: the host's error arms
;; (fnn-upgrade-profile-write and the checkpoint publish report every error at
;; or after the rename as uncertain) are covered by the same theorem.
(in-package "ACL2")
(include-book "byte-store-k0-step-bridge-prefix")
(include-book "byte-store-state-checkpoint-program")
(include-book "byte-store-profile-program")

(defun fn-bs-k0r-s4 (bs stage octets name)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s4) (fn-bs-rename (fn-bs-k0p-s3 bs stage octets) :staging stage :root name :ok)
    (declare (ignore r)) s4))
(defun fn-bs-k0r-s5 (bs stage octets name)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-fence-dir (fn-bs-k0r-s4 bs stage octets name) :root))

;; The stage's inode is fresh: nothing pending names it (the marker book's
;; local lemmas, restated here).
(local (defthm fn-bs-k0r-statep-fresh
  (implies (fn-bs-statep bs)
           (and (true-listp (fn-bs-pending bs))
                (natp (fn-bs-next-ino bs))
                (not (fn-bs-ops-for-ino (fn-bs-pending bs) (fn-bs-next-ino bs)))))
  :hints (("Goal" :in-theory (enable fn-bs-statep)
           :use ((:instance fn-bs-marker-fresh-ino-has-no-writes (ops (fn-bs-pending bs))
                  (inodes (fn-bs-inodes bs)) (n (fn-bs-next-ino bs))))))))
(local (defthm fn-bs-k0r-not-for-ino-id
  (implies (not (fn-bs-ops-for-ino ops n)) (equal (fn-bs-ops-not-for-ino ops n) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))
(local (defthm fn-bs-k0r-not-for-ino-app
  (equal (fn-bs-ops-not-for-ino (append a b) n) (append (fn-bs-ops-not-for-ino a n) (fn-bs-ops-not-for-ino b n)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-ino)))))
(local (defthm fn-bs-k0r-nthcdr-nil (equal (nthcdr n nil) nil)))
(local (defthm fn-bs-k0r-app-nil (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-bs-k0r-take-own (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))
(local (defthm fn-bs-k0r-len-consp (implies (consp x) (not (equal (len x) 0)))))
(local (defthm fn-bs-k0r-len-zero-true (implies (true-listp x) (equal (equal (len x) 0) (not x)))))
(local (defthm fn-bs-k0r-octets-true (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(defthm fn-bs-k0r-s3-facts
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets))
           (let ((s3 (fn-bs-k0p-s3 bs stage octets)) (n (fn-bs-next-ino bs)))
             (and (equal (fn-bs-lookup s3 :staging stage) n)
                  (fn-bs-inop n)
                  (fn-bs-fencedp s3 n)
                  (equal (fn-bs-durable-content s3 n) octets)
                  (consp (assoc-equal n (fn-bs-inodes s3))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0s-octets-are-true-lists (xs octets)))
           :in-theory (e/d (fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-file fn-bs-marker-lookup-is-entry-after fn-bs-entry-after
                            fn-bs-durable-entry fn-bs-durable-content fn-bs-fencedp fn-bs-inop
                            fn-bs-ops-for-ino fn-bs-splice fn-bs-put-assoc fn-bs-invariants-vocabulary
                            fn-bs-ops-for-ino-of-append fn-bs-apply-ops fn-bs-apply-op)
                           (fn-bs-statep fn-bs-lookup fn-bs-k0s-octets-are-true-lists)))))
(defthm fn-bs-k0r-s3-targetp
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets)
                (fn-bs-namep name)
                (not (equal name *fn-bs-scan-frontier-name*))
                (implies (equal name *fn-bs-scan-config-name*) (fn-bs-config-okp octets)))
           (fn-bs-k0s-root-rename-targetp (fn-bs-k0p-s3 bs stage octets) name (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use (fn-bs-k0r-s3-facts)
           :in-theory (e/d (fn-bs-k0s-root-rename-targetp)
                           (fn-bs-statep fn-bs-lookup fn-bs-k0p-s3 fn-bs-fencedp fn-bs-durable-content fn-bs-inop)))))
(defthm fn-bs-k0r-root-steps
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets))
           (and (equal (fn-bs-step (fn-bs-k0p-s3 bs stage octets) k (list :rename :staging stage :root name) :ok g c)
                       (list :ok (fn-bs-k0r-s4 bs stage octets name) k))
                (equal (fn-bs-step (fn-bs-k0r-s4 bs stage octets name) k (list :fsync-dir :root) :ok g c)
                       (list :ok (fn-bs-k0r-s5 bs stage octets name) k))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :use (fn-bs-k0r-s3-facts)
           :in-theory (e/d (fn-bs-step fn-bs-k0r-s4 fn-bs-k0r-s5 fn-bs-rename fn-bs-fsync-dir)
                           (fn-bs-statep fn-bs-lookup fn-bs-k0p-s3 fn-bs-fencedp fn-bs-durable-content fn-bs-fence-dir)))))
(defmacro fn-bs-k0r-run-shape-body (program)
  `(implies (and (fn-bs-statep bs) (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage))
                 (fn-cbor-octet-listp octets))
            (equal (fn-bs-run bs ks (,program stage octets) nil g c)
                   (let ((s1 (fn-bs-k0p-s1 bs stage)) (s2 (fn-bs-k0p-s2 bs stage octets))
                         (s3 (fn-bs-k0p-s3 bs stage octets))
                         (s4 (fn-bs-k0r-s4 bs stage octets name)) (s5 (fn-bs-k0r-s5 bs stage octets name)))
                     (list (cons s1 ks) (cons s1 ks) (cons s2 ks) (cons s2 ks) (cons s3 ks) (cons s3 ks)
                           (cons s4 ks) (cons s4 ks) (cons s5 ks) (cons s5 ks))))))
(defthm fn-bs-k0r-state-checkpoint-run-shape
  (let ((name *fn-bs-state-checkpoint-name*)) (fn-bs-k0r-run-shape-body fn-bs-scp-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-stage-steps (k ks))
                 (:instance fn-bs-k0r-root-steps (k ks) (name *fn-bs-state-checkpoint-name*)))
           :expand ((:free (b k s) (fn-bs-run b k s nil g c)))
           :in-theory (e/d (fn-bs-scp-program fn-bs-k0c-cut-step-is-identity)
                           (fn-bs-step fn-bs-run fn-bs-lookup fn-bs-statep fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                            fn-bs-k0r-s4 fn-bs-k0r-s5)))))
(defthm fn-bs-k0r-profile-run-shape
  (let ((name *fn-bs-config-name*)) (fn-bs-k0r-run-shape-body fn-bs-profile-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-stage-steps (k ks))
                 (:instance fn-bs-k0r-root-steps (k ks) (name *fn-bs-config-name*)))
           :expand ((:free (b k s) (fn-bs-run b k s nil g c)))
           :in-theory (e/d (fn-bs-profile-program fn-bs-k0c-cut-step-is-identity)
                           (fn-bs-step fn-bs-run fn-bs-lookup fn-bs-statep fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                            fn-bs-k0r-s4 fn-bs-k0r-s5)))))
(defthm fn-bs-k0r-no-root-rename-off-root
  (not (fn-bs-k0m-has-root-rename (fn-bs-ops-not-for-dir ops :root)))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-has-root-rename fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0r-root-rename-status
  (implies (and (not (equal name *fn-bs-scan-frontier-name*))
                (fn-bs-inop (fn-bs-lookup (fn-bs-k0p-s3 bs stage octets) :staging stage)))
           (and (fn-bs-k0m-has-root-rename (fn-bs-pending (fn-bs-k0r-s4 bs stage octets name)))
                (not (fn-bs-k0m-has-root-rename (fn-bs-pending (fn-bs-k0r-s5 bs stage octets name))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-k0r-s4 fn-bs-k0r-s5 fn-bs-rename fn-bs-fence-dir fn-bs-k0m-has-root-rename)
                                  (fn-bs-lookup fn-bs-k0p-s3 fn-bs-apply-ops fn-bs-ops-not-for-dir)))))
(defmacro fn-bs-k0r-hyps ()
  '(and (fn-bs-k0p-stage-hyps)
        (fn-bs-namep name)
        (not (equal name *fn-bs-scan-frontier-name*))
        (implies (equal name *fn-bs-scan-config-name*) (fn-bs-config-okp octets))))
(defun fn-bs-k0r-fsync-outcomep (bs stage octets outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((b2 (fn-bs-k0p-s2 bs stage octets)))
    (or (equal outcome :ok)
        (fn-bs-crash-choicesp (cdr outcome)
                              (fn-bs-ops-for-ino (fn-bs-pending b2) (fn-bs-next-ino bs))
                              (fn-bs-unit b2)))))
(defthm fn-bs-k0r-step-inputs
  (implies (fn-bs-k0r-hyps)
           (and (fn-bs-k0-step-inputp bs ks (list :create :staging stage) outcome)
                (implies (fn-bs-store-relation (fn-bs-k0p-s1 bs stage) ks)
                         (fn-bs-k0-step-inputp (fn-bs-k0p-s1 bs stage) ks
                                               (list :write-all :staging stage octets) outcome))
                (implies (and (fn-bs-store-relation (fn-bs-k0p-s2 bs stage octets) ks)
                              (fn-bs-k0r-fsync-outcomep bs stage octets outcome))
                         (fn-bs-k0-step-inputp (fn-bs-k0p-s2 bs stage octets) ks
                                               (list :fsync-file :staging stage) outcome))
                (implies (fn-bs-store-relation (fn-bs-k0p-s3 bs stage octets) ks)
                         (fn-bs-k0-step-inputp (fn-bs-k0p-s3 bs stage octets) ks
                                               (list :rename :staging stage :root name) outcome))
                (implies (fn-bs-k0s-root-rename-pendingp (fn-bs-k0r-s4 bs stage octets name) ks)
                         (fn-bs-k0-step-inputp (fn-bs-k0r-s4 bs stage octets name) ks
                                               (list :fsync-dir :root) outcome))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 fn-bs-k0r-s3-facts fn-bs-k0r-s3-targetp)
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0p-stage-dir-ops2 fn-bs-k0p-stage-lookups fn-bs-statep
                            fn-bs-k0r-fsync-outcomep)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-authority-inode-list fn-bs-k0p-s1 fn-bs-k0p-s2
                            fn-bs-k0p-s3 fn-bs-k0r-s4 fn-bs-k0s-root-rename-pendingp fn-bs-k0-coveredp
                            fn-bs-replay-visiblep fn-bs-k0s-root-rename-targetp
                            fn-bs-crash-choicesp fn-bs-ops-for-ino fn-bs-k0-observation-inputp)))))
(defthm fn-bs-k0r-pairs-by-step
  (implies (fn-bs-k0r-hyps)
           (and (fn-bs-store-relation (fn-bs-k0p-s1 bs stage) ks)
                (fn-bs-store-relation (fn-bs-k0p-s2 bs stage octets) ks)
                (fn-bs-store-relation (fn-bs-k0p-s3 bs stage octets) ks)
                (fn-bs-k0s-root-rename-pendingp (fn-bs-k0r-s4 bs stage octets name) ks)
                (fn-bs-store-relation (fn-bs-k0r-s5 bs stage octets name) ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0p-stage-pairs-by-step
                 (:instance fn-bs-k0r-step-inputs (outcome :ok))
                 (:instance fn-bs-k0r-root-steps (k ks) (g nil) (c nil))
                 fn-bs-k0r-s3-facts fn-bs-k0r-root-rename-status
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s3 bs stage octets))
                  (step (list :rename :staging stage :root name)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0r-s4 bs stage octets name))
                  (step (list :fsync-dir :root)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-k0b-covered-with-root-rename-is-pending (b (fn-bs-k0r-s4 bs stage octets name)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related (b (fn-bs-k0r-s5 bs stage octets name)) (k ks)))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-root-rename-pendingp fn-bs-k0-step-inputp
                               fn-bs-step fn-bs-lookup fn-bs-k0m-has-root-rename fn-bs-statep
                               fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-k0r-s4 fn-bs-k0r-s5
                               fn-bs-replay-visiblep fn-bs-fencedp fn-bs-durable-content fn-bs-inop)))))

; The two programs.  Each cut pair of the successful run: the stage cuts and
; the durable cut related, the replaced cut covered; the kernel is the entry
; kernel throughout.
(defmacro fn-bs-k0r-cuts-body (program)
  `(let ((run (fn-bs-run bs ks (,program stage octets) nil groups capacity)))
     (and (fn-bs-store-relation (car (nth 1 run)) ks)
          (fn-bs-store-relation (car (nth 3 run)) ks)
          (fn-bs-store-relation (car (nth 5 run)) ks)
          (fn-bs-k0s-root-rename-pendingp (car (nth 7 run)) ks)
          (fn-bs-store-relation (car (nth 9 run)) ks)
          (equal (cdr (nth 1 run)) ks) (equal (cdr (nth 3 run)) ks) (equal (cdr (nth 5 run)) ks)
          (equal (cdr (nth 7 run)) ks) (equal (cdr (nth 9 run)) ks))))
(defthm fn-bs-k0-state-checkpoint-cuts-relation-by-step
  (implies (fn-bs-k0p-stage-hyps)
           (fn-bs-k0r-cuts-body fn-bs-scp-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0r-pairs-by-step (name *fn-bs-state-checkpoint-name*))
                 (:instance fn-bs-k0r-state-checkpoint-run-shape (g groups) (c capacity))
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-k0s-root-rename-pendingp fn-bs-run fn-bs-scp-program
                               fn-bs-lookup fn-bs-statep fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                               fn-bs-k0r-s4 fn-bs-k0r-s5 fn-bs-replay-visiblep)))))
(defthm fn-bs-k0-profile-cuts-relation-by-step
  (implies (and (fn-bs-k0p-stage-hyps) (fn-bs-config-okp octets))
           (fn-bs-k0r-cuts-body fn-bs-profile-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0r-pairs-by-step (name *fn-bs-config-name*))
                 (:instance fn-bs-k0r-profile-run-shape (g groups) (c capacity))
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-k0s-root-rename-pendingp fn-bs-run fn-bs-profile-program
                               fn-bs-lookup fn-bs-statep fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                               fn-bs-k0r-s4 fn-bs-k0r-s5 fn-bs-replay-visiblep)))))

; Every step of either program, from the pair the successful run reaches
; before it, with any outcome (the stage fsync with :ok or a well-formed crash
; selection of its writes): the result is covered and the kernel unchanged.
(defun fn-bs-k0r-step-coveredp (pre step outcome ks groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1 ks1) (fn-bs-step (car pre) (cdr pre) step outcome groups capacity)
    (declare (ignore r))
    (and (fn-bs-k0-coveredp bs1 ks1) (equal ks1 ks))))
(defmacro fn-bs-k0r-any-outcome-body (program)
  `(let ((run (fn-bs-run bs ks (,program stage octets) nil groups capacity))
         (prog (,program stage octets)))
     (and (fn-bs-k0r-step-coveredp (cons bs ks) (nth 0 prog) outcome ks groups capacity)
          (fn-bs-k0r-step-coveredp (nth 1 run) (nth 2 prog) outcome ks groups capacity)
          (fn-bs-k0r-step-coveredp (nth 3 run) (nth 4 prog) outcome ks groups capacity)
          (fn-bs-k0r-step-coveredp (nth 5 run) (nth 6 prog) outcome ks groups capacity)
          (fn-bs-k0r-step-coveredp (nth 7 run) (nth 8 prog) outcome ks groups capacity))))
(defthm fn-bs-k0r-pair-steps-covered
  (implies (and (fn-bs-k0r-hyps) (fn-bs-k0r-fsync-outcomep bs stage octets outcome))
           (and (fn-bs-k0r-step-coveredp (cons bs ks) (list :create :staging stage) outcome ks groups capacity)
                (fn-bs-k0r-step-coveredp (cons (fn-bs-k0p-s1 bs stage) ks) (list :write-all :staging stage octets) outcome ks groups capacity)
                (fn-bs-k0r-step-coveredp (cons (fn-bs-k0p-s2 bs stage octets) ks) (list :fsync-file :staging stage) outcome ks groups capacity)
                (fn-bs-k0r-step-coveredp (cons (fn-bs-k0p-s3 bs stage octets) ks) (list :rename :staging stage :root name) outcome ks groups capacity)
                (fn-bs-k0r-step-coveredp (cons (fn-bs-k0r-s4 bs stage octets name) ks) (list :fsync-dir :root) outcome ks groups capacity)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0r-pairs-by-step fn-bs-k0r-step-inputs
                 (:instance fn-bs-step-preserves-k0-coverage (step (list :create :staging stage)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s1 bs stage)) (step (list :write-all :staging stage octets)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s2 bs stage octets)) (step (list :fsync-file :staging stage)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s3 bs stage octets)) (step (list :rename :staging stage :root name)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0r-s4 bs stage octets name)) (step (list :fsync-dir :root))))
           :in-theory (e/d (fn-bs-k0r-step-coveredp)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-step
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-k0r-s4 fn-bs-k0r-s5
                            fn-bs-k0-coveredp fn-bs-k0-step-inputp fn-bs-k0s-root-rename-pendingp
                            fn-bs-k0r-fsync-outcomep fn-bs-replay-visiblep)))))
(defthm fn-bs-step-at-state-checkpoint-pairs-preserves-k0-coverage
  (implies (and (fn-bs-k0p-stage-hyps)
                (fn-bs-k0r-fsync-outcomep bs stage octets outcome))
           (fn-bs-k0r-any-outcome-body fn-bs-scp-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0r-pair-steps-covered (name *fn-bs-state-checkpoint-name*))
                 (:instance fn-bs-k0r-state-checkpoint-run-shape (g groups) (c capacity))
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-scp-program)
                           (fn-bs-k0r-step-coveredp fn-bs-store-relation fn-bs-run fn-bs-lookup fn-bs-statep
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-k0r-s4 fn-bs-k0r-s5
                            fn-bs-k0r-fsync-outcomep fn-bs-replay-visiblep)))))
(defthm fn-bs-step-at-profile-pairs-preserves-k0-coverage
  (implies (and (fn-bs-k0p-stage-hyps) (fn-bs-config-okp octets)
                (fn-bs-k0r-fsync-outcomep bs stage octets outcome))
           (fn-bs-k0r-any-outcome-body fn-bs-profile-program))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0r-pair-steps-covered (name *fn-bs-config-name*))
                 (:instance fn-bs-k0r-profile-run-shape (g groups) (c capacity))
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-profile-program)
                           (fn-bs-k0r-step-coveredp fn-bs-store-relation fn-bs-run fn-bs-lookup fn-bs-statep
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-k0r-s4 fn-bs-k0r-s5
                            fn-bs-k0r-fsync-outcomep fn-bs-replay-visiblep)))))
