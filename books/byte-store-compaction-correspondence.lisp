; Physical selected-pack prefix reclamation in the byte crash model.
(in-package "ACL2")
(include-book "byte-store-programs")
(include-book "byte-store-txn-name")
(include-book "checkpoint-compaction")
(include-book "store-profile-upgrade")

; The plan's gate is a four-conjunct wrapper; the proofs below reason about
; the scan under it.
(local (in-theory (enable fn-profile-txn-observation)))

(defun fn-bs-pack-covered-names (pairs selected-lower)
  (declare (xargs :guard t))
  (if (consp pairs)
      (if (< (nfix (fn-store-event-nth 0 (car pairs))) (nfix selected-lower))
          (cons (fn-store-event-nth 1 (car pairs))
                (fn-bs-pack-covered-names (cdr pairs) selected-lower))
        nil)
    nil))

; Logical subject called by the native reclaim path.  Only surviving covered
; names are removed; missing covered names are an interrupted prior attempt,
; and the selected observer separately requires an exact contiguous suffix.
; The namespace bound and grammar are the open path's own gate,
; `fn-profile-txn-observation' (books/store-profile-upgrade): the plan reads
; the same observation the next open reads, with one owner of field 4.
(defun fn-bs-pack-reclaim-plan (names maximum selected-lower)
  (declare (xargs :guard t))
  (let ((selected (fn-profile-txn-observation names maximum selected-lower)))
    (if (equal selected :invalid) :invalid
      (fn-bs-pack-covered-names (third selected) selected-lower))))

(defun fn-bs-pack-reclaim-steps (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (list :unlink :transactions (car names))
            (cons (list :cut "pack-reclaim-unlink")
                  (fn-bs-pack-reclaim-steps (cdr names))))
    (list (list :fsync-dir :transactions)
          (list :cut "pack-reclaim-directory"))))

(defun fn-bs-pack-reclaim-program (names maximum selected-lower)
  (declare (xargs :guard t))
  (let ((plan (fn-bs-pack-reclaim-plan names maximum selected-lower)))
    (if (equal plan :invalid) nil (fn-bs-pack-reclaim-steps plan))))

(verify-guards fn-bs-pack-covered-names)
(verify-guards fn-bs-pack-reclaim-plan)
(verify-guards fn-bs-pack-reclaim-steps)
(verify-guards fn-bs-pack-reclaim-program)

(defthm fn-bs-pack-reclaim-plan-is-selected-covered-names
  (implies (and (natp maximum) (natp selected-lower) (true-listp names)
                (<= (len names) maximum)
                (not (equal (fn-bs-txn-observation-selected names selected-lower)
                            :invalid)))
           (equal (fn-bs-pack-reclaim-plan names maximum selected-lower)
                  (fn-bs-pack-covered-names
                   (third (fn-bs-txn-observation-selected names selected-lower))
                   selected-lower)))
  :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-plan))))

(local
 (defthm fn-bs-txn-name-of-distinct-naturals
   (implies (and (natp a) (natp b) (not (equal a b)))
            (not (equal (fn-bs-txn-name a) (fn-bs-txn-name b))))
   :hints (("Goal" :use ((:instance fn-bs-txn-name-is-injective))))))

(local
 (defthm fn-bs-covered-observation-excludes-suffix-sequence
   (implies (and (natp start) (natp selected-lower)
                 (natp sequence) (<= start selected-lower)
                 (<= selected-lower sequence))
            (not (member-equal
                  (fn-bs-txn-name sequence)
                  (fn-bs-pack-covered-names
                   (fn-bs-txn-observation-covered
                    names start selected-lower)
                   selected-lower))))
   :hints (("Goal"
            :induct (fn-bs-txn-observation-covered
                     names start selected-lower)
            :in-theory (enable fn-bs-txn-observation-covered
                               fn-bs-pack-covered-names)))))

; This is the selected-observation-to-program bridge used by the crash
; theorem: every canonical suffix sequence is absent from the actual covered
; reclaim plan.
(defthm fn-bs-selected-suffix-is-not-in-reclaim-plan
  (implies (and (natp maximum) (natp selected-lower) (natp sequence)
                (<= selected-lower sequence)
                (true-listp names) (<= (len names) maximum)
                (not (equal (fn-bs-txn-observation-selected
                             names selected-lower)
                            :invalid)))
           (not (member-equal
                 (fn-bs-txn-name sequence)
                 (fn-bs-pack-reclaim-plan names maximum selected-lower))))
  :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-plan
                                      fn-bs-txn-observation-selected))))

(local
 (defthm fn-bs-pack-reclaim-steps-last
   (equal (last (fn-bs-pack-reclaim-steps names))
          (list (list :cut "pack-reclaim-directory")))
   :hints (("Goal" :induct (fn-bs-pack-reclaim-steps names)
            :in-theory (enable fn-bs-pack-reclaim-steps)))))

; The exact source text calls the logical subject above.  This executable fact
; pins the two physical cut labels to transitions rather than prose strings.
(defthm fn-bs-pack-reclaim-program-has-closing-directory-fence
  (implies (not (equal (fn-bs-pack-reclaim-plan names maximum selected-lower)
                       :invalid))
           (equal (last (fn-bs-pack-reclaim-program
                         names maximum selected-lower))
                  (list (list :cut "pack-reclaim-directory"))))
  :hints (("Goal" :in-theory (enable fn-bs-pack-reclaim-program
                                     fn-bs-pack-reclaim-steps))))

; Execute exactly the first LIMIT transitions of a program with successful
; syscall outcomes.  This is the state at the corresponding process-death
; cut; unlike fn-bs-run's trace result it gives the zero-step cut a state.
(defun fn-bs-prefix-state (bs ks steps limit groups capacity)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix limit)))
  (if (or (zp limit) (atom steps))
      bs
    (mv-let (result bs1 ks1)
      (fn-bs-step bs ks (car steps) :ok groups capacity)
      (if (equal result :ok)
          (fn-bs-prefix-state bs1 ks1 (cdr steps) (1- (nfix limit))
                              groups capacity)
        bs1))))

(defun fn-bs-reclaim-steps-avoid-namep (steps name)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (or (not (equal (caar steps) :unlink))
               (not (equal (nth 2 (car steps)) name)))
           (fn-bs-reclaim-steps-avoid-namep (cdr steps) name))
    t))

(defun fn-bs-reclaim-program-shapep (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (let ((step (car steps)))
             (or (and (equal (car step) :unlink)
                      (equal (nth 1 step) :transactions))
                 (equal step (list :cut "pack-reclaim-unlink"))
                 (equal step (list :fsync-dir :transactions))
                 (equal step (list :cut "pack-reclaim-directory"))))
           (fn-bs-reclaim-program-shapep (cdr steps)))
    t))

(defun fn-bs-pending-reclaim-safe-p (ops name)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (equal (caar ops) :del-entry)
           (equal (nth 1 (car ops)) :transactions)
           (not (equal (nth 2 (car ops)) name))
           (fn-bs-pending-reclaim-safe-p (cdr ops) name))
    (null ops)))

(defun fn-bs-exact-name-payloadp (before after name)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-lookup before :transactions name)))
    (and (equal (fn-bs-lookup after :transactions name) ino)
         (equal (fn-bs-content after ino) (fn-bs-content before ino)))))

(defun fn-bs-crash-preserves-name-payloadp (before at-cut image name)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-lookup before :transactions name)))
    (and (fn-bs-crash-imagep at-cut image)
         (equal (fn-bs-durable-entry image :transactions name) ino)
         (equal (fn-bs-durable-content image ino)
                (fn-bs-content before ino)))))

(defun fn-bs-reclaim-cut-ready-p (before at-cut name)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-exact-name-payloadp before at-cut name)
       (fn-bs-pending-reclaim-safe-p (fn-bs-pending at-cut) name)
       (fn-bs-fencedp at-cut (fn-bs-lookup before :transactions name))))

(local
 (defthm assoc-equal-of-fn-bs-del-assoc-other
   (implies (not (equal a b))
            (equal (assoc-equal a (fn-bs-del-assoc b xs))
                   (assoc-equal a xs)))
   :hints (("Goal" :induct (fn-bs-del-assoc b xs)
            :in-theory (enable fn-bs-del-assoc)))))

(local
 (defthm assoc-equal-of-fn-bs-put-assoc
   (implies key
            (equal (assoc-equal key (fn-bs-put-assoc key value xs))
                   (cons key value)))
   :hints (("Goal" :induct (fn-bs-put-assoc key value xs)
            :in-theory (enable fn-bs-put-assoc)))))

(local
 (defthm fn-bs-apply-ops-of-append
   (equal (fn-bs-apply-ops inodes dirs (append a b))
          (mv-let (inodes1 dirs1) (fn-bs-apply-ops inodes dirs a)
            (fn-bs-apply-ops inodes1 dirs1 b)))
   :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs a)
            :in-theory (enable fn-bs-apply-ops)))))

(local
 (defthm fn-bs-unlink-other-name-preserves-lookup
   (implies (not (equal removed name))
            (equal (fn-bs-lookup (mv-nth 1 (fn-bs-unlink bs :transactions removed :ok))
                                 :transactions name)
                   (fn-bs-lookup bs :transactions name)))
   :hints (("Goal" :in-theory (enable fn-bs-unlink fn-bs-lookup fn-bs-view
                                       fn-bs-apply-ops fn-bs-apply-op)))))

(local
 (defthm fn-bs-unlink-preserves-content
   (equal (fn-bs-content (mv-nth 1 (fn-bs-unlink bs dir removed :ok)) ino)
          (fn-bs-content bs ino))
   :hints (("Goal" :in-theory (enable fn-bs-unlink fn-bs-content fn-bs-view
                                       fn-bs-apply-ops fn-bs-apply-op)))))

(local
 (defthm fn-bs-pending-reclaim-safe-of-append-delete
   (implies (and (fn-bs-pending-reclaim-safe-p ops name)
                 (not (equal removed name)))
            (fn-bs-pending-reclaim-safe-p
             (append ops (list (list :del-entry :transactions removed))) name))
   :hints (("Goal" :induct (fn-bs-pending-reclaim-safe-p ops name)
            :in-theory (enable fn-bs-pending-reclaim-safe-p)))))

(local
 (defthm fn-bs-unlink-other-preserves-reclaim-safe
   (implies (and (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                 (not (equal removed name)))
            (fn-bs-pending-reclaim-safe-p
             (fn-bs-pending
              (mv-nth 1 (fn-bs-unlink bs :transactions removed :ok)))
             name))
   :hints (("Goal" :in-theory (enable fn-bs-unlink
                                       fn-bs-pending-reclaim-safe-p)))))

(local
 (defthm fn-bs-ops-for-ino-append-delete
   (equal (fn-bs-ops-for-ino
           (append ops (list (list :del-entry dir removed))) ino)
          (fn-bs-ops-for-ino ops ino))
   :hints (("Goal" :induct (fn-bs-ops-for-ino ops ino)
            :in-theory (enable fn-bs-ops-for-ino)))))

(local
 (defthm fn-bs-unlink-preserves-fencedp
   (equal (fn-bs-fencedp (mv-nth 1 (fn-bs-unlink bs dir removed :ok)) ino)
          (fn-bs-fencedp bs ino))
   :hints (("Goal" :in-theory (enable fn-bs-unlink fn-bs-fencedp
                                       fn-bs-ops-for-ino)))))

(local
 (defthm fn-bs-ops-for-dir-of-reclaim-safe
   (implies (fn-bs-pending-reclaim-safe-p ops name)
            (equal (fn-bs-ops-for-dir ops :transactions) ops))
   :hints (("Goal" :induct (fn-bs-pending-reclaim-safe-p ops name)
            :in-theory (enable fn-bs-pending-reclaim-safe-p fn-bs-ops-for-dir)))))

(local
 (defthm fn-bs-ops-not-for-dir-of-reclaim-safe
   (implies (fn-bs-pending-reclaim-safe-p ops name)
            (equal (fn-bs-ops-not-for-dir ops :transactions) nil))
   :hints (("Goal" :induct (fn-bs-pending-reclaim-safe-p ops name)
            :in-theory (enable fn-bs-pending-reclaim-safe-p
                               fn-bs-ops-not-for-dir)))))

(local
 (defthm fn-bs-fsync-dir-preserves-view-lookup
   (implies (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) protected)
            (equal (fn-bs-lookup
                    (mv-nth 1 (fn-bs-fsync-dir bs :transactions :ok))
                    :transactions name)
                   (fn-bs-lookup bs :transactions name)))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                                       fn-bs-lookup fn-bs-view)))))

(local
 (defthm fn-bs-fsync-dir-preserves-view-content
   (implies (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) protected)
            (equal (fn-bs-content
                    (mv-nth 1 (fn-bs-fsync-dir bs :transactions :ok)) ino)
                   (fn-bs-content bs ino)))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                                       fn-bs-content fn-bs-view)))))

(local
 (defthm fn-bs-fsync-reclaim-safe-leaves-safe
   (implies (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
            (fn-bs-pending-reclaim-safe-p
             (fn-bs-pending
              (mv-nth 1 (fn-bs-fsync-dir bs :transactions :ok)))
             name))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                                       fn-bs-pending-reclaim-safe-p)))))

(local
 (defthm fn-bs-reclaim-safe-has-no-inode-ops
   (implies (fn-bs-pending-reclaim-safe-p ops name)
            (equal (fn-bs-ops-for-ino ops ino) nil))
   :hints (("Goal" :induct (fn-bs-pending-reclaim-safe-p ops name)
            :in-theory (enable fn-bs-pending-reclaim-safe-p
                               fn-bs-ops-for-ino)))))

(local
 (defthm fn-bs-reclaim-safe-has-no-protected-name-ops
   (implies (fn-bs-pending-reclaim-safe-p ops name)
            (equal (fn-bs-ops-for-name ops :transactions name) nil))
   :hints (("Goal" :induct (fn-bs-pending-reclaim-safe-p ops name)
            :in-theory (enable fn-bs-pending-reclaim-safe-p
                               fn-bs-ops-for-name)))))

(local
 (defthm fn-bs-fsync-dir-preserves-fencedp
   (implies (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) protected)
            (equal (fn-bs-fencedp
                    (mv-nth 1 (fn-bs-fsync-dir bs :transactions :ok)) ino)
                   (fn-bs-fencedp bs ino)))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                                       fn-bs-fencedp fn-bs-ops-for-ino)))))

(defthm fn-bs-prefix-of-reclaim-preserves-unmentioned-name
  (implies (and (fn-bs-reclaim-program-shapep steps)
                (fn-bs-reclaim-steps-avoid-namep steps name)
                (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                (fn-bs-fencedp bs (fn-bs-lookup bs :transactions name)))
           (fn-bs-exact-name-payloadp
            bs (fn-bs-prefix-state bs ks steps limit groups capacity) name))
  :hints (("Goal" :induct (fn-bs-prefix-state bs ks steps limit groups capacity)
           :in-theory (enable fn-bs-prefix-state
                              fn-bs-reclaim-program-shapep
                              fn-bs-reclaim-steps-avoid-namep
                              fn-bs-exact-name-payloadp
                              fn-bs-step))))

(defthm fn-bs-prefix-of-reclaim-maintains-cut-readiness
  (implies (and (fn-bs-reclaim-program-shapep steps)
                (fn-bs-reclaim-steps-avoid-namep steps name)
                (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                (fn-bs-fencedp bs (fn-bs-lookup bs :transactions name)))
           (fn-bs-reclaim-cut-ready-p
            bs (fn-bs-prefix-state bs ks steps limit groups capacity) name))
  :hints (("Goal" :induct (fn-bs-prefix-state bs ks steps limit groups capacity)
           :in-theory (enable fn-bs-prefix-state
                              fn-bs-reclaim-program-shapep
                              fn-bs-reclaim-steps-avoid-namep
                              fn-bs-reclaim-cut-ready-p
                              fn-bs-exact-name-payloadp
                              fn-bs-step))))

(defthm fn-bs-pack-reclaim-steps-have-reclaim-shape
  (fn-bs-reclaim-program-shapep (fn-bs-pack-reclaim-steps names))
  :hints (("Goal" :induct (fn-bs-pack-reclaim-steps names)
           :in-theory (enable fn-bs-pack-reclaim-steps
                              fn-bs-reclaim-program-shapep))))

(defthm fn-bs-pack-reclaim-steps-avoid-an-unplanned-name
  (implies (not (member-equal name names))
           (fn-bs-reclaim-steps-avoid-namep
            (fn-bs-pack-reclaim-steps names) name))
  :hints (("Goal" :induct (fn-bs-pack-reclaim-steps names)
           :in-theory (enable fn-bs-pack-reclaim-steps
                              fn-bs-reclaim-steps-avoid-namep))))

; Semantic preservation for the actual program supplied to fn-bs-run by the
; native reclaim caller.  SELECTED-LOWER's uncovered suffix supplies NAME;
; the selected observation establishes that NAME is not in its covered plan.
(defthm fn-bs-pack-reclaim-program-prefix-preserves-uncovered-payload
  (let ((plan (fn-bs-pack-reclaim-plan names maximum selected-lower)))
    (implies (and (not (equal plan :invalid))
                  (not (member-equal name plan))
                  (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                  (fn-bs-fencedp bs (fn-bs-lookup bs :transactions name)))
             (fn-bs-exact-name-payloadp
              bs
              (fn-bs-prefix-state
               bs ks (fn-bs-pack-reclaim-program names maximum selected-lower)
               limit groups capacity)
              name)))
  :hints (("Goal"
           :use ((:instance fn-bs-prefix-of-reclaim-preserves-unmentioned-name
                            (steps (fn-bs-pack-reclaim-program
                                    names maximum selected-lower))))
           :in-theory (enable fn-bs-pack-reclaim-program fn-bs-fencedp))))

(defthm fn-bs-reclaim-cut-crash-preserves-exact-payload
  (implies (and (stringp name)
                (fn-bs-reclaim-cut-ready-p before at-cut name)
                (fn-bs-crash-imagep at-cut image))
           (fn-bs-crash-preserves-name-payloadp before at-cut image name))
  :hints (("Goal"
           :use ((:instance fn-bs-crash-keeps-untouched-entry
                            (s at-cut) (dir :transactions))
                 (:instance fn-bs-lookup-of-an-untouched-name
                            (s at-cut) (dir :transactions))
                 (:instance fn-bs-content-of-a-fenced-inode
                            (s at-cut)
                            (ino (fn-bs-lookup before :transactions name)))
                 (:instance fn-bs-crash-keeps-fenced-content
                            (s at-cut)
                            (ino (fn-bs-lookup before :transactions name))))
           :in-theory (enable fn-bs-reclaim-cut-ready-p
                              fn-bs-exact-name-payloadp
                              fn-bs-crash-preserves-name-payloadp))))

(defthm fn-bs-pack-reclaim-program-crash-preserves-uncovered-sequence
  (let* ((plan (fn-bs-pack-reclaim-plan names maximum selected-lower))
         (name (fn-bs-txn-name sequence))
         (at-cut (fn-bs-prefix-state
                  bs ks (fn-bs-pack-reclaim-program names maximum selected-lower)
                  limit groups capacity)))
    (implies (and (not (member-equal name plan))
                  (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                  (fn-bs-crash-imagep at-cut image))
             (fn-bs-crash-preserves-name-payloadp bs at-cut image name)))
  :hints (("Goal"
           :use ((:instance fn-bs-prefix-of-reclaim-maintains-cut-readiness
                            (steps (fn-bs-pack-reclaim-program
                                    names maximum selected-lower))
                            (name (fn-bs-txn-name sequence)))
                 (:instance fn-bs-pack-reclaim-steps-have-reclaim-shape
                            (names (fn-bs-pack-reclaim-plan
                                    names maximum selected-lower)))
                 (:instance fn-bs-pack-reclaim-steps-avoid-an-unplanned-name
                            (names (fn-bs-pack-reclaim-plan
                                    names maximum selected-lower))
                            (name (fn-bs-txn-name sequence)))
                 (:instance fn-bs-reclaim-cut-crash-preserves-exact-payload
                            (before bs)
                            (name (fn-bs-txn-name sequence))
                            (at-cut (fn-bs-prefix-state
                                     bs ks
                                     (fn-bs-pack-reclaim-program
                                      names maximum selected-lower)
                                     limit groups capacity))))
           :in-theory (enable fn-bs-pack-reclaim-program fn-bs-fencedp))))

(defthm fn-bs-selected-reclaim-crash-preserves-suffix-payload
  (let* ((name (fn-bs-txn-name sequence))
         (at-cut (fn-bs-prefix-state
                  bs ks (fn-bs-pack-reclaim-program names maximum selected-lower)
                  limit groups capacity)))
    (implies (and (natp maximum) (natp selected-lower) (natp sequence)
                  (<= selected-lower sequence)
                  (true-listp names) (<= (len names) maximum)
                  (not (equal (fn-bs-txn-observation-selected
                               names selected-lower)
                              :invalid))
                  (fn-bs-pending-reclaim-safe-p (fn-bs-pending bs) name)
                  (fn-bs-crash-imagep at-cut image))
             (fn-bs-crash-preserves-name-payloadp bs at-cut image name)))
  :hints (("Goal"
           :use ((:instance fn-bs-selected-suffix-is-not-in-reclaim-plan)
                 (:instance
                  fn-bs-pack-reclaim-program-crash-preserves-uncovered-sequence)))))
