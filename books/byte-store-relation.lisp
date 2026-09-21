; First K0 packet: initialization and the program-input boundary.
; The full arbitrary-program statement in crash-model-v2 is false: byte
; arguments must describe the kernel candidate.  No crash freedom changes.
(in-package "ACL2")
(include-book "byte-store-scan")
(include-book "byte-store-programs")

(defun fn-bs-initial-inputp (config frontier)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cbor-octet-listp config)
       (fn-cbor-octet-listp frontier)
       (fn-bs-config-okp config)
       (equal (fn-bs-frontier-decode frontier) 0)))

(defun fn-bs-initial-image (unit config frontier)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make unit
              (list (cons 1 frontier) (cons 0 config))
              (list (cons :staging nil) (cons :transactions nil)
                    (cons :root (list (cons "transactions" :transactions)
                                     (cons "staging" :staging)
                                     (cons *fn-bs-config-name* 0)
                                     (cons *fn-bs-frontier-name* 1)))
                    (cons :parent (list (cons "store" :root))))
              '((:set-entry :staging ".init-config" 0)
                (:del-entry :staging ".init-config")
                (:set-entry :staging ".init-frontier" 1)
                (:del-entry :staging ".init-frontier")) 2))

(defthm fn-bs-initial-image-establishes-relation
  (implies (and (posp unit)
                (fn-cbor-octet-listp config)
                (fn-cbor-octet-listp frontier)
                (fn-bs-config-okp config)
                (equal (fn-bs-frontier-decode frontier) 0))
           (fn-bs-store-relation (fn-bs-initial-image unit config frontier)
                                (fn-sf-initial-state)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-store-relation fn-bs-statep
                                    fn-bs-durable-entry fn-bs-durable-content
                                    fn-bs-fencedp fn-bs-dir-quietp
                                    fn-bs-view fn-bs-content fn-bs-lookup
                                    fn-sf-statep fn-sf-crash-imagep
                                    fn-bs-durable fn-bs-durable-names
                                    fn-bs-durable-frontier fn-bs-durable-records
                                    fn-bs-replay-visiblep fn-bs-pending-shape-okp
                                    fn-bs-pending-matches-phase fn-bs-contiguous-namesp
                                    fn-bs-txn-names fn-bs-read-records
                                    fn-bs-pending-entry-targets fn-bs-authority-inode-list
                                    fn-bs-all-fencedp fn-bs-authority-fencedp
                                    fn-bs-inode-list-knownp fn-bs-authority-knownp))))

(local
 (defthm fn-bs-k0-take-of-len
   (implies (true-listp xs) (equal (fn-bs-take (len xs) xs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-bs-k0-octets-are-true-lists
   (implies (fn-cbor-octet-listp xs) (true-listp xs))))

(local
 (defthm fn-bs-k0-empty-true-list
   (implies (true-listp xs)
            (equal (equal (len xs) 0) (equal xs nil)))))

(local (defthm fn-bs-k0-nthcdr-of-nil
         (equal (nthcdr n nil) nil)))
(local (defthm fn-bs-k0-append-nil
         (implies (true-listp xs) (equal (append xs nil) xs))))
(local (defthm fn-bs-k0-splice-new-file
         (implies (true-listp octets)
                  (equal (fn-bs-splice nil 0 octets) octets))
         :hints (("Goal" :in-theory (enable fn-bs-splice)))))

(local
 (defun fn-bs-k0-find-run (term)
   (declare (xargs :mode :program))
   (cond ((atom term) nil)
         ((equal (car term) 'fn-bs-run) term)
         ((equal (car term) 'quote) nil)
         (t (or (fn-bs-k0-find-run (car term))
                (fn-bs-k0-find-run (cdr term)))))))
(local
 (defun fn-bs-k0-unroll-hint (clause stable-under-simplificationp)
   (declare (xargs :mode :program))
   (let ((term (and stable-under-simplificationp
                    (fn-bs-k0-find-run clause))))
     (and term
          (list :computed-hint-replacement
                '((fn-bs-k0-unroll-hint clause stable-under-simplificationp))
                :expand (list term))))))

(defthm fn-bs-init-program-establishes-initial-image
  (implies (and (fn-cbor-octet-listp config)
                (fn-cbor-octet-listp frontier))
           (equal
            (car (car (last
             (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bs-init-program config frontier) nil nil nil))))
            (fn-bs-initial-image 4 config frontier)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
                  :cases ((consp config) (consp frontier))
                  :in-theory (e/d (fn-bs-step fn-bs-mkdir
                                    fn-bs-create fn-bs-write fn-bs-fsync-file
                                    fn-bs-fsync-dir fn-bs-link fn-bs-unlink
                                    fn-bs-fence-file fn-bs-fence-dir
                                    fn-bs-lookup fn-bs-content fn-bs-view
                                    fn-bs-apply-ops-inodes-are-apply-writes
                                    fn-bs-apply-ops-dirs-are-apply-entries
                                    fn-bs-splice)
                                   (fn-bs-apply-ops fn-bs-run)))
          (fn-bs-k0-unroll-hint clause stable-under-simplificationp)))

; This recognizes host input values, without asking that any output pair
; satisfy the relation.  The outcome domain is a separate per-step issue.
(defun fn-bs-frontier-inputp (ks stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-sf-phase ks) :ready)
       (< (fn-sf-frontier ks) *fn-sf-max-uint*)
       (fn-bs-namep stage)
       (fn-cbor-octet-listp octets)
       (equal (fn-bs-frontier-decode octets) (1+ (fn-sf-frontier ks)))))

(defun fn-bs-record-inputp (ks stage name frame)
  (declare (xargs :guard t :verify-guards nil))
  (and (equal (fn-sf-phase ks) :record-staged)
       (fn-bs-namep stage)
       (fn-cbor-octet-listp frame)
       (equal (fn-bs-record-of-octets frame) (fn-sf-record-candidate ks))
       (equal name (fn-bs-txn-name
                    (fn-record-sequence (fn-sf-record-candidate ks))))))

; Keystones name the interpreted program, not only its representation.
(defthm fn-bs-init-program-establishes-relation
  (implies (fn-bs-initial-inputp config frontier)
           (fn-bs-store-relation
            (car (car (last
             (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bs-init-program config frontier) nil nil nil))))
            (fn-sf-initial-state)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-init-program-establishes-initial-image
                 (:instance fn-bs-initial-image-establishes-relation (unit 4)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-bs-initial-inputp (:executable-counterpart posp))))))

(defun fn-bs-run-relatedp (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (fn-bs-store-relation (car (car pairs)) (cdr (car pairs)))
           (fn-bs-run-relatedp (cdr pairs)))
    (null pairs)))

; A complete first allocation, with an arbitrary staging name and arbitrary
; valid codec octets. Every syscall boundary and every cut stays in the run.
; Error outcomes, non-empty transaction histories, and recovery establishment
; remain the general K0 obligation; none is a hypothesis disguised as a proof.
(local
 (deftheory fn-bs-k0-frontier-theory
  (e/d (fn-bs-step fn-bs-create fn-bs-write fn-bs-fsync-file
                 fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file fn-bs-fence-dir
                 fn-bs-lookup fn-bs-content fn-bs-view
                 fn-bs-apply-ops-inodes-are-apply-writes
                 fn-bs-apply-ops-dirs-are-apply-entries fn-bs-splice
                 fn-bs-store-relation fn-bs-statep
                 fn-bs-durable-entry fn-bs-durable-content
                 fn-bs-fencedp fn-bs-dir-quietp
                 fn-sf-statep fn-sf-crash-imagep fn-sf-dispatch
                 fn-bs-durable fn-bs-durable-names
                 fn-bs-durable-frontier fn-bs-durable-records
                 fn-bs-replay-visiblep fn-bs-pending-shape-okp
                 fn-bs-pending-matches-phase fn-bs-contiguous-namesp
                 fn-bs-txn-names fn-bs-read-records
                 fn-bs-pending-entry-targets fn-bs-authority-inode-list
                 fn-bs-all-fencedp fn-bs-authority-fencedp
                 fn-bs-inode-list-knownp fn-bs-authority-knownp)
                (fn-bs-apply-ops fn-bs-run))))

(defthm fn-bs-first-frontier-program-preserves-relation
  (implies (and (posp unit)
                (fn-bs-initial-inputp config frontier)
                (fn-bs-frontier-inputp (fn-sf-initial-state) stage next))
           (fn-bs-run-relatedp
            (fn-bs-run (fn-bs-initial-image unit config frontier)
                       (fn-sf-initial-state)
                       (fn-bs-frontier-program stage next) nil nil nil)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (theory 'fn-bs-k0-frontier-theory))
          (fn-bs-k0-unroll-hint clause stable-under-simplificationp)))


(defthm fn-bs-first-frontier-program-completes
  (implies (and (fn-cbor-octet-listp config)
                (fn-cbor-octet-listp frontier)
                (fn-cbor-octet-listp next)
                (stringp stage))
           (let ((run (fn-bs-run (fn-bs-initial-image unit config frontier)
                                (fn-sf-initial-state)
                                (fn-bs-frontier-program stage next) nil nil nil)))
             (and (equal (len run) (len (fn-bs-frontier-program stage next)))
                  (equal (fn-sf-phase (cdr (car (last run)))) :reserved))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (theory 'fn-bs-k0-frontier-theory))
          (fn-bs-k0-unroll-hint clause stable-under-simplificationp)))

; Counterexample to the unqualified K0 formula: recycling the old frontier
; bytes in an otherwise valid initialized run violates the relation at the
; rename. The process nevertheless reaches :reserved (the completion lemma
; above), so completion alone cannot substitute for the byte/value contract.
(defthm fn-bs-first-frontier-program-rejects-old-frontier-bytes
  (implies (and (posp unit)
                (fn-bs-initial-inputp config frontier)
                (stringp stage))
           (not (fn-bs-run-relatedp
                 (fn-bs-run (fn-bs-initial-image unit config frontier)
                            (fn-sf-initial-state)
                            (fn-bs-frontier-program stage frontier) nil nil nil))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (theory 'fn-bs-k0-frontier-theory))
          (fn-bs-k0-unroll-hint clause stable-under-simplificationp)))
