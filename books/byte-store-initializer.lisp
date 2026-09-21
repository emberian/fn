; fn: the current fresh-store initializer over the byte store.
;
; This is deliberately separate from byte-store-programs' historical
; fn-bs-init-program.  Store.initialize in tools/run_store.py:980 calls
; _safe_directory for root, transactions, staging and config; that helper
; fences the parent after a fresh mkdir.  It then opens writer.lock, publishes
; config.json, config/00000001.cfg and allocation-frontier.json, and carries
; out five final barriers.  All durable calls have a following :cut here.
;
; This book covers only the fresh successful/error path.  An existing
; directory/file is a different host branch: _safe_directory reads it and
; _publish_initial_file returns False on EEXIST.  It is named below as open;
; no theorem in this book treats it as a retry of the fresh path.

(in-package "ACL2")
(include-book "byte-store-relation")

(defconst *fn-bsi-lock-name* "writer.lock")
(defconst *fn-bsi-config-record-name* "00000001.cfg")

; The three stage names stand for the pid/random names the host creates.  A
; finished publication leaves its staging name absent from the *view*, even
; though the create/unlink pair remains pending, so equal names work in this
; fresh program.  An O_EXCL EEXIST against an entry that was already present
; is a separate existing-entry branch and remains open.  This boundary does
; not mention the desired kernel relation or metadata decoding.
(defun fn-bsi-fresh-inputp (config config-record frontier config-stage record-stage frontier-stage)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cbor-octet-listp config)
       (fn-cbor-octet-listp config-record)
       (fn-cbor-octet-listp frontier)
       ; Every current generator emits a nonempty frame.  This is a physical
       ; publication precondition, not a claim about what the bytes decode to.
       (consp config)
       (consp config-record)
       (consp frontier)
       (fn-bs-namep config-stage)
       (fn-bs-namep record-stage)
       (fn-bs-namep frontier-stage)))

(defun fn-bsi-publish-steps (label stage target-dir target-name octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut (string-append label "created"))
        (list :write-all :staging stage octets)
        (list :cut (string-append label "written"))
        (list :fsync-file :staging stage)
        (list :cut (string-append label "file-fenced"))
        (list :link :staging stage target-dir target-name)
        (list :cut (string-append label "linked"))
        ; _publish_initial_file currently fences root even for a config/
        ; target.  The caller supplies the later config-directory fence.
        (list :fsync-dir :root)
        (list :cut (string-append label "root-fenced"))
        (list :unlink :staging stage)
        (list :cut (string-append label "stage-unlinked"))))

(defun fn-bsi-current-init-program (config config-record frontier
                                           config-stage record-stage frontier-stage)
  (declare (xargs :guard t :verify-guards nil))
  (append
   ; _safe_directory(root, create=True): mkdir then fsync(root.parent).
   (list (list :mkdir :parent "store" :root)
         (list :cut "init-root-mkdir")
         (list :fsync-dir :parent)
         (list :cut "init-root-parent-fenced")
         ; _open_lock(O_CREAT) on a fresh path.  The byte primitive is the
         ; fresh O_EXCL refinement; existing lock-open behavior remains open.
         (list :create :root *fn-bsi-lock-name*)
         (list :cut "init-lock-created")
         ; each remaining _safe_directory does mkdir + fsync(parent=root).
         (list :mkdir :root "transactions" :transactions)
         (list :cut "init-transactions-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-transactions-parent-fenced")
         (list :mkdir :root "staging" :staging)
         (list :cut "init-staging-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-staging-parent-fenced")
         (list :mkdir :root "config" :config)
         (list :cut "init-config-dir-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-config-dir-parent-fenced"))
   (fn-bsi-publish-steps "init-config-" config-stage :root *fn-bs-config-name* config)
   (fn-bsi-publish-steps "init-history-" record-stage :config *fn-bsi-config-record-name* config-record)
   ; The explicit post-publication config-directory barrier is not redundant:
   ; _publish_initial_file fenced :root, while the link above targets :config.
   (list (list :fsync-dir :config)
         (list :cut "init-config-history-fenced"))
   (fn-bsi-publish-steps "init-frontier-" frontier-stage :root *fn-bs-frontier-name* frontier)
   ; Store.initialize:1014-1024, including every actual init-barrier site.
   (list (list :fsync-file :root *fn-bs-config-name*)
         (list :cut "init-final-config-file-fenced")
        (list :fsync-file :config *fn-bsi-config-record-name*)
         (list :cut "init-final-config-record-file-fenced")
        (list :fsync-file :root *fn-bs-frontier-name*)
         (list :cut "init-final-frontier-file-fenced")
         (list :fsync-dir :transactions)
         (list :cut "init-transactions-fenced")
         (list :fsync-dir :root)
         (list :cut "init-root-fenced")
         (list :fsync-dir :parent)
         (list :cut "init-parent-fenced"))))

; The exact fresh final byte representation.  Staging cleanup is intentionally
; pending: os.unlink has no following staging-directory fsync in this host
; path.  The relation's authority namespace remains root/transactions; config
; history and writer.lock are represented without pretending they are kernel
; records.
(defun fn-bsi-current-initial-image (config config-record frontier
                                            config-stage record-stage frontier-stage)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make 4
              (list (cons 3 frontier) (cons 2 config-record)
                    (cons 1 config) (cons 0 nil))
              (list (cons :config (list (cons *fn-bsi-config-record-name* 2)))
                    (cons :staging nil)
                    (cons :transactions nil)
                    ; fn-bs-put-assoc appends a new root entry, so this is
                    ; the host issue order rather than a sorted namespace.
                    (cons :root (list (cons *fn-bsi-lock-name* 0)
                                      (cons "transactions" :transactions)
                                      (cons "staging" :staging)
                                      (cons "config" :config)
                                      (cons *fn-bs-config-name* 1)
                                      (cons *fn-bs-frontier-name* 3)))
                    (cons :parent (list (cons "store" :root))))
              (list (list :set-entry :staging config-stage 1)
                    (list :del-entry :staging config-stage)
                    (list :set-entry :staging record-stage 2)
                    (list :del-entry :staging record-stage)
                    (list :set-entry :staging frontier-stage 3)
                    (list :del-entry :staging frontier-stage))
              4))

; This is a separate concrete representation lemma rather than a claim that
; the obsolete metadata-only initializer was the host path.  This lemma, not
; fn-bsi-current-init-program-establishes-relation, carries the durability
; claim for config/00000001.cfg: fn-bs-store-relation currently observes only
; :root and :transactions and is intentionally blind to :config and the lock.
(local
 (defun fn-bsi-find-run (term)
   (declare (xargs :mode :program))
   (cond ((atom term) nil)
         ((equal (car term) 'fn-bs-run) term)
         ((equal (car term) 'quote) nil)
         (t (or (fn-bsi-find-run (car term))
                (fn-bsi-find-run (cdr term)))))))
(local
 (defun fn-bsi-unroll-hint (clause stable-under-simplificationp)
   (declare (xargs :mode :program))
   (let ((term (and stable-under-simplificationp (fn-bsi-find-run clause))))
     (and term
          (list :computed-hint-replacement
                '((fn-bsi-unroll-hint clause stable-under-simplificationp))
                :expand (list term))))))
(local
 (defthm fn-bsi-take-of-len
   (implies (true-listp xs) (equal (fn-bs-take (len xs) xs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-bsi-octets-are-true-lists
   (implies (fn-cbor-octet-listp xs) (true-listp xs))))
(local
 (defthm fn-bsi-consp-has-positive-len
   (implies (consp xs) (< 0 (len xs)))))
(local (defthm fn-bsi-nthcdr-of-nil (equal (nthcdr n nil) nil)))
(local
 (defthm fn-bsi-append-nil
   (implies (true-listp xs) (equal (append xs nil) xs))))
(local
 (defthm fn-bsi-splice-new-file
   (implies (true-listp octets)
            (equal (fn-bs-splice nil 0 octets) octets))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))

(defthm fn-bsi-current-init-program-establishes-current-image
  (implies (fn-bsi-fresh-inputp config config-record frontier
                                config-stage record-stage frontier-stage)
           (equal
            (car (car (last
             (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bsi-current-init-program config config-record frontier
                                                     config-stage record-stage frontier-stage)
                        nil nil nil))))
            (fn-bsi-current-initial-image config config-record frontier
                                          config-stage record-stage frontier-stage)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :cases ((consp config) (consp config-record) (consp frontier))
           :in-theory (e/d (fn-bsi-fresh-inputp fn-bsi-current-init-program
                              fn-bsi-publish-steps fn-bs-step fn-bs-mkdir
                              fn-bs-create fn-bs-write fn-bs-fsync-file
                              fn-bs-fsync-dir fn-bs-link fn-bs-unlink
                              fn-bs-fence-file fn-bs-fence-dir fn-bs-lookup
                              fn-bs-content fn-bs-view
                              fn-bs-apply-ops-inodes-are-apply-writes
                              fn-bs-apply-ops-dirs-are-apply-entries
                              fn-bs-splice)
                            (fn-bs-apply-ops fn-bs-run)))
          (fn-bsi-unroll-hint clause stable-under-simplificationp)))

; Conditional relation-projection proof.  fn-bsi-fresh-inputp is an I/O/domain
; contract; fn-bs-initial-inputp is the independent metadata-to-kernel binding.
; Keeping them separate makes it possible to test each missing condition
; honestly.  This theorem does not establish config-history durability because
; fn-bs-store-relation has no :config clause; cite the image theorem above for
; that physical fact.
(defthm fn-bsi-current-init-program-establishes-relation
  (implies (and (fn-bsi-fresh-inputp config config-record frontier
                                     config-stage record-stage frontier-stage)
                (fn-bs-initial-inputp config frontier))
           (fn-bs-store-relation
            (car (car (last
             (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                        (fn-bsi-current-init-program config config-record frontier
                                                     config-stage record-stage frontier-stage)
                        nil nil nil))))
            (fn-sf-initial-state)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bsi-current-init-program-establishes-current-image)
           :in-theory (e/d (fn-bsi-current-initial-image fn-bs-store-relation
                              fn-bs-statep fn-bs-durable-entry fn-bs-durable-content
                              fn-bs-fencedp fn-bs-dir-quietp fn-bs-view fn-bs-content
                              fn-bs-lookup fn-sf-statep fn-sf-crash-imagep
                              fn-bs-durable fn-bs-durable-names
                              fn-bs-durable-frontier fn-bs-durable-records
                              fn-bs-replay-visiblep fn-bs-pending-shape-okp
                              fn-bs-pending-matches-phase fn-bs-contiguous-namesp
                              fn-bs-txn-names fn-bs-read-records
                              fn-bs-pending-entry-targets fn-bs-authority-inode-list
                              fn-bs-all-fencedp fn-bs-authority-fencedp
                              fn-bs-inode-list-knownp fn-bs-authority-knownp)
                            (fn-bs-apply-ops)))))
