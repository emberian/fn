; Teeth for the actual P-RECORD file-fence cut.  The second publication
; follows an earlier acknowledged record, so the retained Store is not empty.
(in-package "ACL2")
(include-book "../../books/byte-store-record-provenance")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bsk6-start () (car (bsk5-frontier-2)))
(defun bsk6-file-cut () (car (nth 5 (bsk5-record-2-run))))

(assert-event
 (and (fn-bs-statep (bsk6-start))
      (not (fn-bs-lookup (bsk6-start) :staging ".stage-k5-2"))
      (fn-bs-fencedp (bsk6-file-cut) (fn-bs-next-ino (bsk6-start)))
      (equal (fn-bs-durable-content
              (bsk6-file-cut) (fn-bs-next-ino (bsk6-start)))
             (bsk5-frame-2))
      (equal (fn-bs-durable-records (bsk6-file-cut))
             (list *bsk5-record*))))

; Name grammar is deliberately absent from the raw-byte theorem.  The
; executable byte interpreter can stage under NIL; the host input guard
; rejects that key before any syscall.  It is a positive separation witness
; for the stronger theorem, not a fabricated failure of a redundant premise.
(assert-event
 (let* ((bs (bsk6-start))
        (cut (car (nth 5 (fn-bs-run
                          bs (cdr (bsk5-frontier-2))
                          (fn-bs-record-program nil (fn-bs-txn-name 1)
                                                (bsk5-frame-2))
                          nil *bsk5-groups* *bsk5-capacity*)))))
   (and (not (fn-bs-namep nil))
        (not (fn-bs-lookup bs :staging nil))
        (equal (fn-bs-durable-content cut (fn-bs-next-ino bs))
               (bsk5-frame-2)))))

; An already occupied staging name stops at O_EXCL, before any write/fence.
(assert-event
 (fn-bs-lookup (car (bsk5-linked-2)) :staging ".stage-k5-2"))
(must-fail
 (assert-event
  (let* ((bs (car (bsk5-linked-2)))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-linked-2))
                           (fn-bs-record-program ".stage-k5-2"
                                                 (fn-bs-txn-name 1)
                                                 (bsk5-frame-2))
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs))
           (bsk5-frame-2)))))

; A non-list is not an octet frame.  write-all accepts zero octets, so the
; file-fence cut cannot equal that malformed argument.
(must-fail
 (assert-event
  (let* ((bs (bsk6-start))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-frontier-2))
                           (fn-bs-record-program ".stage-k6-atom"
                                                 (fn-bs-txn-name 1) 65)
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) 65))))

; The state invariant excludes a stale pending write to the unallocated
; next inode.  If admitted, that write can leave trailing bytes after the
; shorter new frame even though the new write and fsync succeed.
(defun bsk6-invalid-pending-write ()
  (let ((bs (bsk6-start)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :write (fn-bs-next-ino bs) 0 '(99 88))))
                (fn-bs-next-ino bs))))
(assert-event
 (not (fn-bs-statep (bsk6-invalid-pending-write))))
(must-fail
 (assert-event
  (let* ((bs (bsk6-invalid-pending-write))
         (cut (car (nth 5 (fn-bs-run
                           bs (cdr (bsk5-frontier-2))
                           (fn-bs-record-program ".stage-k6-bad-state"
                                                 (fn-bs-txn-name 1) '(65))
                           nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) '(65)))))

; At the actual P-RECORD link cut the final name aliases the newly
; allocated, already fenced inode.  Its raw octets are the full frame and
; the first record remains in the durable prefix.
(defun bsk6-prepared ()
  (fn-sf-prepare-record (cdr (bsk5-frontier-2)) *bsk5-record-2*
                        *bsk5-groups* *bsk5-capacity*))
(assert-event
 (let* ((bs (bsk6-start)) (ks (bsk6-prepared))
        (name (fn-bs-txn-name 1))
        (file (bsk6-file-cut))
        (linked (car (nth 8 (bsk5-record-2-run)))))
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks ".stage-k5-2" name (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (not (fn-bs-lookup file :transactions name))
        (equal (fn-bs-lookup linked :transactions name)
               (fn-bs-next-ino bs))
        (fn-bs-fencedp linked (fn-bs-next-ino bs))
        (equal (fn-bs-durable-content linked (fn-bs-next-ino bs))
               (bsk5-frame-2))
        (equal (fn-bs-durable-records linked)
               (list *bsk5-record*)))))

; A stale pending write to the next inode leaves an extra suffix after
; the new frame.  This separates fn-bs-statep from mere table shape.
(defun bsk6-invalid-link-start ()
  (let ((bs (bsk6-start)))
    (fn-bs-make
     (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
     (append (fn-bs-pending bs)
             (list (list :write (fn-bs-next-ino bs)
                         (len (bsk5-frame-2)) '(99))))
     (fn-bs-next-ino bs))))
(assert-event (not (fn-bs-statep (bsk6-invalid-link-start))))
(must-fail
 (assert-event
  (let* ((bs (bsk6-invalid-link-start))
         (linked (car (nth 8
                           (fn-bs-run bs (bsk6-prepared)
                                      (fn-bs-record-program
                                       ".stage-k5-2" (fn-bs-txn-name 1)
                                       (bsk5-frame-2))
                                      nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content linked (fn-bs-next-ino bs))
           (bsk5-frame-2)))))

; The input contract rules out a non-frame atom.  write-all sees zero
; octets, so the claimed raw frame cannot appear under the final name.
(must-fail
 (assert-event
  (let* ((bs (bsk6-start))
         (linked (car (nth 8
                           (fn-bs-run bs (bsk6-prepared)
                                      (fn-bs-record-program
                                       ".stage-k6-atom" (fn-bs-txn-name 1) 65)
                                      nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content linked (fn-bs-next-ino bs)) 65))))

; O_EXCL on an existing stage stops before the link.  This is independent
; of the destination: the final transaction name is still free here.
(must-fail
 (assert-event
  (let* ((bs (bsk6-file-cut))
         (linked (car (nth 8
                           (fn-bs-run bs (bsk6-prepared)
                                      (fn-bs-record-program
                                       ".stage-k5-2" (fn-bs-txn-name 1)
                                       (bsk5-frame-2))
                                      nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-lookup linked :transactions (fn-bs-txn-name 1))
           (fn-bs-next-ino bs)))))

; A preexisting final name makes link return EEXIST even with a fresh
; stage and well-formed frame.  Use the earlier durable inode as its target.
(defun bsk6-occupied-final-start ()
  (let* ((bs (bsk6-start))
         (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0)))
         (entries (cdr (assoc-equal :transactions (fn-bs-dirs bs))))
         (dirs (fn-bs-put-assoc
                :transactions
                (fn-bs-put-assoc (fn-bs-txn-name 1) old entries)
                (fn-bs-dirs bs))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) dirs
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event
 (and (fn-bs-statep (bsk6-occupied-final-start))
      (not (fn-bs-lookup (bsk6-occupied-final-start)
                         :staging ".stage-k5-2"))
      (fn-bs-lookup (bsk6-occupied-final-start)
                    :transactions (fn-bs-txn-name 1))))
(must-fail
 (assert-event
  (let* ((bs (bsk6-occupied-final-start))
         (linked (car (nth 8
                           (fn-bs-run bs (bsk6-prepared)
                                      (fn-bs-record-program
                                       ".stage-k5-2" (fn-bs-txn-name 1)
                                       (bsk5-frame-2))
                                      nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-lookup linked :transactions (fn-bs-txn-name 1))
           (fn-bs-next-ino bs)))))

; A modeled crash that keeps the final link retains the exact raw frame.
; The scanner's one-record decoder therefore reads the same candidate.
(local
 (defthm bsk6-legal-choices-make-crash-image
   (implies (fn-bs-crash-choicesp choices (fn-bs-pending bs)
                                  (fn-bs-unit bs))
            (fn-bs-crash-imagep bs (fn-bs-crash bs choices)))
   :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                     (s bs)
                                     (image (fn-bs-crash bs choices))))))))
(defun bsk6-kept-link-image ()
  (fn-bs-crash (car (bsk5-linked-2))
               '(:drop :drop :drop :apply)))
(assert-event
 (let* ((bs (bsk6-start)) (file (bsk6-file-cut))
        (linked (car (bsk5-linked-2)))
        (image (bsk6-kept-link-image))
        (name (fn-bs-txn-name 1)))
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp (bsk6-prepared)
                              ".stage-k5-2" name (bsk5-frame-2))
        (not (fn-bs-lookup file :transactions name))
        (equal (fn-bs-ops-for-name (fn-bs-pending file)
                                   :transactions name) nil)
        (fn-bs-crash-choicesp '(:drop :drop :drop :apply)
                              (fn-bs-pending linked) (fn-bs-unit linked))
        (equal (fn-bs-lookup image :transactions name)
               (fn-bs-next-ino bs))
        (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name))
               (bsk5-frame-2))
        (equal (fn-bs-record-of
                image (fn-bs-lookup image :transactions name))
               *bsk5-record-2*))))

; Pair 10 is the actual record-attempted cut consumed by the directory
; fence argument.  The intervening kernel callback and cut leave the byte
; state at the linked cut unchanged, so the same surviving image decodes.
(assert-event
 (let* ((linked (car (nth 8 (bsk5-record-2-run))))
        (attempted (car (nth 10 (bsk5-record-2-run))))
        (image (fn-bs-crash attempted '(:drop :drop :drop :apply)))
        (name (fn-bs-txn-name 1)))
   (and (equal attempted linked)
        (fn-bs-crash-choicesp '(:drop :drop :drop :apply)
                              (fn-bs-pending attempted)
                              (fn-bs-unit attempted))
        (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name))
               (bsk5-frame-2))
        (equal (fn-bs-record-of
                image (fn-bs-lookup image :transactions name))
               *bsk5-record-2*))))

; The input relation itself excludes the earlier set/delete that made a
; surviving final name ambiguous.  The actual file-cut prefix preserves
; that quiet transaction directory, so the related-input theorem needs no
; separate no-prior-operation premise.
(assert-event
 (let* ((bs (bsk6-start)) (ks (bsk6-prepared))
        (file (bsk6-file-cut)) (name (fn-bs-txn-name 1)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks ".stage-k5-2" name (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (not (fn-bs-lookup file :transactions name))
        (equal (fn-bs-ops-for-dir (fn-bs-pending file)
                                   :transactions) nil)
        (equal (fn-bs-ops-for-name (fn-bs-pending file)
                                    :transactions name) nil)
        (fn-bs-store-relation
         (car (nth 10 (bsk5-record-2-run)))
         (cdr (nth 10 (bsk5-record-2-run))))
        (equal (fn-bs-durable-content
                (bsk6-kept-link-image)
                (fn-bs-lookup (bsk6-kept-link-image)
                              :transactions name))
               (bsk5-frame-2)))))

; Survival is a real premise: the all-drop model image omits the new name.
(must-fail
 (assert-event
  (let* ((bs (bsk6-start))
         (image (fn-bs-crash (car (bsk5-linked-2)) nil)))
    (equal (fn-bs-lookup image :transactions (fn-bs-txn-name 1))
           (fn-bs-next-ino bs)))))

; Replacing the newly fenced inode's bytes after selecting a legitimate
; image breaks raw provenance.  Such a modified image is not a model crash.
(defun bsk6-corrupted-kept-image ()
  (let* ((image (bsk6-kept-link-image))
         (ino (fn-bs-lookup image :transactions (fn-bs-txn-name 1))))
    (fn-bs-make (fn-bs-unit image)
                (fn-bs-put-assoc ino '(66) (fn-bs-inodes image))
                (fn-bs-dirs image) (fn-bs-pending image)
                (fn-bs-next-ino image))))
(must-fail
 (assert-event
  (let ((image (bsk6-corrupted-kept-image)))
    (equal (fn-bs-durable-content
            image (fn-bs-lookup image :transactions (fn-bs-txn-name 1)))
           (bsk5-frame-2)))))

; A live-absent final name is insufficient if earlier operations at that
; name remain pending.  An old set followed by a delete can leave the live
; name absent; a crash may keep the old set, drop the delete and new link.
(defun bsk6-prior-final-set-and-delete ()
  (let* ((bs (bsk6-start))
         (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0)))
         (name (fn-bs-txn-name 1)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :set-entry :transactions name old)
                              (list :del-entry :transactions name)))
                (fn-bs-next-ino bs))))
(defun bsk6-prior-run ()
  (fn-bs-run (bsk6-prior-final-set-and-delete) (bsk6-prepared)
             (fn-bs-record-program ".stage-k5-2" (fn-bs-txn-name 1)
                                   (bsk5-frame-2))
             nil *bsk5-groups* *bsk5-capacity*))
(assert-event
 (not (fn-bs-store-relation (bsk6-prior-final-set-and-delete)
                            (bsk6-prepared))))
(must-fail
 (assert-event
  (let* ((file (car (nth 5 (bsk6-prior-run))))
         (name (fn-bs-txn-name 1)))
    (equal (fn-bs-ops-for-name (fn-bs-pending file)
                               :transactions name) nil))))

; A retention Store event shares the immutable transaction namespace but is
; not an article record.  Its typed sequence is 1; the article-only accessor
; does not designate that field.  This detects an article-only P-RECORD input
; gate and executes the same second-publication crash/scan with raw FNST bytes.
(defun bsk6-retention-candidate ()
  (fn-store-retention-event-make :undertake 1 1 1
                                  "obligation-k6" "article-0" "local" 1))
(defun bsk6-retention-frame ()
  (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                 *fn-frame-store-kind*
                 (fn-store-event-encode (bsk6-retention-candidate))))
(defun bsk6-retention-prepared ()
  (fn-sf-prepare-record (cdr (bsk5-frontier-2))
                        (bsk6-retention-candidate)
                        *bsk5-groups* *bsk5-capacity*))
(defun bsk6-retention-run ()
  (fn-bs-run (bsk6-start) (bsk6-retention-prepared)
             (fn-bs-record-program ".stage-k6-retention" (fn-bs-txn-name 1)
                                   (bsk6-retention-frame))
             nil *bsk5-groups* *bsk5-capacity*))
(assert-event
 (and (equal (fn-store-event-sequence (bsk6-retention-candidate)) 1)
      (not (equal (fn-record-sequence (bsk6-retention-candidate)) 1))
      (equal (fn-sf-phase (bsk6-retention-prepared)) :record-staged)
      (fn-bs-store-relation (bsk6-start) (bsk6-retention-prepared))
      (fn-bs-store-relation
       (car (nth 10 (bsk6-retention-run)))
       (cdr (nth 10 (bsk6-retention-run))))
      (fn-bs-record-inputp (bsk6-retention-prepared)
                            ".stage-k6-retention" (fn-bs-txn-name 1)
                            (bsk6-retention-frame))))
(must-fail
 (assert-event
  (equal (fn-record-sequence (bsk6-retention-candidate)) 1)))
(assert-event
 (let* ((file (car (nth 5 (bsk6-retention-run))))
        (attempt (car (nth 10 (bsk6-retention-run))))
        (image (fn-bs-crash attempt '(:drop :drop :drop :apply)))
        (name (fn-bs-txn-name 1)))
   (and (not (fn-bs-lookup file :transactions name))
        (fn-bs-crash-choicesp '(:drop :drop :drop :apply)
                              (fn-bs-pending attempt) (fn-bs-unit attempt))
        (fn-bs-lookup image :transactions name)
        (equal (fn-bs-durable-content image
                   (fn-bs-lookup image :transactions name))
               (bsk6-retention-frame))
        (equal (fn-bs-record-of image
                   (fn-bs-lookup image :transactions name))
               (bsk6-retention-candidate))
        (equal (fn-bs-scan-records (fn-bs-scan-store image))
               (list *bsk5-record* (bsk6-retention-candidate))))))
(defun bsk6-keep-old-final-only (ops old name)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops) nil
    (cons (if (equal (car ops)
                     (list :set-entry :transactions name old))
              :apply
            (if (equal (car (car ops)) :write) nil :drop))
          (bsk6-keep-old-final-only (cdr ops) old name))))
(defun bsk6-prior-image ()
  (let* ((linked (car (nth 8 (bsk6-prior-run))))
         (old (fn-bs-durable-entry (bsk6-start)
                                   :transactions (fn-bs-txn-name 0))))
    (fn-bs-crash linked
                 (bsk6-keep-old-final-only
                  (fn-bs-pending linked) old (fn-bs-txn-name 1)))))
(assert-event
 (let* ((bs (bsk6-prior-final-set-and-delete))
        (file (car (nth 5 (bsk6-prior-run))))
        (linked (car (nth 8 (bsk6-prior-run))))
        (image (bsk6-prior-image))
        (name (fn-bs-txn-name 1))
        (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0))))
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp (bsk6-prepared)
                              ".stage-k5-2" name (bsk5-frame-2))
        (not (fn-bs-lookup file :transactions name))
        (consp (fn-bs-ops-for-name (fn-bs-pending file)
                                    :transactions name))
        (fn-bs-crash-choicesp
         (bsk6-keep-old-final-only (fn-bs-pending linked) old name)
         (fn-bs-pending linked) (fn-bs-unit linked))
        (equal (fn-bs-lookup image :transactions name) old)
        (not (equal old (fn-bs-next-ino bs))))))
(must-fail
 (assert-event
  (let ((bs (bsk6-prior-final-set-and-delete))
        (image (bsk6-prior-image)))
    (equal (fn-bs-lookup image :transactions (fn-bs-txn-name 1))
           (fn-bs-next-ino bs)))))

; K0 actual trace witness: both article and retention callbacks advance the
; logical file kernel through file success and link success at pair 10.
(defun bsk0-trace-equalp (bs ks stage name frame)
  (equal (cdr (nth 10 (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil *bsk5-groups* *bsk5-capacity*)))
         (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :ok)))
(assert-event
 (and (bsk0-trace-equalp (bsk6-start) (bsk6-prepared)
                          ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
      (bsk0-trace-equalp (bsk6-start) (bsk6-retention-prepared)
                          ".stage-k6-retention" (fn-bs-txn-name 1)
                          (bsk6-retention-frame))))

; Dropping the relation admits an already occupied final name, so link
; stops before the callback while the expected kernel advances.
(assert-event
 (let ((bs (bsk6-occupied-final-start)))
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp (bsk6-prepared) ".stage-k5-2"
                             (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2"))
        (not (fn-bs-store-relation bs (bsk6-prepared))))))
(must-fail
 (assert-event
  (bsk0-trace-equalp (bsk6-occupied-final-start) (bsk6-prepared)
                     ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))

; Dropping the typed input gate allows the caller to reuse a durable name.
(assert-event
 (let ((bs (bsk6-start)) (ks (bsk6-prepared)))
   (and (fn-bs-store-relation bs ks)
        (not (fn-bs-record-inputp ks ".stage-k5-2"
                                  (fn-bs-txn-name 0) (bsk5-frame-2)))
        (not (fn-bs-lookup bs :staging ".stage-k5-2")))))
(must-fail
 (assert-event
  (bsk0-trace-equalp (bsk6-start) (bsk6-prepared)
                     ".stage-k5-2" (fn-bs-txn-name 0) (bsk5-frame-2))))

; Dropping O_EXCL freshness stops before even the file-fence callback.
(defun bsk0-occupied-stage ()
  (mv-let (result bs)
    (fn-bs-create (bsk6-start) :staging ".stage-k5-2" :ok)
    (declare (ignore result))
    bs))
(assert-event
 (let ((bs (bsk0-occupied-stage)) (ks (bsk6-prepared)))
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks ".stage-k5-2"
                             (fn-bs-txn-name 1) (bsk5-frame-2))
        (fn-bs-lookup bs :staging ".stage-k5-2"))))
(must-fail
 (assert-event
  (bsk0-trace-equalp (bsk0-occupied-stage) (bsk6-prepared)
                     ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))

; The physical transaction-directory delta at the same attempt cut is one
; issued link to the newly allocated inode.  The three stopped traces above
; also separate this stronger, physical conclusion's three premises.
(defun bsk0-issued-link-equalp (bs ks stage name frame)
  (equal (fn-bs-ops-for-dir
          (fn-bs-pending
           (car (nth 10 (fn-bs-run bs ks
                                        (fn-bs-record-program stage name frame)
                                        nil *bsk5-groups* *bsk5-capacity*))))
          :transactions)
         (list (list :set-entry :transactions name (fn-bs-next-ino bs)))))
(assert-event
 (and (bsk0-issued-link-equalp (bsk6-start) (bsk6-prepared)
                                     ".stage-k5-2" (fn-bs-txn-name 1)
                                     (bsk5-frame-2))
      (bsk0-issued-link-equalp (bsk6-start) (bsk6-retention-prepared)
                                     ".stage-k6-retention" (fn-bs-txn-name 1)
                                     (bsk6-retention-frame))))
(assert-event
 (let ((article (car (nth 10 (bsk5-record-2-run))))
       (retention (car (nth 10 (bsk6-retention-run)))))
   (and (fn-bs-pending-shape-okp article)
        (fn-bs-pending-shape-okp retention)
        (equal (fn-bs-record-of (fn-bs-durable article)
                                (fn-bs-next-ino (bsk6-start)))
               *bsk5-record-2*)
        (equal (fn-bs-record-of (fn-bs-durable retention)
                                (fn-bs-next-ino (bsk6-start)))
               (bsk6-retention-candidate)))))
(must-fail
 (assert-event
  (bsk0-issued-link-equalp (bsk6-occupied-final-start)
                            (bsk6-prepared) ".stage-k5-2"
                            (fn-bs-txn-name 1) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-issued-link-equalp (bsk6-start) (bsk6-prepared)
                            ".stage-k5-2" (fn-bs-txn-name 0)
                            (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-issued-link-equalp (bsk0-occupied-stage) (bsk6-prepared)
                            ".stage-k5-2" (fn-bs-txn-name 1)
                            (bsk5-frame-2))))

; K0 retained-prefix teeth. The positive cut follows an acknowledged old
; article and runs both an article and a non-article Store event.  Without
; the relation, reusing an old authority inode can overwrite its frame;
; without the typed name or O_EXCL freshness, execution stops before pair 10.
(defun bsk0-prefix-equalp (bs ks stage name frame)
  (equal (fn-bs-durable-records
          (car (nth 10 (fn-bs-run bs ks
                                       (fn-bs-record-program stage name frame)
                                       nil *bsk5-groups* *bsk5-capacity*))))
         (fn-bs-durable-records bs)))
(assert-event
 (and (equal (fn-bs-durable-records (bsk6-start))
             (list *bsk5-record*))
      (bsk0-prefix-equalp (bsk6-start) (bsk6-prepared)
                            ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))
      (bsk0-prefix-equalp (bsk6-start) (bsk6-retention-prepared)
                            ".stage-k6-retention" (fn-bs-txn-name 1)
                            (bsk6-retention-frame))))

(defun bsk0-alias-old-record ()
  (let ((bs (bsk6-start)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (fn-bs-pending bs)
                (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0)))))
(assert-event
 (let ((bs (bsk0-alias-old-record)))
   (and (not (fn-bs-store-relation bs (bsk6-prepared)))
        (fn-bs-record-inputp (bsk6-prepared) ".stage-k5-2"
                             (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2")))))
(must-fail
 (assert-event
  (bsk0-prefix-equalp (bsk0-alias-old-record) (bsk6-prepared)
                       ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-prefix-equalp (bsk6-start) (bsk6-prepared)
                       ".stage-k5-2" (fn-bs-txn-name 0) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-prefix-equalp (bsk0-occupied-stage) (bsk6-prepared)
                       ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))

; K0's fresh-inode authority clause is now derived through the full
; create/write/file-fence/link prefix, including write-all's empty branch.
; The second article and a retention Store event both reach pair 10 with
; the allocator's new inode present in the durable inode table.
(assert-event
 (let* ((article (car (nth 10 (bsk5-record-2-run))))
        (retention (car (nth 10 (bsk6-retention-run))))
        (new (fn-bs-next-ino (bsk6-start))))
   (and (consp (assoc-equal new (fn-bs-inodes article)))
        (consp (assoc-equal new (fn-bs-inodes retention))))))
