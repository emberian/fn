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

; The old article's inode survives the actual served cut.  The authority
; lists gain exactly the new target, and both are known and file-fenced.
(assert-event
 (let* ((bs (bsk6-start))
        (article (car (nth 10 (bsk5-record-2-run))))
        (retention (car (nth 10 (bsk6-retention-run))))
        (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0))))
   (and (fn-bs-store-relation bs (bsk6-prepared))
        (consp (assoc-equal old (fn-bs-inodes bs)))
        (equal (assoc-equal old (fn-bs-inodes article))
               (assoc-equal old (fn-bs-inodes bs)))
        (equal (fn-bs-authority-inode-list article)
               (append (fn-bs-authority-inode-list bs)
                       (list (fn-bs-next-ino bs))))
        (fn-bs-authority-knownp article)
        (fn-bs-authority-fencedp article)
        (fn-bs-authority-knownp retention)
        (fn-bs-authority-fencedp retention))))

; A state with a valid pending write to the old article is not a related
; input.  The P-RECORD file fence drains only the new inode, so the old
; authority target remains unfenced at the attempted cut.
(defun bsk0-unfenced-old-authority ()
  (let* ((bs (bsk6-start))
         (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :write old 0 '(65))))
                (fn-bs-next-ino bs))))
(assert-event
 (let ((bs (bsk0-unfenced-old-authority)))
   (and (fn-bs-statep bs)
        (not (fn-bs-store-relation bs (bsk6-prepared)))
        (fn-bs-record-inputp (bsk6-prepared) ".stage-k5-2"
                             (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2")))))
(must-fail
 (assert-event
  (let* ((bs (bsk0-unfenced-old-authority))
         (cut (car (nth 10 (fn-bs-run bs (bsk6-prepared)
                                       (fn-bs-record-program
                                        ".stage-k5-2" (fn-bs-txn-name 1)
                                        (bsk5-frame-2))
                                       nil *bsk5-groups* *bsk5-capacity*)))))
    (fn-bs-authority-fencedp cut))))

; The byte-state grammar permits a dangling durable directory entry.  A
; fresh P-RECORD cannot repair the missing old inode; known-authority is a
; genuine input-relation obligation.
(defun bsk0-missing-old-authority ()
  (let* ((bs (bsk6-start))
         (old (fn-bs-durable-entry bs :transactions (fn-bs-txn-name 0))))
    (fn-bs-make (fn-bs-unit bs)
                (remove-assoc-equal old (fn-bs-inodes bs))
                (fn-bs-dirs bs) (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event
 (let ((bs (bsk0-missing-old-authority)))
   (and (fn-bs-statep bs)
        (not (fn-bs-store-relation bs (bsk6-prepared)))
        (fn-bs-record-inputp (bsk6-prepared) ".stage-k5-2"
                             (fn-bs-txn-name 1) (bsk5-frame-2))
        (not (fn-bs-lookup bs :staging ".stage-k5-2")))))
(must-fail
 (assert-event
  (let* ((bs (bsk0-missing-old-authority))
         (cut (car (nth 10 (fn-bs-run bs (bsk6-prepared)
                                       (fn-bs-record-program
                                        ".stage-k5-2" (fn-bs-txn-name 1)
                                        (bsk5-frame-2))
                                       nil *bsk5-groups* *bsk5-capacity*)))))
    (fn-bs-authority-knownp cut))))

; The complete K0 relation is regained by the actual interpreter pair,
; after the old durable article and for both article/retention Store events.
(defun bsk0-attempted-cut-relatedp (bs ks stage name frame)
  (let ((cut (nth 10 (fn-bs-run bs ks
                                (fn-bs-record-program stage name frame)
                                nil *bsk5-groups* *bsk5-capacity*))))
    (fn-bs-store-relation (car cut) (cdr cut))))
(assert-event
 (and (bsk0-attempted-cut-relatedp
       (bsk6-start) (bsk6-prepared) ".stage-k5-2"
       (fn-bs-txn-name 1) (bsk5-frame-2))
      (bsk0-attempted-cut-relatedp
       (bsk6-start) (bsk6-retention-prepared)
       ".stage-k6-retention" (fn-bs-txn-name 1)
       (bsk6-retention-frame))))
(must-fail
 (assert-event
  (bsk0-attempted-cut-relatedp
   (bsk6-occupied-final-start) (bsk6-prepared)
   ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-attempted-cut-relatedp
   (bsk6-start) (bsk6-prepared)
   ".stage-k5-2" (fn-bs-txn-name 0) (bsk5-frame-2))))
(must-fail
 (assert-event
  (bsk0-attempted-cut-relatedp
   (bsk0-occupied-stage) (bsk6-prepared)
   ".stage-k5-2" (fn-bs-txn-name 1) (bsk5-frame-2))))

; Native fnn-owner-publish-prepared passes ACL2's encoded candidate to
; fnn-publish.  fnn-frame concatenates the ACL2 protected prefix and ACL2
; trailer; fnn-transaction-name delegates the sequence to ACL2.  This is
; the typed P-RECORD input for the second served article, not an arbitrary
; Python or host-side decoder agreement assumption.
(defun bsk0-article-host-frame (record)
  (let ((octets (fn-store-event-encode record)))
    (append (fn-frame-store-protected octets)
            (fn-frame-trailer (fn-frame-store-protected octets)))))
(defun bsk0-article-host-inputp (ks record stage)
  (fn-bs-record-inputp
   ks stage (fn-bs-txn-name (fn-store-event-sequence record))
   (bsk0-article-host-frame record)))
(assert-event
 (and (fn-record-p *bsk5-record-2*)
      (equal (fn-sf-phase (bsk6-prepared)) :record-staged)
      (equal (fn-sf-record-candidate (bsk6-prepared)) *bsk5-record-2*)
      (bsk0-article-host-inputp (bsk6-prepared) *bsk5-record-2*
                               ".stage-k5-2")
      (bsk0-attempted-cut-relatedp
       (bsk6-start) (bsk6-prepared) ".stage-k5-2"
       (fn-bs-txn-name (fn-store-event-sequence *bsk5-record-2*))
       (bsk0-article-host-frame *bsk5-record-2*))))

; Each article call-argument premise has a direct negative witness.
(must-fail
 (assert-event
  (bsk0-article-host-inputp
   (fn-sf-make :record-staged 2 nil nil :junk nil nil nil)
   :junk ".stage-k5-2")))
(must-fail
 (assert-event
  (bsk0-article-host-inputp
   (fn-sf-make :ready (fn-sf-frontier (bsk6-prepared)) nil
               (fn-sf-records (bsk6-prepared)) *bsk5-record-2* nil nil nil)
   *bsk5-record-2* ".stage-k5-2")))
(must-fail
 (assert-event
  (bsk0-article-host-inputp
   (fn-sf-make :record-staged (fn-sf-frontier (bsk6-prepared)) nil
               (fn-sf-records (bsk6-prepared)) *bsk5-record* nil nil nil)
   *bsk5-record-2* ".stage-k5-2")))
(must-fail
 (assert-event
  (bsk0-article-host-inputp (bsk6-prepared) *bsk5-record-2* nil)))

; ACL2 node preparation is the served article caller's logical step. It
; does not mutate the byte store, and the relation survives both the file
; kernel prepare and the actual fn-sn-prepare that calls it. The first
; article witness has a nonempty framed candidate and a durable reservation.
(defun bsk0-node-reserved ()
  (let ((s (fn-sn-initial *bsk5-groups* *bsk5-capacity*)))
    (fn-sn-io
     (fn-sn-io
      (fn-sn-io
       (fn-sn-io s :start-frontier nil)
       :frontier-file :ok)
      :frontier-replace :ok)
     :frontier-directory :ok)))
(assert-event
 (let* ((pair (car (last (bsk5-frontier-run))))
        (bs (car pair))
        (ks (cdr pair))
        (node (bsk0-node-reserved))
        (prepared (fn-sn-prepare node *bsk5-record*)))
   (and (fn-bs-store-relation bs ks)
        (equal ks (fn-sn-files node))
        (equal (fn-sf-phase ks) :reserved)
        (equal (fn-sf-phase (fn-sf-prepare-record
                            ks *bsk5-record* *bsk5-groups* *bsk5-capacity*))
               :record-staged)
        (equal (fn-sf-phase (fn-sn-files prepared)) :record-staged)
        (fn-bs-store-relation
         bs (fn-sf-prepare-record
             ks *bsk5-record* *bsk5-groups* *bsk5-capacity*))
        (fn-bs-store-relation bs (fn-sn-files prepared)))))

; Without the physical relation, a valid pending write to an old article
; remains unfenced across preparation; no ACL2 callback can repair bytes.
(must-fail
 (assert-event
  (fn-bs-store-relation
   (bsk0-unfenced-old-authority)
   (fn-sf-prepare-record (cdr (bsk5-frontier-2)) *bsk5-record-2*
                         *bsk5-groups* *bsk5-capacity*))))

; Compose the actual fn-sn-prepare article call with ACL2's host-facing
; frame/name values and the actual P-RECORD attempted cut.
(defun bsk0-node-article-attempted-relatedp (bs s record stage)
  (let* ((ks (fn-sn-files (fn-sn-prepare s record)))
         (name (fn-bs-txn-name (fn-store-event-sequence record)))
         (frame (bsk0-article-host-frame record))
         (cut (nth 10 (fn-bs-run bs ks
                                 (fn-bs-record-program stage name frame)
                                 nil *bsk5-groups* *bsk5-capacity*))))
    (fn-bs-store-relation (car cut) (cdr cut))))
(assert-event
 (let* ((pair (car (last (bsk5-frontier-run))))
        (bs (car pair))
        (s (bsk0-node-reserved)))
   (and (fn-bs-store-relation bs (fn-sn-files s))
        (equal (fn-sf-phase (fn-sn-files s)) :reserved)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-prepare s *bsk5-record*)))
               :record-staged)
        (not (fn-bs-lookup bs :staging ".stage-k5"))
        (bsk0-node-article-attempted-relatedp
         bs s *bsk5-record* ".stage-k5"))))

; Invalid byte authority survives node preparation, so the served cut
; cannot gain a physical relation from the logical node alone.
(defun bsk0-unfenced-config-at-reservation ()
  (let* ((bs (car (car (last (bsk5-frontier-run)))))
         (config (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :write config 0 '(65))))
                (fn-bs-next-ino bs))))
(assert-event
 (and (fn-bs-statep (bsk0-unfenced-config-at-reservation))
      (not (fn-bs-store-relation (bsk0-unfenced-config-at-reservation)
                                 (fn-sn-files (bsk0-node-reserved))))))
(must-fail
 (assert-event
  (bsk0-node-article-attempted-relatedp
   (bsk0-unfenced-config-at-reservation)
   (bsk0-node-reserved) *bsk5-record* ".stage-k5")))

; The successful prepare phase matters: an invalid record leaves the
; reservation unprepared, so the P-RECORD attempted cut is unreachable.
(must-fail
 (assert-event
  (bsk0-node-article-attempted-relatedp
   (car (car (last (bsk5-frontier-run))))
   (bsk0-node-reserved) :junk ".stage-k5")))

; Re-entering preparation from an already staged first article is a no-op.
; Supplying a different second article to the publication program then
; targets the wrong transaction name, despite the source being related.
(assert-event
 (let* ((bs (car (car (last (bsk5-frontier-run)))))
        (staged (fn-sn-prepare (bsk0-node-reserved) *bsk5-record*)))
   (and (fn-bs-store-relation bs (fn-sn-files staged))
        (equal (fn-sf-phase (fn-sn-files staged)) :record-staged)
        (equal (fn-sf-phase
                (fn-sn-files (fn-sn-prepare staged *bsk5-record-2*)))
               :record-staged))))
(must-fail
 (assert-event
  (bsk0-node-article-attempted-relatedp
   (car (car (last (bsk5-frontier-run))))
   (fn-sn-prepare (bsk0-node-reserved) *bsk5-record*)
   *bsk5-record-2* ".stage-k5")))

; An occupied staging key stops O_EXCL before the record-file callback.
(must-fail
 (assert-event
  (let* ((bs (car (car (last (bsk5-frontier-run)))))
         (occupied (mv-nth 1 (fn-bs-create bs :staging ".stage-k5" :ok))))
    (bsk0-node-article-attempted-relatedp
     occupied (bsk0-node-reserved) *bsk5-record* ".stage-k5"))))

; The second allocation begins after an acknowledged first article.  These
; values are generated by the same ACL2 codec entry points called by the
; native allocator, and the byte run retains the first article throughout.
(defun bsk0-second-frontier-host-frame () (fn-bs-frontier-encode 2))
(defun bsk0-second-frontier-file-pair ()
  (let ((pair (bsk5-finished)))
    (nth 5 (fn-bs-run (car pair) (cdr pair)
                      (fn-bs-frontier-program ".allocation-k0-2"
                                              (bsk0-second-frontier-host-frame))
                      nil *bsk5-groups* *bsk5-capacity*))))
(assert-event
 (let* ((entry (bsk5-finished))
        (bs (car entry)) (ks (cdr entry))
        (file (car (bsk0-second-frontier-file-pair))))
   (and (fn-bs-store-relation bs ks)
        (equal (fn-sf-phase ks) :ready)
        (equal (fn-bs-frontier-next (fn-sf-frontier ks)) 2)
        (equal (bsk0-second-frontier-host-frame)
               (fn-bs-frontier-encode-impl 2))
        (fn-bs-frontier-inputp ks ".allocation-k0-2"
                               (bsk0-second-frontier-host-frame))
        (equal (fn-bs-durable-content file (fn-bs-next-ino bs))
               (bsk0-second-frontier-host-frame))
        (equal (fn-bs-lookup file :staging ".allocation-k0-2")
               (fn-bs-next-ino bs))
        (fn-bs-statep file)
        (equal (fn-bs-dirs file) (fn-bs-dirs bs))
        (equal (fn-bs-durable-frontier file)
               (fn-bs-durable-frontier bs))
        (equal (fn-bs-durable-entry file :root *fn-bs-scan-config-name*)
               (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
        (equal (fn-bs-durable-content
                file (fn-bs-durable-entry file :root *fn-bs-scan-config-name*))
               (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
        (equal (fn-bs-durable-content
                file (fn-bs-durable-entry bs :transactions
                                           (fn-bs-txn-name 0)))
               (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :transactions
                                         (fn-bs-txn-name 0))))
        (equal (fn-bs-durable-records file) (list *bsk5-record*))
        (equal (fn-bs-durable-records file)
               (fn-bs-durable-records bs))
        (equal (car (nth 6 (fn-bs-run
                             bs ks
                             (fn-bs-frontier-program
                              ".allocation-k0-2"
                              (bsk0-second-frontier-host-frame))
                             nil *bsk5-groups* *bsk5-capacity*)))
               file)
        (fn-bs-store-relation
         (car (nth 6 (fn-bs-run
                      bs ks
                      (fn-bs-frontier-program
                       ".allocation-k0-2"
                       (bsk0-second-frontier-host-frame))
                      nil *bsk5-groups* *bsk5-capacity*)))
         (cdr (nth 6 (fn-bs-run
                      bs ks
                      (fn-bs-frontier-program
                       ".allocation-k0-2"
                       (bsk0-second-frontier-host-frame))
                      nil *bsk5-groups* *bsk5-capacity*))))
        (equal (fn-sf-phase (cdr (nth 6 (fn-bs-run
                                             bs ks
                                             (fn-bs-frontier-program
                                              ".allocation-k0-2"
                                              (bsk0-second-frontier-host-frame))
                                             nil *bsk5-groups* *bsk5-capacity*))))
               :frontier-data-durable))))

; Existing staging occupancy stops at O_EXCL, before the exact-frame cut.
(must-fail
 (assert-event
  (let* ((entry (bsk5-finished)) (bs (car entry))
         (occupied (mv-nth 1 (fn-bs-create bs :staging
                                        ".allocation-k0-2" :ok)))
         (file (car (nth 5 (fn-bs-run
                            occupied (cdr entry)
                            (fn-bs-frontier-program
                             ".allocation-k0-2"
                             (bsk0-second-frontier-host-frame))
                            nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content file (fn-bs-next-ino occupied))
           (bsk0-second-frontier-host-frame)))))

; Wrong codec bytes and an exhausted successor cannot enter the host input
; contract, even though a raw byte run may accept a caller-supplied frame.
(must-fail
 (assert-event
  (fn-bs-frontier-inputp (cdr (bsk5-finished)) ".allocation-k0-2"
                         (fn-bs-frontier-encode-impl 1))))
(must-fail
 (assert-event
  (fn-bs-frontier-next *fn-cbor-max-uint*)))

; The old-content theorem excludes the newly allocated inode.  That inode
; changes from absent/empty to the exact host frame at file fsync.
(must-fail
 (assert-event
  (let* ((entry (bsk5-finished)) (bs (car entry))
         (file (car (bsk0-second-frontier-file-pair))))
    (equal (fn-bs-durable-content file (fn-bs-next-ino bs))
           (fn-bs-durable-content bs (fn-bs-next-ino bs))))))

; fn-bs-statep alone permits a transaction entry to name the unallocated
; next inode.  Authority-known in the relation excludes this alias.  Without
; it, allocation changes that old transaction path's raw bytes.
(defun bsk0-dangling-old-transaction ()
  (let ((bs (car (bsk5-finished))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (fn-bs-put-assoc
                 :transactions
                 (list (cons (fn-bs-txn-name 0) (fn-bs-next-ino bs)))
                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(assert-event
 (and (fn-bs-statep (bsk0-dangling-old-transaction))
      (not (fn-bs-store-relation
            (bsk0-dangling-old-transaction) (cdr (bsk5-finished))))))
(must-fail
 (assert-event
  (let* ((bs (bsk0-dangling-old-transaction))
         (name (fn-bs-txn-name 0))
         (old (fn-bs-durable-entry bs :transactions name))
         (file (car (nth 5 (fn-bs-run
                            bs (cdr (bsk5-finished))
                            (fn-bs-frontier-program
                             ".allocation-k0-2"
                             (bsk0-second-frontier-host-frame))
                            nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content file old)
           (fn-bs-durable-content bs old)))))

(must-fail
 (assert-event
  (let* ((entry (bsk5-finished))
         (occupied (mv-nth 1 (fn-bs-create (car entry) :staging
                                        ".allocation-k0-2" :ok)))
         (cut (nth 6 (fn-bs-run
                       occupied (cdr entry)
                       (fn-bs-frontier-program
                        ".allocation-k0-2"
                        (bsk0-second-frontier-host-frame))
                       nil *bsk5-groups* *bsk5-capacity*))))
    (fn-bs-store-relation (car cut) (cdr cut)))))

(must-fail
 (assert-event
  (let* ((entry (bsk5-finished))
         (file (car (nth 5 (fn-bs-run
                            (car entry) (cdr entry)
                            (fn-bs-frontier-program ".allocation-k0-empty" 65)
                            nil *bsk5-groups* *bsk5-capacity*)))))
    (equal (fn-bs-durable-content file (fn-bs-next-ino (car entry))) 65))))
