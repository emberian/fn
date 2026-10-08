;;;; Paged checkpoint I/O, driven by the certified page-store entries.
(in-package "ACL2")

(defun fnn-pck-write-words (fd offset sel base count mem octets)
  "Write ACL2's serialization of COUNT resident words at byte OFFSET.
OCTETS is this driver's private fn-octets-pg, never a served buffer."
  ;; Clearing the concrete buffer is the existing native buffer realization;
  ;; the words-to-octets codec itself is pgs-x-words-load-is-octets.
  (setf (svref octets 1) 0)
  (fnn-core 'pgs-x-words-load 0 count sel base mem octets)
  (fnn-posix () (sb-posix:lseek fd offset sb-posix:seek-set))
  (fnn-write-range fd (svref octets 0) 0 (svref octets 1)))

(defun fnn-pck-write-payload-frame (fd base source-start source-length octets)
  "Write the frame ACL2 appends to the source buffer, at committed BASE.
The caller must have accepted fn-pck-x-frame-preflight for the whole delta
before entering this writer. BASE is committed PLEN, including after a
crash that left bytes beyond PLEN. The caller owns the payload barrier."
  (let* ((start (svref octets 1))
         (answer (fnn-call 'fn-cpl-x-write-frame
                           source-start source-length base octets)))
    (fnn-posix () (sb-posix:lseek fd base sb-posix:seek-set))
    (fnn-write-range fd (svref octets 0) start (svref octets 1))
    ;; Ref and trailer are ACL2's outputs. No host frame/digest calculation.
    (values (first answer) (second answer))))

(defun fnn-pck-load-resident-image (file rec mem octets)
  "Fill and check REC's resident image; return ACL2's first refusal or NIL.
FILE is registered with the page-fill realizer. MEM and OCTETS are private
to this open/publication driver. No payload bytes or history image are read."
  ;; The existing guarded disk helper sizes the image, loads the directory
  ;; and all table pages through fn-pgs-fill-frame, and checks their digests
  ;; through pgs-x-open-dir and pgs-x-open-table-page, in that order.
  (let ((verdict (first (fnn-call 'fn-hrs-open-pgs file rec mem octets))))
    (when verdict (return-from fnn-pck-load-resident-image verdict)))
  (let* ((npages (fnn-core 'pgs-rec-npages rec))
         (txid (fnn-core 'pgs-rec-txid rec))
         (pages (fnn-core 'pgs-x-open-pages 0 npages txid :eager nil mem)))
    (dolist (page pages)
      (destructuring-bind (logical physical) page
        ;; Word address translation only: ACL2 selected LOGICAL/PHYSICAL.
        (fnn-core 'fn-pgs-fill-frame file physical 0 (* 2048 logical) mem)
        (let ((verdict (first (fnn-call 'pgs-x-open-page logical txid :eager mem octets))))
          (when verdict (return-from fnn-pck-load-resident-image verdict)))))
    nil))

(defun fnn-pck-open-resident-capture (file rec payload-file mem page-octets arena octets)
  "Read the selected record's pages, then decode through the resident entry.
Return the page-store refusal separately from the checkpoint entry's MV
list. The selection/retained-log decision belongs to the caller's ACL2 entry."
  (let ((verdict (fnn-pck-load-resident-image file rec mem page-octets)))
    (if verdict
        (values verdict nil)
      (values nil (fnn-call 'fn-pck-x-open (fnn-core 'pgs-rec-npages rec)
                            mem payload-file arena octets)))))

(defun fnn-pck-commit-pages (pages-fd payload-fd lpages n txid alloc adopted-slot mem octets)
  "Execute a page-store commit and return ACL2's plan or refusal.
ADOPTED-SLOT is the open's result; pgs-x-commit-slot chooses the write slot.
TXID is ACL2's next transaction output. Payload frames are already written at committed PLEN.
A post-plan I/O failure requires recovery because MEM contains new tables."
  (let* ((slot (fnn-core 'pgs-x-commit-slot adopted-slot))
         (plan (first (fnn-call 'pgs-x-commit lpages n txid alloc slot mem octets))))
    (unless (eq (first plan) :plan)
      (return-from fnn-pck-commit-pages plan))
    (handler-case
        (progn
          ;; These address lists are the commit's outputs. Multiplication
          ;; below translates their page/word units into I/O byte offsets.
          (loop for logical in lpages for physical in (third plan) do
            (fnn-pck-write-words pages-fd (* 16384 physical) 0 (* 2048 logical) 2048 mem octets))
          (loop for table in (fourth plan) for physical in (fifth plan) do
            (fnn-pck-write-words pages-fd (* 16384 physical) 2 (* 2048 table) 2048 mem octets))
          (loop for j below (seventh plan) do
            (fnn-pck-write-words pages-fd (* 16384 (+ (sixth plan) j))
                                  1 (+ 1024 (* 2048 j)) 2048 mem octets))
          ;; A5: the payload barrier PRECEDES the record write, not merely
          ;; the page-store barrier. A visible new root can resolve payloads.
          (fnn-durable-barrier payload-fd)
          (fnn-pck-write-words pages-fd (* 8 slot) 1 slot 20 mem octets)
          (fnn-durable-barrier pages-fd)
          ;; No compaction or clean marking is permitted before this barrier.
          (fnn-core 'pgs-x-commit-durable lpages mem)
          plan)
      (fnn-os-error (e)
        (fnn-indeterminate "paged checkpoint commit requires recovery: ~a" e)))))
