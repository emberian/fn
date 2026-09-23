; One FNBS immutable publication, using the byte-store syscalls underlying
; host/native/immutable-publish.lisp.  fn-jpub-step remains the sole publisher
; phase classifier; this book records its corresponding physical cut states.
(in-package "ACL2")
(include-book "bp-fnbs-codec")
(include-book "byte-store-invariants")
(include-book "journal-publish")

(set-verify-guards-eagerness 0)

(defun fn-bpnf-byte-after-create (bs stage)
  (declare (xargs :guard t))
  (mv-let (result bs1) (fn-bs-create bs :fnbs stage :ok)
    (declare (ignore result)) bs1))

(defun fn-bpnf-byte-after-write (bs stage frame)
  (declare (xargs :guard t))
  (mv-let (result bs1)
    (fn-bs-write bs (fn-bs-lookup bs :fnbs stage) 0 frame :ok)
    (declare (ignore result)) bs1))

(defun fn-bpnf-byte-after-file-barrier (bs stage)
  (declare (xargs :guard t))
  (mv-let (result bs1)
    (fn-bs-fsync-file bs (fn-bs-lookup bs :fnbs stage) :ok)
    (declare (ignore result)) bs1))

(defun fn-bpnf-byte-after-link (bs stage final outcome)
  (declare (xargs :guard t))
  (mv-let (result bs1) (fn-bs-link bs :fnbs stage :fnbs final outcome)
    (declare (ignore result)) bs1))

(defun fn-bpnf-byte-after-dir-barrier (bs)
  (declare (xargs :guard t))
  (mv-let (result bs1) (fn-bs-fsync-dir bs :fnbs :ok)
    (declare (ignore result)) bs1))

(defun fn-bpnf-byte-cuts (bs stage final frame)
  (declare (xargs :guard t))
  (let* ((created (fn-bpnf-byte-after-create bs stage))
         (written (fn-bpnf-byte-after-write created stage frame))
         (fenced (fn-bpnf-byte-after-file-barrier written stage))
         (linked (fn-bpnf-byte-after-link fenced stage final :ok))
         (durable (fn-bpnf-byte-after-dir-barrier linked)))
    (list bs created written fenced linked durable)))

(defun fn-bpnf-byte-cut (cuts phase)
  (declare (xargs :guard t))
  (case phase
    (:base (nth 0 cuts))
    (:stage (nth 1 cuts))
    (:write (nth 2 cuts))
    (:file-barrier (nth 3 cuts))
    (:link (nth 4 cuts))
    (:directory-barrier (nth 5 cuts))
    (otherwise nil)))

; Recovery reads a present final name and refuses malformed or mismatched
; content.  It never converts an occupied damaged name into absence.
(defun fn-bpnf-byte-slot (bs epoch operation-id)
  (declare (xargs :guard t))
  (let* ((name (fn-bpnf-stored-record-name epoch operation-id))
         (ino (fn-bs-durable-entry bs :fnbs name)))
    (if (not (natp ino))
        :absent
      (let ((record (fn-bpnf-stored-record-unframe
                     (fn-bs-durable-content bs ino))))
        (if (and record
                 (equal (nth 1 record) epoch)
                 (equal (nth 2 record) operation-id))
            (list :record record)
          (list :fault :occupied-damaged))))))

(defun fn-bpnf-byte-link-phase ()
  (declare (xargs :guard t))
  (fn-jpub-step
   (fn-jpub-step
    (fn-jpub-step
     (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok))
     '(:file-barrier-result :ok))
    '(:link-begin))
   '(:link-result :ok)))

(defun fn-bpnf-byte-publisher-phase (phase)
  (declare (xargs :guard t))
  (case phase
    (:base (fn-jpub-initial t))
    (:stage (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok)))
    (:write (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok)))
    (:file-barrier
     (fn-jpub-step
      (fn-jpub-step (fn-jpub-initial t) '(:stage-result :ok))
      '(:file-barrier-result :ok)))
    (:link (fn-bpnf-byte-link-phase))
    (:directory-barrier
     (fn-jpub-step (fn-bpnf-byte-link-phase)
                   '(:directory-barrier-result :ok)))
    (otherwise (fn-jpub-initial nil))))
