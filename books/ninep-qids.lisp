; Mount-scoped exported identities. IDs are protocol indices, never grants.
(in-package "ACL2")
(include-book "ninep-session")

(defstobj fn-ninep-qids
 (fn-9pq-keys :type (array t (1)) :initially nil :resizable t)
 (fn-9pq-used :type (integer 0 *) :initially 0)
 (fn-9pq-mount :type t :initially nil)
 :inline t)

; Only the real mount producer calls this after prepaid storage provision.
; Independent attaches on the same connection share this registry.
(defun fn-9pq-provision-owned (capacity fn-ninep-session fn-ninep-qids)
 (declare (xargs :stobjs (fn-ninep-session fn-ninep-qids) :guard t))
 (if (not (and (posp capacity) (<= capacity 18446744073709551616)
               (eq (fn-9ps-mount-phase fn-ninep-session) :held)
               (fn-9ps-mount-token fn-ninep-session)
               (not (fn-9pq-mount fn-ninep-qids))
               (equal (fn-9pq-used fn-ninep-qids) 0)))
     (mv :unavailable fn-ninep-qids)
   (let* ((fn-ninep-qids (resize-fn-9pq-keys capacity fn-ninep-qids))
          (fn-ninep-qids
           (update-fn-9pq-mount (fn-9ps-mount-token fn-ninep-session) fn-ninep-qids)))
    (mv :provisioned fn-ninep-qids))))

(defun fn-9pq-key-scalarp (key)
 (declare (xargs :guard t))
 (and (equal (fn-9p-metadata-at 0 key) :ninep-node)
      (member-eq (fn-9p-metadata-at 1 key)
        '(:root :groups :by-id :status :group :group-file :by-id-file))
      (natp (fn-9p-metadata-at 2 key)) (natp (fn-9p-metadata-at 4 key))))

(defun fn-9pq-directoryp (key)
 (declare (xargs :guard t))
 (member-eq (fn-9p-metadata-at 1 key) '(:root :groups :by-id :group)))

; Keys come from the immutable provider, never from a native path string.
; A group identity contains its borrowed reversed binary path. Validation
; and comparison consume one bit each tick, with no whole-path EQUAL.
(defun fn-9pq-begin (key)
 (declare (xargs :guard t))
 (if (not (fn-9pq-key-scalarp key)) nil
  (list :ninep-qid key 0 :validate (fn-9p-metadata-at 3 key) nil
        (fn-9p-metadata-at 2 key))))

(defun fn-9pq-step (cursor fn-ninep-session fn-ninep-qids)
 (declare (xargs :stobjs (fn-ninep-session fn-ninep-qids) :guard t))
 (let* ((key (fn-9p-metadata-at 1 cursor)) (index (fn-9p-metadata-at 2 cursor))
        (phase (fn-9p-metadata-at 3 cursor)) (a (fn-9p-metadata-at 4 cursor))
        (b (fn-9p-metadata-at 5 cursor)) (remaining (fn-9p-metadata-at 6 cursor)))
  (cond
   ((not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-qid)
              (fn-9pq-key-scalarp key) (natp index) (natp remaining)
              (eq (fn-9ps-mount-phase fn-ninep-session) :held)
              (fn-9pq-mount fn-ninep-qids)
              (equal (fn-9pq-mount fn-ninep-qids)
                     (fn-9ps-mount-token fn-ninep-session))))
    (mv :stale nil cursor fn-ninep-qids))
   ((eq phase :validate)
    (cond ((zp remaining)
           (if a (mv :invalid nil cursor fn-ninep-qids)
            (mv :yield nil (list :ninep-qid key 0 :lookup nil nil 0) fn-ninep-qids)))
          ((not (and (consp a) (member-equal (car a) '(0 1))))
           (mv :invalid nil cursor fn-ninep-qids))
          (t (mv :yield nil (list :ninep-qid key 0 :validate (cdr a) nil (1- remaining))
                 fn-ninep-qids))))
   ((eq phase :compare)
    (cond ((zp remaining)
           (if (or a b) (mv :invalid nil cursor fn-ninep-qids)
            (mv :qid (list (if (fn-9pq-directoryp key) 128 0) 0 index)
                cursor fn-ninep-qids)))
          ((not (and (consp a) (consp b) (equal (car a) (car b))))
           (mv :yield nil (list :ninep-qid key (1+ index) :lookup nil nil 0) fn-ninep-qids))
          (t (mv :yield nil (list :ninep-qid key index :compare (cdr a) (cdr b) (1- remaining))
                 fn-ninep-qids))))
   ((not (eq phase :lookup)) (mv :invalid nil cursor fn-ninep-qids))
   ((>= index (fn-9pq-used fn-ninep-qids))
    (if (not (and (equal index (fn-9pq-used fn-ninep-qids))
                  (< index (fn-9pq-keys-length fn-ninep-qids))
                  (< index 18446744073709551616)))
        (mv :namespace-capacity nil cursor fn-ninep-qids)
      (let* ((fn-ninep-qids (update-fn-9pq-keysi index key fn-ninep-qids))
             (fn-ninep-qids (update-fn-9pq-used (1+ index) fn-ninep-qids)))
       (mv :qid (list (if (fn-9pq-directoryp key) 128 0) 0 index)
           cursor fn-ninep-qids))))
   ((>= index (fn-9pq-keys-length fn-ninep-qids)) (mv :recovery-required nil cursor fn-ninep-qids))
   (t
    (let ((old (fn-9pq-keysi index fn-ninep-qids)))
     (if (not (and (equal (fn-9p-metadata-at 1 old) (fn-9p-metadata-at 1 key))
                   (equal (fn-9p-metadata-at 2 old) (fn-9p-metadata-at 2 key))
                   (equal (fn-9p-metadata-at 4 old) (fn-9p-metadata-at 4 key))))
         (mv :yield nil (list :ninep-qid key (1+ index) :lookup nil nil 0) fn-ninep-qids)
       (mv :yield nil (list :ninep-qid key index :compare
                           (fn-9p-metadata-at 3 key) (fn-9p-metadata-at 3 old)
                           (fn-9p-metadata-at 2 key)) fn-ninep-qids)))))))

; Definite generation return is produced by the real mount return, not by
; Tflush/Rclunk/disconnect or a caller Boolean. Drop the registry only then.
(defun fn-9pq-retire-step (index fn-ninep-session fn-ninep-qids)
 (declare (xargs :stobjs (fn-ninep-session fn-ninep-qids) :guard t))
 (cond ((not (and (natp index) (eq (fn-9ps-mount-phase fn-ninep-session) :returned)
                   (not (fn-9ps-mount-token fn-ninep-session))))
        (mv :await-return index fn-ninep-qids))
       ((< index (fn-9pq-keys-length fn-ninep-qids))
        (let ((fn-ninep-qids (update-fn-9pq-keysi index nil fn-ninep-qids)))
         (mv :yield (1+ index) fn-ninep-qids)))
       (t (let* ((fn-ninep-qids (update-fn-9pq-used 0 fn-ninep-qids))
                 (fn-ninep-qids (update-fn-9pq-mount nil fn-ninep-qids)))
            (mv :retired index fn-ninep-qids)))))

(defthm fn-9pq-stale-step-preserves-complete-registry
 (implies (equal (mv-nth 0 (fn-9pq-step cursor fn-ninep-session fn-ninep-qids)) :stale)
  (equal (mv-nth 3 (fn-9pq-step cursor fn-ninep-session fn-ninep-qids)) fn-ninep-qids)))

(defthm fn-9pq-return-required-before-registry-retirement
 (implies (not (equal (nth 13 fn-ninep-session) :returned))
  (equal (fn-9pq-retire-step index fn-ninep-session fn-ninep-qids)
         (list :await-return index fn-ninep-qids))))
