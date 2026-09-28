;;; The `checkpoint' verbs of the record log: `checkpoint clone'
;;; and `clone-resume', and `store compact' / `store reclaim' (the state
;;; checkpoint's rotation and the covered segments' drop).
;;;
;;; The generation checkpoints (`checkpoint publish [select]', `checkpoint
;;; select', `checkpoint status', and the open's diagnostic restore of a
;;; selected generation) are retired (lane matrix-reds, 2026-09-27).  Their
;;; frame is the node of books/checkpoint.lisp fn-checkpoint-capture, and since
;;; the records flip that node holds arena handles its frame does not resolve,
;;; so every capture of a store holding an article was refused ("ACL2 refused
;;; checkpoint capture").  The record log's checkpoint is the state checkpoint
;;; (fn-bs-scp-program; the arena run then the tables, lane checkpoint-arena):
;;; the open reads it (fn-sn-recover-from-checkpoint-equals-full-recover,
;;; PRF-083; KEYSTONE fn-scka-load-of-written-file), the owner publishes it
;;; (tests.test_native_checkpoint_auto), `store checkpoint' writes it
;;; (tests.test_native_state_checkpoint, every cut), and `store compact'
;;; rotates at it and drops the covered segments
;;; (tests.test_native_log_compaction).  The retired verbs answer a refusal
;;; naming it.
(in-package "ACL2")

(defun fnn-checkpoint-require-mutation-ready (store)
  "Checkpoint mutation requires the common writer gate and an unfenced Store."
  (fnn-require-writer store)
  (when (fnn-store-fenced store)
    (fnn-indeterminate "store is fenced pending recovery")))

;; The four stops are reached only from fnn-checkpoint-command-clone and
;; fnn-clone-activate, which the `checkpoint' verb calls; the owner that
;; fnn-clone-activate installs never calls them.
;; thread-confined: the `checkpoint' verb's command thread
(defvar *fnn-checkpoint-test-stop-counts* (make-hash-table :test #'equal))

(defun fnn-checkpoint-test-stop-after ()
  "Return the bounded matching-hook occurrence selected by the test process."
  (let ((raw (fnn-developer-selector "FN_CHECKPOINT_TEST_STOP_AFTER")))
    (if raw
        (handler-case
            (let ((value (parse-integer raw :junk-allowed nil)))
              (if (and (> value 0) (<= value 4096)) value
                (fnn-fault "invalid checkpoint test stop occurrence")))
          (error () (fnn-fault "invalid checkpoint test stop occurrence")))
      1)))

(defun fnn-checkpoint-test-stop (point)
  "Stop at a selected occurrence of a named test-only process-death boundary."
  (when (string= (or (fnn-developer-selector "FN_CHECKPOINT_TEST_STOP") "") point)
    (let ((count (1+ (gethash point *fnn-checkpoint-test-stop-counts* 0))))
      (setf (gethash point *fnn-checkpoint-test-stop-counts*) count)
      (when (= count (fnn-checkpoint-test-stop-after))
        (sb-posix:kill (sb-posix:getpid) sb-unix:sigstop)))))

(defun fnn-command-compact (root)
  "`store compact'.  On the record log compaction is the
checkpoint's rotation and the drop of the segments it covers (design
2026-09-27 storage-log section 6; T8 books/store-log-stream.lisp
fn-lgw-segment-drop-preserves-the-open):
a state checkpoint is published at the history's end with the log rotated,
then the covered segments are unlinked.  The open answers the history's
count and keeps no records (PKT-823); the checkpoint is written from the
state (D27)."
  (multiple-value-bind (store count) (fnn-open-live-store root t)
    (unwind-protect
         (progn
           ;; Every store an image opens is on the record log (batch AW: a format-8
           ;; profile is refused at the open); the pack chain's verb is the
           ;; per-file layout's, deleted with it (design section 9 row 5).
           (unless (fnn-store-logp store)
             (fnn-fault "a store that is not on the record log opened"))
           (fnn-out "compacted steps=checkpoint,drop records=~d ~a"
                    count (fnn-state-checkpoint-publish-steps store count))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(setq *fnn-compact-callback* #'fnn-command-compact)

;;; `operator CONFIG store reclaim [--dry-run]' (D13, STO-017): content
;;; reclamation over the record log (fnn-log-reclaim-steps below: the
;;; tombstones' checkpoint and the drop of the segments it covers).

(defun fnn-reclaim-counts-line (counts)
  (unless (and (listp counts) (= (length counts) 5)
               (every (lambda (n) (and (integerp n) (>= n 0))) counts))
    (fnn-fault "ACL2 returned malformed reclaim counts"))
  (destructuring-bind (reclaimable octets reclaimed freed held) counts
    (format nil "reclaimable=~d reclaimable-octets=~d held=~d reclaimed=~d freed-octets=~d"
            reclaimable octets held reclaimed freed)))

(defun fnn-reclaim-record-instant (store clock)
  "The reclaim's instant, recorded before anything is rewritten
(books/reclaim-instant.lisp, PKT-857): ACL2 builds the configuration record
carrying CLOCK's stamp as the `retention-reclaim-at' row
(fn-store-reclaim-instant-record) and the administrative path authorizes,
publishes and reads it back (fnn-admin-publish-record).  A refusal or a
record that does not read back refuses the reclaim before any rewrite.
Answers the report line's field."
  (let* ((stamp (fnn-admin-clock-plan))
         (status (fnn-core-state 'fn-store-reclaim-instant-record clock stamp)))
    (unless (eq status :ok)
      (fnn-refuse "reclaim refused: its instant's configuration record: ~(~a~)"
                  (fnn-core-state 'fn-store-cfg-last-reason)))
    (let ((record (fnn-core-state 'fn-store-cfg-last-octets)))
      (unless (fnn-octet-list-p record)
        (fnn-fault "ACL2 accepted the reclaim instant's record without octets"))
      (multiple-value-bind (generation name verification) (fnn-admin-publish-record store record)
        (unless (eq verification :verified)
          (fnn-refuse "reclaim refused: its instant's configuration record ~a did not read back: ~(~a~)"
                      name verification))
        (format nil "instant-record=~a generation=~d" name generation)))))

(defun fnn-log-reclaim-steps (store mode)
  "`store reclaim' on a store (books/store-log-reclaim.lisp): the
history streamed one record at a time into ACL2's fold (fn-rcls-step under the
store's context, compact-arena's books/store-reclaim-stream.lisp) with each
record's rewrite (fn-rclp-event) kept as an octet vector, then ACL2's decision
over the fold (fn-lgr-decide-stream; KEYSTONE fn-lgr-decide-stream-is-lgr-
decide: the whole-history decision, whose rewritten history is those
rewrites).  On :reclaim the instant is recorded first (fnn-reclaim-record-
instant: the configuration row the context's NOW came from, PKT-857), then the
rewritten history is replayed into the store node (the chunked replay every
open runs, fnn-recover-log-replay) and its state checkpoint published with the
log rotated, then the segments it covers are dropped
(fnn-state-checkpoint-publish-steps: T8): the released payloads' octets leave
the disk with them.  MODE :reclaim, :dry-run (nothing written, nothing
recorded) or :recorded (`--recorded': the context and the decision from the
configuration's recorded instant, fn-store-reclaim-context-recorded and
fn-store-log-reclaim-decide-recorded, KEYSTONE fn-rci-recorded-decision-is-
the-decision; nothing new is recorded: this completes a reclaim whose record
was published before a process death, or reproduces one on a copy).  Returns
the report line."
  (let* ((dry (eq mode :dry-run))
         (recorded (eq mode :recorded))
         (clock (and (not recorded) (fnn-store-prepare-observation)))
         (ctx (if recorded
                  (fnn-core-state 'fn-store-reclaim-context-recorded)
                (fnn-core-state 'fn-store-reclaim-context clock)))
         ;; The classes before anything is rewritten (books/expiry.lisp
         ;; fn-xpy-ctx-classes): (reclaimable expired held reclaimed signed
         ;; kept); the report names the expiry policy's share (Q14).
         (classes (fnn-core-state 'fn-store-reclaim-ctx-classes ctx))
         (expired (if (and (listp classes) (= (length classes) 6)
                           (every (lambda (n) (and (integerp n) (>= n 0))) classes))
                      (second classes)
                    (fnn-fault "ACL2 returned malformed reclaim classes")))
         (acc (fnn-core 'fn-store-reclaim-init))
         (count 0)
         (rewritten nil))
    (fnn-log-history-each
     store
     (lambda (record)
       (let ((octets (fnn-octet-list record)))
         (incf count)
         (setq acc (fnn-core 'fn-store-reclaim-step acc octets ctx))
         (unless dry
           (let ((event (fnn-core 'fn-store-log-reclaim-event octets ctx)))
             (unless (fnn-octet-list-p event)
               (fnn-fault "ACL2 returned a malformed rewritten record"))
             (push (fnn-octets event) rewritten))))))
    (let ((decision (if recorded
                        (fnn-core-state 'fn-store-log-reclaim-decide-recorded
                                        (fnn-store-config store) acc nil)
                      (fnn-core-state 'fn-store-log-reclaim-decide-stream
                                      (fnn-store-config store) clock acc (if dry t nil)))))
      (unless (and (consp decision) (member (first decision) '(:refused :none :dry-run :reclaim)))
        (fnn-fault "ACL2 returned no reclaim decision"))
      (case (first decision)
        (:refused (fnn-refuse "reclaim refused: ~(~a~)" (second decision)))
        (:none (format nil "reclaimed=0 expired=~d ~a" expired
                       (fnn-reclaim-counts-line (second decision))))
        (:dry-run
         (destructuring-bind (msgids freed counts) (rest decision)
           (format nil "dry-run would-reclaim=~d would-expire=~d freed-octets=~d ~a~{~%would-reclaim ~a~}"
                   (length msgids) expired freed (fnn-reclaim-counts-line counts)
                   (mapcar (lambda (m) (if (stringp m) m (fnn-fault "malformed msgid")))
                           msgids))))
        (:reclaim
         (destructuring-bind (msgids freed counts) (rest decision)
           (declare (ignore counts))
           (let ((history (nreverse rewritten)))
             (unless (= (length history) count)
               (fnn-fault "the rewritten history is not the history's length"))
             (setq rewritten nil)
             (fnn-checkpoint-require-mutation-ready store)
             (let ((instant (if recorded
                                "instant=recorded"
                              (fnn-reclaim-record-instant store clock))))
               ;; The store node becomes the rewritten history's (the chunked
               ;; replay every open runs), and the checkpoint the open will
               ;; read is its capture.
               (fnn-core-state 'fn-store-sco-clear)
               (fnn-bridge-reset)
               (fnn-recover-log-replay store history (fnn-config-records store))
               (setf (fnn-store-open-mode store) (list :full-replay :reclaim))
               (format nil "reclaimed=~d expired=~d freed-octets=~d ~a ~a~{~%reclaimed ~a~}"
                       (length msgids) expired freed
                       (fnn-state-checkpoint-publish-steps store count)
                       instant msgids)))))
        (otherwise (fnn-fault "ACL2 returned an unknown reclaim decision"))))))

(defun fnn-command-reclaim (root mode)
  ;; MODE :reclaim, :dry-run or :recorded (host/native/operator.lisp's
  ;; actions).  The open answers the history's count; the reclaim streams the
  ;; history after it, as the open read it (fnn-log-history-each).
  ;; The developer image's FN_NATIVE_STATE_CHECKPOINT_FAULT cuts the
  ;; reclaim's checkpoint as it cuts `store checkpoint's (lane expiry: before,
  ;; the reclaim opened without it, so no cut of a reclaim was ever taken).
  (multiple-value-bind (store count)
      (fnn-open-live-store root (not (eq mode :dry-run))
                           (and (not (eq mode :dry-run)) (fnn-state-checkpoint-test-fault)))
    (declare (ignore count))
    (unwind-protect
         (progn (unless (fnn-store-logp store)
                  (fnn-fault "a store that is not on the record log opened"))
                (fnn-out "~a" (fnn-log-reclaim-steps store mode))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(setq *fnn-reclaim-callback* #'fnn-command-reclaim)

;;; Cold copy activation.  The copied directory is fenced before publication;
;;; every ordinary Store open checks that marker in fnn-acquire.  The marker is
;;; the canonical v1 E2 rollover event itself, not a second projection format.
(defvar *fnn-clone-copy-count* 0)
(defvar *fnn-clone-copy-bytes* 0)

(defun fnn-clone-path-bound ()
  (let ((bound (fnn-core 'fn-store-checkpoint-clone-path-bound)))
    (unless (and (integerp bound) (> bound 0))
      (fnn-fault "ACL2 returned an invalid clone path bound"))
    bound))

(defun fnn-clone-checked-path (path bound &optional inputp)
  "Bound an argument or derived canonical path before filesystem traversal."
  (unless (and (stringp path) (<= (length path) bound))
    (fnn-refuse "clone path exceeds ACL2-owned path bound"))
  (let ((octets (fnn-string-octets path)))
    (unless (and (<= (length octets) bound)
                 (or (not inputp)
                     (eq (fnn-core 'fn-store-checkpoint-clone-input-pathp
                                   (fnn-octet-list octets)) t)))
      (fnn-refuse "clone path is not an admitted absolute path")))
  path)

#+linux
(sb-alien:define-alien-routine ("renameat2" fnn-%clone-renameat2)
    sb-alien:int
  (old-directory sb-alien:int) (old-name sb-alien:c-string)
  (new-directory sb-alien:int) (new-name sb-alien:c-string)
  (flags sb-alien:unsigned-int))

(defun fnn-clone-publish-no-replace (stage destination)
  "Publish a completed fenced tree without ever replacing a destination."
  #+linux
  (let ((result (fnn-%clone-renameat2 -100 stage -100 destination 1)))
    (when (< result 0)
      (let ((errno (sb-alien:get-errno)))
        (if (= errno sb-posix:eexist)
            (fnn-refuse "clone destination appeared during publication")
          (fnn-os-fail errno destination)))))
  #-linux
  (declare (ignore stage destination))
  #-linux
  (fnn-refuse "clone publication requires no-replace renameat2"))

(defun fnn-clone-copy-regular (source destination max-bytes)
  (let ((input nil) (output nil))
    (unwind-protect
         (progn
           (setq input (fnn-open source (logior sb-posix:o-rdonly
                                                +fnn-o-nofollow+)))
           (let ((info (fnn-fstat input)))
             (unless (fnn-regular-p info)
               (fnn-fault "clone source is not a regular file: ~a" source))
             (unless (and (<= 0 (sb-posix:stat-size info))
                          (<= (sb-posix:stat-size info)
                              (- max-bytes *fnn-clone-copy-bytes*)))
               (fnn-refuse "clone exceeds ACL2-owned byte bound")))
           (setq output (fnn-open destination
                                  (logior sb-posix:o-wronly sb-posix:o-creat
                                          sb-posix:o-excl +fnn-o-nofollow+)
                                  #o600))
           (let ((buffer (fnn-make-octets 65536)))
             (loop for count = (fnn-read-fd input buffer)
                   until (zerop count)
                   do (progn
                        (incf *fnn-clone-copy-bytes* count)
                        (when (> *fnn-clone-copy-bytes* max-bytes)
                          (fnn-refuse "clone exceeds ACL2-owned byte bound"))
                        (fnn-write-all output (subseq buffer 0 count)))))
           (fnn-fsync-file output))
      (when output (fnn-close output))
      (when input (fnn-close input)))))

(defun fnn-clone-copy-tree (source destination depth max-depth max-entries
                            max-bytes path-bound)
  (when (> depth max-depth)
    (fnn-refuse "clone exceeds ACL2-owned directory depth bound"))
  (fnn-clone-checked-path source path-bound)
  (fnn-clone-checked-path destination path-bound)
  (fnn-safe-directory source)
  (fnn-safe-directory destination)
  (let ((dir (fnn-posix (source) (sb-posix:opendir source))))
    (unwind-protect
         (loop
           (let ((entry (fnn-posix (source) (sb-posix:readdir dir))))
             (when (sb-alien:null-alien entry) (return))
             (let ((name (sb-posix:dirent-name entry)))
               (unless (or (string= name ".") (string= name ".."))
                 (incf *fnn-clone-copy-count*)
                 (when (> *fnn-clone-copy-count* max-entries)
                   (fnn-refuse "clone exceeds ACL2-owned entry bound"))
                 (let* ((from (fnn-join source name))
                        (to (fnn-join destination name))
                        (info (progn
                                (fnn-clone-checked-path from path-bound)
                                (fnn-clone-checked-path to path-bound)
                                (fnn-lstat from))))
                   (cond ((and info (fnn-directory-p info)
                               (not (fnn-symlink-p info)))
                          (fnn-mkdir to #o700)
                          (fnn-clone-copy-tree from to (1+ depth)
                                               max-depth max-entries max-bytes
                                               path-bound))
                         ((and info (fnn-regular-p info)
                               (not (fnn-symlink-p info)))
                          (fnn-clone-copy-regular from to max-bytes))
                         (t (fnn-refuse
                             "clone refuses missing, linked, or special source: ~a"
                             from))))))))
      (fnn-posix (source) (sb-posix:closedir dir))))
  (fnn-fsync-dir destination))

(defun fnn-clone-canonical-paths (source destination)
  (let ((path-bound (fnn-clone-path-bound)))
   (fnn-clone-checked-path source path-bound t)
   (fnn-clone-checked-path destination path-bound t)
   (fnn-safe-directory source)
   (let* ((source-real (string-right-trim "/" (namestring (truename source))))
         (source-parent
           (string-right-trim "/" (namestring (truename (fnn-parent source-real)))))
         (destination-parent
           (string-right-trim "/" (namestring (truename (fnn-parent destination)))))
         (trimmed (string-right-trim "/" destination))
         (slash (position #\/ trimmed :from-end t))
         (name (and slash (subseq trimmed (1+ slash)))))
    (unless (and (string= source-parent destination-parent)
                 name (> (length name) 0)
                 (not (member name '("." "..") :test #'string=)))
      (fnn-refuse "clone destination must be a distinct sibling of source"))
    (let ((target (fnn-join destination-parent name)))
      (fnn-clone-checked-path source-real path-bound t)
      (fnn-clone-checked-path target path-bound t)
      (when (or (string= source-real target) (fnn-lstat target))
        (fnn-refuse "clone destination already exists"))
      (values source-real target destination-parent path-bound)))))

(defun fnn-clone-read-marker (destination)
  (let* ((path-bound (fnn-clone-path-bound))
         (_ (fnn-clone-checked-path destination path-bound t))
         (store (make-fnn-store destination :writable nil))
         (path (fnn-clone-fence-path store))
         (bound (fnn-nat (fnn-core 'fn-store-checkpoint-clone-fence-read-bound))))
    (declare (ignore _))
    (fnn-clone-checked-path path path-bound)
    (unless (fnn-check-regular path)
      (fnn-refuse "clone activation requires its durable fence"))
    (fnn-read-regular-bounded path bound)))

(defun fnn-clone-canonical-target (destination)
  "A short parent alias cannot bypass the ACL2 clone path width."
  (let ((path-bound (fnn-clone-path-bound)))
    (fnn-clone-checked-path destination path-bound t)
    (fnn-safe-directory destination)
    (fnn-clone-checked-path
     (string-right-trim "/" (namestring (truename destination)))
     path-bound t)))

(defun fnn-clone-activate (destination)
  (let* ((destination (fnn-clone-canonical-target destination))
         (marker (fnn-clone-read-marker destination))
         (octets (fnn-octet-list marker))
         (decoded (fnn-core 'fn-cpe-decode-exact octets))
         (service nil))
    (unless (and (listp decoded) (eq (first decoded) :ok))
      (fnn-refuse "clone fence is not a canonical rollover event"))
    (let ((*fnn-clone-activation* t))
      (unwind-protect
           (progn
             (setq service (fnn-owner-install destination 1))
             (case (fnn-owner-core 'fn-owner-checkpoint-clone-phase octets)
               (:pending
                (unless (eq (fnn-owner-consumer-commit service (second decoded))
                            :durable)
                  (fnn-indeterminate "clone rollover was not durable"))
                (fnn-checkpoint-test-stop "clone-rollover-durable"))
               (:completed nil)
               (otherwise (fnn-refuse
                           "clone fence does not bind recovered Store"))))
        (when service
          (ignore-errors (fnn-owner-feed-close-all service))
          (fnn-store-close (fnn-owner-service-store service))))
      ; Reopen independently after the publisher closed.  A completed journal
      ; event, rather than the in-memory owner transition, releases the fence.
      (multiple-value-bind (store records)
          (fnn-open-live-store destination t)
        (declare (ignore records))
        (unwind-protect
             (unless (eq (fnn-core-state 'fn-store-checkpoint-clone-phase
                                         octets) :completed)
               (fnn-indeterminate "clone rollover did not survive reopen"))
          (fnn-store-close store)))
      (let* ((store (make-fnn-store destination :writable nil))
             (path (fnn-clone-fence-path store)))
        (handler-case
            (progn (fnn-unlink path)
                   (fnn-checkpoint-test-stop "clone-fence-unlinked")
                   (fnn-fsync-dir destination))
          (fnn-os-error ()
            (fnn-indeterminate
             "clone activation fence removal is uncertain")))))
    (fnn-out "clone activated with durable incarnation rollover")
    +fnn-exit-ok+))

(defun fnn-checkpoint-command-clone (source destination)
  (multiple-value-bind (source-real target parent path-bound)
      (fnn-clone-canonical-paths source destination)
    (multiple-value-bind (store records) (fnn-open-live-store source-real t)
      (declare (ignore records))
      (unwind-protect
           (let* ((fresh-id
                    (multiple-value-bind (history incarnation)
                        (fnn-owner-consumer-entropy-observation)
                      (declare (ignore history))
                      incarnation))
                  (proposed
                    (fnn-core-state 'fn-store-checkpoint-rollover-proposal
                                    fresh-id)))
             (unless (and (listp proposed) (eq (first proposed) :ok))
               (fnn-refuse "ACL2 refused clone incarnation: ~s" proposed))
             (let* ((event (second proposed))
                    (frame (fnn-core 'fn-cpe-encode event))
                    (stage (fnn-join parent
                                     (format nil ".fn-clone-~d-~a"
                                             (sb-posix:getpid)
                                             (fnn-random-hex 12))))
                    (max-depth
                      (fnn-nat (fnn-core 'fn-store-checkpoint-clone-max-depth)))
                    (max-entries
                      (fnn-nat (fnn-core 'fn-store-checkpoint-clone-max-entries)))
                    (max-bytes
                      (fnn-nat (fnn-core 'fn-store-checkpoint-clone-max-bytes))))
               (unless (fnn-octet-list-p frame)
                 (fnn-fault "ACL2 returned a malformed clone fence"))
               (fnn-clone-checked-path stage path-bound)
               (fnn-clone-checked-path
                (fnn-clone-fence-path (make-fnn-store stage :writable nil))
                path-bound)
               (fnn-mkdir stage #o700)
               (fnn-write-staged
                (fnn-clone-fence-path (make-fnn-store stage :writable nil))
                (fnn-octets frame))
               (fnn-fsync-dir stage)
               (fnn-fsync-dir parent)
               (fnn-checkpoint-test-stop "clone-fence-durable")
               (let ((*fnn-clone-copy-count* 0)
                     (*fnn-clone-copy-bytes* 0))
                 (fnn-clone-copy-tree source-real stage 0
                                      max-depth max-entries max-bytes path-bound))
               (fnn-fsync-dir stage)
               (when (fnn-lstat target)
                 (fnn-refuse "clone destination appeared during copy"))
               (handler-case
                   (progn (fnn-clone-publish-no-replace stage target)
                          (fnn-fsync-dir parent)
                          (fnn-checkpoint-test-stop "clone-published"))
                 (fnn-os-error ()
                   (fnn-indeterminate
                    "clone directory publication is uncertain")))
               (fnn-clone-activate target)))
        (fnn-store-close store)))))

(defparameter +fnn-checkpoint-retired-verbs+ '("publish" "select" "status"))

(defun fnn-checkpoint-command (command args)
  (cond ((member command +fnn-checkpoint-retired-verbs+ :test #'string=)
         (fnn-refuse "checkpoint ~a: generation checkpoints are retired on the record log; the store's checkpoint is the state checkpoint: `operator CONFIG store checkpoint' (or `store ROOT checkpoint'), `operator CONFIG store compact'" command))
        ((string= command "clone")
         (unless (= (length args) 2)
           (error 'fnn-usage-error :message
                  "checkpoint clone SOURCE DESTINATION"))
         (fnn-checkpoint-command-clone (first args) (second args)))
        ((string= command "clone-resume")
         (unless (= (length args) 1)
           (error 'fnn-usage-error :message "checkpoint clone-resume DESTINATION"))
         (fnn-clone-activate (first args)))
        (t (error 'fnn-usage-error :message
                  (format nil "unknown checkpoint command ~a" command)))))

(fnn-register-verb "checkpoint" #'fnn-checkpoint-command)
