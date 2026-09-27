;;; Native checkpoint capture, publication, selection, and diagnostic restore.
;;;
;;; Authoritative recovery remains fnn-recover's full immutable-journal replay.
;;; This layer runs afterward.  ACL2 captures and validates checkpoint bytes,
;;; restores their suffix into checkpoint-private globals, and compares that
;;; result with the already-replayed fn-store-sn.  It never installs a
;;; checkpoint as the live store state.
(in-package "ACL2")

(define-condition fnn-checkpoint-corruption (error)
  ((reason :initarg :reason :reader fnn-checkpoint-corruption-reason)))

(defun fnn-checkpoint-corrupt (control &rest args)
  (error 'fnn-checkpoint-corruption :reason (apply #'format nil control args)))

(defun fnn-checkpoints (store)
  (fnn-join (fnn-store-root store) "checkpoints"))

; fnn-checkpoint-name-result, which decodes every ACL2-owned checkpoint path
; component below, is in io.lisp: opening any Store decodes the clone fence
; name with it, and the DTN image loads io.lisp without this file.

(defun fnn-checkpoint-selection-name ()
  (fnn-checkpoint-name-result
   (fnn-core 'fn-store-checkpoint-selection-name-octets)
   "checkpoint selection name"))

(defun fnn-checkpoint-selection-path (store)
  (fnn-join (fnn-checkpoints store) (fnn-checkpoint-selection-name)))

(defun fnn-checkpoint-generation-name (generation)
  (fnn-checkpoint-name-result
   (fnn-core 'fn-store-checkpoint-generation-name-octets generation)
   "checkpoint generation name"))

(defun fnn-checkpoint-generation-path (store generation)
  (fnn-join (fnn-checkpoints store)
            (fnn-checkpoint-generation-name generation)))

(defun fnn-checkpoint-namespace-observation-limit (store)
  "D27, PRF-171: the opened profile's retained-generation capacity plus the
selection marker (`fn-cpp-generation-capacity')."
  (let ((limit (fnn-core 'fn-store-checkpoint-namespace-observation-limit
                         (fnn-store-config store))))
    (unless (and (integerp limit) (>= limit 0))
      (fnn-fault "ACL2 returned invalid checkpoint namespace bound"))
    limit))

(defun fnn-checkpoint-selection-read-bound ()
  (let ((bound (fnn-core 'fn-store-checkpoint-selection-read-bound)))
    (unless (and (integerp bound) (> bound 0))
      (fnn-fault "ACL2 returned invalid checkpoint selection read bound"))
    bound))

(defun fnn-checkpoint-generations (store)
  "The ACL2-owned sorted plan for one bounded directory observation."
  (let ((directory (fnn-checkpoints store)))
    (unless (fnn-lstat directory) (return-from fnn-checkpoint-generations nil))
    (fnn-safe-directory directory)
    (let* ((names (fnn-list-directory-bounded
                   directory (fnn-checkpoint-namespace-observation-limit store)
                   "checkpoint namespace"))
           (plan (fnn-core
                  'fn-store-checkpoint-namespace-plan
                  (mapcar (lambda (name)
                            (fnn-octet-list (fnn-string-octets name)))
                          names)
                  (fnn-store-config store))))
      (unless (and (listp plan) (eq (first plan) :ok)
                   (listp (second plan))
                   (every (lambda (generation)
                            (and (integerp generation) (>= generation 0)))
                          (second plan)))
        (fnn-fault "ACL2 rejected checkpoint namespace: ~s" plan))
      (dolist (generation (second plan))
        (fnn-check-regular (fnn-checkpoint-generation-path store generation)))
      (second plan))))

(defun fnn-checkpoint-require-mutation-ready (store)
  "Checkpoint mutation requires the common writer gate and an unfenced Store."
  (fnn-require-writer store)
  (when (fnn-store-fenced store)
    (fnn-indeterminate "store is fenced pending recovery")))

(defun fnn-checkpoint-capture (records store)
  (let ((protected
          (fnn-core-state 'fn-store-checkpoint-protected
                          (mapcar #'fnn-octet-list records)
                          (fnn-store-frontier store))))
    (when (or (keywordp protected) (not (fnn-octet-list-p protected)))
      (fnn-refuse "ACL2 refused checkpoint capture"))
    (fnn-seal (fnn-octets protected))))

(defun fnn-checkpoint-candidate-observer (point publication)
  (declare (ignore publication))
  (case point
    (:file-barrier (fnn-checkpoint-test-stop "candidate-file"))
    (:link-result (fnn-checkpoint-test-stop "candidate-link"))
    (:directory-barrier (fnn-checkpoint-test-stop "candidate-directory"))))

(defun fnn-checkpoint-publish (store records)
  "Publish one immutable generation through the shared fn-jpub I/O effect."
  (fnn-checkpoint-require-mutation-ready store)
  (let ((directory (fnn-checkpoints store)))
    (fnn-safe-directory directory t)
    (let* ((generations (fnn-checkpoint-generations store))
           (generation (let ((answer (fnn-core 'fn-store-checkpoint-next-generation
                                               generations (fnn-store-config store))))
                         (case answer
                           (:bad (fnn-fault "checkpoint generation namespace is not gap-free"))
                           (:exhausted (fnn-refuse "checkpoint generations at the profile's capacity (max-transactions + 1); reinstall with a larger max-transactions: store export, then store import --max-transactions N"))
                           (otherwise (fnn-nat answer)))))
           (frame (fnn-checkpoint-capture records store))
           (stage (fnn-join (fnn-staging store)
                            (format nil ".checkpoint-~d-~a"
                                    (sb-posix:getpid) (fnn-random-hex 12))))
           (final (fnn-checkpoint-generation-path store generation)))
      ; The exclusive store lock plus this exact-name check supplies U04's
      ; next-final-absent premise.  The shared effect never replaces FINAL.
      (let ((authorization
              (fnn-core 'fn-store-checkpoint-publication-initial
                        generations generation t (if (fnn-lstat final) nil t)
                        (fnn-store-config store))))
        (unless (and (listp authorization) (eq (first authorization) :ok)
                     (= (second authorization) generation))
          (case (second authorization)
            (:occupied (fnn-fault "checkpoint next generation is already occupied"))
            (:exhausted (fnn-refuse "checkpoint generations at the profile's capacity (max-transactions + 1); reinstall with a larger max-transactions: store export, then store import --max-transactions N"))
            (otherwise (fnn-fault "ACL2 refused checkpoint publication authority: ~s"
                                  authorization))))
        (setf (fnn-store-fenced store) t)
        (case (fnn-immutable-publish-effect
               (third authorization) stage final directory frame
               :cleanup-directory (fnn-staging store)
               :observer #'fnn-checkpoint-candidate-observer)
          (:durable
           (setf (fnn-store-fenced store) nil)
           generation)
          (:refused
           (setf (fnn-store-fenced store) nil)
           (fnn-refuse "checkpoint generation publication refused"))
          (:uncertain
           (fnn-indeterminate "checkpoint generation publication is uncertain"))
          (otherwise
           (fnn-fault "invalid immutable checkpoint publication outcome")))))))

(defun fnn-checkpoint-test-fault (point path)
  (when (string= (or (fnn-developer-selector "FN_CHECKPOINT_TEST_FAIL") "") point)
    (fnn-os-fail sb-posix:eio path)))

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

(defun fnn-checkpoint-marker-step (phase result)
  (fnn-core 'fn-store-checkpoint-marker-step phase result))

(defun fnn-marker-replace (store directory final frame stage-prefix)
  "Replace one selection marker under the ACL2 marker driver; the model outcome.

The checkpoint and the pack selection share this loop and so share its
selection-* process-death cuts (fn-cpp-marker-step)."
  (let ((stage (fnn-join (fnn-staging store)
                         (format nil "~a-~d-~a" stage-prefix
                                 (sb-posix:getpid) (fnn-random-hex 12))))
        (phase :marker-staged))
    (unwind-protect
         (loop
           (case (fnn-core 'fn-store-checkpoint-marker-action phase)
             (:stage-and-file-barrier
              (setq phase
                    (handler-case
                        (progn (fnn-checkpoint-test-fault "selection-file" stage)
                               (fnn-write-staged stage frame)
                               (let ((next (fnn-checkpoint-marker-step phase :ok)))
                                 (fnn-checkpoint-test-stop "selection-file")
                                 next))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :known-fail)))))
             (:replace
              (setf (fnn-store-fenced store) t)
              (setq phase
                    (handler-case
                        (progn (fnn-checkpoint-test-fault "selection-replace" final)
                               (fnn-replace stage final)
                               (let ((next (fnn-checkpoint-marker-step phase :ok)))
                                 (fnn-checkpoint-test-stop "selection-replace")
                                 next))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :error)))))
             (:directory-barrier
              (setq phase
                    (handler-case
                        (progn (fnn-checkpoint-test-fault "selection-directory" directory)
                               (fnn-fsync-dir directory)
                               (let ((next (fnn-checkpoint-marker-step phase :ok)))
                                 (fnn-checkpoint-test-stop "selection-directory")
                                 next))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :error)))))
             (:done (return))
             (otherwise (fnn-fault "ACL2 returned invalid checkpoint marker action"))))
      ; Cleanup occurs after the model's terminal outcome and cannot change it.
      (ignore-errors (fnn-unlink stage) (fnn-fsync-dir (fnn-staging store))))
    (fnn-core 'fn-store-checkpoint-marker-outcome phase)))

(defun fnn-checkpoint-select (store generation)
  "Replace the authority marker under the ACL2 marker driver."
  (fnn-checkpoint-require-mutation-ready store)
  (unless (member generation (fnn-checkpoint-generations store))
    (fnn-refuse "checkpoint generation ~d is not published" generation))
  (let* ((protected (fnn-core 'fn-store-checkpoint-selection-protected generation))
         (frame (and (fnn-octet-list-p protected) (fnn-seal (fnn-octets protected)))))
    (unless frame (fnn-refuse "ACL2 refused checkpoint selection marker"))
    (case (fnn-marker-replace store (fnn-checkpoints store)
                              (fnn-checkpoint-selection-path store) frame ".selection")
      (:durable
       (setf (fnn-store-fenced store) nil)
       :durable)
      (:refused
       (setf (fnn-store-fenced store) nil)
       (fnn-refuse "checkpoint selection refused before replacement"))
      (:uncertain (fnn-indeterminate "checkpoint selection replacement is uncertain"))
      (otherwise (fnn-fault "ACL2 left checkpoint marker replacement pending")))))

(defun fnn-checkpoint-selected-generation (store)
  (let ((path (fnn-checkpoint-selection-path store)))
    (unless (fnn-check-regular path)
      (return-from fnn-checkpoint-selected-generation nil))
    (let* ((raw (fnn-read-regular-bounded
                 path (fnn-checkpoint-selection-read-bound)))
           (answer (fnn-core 'fn-store-checkpoint-selection-decode
                             (fnn-octet-list raw) (fnn-digest-of raw))))
      (unless (and (listp answer) (eq (first answer) :ok)
                   (integerp (second answer)) (>= (second answer) 0))
        (fnn-checkpoint-corrupt "selection marker does not decode: ~s" answer))
      (second answer))))

(defun fnn-checkpoint-restore-selected (store records)
  "Validate selected checkpoint and compare checkpoint+suffix to full replay."
  (handler-case
      (let ((directory (fnn-checkpoints store)))
        (unless (fnn-lstat directory) (return-from fnn-checkpoint-restore-selected '(:none)))
        (fnn-safe-directory directory)
        ; Resolve a prior uncertain marker or generation namespace observation
        ; before consulting it.  Full journal recovery remains independent.
        (fnn-fsync-dir directory)
        (let ((generation (fnn-checkpoint-selected-generation store)))
          (unless generation (return-from fnn-checkpoint-restore-selected '(:none)))
          (let ((path (fnn-checkpoint-generation-path store generation)))
            (unless (fnn-check-regular path)
              (fnn-checkpoint-corrupt "selected generation ~d is missing" generation))
            (let* ((raw (fnn-read-regular-bounded
                         path (+ (fnn-constant :overhead) (fnn-constant :max-inbound))))
                   (decoded (fnn-core-state 'fn-store-checkpoint-decode
                                            (fnn-octet-list raw) (fnn-digest-of raw)
                                            (fnn-store-frontier store) (length records))))
              (unless (and (listp decoded) (eq (first decoded) :ok)
                           (integerp (second decoded))
                           (<= 0 (second decoded) (length records)))
                (fnn-checkpoint-corrupt "selected generation ~d does not decode: ~s"
                                        generation decoded))
              (let* ((sequence (second decoded))
                     (suffix (nthcdr sequence records))
                     (restored (fnn-core-state 'fn-store-checkpoint-restore
                                               (mapcar #'fnn-octet-list suffix)
                                               (fnn-store-frontier store))))
                (unless (eq restored :ok)
                  (fnn-checkpoint-corrupt "selected generation ~d does not restore: ~s"
                                          generation restored))
                (let ((differential
                        (and (eq (fnn-core-state
                                  'fn-store-checkpoint-differential) t)
                             ; Developer-only reachability hook for the
                             ; otherwise theorem-excluded mismatch branch.
                             (not (string=
                                   (or (fnn-developer-selector "FN_CHECKPOINT_TEST_MISMATCH") "")
                                   "1")))))
                  ; Full replay remains live authority, but an ACL2-computed
                  ; mismatch means the selected checkpoint is not a valid
                  ; diagnostic image.  Surface corruption on every open;
                  ; an environment flag must not turn disagreement into OK.
                  (unless differential
                    (fnn-checkpoint-corrupt
                     "checkpoint plus suffix differs from full replay"))
                  (let ((auxiliary
                         (fnn-core-state
                          'fn-store-checkpoint-auxiliary-differential)))
                    (unless (equal auxiliary '(:ok 2))
                      (fnn-checkpoint-corrupt
                       "full replay auxiliary state differs: ~s" auxiliary))
                    (list :ok generation sequence differential :equal-v2))))))))
    (fnn-checkpoint-corruption (e)
      (list :corrupt (fnn-checkpoint-corruption-reason e)))))

(setq *fnn-checkpoint-recover-callback* #'fnn-checkpoint-restore-selected)

(defun fnn-checkpoint-command-publish (root selectp)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (unwind-protect
         (let ((generation (fnn-checkpoint-publish store records)))
           (when selectp (fnn-checkpoint-select store generation))
           (fnn-out "published generation=~d records=~d selected=~a"
                    generation (length records) (if selectp "yes" "no"))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-checkpoint-command-select (root generation)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (declare (ignore records))
    (unwind-protect
         (progn (fnn-checkpoint-select store generation)
                (fnn-out "selected generation=~d" generation)
                +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-checkpoint-command-status (root)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (let* ((outcome (fnn-store-checkpoint-outcome store))
                (generations (fnn-checkpoint-generations store)))
           (fnn-out "generations=~a ~a"
                    (if generations (format nil "~{~d~^ ~}" generations) "-")
                    (fnn-checkpoint-report store))
           (if (eq (first outcome) :corrupt) +fnn-exit-fault+ +fnn-exit-ok+))
      (fnn-store-close store))))

(defun fnn-command-compact (root)
  "`store compact'.  Format 9 (the record log): compaction is the
checkpoint's rotation and the drop of the segments it covers (design
2026-09-27 storage-log section 6; T8 fn-lg-segment-drop-preserves-the-open):
a state checkpoint is published at the history's end with the log rotated,
then the covered segments are unlinked.  The open keeps the covered prefix in
the arena (no octet list of the history: D27; the checkpoint is written from
the state).  Format 8: the pack chain."
  (multiple-value-bind (store records) (fnn-open-live-store root t nil nil)
    (unwind-protect
         (progn
           ;; Every store an image opens is format 9 (batch AW: a format-8
           ;; profile is refused at the open); the pack chain's verb is the
           ;; per-file layout's, deleted with it (design section 9 row 5).
           (unless (fnn-store-logp store)
             (fnn-fault "a store that is not on the record log opened"))
           (let ((count (fnn-open-history-count store records)))
             (fnn-out "compacted steps=checkpoint,drop records=~d ~a"
                      count (fnn-state-checkpoint-publish-steps store count)))
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

(defun fnn-log-history-each (store records fn)
  "Call FN on each record of the history the open recovered, in order, as
octets: the covered prefix encoded from the checkpoint's rows a chunk at a
time (fn-store-sco-prefix-octets-range), then RECORDS (the suffix the open
read; the whole history after a full replay).  No list of the history's
octet lists is built."
  (let ((mode (fnn-store-open-mode store)))
    (when (eq (first mode) :checkpoint)
      (let ((s (second mode)))
        (loop for start from 0 below s by +fnn-log-reclaim-prefix-chunk+ do
          (let ((chunk (fnn-core-arena-state 'fn-store-sco-prefix-octets-range start
                                             (min +fnn-log-reclaim-prefix-chunk+ (- s start)))))
            (dolist (octets chunk)
              (funcall fn (fnn-as-octets octets)))))))
    (dolist (record records)
      (funcall fn record))))

(defun fnn-log-reclaim-steps (store records dry)
  "`store reclaim' on a format-9 store (books/store-log-reclaim.lisp): the
history streamed one record at a time into ACL2's fold (fn-rcls-step under the
store's context, compact-arena's books/store-reclaim-stream.lisp) with each
record's rewrite (fn-rclp-event) kept as an octet vector, then ACL2's decision
over the fold (fn-lgr-decide-stream; KEYSTONE fn-lgr-decide-stream-is-lgr-
decide: the whole-history decision, whose rewritten history is those
rewrites).  On :reclaim the rewritten history is replayed into the store node
(the chunked replay every open runs, fnn-recover-log-replay) and its state
checkpoint published with the log rotated, then the segments it covers are
dropped (fnn-state-checkpoint-publish-steps: T8): the released payloads'
octets leave the disk with them.  Returns the report line."
  (let* ((clock (fnn-store-prepare-observation))
         (ctx (fnn-core-state 'fn-store-reclaim-context clock))
         (acc (fnn-core 'fn-store-reclaim-init))
         (count 0)
         (rewritten nil))
    (fnn-log-history-each
     store records
     (lambda (record)
       (let ((octets (fnn-octet-list record)))
         (incf count)
         (setq acc (fnn-core 'fn-store-reclaim-step acc octets ctx))
         (unless dry
           (let ((event (fnn-core 'fn-store-log-reclaim-event octets ctx)))
             (unless (fnn-octet-list-p event)
               (fnn-fault "ACL2 returned a malformed rewritten record"))
             (push (fnn-octets event) rewritten))))))
    (let ((decision (fnn-core-state 'fn-store-log-reclaim-decide-stream
                                    (fnn-store-config store) clock acc (if dry t nil))))
      (unless (and (consp decision) (member (first decision) '(:refused :none :dry-run :reclaim)))
        (fnn-fault "ACL2 returned no reclaim decision"))
      (case (first decision)
        (:refused (fnn-refuse "reclaim refused: ~(~a~)" (second decision)))
        (:none (format nil "reclaimed=0 ~a" (fnn-reclaim-counts-line (second decision))))
        (:dry-run
         (destructuring-bind (msgids freed counts) (rest decision)
           (format nil "dry-run would-reclaim=~d freed-octets=~d ~a~{~%would-reclaim ~a~}"
                   (length msgids) freed (fnn-reclaim-counts-line counts)
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
             ;; The store node becomes the rewritten history's (the chunked
             ;; replay every open runs), and the checkpoint the open will read
             ;; is its capture.
             (fnn-core-state 'fn-store-sco-clear)
             (fnn-bridge-reset)
             (fnn-recover-log-replay store history (fnn-config-records store))
             (setf (fnn-store-open-mode store) (list :full-replay :reclaim))
             (format nil "reclaimed=~d freed-octets=~d ~a~{~%reclaimed ~a~}"
                     (length msgids) freed
                     (fnn-state-checkpoint-publish-steps store count)
                     msgids))))
        (otherwise (fnn-fault "ACL2 returned an unknown reclaim decision"))))))

(defun fnn-command-reclaim (root dry)
  ;; The open keeps the covered prefix in the arena; the reclaim streams it
  ;; (fnn-log-history-each).
  (multiple-value-bind (store records) (fnn-open-live-store root (not dry) nil nil)
    (unwind-protect
         (progn (unless (fnn-store-logp store)
                  (fnn-fault "a store that is not on the record log opened"))
                (fnn-out "~a" (fnn-log-reclaim-steps store records dry))
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

(defun fnn-checkpoint-command (command args)
  (cond ((string= command "publish")
         (unless (or (= (length args) 1)
                     (and (= (length args) 2) (string= (second args) "select")))
           (error 'fnn-usage-error :message "checkpoint publish ROOT [select]"))
         (fnn-checkpoint-command-publish (first args) (= (length args) 2)))
        ((string= command "select")
         (unless (= (length args) 2)
           (error 'fnn-usage-error :message "checkpoint select ROOT GENERATION"))
         (fnn-checkpoint-command-select (first args) (parse-integer (second args))))
        ((string= command "status")
         (unless (= (length args) 1)
           (error 'fnn-usage-error :message "checkpoint status ROOT"))
         (fnn-checkpoint-command-status (first args)))
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
