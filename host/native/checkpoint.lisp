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

(defun fnn-checkpoint-name-result (value description)
  "Validate and decode one ACL2-owned path component."
  (unless (and (fnn-octet-list-p value) value
               (every (lambda (octet) (< octet 128)) value)
               (not (member (char-code #\/) value))
               (not (member 0 value)))
    (fnn-fault "ACL2 returned invalid ~a" description))
  (fnn-octets-string (fnn-octets value)))

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

(defun fnn-checkpoint-namespace-observation-limit ()
  (let ((limit (fnn-core 'fn-store-checkpoint-namespace-observation-limit)))
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
                   directory (fnn-checkpoint-namespace-observation-limit)
                   "checkpoint namespace"))
           (plan (fnn-core
                  'fn-store-checkpoint-namespace-plan
                  (mapcar (lambda (name)
                            (fnn-octet-list (fnn-string-octets name)))
                          names))))
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
                                               generations)))
                         (case answer
                           (:bad (fnn-fault "checkpoint generation namespace is not gap-free"))
                           (:exhausted (fnn-refuse "checkpoint generation domain exhausted"))
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
                        generations generation t (if (fnn-lstat final) nil t))))
        (unless (and (listp authorization) (eq (first authorization) :ok)
                     (= (second authorization) generation))
          (case (second authorization)
            (:occupied (fnn-fault "checkpoint next generation is already occupied"))
            (:exhausted (fnn-refuse "checkpoint generation domain exhausted"))
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
  (when (string= (or (sb-ext:posix-getenv "FN_CHECKPOINT_TEST_FAIL") "") point)
    (fnn-os-fail sb-posix:eio path)))

(defun fnn-checkpoint-test-stop (point)
  "A deterministic process-death boundary used only when the test env names it."
  (when (string= (or (sb-ext:posix-getenv "FN_CHECKPOINT_TEST_STOP") "") point)
    (sb-posix:kill (sb-posix:getpid) sb-unix:sigstop)))

(defun fnn-checkpoint-marker-step (phase result)
  (fnn-core 'fn-store-checkpoint-marker-step phase result))

(defun fnn-checkpoint-select (store generation)
  "Replace the authority marker under the ACL2 marker driver."
  (fnn-checkpoint-require-mutation-ready store)
  (unless (member generation (fnn-checkpoint-generations store))
    (fnn-refuse "checkpoint generation ~d is not published" generation))
  (let* ((protected (fnn-core 'fn-store-checkpoint-selection-protected generation))
         (frame (and (fnn-octet-list-p protected) (fnn-seal (fnn-octets protected))))
         (directory (fnn-checkpoints store))
         (stage (fnn-join (fnn-staging store)
                          (format nil ".selection-~d-~a"
                                  (sb-posix:getpid) (fnn-random-hex 12))))
         (final (fnn-checkpoint-selection-path store))
         (phase :marker-staged))
    (unless frame (fnn-refuse "ACL2 refused checkpoint selection marker"))
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
    (case (fnn-core 'fn-store-checkpoint-marker-outcome phase)
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
                                   (or (sb-ext:posix-getenv
                                        "FN_CHECKPOINT_TEST_MISMATCH") "")
                                   "1")))))
                  ; Full replay remains live authority, but an ACL2-computed
                  ; mismatch means the selected checkpoint is not a valid
                  ; diagnostic image.  Surface corruption on every open;
                  ; an environment flag must not turn disagreement into OK.
                  (unless differential
                    (fnn-checkpoint-corrupt
                     "checkpoint plus suffix differs from full replay"))
                  (list :ok generation sequence differential)))))))
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
        (t (error 'fnn-usage-error :message
                  (format nil "unknown checkpoint command ~a" command)))))

(fnn-register-verb "checkpoint" #'fnn-checkpoint-command)
