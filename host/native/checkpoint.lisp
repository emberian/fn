;;; Native checkpoint capture, publication, selection, and diagnostic restore.
;;;
;;; Authoritative recovery remains fnn-recover's full immutable-journal replay.
;;; This layer runs afterward.  ACL2 captures and validates checkpoint bytes,
;;; restores their suffix into checkpoint-private globals, and compares that
;;; result with the already-replayed fn-store-sn.  It never installs a
;;; checkpoint as the live store state.
(in-package "ACL2")

(defconstant +fnn-checkpoint-selection-bound+ 4096)
(defconstant +fnn-checkpoint-prefix+ "generation-")
(defconstant +fnn-checkpoint-suffix+ ".fncp")
(defconstant +fnn-checkpoint-selection-name+ "selected.fncp")

(define-condition fnn-checkpoint-corruption (error)
  ((reason :initarg :reason :reader fnn-checkpoint-corruption-reason)))

(defun fnn-checkpoint-corrupt (control &rest args)
  (error 'fnn-checkpoint-corruption :reason (apply #'format nil control args)))

(defun fnn-checkpoints (store)
  (fnn-join (fnn-store-root store) "checkpoints"))

(defun fnn-checkpoint-selection-path (store)
  (fnn-join (fnn-checkpoints store) +fnn-checkpoint-selection-name+))

(defun fnn-checkpoint-generation-name (generation)
  ; Filename grammar remains a bounded host boundary.  ACL2 owns generation
  ; selection and the uint32 domain through fn-store-checkpoint-next-generation.
  (format nil "~a~d~a" +fnn-checkpoint-prefix+ generation +fnn-checkpoint-suffix+))

(defun fnn-checkpoint-generation-path (store generation)
  (fnn-join (fnn-checkpoints store)
            (fnn-checkpoint-generation-name generation)))

(defun fnn-checkpoint-generation-from-name (name)
  "A canonical generation filename's natural, or NIL for another entry."
  (let* ((prefix-length (length +fnn-checkpoint-prefix+))
         (suffix-length (length +fnn-checkpoint-suffix+))
         (name-length (length name)))
    (when (and (> name-length (+ prefix-length suffix-length))
               (string= +fnn-checkpoint-prefix+ name :end2 prefix-length)
               (string= +fnn-checkpoint-suffix+ name
                        :start2 (- name-length suffix-length)))
      (let ((digits (subseq name prefix-length (- name-length suffix-length))))
        (when (every #'digit-char-p digits)
          (let ((generation (parse-integer digits)))
            ; Reject aliases such as generation-00.fncp.
            (when (string= name (fnn-checkpoint-generation-name generation))
              generation)))))))

(defun fnn-checkpoint-generations (store)
  "Published generation naturals, boundary-checked and ascending."
  (let ((directory (fnn-checkpoints store)))
    (unless (fnn-lstat directory) (return-from fnn-checkpoint-generations nil))
    (fnn-safe-directory directory)
    (let ((found nil))
      (dolist (name (fnn-list-directory directory))
        (unless (string= name +fnn-checkpoint-selection-name+)
          (let ((generation (fnn-checkpoint-generation-from-name name)))
            (unless generation
              (fnn-fault "unexpected checkpoint namespace entry: ~a" name))
            (fnn-check-regular (fnn-join directory name))
            (push generation found))))
      (sort found #'<))))

(defun fnn-checkpoint-next-generation (store)
  (let ((answer (fnn-core 'fn-store-checkpoint-next-generation
                          (fnn-checkpoint-generations store))))
    (case answer
      (:bad (fnn-fault "checkpoint generation namespace is not gap-free"))
      (:exhausted (fnn-refuse "checkpoint generation domain exhausted"))
      (otherwise (fnn-nat answer)))))

(defun fnn-checkpoint-capture (records store)
  (let ((protected
          (fnn-core-state 'fn-store-checkpoint-protected
                          (mapcar #'fnn-octet-list records)
                          (fnn-store-frontier store))))
    (when (or (keywordp protected) (not (fnn-octet-list-p protected)))
      (fnn-refuse "ACL2 refused checkpoint capture"))
    (fnn-seal (fnn-octets protected))))

(defun fnn-checkpoint-publish (store records)
  "Publish one immutable generation through the shared fn-jpub I/O effect."
  (fnn-require-writer store)
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
        (case (fnn-immutable-publish-effect
               (third authorization) stage final directory frame
               :cleanup-directory (fnn-staging store))
        (:durable generation)
        (:refused (fnn-refuse "checkpoint generation publication refused"))
        (:uncertain (fnn-indeterminate "checkpoint generation publication is uncertain"))
        (otherwise (fnn-fault "invalid immutable checkpoint publication outcome")))))))

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
  (fnn-require-writer store)
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
                               (fnn-checkpoint-test-stop "selection-file")
                               (fnn-checkpoint-marker-step phase :ok))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :known-fail)))))
             (:replace
              (setq phase
                    (handler-case
                        (progn (fnn-checkpoint-test-fault "selection-replace" final)
                               (fnn-replace stage final)
                               (fnn-checkpoint-test-stop "selection-replace")
                               (fnn-checkpoint-marker-step phase :ok))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :error)))))
             (:directory-barrier
              (setq phase
                    (handler-case
                        (progn (fnn-checkpoint-test-fault "selection-directory" directory)
                               (fnn-fsync-dir directory)
                               (fnn-checkpoint-test-stop "selection-directory")
                               (fnn-checkpoint-marker-step phase :ok))
                      (fnn-os-error ()
                        (fnn-checkpoint-marker-step phase :error)))))
             (:done (return))
             (otherwise (fnn-fault "ACL2 returned invalid checkpoint marker action"))))
      ; Cleanup occurs after the model's terminal outcome and cannot change it.
      (ignore-errors (fnn-unlink stage) (fnn-fsync-dir (fnn-staging store))))
    (case (fnn-core 'fn-store-checkpoint-marker-outcome phase)
      (:durable :durable)
      (:refused (fnn-refuse "checkpoint selection refused before replacement"))
      (:uncertain (fnn-indeterminate "checkpoint selection replacement is uncertain"))
      (otherwise (fnn-fault "ACL2 left checkpoint marker replacement pending")))))

(defun fnn-checkpoint-selected-generation (store)
  (let ((path (fnn-checkpoint-selection-path store)))
    (unless (fnn-check-regular path)
      (return-from fnn-checkpoint-selected-generation nil))
    (let* ((raw (fnn-read-regular-bounded path +fnn-checkpoint-selection-bound+))
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
                        (eq (fnn-core-state 'fn-store-checkpoint-differential) t)))
                  (when (and (not differential)
                             (not (member (or (sb-ext:posix-getenv
                                               "FN_CHECKPOINT_DIFFERENTIAL") "")
                                          '("" "0") :test #'string=)))
                    (fnn-fault "checkpoint plus suffix differs from full replay"))
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
