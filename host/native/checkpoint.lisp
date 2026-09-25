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

; Lossless transaction packs use a separate durable namespace but the same
; ACL2-owned canonical generation and selection component names.
(defun fnn-pack-directory (store) (fnn-join (fnn-store-root store) "packs"))
(defun fnn-pack-generation-path (store generation)
  (fnn-join (fnn-pack-directory store) (fnn-checkpoint-generation-name generation)))
(defun fnn-pack-selection-path (store)
  (fnn-join (fnn-pack-directory store) (fnn-checkpoint-selection-name)))

(defun fnn-pack-generations (store)
  (let ((directory (fnn-pack-directory store)))
    (unless (fnn-lstat directory) (return-from fnn-pack-generations nil))
    (fnn-safe-directory directory)
    (let* ((names (fnn-list-directory-bounded
                   directory (fnn-checkpoint-namespace-observation-limit) "pack namespace"))
           (plan (fnn-core 'fn-store-checkpoint-namespace-plan
                           (mapcar (lambda (name)
                                     (fnn-octet-list (fnn-string-octets name))) names))))
      (unless (and (listp plan) (eq (first plan) :ok))
        (fnn-fault "ACL2 rejected pack namespace: ~s" plan))
      (second plan))))

(defun fnn-pack-selected-generation (store)
  (let ((path (fnn-pack-selection-path store)))
    (unless (fnn-check-regular path) (return-from fnn-pack-selected-generation nil))
    (let* ((raw (fnn-read-regular-bounded path (fnn-checkpoint-selection-read-bound)))
           (answer (fnn-core 'fn-store-checkpoint-selection-decode
                             (fnn-octet-list raw) (fnn-digest-of raw))))
      (unless (and (listp answer) (eq (first answer) :ok))
        (fnn-checkpoint-corrupt "pack selection marker does not decode"))
      (second answer))))

(defun fnn-pack-publish-generation (store records &optional chain coverage selected)
  "Capture the next link of the selected chain (RECORDS above its boundary,
one quantum) into the next pack generation and publish it, unselected.
Returns the generation, the sealed frame and the new boundary; or
:NOTHING-UNCOVERED and ACL2's line when the chain already covers RECORDS
(`fn-ccc-nothing-uncovered-leaves-files-and-marker'), before any directory
operation."
  (fnn-checkpoint-require-mutation-ready store)
  (let ((directory (fnn-pack-directory store))
        (captured (fnn-core 'fn-store-checkpoint-chain-capture
                            (mapcar #'fnn-octet-list records)
                            (if coverage (second coverage) 0)
                            (if coverage (third coverage) 0)
                            (or selected 0)
                            (if chain (third (first chain)) nil))))
    (when (and (listp captured) (eq (first captured) :nothing-uncovered))
      (unless (stringp (second captured))
        (fnn-fault "ACL2 returned an invalid no-op line: ~s" captured))
      (return-from fnn-pack-publish-generation
        (values :nothing-uncovered (second captured))))
    (fnn-safe-directory directory t)
    (let* ((generations (fnn-pack-generations store))
           (generation (fnn-core 'fn-store-checkpoint-pack-next-generation
                                 generations)))
      (unless (and (integerp generation) (>= generation 0)
                   (listp captured) (eq (first captured) :ok)
                   (fnn-octet-list-p (second captured))
                   (integerp (third captured)))
        (fnn-refuse "ACL2 refused pack capture/publication"))
      (let* ((stage (fnn-join (fnn-staging store)
                              (format nil ".pack-~d-~a" (sb-posix:getpid)
                                      (fnn-random-hex 12))))
             (final (fnn-pack-generation-path store generation))
             (frame (fnn-seal (fnn-octets (second captured)))))
        (let ((authorization
                (fnn-core 'fn-store-checkpoint-pack-publication-initial
                          generations generation t (if (fnn-lstat final) nil t))))
          (unless (and (listp authorization) (eq (first authorization) :ok)
                       (= (second authorization) generation))
            (fnn-fault "ACL2 refused pack publication authority: ~s" authorization))
          (setf (fnn-store-fenced store) t)
          ; The same fn-jpub publication as a checkpoint generation, so the
          ; same candidate-* process-death cuts (fn-cpp-publication-step).
          (case (fnn-immutable-publish-effect
                 (third authorization) stage final directory frame
                 :cleanup-directory (fnn-staging store)
                 :observer #'fnn-checkpoint-candidate-observer)
            (:durable (setf (fnn-store-fenced store) nil))
            (:refused (setf (fnn-store-fenced store) nil)
                      (fnn-refuse "pack generation publication refused"))
            (:uncertain (fnn-indeterminate "pack generation publication is uncertain"))
            (otherwise (fnn-fault "invalid pack publication outcome"))))
        (values generation frame (third captured))))))

(defun fnn-pack-select (store generation)
  "Replace the pack selection marker under the ACL2 marker driver."
  (fnn-checkpoint-require-mutation-ready store)
  (let* ((marker-value (fnn-core 'fn-store-checkpoint-selection-protected generation))
         (marker (and (fnn-octet-list-p marker-value) (fnn-seal (fnn-octets marker-value)))))
    (unless marker (fnn-refuse "ACL2 refused pack selection marker"))
    (case (fnn-marker-replace store (fnn-pack-directory store)
                              (fnn-pack-selection-path store) marker ".pack-selection")
      (:durable (setf (fnn-store-fenced store) nil) :durable)
      (:refused (setf (fnn-store-fenced store) nil)
                (fnn-refuse "pack selection refused"))
      (:uncertain (fnn-indeterminate "pack selection is uncertain"))
      (otherwise (fnn-fault "pack selection marker remained pending")))))

(defun fnn-pack-publish (store records selectp)
  "`checkpoint pack ROOT [select]': with select, extend the selected chain
until it covers RECORDS; without, publish the next link unselected.  Returns
the generation, or :NOTHING-UNCOVERED and ACL2's line when the selected chain
already covers RECORDS (nothing written)."
  (if selectp
      (multiple-value-bind (generation links line)
          (fnn-pack-extend-chain store records)
        (if (zerop links) (values :nothing-uncovered line) generation))
    (multiple-value-bind (chain coverage selected)
        (fnn-pack-selected-raw-and-coverage store)
      (multiple-value-bind (generation line)
          (fnn-pack-publish-generation store records chain coverage selected)
        (setf (fnn-store-fenced store) nil)
        (values generation line)))))

(defun fnn-pack-extend-chain (store records)
  "Publish and select links, each over the records above the selected chain,
until the chain covers RECORDS.  Each link is its own publication and
selection, so a cut leaves the previous chain selected
(`fn-ccc-publication-crash-walks-old-or-new-chain').  ACL2's capture ends the
loop with its no-op.  Returns the newest generation, the number of links
written and ACL2's no-op line."
  (multiple-value-bind (chain coverage selected)
      (fnn-pack-selected-raw-and-coverage store)
    (let ((links 0) (generation selected) (line nil))
      (loop do (multiple-value-bind (next frame boundary)
                   (fnn-pack-publish-generation store records chain coverage selected)
                 (when (eq next :nothing-uncovered)
                   (setq line frame)
                   (loop-finish))
                 (unless (> boundary (if coverage (second coverage) 0))
                   (fnn-fault "ACL2 captured a link that covers nothing"))
                 (fnn-pack-select store next)
                 (fnn-checkpoint-test-stop "pack-chain-link")
                 (incf links)
                 (setq generation next selected next
                       chain (cons (list next (fnn-octet-list frame) (fnn-digest-of frame))
                                   chain))
                 (let ((c (fnn-core 'fn-store-checkpoint-chain-coverage
                                    chain (fnn-config-max-transactions store)
                                    (fnn-store-frontier store)
                                    (fnn-pack-link-bound store))))
                   (unless (and (listp c) (eq (first c) :ok) (= (second c) boundary))
                     (fnn-fault "ACL2 refused the chain it just extended: ~s" c))
                   (setq coverage c))))
      (setf (fnn-store-fenced store) nil)
      (values generation links line))))

(defun fnn-pack-prefix-reclaim (store)
  (fnn-checkpoint-require-mutation-ready store)
  (let ((lower (fnn-pack-lower-bound store)))
    (when (= lower 0) (fnn-refuse "selected pack covers no reclaimable prefix"))
    (let* ((limit (fnn-config-max-transactions store))
           (observed (sort (fnn-list-directory-bounded
                            (fnn-transactions store) limit "transaction namespace")
                           #'string<))
           (plan (fnn-core 'fn-bs-pack-reclaim-plan observed limit lower)))
      (unless (and (listp plan) (<= (length plan) lower)
                   (every (lambda (name)
                            (and (stringp name)
                                 (member name observed :test #'string=)))
                          plan))
        (fnn-fault "ACL2 refused transaction prefix reclaim plan"))
      (setf (fnn-store-fenced store) t)
      (handler-case
          (progn
            (dolist (name plan)
              (fnn-unlink (fnn-join (fnn-transactions store) name))
              (fnn-checkpoint-test-stop "pack-reclaim-unlink"))
            (fnn-fsync-dir (fnn-transactions store))
            (fnn-checkpoint-test-stop "pack-reclaim-directory")
            (setf (fnn-store-fenced store) nil)
            plan)
        (fnn-os-error (e)
          (fnn-indeterminate "transaction prefix reclamation is uncertain: ~a" e))))))

(defun fnn-pack-retire-older-generations (store)
  "Reclaim only pack generations older than validated selected authority."
  (fnn-checkpoint-require-mutation-ready store)
  ; This resolves an interrupted marker replacement, checks the selected
  ; generation frame and its coverage, and refuses any missing authority.
  (multiple-value-bind (chain coverage selected)
      (fnn-pack-selected-raw-and-coverage store)
    (unless (and coverage (integerp selected) (>= selected 0))
      (fnn-refuse "no selected pack generation to retain"))
    (let* ((generations (fnn-pack-generations store))
           (plan (fnn-core 'fn-store-checkpoint-chain-retire-plan
                           generations chain (fnn-pack-link-bound store))))
      (unless (and (listp plan)
                   (<= (length plan) (length generations))
                   (every (lambda (generation)
                            (and (integerp generation) (>= generation 0)
                                 (member generation generations)
                                 (not (member generation (mapcar #'first chain)))))
                          plan))
        (fnn-fault "ACL2 refused pack generation retirement plan"))
      (when (null plan) (return-from fnn-pack-retire-older-generations nil))
      (setf (fnn-store-fenced store) t)
      (handler-case
          (progn
            (dolist (generation plan)
              (fnn-unlink (fnn-pack-generation-path store generation))
              (fnn-checkpoint-test-stop "pack-retire-unlink"))
            (fnn-fsync-dir (fnn-pack-directory store))
            (fnn-checkpoint-test-stop "pack-retire-directory")
            (setf (fnn-store-fenced store) nil)
            plan)
        (fnn-os-error (e)
          (fnn-indeterminate "pack generation retirement is uncertain: ~a" e))))))

(defun fnn-pack-link-bound (store)
  (let ((bound (fnn-core 'fn-store-checkpoint-chain-link-bound (fnn-store-config store))))
    (unless (and (integerp bound) (> bound 0))
      (fnn-fault "ACL2 returned invalid pack link read bound"))
    bound))

(defun fnn-pack-walk (store head)
  "Read the chain from HEAD, newest first, one bounded link read per step.
ACL2 decodes each link and names its predecessor; the walk is given the
profile's max-transactions links (every link covers a record)."
  (let ((bound (fnn-pack-link-bound store))
        (fuel (fnn-core 'fn-store-checkpoint-chain-walk-bound (fnn-store-config store)))
        (chain nil)
        (generation head))
    (unless (and (integerp fuel) (> fuel 0))
      (fnn-fault "ACL2 returned invalid pack chain walk bound"))
    (loop
      (when (<= fuel 0)
        (fnn-checkpoint-corrupt "pack chain exceeds the profile's walk bound"))
      (decf fuel)
      (let ((path (fnn-pack-generation-path store generation)))
        (unless (fnn-check-regular path)
          (fnn-checkpoint-corrupt "pack chain generation ~d is missing" generation))
        (let* ((raw (fnn-read-regular-bounded path (+ (fnn-constant :trailer) bound)))
               (octets (fnn-octet-list raw))
               (digest (fnn-digest-of raw))
               (step (fnn-core 'fn-store-checkpoint-chain-step octets digest bound)))
          (unless (and (listp step) (eq (first step) :ok)
                       (integerp (second step)) (>= (second step) 0)
                       (integerp (third step)) (>= (third step) 0))
            (fnn-checkpoint-corrupt "pack chain link ~d does not decode" generation))
          (push (list generation octets digest) chain)
          (when (= (second step) 0) (return (nreverse chain)))
          (setq generation (third step)))))))

(defun fnn-pack-selected-raw-and-coverage (store)
  "The selected chain (newest first, (GENERATION OCTETS DIGEST) each), its
coverage (:ok BOUNDARY FRONTIER) and the selected generation."
  ; Resolve any prior process-death window in generation/marker publication
  ; before consulting selected authority.  A barrier error cannot authorize a
  ; zero-start fallback or prefix deletion.
  (when (fnn-lstat (fnn-pack-directory store))
    (fnn-safe-directory (fnn-pack-directory store))
    (handler-case (fnn-fsync-dir (fnn-pack-directory store))
      (fnn-os-error (e)
        (fnn-indeterminate "cannot resolve selected pack namespace: ~a" e))))
  (let ((generation (fnn-pack-selected-generation store)))
    (unless generation (return-from fnn-pack-selected-raw-and-coverage (values nil nil)))
    (let* ((chain (fnn-pack-walk store generation))
           (coverage (fnn-core 'fn-store-checkpoint-chain-coverage
                               chain
                               (fnn-config-max-transactions store)
                               (fnn-store-frontier store)
                               (fnn-pack-link-bound store))))
      (unless (and (listp coverage) (eq (first coverage) :ok)
                   (integerp (second coverage)) (>= (second coverage) 0))
        (fnn-checkpoint-corrupt "selected pack chain coverage is invalid: ~s" coverage))
      (values chain coverage generation))))

(defun fnn-pack-lower-bound (store)
  (multiple-value-bind (raw coverage) (fnn-pack-selected-raw-and-coverage store)
    (declare (ignore raw))
    (if coverage (second coverage) 0)))

(defun fnn-pack-recover-records (store records sequences actual-lower)
  (multiple-value-bind (chain coverage) (fnn-pack-selected-raw-and-coverage store)
    (unless coverage (return-from fnn-pack-recover-records records))
    (let* ((sequence (second coverage))
           (_ (unless (= actual-lower sequence)
                (fnn-checkpoint-corrupt
                 "ACL2 namespace lower bound disagrees with selected pack")))
           (observed (mapcar (lambda (number record)
                               (list number (fnn-octet-list record)))
                             sequences records))
           (answer (fnn-core 'fn-store-checkpoint-chain-observe
                             chain observed
                             (fnn-store-frontier store)
                             (fnn-pack-link-bound store))))
      (unless (and (listp answer) (eq (first answer) :ok))
        (fnn-checkpoint-corrupt "selected pack does not reconstruct observed history"))
      (mapcar #'fnn-as-octets (second answer)))))

(defun fnn-pack-chain-report (store)
  "The `status' line for the selected pack chain: its links, newest first,
and the boundary ACL2 computed over them."
  (multiple-value-bind (chain coverage) (fnn-pack-selected-raw-and-coverage store)
    (if (null coverage)
        "pack-chain none"
      (format nil "pack-chain links=~d boundary=~d generations=~{~d~^,~}"
              (length chain) (second coverage) (mapcar #'first chain)))))

(setq *fnn-pack-status-callback* #'fnn-pack-chain-report)
(setq *fnn-pack-recover-callback* #'fnn-pack-recover-records)
(setq *fnn-pack-lower-bound-callback* #'fnn-pack-lower-bound)

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

(defun fnn-checkpoint-command-pack (root selectp)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (unwind-protect
         (multiple-value-bind (generation line) (fnn-pack-publish store records selectp)
           (if (eq generation :nothing-uncovered)
               (fnn-out "~a" line)
               (fnn-out "packed generation=~d records=~d selected=~a"
                        generation (length records) (if selectp "yes" "no")))
           +fnn-exit-ok+)
      (fnn-store-close store))))
(defun fnn-checkpoint-command-pack-reclaim (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (declare (ignore records))
    (unwind-protect
         (let ((removed (fnn-pack-prefix-reclaim store)))
           (fnn-out "reclaimed transaction-prefix=~d" (length removed))
           +fnn-exit-ok+)
      (fnn-store-close store))))

(defun fnn-checkpoint-command-pack-retire (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (declare (ignore records))
    (unwind-protect
         (let ((retired (fnn-pack-retire-older-generations store)))
           (fnn-out "retired pack-generations=~d" (length retired))
           +fnn-exit-ok+)
      (fnn-store-close store))))

;;; `operator CONFIG store compact': one offline verb over the three steps
;;; above.  ACL2 decides (books/store-compact-verb.lisp `fn-cverb-decide',
;;; through host/checkpoint-host.lisp `fn-store-compact-decide'); this
;;; function observes the store once, carries out exactly the steps ACL2
;;; returned, in ACL2's order, and reports.  The exclusive open refuses the
;;; verb while an owner runs.  Each step keeps its own outcome classes:
;;; a refusal before any durable change exits 1, an uncertain publication,
;;; selection, reclaim or retirement exits 3, a fault 4.

(defun fnn-compact-footprint (store names generations)
  "lstat sizes of every transaction file and pack generation present."
  (flet ((size (path)
           (let ((st (fnn-lstat path)))
             (unless (and st (fnn-regular-p st) (not (fnn-symlink-p st)))
               (fnn-fault "compaction footprint: ~a is not a regular file" path))
             (sb-posix:stat-size st))))
    (append (mapcar (lambda (name) (size (fnn-join (fnn-transactions store) name)))
                    names)
            (mapcar (lambda (generation)
                      (size (fnn-pack-generation-path store generation)))
                    generations))))

(defun fnn-compact-steps (store records)
  "Observe, ask ACL2, and carry out its steps.  Returns the report line."
  (fnn-checkpoint-require-mutation-ready store)
  (multiple-value-bind (chain coverage selected)
      (fnn-pack-selected-raw-and-coverage store)
    (let* ((lower (if coverage (second coverage) 0))
           (names (sort (fnn-list-directory-bounded
                         (fnn-transactions store) (fnn-config-max-transactions store)
                         "transaction namespace")
                        #'string<))
           (generations (fnn-pack-generations store))
           ;; The generations the decision may retire: ACL2's plan outside the
           ;; selected chain (a chain link is never older-and-retirable), plus
           ;; the selected head it counts from.
           (retirable (if chain
                          (let ((plan (fnn-core 'fn-store-checkpoint-chain-retire-plan
                                                generations chain
                                                (fnn-pack-link-bound store))))
                            (unless (listp plan)
                              (fnn-fault "ACL2 refused the pack retirement plan"))
                            (sort (cons selected (copy-list plan)) #'<))
                        generations))
           (decision (fnn-core 'fn-store-compact-decide
                               (fnn-store-config store)
                               (mapcar #'fnn-octet-list records)
                               lower names retirable selected
                               (fnn-compact-footprint store names generations))))
      (unless (and (listp decision) (member (first decision) '(:compact :refused)))
        (fnn-fault "ACL2 returned no compaction decision"))
      (when (eq (first decision) :refused)
        (fnn-refuse "compaction refused: ~(~a~)" (second decision)))
      (let ((generation nil) (links 0) (reclaimed nil) (retired nil))
        (dolist (step (second decision))
          (case step
            (:pack (multiple-value-setq (generation links)
                     (fnn-pack-extend-chain store records)))
            ;; Each link was selected as it was published (fnn-pack-extend-chain).
            (:select
             (unless generation (fnn-fault "ACL2 selected a pack it did not publish")))
            (:reclaim (setq reclaimed (fnn-pack-prefix-reclaim store)))
            (:retire (setq retired (fnn-pack-retire-older-generations store)))
            (otherwise (fnn-fault "ACL2 returned an unknown compaction step ~s" step))))
        (format nil "compacted steps=~{~(~a~)~^,~} records=~d generation=~a links=~d reclaimed=~d retired=~d"
                (second decision) (length records)
                (or generation (fnn-pack-selected-generation store))
                links (length reclaimed) (length retired))))))

(defun fnn-command-compact (root)
  (multiple-value-bind (store records) (fnn-open-live-store root t)
    (unwind-protect
         (progn (fnn-out "~a" (fnn-compact-steps store records))
                +fnn-exit-ok+)
      (fnn-store-close store))))

(setq *fnn-compact-callback* #'fnn-command-compact)

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
        ((string= command "pack")
         (unless (or (= (length args) 1)
                     (and (= (length args) 2) (string= (second args) "select")))
           (error 'fnn-usage-error :message "checkpoint pack ROOT [select]"))
         (fnn-checkpoint-command-pack (first args) (= (length args) 2)))
        ((string= command "pack-reclaim")
         (unless (= (length args) 1)
           (error 'fnn-usage-error :message "checkpoint pack-reclaim ROOT"))
         (fnn-checkpoint-command-pack-reclaim (first args)))
        ((string= command "pack-retire")
         (unless (= (length args) 1)
           (error 'fnn-usage-error :message "checkpoint pack-retire ROOT"))
         (fnn-checkpoint-command-pack-retire (first args)))
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
