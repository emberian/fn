; fn: the cut names and the admission of `operator CONFIG init' (PKT-647),
; P-INIT-PUB, over the byte model (crash model v2).
;
; `operator init' used to build the store in place, file by file under ROOT
; (fnn-initialize), so a crash left a partial store the operator verb then
; refused (STORE-EXISTS) and recovery faulted on (power-loss 2026-09-26,
; PKT-647).  It now builds the empty store beside ROOT, in ROOT.init-XXXX,
; and publishes it by the import's program: the SAME steps as
; books/store-import-publication.lisp fn-bs-imp-program, with init's cut
; names.  The host is host/native/io.lisp `fnn-command-init-published', which
; `operator init' calls (host/native/operator.lisp fnn-operator-execute-init).
;
; What the host publishes is books/store-init-log-publication.lisp's plan
; (the record log's: staging/, config/, journal/; config.json, the
; generation-1 configuration record and journal/000001.log), under that
; book's keystone `fn-bs-init-log-program-crash-is-no-store-or-the-complete-
; empty-log' (PRF-268).  This book keeps what that plan reuses: init's cut
; names and their renaming, and the admission the host asks before it writes
; anything.  (The per-file layout's plan, transactions/ and
; allocation-frontier.json, went with lane log-leftovers, 2026-09-27: no
; image published it since the flip.)
(in-package "ACL2")
(include-book "store-import-publication")

; -----------------------------------------------------------------------------
; The program.

; init's cut names, one for each of fn-bs-imp-program's.
(defconst *fn-bs-init-pub-cut-names*
  '(("import-stage-created" . "init-stage-created")
    ("import-subdir-created" . "init-subdir-created")
    ("import-file-created" . "init-file-created")
    ("import-file-written" . "init-file-written")
    ("import-file-durable" . "init-file-durable")
    ("import-subdir-durable" . "init-subdir-durable")
    ("import-staged-durable" . "init-staged-durable")
    ("import-validated" . "init-validated")
    ("import-published" . "init-published")
    ("import-durable" . "init-durable")))

(defun fn-bs-init-pub-cut-name (label)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal label *fn-bs-init-pub-cut-names*)))
    (if hit (cdr hit) label)))

(defun fn-bs-init-pub-rename-step (step)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp step) (equal (car step) :cut))
      (list :cut (fn-bs-init-pub-cut-name (nth 1 step)))
    step))

(defun fn-bs-init-pub-rename-cuts (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (cons (fn-bs-init-pub-rename-step (car steps))
            (fn-bs-init-pub-rename-cuts (cdr steps)))
    nil))

; -----------------------------------------------------------------------------
; `operator init' before it writes anything (host: fnn-command-init-published).
; STAGE-VERDICT is fn-bs-imp-classify of a leftover ROOT.init-* and ROOT (nil
; when there is none); ROOT-PRESENT is whether ROOT exists; STAGE-HELD is
; whether a live init holds the leftover's lock (the host's non-blocking
; flock on the staged directory, which every init holds from its mkdir to
; its end).  The answer:
;   :proceed                  nothing is there: build and publish
;   :discard-stage            only an unheld staged directory: an earlier
;                             init died before publication; ROOT holds no
;                             store and the stage holds nothing any command
;                             acknowledged, so the host removes it and asks
;                             again (PKT-894: a crash at any init cut leaves
;                             the old state, and a retry of init runs; no
;                             repair verb)
;   (:refused :init-in-progress)     only a staged directory another live
;                             init holds: that init is running
;   (:refused :publication-uncertain) the staged directory beside ROOT: ROOT
;                             is the complete empty store (PRF-268);
;                             recover it, then remove the staged directory
;   (:refused :store-path-exists)    ROOT exists (the store markers are
;                             fn-native-operator-init-outcome's): init never
;                             replaces or fills an existing directory; a
;                             ROOT an init published is complete (PRF-268)
;                             and `recover' opens it
(defun fn-bs-init-pub-admission (stage-verdict root-present stage-held)
  (declare (xargs :guard t))
  (cond ((equal stage-verdict :not-published)
         (if stage-held (list :refused :init-in-progress) :discard-stage))
        ((equal stage-verdict :publication-uncertain) (list :refused :publication-uncertain))
        (root-present (list :refused :store-path-exists))
        (t :proceed)))

; Init proceeds only when neither name is present.
(defthm fn-bs-init-pub-admission-proceeds-only-on-nothing
  (implies (equal (fn-bs-init-pub-admission (and stage-present
                                                 (fn-bs-imp-classify stage-present root-present))
                                            root-present stage-held)
                  :proceed)
           (and (not stage-present) (not root-present)))
  :rule-classes nil)


; KEYSTONE (PRF-942).  The admission as the host composes it
; (fnn-command-init-published: the classification of a leftover stage, nil
; without one, whether ROOT exists and whether a live init holds the stage)
; decides by what is present and by nothing else: it proceeds exactly when
; neither name is present, it discards exactly an unheld stage beside an
; absent ROOT, and each other combination is the refusal that names it.
; The theorem above takes the admission as a hypothesis; this one concludes
; it.
(defthm fn-bs-init-pub-admission-decides-by-what-is-present
  (let ((admission (fn-bs-init-pub-admission
                    (and stage-present
                         (fn-bs-imp-classify stage-present root-present))
                    root-present stage-held)))
    (and (iff (equal admission :proceed)
              (and (not stage-present) (not root-present)))
         (iff (equal admission :discard-stage)
              (and stage-present (not root-present) (not stage-held)))
         (implies (and stage-present (not root-present) stage-held)
                  (equal admission (list :refused :init-in-progress)))
         (implies (and stage-present root-present)
                  (equal admission (list :refused :publication-uncertain)))
         (implies (and (not stage-present) root-present)
                  (equal admission (list :refused :store-path-exists)))))
  :rule-classes nil)
