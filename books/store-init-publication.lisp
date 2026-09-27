; fn: the publication program of `operator CONFIG init' (PKT-647), P-INIT-PUB,
; over the byte model (crash model v2).
;
; `operator init' used to build the store in place, file by file under ROOT
; (fnn-initialize), so a crash left a partial store the operator verb then
; refused (STORE-EXISTS) and recovery faulted on (power-loss 2026-09-26,
; PKT-647).  It now builds the empty store beside ROOT, in ROOT.init-XXXX,
; and publishes it by the import's program: the SAME steps as
; books/store-import-publication.lisp fn-bs-imp-program, with init's plan
; (the three subdirectories; config.json, the allocation frontier and the
; generation-1 configuration record; no transaction file) and init's cut
; names.  The host is host/native/io.lisp `fnn-command-init-published', which
; `operator init' calls (host/native/operator.lisp fnn-operator-execute-init).
;
; Keystone fn-bs-init-pub-program-crash-is-no-store-or-the-complete-empty-store:
; a crash at any point of any run, any syscall outcome, leaves no store at
; ROOT or the complete empty store: the staged directory with every
; subdirectory and every plan file durable with exactly its octets, and
; nothing named in its transactions directory.
; fn-bs-init-pub-classify-by-what-is-known: the two names the host observes
; (ROOT.init-XXXX and ROOT) are read by fn-bs-imp-classify, and the answers
; that say ROOT holds no store are given only when it holds none.
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

; The staged tree: host/native/io.lisp makes transactions/, staging/ and
; config/ in this order.
(defconst *fn-bs-init-pub-subdirs*
  '(("transactions" . :transactions) ("staging" . :staging) ("config" . :config)))

; The plan, in the host's order: the profile, the frontier, the generation-1
; configuration record.  CONFIG, FRONTIER and RECORD are ACL2's frames
; (fn-store-metadata-config-frame, fn-store-metadata-frontier-frame,
; the bridge's initial configuration record).
(defun fn-bs-init-pub-files (config frontier record-name record)
  (declare (xargs :guard t))
  (list (list* :stage "config.json" config)
        (list* :stage "allocation-frontier.json" frontier)
        (list* :config record-name record)))

(defun fn-bs-init-pub-program (stage root config frontier record-name record)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-init-pub-rename-cuts
   (fn-bs-imp-program stage root *fn-bs-init-pub-subdirs*
                      (fn-bs-init-pub-files config frontier record-name record))))

; The staged store is empty: nothing named in its transactions directory.
(defun fn-bs-init-pub-emptyp (img)
  (declare (xargs :guard t :verify-guards nil))
  (null (cdr (assoc-equal :transactions (fn-bs-dirs img)))))

; -----------------------------------------------------------------------------
; A cut changes no state: the renamed program runs as the import's does.

(local (in-theory (enable fn-bs-invariants-vocabulary)))

(local
 (defthm fn-bs-init-pub-rename-cuts-step
   (equal (fn-bs-imp-step bs ks (fn-bs-init-pub-rename-step step) out groups capacity)
          (fn-bs-imp-step bs ks step out groups capacity))
   :hints (("Goal" :in-theory '(fn-bs-init-pub-rename-step fn-bs-imp-step fn-bs-step
                                car-cons (:e equal))))))

(local
 (defthm fn-bs-init-pub-run-of-renamed-cuts
   (equal (fn-bs-imp-run bs ks (fn-bs-init-pub-rename-cuts steps) outs groups capacity)
          (fn-bs-imp-run bs ks steps outs groups capacity))
   :hints (("Goal" :induct (fn-bs-imp-run bs ks steps outs groups capacity)
            :in-theory '(fn-bs-imp-run fn-bs-init-pub-rename-cuts car-cons cdr-cons
                         fn-bs-init-pub-rename-cuts-step
                         (:type-prescription fn-bs-init-pub-rename-cuts))))))

; -----------------------------------------------------------------------------
; Nothing is ever named in the transactions directory: no plan file is there,
; and no step issues an entry operation on it.

(defun fn-bs-init-pub-dir-quietp (s d)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-ops-for-dir (fn-bs-pending s) d))
       (null (cdr (assoc-equal d (fn-bs-dirs s))))))

(defun fn-bs-init-pub-step-sparesp (step d)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp step)
       (case (car step)
         ((:cut :write-all :fsync-file :fsync-dir) t)
         ((:create :mkdir) (not (equal (nth 1 step) d)))
         (:rename-dir-noreplace (and (not (equal (nth 1 step) d))
                                     (not (equal (nth 3 step) d))))
         (otherwise nil))))

(defun fn-bs-init-pub-steps-sparep (steps d)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (fn-bs-init-pub-step-sparesp (car steps) d)
           (fn-bs-init-pub-steps-sparep (cdr steps) d))
    t))

(local
 (defthm fn-bs-init-pub-ops-for-dir-of-crash-select-of-ops-for-dir
   (implies (not (equal x d))
            (equal (fn-bs-ops-for-dir (fn-bs-crash-select (fn-bs-ops-for-dir ops x) ch u) d)
                   nil))
   :hints (("Goal" :in-theory '(fn-bs-crash-select-keeps-quiet-dir
                                fn-bs-ops-for-dir-of-ops-for-dir-other)))))

(local
 (defthm fn-bs-init-pub-ops-for-dir-of-ops-not
   (and (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-ino ops ino) d)
               (fn-bs-ops-for-dir ops d))
        (implies (not (equal x d))
                 (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops x) d)
                        (fn-bs-ops-for-dir ops d))))
   :hints (("Goal" :in-theory '(fn-bs-ops-for-dir fn-bs-ops-not-for-ino
                                fn-bs-ops-not-for-dir car-cons cdr-cons atom (:e member-equal)
                                (:e equal) (:e car) (:e consp) member-equal)))))

(local
 (defthm fn-bs-init-pub-quiet-after-ops-not-for-dir
   (implies (not (fn-bs-ops-for-dir ops d))
            (not (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops x) d)))
   :hints (("Goal" :cases ((equal x d))
            :in-theory '(fn-bs-init-pub-ops-for-dir-of-ops-not
                         fn-bs-ops-for-dir-of-ops-not-for-dir)))))

(local
 (defthm fn-bs-init-pub-quiet-after-ops-for-dir
   (implies (not (fn-bs-ops-for-dir ops d))
            (and (not (fn-bs-ops-for-dir (fn-bs-ops-for-dir ops x) d))
                 (not (fn-bs-ops-for-dir (fn-bs-crash-select (fn-bs-ops-for-dir ops x) ch u)
                                         d))))
   :hints (("Goal" :in-theory '(fn-bs-ops-for-dir car-cons cdr-cons atom member-equal
                                (:e member-equal) (:e equal) (:e car) (:e consp)
                                fn-bs-crash-select-keeps-quiet-dir)))))

(local
 (defthm fn-bs-init-pub-step-keeps-dir-quiet
   (implies (and (fn-bs-init-pub-dir-quietp s d)
                 (fn-bs-init-pub-step-sparesp step d))
            (fn-bs-init-pub-dir-quietp (mv-nth 1 (fn-bs-imp-step s ks step out groups capacity))
                                       d))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-imp-step fn-bs-step fn-bs-create fn-bs-write
                             fn-bs-fsync-file fn-bs-fence-file fn-bs-fsync-dir fn-bs-fence-dir
                             fn-bs-mkdir fn-bs-rename-dir-noreplace)
                            (fn-bs-apply-entries fn-bs-crash-select))))))

(local
 (defthm fn-bs-init-pub-run-keeps-dir-quiet
   (implies (and (member-equal p (fn-bs-imp-run s ks steps outs groups capacity))
                 (fn-bs-init-pub-dir-quietp s d)
                 (fn-bs-init-pub-steps-sparep steps d))
            (fn-bs-init-pub-dir-quietp (car p) d))
   :hints (("Goal" :induct (fn-bs-imp-run s ks steps outs groups capacity)
            :in-theory (disable fn-bs-init-pub-dir-quietp fn-bs-imp-step)))))

(local
 (defthm fn-bs-init-pub-quiet-crash-is-empty
   (implies (fn-bs-init-pub-dir-quietp s :transactions)
            (fn-bs-init-pub-emptyp (fn-bs-crash s ch)))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))

(local
 (defthm fn-bs-init-pub-program-spares-transactions
   (implies (and (stringp stage) (stringp root))
            (fn-bs-init-pub-steps-sparep
             (fn-bs-imp-program stage root *fn-bs-init-pub-subdirs*
                                (fn-bs-init-pub-files config frontier record-name record))
             :transactions))
   :hints (("Goal" :in-theory (enable fn-bs-imp-program fn-bs-imp-staging-program
                                      fn-bs-imp-publication-program)))))

(local
 (defthm fn-bs-init-pub-quiet-at-start
   (implies (and (null (fn-bs-pending bs))
                 (not (assoc-equal d (fn-bs-dirs bs))))
            (fn-bs-init-pub-dir-quietp bs d))
   :hints (("Goal" :in-theory '(fn-bs-init-pub-dir-quietp fn-bs-ops-for-dir (:e cdr)
                                (:e fn-bs-ops-for-dir) default-cdr)))))

(local
 (defthm fn-bs-init-pub-input-is-quiet
   (implies (and (fn-bs-imp-inputp bs stage root subdirs files old)
                 (not (assoc-equal d (fn-bs-dirs bs))))
            (fn-bs-init-pub-dir-quietp bs d))
   :hints (("Goal" :in-theory '(fn-bs-imp-inputp fn-bs-init-pub-quiet-at-start)))))

(local
 (defthm fn-bs-init-pub-imp-inputp-strings
   (implies (fn-bs-imp-inputp bs stage root subdirs files old)
            (and (stringp stage) (stringp root)))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-bs-imp-inputp)))))

; -----------------------------------------------------------------------------
; The keystone and the classification.

(defthm fn-bs-init-pub-program-crash-is-no-store-or-the-complete-empty-store
  (implies (and (fn-bs-imp-inputp bs stage root *fn-bs-init-pub-subdirs*
                                  (fn-bs-init-pub-files config frontier record-name record)
                                  old)
                (not (assoc-equal :transactions (fn-bs-dirs bs)))
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks
                                               (fn-bs-init-pub-program stage root config frontier
                                                                       record-name record)
                                               outs groups capacity)))
           (and (fn-bs-imp-no-store-or-completep
                 (fn-bs-crash (car p) choices) root *fn-bs-init-pub-subdirs*
                 (fn-bs-init-pub-files config frontier record-name record)
                 (fn-bs-next-ino bs) old)
                (fn-bs-init-pub-emptyp (fn-bs-crash (car p) choices))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-bs-init-pub-program fn-bs-init-pub-run-of-renamed-cuts)
           :use ((:instance fn-bs-imp-program-crash-is-no-store-or-the-complete-store
                            (subdirs *fn-bs-init-pub-subdirs*)
                            (files (fn-bs-init-pub-files config frontier record-name record)))
                 (:instance fn-bs-init-pub-input-is-quiet
                            (subdirs *fn-bs-init-pub-subdirs*) (d :transactions)
                            (files (fn-bs-init-pub-files config frontier record-name record)))
                 (:instance fn-bs-init-pub-imp-inputp-strings
                            (subdirs *fn-bs-init-pub-subdirs*)
                            (files (fn-bs-init-pub-files config frontier record-name record)))
                 (:instance fn-bs-init-pub-program-spares-transactions)
                 (:instance fn-bs-init-pub-run-keeps-dir-quiet
                            (s bs) (d :transactions)
                            (steps (fn-bs-imp-program stage root *fn-bs-init-pub-subdirs*
                                                      (fn-bs-init-pub-files config frontier
                                                                            record-name record))))
                 (:instance fn-bs-init-pub-quiet-crash-is-empty (s (car p)) (ch choices))))))

(defthm fn-bs-init-pub-classify-by-what-is-known
  (implies (and (fn-bs-imp-inputp bs stage root *fn-bs-init-pub-subdirs*
                                  (fn-bs-init-pub-files config frontier record-name record)
                                  nil)
                (not (assoc-equal :transactions (fn-bs-dirs bs)))
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks
                                               (fn-bs-init-pub-program stage root config frontier
                                                                       record-name record)
                                               outs groups capacity)))
           (let* ((img (fn-bs-crash (car p) choices))
                  (verdict (fn-bs-imp-classify (fn-bs-durable-entry img :parent stage)
                                               (fn-bs-durable-entry img :parent root))))
             (and (implies (member-equal verdict '(:no-store :not-published))
                           (null (fn-bs-durable-entry img :parent root)))
                  (implies (member-equal verdict '(:store-present :publication-uncertain))
                           (and (equal (fn-bs-durable-entry img :parent root) :stage)
                                (fn-bs-imp-completep img *fn-bs-init-pub-subdirs*
                                                     (fn-bs-init-pub-files config frontier
                                                                           record-name record)
                                                     (fn-bs-next-ino bs))
                                (fn-bs-init-pub-emptyp img))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-init-pub-program)
                           (fn-bs-init-pub-files fn-bs-init-pub-emptyp fn-bs-crash
                            fn-bs-imp-classify-by-what-is-known
                            fn-bs-init-pub-program-crash-is-no-store-or-the-complete-empty-store))
           :use ((:instance fn-bs-imp-classify-by-what-is-known
                            (subdirs *fn-bs-init-pub-subdirs*)
                            (files (fn-bs-init-pub-files config frontier record-name record)))
                 (:instance fn-bs-init-pub-program-crash-is-no-store-or-the-complete-empty-store
                            (old nil))))))

; -----------------------------------------------------------------------------
; `operator init' before it writes anything (host: fnn-command-init-published).
; STAGE-VERDICT is fn-bs-imp-classify of a leftover ROOT.init-* and ROOT (nil
; when there is none); ROOT-PRESENT is whether ROOT exists.  The answer:
;   :proceed                  nothing is there: build and publish
;   (:refused :interrupted-init)     only the staged directory: the earlier
;                             init died before publication and ROOT holds no
;                             store; remove the staged directory, init again
;   (:refused :publication-uncertain) the staged directory beside ROOT: ROOT
;                             is the complete empty store (the keystone);
;                             recover it, then remove the staged directory
;   (:refused :store-path-exists)    ROOT exists (the store markers are
;                             fn-native-operator-init-outcome's): init never
;                             replaces or fills an existing directory
(defun fn-bs-init-pub-admission (stage-verdict root-present)
  (declare (xargs :guard t))
  (cond ((equal stage-verdict :not-published) (list :refused :interrupted-init))
        ((equal stage-verdict :publication-uncertain) (list :refused :publication-uncertain))
        (root-present (list :refused :store-path-exists))
        (t :proceed)))

; Init proceeds only when neither name is present.
(defthm fn-bs-init-pub-admission-proceeds-only-on-nothing
  (implies (equal (fn-bs-init-pub-admission (and stage-present
                                                 (fn-bs-imp-classify stage-present root-present))
                                            root-present)
                  :proceed)
           (and (not stage-present) (not root-present)))
  :rule-classes nil)

(in-theory (disable fn-bs-init-pub-program fn-bs-init-pub-files fn-bs-init-pub-emptyp))
