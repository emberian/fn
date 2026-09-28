; fn: `operator CONFIG init' of a format-9 store (lane log-2, 2026-09-27;
; PKT-COL-2 of lane commit-onto-log's record): its own publication program.
;
; A format-9 store commits through the record log (journal/000001.log) and
; never reads the per-file allocator (allocation-frontier.json) or the
; transactions directory.  Before this book its `init' ran the format-8
; per-file plan (those two written and never read; deleted by lane
; log-leftovers) and created the segment afterwards, outside any
; modelled program.  Its plan is now:
;
;   subdirectories  staging/, config/, journal/            (in this order)
;   files           config.json                            (the profile)
;                   config/00000001.cfg                    (generation 1)
;                   journal/000001.log                     (EXTENT zeros)
;
; published by the import's program with init's cut names (the SAME steps
; and cuts as the import's program, fn-bs-imp-program's), so
; tests/campaign/native_cuts.py's INIT_PUB_CUTS and the host's
; +fnn-init-publication-cuts+ name its cuts.  The segment is written as a
; plan file (create, write-all of its zeros, fsync), so its extent is
; durable before the stage is sealed and published.
;
; Keystone fn-bs-init-log-program-crash-is-no-store-or-the-complete-empty-log:
; a crash at any point of any run leaves no store at ROOT or the complete
; format-9 store (every subdirectory and plan file durable with exactly its
; octets), and then the segment is the empty log:
; fn-bs-init-log-segment-is-the-empty-log (recovery's kernel of EXTENT
; zeros holds no record, its frontier is 0, and R's content conjuncts hold,
; so the first open's P-LOG-RECOVER establishes R).
; fn-bs-init-log-classify-by-what-is-known: the host's classification of a
; leftover stage is the import's, over this plan.
(in-package "ACL2")
(include-book "store-init-publication")
(include-book "store-log-route")

(defconst *fn-bs-init-log-subdirs*
  '(("staging" . :staging) ("config" . :config) ("journal" . :journal)))

; The names the host creates, in order (host/native/io.lisp
; fnn-command-init-published).
(defun fn-bs-init-log-subdir-names ()
  (declare (xargs :guard t))
  (strip-cars *fn-bs-init-log-subdirs*))

; The segment's name is the log route's (books/store-log-route.lisp).
(defmacro fn-bs-init-log-segment-name () '(fn-olr-segment-name))

(defun fn-bs-init-log-files (config record-name record extent)
  (declare (xargs :guard t :verify-guards nil))
  (list (list* :stage "config.json" config)
        (list* :config record-name record)
        (list* :journal (fn-bs-init-log-segment-name) (fn-bs-zeros extent))))

(defun fn-bs-init-log-program (stage root config record-name record extent)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-init-pub-rename-cuts
   (fn-bs-imp-program stage root *fn-bs-init-log-subdirs*
                      (fn-bs-init-log-files config record-name record extent))))

; -----------------------------------------------------------------------------
; The program is the import's, its cuts renamed: a cut changes no state.

(local
 (defthm fn-bs-init-log-rename-cuts-step
   (equal (fn-bs-imp-step bs ks (fn-bs-init-pub-rename-step step) out groups capacity)
          (fn-bs-imp-step bs ks step out groups capacity))
   :hints (("Goal" :in-theory '(fn-bs-init-pub-rename-step fn-bs-imp-step fn-bs-step
                                car-cons (:e equal))))))

(local
 (defthm fn-bs-init-log-run-of-renamed-cuts
   (equal (fn-bs-imp-run bs ks (fn-bs-init-pub-rename-cuts steps) outs groups capacity)
          (fn-bs-imp-run bs ks steps outs groups capacity))
   :hints (("Goal" :induct (fn-bs-imp-run bs ks steps outs groups capacity)
            :in-theory '(fn-bs-imp-run fn-bs-init-pub-rename-cuts car-cons cdr-cons
                         fn-bs-init-log-rename-cuts-step
                         (:type-prescription fn-bs-init-pub-rename-cuts))))))

; -----------------------------------------------------------------------------
; The keystone.

(defthm fn-bs-init-log-program-crash-is-no-store-or-the-complete-empty-log
  (implies (and (fn-bs-imp-inputp bs stage root *fn-bs-init-log-subdirs*
                                  (fn-bs-init-log-files config record-name record extent)
                                  old)
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks
                                               (fn-bs-init-log-program stage root config
                                                                       record-name record extent)
                                               outs groups capacity)))
           (fn-bs-imp-no-store-or-completep
            (fn-bs-crash (car p) choices) root *fn-bs-init-log-subdirs*
            (fn-bs-init-log-files config record-name record extent)
            (fn-bs-next-ino bs) old))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-bs-init-log-program fn-bs-init-log-run-of-renamed-cuts)
           :use ((:instance fn-bs-imp-program-crash-is-no-store-or-the-complete-store
                            (subdirs *fn-bs-init-log-subdirs*)
                            (files (fn-bs-init-log-files config record-name record extent)))))))

(defthm fn-bs-init-log-classify-by-what-is-known
  (implies (and (fn-bs-imp-inputp bs stage root *fn-bs-init-log-subdirs*
                                  (fn-bs-init-log-files config record-name record extent)
                                  nil)
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks
                                               (fn-bs-init-log-program stage root config
                                                                       record-name record extent)
                                               outs groups capacity)))
           (let* ((img (fn-bs-crash (car p) choices))
                  (verdict (fn-bs-imp-classify (fn-bs-durable-entry img :parent stage)
                                               (fn-bs-durable-entry img :parent root))))
             (and (implies (member-equal verdict '(:no-store :not-published))
                           (null (fn-bs-durable-entry img :parent root)))
                  (implies (member-equal verdict '(:store-present :publication-uncertain))
                           (and (equal (fn-bs-durable-entry img :parent root) :stage)
                                (fn-bs-imp-completep img *fn-bs-init-log-subdirs*
                                                     (fn-bs-init-log-files config record-name
                                                                           record extent)
                                                     (fn-bs-next-ino bs)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(fn-bs-init-log-program fn-bs-init-log-run-of-renamed-cuts)
           :use ((:instance fn-bs-imp-classify-by-what-is-known
                            (subdirs *fn-bs-init-log-subdirs*)
                            (files (fn-bs-init-log-files config record-name record extent)))))))

; In the complete store the segment (the plan's third file, inode INO + 2)
; holds exactly EXTENT zeros.
(defthm fn-bs-init-log-complete-segment-is-zeros
  (implies (fn-bs-imp-completep img *fn-bs-init-log-subdirs*
                                (fn-bs-init-log-files config record-name record extent) ino)
           (and (equal (fn-bs-durable-entry img :journal (fn-bs-init-log-segment-name)) (+ 2 ino))
                (equal (fn-bs-durable-content img (+ 2 ino)) (fn-bs-zeros extent))))
  :hints (("Goal" :in-theory '(fn-bs-imp-completep fn-bs-imp-files-completep
                               fn-bs-init-log-files car-cons cdr-cons
                               (:e fn-bs-imp-subdirs-completep))
           :expand ((fn-bs-imp-files-completep img (fn-bs-init-log-files config record-name record extent) ino)))))

; The empty log: recovery's kernel of EXTENT zeros (the host's open,
; fn-lg-open-kernel = fn-lgt-recover) holds no record at frontier 0, and R's
; content conjuncts hold of it.
(local (defthm fn-bs-init-log-zerosp-zeros (fn-lg-zerosp (fn-bs-zeros n))))
(local (defthm fn-bs-init-log-zeros-len (equal (len (fn-bs-zeros n)) (nfix n))))
(local (defthm fn-bs-init-log-zeros-true-listp (true-listp (fn-bs-zeros n))))

(defthm fn-bs-init-log-segment-is-the-empty-log
  (implies (and (equal (mod extent unit) 0)
                (fn-frame-digestp genesis))
           (let ((ks (fn-lgt-recover (fn-bs-zeros extent) genesis unit max floor)))
             (and (equal (fn-lgk-committed ks) nil)
                  (equal (fn-lgk-frontier ks) 0)
                  (equal (fn-lgk-last ks) genesis)
                  (fn-lgk-content-okp (fn-bs-zeros extent) ks unit genesis max))))
  :hints (("Goal" :cases ((natp extent))
           :in-theory (e/d (fn-lgt-recover fn-lgk-recover fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-bs-zeros fn-lgt-next-after)))
          ("Subgoal 2" :expand ((fn-bs-zeros extent)))))
