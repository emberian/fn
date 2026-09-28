; Witnesses and teeth for books/store-init-log-publication.lisp (lane
; log-2): `operator init' of a format-9 store.  The crash keystone is
; books/store-import-publication.lisp's fn-bs-imp-program-crash-is-no-store-
; or-the-complete-store at this plan; its hypothesis-removal witnesses are
; that book's (tests/acl2/store-import-publication-tests.lisp).  Here: the
; plan and program are the import's with init's cuts, a whole run reaches
; the complete store whose segment is zeros, and the empty log's teeth.
(in-package "ACL2")
(include-book "../../books/store-init-log-publication")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

(defun sil-bs () (declare (xargs :guard t))
  (fn-bs-make 4 nil (list (cons :parent nil)) nil 0))
(defun sil-files () (declare (xargs :guard t :verify-guards nil))
  (fn-bs-init-log-files '(1 2 3) "00000001.cfg" '(4 5) 16 '(6 7)))
(defun sil-run () (declare (xargs :guard t :verify-guards nil))
  (fn-bs-imp-run (sil-bs) nil (fn-bs-init-log-program "store.init-x" "store" '(1 2 3)
                                                      "00000001.cfg" '(4 5) 16 '(6 7))
                 nil nil nil))

; The plan: three subdirectories, no transactions/, no frontier file; the
; genesis before the segment.
(assert-event (equal (fn-bs-init-log-subdir-names) '("staging" "config" "journal")))
(assert-event (not (member-equal "allocation-frontier.json" (strip-cadrs (sil-files)))))
(assert-event (equal (cddr (third (sil-files))) '(6 7)))
(assert-event (equal (cadr (third (sil-files))) "000000.log"))
(assert-event (equal (cddr (fourth (sil-files))) (fn-bs-zeros 16)))
; Its cuts are init's names for the import program's, in order.
(assert-event
 (equal (fn-bs-init-log-program "s" "r" '(1) "c" '(2) 4 '(3))
        (fn-bs-init-pub-rename-cuts
         (fn-bs-imp-program "s" "r" *fn-bs-init-log-subdirs* (fn-bs-init-log-files '(1) "c" '(2) 4 '(3))))))
; The keystone's hypotheses hold of this reachable input, and the run ends
; in the complete store at ROOT with the segment's 16 zeros durable.
(assert-event (fn-bs-imp-inputp (sil-bs) "store.init-x" "store" *fn-bs-init-log-subdirs*
                                (sil-files) nil))
(assert-event
 (let ((final (car (car (last (sil-run))))))
   (and (equal (fn-bs-durable-entry final :parent "store") :stage)
        (fn-bs-imp-completep final *fn-bs-init-log-subdirs* (sil-files) 0)
        (equal (fn-bs-durable-content final 2) '(6 7))
        (equal (fn-bs-durable-content final 3) (fn-bs-zeros 16))
        (fn-bs-imp-no-store-or-completep (fn-bs-crash final nil) "store"
                                         *fn-bs-init-log-subdirs* (sil-files) 0 nil))))
; A crash before the rename: no store at ROOT (the first state of the run).
(assert-event
 (let ((first (car (car (sil-run)))))
   (and (null (fn-bs-durable-entry (fn-bs-crash first nil) :parent "store"))
        (fn-bs-imp-no-store-or-completep (fn-bs-crash first nil) "store"
                                         *fn-bs-init-log-subdirs* (sil-files) 0 nil))))

; fn-bs-init-log-segment-is-the-empty-log: witness at unit 4096, 1 MiB.
(assert-event
 (let ((ks (fn-lgt-recover (fn-bs-zeros 64) *fn-lg-genesis* 4 4096 1)))
   (and (null (fn-lgk-committed ks)) (equal (fn-lgk-frontier ks) 0)
        (fn-lgk-content-okp (fn-bs-zeros 64) ks 4 *fn-lg-genesis* 4096))))
; Tooth (whole units): 6 zeros at unit 4 is not a segment R relates.
(assert-event
 (and (not (equal (mod 6 4) 0)) (fn-frame-digestp *fn-lg-genesis*)
      (not (fn-lgk-content-okp (fn-bs-zeros 6)
                               (fn-lgt-recover (fn-bs-zeros 6) *fn-lg-genesis* 4 4096 1)
                               4 *fn-lg-genesis* 4096))))
; Tooth (a chain head): with no digest as genesis the kernel's head is none.
(assert-event
 (and (equal (mod 64 4) 0) (not (fn-frame-digestp nil))
      (not (fn-lgk-content-okp (fn-bs-zeros 64)
                               (fn-lgt-recover (fn-bs-zeros 64) nil 4 4096 1)
                               4 nil 4096))))

; -----------------------------------------------------------------------------
; fn-bs-init-log-classify-by-what-is-known (PRF-268; audit packet G4-4, lane
; audit-fixes): init's own run classified.  The conclusion for one state P of
; the run and crash CHOICES, verbatim, with the store's next inode INO.
(defun sil-classify-concl (p choices ino)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((img (fn-bs-crash (car p) choices))
         (verdict (fn-bs-imp-classify (fn-bs-durable-entry img :parent "store.init-x")
                                      (fn-bs-durable-entry img :parent "store"))))
    (and (implies (member-equal verdict '(:no-store :not-published))
                  (null (fn-bs-durable-entry img :parent "store")))
         (implies (member-equal verdict '(:store-present :publication-uncertain))
                  (and (equal (fn-bs-durable-entry img :parent "store") :stage)
                       (fn-bs-imp-completep img *fn-bs-init-log-subdirs* (sil-files) ino))))))
(defun sil-all-concl (ps ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ps) (and (sil-classify-concl (car ps) nil ino) (sil-all-concl (cdr ps) ino)) t))
(defun sil-verdict (p)
  (declare (xargs :guard t :verify-guards nil))
  (let ((img (fn-bs-crash (car p) nil)))
    (fn-bs-imp-classify (fn-bs-durable-entry img :parent "store.init-x")
                        (fn-bs-durable-entry img :parent "store"))))
(defun sil-run-outs (bs outs) (declare (xargs :guard t :verify-guards nil))
  (fn-bs-imp-run bs nil (fn-bs-init-log-program "store.init-x" "store" '(1 2 3)
                                                "00000001.cfg" '(4 5) 16 '(6 7))
                 outs nil nil))
; Positive: the input and the outcomes hold; the first state's crash image
; is :no-store with no ROOT entry, the final state's is :store-present with
; ROOT = the stage and the store complete; the conclusion holds at every
; state of the run (the member hypothesis).
(assert-event
 (let ((ps (sil-run)))
   (and (fn-bs-imp-inputp (sil-bs) "store.init-x" "store" *fn-bs-init-log-subdirs* (sil-files) nil)
        (fn-bs-imp-outcomesp nil)
        (equal (sil-verdict (car ps)) :no-store)
        (null (fn-bs-durable-entry (fn-bs-crash (car (car ps)) nil) :parent "store"))
        (equal (sil-verdict (car (last ps))) :store-present)
        (equal (fn-bs-durable-entry (fn-bs-crash (car (car (last ps))) nil) :parent "store") :stage)
        (fn-bs-imp-completep (fn-bs-crash (car (car (last ps))) nil) *fn-bs-init-log-subdirs*
                             (sil-files) 0)
        (sil-all-concl ps 0))))
; Removal of the input hypothesis: ROOT already names inode 5 before init
; runs.  The outcomes hold; the first state's image classifies
; :store-present, but ROOT is not the stage.
(assert-event
 (let* ((bs (fn-bs-make 4 (list (cons 5 nil)) (list (cons :parent (list (cons "store" 5)))) nil 6))
        (ps (sil-run-outs bs nil)))
   (and (not (fn-bs-imp-inputp bs "store.init-x" "store" *fn-bs-init-log-subdirs* (sil-files) nil))
        (fn-bs-imp-outcomesp nil)
        (equal (sil-verdict (car ps)) :store-present)
        (not (sil-classify-concl (car ps) nil (fn-bs-next-ino bs))))))
; (fn-bs-imp-outcomesp outs): no removal witness is constructible here.  The
; run reads any value but :ok as a failed syscall, so a non-outcome behaves
; as some failure outcome; the classification reads only the durable
; entries.  Evaluated: a run with (:ok 1) (not an outcome) and one with a
; bare symbol; the conclusion holds at every state of both.
(assert-event
 (and (not (fn-bs-imp-outcomesp (list :ok (list :ok 1) :ok)))
      (sil-all-concl (sil-run-outs (sil-bs) (list :ok (list :ok 1) :ok)) 0)
      (not (fn-bs-imp-outcomesp '(bad)))
      (sil-all-concl (sil-run-outs (sil-bs) '(bad bad bad bad)) 0)))
