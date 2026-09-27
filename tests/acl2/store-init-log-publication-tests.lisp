; Witnesses and teeth for books/store-init-log-publication.lisp (lane
; log-2): `operator init' of a format-9 store.  The crash keystone is
; books/store-import-publication.lisp's fn-bs-imp-program-crash-is-no-store-
; or-the-complete-store at this plan; its hypothesis-removal witnesses are
; that book's (tests/acl2/store-import-publication-tests.lisp).  Here: the
; plan and program are the import's with init's cuts, a whole run reaches
; the complete store whose segment is zeros, and the empty log's teeth.
(in-package "ACL2")
(include-book "../../books/store-init-log-publication")

(defun sil-bs () (declare (xargs :guard t))
  (fn-bs-make 4 nil (list (cons :parent nil)) nil 0))
(defun sil-files () (declare (xargs :guard t :verify-guards nil))
  (fn-bs-init-log-files '(1 2 3) "00000001.cfg" '(4 5) 16))
(defun sil-run () (declare (xargs :guard t :verify-guards nil))
  (fn-bs-imp-run (sil-bs) nil (fn-bs-init-log-program "store.init-x" "store" '(1 2 3)
                                                      "00000001.cfg" '(4 5) 16)
                 nil nil nil))

; The plan: three subdirectories, no transactions/, no frontier file.
(assert-event (equal (fn-bs-init-log-subdir-names) '("staging" "config" "journal")))
(assert-event (not (member-equal "allocation-frontier.json" (strip-cadrs (sil-files)))))
(assert-event (equal (cddr (third (sil-files))) (fn-bs-zeros 16)))
; Its cuts are init's names for the import program's, in order.
(assert-event
 (equal (fn-bs-init-log-program "s" "r" '(1) "c" '(2) 4)
        (fn-bs-init-pub-rename-cuts
         (fn-bs-imp-program "s" "r" *fn-bs-init-log-subdirs* (fn-bs-init-log-files '(1) "c" '(2) 4)))))
; The keystone's hypotheses hold of this reachable input, and the run ends
; in the complete store at ROOT with the segment's 16 zeros durable.
(assert-event (fn-bs-imp-inputp (sil-bs) "store.init-x" "store" *fn-bs-init-log-subdirs*
                                (sil-files) nil))
(assert-event
 (let ((final (car (car (last (sil-run))))))
   (and (equal (fn-bs-durable-entry final :parent "store") :stage)
        (fn-bs-imp-completep final *fn-bs-init-log-subdirs* (sil-files) 0)
        (equal (fn-bs-durable-content final 2) (fn-bs-zeros 16))
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
