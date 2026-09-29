; Literal positive witness for the imported crash keystone at the actual
; snapshot program coordinate; no artificial host SNAPSHOT fixture.
(in-package "ACL2")
(include-book "../../books/snapshot-publication")
(defun osdt-source () (declare (xargs :guard t))
  (fn-bs-make 4 nil (list (cons :parent nil)) nil 0))
(defun osdt-data () (declare (xargs :guard t))
  '((:stage "config.json" 1) (:config "00000001.cfg" 2)
    (:journal "000000.log" 3) (:journal "000001.log" 0 0)
    (:stage "checkpoint.bin" 4 5) (:keys "node.secret" 6)))
(defun osdt-run () (declare (xargs :guard t :verify-guards nil))
  (fn-bs-imp-run (osdt-source) nil
                 (fn-osd-program "target.snapshot-x" "target" (osdt-data) '(7 8))
                 nil nil nil))
(assert-event
 (and (fn-bs-imp-inputp (osdt-source) "target.snapshot-x" "target"
                        *fn-osd-subdirs* (fn-osd-files (osdt-data) '(7 8)) nil)
      (fn-bs-imp-outcomesp nil)
      (member-equal (car (last (osdt-run))) (osdt-run))
      (fn-bs-imp-no-store-or-completep
       (fn-bs-crash (car (car (last (osdt-run)))) nil)
       "target" *fn-osd-subdirs* (fn-osd-files (osdt-data) '(7 8))
       (fn-bs-next-ino (osdt-source)) nil)))
(assert-event
 (let ((img (fn-bs-crash (car (car (last (osdt-run)))) nil)))
   (and (equal (fn-bs-durable-entry img :parent "target") :stage)
        (fn-bs-imp-completep img *fn-osd-subdirs*
                             (fn-osd-files (osdt-data) '(7 8)) 0)
        (equal (fn-bs-durable-content
                img (fn-bs-durable-entry img :stage "SNAPSHOT")) '(7 8)))))
; Every observed cut of this nonempty positive run, not only its last cut.
(defun osdt-all-cuts-completep (run)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp run)
      (and (fn-bs-imp-no-store-or-completep
            (fn-bs-crash (car (car run)) nil) "target" *fn-osd-subdirs*
            (fn-osd-files (osdt-data) '(7 8)) 0 nil)
           (osdt-all-cuts-completep (cdr run)))
    t))
(assert-event (osdt-all-cuts-completep (osdt-run)))
