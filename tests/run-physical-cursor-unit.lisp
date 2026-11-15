; Prepared source-projection control. The installed row is SYNTHETIC: this
; does not claim catalog adoption, page authentication, I/O, or durability.
(in-package "ACL2")
(include-book "../books/runs")
(defun fn2-run-physical-cursor-ref-unit (fn2-run-installed fn2-run-cursors fn2-run-paths)
 (declare (xargs :stobjs (fn2-run-installed fn2-run-cursors fn2-run-paths) :verify-guards nil))
 (b* ((fn2-run-installed (fn2-run-installed-init 1 fn2-run-installed))
      (fn2-run-cursors (fn2-run-cursors-init 1 fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init *fn2-run-max-levels* fn2-run-paths))
      ((mv code fn2-run-installed) (fn2-run-install-physical 0 2 11 9 1 4 32 3 7 17
       11 22 33 44 55 66 77 88 fn2-run-installed))
      ((mv rootcode fn2-run-cursors) (fn2-run-cursor-start-installed 0 0 0 4 5 6 fn2-run-installed fn2-run-cursors))
      (root-ok (and (eq code :ok) (eq rootcode :ok)
       (equal (fn2-run-cursors-phase 0 fn2-run-cursors) *fn2-run-cursor-phase-miss*)
       (equal (fn2-run-cursors-slot 0 fn2-run-cursors) *fn2-none*)
       (equal (fn2-run-cursors-source-row 0 fn2-run-cursors) 0)
       (equal (fn2-run-cursors-catalog-tag 0 fn2-run-cursors) 17)
       (equal (fn2-run-cursors-epoch 0 fn2-run-cursors) 3)
       (equal (fn2-run-cursors-run 0 fn2-run-cursors) 9)
       (equal (fn2-run-cursors-priority 0 fn2-run-cursors) 11)
       (equal (fn2-run-installed-physical-count fn2-run-installed) 1)
       (equal (fn2-run-cursors-okind 0 fn2-run-cursors) 4)
       (equal (fn2-run-cursors-oslot 0 fn2-run-cursors) 5)
       (equal (fn2-run-cursors-ogen 0 fn2-run-cursors) 6)))
      ((mv note fn2-run-paths) (fn2-run-path-physical-note 0 1 fn2-run-cursors fn2-run-paths))
      ; The one page buffer will later be overwritten by a child. Saving the
      ; parent digest/epoch is independent of that buffer's current contents.
      (fn2-run-cursors (fn2-run-cursors-put 0 (epoch 99) (hash-0 0) (hash-1 0) (hash-2 0) (hash-3 0)
       (hash-4 0) (hash-5 0) (hash-6 0) (hash-7 0)))
      ((mv back fn2-run-cursors) (fn2-run-cursor-parent-ref 0 1 fn2-run-cursors fn2-run-paths))
      (good (and root-ok (eq note :ok) (eq back :ok)
       (equal (fn2-run-cursors-epoch 0 fn2-run-cursors) 3)
       (equal (fn2-run-cursors-resume-child 0 fn2-run-cursors) 1)
       (equal (fn2-run-cursor-hash-word 0 0 fn2-run-cursors) 11)
       (equal (fn2-run-cursor-hash-word 0 1 fn2-run-cursors) 22)
       (equal (fn2-run-cursor-hash-word 0 2 fn2-run-cursors) 33)
       (equal (fn2-run-cursor-hash-word 0 3 fn2-run-cursors) 44)
       (equal (fn2-run-cursor-hash-word 0 4 fn2-run-cursors) 55)
       (equal (fn2-run-cursor-hash-word 0 5 fn2-run-cursors) 66)
       (equal (fn2-run-cursor-hash-word 0 6 fn2-run-cursors) 77)
       (equal (fn2-run-cursor-hash-word 0 7 fn2-run-cursors) 88))))
  (mv good fn2-run-installed fn2-run-cursors fn2-run-paths)))
(assert-event
 (with-local-stobj fn2-run-installed
  (with-local-stobj fn2-run-cursors
   (with-local-stobj fn2-run-paths
    (mv-let (good fn2-run-installed fn2-run-cursors fn2-run-paths)
     (fn2-run-physical-cursor-ref-unit fn2-run-installed fn2-run-cursors fn2-run-paths)
     good)))))
