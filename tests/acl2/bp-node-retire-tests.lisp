; Teeth of books/bp-node-retire.lisp (N16 housekeeping, PKT-059).
(in-package "ACL2")
(include-book "../../books/bp-node-retire")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

;; A journal root after generation 2 was selected: generation 0
;; ("lifecycle") and 1 with rows, generation 2 (selected) with one row, a
;; killed rotation's stage, the lock and the sequence file.  The selection
;; file is a real checkpoint file (a zero-argument function: its trailer
;; calls the attached digest, which a defconst does not see).
(defconst *bpret-budget* (fn-bpnr-depth-budget 8))
(defun bpret-ck () (fn-bpnr-checkpoint 2 nil nil '(4 . 0) 0 0))
(defun bpret-selection () (fn-bpnr-checkpoint-octets (bpret-ck) *bpret-budget*))
(defun bpret-tree ()
  (list (cons "lifecycle" (list :dir (cons "a" '(:file 1)) (cons "b" '(:file 2))))
        (cons (fn-bpnr-generation-directory 1) (list :dir (cons "c" '(:file 3))))
        (cons (fn-bpnr-generation-directory 2) (list :dir (cons "d" '(:file 4))))
        (cons ".bp-generation-77-abcdef012345" (cons :file (bpret-selection)))
        (cons "bp-generation.fnb" (cons :file (bpret-selection)))
        (cons "lifecycle.lock" '(:file))
        (cons "sequence" '(:file 9))))
(defun bpret-names () (strip-cars (bpret-tree)))
(defun bpret-listings ()
  (list (cons "lifecycle" '("a" "b"))
        (cons (fn-bpnr-generation-directory 1) '("c"))))
(defun bpret-ops (selected) (fn-bpnr-retire-ops (bpret-names) (bpret-listings) selected))
(defconst *bpret-extra* '("lifecycle.lock" "sequence"))
(defun bpret-view (k selected)
  (fn-bpnr-open-view (fn-bpnr-apply-ops (bpret-tree) (take k (bpret-ops selected)))
                     *bpret-extra* *bpret-budget*))
(defun bpret-all-cuts-keep (k selected)
  (declare (xargs :mode :program))
  (if (zp k)
      (equal (bpret-view 0 selected) (bpret-view 0 selected))
    (and (equal (bpret-view k selected)
                (fn-bpnr-open-view (bpret-tree) *bpret-extra* *bpret-budget*))
         (bpret-all-cuts-keep (1- k) selected))))

;; Witness: the names, the program, and every cut of it.
(assert-event
 (and (consp (bpret-selection))
      (equal (fn-bpnr-plan-generation (fn-bpnr-tree-plan (bpret-tree) *bpret-budget*)) 2)
      (equal (fn-bpnr-retired-names (bpret-names) 2)
             (list "lifecycle" (fn-bpnr-generation-directory 1)
                   ".bp-generation-77-abcdef012345"))
      (equal (bpret-ops 2)
             (list '(:unlink-in "lifecycle" "a") '(:unlink-in "lifecycle" "b")
                   '(:rmdir "lifecycle")
                   (list :unlink-in (fn-bpnr-generation-directory 1) "c")
                   (list :rmdir (fn-bpnr-generation-directory 1))
                   '(:unlink ".bp-generation-77-abcdef012345")
                   '(:barrier)))
      ;; After the whole program only the selected generation, the
      ;; selection file, the lock and the sequence file remain.
      (equal (strip-cars (fn-bpnr-apply-ops (bpret-tree) (bpret-ops 2)))
             (list (fn-bpnr-generation-directory 2) "bp-generation.fnb"
                   "lifecycle.lock" "sequence"))
      ;; Every cut, including the partial removal of "lifecycle" after one
      ;; file, and cuts past the end, keeps the open's view.
      (equal (fn-bpnr-tree-entry "lifecycle"
                                 (fn-bpnr-apply-ops (bpret-tree) (take 1 (bpret-ops 2))))
             (list :dir (cons "b" '(:file 2))))
      (bpret-all-cuts-keep 9 2)
      ;; Nothing is retired before any selection.
      (null (fn-bpnr-retired-names (bpret-names) 0))))

;; Without "the selection file selects SELECTED": run the program for 3
;; while the file selects 2; generation 2's directory is retired and the
;; open's view loses it.
(assert-event
 (member-equal (fn-bpnr-generation-directory 2) (fn-bpnr-retired-names (bpret-names) 3)))
(must-fail
 (assert-event (bpret-all-cuts-keep 9 3)))
;; Without "no other name the open reads is retired": if the open read
;; "lifecycle" (the legacy generation), the program changes it.
(must-fail
 (assert-event
  (equal (fn-bpnr-open-view (fn-bpnr-apply-ops (bpret-tree) (take 3 (bpret-ops 2)))
                            '("lifecycle") *bpret-budget*)
         (fn-bpnr-open-view (bpret-tree) '("lifecycle") *bpret-budget*))))
