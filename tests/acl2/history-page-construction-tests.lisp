(in-package "ACL2")
(include-book "../../books/history-page-construction-frame")

; MODEL storage construction only; no source issuer/allowance authority.
(defun-nx fn-hpct2-run (fn-hep-node)
 (declare (xargs :stobjs fn-hep-node :guard t :verify-guards nil))
 (mv-let (zero zero-left fn-hep-node) (fn-hpc-node-one 0 0 1 1 0 0 8 fn-hep-node)
 (declare (ignore zero-left))
 (mv-let (append fn-hep-node) (fn-hep-node-append 0 0 1 1 0 0 0 :old-row fn-hep-node)
 (mv-let (one-a one-a-left fn-hep-node) (fn-hpc-node-one 1 1 1 2 0 256 8 fn-hep-node)
 (declare (ignore one-a-left))
 (mv-let (one-b one-b-left fn-hep-node) (fn-hpc-node-one 1 1 1 2 0 256 8 fn-hep-node)
 (declare (ignore one-b-left))
 (mv-let (two-a two-a-left fn-hep-node) (fn-hpc-node-one 2 2 1 3 0 512 8 fn-hep-node)
 (declare (ignore two-a-left))
 (mv-let (two-b two-b-left fn-hep-node) (fn-hpc-node-one 2 2 1 3 0 512 8 fn-hep-node)
 (declare (ignore two-b-left))
 (mv-let (two-c two-c-left fn-hep-node) (fn-hpc-node-one 2 2 1 3 0 512 8 fn-hep-node)
 (declare (ignore two-c-left))
 (mv-let (three-a three-a-left fn-hep-node) (fn-hpc-node-one 3 2 1 4 0 768 8 fn-hep-node)
 (declare (ignore three-a-left))
 (mv-let (three-b three-b-left fn-hep-node) (fn-hpc-node-one 3 2 1 4 0 768 8 fn-hep-node)
 (declare (ignore three-b-left))
 (mv-let (duplicate duplicate-left fn-hep-node) (fn-hpc-node-one 1 1 1 2 0 256 8 fn-hep-node)
 (declare (ignore duplicate-left))
 (mv-let (foreign foreign-left fn-hep-node) (fn-hpc-node-one 1 1 1 99 0 256 8 fn-hep-node)
 (declare (ignore foreign-left))
 (mv-let (occupied occupied-left fn-hep-node) (fn-hpc-node-one 0 0 1 1 0 0 8 fn-hep-node)
 (declare (ignore occupied-left))
 (mv-let (word row left) (fn-hep-node-read 0 0 1 1 0 0 0 1 8 fn-hep-node)
 (mv (list zero append one-a one-b two-a two-b two-c three-a three-b duplicate foreign occupied word row left) fn-hep-node)))))))))))))))
(defun-nx fn-hpct2-model ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hep-node
  (mv-let (data fn-hep-node) (fn-hpct2-run fn-hep-node) data)))
(defthm fn-hpct2-prefix-pages-retain-old-row-model
 (equal (fn-hpct2-model)
  '(:page-ready :appended :constructed :page-ready :constructed :constructed
    :page-ready :constructed :page-ready :page-ready :stale :stale
    :row :old-row 7))
 :hints (("Goal" :in-theory (enable fn-hpct2-model fn-hpct2-run))))


; Logical MODEL storage only: real constructor/read effects, synthetic stamps.
(defun-nx fn-hpcf-frame-model (occupied fn-hep-node)
 (declare (xargs :stobjs fn-hep-node :verify-guards nil))
 (mv-let (word left fn-hep-node) (fn-hpc-node-one 0 0 1 1 0 0 8 fn-hep-node)
 (declare (ignore word left))
 (mv-let (word fn-hep-node)
  (if occupied (fn-hep-node-append 0 0 1 1 0 0 0 :old-row fn-hep-node)
    (mv :no-row fn-hep-node))
 (declare (ignore word))
 (let ((before (fn-hep-node-read 0 0 1 1 0 0 0 1 8 fn-hep-node)))
 (mv-let (word left fn-hep-node)
  (fn-hpc-node-one (if occupied 1 0) (if occupied 1 0) 1 2 0 256 8 fn-hep-node)
 (declare (ignore word left))
 (let ((after (fn-hep-node-read 0 0 1 1 0 0 0 1 8 fn-hep-node)))
 (mv (list (and (natp (if occupied 1 0)) (natp (if occupied 1 0))
                (posp 1) (posp 2) (natp 0) (natp 256) (natp 8)
                (natp 0) (natp 0) (natp 0) (natp 0) (natp 1) (natp 8))
           (eq (car before) :row) (equal after before)) fn-hep-node)))))))
(defun-nx fn-hpcf-positive ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hep-node
  (mv-let (facts fn-hep-node) (fn-hpcf-frame-model t fn-hep-node) facts)))
(defthm fn-hpcf-complete-frame-positive-model
 (equal (fn-hpcf-positive) '(t t t))
 :hints (("Goal" :in-theory (enable fn-hpcf-positive fn-hpcf-frame-model))))


; Premise removal MODEL: virgin page, not an issued old source/read witness.
(defun-nx fn-hpcf-unpublished-model (fn-hep-node)
 (declare (xargs :stobjs fn-hep-node :verify-guards nil))
 (let ((before (fn-hep-node-read 0 0 1 2 0 256 256 1 8 fn-hep-node)))
 (mv-let (word left fn-hep-node) (fn-hpc-node-one 0 0 1 2 0 256 8 fn-hep-node)
 (declare (ignore word left))
 (let ((after (fn-hep-node-read 0 0 1 2 0 256 256 1 8 fn-hep-node)))
 (mv (list (and (natp 0) (natp 0) (posp 1) (posp 2) (natp 0) (natp 256)
                (natp 8) (natp 0) (natp 0) (natp 256) (natp 256) (natp 1) (natp 8))
           (not (eq (car before) :row)) (not (equal after before))) fn-hep-node)))))
(defun-nx fn-hpcf-unpublished ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hep-node
  (mv-let (facts fn-hep-node) (fn-hpcf-unpublished-model fn-hep-node) facts)))
(defthm fn-hpcf-old-row-premise-removal-model
 (equal (fn-hpcf-unpublished) '(t t t))
 :hints (("Goal" :in-theory (enable fn-hpcf-unpublished fn-hpcf-unpublished-model))))

