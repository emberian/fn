; Controller metadata in the SAME native GET/SET/spine units as consume-work.
; The prepared SAME-arm-emitter gate checks actual row bindings/flush/cases.
; This source accounting does not establish physical/extraction refinement.
(in-package "ACL2")
(include-book "checkpoint-directory-consume-work")
(include-book "checkpoint-live-finish")
(include-book "machine-arms")
(fn2-book-layer :c)
; Data callbacks consume bytes; the scheduler BUDGET scalar is descriptor credit.
(defconst *fn2-checkpoint-master-pure-byte-quantum* *fn2-commit-unit-bytes*)
; machines-a-access: idp GETs the core directory then its ROWS; checked kind
; and slot readers repeat idp then GET the directory and one native column.
(defconst *fn2-master-id-check-steps* (+ 1 1))
(defconst *fn2-master-index-read-steps* (+ *fn2-master-id-check-steps* 1 1))
; machines.lisp FIELD-EVENTS :code: idp, slot, kind, selected kind GET/ROWS.
(defconst *fn2-master-phase-code-steps*
 (+ *fn2-master-id-check-steps* (* 2 *fn2-master-index-read-steps*) 1 1))
; SNAPSHOT-EVENTS adds the checked kind read. Each generated kind ROW reader
; repeats snapshot, checked slot and kind table/native column GETs.
(defconst *fn2-master-snapshot-steps* (+ *fn2-master-phase-code-steps* *fn2-master-index-read-steps*))
(defconst *fn2-master-row-read-steps* (+ *fn2-master-snapshot-steps* *fn2-master-index-read-steps* 1 1))
; CORE-PUT-EXPANSION: idp, kind, slot, kind GET/ROWS, native SET/core store.
(defconst *fn2-master-phase-write-steps*
 (+ *fn2-master-id-check-steps* (* 2 *fn2-master-index-read-steps*) 1 1 1 1))
(defun fn2-master-controller-steps (reads cases)
 (declare (xargs :guard (and (natp reads) (natp cases))))
 (+ *fn2-master-snapshot-steps* (* reads *fn2-master-row-read-steps*)
    *fn2-master-phase-write-steps* (* cases (+ 1 1))))
; One literal case has one probe plus end. Branch alternatives use MAX,
; not the sum of mutually exclusive phase writes. Consume reads two columns:
; row-token and row-generation; its other two scalar actuals are constant/id.
(defconst *fn2-master-one-case-controller-steps* (fn2-master-controller-steps 0 1))
(defconst *fn2-master-two-case-controller-steps* (fn2-master-controller-steps 0 2))
(defconst *fn2-master-three-case-controller-steps* (fn2-master-controller-steps 0 3))
(defconst *fn2-master-consume-controller-steps* (fn2-master-controller-steps 2 1))
(defconst *fn2-master-consume-turn-steps* (+ *fn2-directory-rebase-consume-steps* *fn2-master-consume-controller-steps*))
; Bind the actual declared faces through the SAME operation registry. New
; provider accounting therefore flows into this kind without numeric copies.
; These declarations remain distinct from physical/extraction qualification.
(make-event
 (let* ((finish (fn2-arms-op-row 'fn2-checkpoint-live-replace-finish-op (w state)))
        (reopen (fn2-arms-op-row 'fn2-checkpoint-live-replace-reopen-op (w state)))
        (fs (cadr (fn2-cost-values finish (w state))))
        (rs (cadr (fn2-cost-values reopen (w state)))))
  (if (and finish reopen (posp fs) (posp rs))
   (value `(progn (defconst *fn2-master-finish-face-steps* ,fs)
                  (defconst *fn2-master-reopen-face-steps* ,rs)))
   (er soft 'checkpoint-master-work "Actual typed face cost declarations are missing."))))
(defconst *fn2-master-promote-turn-steps* (+ *fn2-master-finish-face-steps* *fn2-master-two-case-controller-steps*))
(defconst *fn2-master-reopen-turn-steps* (+ *fn2-master-reopen-face-steps* *fn2-master-one-case-controller-steps*))
(defconst *fn2-master-live-one-turn-steps* (+ *fn2-work-stage* *fn2-master-one-case-controller-steps*))
(defconst *fn2-master-live-two-turn-steps* (+ *fn2-work-stage* *fn2-master-two-case-controller-steps*))
(defconst *fn2-master-live-three-turn-steps* (+ *fn2-work-stage* *fn2-master-three-case-controller-steps*))
