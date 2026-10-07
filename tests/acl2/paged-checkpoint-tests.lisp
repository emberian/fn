; Premises inhabited and teeth for books/paged-checkpoint.lisp (the
; keystones fn-pck-dirty-is-the-delta, fn-pck-dirty-bound,
; fn-pck-open-after-commit-is-full-recover, fn-pck-crash-recovers-from-old-or-new).
;
; Each tooth is a must-fail AND a concrete witness that its claim is false for
; the right reason, so a stale or untranslatable body cannot pass for a tooth:
;   1. the premises (fn-pck-recordsp, fn-pck-root-fitsp) hold of a nonempty
;      record list with a wide record, executed;
;   2. a dirty set that forgets the root region is not the delta (the root
;      changes with the records);
;   3. a bound of K (the root pages alone) is false: a wide delta takes more;
;   4. a log compacted past the old checkpoint's S cannot reach the records
;      the old slot lacks.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *pckt-wide* (make-list 20000 :initial-element 7))
(defconst *pckt-prefix* (list '(1 2) "x"))
(defconst *pckt-delta* (list *pckt-wide* *pckt-wide* *pckt-wide*))

; 1. Premises.
(assert-event (and (fn-pck-recordsp nil (append *pckt-prefix* *pckt-delta*))
                   (fn-pck-root-fitsp nil (append *pckt-prefix* *pckt-delta*))
                   (fn-pck-recordsp nil *pckt-prefix*)
                   (fn-pck-root-fitsp nil *pckt-prefix*)))

; The image reads back as the records (the capture decodes, event index included).
(assert-event (equal (fn-pck-capture-of-pages (fn-pck-pages nil (append *pckt-prefix* *pckt-delta*)))
                     (fn-sco-capture nil (append *pckt-prefix* *pckt-delta*))))

; The dirty set applies to the old image and yields the new one.
(assert-event (equal (pgs-apply-dirty (fn-pck-pages nil *pckt-prefix*)
                                      (fn-pck-dirty nil *pckt-prefix* *pckt-delta*))
                     (fn-pck-pages nil (append *pckt-prefix* *pckt-delta*))))

; 2. A dirty set without the root region.
(defun pckt-bad-dirty (configs prefix delta)
  (declare (xargs :verify-guards nil) (ignore configs))
  (pck-shift *fn-pck-root-pages*
             (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows delta))))

(must-fail-checked
 (defthm pckt-bad-dirty-is-the-delta
   (implies (and (true-listp prefix) (true-listp delta)
                 (fn-pck-sccb-listp (append prefix delta)))
            (equal (pgs-apply-dirty (fn-pck-pages configs prefix) (pckt-bad-dirty configs prefix delta))
                   (fn-pck-pages configs (append prefix delta))))))

(assert-event (not (equal (pgs-apply-dirty (fn-pck-pages nil nil) (pckt-bad-dirty nil nil '((1 2))))
                          (fn-pck-pages nil '((1 2))))))

; 3. A bound of the root pages alone.
(must-fail-checked
 (defthm pckt-bound-root-only
   (<= (len (fn-pck-dirty configs prefix delta)) *fn-pck-root-pages*)))

(assert-event (< *fn-pck-root-pages* (len (fn-pck-dirty nil nil *pckt-delta*))))

; The real bound at the witness, and no term in the prefix: the same delta
; after a long prefix needs the same number of pages or one more.
(assert-event (<= (len (fn-pck-dirty nil *pckt-prefix* *pckt-delta*))
                  (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckt-delta*))))
(assert-event (<= (len (fn-pck-dirty nil (make-list 3000 :initial-element '(1 2)) *pckt-delta*))
                  (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckt-delta*))))

; 4. A log compacted past the old checkpoint's S.
(must-fail-checked
 (defthm pckt-crash-compacted-log
   (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                 (fn-pck-recordsp configs (append prefix delta))
                 (fn-pck-recordsp configs prefix)
                 (fn-pck-root-fitsp configs (append prefix delta))
                 (fn-pck-root-fitsp configs prefix)
                 (fn-pck-log-retains log (+ (len prefix) (len delta)))
                 (equal (nthcdr (car log) (append prefix delta suffix)) (cdr log))
                 (equal v (list t0 (fn-pck-pages configs prefix))))
            (equal (fn-pck-recover-view v log configs frontier max-conns)
                   (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns)))))

; The witness: opening the old checkpoint (S = 2) with a log that starts at 5
; replays no record of the delta, so the recovered records lack them.
(defconst *pckt-log* (cons 5 '(5 6)))
(assert-event
 (let* ((c (fn-pck-capture-of-pages (fn-pck-pages nil *pckt-prefix*)))
        (e (fn-sco-extend c nil (nthcdr (nfix (- (len (fn-sco-records c)) (nfix (car *pckt-log*)))) (cdr *pckt-log*)))))
   (and (equal (fn-sco-records e) (append *pckt-prefix* '(5 6)))
        (not (equal (fn-sco-records e) (append *pckt-prefix* '(a b c) '(5 6)))))))
