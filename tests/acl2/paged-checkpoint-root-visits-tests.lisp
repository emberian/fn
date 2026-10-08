(in-package "ACL2")
(include-book "../../books/paged-checkpoint-root-visits")
(include-book "paged-checkpoint-root-carried-tests")

(defun pckv-raw (roots ix rest s delta f plen)
  (declare (xargs :mode :program))
  (fn-pck-root-extend-carried-fold-visits roots ix rest s delta f plen))

; Every bound premise and the conclusion; K=2 must be charged even for
; this single article. The rooted model and raw execution agree above.
(assert-event
 (let* ((out (pckrc-raw *pckrc-roots* *pckc-ix* *pckc-rest* 2
                        *pckc-delta* nil 39))
        (k (fn-pck-configs-consumed (fn-sco-at 0 *pckrc-roots*) (caar out)))
        (visits (pckv-raw *pckrc-roots* *pckc-ix* *pckc-rest* 2
                          *pckc-delta* nil 39)))
   (and (fn-sco-pausedp (caar out))
        (equal k 2)
        (equal visits 16)
        (<= visits (+ 8 (* 4 (len *pckc-delta*)) (* 2 k))))))

; Omitting consumed configurations makes the claimed traversal bound false.
(must-fail-checked
 (assert-event
  (<= (pckv-raw *pckrc-roots* *pckc-ix* *pckc-rest* 2 *pckc-delta* nil 39)
      (+ 8 (* 4 (len *pckc-delta*))))))

(defun pckv-cei-walkerp (names)
  (if (consp names)
      (or (let ((s (symbol-name (car names))))
            (and (<= 7 (length s)) (equal (subseq s 0 7) "FN-CEI-")))
          (pckv-cei-walkerp (cdr names)))
    nil))

(assert-event
 (let* ((row (cdr (assoc-eq 'fn-pck-root-extend-carried
                            (table-alist 'fn-fold-visits (w state)))))
        (leaves (cadr row))
        (calls (sfi-t-exec-closure '(fn-pck-root-extend-carried) nil (w state))))
   (and (consp leaves)
        (not (pckv-cei-walkerp leaves))
        (not (intersection-eq '(fn-sco-extend fn-rii-sco-extend) leaves))
        (not (pckv-cei-walkerp calls))
        (not (intersection-eq '(fn-sco-extend fn-rii-sco-extend
                                fn-cnode-statep fn-rii-ix-of fn-sco-drop) calls))
        ; Per-event semantics are named, not claimed to have constant cost.
        (member-eq 'fn-rii-cpr-apply-event leaves)
        (member-eq 'fn-replay-identity-step leaves)
        (member-eq 'fn-cpe-projection-step leaves)
        (member-eq 'fn-th-prefix-step leaves))))
