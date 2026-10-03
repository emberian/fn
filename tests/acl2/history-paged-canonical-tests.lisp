; Exact canonical attachment order and normal exported execution.
(in-package "ACL2")
(include-book "../../books/history-paged-attach")

(defconst *hpct-held*
  (fn-held-make 0 1 0 "<canonical@fn>" 0 '("fn.test") "o" "s" "e" 1 5
    (fn-hf-make 100 14 2 nil)
    (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))
(defconst *hpct-events* (list '(:origin "exact") *hpct-held* '(:receipt 8) *hpct-held*))
(defun hpct-ats (ordinal n fn-hist)
  (declare (xargs :stobjs fn-hist :guard (and (natp ordinal) (natp n) (<= n (fn-hist-count fn-hist)))
                  :measure (nfix (- n ordinal))))
  (if (and (natp ordinal) (natp n) (< ordinal n)) (cons (fn-hist-at ordinal fn-hist) (hpct-ats (+ ordinal 1) n fn-hist)) nil))
(defun hpct-actual (fn-hist)
  (declare (xargs :stobjs fn-hist))
  (let* ((fn-hist (fn-hist-load *hpct-events* 17 fn-hist))
         (before (list (fn-hist-count fn-hist) (hpct-ats 0 (fn-hist-count fn-hist) fn-hist)
                       (fn-hist-msgid-records "<canonical@fn>" fn-hist)))
         (fn-hist (fn-hist-append '(:tail :ordinary-append) fn-hist))
         (after (list (fn-hist-count fn-hist) (fn-hist-at 4 fn-hist)))
         (fn-hist (fn-hist-clear 19 fn-hist)))
    (mv (and (equal before (list 4 *hpct-events* (list *hpct-held* *hpct-held*)))
             (equal after '(5 (:tail :ordinary-append)))
             (equal (fn-hist-count fn-hist) 0)
             (equal (fn-hist-msgid-records "<canonical@fn>" fn-hist) nil)) fn-hist)))
(assert-event
 (mv-let (ok fn-hist) (hpct-actual fn-hist) (mv ok fn-hist))
 :stobjs-out '(nil fn-hist))
