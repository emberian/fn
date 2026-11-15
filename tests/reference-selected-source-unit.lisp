; Source-binding controls only. These do not certify a served callback,
; full-R square, or the host's execution of an attachment map.
(in-package "ACL2")
(include-book "../books/reference-selected-source")
(include-book "std/testing/must-fail" :dir :system)

(encapsulate (((fn2-rss-hook *) => *) ((fn2-rss-other-hook *) => *))
 (local (defun fn2-rss-hook (x) (declare (ignore x)) 0))
 (local (defun fn2-rss-other-hook (x) (declare (ignore x)) 0))
 (defthm fn2-rss-hook-natural (natp (fn2-rss-hook x)))
 (defthm fn2-rss-other-hook-natural (natp (fn2-rss-other-hook x))))

(defun fn2-rss-helper (x) (declare (xargs :guard t)) (nfix x))
(defun fn2-rss-first (x) (declare (xargs :guard t)) (fn2-rss-helper x))
(defun fn2-rss-second (x) (declare (xargs :guard t)) (+ 1 (nfix x)))
(defattach (fn2-rss-hook fn2-rss-first) (fn2-rss-other-hook fn2-rss-first))

(defun fn2-rss-source (x)
 (declare (xargs :guard t))
 (if (consp x) (fn2-rss-hook (car x)) (fn2-rss-other-hook x)))
(defun fn2-rss-selected (x)
 (declare (xargs :guard t))
 (if (consp x) (fn2-rss-first (car x)) (fn2-rss-first x)))

; The statement mentions the resolved source body, never equality of either
; constrained hook with FIRST. Two distinct hooks may select the same body.
(make-event
 (value `(defthm fn2-rss-resolved-source
   ,(fn2-reference-selected-body-formula 'fn2-rss-source 'fn2-rss-selected
      '(fn2-rss-hook fn2-rss-other-hook) (w state))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-rss-selected))))))
(fn2-reference-selected-bind fn2-rss-source-binding fn2-rss-source fn2-rss-selected
 (fn2-rss-hook fn2-rss-other-hook) fn2-rss-resolved-source)
(fn2-reference-selected-check fn2-rss-source-binding)

(defthm fn2-rss-unrelated-true t :rule-classes nil)
(make-event
 (let ((record (cdr (assoc-eq 'fn2-rss-source-binding
                             (table-alist 'fn2-reference-selected-sources (w state))))))
  (value `(assert-event
   ',(and
      (fn2-reference-selected-currentp record (w state))
      (equal (fn2-selected-get :pairs record)
             '((fn2-rss-hook . fn2-rss-first) (fn2-rss-other-hook . fn2-rss-first)))
      (assoc-eq 'fn2-rss-helper (fn2-selected-get :graph record))
      (not (fn2-selected-get :logical-stub-equality record))
      (not (fn2-selected-get :host-execution-proof record))
      (equal (fn2-selected-source-problem 'fn2-rss-source 'fn2-rss-selected
               '(fn2-rss-hook fn2-rss-other-hook) 'fn2-rss-unrelated-true (w state))
             :resolved-source-equation)
      (equal (fn2-selected-source-problem 'fn2-rss-source 'fn2-rss-selected
               '(fn2-rss-hook fn2-rss-hook) 'fn2-rss-resolved-source (w state))
             :selection-census)
      (equal (fn2-selected-source-problem 'fn2-rss-source 'fn2-rss-selected
               '(fn2-rss-hook) 'fn2-rss-resolved-source (w state))
             :incomplete-dispatch-selection)
      (equal (fn2-selected-source-problem 'fn2-rss-source 'fn2-rss-selected
               '(fn2-rss-hook fn2-rss-first) 'fn2-rss-resolved-source (w state))
             :selection-not-in-source-body))))))

; Exact call-position replacement must not rewrite quoted symbols or a
; variable which happens to share an attachment's printed name.
(assert-event
 (equal
  (fn2-selected-body
   '((lambda (fn2-rss-hook)
       (cons fn2-rss-hook (cons 'fn2-rss-hook (fn2-rss-hook fn2-rss-hook)))) '7)
   '((fn2-rss-hook . fn2-rss-first)))
  '((lambda (fn2-rss-hook)
      (cons fn2-rss-hook (cons 'fn2-rss-hook (fn2-rss-first fn2-rss-hook)))) '7)))

; The old selected function and theorem still exist; only the operational
; selection changes. A consumer must reject the stale source binding.
(defattach (fn2-rss-hook fn2-rss-second) (fn2-rss-other-hook fn2-rss-first))
(make-event
 (let ((record (cdr (assoc-eq 'fn2-rss-source-binding
                             (table-alist 'fn2-reference-selected-sources (w state))))))
  (value `(assert-event ',(not (fn2-reference-selected-currentp record (w state)))))))
(must-fail (fn2-reference-selected-check fn2-rss-source-binding))
