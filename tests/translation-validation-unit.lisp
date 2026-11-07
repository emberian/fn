; Semantic export controls, judged by the ACL2 kernel and live world checks.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-a")
(include-book "../books/translation-validation")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (equal (fn2-tv-object (coerce (list (code-char 13) (code-char 10)) 'string))
             '(:string (13 10)))
      (not (equal (fn2-tv-object 'acl2::fn2-echo) (fn2-tv-object :fn2-echo)))
      (equal (fn2-tv-object 3/2) '(:rational 3 2))))

(defun fn2-tv-replace (key value row)
  (declare (xargs :guard t))
  (if (and (consp row) (consp (cdr row)))
      (cons (car row) (cons (if (equal key (car row)) value (cadr row))
                            (fn2-tv-replace key value (cddr row))))
    nil))

; Positive control uses the exact same live-world checking macro as exports.
(fn2-tv-check-function (fn2-tv-function 'fn2-echo-run-free-children (w state))
                       'fn2-echo-run-free-children)
(fn2-tv-check-manifest (fn2-tv-manifest (w state)))

; Changed valid logical body, not malformed syntax.
(must-fail
 (fn2-tv-check-function
  (fn2-tv-replace :logical-body (fn2-tv-object '(quote nil))
                 (fn2-tv-function 'fn2-echo-run-free-children (w state)))
  'fn2-echo-run-free-children))

; Same children, wrong field order.
(must-fail
 (fn2-tv-check-manifest
  (fn2-tv-replace :core-layout
                 (fn2-tv-object (list 'quote (reverse *fn2-core-children*)))
                 (fn2-tv-manifest (w state)))))

; An executable selection absent from the admitted world is never a body.
(must-fail
 (fn2-tv-check-function
  (fn2-tv-replace :attachment
                 (fn2-tv-object '(fn2-echo-run-free . fn2-scribe-run-free))
                 (fn2-tv-function 'fn2-echo-run-free (w state)))
  'fn2-echo-run-free))

; Whole-antecedent positive witness for the changed body control.
(defthm fn2-tv-body-positive-and-mutation
 (and (equal (fn2-echo-run-free-children 0 0 1 0 1 nil nil) '(0 1 0 nil))
      (not (equal nil (fn2-echo-run-free-children 0 0 1 0 1 nil nil))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-echo-run-free-children))))
