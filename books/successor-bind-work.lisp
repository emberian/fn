; Declaration-time inventory of the actual bind path. No served schema scan,
; dynamic cost evaluator, second writer, or new caller readiness input.
(in-package "ACL2")
(include-book "successor-schema-geometry")
(include-book "arms")
(fn2-book-layer :c)
(defun fn2-successor-static-natural (term world)
 (declare (xargs :verify-guards nil))
 (cond ((natp term) term)
       ((and (quotep term) (natp (unquote term))) (unquote term))
       ((symbolp term) (fn2-cost-constant term world))
       (t nil)))
(defun fn2-successor-search-limits (term world)
 (declare (xargs :verify-guards nil))
 (cond ((atom term) nil)
       ((quotep term) nil)
       ((eq (car term) 'fn2-ov-search)
        (list (fn2-successor-static-natural (cadr term) world)))
       (t (append (fn2-successor-search-limits (car term) world)
                  (fn2-successor-search-limits (cdr term) world)))))
(defun fn2-successor-bind-work-inventory (ids search)
 (declare (xargs :verify-guards nil))
 (if (atom ids) nil
  (let* ((sid (car ids)) (nf (nfix (fn2-run-layout-fields sid 0)))
         (entry (fn2-run-layout-max-size sid 0))
         (key (fn2-succ-octets-total sid 0 (nfix (fn2-run-layout-keys sid))))
         (octets (fn2-succ-octets-total sid 0 nf)))
   (cons (list sid entry key octets
               (fn2-successor-slot-bind-byte-bound entry key octets search))
         (fn2-successor-bind-work-inventory (cdr ids) search)))))
(defun fn2-successor-bind-work-max (inventory)
 (declare (xargs :verify-guards nil))
 (if (atom inventory) 0
  (max (nfix (nth 4 (car inventory))) (fn2-successor-bind-work-max (cdr inventory)))))
(make-event
 (let ((limits (fn2-successor-search-limits
                 (getpropc 'fn2-ov-locate 'unnormalized-body nil (w state)) (w state))))
  (if (not (and (equal (len limits) 1) (natp (car limits))))
      (er soft 'successor-bind-work "Actual overlay search has no unique static work bound: ~x0." limits)
   (let* ((search (car limits))
          (inventory (fn2-successor-bind-work-inventory *fn2-run-assembled-ids* search))
          (bound (* *fn2-succ-slots* (fn2-successor-bind-work-max inventory))))
    (value `(progn
     (defconst *fn2-successor-bind-search-bound* ,search)
     (defconst *fn2-successor-bind-work-inventory* ',inventory)
     (defconst *fn2-successor-bind-byte-bound* ,bound)))))))
; A scalar-only entry still needs actual decode/encode work. Per-entry2O
; alone, or an unmultiplied entry bound, cannot certify the whole bind.
(assert-event (< 0 (fn2-successor-slot-bind-byte-bound 1 0 0 0)))
