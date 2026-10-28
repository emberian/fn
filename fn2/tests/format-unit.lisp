(in-package "ACL2")
(include-book "../books/format")
(defun fn2-format-layouts-p (entries)
  (declare (xargs :verify-guards nil))
  (if (atom entries) t
    (and (fn2-layoutp (cadar entries)) (fn2-format-layouts-p (cdr entries)))))
(assert-event (fn2-format-layouts-p *fn2-format-layouts*))
; Independent hand-built bytes: an anchor's four digests and embedded Ref.
(assert-event
 (let ((digest (cons 1 (make-list 32 :initial-element 170)))
       (wire-digest (cons 1 (make-list 32 :initial-element 170))))
   (equal (fn2-layout-octets *fn2-format-anchor*
            (list 0 128 2 3 digest 4 5 6 7 0 129 digest digest digest digest))
          (append '(0 128 1 2 3) wire-digest '(4 5 6 7 0 129 1)
                  wire-digest wire-digest wire-digest wire-digest))))
(assert-event
 (equal (fn2-layout-octets *fn2-format-frame-header*
          (list *fn2-format-frame-magic* 1 128 2 3 4 5 6 7 8 129 250))
        '(70 50 74 82 1 128 1 2 3 4 5 6 7 8 129 1 250 1)))
(assert-event (equal *fn2-format-message-id-max* 250))
(assert-event (equal (cadr (assoc-eq 'message-id *fn2-format-article-acceptance*))
                     '(:octets 250)))
