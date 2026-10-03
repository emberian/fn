(in-package "ACL2")
(include-book "../../books/newnews-metadata-cursor")

; Literal producer teeth: sparse no-match candidate work is distinct from
; output drain. The captured root/configuration remain fixed across both.
(defconst *nnmt-a*
  (fn-make-article "<a@x>" '(13 10 13 10 65) '("fn.test") '(("fn.test" . 1)) 1 5))
(defconst *nnmt-b*
  (fn-make-article "<b@x>" '(13 10 13 10 66) '("fn.other") '(("fn.other" . 1)) 2 6))
(defconst *nnmt-cur*
  (fn-cur-make '(:snapshot root-a :config cfg-a)
               (fn-nnw-cursor '("fn.test") 0 (list *nnmt-b* *nnmt-a*) nil 7)
               nil nil))

(defthm nnmt-sparse-progress-and-output-residual
  (let* ((one (fn-nnw-meta-step *nnmt-cur* 1 2 nil nil))
         (next (mv-nth 1 one))
         (two (fn-nnw-meta-step next 1 2 nil nil))
         (saved (mv-nth 1 two))
         (drain (fn-nnw-meta-step saved 0 2 nil nil)))
    (and (equal (mv-nth 0 one) nil)
         (equal (mv-nth 2 one) 1)
         (equal (fn-nnw-tail (fn-cur-progress next)) (list *nnmt-a*))
         (equal (mv-nth 0 two) '(60 97))
         (equal (fn-cur-progress saved) nil)
         (equal (fn-cur-context saved) (fn-cur-context *nnmt-cur*))
         (equal (mv-nth 2 drain) 0)
         (equal (mv-nth 0 drain) '(64 120))
         (equal (append (mv-nth 0 one) (mv-nth 0 two) (mv-nth 0 drain)
                        (fn-nnw-meta-remaining (mv-nth 1 drain) nil nil))
                (fn-nnw-meta-remaining *nnmt-cur* nil nil)))))

; The generated bounds are about emitted bytes and candidate calls. This
; witness deliberately has a row larger than BYTES, not an implementation
; ceiling: its suffix remains owed after the last candidate is consumed.
(defthm nnmt-final-row-remains-live-while-buffered
  (let ((next (mv-nth 1
              (fn-nnw-meta-step
               (fn-cur-make 'root-a
                            (fn-nnw-cursor '("fn.test") 0 (list *nnmt-a*) nil 7)
                            nil nil)
               1 1 nil nil))))
    (and (not (fn-cur-progress next))
         (fn-nnw-meta-livep next)
         (equal (len (fn-cur-pending next)) 9))))
