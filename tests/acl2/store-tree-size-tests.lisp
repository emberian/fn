; Literal positive and hypothesis-removal teeth for PRF-1113.
(in-package "ACL2")
(include-book "../../books/store-tree-size")

(assert-event
 (and (eq (symbol-class 'fn-scs-width (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scs-atom-size (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scs-atom (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scs-cons (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scs-spine (w state)) :common-lisp-compliant)))

; fn-scs-cons-preserves-canonical-size: compact octets, normal cons, dotted.
(assert-event
 (let* ((x 255) (y '(0 1 255))
        (a (fn-scs-summary x)) (d (fn-scs-summary y)))
   (and (equal a (fn-scs-summary x)) (equal d (fn-scs-summary y))
        (equal (fn-scs-cons a d) (fn-scs-summary (cons x y)))
        (equal (car (fn-scs-cons a d)) 7))))
(assert-event
 (let* ((x "shared context") (y '(:snapshot 65536 (0 1 255)))
        (a (fn-scs-summary x)) (d (fn-scs-summary y)))
   (and (equal a (fn-scs-summary x)) (equal d (fn-scs-summary y))
        (equal (fn-scs-cons a d) (fn-scs-summary (cons x y))))))
(assert-event
 (let* ((x 256) (y 65536)
        (a (fn-scs-summary x)) (d (fn-scs-summary y)))
   (and (equal a (fn-scs-summary x)) (equal d (fn-scs-summary y))
        (equal (fn-scs-cons a d) (fn-scs-summary (cons x y))))))

; Remove first literal equality; retain the second, make conclusion false.
(assert-event
 (let* ((x 256) (y '(1 2)) (a '(99 nil nil)) (d (fn-scs-summary y)))
   (and (not (equal a (fn-scs-summary x))) (equal d (fn-scs-summary y))
        (not (equal (fn-scs-cons a d) (fn-scs-summary (cons x y)))))))
; Remove second literal equality; retain the first, make conclusion false.
(assert-event
 (let* ((x 256) (y '(1 2)) (a (fn-scs-summary x)) (d '(99 nil nil)))
   (and (equal a (fn-scs-summary x)) (not (equal d (fn-scs-summary y)))
        (not (equal (fn-scs-cons a d) (fn-scs-summary (cons x y)))))))

; Corrupted metadata separately: correct bytes alone cannot identify compact
; octets. Loss of the tail's octet flag would charge a different program.
(assert-event
 (let ((a (fn-scs-summary 1)) (d '(5 nil nil)))
   (and (equal (car d) (len (fn-scc-encode '(2 3))))
        (not (equal (fn-scs-cons a d) (fn-scs-summary '(1 2 3)))))))
; Mutation witness: treating every cons as additive is false for octet lists.
(assert-event
 (not (equal (+ 1 (len (fn-scc-encode 1)) (len (fn-scc-encode '(2 3))))
             (len (fn-scc-encode '(1 2 3))))))

; fn-scs-spine-preserves-canonical-size: complete literal hypothesis and result.
(assert-event
 (let ((cs (list (fn-scs-summary :snapshot) (fn-scs-summary 256)
                 (fn-scs-summary '(1 2 3)))))
   (and (fn-scs-correspondsp cs '(:snapshot 256 (1 2 3)))
        (equal (fn-scs-spine cs) (fn-scs-summary '(:snapshot 256 (1 2 3)))))))
(assert-event
 (let ((cs (list (fn-scs-summary :snapshot) '(99 nil nil)
                 (fn-scs-summary '(1 2 3)))))
   (and (not (fn-scs-correspondsp cs '(:snapshot 256 (1 2 3))))
        (not (equal (fn-scs-spine cs)
                    (fn-scs-summary '(:snapshot 256 (1 2 3))))))))

; Representation boundaries at 255/256/65536; no old/new-width assumption.
(assert-event
 (and (equal (fn-scs-atom-size 255) 3)
      (equal (fn-scs-atom-size 256) 4)
      (equal (fn-scs-atom-size 65536) 5)
      (equal (fn-scs-atom-size -257) 4)
      (equal (fn-scs-atom-size "abcd") 7)
      (equal (fn-scs-atom-size :snapshot) 12)))

; Exact-length carry from a decoder's compact byte-span descriptor.
(assert-event
 (and (fn-scc-octet-listp '(0 1 255)) (equal 3 (len '(0 1 255)))
      (equal (fn-scs-octets 3) (fn-scs-summary '(0 1 255)))))
(assert-event
 (and (fn-scc-octet-listp '(0 1 255)) (not (equal 4 (len '(0 1 255))))
      (not (equal (fn-scs-octets 4) (fn-scs-summary '(0 1 255))))))
(assert-event
 (and (not (fn-scc-octet-listp '(0 256))) (equal 2 (len '(0 256)))
      (not (equal (fn-scs-octets 2) (fn-scs-summary '(0 256))))))
