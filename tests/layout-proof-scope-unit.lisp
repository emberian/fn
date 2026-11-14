(in-package "ACL2")
(include-book "../books/layout")

;; A codec must admit from the library's proof basis even when its caller
;; supplies no codec facts, then restore that caller's existing theory.
(encapsulate ()
 (local (in-theory (theory 'minimal-theory)))
 (make-event
  (value `(defconst *fn2-codec-scope-incoming* ',(current-theory :here))))

 (deflayout fn2-codec-scope-mixed
   '((kind :u8) (counter :varint)
     (state (:enum fn2-codec-scope-state (:open :done)))
     (owner (:id principal)) (hash :digest)
     (payload (:octets16 11)) (padding (:zero 2))))
 (assert-event
  (equal (intersection-equal (current-theory :here) (theory 'fn2-codec-proof-theory))
         (intersection-equal *fn2-codec-scope-incoming* (theory 'fn2-codec-proof-theory))))

 ;; A repeated enum is already declared outside this codec's local basis.
 (deflayout fn2-codec-scope-shared-enum
   '((state (:enum fn2-codec-scope-state (:open :done))) (marker :u16be)))
 (assert-event
  (equal (intersection-equal (current-theory :here) (theory 'fn2-codec-proof-theory))
         (intersection-equal *fn2-codec-scope-incoming* (theory 'fn2-codec-proof-theory)))))
