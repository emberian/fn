(in-package "ACL2")
(include-book "../../books/obligation-view-budget")

; Arithmetic-model teeth only. Actual trie support, machine integer layout
; and allocator/collector lifetimes remain the composed PRF-1052 target.
(defun ovbt-hyps (characters subjects records)
  (list (<= (nfix characters) (* *fn-record-max-metadata* (nfix records)))
        (<= (nfix subjects) (nfix records))))
(defun ovbt-conclusion (characters subjects records)
  (<= (+ (* 4 (fn-ovb-object-octets characters subjects))
         (fn-ovb-delta-reserve))
      (fn-heap-obligation-view-reserve records)))

; Reachable maximal metadata contribution, with both hypotheses explicit.
(assert! (equal (ovbt-hyps 512 2 2) '(t t)))
(assert! (ovbt-conclusion 512 2 2))
; Removing the character-support hypothesis alone makes the conclusion fail.
(assert! (equal (ovbt-hyps 513 2 2) '(nil t)))
(assert! (not (ovbt-conclusion 513 2 2)))
; Removing the subject-support hypothesis alone makes the conclusion fail.
(assert! (equal (ovbt-hyps 512 3 2) '(t nil)))
(assert! (not (ovbt-conclusion 512 3 2)))

(assert! (and (<= (nfix 2) (nfix 3))
              (<= (fn-heap-obligation-view-reserve 2)
                  (fn-heap-obligation-view-reserve 3))))
(assert! (and (not (<= (nfix 3) (nfix 2)))
              (not (<= (fn-heap-obligation-view-reserve 3)
                       (fn-heap-obligation-view-reserve 2)))))
(assert! (natp (fn-heap-obligation-view-reserve 2)))
(assert! (equal (fn-heap-obligation-view-reserve 16384) 546341504))
(assert! (equal (fn-heap-obligation-view-reserve 0) 2130560))
