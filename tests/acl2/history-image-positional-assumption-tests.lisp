; Literal constraint teeth for A-HPI-POSITIONAL-IO's local witness shape.
; These do not evaluate a physical assumption or qualify native syscalls.
(in-package "ACL2")
(include-book "../../books/assumptions-hpi-positional")

(local (defconst *hio-before* (fn-bs-make 1 (list (cons 7 '(1 2 3 4))) nil nil 8)))
(local (defconst *hio-after* (fn-bs-make 1 (list (cons 7 '(1 9 8 4))) nil nil 8)))
(local (defun hio-write-conclusion (before after offset octets got outcome)
 (and (eq outcome :ok) (natp offset) (equal got (len octets))
      (equal (fn-bs-content after 7)
             (fn-bs-splice (fn-bs-content before 7) offset octets)))))
(local (defun hio-read-conclusion (bytes offset count octets got outcome)
 (and (eq outcome :ok) (natp offset) (natp count) (equal got count)
      (<= (+ offset count) (len (fn-bs-content bytes 7)))
      (equal octets (take count (nthcdr offset (fn-bs-content bytes 7)))))))
; Complete witness-shaped writes and reads are nonvacuous.
(local (assert-event
 (and (hio-write-conclusion *hio-before* *hio-after* 1 '(9 8) 2 :ok)
      (hio-read-conclusion *hio-after* 1 2 '(9 8) 2 :ok))))
; Corrupted observations: all scalar/count/outcome premises remain true,
; but a lying full-count write or read violates the exact visible bytes.
(local (assert-event
 (and (natp 1) (equal 2 (len '(9 8))) (eq :ok :ok)
      (not (equal (fn-bs-content *hio-before* 7)
                  (fn-bs-splice (fn-bs-content *hio-before* 7) 1 '(9 8))))
      (not (hio-write-conclusion *hio-before* *hio-before* 1 '(9 8) 2 :ok)))))
(local (assert-event
 (and (natp 1) (natp 2) (equal 2 2) (eq :ok :ok)
      (<= (+ 1 2) (len (fn-bs-content *hio-after* 7)))
      (not (equal '(9 7) (take 2 (nthcdr 1 (fn-bs-content *hio-after* 7)))))
      (not (hio-read-conclusion *hio-after* 1 2 '(9 7) 2 :ok)))))
; Incomplete counts do not meet the full observation constraint.
(local (assert-event
 (and (not (hio-write-conclusion *hio-before* *hio-after* 1 '(9 8) 1 :ok))
      (not (hio-read-conclusion *hio-after* 1 2 '(9 8) 1 :ok)))))

; A full successful splice does not itself constrain a different inode.
(local (defconst *hio-two-before*
 (fn-bs-make 1 (list (cons 7 '(1 2 3 4)) (cons 8 '(5 6))) nil nil 9)))
(local (defconst *hio-two-after*
 (fn-bs-make 1 (list (cons 7 '(1 9 8 4)) (cons 8 '(5 6))) nil nil 9)))
(local (defconst *hio-two-corrupt*
 (fn-bs-make 1 (list (cons 7 '(1 9 8 4)) (cons 8 '(5 99))) nil nil 9)))
(local (assert-event
 (and (eq :ok :ok) (not (equal 7 8))
      (hio-write-conclusion *hio-two-before* *hio-two-after* 1 '(9 8) 2 :ok)
      (equal (fn-bs-content *hio-two-after* 8) (fn-bs-content *hio-two-before* 8)))))
(local (assert-event
 (and (eq :ok :ok) (not (equal 7 8))
      (hio-write-conclusion *hio-two-before* *hio-two-corrupt* 1 '(9 8) 2 :ok)
      (not (equal (fn-bs-content *hio-two-corrupt* 8)
                  (fn-bs-content *hio-two-before* 8))))))
