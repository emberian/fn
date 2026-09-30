; A-HPI-POSITIONAL-IO: visible private stage/spool bytes, not durability.
; The actual holder must bind FILE to the exact live FD/inode and serialize
; its exclusive writer. Native full-count observations alone are not this
; assumption; selected platform qualification must discharge the relation.
(in-package "ACL2")
(include-book "byte-store")

(encapsulate
 (((fn-assume-hpi-positional-write * * * * * * *) => *)
  ((fn-assume-hpi-positional-read * * * * * * *) => *))
 (local
  (defun fn-assume-hpi-positional-write (before after file offset octets got outcome)
   (or (not (eq outcome :ok))
       (and (natp offset) (equal got (len octets))
            (equal (fn-bs-content after file)
                   (fn-bs-splice (fn-bs-content before file) offset octets))))))
 (local
  (defun fn-assume-hpi-positional-read (bytes file offset count octets got outcome)
   (or (not (eq outcome :ok))
       (and (natp offset) (natp count) (equal got count)
            (<= (+ offset count) (len (fn-bs-content bytes file)))
            (equal octets (take count (nthcdr offset (fn-bs-content bytes file))))))))
 (defthm fn-assume-hpi-full-write-is-visible-byte-splice
  (implies (and (fn-assume-hpi-positional-write before after file offset octets got outcome)
                (eq outcome :ok))
           (and (natp offset) (equal got (len octets))
                (equal (fn-bs-content after file)
                       (fn-bs-splice (fn-bs-content before file) offset octets))))
  :rule-classes nil)
 (defthm fn-assume-hpi-full-read-is-visible-byte-range
  (implies (and (fn-assume-hpi-positional-read bytes file offset count octets got outcome)
                (eq outcome :ok))
           (and (natp offset) (natp count) (equal got count)
                (<= (+ offset count) (len (fn-bs-content bytes file)))
                (equal octets (take count (nthcdr offset (fn-bs-content bytes file))))))
  :rule-classes nil))
