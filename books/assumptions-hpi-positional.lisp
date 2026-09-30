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

; Interleaved stage and two-spool traces also require a visible frame.
; This is explicit evidence for a distinct retained role, never inferred
; from a full byte count on the written role or from an FD number alone.
(encapsulate
 (((fn-assume-hpi-positional-other-role * * * * *) => *))
 (local
  (defun fn-assume-hpi-positional-other-role (before after file other outcome)
   (or (not (eq outcome :ok)) (equal file other)
       (equal (fn-bs-content after other) (fn-bs-content before other)))))
 (defthm fn-assume-hpi-full-write-preserves-distinct-visible-role
  (implies (and (fn-assume-hpi-positional-other-role before after file other outcome)
                (eq outcome :ok) (not (equal file other)))
           (equal (fn-bs-content after other) (fn-bs-content before other)))
  :rule-classes nil))
