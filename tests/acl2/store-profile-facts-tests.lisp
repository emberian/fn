; Teeth for books/store-profile-facts: the open gates at the two presets and
; the profile frame's round trip.  The two presets keep the values they had
; as format-7 translations (D34 kept the values, dropped the format).
(in-package "ACL2")
(include-book "../../books/store-profile-facts")
(include-book "std/testing/must-fail" :dir :system)

(defconst *spft-dev* *fn-bs-profile-development*)
(defconst *spft-scale* *fn-bs-profile-scale*)

; The presets, field by field (T H R A G N K, the five counts, the marker).
(assert-event (equal (cddr *spft-dev*)
                     (list 128 25165824 17138486 32768 65535 256 128
                           1048576 1048576 1048576 1048576 1048576 0)))
(assert-event (equal (cddr *spft-scale*)
                     (list 4096 805306368 17138486 32768 65535 256 4096
                           1048576 1048576 1048576 1048576 1048576 0)))
(assert-event (fn-bs-profile-validp *spft-dev*))
(assert-event (fn-bs-profile-validp *spft-scale*))
(assert-event (equal (fn-bs-profile-of *spft-scale*) *spft-scale*))
(assert-event (null (fn-bs-profile-of '(1 2 3 4 5 6))))

; The round trip (fn-bs-config-decode-of-encode) at both presets and at a
; raised request; a value that is not a profile encodes to nothing.
(assert-event (equal (fn-bs-config-decode (fn-bs-config-encode *spft-dev*)) *spft-dev*))
(assert-event (equal (fn-bs-config-decode (fn-bs-config-frame-for-profile :scale))
                     *spft-scale*))
(defconst *spft-raised*
  (fn-bs-profile-set-fields *spft-dev* '((2 . 1000) (3 . 1099511627776))))
(assert-event (fn-bs-profile-validp *spft-raised*))
(assert-event (equal (fn-bs-config-decode (fn-bs-config-encode *spft-raised*))
                     *spft-raised*))
(must-fail
 (defthm spft-round-trip-without-validp
   (equal (fn-bs-config-decode (fn-bs-config-encode '(1 2 3))) '(1 2 3))))

; The transaction namespace observation: 129 names are one past the
; development bound and inside scale's.
(defun spft-names (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-bs-txn-name-impl i) (spft-names (1+ i) n))
    nil))
(defconst *spft-129* (spft-names 0 129))
(assert-event (equal (fn-profile-txn-observation *spft-129* 128 0) :invalid))
(assert-event (not (equal (fn-profile-txn-observation *spft-129* 4096 0) :invalid)))
(assert-event (equal (len (caddr (fn-profile-txn-observation (spft-names 0 127) 128 0)))
                     127))

; The replay bound: 24 MiB under development, 768 MiB under scale.
(assert-event (fn-profile-replay-within-boundp *spft-dev* 25165824))
(assert-event (not (fn-profile-replay-within-boundp *spft-dev* 25165825)))
(assert-event (fn-profile-replay-within-boundp *spft-scale* 25165825))
(assert-event (not (fn-profile-replay-within-boundp '(1 2 3) 0)))
