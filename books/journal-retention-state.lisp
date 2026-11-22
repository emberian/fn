; A singleton lease serves the singleton retained event reader. Its
; generation comes from C's monotonic cut token, never a client ordinal.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)

(defcolumns fn2-journal-lease
 ((phase (:enum fn2-journal-lease-phase (:idle :collecting :ready :closing)))
  (token :u60) (kind :u8) (owner :u32) (generation :u60)
  (cut-commit :u60) (cut-event :u60) (scan :u32) (next-event :u60)))

(defun fn2-journal-lease-ownerp (token kind owner generation fn2-journal-lease)
 (declare (xargs :stobjs fn2-journal-lease :guard (fn2-journal-lease-wfp fn2-journal-lease)))
 (and (posp token) (< 0 (fn2-journal-lease-rows fn2-journal-lease))
      (not (= (fn2-journal-lease-phase 0 fn2-journal-lease) *fn2-journal-lease-phase-idle*))
      (equal token (fn2-journal-lease-token 0 fn2-journal-lease))
      (equal kind (fn2-journal-lease-kind 0 fn2-journal-lease))
      (equal owner (fn2-journal-lease-owner 0 fn2-journal-lease))
      (equal generation (fn2-journal-lease-generation 0 fn2-journal-lease))))
