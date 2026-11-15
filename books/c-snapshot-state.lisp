; Held source-cut state and exact ownership, below live C operations.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)

(defcolumns fn2-csnapshot
 ((phase (:enum fn2-csnapshot-phase (:idle :closing :held :adopting :adopted)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (scan :u32) (blocked :bool) (cut-commit :u60) (cut-event :u60)
  (source :u8) (row :u32) (complete :bool)))

(defun fn2-csnapshot-ownerp (token okind oslot ogen fn2-csnapshot)
  (declare (xargs :stobjs fn2-csnapshot :guard (fn2-csnapshot-wfp fn2-csnapshot)))
  (and (< 0 (fn2-csnapshot-rows fn2-csnapshot))
       (not (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*))
       (equal token (fn2-csnapshot-token 0 fn2-csnapshot))
       (equal okind (fn2-csnapshot-owner-kind 0 fn2-csnapshot))
       (equal oslot (fn2-csnapshot-owner-slot 0 fn2-csnapshot))
       (equal ogen (fn2-csnapshot-owner-gen 0 fn2-csnapshot))))

; C source mutation stays closed after HELD read handles are invalidated by
; the exact adopter. CLOSING still lets already active workers finish.
(defun fn2-csnapshot-source-closed-p (fn2-csnapshot)
 (declare (xargs :stobjs fn2-csnapshot :guard (fn2-csnapshot-wfp fn2-csnapshot)))
 (and (< 0 (fn2-csnapshot-rows fn2-csnapshot))
      (member-equal (fn2-csnapshot-phase 0 fn2-csnapshot)
       (list *fn2-csnapshot-phase-held* *fn2-csnapshot-phase-adopting* *fn2-csnapshot-phase-adopted*))))
