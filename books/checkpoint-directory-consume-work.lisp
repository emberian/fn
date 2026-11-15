; Canonical consume fixed representation work, in the existing work categories.
; :bytes counts typed payload READ+WRITE octets (copy/compare, not scalar math).
; :steps counts native metadata GET/SET (including row/array-length checks in
; BODY-invoked fixed-column WFP), bounded literal-list probes/end and generated
; core child GET/store. Local scalar arithmetic/comparison belongs to that
; bounded primitive; it does not turn every Lisp expression into a work step.
; All bank/short-circuit alternatives are summed, not trusted caller flags.
; Source controls tie these components to the real providers and generator.
; Physical/extraction work refinement remains owed; these are not CPU timings.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :c)

; The actual two-record authority layout: 32 descriptor bytes, 60 peaks of
; eight u32 words, and eight u32 predecessor words in each record.
(defconst *fn2-directory-consume-descriptor-bytes* 32)
(defconst *fn2-directory-consume-frontier-levels* 60)
(defconst *fn2-directory-consume-word-count* 8)
(defconst *fn2-directory-consume-word-bytes* (ceiling 32 8))
(defconst *fn2-directory-consume-authority-copy-bytes*
 (* 2 (+ *fn2-directory-consume-descriptor-bytes*
         (* *fn2-directory-consume-word-bytes*
            (+ (* *fn2-directory-consume-frontier-levels* *fn2-directory-consume-word-count*)
               *fn2-directory-consume-word-count*)))))
(defconst *fn2-directory-consume-base-seal-bytes*
 (* 2 *fn2-directory-consume-word-count* *fn2-directory-consume-word-bytes*))
; The full event subject checks pending authority/descriptor once. The remaining
; comparisons are event descriptor, scanned predecessor seal and published hash.
(defconst *fn2-directory-consume-compare-bytes*
 (+ (* 2 *fn2-directory-consume-descriptor-bytes*)
    (* 2 *fn2-directory-consume-descriptor-bytes*)
    (* 2 *fn2-directory-consume-word-count* *fn2-directory-consume-word-bytes*)
    (* 2 *fn2-directory-consume-word-count* *fn2-directory-consume-word-bytes*)))
(defconst *fn2-directory-rebase-consume-bytes*
 (+ *fn2-directory-consume-authority-copy-bytes*
    *fn2-directory-consume-base-seal-bytes* *fn2-directory-consume-compare-bytes*))

; WFP executes fixed column-length metadata checks, never a stored-row scan:
; two ROWS reads plus one LENGTH and one ROWS read per declared column.
(defconst *fn2-directory-consume-slot-shape-steps*
 (+ (+ 2 (* 2 15)) (+ 2 (* 2 12)) (+ 2 (* 2 1))))
(defconst *fn2-directory-consume-slot-steps*
 (+ *fn2-directory-consume-slot-shape-steps* 3))
; Existing caller WFP guards discharge the generated carried equivalence.
(defconst *fn2-directory-consume-slot-carried-steps* 3)
(defconst *fn2-directory-consume-authority-current-steps*
 (+ 16 *fn2-directory-consume-slot-carried-steps*))
(defconst *fn2-directory-consume-authority-complete-steps*
 (+ 2 *fn2-directory-consume-authority-current-steps*))
(defconst *fn2-directory-consume-event-subject-steps*
 (+ 24 1 *fn2-directory-consume-authority-complete-steps*))
(defconst *fn2-directory-consume-digest-row-steps* (+ 2 (* 2 8) 1))
(defconst *fn2-directory-consume-raw-metadata-steps*
 (+ 83 ; actual consume's direct scalar reads/writes, including publication
    6  ; actual held snapshot owner predicate
    *fn2-directory-consume-event-subject-steps*
    28 ; publication scalar/bank identity, both bank alternatives
    *fn2-directory-consume-digest-row-steps*))
(defconst *fn2-directory-consume-literal-spine-steps*
 (+ (+ 2 1) (+ 4 1) (+ 3 1)))
; SAME emitted stobj-let: source-world gate checks the actual child bindings
; and mutable return set. This is not a parallel handwritten core face.
(defconst *fn2-directory-consume-core-get-steps* 13)
(defconst *fn2-directory-consume-core-store-steps* 4)
(defconst *fn2-directory-rebase-consume-steps*
 (+ *fn2-directory-consume-raw-metadata-steps*
    *fn2-directory-consume-literal-spine-steps*
    *fn2-directory-consume-core-get-steps* *fn2-directory-consume-core-store-steps*))
(assert-event (and (posp *fn2-directory-rebase-consume-bytes*)
                  (unsigned-byte-p 32 *fn2-directory-rebase-consume-bytes*)
                  (unsigned-byte-p 32 *fn2-directory-rebase-consume-steps*)
                  (posp *fn2-directory-rebase-consume-steps*)))

; These component checks are ACL2 arithmetic, not host decisions. The
; actual registered-kind independent/combined work-limit gate is prepared in
; directory-consume-face-source-unit and must join the controller declaration.
(assert-event (equal *fn2-directory-rebase-consume-bytes* 4288))
(assert-event (equal *fn2-directory-rebase-consume-steps* 211))
