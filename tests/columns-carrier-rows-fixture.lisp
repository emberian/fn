; Source-only fixture prepared for later authorized ACL2 admission. Not executed.
; Default carrier output stays identical; only :rows t requests a frame.
(in-package "ACL2")
(include-book "../books/columns")

(assert-event
 (equal
  (fn2-columns-carrier-specs '((fn2-carrier-rows-left 1 :prefix "-LEFT")))
  '(("-LEFT-TYPE" fn2-carrier-rows-leftp 1)
    ("-LEFT-WFP" fn2-carrier-rows-left-wfp 1 :hints nil))))
(assert-event
 (equal
  (fn2-columns-carrier-specs '((fn2-carrier-rows-left 1 :prefix "-LEFT" :rows nil)))
  (fn2-columns-carrier-specs '((fn2-carrier-rows-left 1 :prefix "-LEFT")))))
(assert-event
 (equal
  (fn2-columns-carrier-specs
   '((fn2-carrier-rows-left 1 :prefix "-LEFT" :rows t)
     (fn2-carrier-rows-right 2 :prefix "-RIGHT")))
  '(("-LEFT-TYPE" fn2-carrier-rows-leftp 1)
    ("-LEFT-WFP" fn2-carrier-rows-left-wfp 1 :hints nil)
    ("-LEFT-ROWS" fn2-carrier-rows-left-rows 1 :frame fn2-carrier-rows-left)
    ("-RIGHT-TYPE" fn2-carrier-rows-rightp 2)
    ("-RIGHT-WFP" fn2-carrier-rows-right-wfp 2 :hints nil))))

; Real mutable and read-only child inputs: the generated preservation claims
; retain both actual guards. Only the first output opts into a row-count frame.
(defcolumns fn2-carrier-rows-left ((value :u8)))
(defcolumns fn2-carrier-rows-right ((value :u8)))
(defun fn2-carrier-rows-copy (fn2-carrier-rows-left fn2-carrier-rows-right)
 (declare (xargs :stobjs (fn2-carrier-rows-left fn2-carrier-rows-right)
  :guard (and (fn2-carrier-rows-left-wfp fn2-carrier-rows-left)
              (fn2-carrier-rows-right-wfp fn2-carrier-rows-right))))
 (if (and (< 0 (fn2-carrier-rows-left-rows fn2-carrier-rows-left))
          (< 0 (fn2-carrier-rows-right-rows fn2-carrier-rows-right)))
  (let ((fn2-carrier-rows-left
         (fn2-carrier-rows-left-set-value 0 (fn2-carrier-rows-right-value 0 fn2-carrier-rows-right) fn2-carrier-rows-left)))
   (mv :ok fn2-carrier-rows-left fn2-carrier-rows-right))
  (mv :empty fn2-carrier-rows-left fn2-carrier-rows-right)))
(fn2-carrier-rows-left-preserves fn2-carrier-rows-copy
 (fn2-carrier-rows-left fn2-carrier-rows-right)
 :carriers ((fn2-carrier-rows-left 1 :prefix "-LEFT" :rows t)
            (fn2-carrier-rows-right 2 :prefix "-RIGHT")))

; Row frames follow the existing unconditional frame convention. TYPE/WFP
; claims retain all actual carrier guards, including the read-only child.
(make-event
 (let* ((name 'fn2-carrier-rows-copy)
        (args '(fn2-carrier-rows-left fn2-carrier-rows-right))
        (carriers '((fn2-carrier-rows-left 1 :prefix "-LEFT" :rows t)
                    (fn2-carrier-rows-right 2 :prefix "-RIGHT")))
        (hyps (fn2-columns-carrier-hyps carriers))
        (specs (fn2-columns-carrier-specs carriers))
        (events (fn2-columns-preservation-facts name (cons name args) specs hyps nil)))
  (if (and
       (equal (caddr (third events))
        '(equal (fn2-carrier-rows-left-rows
                 (mv-nth 1 (fn2-carrier-rows-copy fn2-carrier-rows-left fn2-carrier-rows-right)))
                (fn2-carrier-rows-left-rows fn2-carrier-rows-left)))
       (equal (caddr (second events))
        '(implies
          (and (fn2-carrier-rows-leftp fn2-carrier-rows-left)
               (fn2-carrier-rows-left-wfp fn2-carrier-rows-left)
               (fn2-carrier-rows-rightp fn2-carrier-rows-right)
               (fn2-carrier-rows-right-wfp fn2-carrier-rows-right))
          (fn2-carrier-rows-left-wfp
           (mv-nth 1 (fn2-carrier-rows-copy fn2-carrier-rows-left fn2-carrier-rows-right))))))
      (value '(value-triple :all-actual-carrier-guards))
    (er soft 'columns-carrier-rows-fixture "Missing row frame or actual carrier guards."))))
