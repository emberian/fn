; Numeric extras share the ordinary column proof basis; raw extras keep theirs.
(in-package "ACL2")
(include-book "../books/columns")
(make-event
 (value `(defconst *fn2-numeric-theory-incoming* ',(current-theory :here))))

(defcolumns fn2-numeric-theory-table ((value :u60) (flag :bool))
 :extra-fields
 ((fn2-numeric-theory-count :type (unsigned-byte 60) :initially 0
   :why "Numeric scalar uses the library proof basis.")
  (fn2-numeric-theory-fixed :type (array (unsigned-byte 8) (2)) :initially 0
   :why "Fixed numeric array retains its indexed proof interface.")
  (fn2-numeric-theory-data :type (array (unsigned-byte 32) (0)) :initially 0 :resizable t
   :why "Resizable numeric array retains its shape and type contracts.")))

; This external stobj's creator/predicate facts were not present when the
; columns library froze its theory. The raw-extra fallback must retain them.
(defstobj fn2-numeric-theory-child (fn2-numeric-theory-child-value :type (unsigned-byte 8) :initially 0))
(defcolumns fn2-numeric-theory-mixed ((value :u8))
 :extra-fields
 ((fn2-numeric-theory-child-slot :type fn2-numeric-theory-child
   :why "External nested-stobj constructor requires incoming facts.")
  (fn2-numeric-theory-mixed-count :type (unsigned-byte 32) :initially 0
   :why "A numeric sibling does not hide the external constructor.")))
(assert-event (subsetp-equal *fn2-numeric-theory-incoming* (current-theory :here)))
