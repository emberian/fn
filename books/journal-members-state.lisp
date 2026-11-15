; Retained member cursor shape, independent of the C record body codecs.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-journal-members
 ((phase (:enum fn2-journal-members-phase (:idle :scanning :leaf :done :invalid)))
  (next-event :u60) (end-event :u60) (event :u60)
  (off :u32) (end :u32) (start :u32) (leaf-end :u32)
  (slot :u32) (gen :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (hash-phase :u8)))
