; Extent-indexed construction ownership, populated by actual reservation only.
; A resident source location or decoded Ref cannot register a construction.
(in-package "ACL2")
(include-book "alloc")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-construction
 ((live :bool) (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (role :u8) (ordinal :u60) (epoch :u60) (counter :u60)
  (intended-bytes :u60) (completed-bytes :u60)))

