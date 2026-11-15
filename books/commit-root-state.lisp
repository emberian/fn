; Actual commit directory carrier, independent of B registration.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-commit-root
 ((installed :u60) (published :u60) (proposed :u60)
  ; Row0 retained recovery boundary; positive base requires separate authority.
  (base-batch :u60) (base-event :u60) (base-ready :bool)
  (parent :u60) (extent :u32) (physical-history :u60) (physical-incarnation :u60) (first-key :u60) (members :u32) (seal-ready :bool) (barrier-mode :bool)
  ; Row 0 only: the first refused batch of an abort in progress (0: none)
  ; and the event it began at (b54 M3).
  (aborting :u60) (abort-event :u60)
 ))
