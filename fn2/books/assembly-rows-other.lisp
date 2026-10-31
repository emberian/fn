; The row readers (K-ROW-<field>, their widths) of layer other's kinds
; (machines.lisp fn2-machine-row-events): one section book per layer, so this
; book's cost follows its own kinds, not the instance.
(in-package "ACL2")
(include-book "assembly-rows-c")
(fn2-machine-row-events :other)
