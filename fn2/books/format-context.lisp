; Checker continuations and named caller expectations; independent of disk layouts.
(in-package "ACL2")
(include-book "columns")
(include-book "tuple")
(defcolumns fn2-fc
 ((phase (:enum fn2-fc-phase (:idle :decode :prefix :hash :digest)))
  (pos :u32) (zero :u32) (pad :u32) (pad-end :u32) (geom :u32)
  (previous-seal-offset :u32)
  (digest-0 :u32)
  (digest-1 :u32)
  (digest-2 :u32)
  (digest-3 :u32)
  (digest-4 :u32)
  (digest-5 :u32)
  (digest-6 :u32)
  (digest-7 :u32)
))
(defcolumns fn2-fc-context
 ((location :u60)
  (allocation :u60)
  (history :u60)
  (incarnation :u60)
  (writer-epoch :u60)
  (commit :u60)
  (page-kind :u60)
  (encoded-length :u60)
  (hash-0 :u32)
  (hash-1 :u32)
  (hash-2 :u32)
  (hash-3 :u32)
  (hash-4 :u32)
  (hash-5 :u32)
  (hash-6 :u32)
  (hash-7 :u32)
  (geometry-0 :u32)
  (geometry-1 :u32)
  (geometry-2 :u32)
  (geometry-3 :u32)
  (geometry-4 :u32)
  (geometry-5 :u32)
  (geometry-6 :u32)
  (geometry-7 :u32)
  (extent-writer-epoch :u60)
  (previous-commit :u60)
  (previous-seal-0 :u32)
  (previous-seal-1 :u32)
  (previous-seal-2 :u32)
  (previous-seal-3 :u32)
  (previous-seal-4 :u32)
  (previous-seal-5 :u32)
  (previous-seal-6 :u32)
  (previous-seal-7 :u32)
  (extent :u60)))
; Logical context tuple names are also generated, never decoded-field ordinals.
(fn2-cm-defreaders
 fn2-fc-expected-location
 fn2-fc-expected-allocation
 fn2-fc-expected-history
 fn2-fc-expected-incarnation
 fn2-fc-expected-writer-epoch
 fn2-fc-expected-commit
 fn2-fc-expected-page-kind
 fn2-fc-expected-encoded-length
 fn2-fc-expected-hash-0
 fn2-fc-expected-hash-1
 fn2-fc-expected-hash-2
 fn2-fc-expected-hash-3
 fn2-fc-expected-hash-4
 fn2-fc-expected-hash-5
 fn2-fc-expected-hash-6
 fn2-fc-expected-hash-7
 fn2-fc-expected-geometry-0
 fn2-fc-expected-geometry-1
 fn2-fc-expected-geometry-2
 fn2-fc-expected-geometry-3
 fn2-fc-expected-geometry-4
 fn2-fc-expected-geometry-5
 fn2-fc-expected-geometry-6
 fn2-fc-expected-geometry-7
 fn2-fc-expected-extent-writer-epoch
 fn2-fc-expected-previous-commit
 fn2-fc-expected-previous-seal-0
 fn2-fc-expected-previous-seal-1
 fn2-fc-expected-previous-seal-2
 fn2-fc-expected-previous-seal-3
 fn2-fc-expected-previous-seal-4
 fn2-fc-expected-previous-seal-5
 fn2-fc-expected-previous-seal-6
 fn2-fc-expected-previous-seal-7
 fn2-fc-expected-extent)

