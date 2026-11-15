; Four bounded continuations per actual consumer read row: cursor lookup,
; stream frontier, next-item selection and overview Message-ID selection.
(in-package "ACL2")
(include-book "machines-b")
(fn2-book-layer :e)
(defconst *fn2-cns-read-work-stride* 4)
(defconst *fn2-cns-read-work-done* 255)
(defcolumns fn2-cns-read-work
 ((owner :u32) (generation :u60) (phase :u8)
  (a :u60) (b :u60) (c :u60) (d :u60) (e :u60) (f :u60)
  (v0 :u60) (v1 :u60) (v2 :u60) (v3 :u60) (v4 :u60) (v5 :u60)))
(defcorechild fn2-core-cns-read-work fn2-cns-read-work
 :init (fn2-cns-read-work-init (* *fn2-cns-read-work-stride* (fn2-b-read-rows profile)) fn2-cns-read-work)
 :profilep (unsigned-byte-p 32 (* *fn2-cns-read-work-stride* (fn2-b-read-rows profile)))
 :why "Consumer reads retain actual request generation, inputs and selected rows across physical page misses.")
