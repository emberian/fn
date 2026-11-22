; Fixed FNCT envelope widths shared by the carrier policy and the codec.
(in-package "ACL2")

(defconst *fn2-fnct-header-octets* 10)
(defconst *fn2-fnct-trailer-octets* 32)
(defconst *fn2-fnct-overhead* (+ *fn2-fnct-header-octets* *fn2-fnct-trailer-octets*))
