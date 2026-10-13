; The derived visit costs of the read's extent cap's dispatched entries
; (books/heap-log-extent-cap.lisp; host/native/heap.lisp fnn-command-heap,
; host/native/io.lisp fnn-log-observed-extent).  Each is `def-cost' with no
; declared bound: the twin is derived from the entry's executed body and the
; :unaccounted list is exactly the derived one (D27: nothing declared,
; nothing pinned): ACL2's digit table walk (our-digit-char-p), the string
; primitives, the decimal renderer and the probe line's pieces, each its own
; book's figure.
(in-package "ACL2")
(include-book "image-world")
(include-book "def-cost")
(include-book "memory-entry-cost")
(include-book "heap-log-extent-cap")

(def-cost fn-lxc-capped-p)
(def-cost fn-lxc-digits-value :unaccounted (our-digit-char-p))
(def-cost fn-lxc-words :unaccounted (fn-decimal-text string-append))
(def-cost fn-lxc-cap-of-text :unaccounted (length coerce our-digit-char-p))
(def-cost fn-lxc-verdict)
(def-cost fn-lxc-refusal-text :unaccounted (fn-decimal-text string-append-lst))
(def-cost fn-lxc-command-line :unaccounted (fn-mo-read-refusal-line fn-heap-reserve-report-line
                                            fn-mo-unseen-suffix fn-decimal-text string-append))

(def-cost-check fn-lxc-cap-of-text)
(def-cost-check fn-lxc-verdict)
(def-cost-check fn-lxc-refusal-text)
(def-cost-check fn-lxc-command-line)
