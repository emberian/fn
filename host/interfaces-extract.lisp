; fn: the extraction roots the image does not load (G7, host/interfaces.lisp).
;
; host/store-open-host.lisp (the read-only store open as ACL2 :program code
; over the host primitives) and host/store-write-host.lisp (the writable store
; verbs, lane extract-writable) are loaded by the extractor's world
; (tools/extract/world.py EXTRA_HOSTS), not by the image, so its root is
; declared and checked there.

(in-package "ACL2")
(include-book "../books/definterface")

(definterface fn-xo-open-store
  :class :program
  :root :extract)

(definterface fn-xw-main
  :class :program
  :root :extract)
