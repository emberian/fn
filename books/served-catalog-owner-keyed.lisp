; The keyed open (lane paged-history-6, row P2 slice 3).
;
; The catalog's paged Message-ID table is keyed by the node secret's current
; entry (books/msgid-pages-exec.lisp fn-mpxt-key-of-entry, one key per
; generation): the open installs that key with fn-cat-clear-keyed BEFORE it
; loads the held rows, so every commit's tag is under the ring's key and the
; served refusal fn-cat-msgid-saturatedp, asked with the same key, is the
; table's own reading (host/owner-host.lisp fn-owner-install-extended, and
; the reclaim pass's fn-owner-orcp-load-columns).
;
; Logically the keyed clear is the clear (books/catalog.lisp
; fn-cat-clear-keyed-is-nil): this load IS fn-sca-load-held-rows, so every
; theorem stated over the open's catalog (the served-catalog-join-* keystones
; over fn-sca-load-held-rows) holds of the host's call unchanged.

(in-package "ACL2")

(include-book "served-catalog-owner")

(defun fn-sca-load-held-rows-keyed (key rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-sca-held-rowsp rows)
                              (fn-mpxt-keyp key)
                              (equal (len key) *fn-mpxt-key-octets*)))
           (ignorable fn-arena))
  (let ((fn-cat (fn-cat-clear-keyed key fn-cat)))
    (fn-sca-load-held-rows-from rows view-index fn-cat)))

; The host's open is the modelled open: the key changes what the executable
; table tags with, never the rows the catalog holds.
(defthm fn-sca-load-held-rows-keyed-is-load-held-rows
  (equal (fn-sca-load-held-rows-keyed key rows view-index fn-arena fn-cat)
         (fn-sca-load-held-rows rows view-index fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-sca-load-held-rows
                                     fn-sca-load-held-rows-keyed))))

(in-theory (disable fn-sca-load-held-rows-keyed))
