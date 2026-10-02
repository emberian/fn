; fn: the served columns across a forget (lane arena-forget, 2026-10-03;
; PRF-1235).
;
; The relation F (books/served-columns.lisp fn-scol-okp) says every catalog
; row's decided column is the column of the bytes at its handle; every arena
; export the owner calls keeps it (fn-scol-okp-of-seal-list, -of-faithful-
; reseat, ...).  The forget keeps it for a catalog none of whose rows names
; the forgotten handle: the rows the forget does not touch read the bytes
; they read before.  That no row names it is the reclaim swap's root fact
; (books/arena-forget.lisp fn-arf-changed-handles-are-unnamed over the rows
; the rebuilt catalog is loaded from).

(in-package "ACL2")
(include-book "served-columns")
(include-book "arena-forget")

; No row names H.
(defun fn-arf-rows-unnamed-p (h rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (not (equal (fn-record-payload (car rows)) h))
           (fn-arf-rows-unnamed-p h (cdr rows)))
    t))

(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-p-is-payload-listp)))

(local
 (defthm fn-arf-payload-bytes-of-forget
   (implies (and (natp h) (not (equal p h)))
            (equal (fn-nntp-payload-bytes p (fn-arena-forget h fn-arena))
                   (fn-nntp-payload-bytes p fn-arena)))
   :hints (("Goal" :in-theory (enable fn-nntp-payload-bytes)))))

(local
 (defthm fn-arf-rows-okp-of-forget
   (implies (and (fn-scol-rows-okp rows fn-arena)
                 (natp h)
                 (fn-arf-rows-unnamed-p h rows))
            (fn-scol-rows-okp rows (fn-arena-forget h fn-arena)))
   :hints (("Goal" :induct (fn-arf-rows-unnamed-p h rows)
            :in-theory (enable fn-scol-row-okp)))))

; KEYSTONE (PRF-1235).  A forget of a handle no catalog row names keeps F.
(defthm fn-scol-okp-of-forget
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (natp h)
                (fn-arf-rows-unnamed-p h fn-cat))
           (fn-scol-okp (fn-arena-forget h fn-arena) fn-cat))
  :hints (("Goal" :in-theory (enable fn-scol-okp))))
