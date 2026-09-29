; fn: the paged Message-ID reader against the catalog's logic function (lane
; paged-history-2, 2026-09-29; row P2 of planning/design-paged-history-
; 2026-09-29.md; PRF-970).  Prefix fn-mpxt- (books/msgid-pages-exec's).
;
; The catalog's Message-ID column `fn-cat-msgid-seqs' (books/catalog, the
; abstract stobj export every served finder calls: served-columns,
; served-catalog, served-catalog-owner) is `fn-cat$a-msgid-seqs' in the
; logic, the walk `fn-cat-seqs-for' over the rows from 0.  The paged
; reader's walk `fn-mpxt-spec-from' is the same walk stated over `nth', so
; the exec book's keystone restates against the catalog's logic function:
; KEYSTONE `fn-mpxt-seqs-is-cat-msgid-seqs'.  The concrete stobj's reader
; (`fn-cat$c-msgid-seqs', today the hash `fn-cat$c-msgids') becomes
; `fn-mpxt-seqs' over a nested `fn-mpxt' in the catalog's next edit (its
; {correspondence} theorem cites this one; the 5u method, design B.6): no
; served book changes, because the export's logic is unchanged.

(in-package "ACL2")
(include-book "msgid-pages-exec")
(include-book "catalog")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

(local
 (defthm fn-mpxt-nthcdr-cdr
   (implies (natp i)
            (equal (nthcdr (+ 1 i) l) (cdr (nthcdr i l))))))
(local
 (defthm fn-mpxt-car-nthcdr
   (implies (natp i)
            (equal (car (nthcdr i l)) (nth i l)))))
(local
 (defthm fn-mpxt-consp-nthcdr
   (implies (natp i)
            (iff (consp (nthcdr i l)) (< i (len l))))
   :hints (("Goal" :induct (nthcdr i l)))))

; The nth-walk from I is the catalog's cdr-walk over the rows from I.
(defthm fn-mpxt-spec-from-is-cat-seqs-for
  (implies (natp i)
           (equal (fn-mpxt-spec-from i msgid rows)
                  (fn-cat-seqs-for msgid (nthcdr i rows) i)))
  :hints (("Goal" :induct (fn-mpxt-spec-from i msgid rows)
           :in-theory (enable fn-mpxt-spec-from fn-mpxt-hitp fn-cat-seqs-for))))

; KEYSTONE: the paged reader is the catalog's Message-ID column, under the
; faithful relation the catalog's load establishes and its commit keeps.
(defthm fn-mpxt-seqs-is-cat-msgid-seqs
  (implies (fn-mpxt-faithful fn-cat$a fn-mpxt)
           (equal (fn-mpxt-seqs msgid fn-cat$a fn-mpxt)
                  (fn-cat$a-msgid-seqs msgid fn-cat$a)))
  :hints (("Goal" :in-theory (e/d (fn-cat$a-msgid-seqs nthcdr)
                                  (fn-mpxt-seqs fn-mpxt-faithful fn-cat-seqs-for
                                   fn-mpxt-spec-from fn-mpxt-spec-from-is-cat-seqs-for
                                   fn-mpxt-seqs-is-spec-from))
           :use ((:instance fn-mpxt-seqs-is-spec-from (rows fn-cat$a))
                 (:instance fn-mpxt-spec-from-is-cat-seqs-for (i 0) (rows fn-cat$a))))))
