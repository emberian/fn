; fn: R, the history stobj's relation to a store node (lane history-columns-3,
; 2026-09-27).
;
; R(fn-hist, s) := the stobj's logical value IS the store's retained history,
; (fn-sf-records (fn-sn-files s)).  It replaces fn-ceis-indexedp (the store
; node's event index agreeing with its history, PRF-144) as the premise of
; every indexed reader: the readers read the stobj (books/history-columns.lisp)
; instead of the store node's field 13, which is retired.
;
; Established at every open by `fn-hist-load' (KEYSTONE
; fn-hist-load-is-the-history) and preserved across owner runs by
; `fn-hist-sync' (KEYSTONE fn-hist-sync-after-run-is-the-history,
; books/history-columns-store.lisp).  One process serves one store (the
; owner's, or in store mode the store node's), so one stobj.  A proof-only
; relation: never evaluated on a served path.
;
; The three answers under R, over the history list (the analogues of the
; index's fn-cei-*-of-correspondence rules):
;   fn-hist-of-storep-msgid-records, -at, -count.
(in-package "ACL2")
(include-book "history-columns")
(include-book "store-node")

(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-hist-of-storep (fn-hist s)
  (equal fn-hist (fn-sf-records (fn-sn-files s))))

(defthm fn-hist-of-storep-msgid-records
  (implies (fn-hist-of-storep fn-hist s)
           (equal (fn-hist-msgid-records msgid fn-hist)
                  (fn-cei-article-records-for msgid (fn-sf-records (fn-sn-files s))))))

(defthm fn-hist-of-storep-at
  (implies (fn-hist-of-storep fn-hist s)
           (equal (fn-hist-at seq fn-hist)
                  (nth seq (fn-sf-records (fn-sn-files s))))))

(defthm fn-hist-of-storep-count
  (implies (fn-hist-of-storep fn-hist s)
           (equal (fn-hist-count fn-hist)
                  (len (fn-sf-records (fn-sn-files s))))))

; Left ENABLED: a hypothesis (fn-hist-of-storep fn-hist s) opens to the
; equality, and the prover substitutes the history for the stobj.

; -----------------------------------------------------------------------------
; The sync (moved here from books/history-columns-store.lisp so that every
; reader's host line can reach it): the rows of FILES' history past the
; stobj's count, appended in order, each read through `fn-sf-records-nth'
; (the snoc-list's newest end: O(1) per row committed since the last sync).
; Over a prefix it IS the history (fn-hist-sync-of-prefix-is-the-history),
; so a sync before a read establishes R whenever the stobj was a prefix.

(defun fn-hist-sync-aux (k n files fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (natp k) (natp n))
                  :measure (nfix (- (nfix n) (nfix k)))))
  (if (and (natp k) (natp n) (< k n))
      (let ((fn-hist (fn-hist-append (fn-sf-records-nth k files) fn-hist)))
        (fn-hist-sync-aux (1+ k) n files fn-hist))
    fn-hist))

; The rows of FILES' history past the stobj's count, appended in order.
(defun fn-hist-sync (files fn-hist)
  (declare (xargs :stobjs fn-hist))
  (fn-hist-sync-aux (fn-hist-count fn-hist) (fn-sf-records-count files)
                    files fn-hist))

; -----------------------------------------------------------------------------
; The sync over a prefix is the history.

(local
 (defun fn-hist-slice (k n xs)
   (declare (xargs :measure (nfix (- (nfix n) (nfix k)))))
   (if (and (natp k) (natp n) (< k n))
       (cons (nth k xs) (fn-hist-slice (1+ k) n xs))
     nil)))

(local
 (defthm fn-hist-sync-aux-is-append-slice
   (implies (true-listp fn-hist)
            (equal (fn-hist-sync-aux k n files fn-hist)
                   (append fn-hist (fn-hist-slice k n (fn-sf-records files)))))
   :hints (("Goal" :in-theory (enable fn-sf-records-nth)
            :induct (fn-hist-sync-aux k n files fn-hist)))))

(local
 (defthm fn-hist-nthcdr-unroll
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))))

(local
 (defthm fn-hist-nthcdr-len
   (implies (true-listp xs) (equal (nthcdr (len xs) xs) nil))))

(local
 (defthm fn-hist-slice-is-nthcdr
   (implies (and (true-listp xs) (natp k) (<= k (len xs)))
            (equal (fn-hist-slice k (len xs) xs) (nthcdr k xs)))
   :hints (("Goal" :induct (fn-hist-slice k (len xs) xs)
            :in-theory (disable nthcdr nth len)))))

(local (in-theory (disable fn-hist-nthcdr-unroll)))

(local
 (defthm fn-hist-prefix-append-nthcdr
   (implies (and (fn-sf-prefixp h xs) (true-listp xs))
            (equal (append h (nthcdr (len h) xs)) xs))
   :hints (("Goal" :in-theory (enable fn-sf-prefixp)))))

(local
 (defthm fn-hist-prefix-len
   (implies (fn-sf-prefixp h xs) (<= (len h) (len xs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-sf-prefixp)))))

(local
 (defthm fn-hist-prefix-true-listp
   (implies (fn-sf-prefixp h xs) (true-listp h))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-sf-prefixp)))))

(defthm fn-hist-sync-of-prefix-is-the-history
  (implies (and (fn-sf-prefixp fn-hist (fn-sf-records files))
                (true-listp (fn-sf-records files)))
           (equal (fn-hist-sync files fn-hist) (fn-sf-records files)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hist-sync fn-sf-records-count)
                           (fn-hist-sync-aux fn-sf-prefixp)))))

(in-theory (disable fn-hist-sync))

; The host's refresh before a read: a RELOAD (the store was opened or reset
; since the last read: the stobj may hold another history) loads the history
; whole (KEYSTONE fn-hist-load-is-the-history); otherwise the sync appends
; the rows past the stobj's count.  Either way, the result is the history
; (fn-hist-refresh-is-the-history): R holds at the read.
(defun fn-hist-refresh (files reload fn-hist)
  (declare (xargs :stobjs fn-hist))
  (if reload
      (fn-hist-load (true-list-fix (fn-sf-records files)) 0 fn-hist)
    (fn-hist-sync files fn-hist)))

(defthm fn-hist-refresh-is-the-history
  (implies (and (true-listp (fn-sf-records files))
                (or reload (fn-sf-prefixp fn-hist (fn-sf-records files))))
           (equal (fn-hist-refresh files reload fn-hist)
                  (fn-sf-records files))))

(in-theory (disable fn-hist-refresh))
