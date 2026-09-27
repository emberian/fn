; fn: an archive article read through the payload arena without building its
; octet list: its length and whether it is a reclaim tombstone.
;
; Moved here from books/nntp-responses.lisp (lane served-readers wrote them,
; 2026-09-27, F2) by lane matrix-reds-reclaim, so that the reclaim counts
; (books/store-reclaim-holders.lisp) read the same facts the served readers
; do: after the records flip an archive article's payload position is an
; arena HANDLE, and the counts had parsed the handle as the octets.  Names
; unchanged.
(in-package "ACL2")
(include-book "nntp-session")
(include-book "reclaim-tombstone")
;; Whether an article is reclaimed, read through the arena (lane served-readers,
;; 2026-09-27, F2): at most the tombstone's fixed head of the sealed payload
;; is read in place, and no octet list is built.  Logically it IS
;; fn-rcl-tombstonep of the article's bytes (the definition expands in every
;; proof); fn-nntp-article-tombstonep-exec-is-logic is the guard obligation.
(defun fn-nntp-arena-prefixp (prefix h i fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (true-listp prefix) (natp h) (natp i)
                              (< h (fn-arena-count fn-arena)))
                  :measure (len prefix)))
  (if (consp prefix)
      (and (< i (fn-arena-payload-len h fn-arena))
           (equal (car prefix) (fn-arena-get h i fn-arena))
           (fn-nntp-arena-prefixp (cdr prefix) h (+ 1 i) fn-arena))
    t))

(encapsulate ()
  (local (defthm fn-nntp-car-nthcdr (equal (car (nthcdr i xs)) (nth i xs))))
  (local (defthm fn-nntp-cdr-nthcdr
           (implies (natp i) (equal (cdr (nthcdr i xs)) (nthcdr (+ 1 i) xs)))))
  (local (defthm fn-nntp-nthcdr-of-nil (equal (nthcdr i nil) nil)))
  (local (defthm fn-nntp-consp-nthcdr
           (implies (natp i) (iff (consp (nthcdr i xs)) (< i (len xs))))))
  (local (in-theory (disable nthcdr nth)))
  (defthm fn-nntp-arena-prefixp-is-rcl-prefixp
    (implies (natp i)
             (equal (fn-nntp-arena-prefixp prefix h i fn-arena)
                    (fn-rcl-prefixp prefix (nthcdr i (nth h fn-arena)))))
    :hints (("Goal" :induct (fn-nntp-arena-prefixp prefix h i fn-arena)
             :in-theory (enable fn-rcl-prefixp fn-arena-get-is-nth
                                fn-arena-payload-len-is-len-nth)))))

(defthm fn-nntp-arena-prefixp-at-0
  (equal (fn-nntp-arena-prefixp prefix h 0 fn-arena)
         (fn-rcl-prefixp prefix (nth h fn-arena)))
  :hints (("Goal" :use ((:instance fn-nntp-arena-prefixp-is-rcl-prefixp (i 0)))
           :in-theory (enable nthcdr))))

(local
 (defthm fn-nntp-rcl-at-leastp-is-len
   (implies (natp n)
            (equal (fn-rcl-at-leastp n xs) (<= n (len xs))))
   :hints (("Goal" :in-theory (enable fn-rcl-at-leastp)))))

(local
 (defthm fn-nntp-tombstonep-unfolds
   (equal (fn-rcl-tombstonep payload)
          (and (<= *fn-rcl-tombstone-fixed* (len payload))
               (fn-rcl-prefixp *fn-rcl-magic* payload)))
   :hints (("Goal" :in-theory '(fn-rcl-tombstonep fn-nntp-rcl-at-leastp-is-len
                                 (:e natp))))))

;; An article's octet count, read through the arena in O(1) (the arena keeps
;; each payload's length; lane served-readers: OVER 1-2000 spent a third of
;; its time walking every payload to count it).  Logically the length of the
;; article's bytes.
(fn-payload-kind fn-nntp-article-length :handle "reads the arena at the handle")
(defun fn-nntp-article-length (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-nntp-payload-bytes
                                                     fn-nntp-article-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth)))))
  (mbe :logic (len (fn-nntp-article-bytes article fn-arena))
       :exec (let ((p (fn-article-payload article)))
               (if (and (natp p) (< p (fn-arena-count fn-arena)))
                   (fn-arena-payload-len p fn-arena)
                 (len (fn-nntp-article-bytes article fn-arena))))))

(fn-payload-kind fn-nntp-article-tombstonep :handle "reads the arena at the handle")
(defun fn-nntp-article-tombstonep (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :in-theory '(fn-nntp-tombstonep-unfolds
                                                     fn-nntp-payload-bytes
                                                     fn-nntp-article-bytes
                                                     fn-arena-payload-is-nth
                                                     fn-arena-count-is-len
                                                     fn-arena-payload-len-is-len-nth
                                                     fn-nntp-arena-prefixp-at-0)))))
  (mbe :logic (fn-rcl-tombstonep (fn-nntp-article-bytes article fn-arena))
       :exec (let ((p (fn-article-payload article)))
               (if (and (natp p) (< p (fn-arena-count fn-arena)))
                   (and (<= *fn-rcl-tombstone-fixed* (fn-arena-payload-len p fn-arena))
                        (fn-nntp-arena-prefixp *fn-rcl-magic* p 0 fn-arena))
                 (fn-rcl-tombstonep (fn-nntp-article-bytes article fn-arena))))))
