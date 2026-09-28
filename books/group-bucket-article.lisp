; Resolve a selected group's local number through its pinned membership bucket
; and the already pinned Message-ID trie.  This is a read-only derived lookup;
; the authoritative accepted archive remains the proof source.
(in-package "ACL2")
(include-book "group-bucket-index")

(defun fn-gidx-find-number-entry (group number entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (if (and (consp (car entries))
               (equal group (fn-index-entry-group (car entries)))
               (posp number)
               (equal number (fn-nntp-index-entry-available (car entries))))
          (car entries)
        (fn-gidx-find-number-entry group number (cdr entries)))
    nil))

(defun fn-gidx-entry-number-article (group number entries trie)
  (declare (xargs :guard t))
  (let ((entry (fn-gidx-find-number-entry
                group number entries)))
    (if (consp entry)
        (fn-midx-lookup (fn-index-entry-msgid entry) trie)
      nil)))

(defun fn-gidx-number-article (group number buckets trie)
  (declare (xargs :guard t))
  (fn-gidx-entry-number-article
   group number (fn-gidx-bucket group buckets) trie))

(defthm fn-gidx-find-number-entry-of-append
  (equal (fn-gidx-find-number-entry group number (append left right))
         (or (fn-gidx-find-number-entry group number left)
             (fn-gidx-find-number-entry group number right))))

(defthm fn-gidx-find-number-entry-of-select
  (equal (fn-gidx-find-number-entry group number
                                    (fn-gidx-select group entries))
         (fn-gidx-find-number-entry group number entries)))

(defthm fn-gidx-find-number-entry-of-built-bucket
  (equal (fn-gidx-find-number-entry group number
                                    (fn-gidx-bucket group
                                                    (fn-gidx-build articles)))
         (fn-gidx-find-number-entry group number
                                    (fn-index-build articles)))
  :hints (("Goal" :use ((:instance fn-gidx-bucket-of-build))
           :in-theory (disable fn-gidx-bucket-of-build))))

; The served number lookup (over-number-index, PRF-189): the entry at NUMBER
; from the bucket's number index, at most 31 trie steps, then the article
; from the pinned Message-ID trie.  `fn-nov-lines-for-numbers-numbered'
; (books/nntp-range-indexed.lisp) calls it once per OVER row.
(defun fn-gidx-nidx-number-article (number nidx trie)
  (declare (xargs :guard t))
  (let ((entry (fn-gnix-find number nidx)))
    (if (consp entry)
        (fn-midx-lookup (fn-index-entry-msgid entry) trie)
      nil)))

; The number index answers what the walk answers: the first entry of the
; list whose group is GROUP and whose available number is NUMBER.
(defthm fn-gnix-find-of-build
  (equal (fn-gnix-find number (fn-gnix-build group entries))
         (fn-gidx-find-number-entry group number entries)))

(defthm fn-gidx-nidx-number-article-of-build
  (equal (fn-gidx-nidx-number-article number (fn-gnix-build group entries)
                                      trie)
         (fn-gidx-entry-number-article group number entries trie))
  :hints (("Goal" :in-theory (disable fn-gnix-find fn-gnix-build))))

;  KEYSTONE (PRF-189).  Under the relation the group index carries
; (`fn-gidx-numbers-okp', established by every build and preserved by every
; put), the served lookup through GROUP's number index equals
; `fn-gidx-find-number-entry''s walk of GROUP's bucket followed by the same
; trie lookup.
(defthm fn-gidx-nidx-number-article-is-walk
  (implies (fn-gidx-numbers-okp buckets)
           (equal (fn-gidx-nidx-number-article
                   number (fn-gidx-bucket-numbers group buckets) trie)
                  (fn-gidx-entry-number-article
                   group number (fn-gidx-bucket group buckets) trie)))
  :hints (("Goal" :in-theory (disable fn-gidx-nidx-number-article
                                      fn-gidx-entry-number-article
                                      fn-gnix-build fn-gidx-bucket
                                      fn-gidx-bucket-numbers
                                      fn-gidx-numbers-okp))))
