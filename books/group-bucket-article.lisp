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
