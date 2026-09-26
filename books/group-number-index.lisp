; A group's entries keyed by local article number (over-number-index, PRF-189).
;
; A persistent binary trie over the number's bits, least significant first,
; ending at the leading 1: a number <= 2^31 - 1 (RFC 3977 section 6) is at
; most 31 levels deep, so a lookup costs at most 31 steps whatever the size of
; the group.  A node is (value zero . one).  `fn-gnix-add' decides an entry's
; availability -- its number and its Message-ID (`fn-nntp-index-entry-
; available') -- once, when the entry is added; a lookup never re-decides it.
; `fn-gnix-build' adds the entries last first, so the first entry of a list
; wins a number, as `fn-gidx-find-number-entry''s walk does
; (books/group-bucket-article.lisp, `fn-gnix-find-of-build').
(in-package "ACL2")
(include-book "nntp-index-runtime")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gnix-val (node)
  (declare (xargs :guard t))
  (fn-ag-car node))

(defun fn-gnix-zero (node)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr node)))

(defun fn-gnix-one (node)
  (declare (xargs :guard t))
  (fn-ag-cdr (fn-ag-cdr node)))

; The root holds 1 (and every non-number, which no caller asks for); above
; it, the low bit picks the child and the rest of the number goes down.
(defun fn-gnix-get (n node)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((not (consp node)) nil)
        ((or (not (integerp n)) (<= n 1)) (fn-gnix-val node))
        ((evenp n) (fn-gnix-get (floor n 2) (fn-gnix-zero node)))
        (t (fn-gnix-get (floor n 2) (fn-gnix-one node)))))

(defun fn-gnix-set (n value node)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((or (not (integerp n)) (<= n 1))
         (cons value (fn-ag-cdr node)))
        ((evenp n)
         (cons (fn-gnix-val node)
               (cons (fn-gnix-set (floor n 2) value (fn-gnix-zero node))
                     (fn-gnix-one node))))
        (t
         (cons (fn-gnix-val node)
               (cons (fn-gnix-zero node)
                     (fn-gnix-set (floor n 2) value (fn-gnix-one node)))))))

(defun fn-gnix-find (number node)
  (declare (xargs :guard t))
  (if (posp number) (fn-gnix-get number node) nil))

; The key of ENTRY in GROUP's index: its available number, or 0 (not
; indexed) for an entry of another group, a non-entry, or an entry whose
; number or Message-ID is not valid.
(defun fn-gnix-key (group entry)
  (declare (xargs :guard t))
  (if (and (consp entry)
           (equal group (fn-index-entry-group entry)))
      (fn-nntp-index-entry-available entry)
    0))

(defun fn-gnix-add (group entry node)
  (declare (xargs :guard t))
  (let ((key (fn-gnix-key group entry)))
    (if (posp key) (fn-gnix-set key entry node) node)))

(defun fn-gnix-build (group entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-gnix-add group (car entries) (fn-gnix-build group (cdr entries)))
    nil))

(defthm fn-gnix-get-of-nil
  (equal (fn-gnix-get n nil) nil))

(local
 (defun fn-gnix-get-set-induct (n m node)
   (declare (xargs :measure (nfix n)))
   (cond ((or (not (integerp n)) (<= n 1)) (list m node))
         ((or (not (integerp m)) (<= m 1)) (list n node))
         ((evenp n)
          (fn-gnix-get-set-induct (floor n 2) (floor m 2) (fn-gnix-zero node)))
         (t (fn-gnix-get-set-induct (floor n 2) (floor m 2) (fn-gnix-one node))))))

; The trie is a map: reading a number after setting one reads the value set
; when they are the same number and the old value otherwise.
(defthm fn-gnix-get-of-set
  (implies (and (posp n) (posp m))
           (equal (fn-gnix-get n (fn-gnix-set m value node))
                  (if (equal n m) value (fn-gnix-get n node))))
  :hints (("Goal" :induct (fn-gnix-get-set-induct n m node)
           :in-theory (enable fn-gnix-get fn-gnix-set))))
