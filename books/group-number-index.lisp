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
(include-book "group-number-trie")
(local (include-book "arithmetic-5/top" :dir :system))

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

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-gnix-add)
                    (:definition fn-gnix-build)
                    (:definition fn-gnix-key)
                    (:definition fn-gnix-set)))
