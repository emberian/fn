; fn: the Message-ID trie walked by string index.
;
; fn-midx-lookup (books/msgid-index.lisp) converts the Message-ID to its
; character list (fn-midx-key-chars: a coerce, one cons per character) and
; walks the list down the trie; fn-midx-extend converts it again to insert.
; This book is the same trie, with the same nodes (association lists keyed
; by character, the terminal value under *fn-midx-value-key*), walked by
; index into the string: (char msgid i) at depth i, nothing allocated on a
; lookup.  The logical trie does not move: fn-midx-build,
; fn-midx-correspondencep and every theorem over them keep their
; statements, and the concrete functions here are proved EQUAL to their
; references on every input, with no hypothesis:
;
;   fn-midx-concrete-lookup-is-lookup   (fn-mxc-lookup msgid trie)   = (fn-midx-lookup msgid trie)
;   fn-midx-concrete-extend-is-extend   (fn-mxc-extend article trie) = (fn-midx-extend article trie)
;   fn-midx-concrete-build-is-build     (fn-mxc-build articles)      = (fn-midx-build articles)
;   fn-midx-concrete-refresh-is-refresh (fn-mxc-refresh ...)          = (fn-midx-refresh ...)
;
; so (fn-midx-correspondencep (fn-mxc-build articles) articles) holds, and
; a trie built or extended here is the trie the invariants speak of.  The
; lookup is reached on the served path through books/peer-offer-indexed.lisp
; (fn-pix-history-hasp, the IHAVE/CHECK history test, and
; fn-pix-msgid-retrieval-indexed, the ARTICLE/HEAD/BODY/STAT retrieval).
; fn-mxc-extend, -build and -refresh have no host caller yet: the owner's
; refresh (books/owner.lisp fn-own-refresh) calls fn-midx-refresh, which
; converts one Message-ID per accepted article; rerouting it is a twin of
; fn-own-refresh under every owner transition, a freeze item.
;
; The nodes stay association lists.  A node's branch scan is bounded by the
; distinct characters that follow its prefix (fn-midx-unique-branchesp);
; an array node of 256 slots per character would cost 2 KiB per node on
; SBCL against the 16 bytes per branch of the alist, for a Message-ID
; alphabet that in practice branches a handful of ways per node.

(in-package "ACL2")
(include-book "msgid-index")

; -----------------------------------------------------------------------------
; The walk by index.

(defun fn-mxc-get (msgid i trie)
  (declare (xargs :guard (and (stringp msgid) (natp i))
                  :measure (nfix (- (length msgid) (nfix i)))))
  (if (and (mbt (and (stringp msgid) (natp i)))
           (< i (length msgid)))
      (fn-mxc-get msgid (1+ i) (fn-midx-branch-get (char msgid i) trie))
    (fn-midx-branch-get *fn-midx-value-key* trie)))

(defun fn-mxc-lookup (msgid trie)
  (declare (xargs :guard t))
  (if (stringp msgid) (fn-mxc-get msgid 0 trie) nil))

(defun fn-mxc-put (msgid i article trie)
  (declare (xargs :guard (and (stringp msgid) (natp i))
                  :measure (nfix (- (length msgid) (nfix i)))))
  (if (and (mbt (and (stringp msgid) (natp i)))
           (< i (length msgid)))
      (let ((key (char msgid i)))
        (fn-midx-branch-put
         key
         (fn-mxc-put msgid (1+ i) article (fn-midx-branch-get key trie))
         trie))
    (fn-midx-branch-put *fn-midx-value-key* article trie)))

(defun fn-mxc-extend (article trie)
  (declare (xargs :guard t))
  (let ((msgid (fn-article-msgid article)))
    (if (stringp msgid)
        (fn-mxc-put msgid 0 article trie)
      (fn-midx-branch-put *fn-midx-value-key* article trie))))

(defun fn-mxc-build (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (fn-mxc-extend (fn-ag-car articles) (fn-mxc-build (fn-ag-cdr articles)))
    nil))

(defun fn-mxc-refresh (index old-articles new-articles)
  (declare (xargs :guard t))
  (cond ((equal new-articles old-articles) index)
        ((and (consp new-articles)
              (equal (fn-ag-cdr new-articles) old-articles))
         (fn-mxc-extend (fn-ag-car new-articles) index))
        (t (fn-mxc-build new-articles))))

; -----------------------------------------------------------------------------
; The correspondence.  Character I of the string is element I of its
; character list, and the walk from I is the list walk from (nthcdr I ...).

(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-mxc-len-coerce-is-length
  (implies (stringp s) (equal (len (coerce s 'list)) (length s)))))

(local (defthm fn-mxc-shift-less
  (implies (and (integerp i) (integerp n))
           (equal (< (+ -1 i) n) (< i (+ 1 n))))
  :hints (("Goal" :cases ((< i (+ 1 n)))))))

(local (defthm fn-mxc-consp-of-nthcdr
  (implies (natp i)
           (equal (consp (nthcdr i l)) (< i (len l))))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr len)))))

(local (defthm fn-mxc-car-of-nthcdr
  (equal (car (nthcdr i l)) (nth i l))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr nth)))))

(local (defthm fn-mxc-cdr-of-nthcdr
  (implies (natp i)
           (equal (cdr (nthcdr i l)) (nthcdr (+ 1 i) l)))
  :hints (("Goal" :induct (nthcdr i l) :in-theory (enable nthcdr)))))

(local (defthm fn-mxc-char-is-nth
  (equal (char s i) (nth i (coerce s 'list)))
  :hints (("Goal" :in-theory (enable char)))))

(local (in-theory (disable nth nthcdr)))

; The index lemmas: the only statements here with a hypothesis, and local.
; (natp i) is needed: at i = -1 the walk looks up the terminal slot of the
; root and the list walk (nthcdr's zp case) walks the whole key
; (tests/acl2/msgid-index-concrete-tests.lisp).  (stringp msgid) is not: a
; non-string has the empty character list, and both walks read the root's
; terminal slot.
(local (defthm fn-mxc-get-is-get-chars-of-nthcdr
  (implies (natp i)
           (equal (fn-mxc-get msgid i trie)
                  (fn-midx-get-chars (nthcdr i (coerce msgid 'list)) trie)))
  :hints (("Goal" :induct (fn-mxc-get msgid i trie)
           :expand ((fn-midx-get-chars (nthcdr i (coerce msgid 'list)) trie))))))

(local (defthm fn-mxc-put-is-put-chars-of-nthcdr
  (implies (natp i)
           (equal (fn-mxc-put msgid i article trie)
                  (fn-midx-put-chars (nthcdr i (coerce msgid 'list)) article trie)))
  :hints (("Goal" :induct (fn-mxc-put msgid i article trie)
           :expand ((fn-midx-put-chars (nthcdr i (coerce msgid 'list)) article trie))))))

; KEYSTONE.  The lookup by index is the trie lookup, for every Message-ID
; and every trie.
(defthm fn-midx-concrete-lookup-is-lookup
  (equal (fn-mxc-lookup msgid trie) (fn-midx-lookup msgid trie))
  :hints (("Goal" :in-theory (enable fn-mxc-lookup fn-midx-lookup fn-midx-key-chars nthcdr))))

(defthm fn-midx-concrete-extend-is-extend
  (equal (fn-mxc-extend article trie) (fn-midx-extend article trie))
  :hints (("Goal" :in-theory (enable fn-mxc-extend fn-midx-extend fn-midx-key-chars nthcdr))))

(defthm fn-midx-concrete-build-is-build
  (equal (fn-mxc-build articles) (fn-midx-build articles))
  :hints (("Goal" :induct (fn-mxc-build articles)
           :in-theory (e/d (fn-mxc-build fn-midx-build) (fn-mxc-extend fn-midx-extend)))))

(defthm fn-midx-concrete-refresh-is-refresh
  (equal (fn-mxc-refresh index old-articles new-articles)
         (fn-midx-refresh index old-articles new-articles))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-mxc-refresh fn-midx-refresh
                                fn-midx-concrete-extend-is-extend
                                fn-midx-concrete-build-is-build)
                              (theory 'minimal-theory)))))

; The trie invariant the owner carries, stated of the concrete build.
(defthm fn-midx-concrete-build-corresponds
  (fn-midx-correspondencep (fn-mxc-build articles) articles)
  :hints (("Goal" :in-theory (enable fn-midx-correspondencep))))

(in-theory (disable fn-mxc-get fn-mxc-lookup fn-mxc-put fn-mxc-extend
                    fn-mxc-build fn-mxc-refresh))
