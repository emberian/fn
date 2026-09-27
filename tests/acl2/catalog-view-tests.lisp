; fn: teeth for books/catalog-view.lisp (wave 5, lane catalog-slice step 7
; groundwork).
;
; What this book is evidence FOR.  `fn-cat-view-find-article-is-walk',
; `fn-cat-view-number-entry-is-walk' and `fn-cat-view-number-article-is-row':
; over the view a version pins (the visible rows, newest first, as acceptance
; articles), the Message-ID trie's lookup and the group bucket's number lookup
; -- the two reads the served machine runs today -- are walks of the visible
; rows, so the catalog's columns answer them.  The exec path builds the view
; on live stobjs from a mixed history and runs the machine's own lookups
; (fn-midx-lookup of fn-midx-build, fn-gidx-number-article of fn-gidx-build)
; against the walks; then a withdrawal shows the version semantics on the view
; (the target stays in the view at the version before the cancel, leaves it
; after).  The keystones get ground witnesses with their complete antecedents
; and the hypothesis-removal witness the composed lookup needs: a second
; visible row with the same Message-ID (production acceptance excludes it;
; the catalog does not) makes the trie answer the newer row.

(in-package "ACL2")
(include-book "../../books/catalog-view")
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (and (eq (symbol-class 'fn-cat-row-article (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-below (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-articles (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-find (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-bound-find (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-view-msgids-okp (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The mixed history of the relation tests: an article, a retention event, an
; article; both articles in fn.test (numbers 1 and 2).

(defconst *cvt-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *cvt-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *cvt-w0* (fn-record-make 0 1 1 "<a@x>" *cvt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *cvt-r1* (fn-store-retention-event-make :undertake 1 2 2 "id" "subject" "evidence" 3))
(defconst *cvt-w2* (fn-record-make 2 3 3 "<c@x>" *cvt-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *cvt-h* (list *cvt-w0* *cvt-r1* *cvt-w2*))

; -----------------------------------------------------------------------------
; The exec path: the view on live stobjs, the machine's lookups against the
; walks, and the version semantics after a withdrawal.

(defun cvt-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *cvt-h* nil 0 fn-arena fn-cat)
      (let* ((view (fn-cat-view-articles 2 fn-arena fn-cat))
             (trie (fn-midx-build view))
             (buckets (fn-gidx-build view))
             (by-msgid (fn-midx-lookup "<c@x>" trie))
             (walk-msgid (fn-cat-view-find "<c@x>" 2 2 fn-cat))
             (by-number (fn-gidx-number-article "fn.test" 2 buckets trie))
             (walk-number (fn-cat-view-bound-find "fn.test" 2 2 2 fn-cat))
             (loaded (list (len view)
                           (fn-article-msgid (car view))            ; newest first
                           (equal by-msgid (fn-cat-row-article walk-msgid fn-arena fn-cat))
                           walk-msgid
                           (equal by-number (fn-cat-row-article walk-number fn-arena fn-cat))
                           walk-number
                           (fn-article-payload by-number)          ; the row's handle
                           (fn-nntp-article-bytes by-number fn-arena) ; the bytes a reader serves
                           (fn-cat-view-msgids-okp 2 2 fn-cat)
                           (fn-midx-lookup "<zz@x>" trie)          ; absent
                           (fn-gidx-number-article "fn.test" 3 buckets trie)))
             ; the cancel of row 0 committed when the count is 2
             (fn-cat (fn-cat-withdraw 0 9 fn-cat))
             (after (list (len (fn-cat-view-articles 2 fn-arena fn-cat))   ; pinned before the cancel: still 2
                          (len (fn-cat-view-articles 3 fn-arena fn-cat))   ; advanced past it: 1
                          (fn-cat-view-find "<a@x>" 2 2 fn-cat)            ; row 0 at version 2
                          (fn-cat-view-find "<a@x>" 2 3 fn-cat))))         ; gone at version 3
        (mv (list loaded after) fn-arena fn-cat)))))

(defun cvt-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cvt-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event
 (equal (cvt-exec)
        (list (list 2 "<c@x>" t 1 t 1 1 *cvt-p2* t nil nil)
              (list 2 1 0 nil))))

; -----------------------------------------------------------------------------
; The loaded state on the logical side (as catalog-relation-tests builds it).

(defconst *cvt-a* (list *cvt-p0* *cvt-p2*))
(defun cvt-held (w handle)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) nil nil))
(defconst *cvt-c*
  (list (fn-cat-assign (cvt-held *cvt-w0* 0) nil)
        (fn-cat-assign (cvt-held *cvt-w2* 1) (list (fn-cat-assign (cvt-held *cvt-w0* 0) nil)))))

(defthm cvt-w-loaded-is-the-fold
  (mv-let (a c)
    (fn-cat-load *cvt-h* nil 0 nil nil)
    (and (equal a *cvt-a*) (equal c *cvt-c*)))
  :rule-classes nil)

; KEYSTONE 1, reachable and non-degenerate: the walk finds row 1 and the
; trie's article is that row's.
(defthm cvt-w-find-article
  (and (equal (fn-cat-view-find "<c@x>" 2 2 *cvt-c*) 1)
       (equal (fn-find-article "<c@x>" (fn-cat-view-below 2 2 *cvt-a* *cvt-c*))
              (fn-cat-row-article 1 *cvt-a* *cvt-c*))
       (consp (fn-cat-row-article 1 *cvt-a* *cvt-c*))
       ; the article carries row 1's handle; a reader serves its bytes by the arena
       (equal (fn-article-payload (fn-cat-row-article 1 *cvt-a* *cvt-c*)) 1)
       (equal (fn-nntp-article-bytes (fn-cat-row-article 1 *cvt-a* *cvt-c*) *cvt-a*) *cvt-p2*))
  :rule-classes nil)

; KEYSTONE 3, the complete antecedent then the conclusion.
(defthm cvt-w-number-article
  (and (posp 2) (<= 2 *fn-nntp-max-article-number*)
       (fn-cat-view-msgids-okp 2 2 *cvt-c*)
       (fn-midx-string-article-listp (fn-cat-view-below 2 2 *cvt-a* *cvt-c*))
       (equal (fn-cat-view-bound-find "fn.test" 2 2 2 *cvt-c*) 1)
       (equal (fn-cat-view-find (fn-record-msgid (fn-cat-at 1 *cvt-c*)) 2 2 *cvt-c*) 1)
       (equal (fn-gidx-entry-number-article
               "fn.test" 2
               (fn-index-build (fn-cat-view-below 2 2 *cvt-a* *cvt-c*))
               (fn-midx-build (fn-cat-view-below 2 2 *cvt-a* *cvt-c*)))
              (fn-cat-row-article 1 *cvt-a* *cvt-c*)))
  :rule-classes nil)

; HYPOTHESIS REMOVAL (the Message-ID names no newer visible row): a third row
; with the SAME Message-ID as row 1 (the catalog admits it; the acceptance
; kernel refuses a duplicate).  Every retained hypothesis holds, the omitted
; one fails (the walk for <c@x> finds row 2), and the conclusion fails: the
; composed lookup for fn.test number 2 answers row 2's article, not row 1's.
(defconst *cvt-w3* (fn-record-make 3 4 4 "<c@x>" *cvt-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *cvt-a3* (append *cvt-a* (list *cvt-p0*)))
; the commit's logical value (fn-cat-commit-is-append): the row appended
; with its numbers assigned one past fn.test's high (3).
(defconst *cvt-c3* (append *cvt-c* (list (fn-cat-assign (cvt-held *cvt-w3* 2) *cvt-c*))))
(defthm cvt-w-number-article-without-uniqueness
  (and (posp 2) (<= 2 *fn-nntp-max-article-number*)
       (fn-cat-view-msgids-okp 3 3 *cvt-c3*)
       (fn-midx-string-article-listp (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*))
       (equal (fn-cat-view-bound-find "fn.test" 2 3 3 *cvt-c3*) 1)
       (not (equal (fn-cat-view-find (fn-record-msgid (fn-cat-at 1 *cvt-c3*)) 3 3 *cvt-c3*) 1))
       (equal (fn-cat-view-find (fn-record-msgid (fn-cat-at 1 *cvt-c3*)) 3 3 *cvt-c3*) 2)
       (not (equal (fn-gidx-entry-number-article
                    "fn.test" 2
                    (fn-index-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*))
                    (fn-midx-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*)))
                   (fn-cat-row-article 1 *cvt-a3* *cvt-c3*)))
       (equal (fn-gidx-entry-number-article
               "fn.test" 2
               (fn-index-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*))
               (fn-midx-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*)))
              (fn-cat-row-article 2 *cvt-a3* *cvt-c3*)))
  :rule-classes nil)
(must-fail
 (defthm cvt-r-number-article-without-uniqueness
   (equal (fn-gidx-entry-number-article
           "fn.test" 2
           (fn-index-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*))
           (fn-midx-build (fn-cat-view-below 3 3 *cvt-a3* *cvt-c3*)))
          (fn-cat-row-article 1 *cvt-a3* *cvt-c3*))
   :rule-classes nil))

; HYPOTHESIS REMOVAL (N a served number): N above *fn-nntp-max-article-number*
; is never available to the walk (fn-nntp-index-entry-available answers 0),
; while a row may bind it: the entry lookup answers nil, the walk the row.
(defconst *cvt-big* (+ 1 *fn-nntp-max-article-number*))
(defconst *cvt-c-big*
  (list (fn-held-with-numbers (cvt-held *cvt-w0* 0) (list (cons "fn.test" *cvt-big*)))))
(defthm cvt-w-number-entry-above-max
  (and (posp *cvt-big*) (not (<= *cvt-big* *fn-nntp-max-article-number*))
       (fn-cat-view-msgids-okp 1 1 *cvt-c-big*)
       (equal (fn-cat-view-bound-find "fn.test" *cvt-big* 1 1 *cvt-c-big*) 0)
       (equal (fn-gidx-find-number-entry
               "fn.test" *cvt-big* (fn-index-build (fn-cat-view-below 1 1 *cvt-a* *cvt-c-big*)))
              nil))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; KEYSTONE 4 (the column): on live stobjs, and on the duplicate catalog where
; the column lists two seqs and the newer visible one is the answer.

(defun cvt-run-column (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *cvt-h* nil 0 fn-arena fn-cat)
      (mv (list (fn-cat-msgid-seqs "<c@x>" fn-cat)
                (fn-cat-view-last-visible (fn-cat-msgid-seqs "<c@x>" fn-cat) 2 fn-cat)
                (fn-cat-view-find "<c@x>" (fn-cat-count fn-cat) 2 fn-cat)
                (fn-cat-view-last-visible (fn-cat-msgid-seqs "<c@x>" fn-cat) 1 fn-cat)   ; not yet visible at 1
                (fn-cat-view-last-visible (fn-cat-msgid-seqs "<zz@x>" fn-cat) 2 fn-cat))
          fn-arena fn-cat))))

(defun cvt-exec-column ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (cvt-run-column fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event (equal (cvt-exec-column) (list '(1) 1 1 nil nil)))

(defthm cvt-w-msgid-column
  (and (equal (fn-cat-msgid-seqs "<c@x>" *cvt-c3*) '(1 2))
       (equal (fn-cat-view-last-visible (fn-cat-msgid-seqs "<c@x>" *cvt-c3*) 3 *cvt-c3*) 2)
       (equal (fn-cat-view-find "<c@x>" (fn-cat-count *cvt-c3*) 3 *cvt-c3*) 2)
       ; row 2 withdrawn at version 3: the column's newest visible seq falls back to 1
       (equal (fn-cat-view-last-visible (fn-cat-msgid-seqs "<c@x>" (fn-cat-withdraw 2 7 *cvt-c3*)) 4
                                        (fn-cat-withdraw 2 7 *cvt-c3*))
              1)
       (equal (fn-cat-view-find "<c@x>" (fn-cat-count (fn-cat-withdraw 2 7 *cvt-c3*)) 4
                                (fn-cat-withdraw 2 7 *cvt-c3*))
              1))
  :rule-classes nil)
