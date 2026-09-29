; post-identity-catalog-tests.lisp -- teeth for books/post-identity-catalog.lisp
; (the POST duplicate test's lookup through the catalog; lane join-f2-midx).
;
; The owner is tests/acl2/served-catalog-join-tests.lisp's owner after T
; (*scjt-o1*), the catalog loaded at recovery over its history under the
; view's own visibility, the arena holding T's payload at handle 0.
;
;   1. REACHABLE POSITIVE WITNESS of
;      fn-pidx-existing-action-cat-is-store-existing-action: the view's
;      visible list filters its raw list, the catalog is joined to the view,
;      the buffer holds T's bytes (the Store entry is given the same octets
;      as a list, the buffer's logical value); the catalog answers :duplicate for T's
;      Message-ID and groups, as the Store's entry does, and :conflict for
;      other groups, as the Store's entry does.
;   2. HYPOTHESIS REMOVAL (the join): the catalog loaded under an index that
;      hides T (T's row committed withdrawn) while the view shows it; the
;      visible-list relation and the buffer still hold, the join fails, and
;      the catalog answers nil where the Store answers :duplicate.

(in-package "ACL2")

(include-book "served-catalog-join-tests")
(include-book "../../books/post-identity-catalog")

(defconst *pict-groups* (fn-article-groups (car (fn-state-articles (fn-own-view-archive *scjt-view1*)))))

(defun pict-run (index1 groups fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arn-seal-many (list *ocr-t-bytes*) fn-arena))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store *scjt-o1*)))
                                        index1 fn-arena fn-cat))
         (fn-octets (fn-octets-from-list *ocr-t-bytes* fn-octets)))
    (mv (list (fn-ocl-view-visiblep *scjt-view1*)
              (scjt-joinp *scjt-view1* fn-arena fn-cat (scjt-rows-from 0 fn-cat))
              (fn-octets-p fn-octets)
              (fn-pidx-existing-action-cat "<lt@example>" fn-octets groups *scjt-o1* fn-arena fn-cat)
              (fn-store-existing-action "<lt@example>" *ocr-t-bytes* groups (fn-own-store *scjt-o1*) fn-arena))
        fn-octets fn-arena fn-cat)))

(defun pict-exec (index1 groups)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (pict-run index1 groups fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

;; 1. Every hypothesis; :duplicate from both, and :conflict from both.
(defconst *pict-1* (pict-exec (fn-own-view-index *scjt-view1*) *pict-groups*))
(assert-event (equal *pict-1* '(t t t :duplicate :duplicate)))
(defconst *pict-1c* (pict-exec (fn-own-view-index *scjt-view1*) '("other.group")))
(assert-event (equal *pict-1c* '(t t t :conflict :conflict)))

;; 2. The join removed: every other hypothesis holds, the answers differ.
(defconst *pict-2* (pict-exec (fn-midx-build nil) *pict-groups*))
(assert-event (equal *pict-2* '(t nil t nil :duplicate)))
