; owner-view-catalog-lookup.lisp -- the owner view's Message-ID lookup is the
; catalog's column walk (lane s-viewidx, 2026-10-08; P1 of
; planning/design/owner-view-index-removal-2026-10-08.md).
;
; Under the join (fn-scj-joinp: the catalog's visible rows at its count are
; the view's archive articles), the article the view's archive holds for a
; Message-ID is the row article of the newest visible row of the id's
; column.  The statement is about existing functions only; it is the
; replacement for every read of the view's trie (fn-own-view-index) that
; asks which article a Message-ID names among the shown ones.  The trie's
; own value is fn-find-article (fn-midx-lookup-is-find-article); this
; theorem leaves no trie premise.

(in-package "ACL2")

(include-book "served-catalog-join")

(defthm fn-owner-view-lookup-is-the-catalog-walk
  (implies (fn-scj-joinp view fn-arena fn-cat)
           (equal (fn-find-article m (fn-state-articles (fn-own-view-archive view)))
                  (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs m fn-cat)
                                                       (fn-cat-count fn-cat) fn-cat)))
                    (if seq (fn-cat-row-article seq fn-arena fn-cat) nil))))
  :hints (("Goal" :in-theory (e/d (fn-scj-joinp fn-cat-view-articles)
                                  (fn-cat-view-below fn-cat-view-find fn-cat-view-last-visible
                                   fn-cat-row-article fn-cat-msgid-seqs))
           :use ((:instance fn-cat-view-find-article-is-walk
                            (msgid m) (i (fn-cat-count fn-cat)) (v (fn-cat-count fn-cat)))
                 (:instance fn-cat-view-find-is-msgid-column
                            (msgid m) (v (fn-cat-count fn-cat)))))))
