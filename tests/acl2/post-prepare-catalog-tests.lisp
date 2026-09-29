; post-prepare-catalog-tests.lisp -- teeth for books/post-prepare-catalog.lisp
; (a POST's prepare with its duplicate test read from the catalog; lane
; join-f2-midx).

(in-package "ACL2")

(include-book "post-identity-index-tests")
(include-book "../../books/post-prepare-catalog")

; The owner is post-identity-index-tests' (*pit-oc*: two articles, <one> and
; <two>, the Store :reserved); the catalog is recovery's load of its history
; under the view's own visibility; the carry is the host's first-POST carry
; (fn-prc-refresh of nil at the node's ledger).  The acceptance's articles
; carry arena handles, so the load and the row reads need no arena bytes.

(defun ppct-carry (oc)
  (fn-prc-refresh nil (fn-node-retention (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))))

(defun ppct-run (index record fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((o (fn-ocfg-owner *pit-oc*))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        index fn-arena fn-cat))
         (carry (ppct-carry *pit-oc*))
         (dup (fn-pidx-find-article-cat
               (fn-record-msgid record)
               (fn-state-articles (fn-node-acceptance (fn-sn-node (fn-own-store o))))
               (fn-own-view o) fn-arena fn-cat)))
    (mv-let (word next)
      (fn-ppc-pout-prepare-article-cat *pit-oc* record 100 carry fn-arena fn-cat)
      (mv-let (rword rnext)
        (fn-pout-prepare-article *pit-oc* record 100 carry)
        (mv (list (fn-pidx-view-okp (fn-own-view o))
                  (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                         (fn-state-articles (fn-own-view-archive (fn-own-view o))))
                  (fn-prc-carryp carry)
                  (fn-ppc-dup-okp (fn-own-store o) record dup)
                  word rword (equal next rnext))
            fn-arena fn-cat)))))

(defun ppct-exec (index record)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (ppct-run index record fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; Each result: (view facts, join at the count, carry recognizer, the guard's
; dup fact, the word, the reference's word, the owners equal).

;; 1. REACHABLE POSITIVE WITNESSES of
;; fn-ppc-pout-prepare-article-cat-is-pout-prepare-article: every hypothesis
;; holds; a fresh Message-ID stages (:prepared) and a held one is refused by
;; the duplicate test, both values equal to the reference's.
(assert-event (equal (ppct-exec (fn-own-view-index *pit-view*) *pit-fresh-record*)
                     '(t t t t :prepared :prepared t)))
(assert-event (equal (ppct-exec (fn-own-view-index *pit-view*) *pit-dup-record*)
                     '(t t t t :refused :refused t)))

;; 2. HYPOTHESIS REMOVAL (the join): the catalog loaded under an index that
;; shows nothing (every row committed withdrawn); the view facts and the
;; carry hold, the join and the guard's dup fact fail, and the catalog's
;; prepare stages the duplicate the reference refuses.
(assert-event (equal (ppct-exec (fn-midx-build nil) *pit-dup-record*)
                     '(t nil t nil :prepared :refused nil)))
