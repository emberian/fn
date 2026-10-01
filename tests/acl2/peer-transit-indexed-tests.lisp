; peer-transit-indexed-tests.lisp -- teeth for books/peer-transit-indexed.lisp
; (the relay transfer decision's history test read from the catalog; lane
; served-incremental-1).
;
; The owner is post-identity-index-tests' (*pit-oc*: two accepted articles,
; <one@example> among them); the catalog is recovery's load of its history
; under an index (the view's own, or one that shows nothing), as
; post-prepare-catalog-tests loads it.

(in-package "ACL2")

(include-book "post-identity-index-tests")
(include-book "../../books/peer-transit-indexed")

(defun ptit-run (index msgid fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((o (fn-ocfg-owner *pit-oc*))
         (node (fn-sn-node (fn-own-store o)))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        index fn-arena fn-cat)))
    (mv (list (fn-node-statep node)
              (fn-ocl-view-visiblep (fn-own-view o))
              (fn-scj-joinp (fn-own-view o) fn-arena fn-cat)
              (fn-peer-history-hasp-cat msgid node (fn-own-view o) fn-arena fn-cat)
              (fn-peer-history-hasp msgid node))
        fn-arena fn-cat)))

(defun ptit-exec (index msgid)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (ptit-run index msgid fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; Each result: (node invariant, view visible, join, the catalog's history
; answer, the reference's answer).

;; 1. REACHABLE POSITIVE WITNESSES of fn-peer-history-hasp-cat-is-history-hasp:
;; every hypothesis holds; a held Message-ID is in the history and a fresh
;; one is not, each equal to the reference's walk.
(assert-event (equal (ptit-exec (fn-own-view-index *pit-view*) *pit-held*)
                     '(t t t t t)))
(assert-event (equal (ptit-exec (fn-own-view-index *pit-view*) *pit-fresh*)
                     '(t t t nil nil)))

;; 2. HYPOTHESIS REMOVAL (the join): the catalog loaded under an index that
;; shows nothing; the node invariant and the view hold, the join fails, and
;; the catalog misses the held article the reference finds.
(assert-event (equal (ptit-exec (fn-midx-build nil) *pit-held*)
                     '(t t nil nil t)))
