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
(include-book "peer-inbound-tests")
(include-book "../../books/peer-transit-indexed")

(defun ptit-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (ptit-rows-of (+ 1 i) fn-cat))
    nil))

(defun ptit-run (index msgid fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((o (fn-ocfg-owner *pit-oc*))
         (node (fn-sn-node (fn-own-store o)))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        index fn-arena fn-cat)))
    (mv (list (fn-node-statep node)
              ;; the view hypothesis (fn-pidx-view-okp includes
              ;; fn-ocl-view-visiblep) and the join's three conjuncts
              ;; (fn-scj-joinp is a defun-nx, its body read executably)
              (fn-pidx-view-okp (fn-own-view o))
              (let ((c (ptit-rows-of 0 fn-cat)))
                (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                            (fn-state-articles (fn-own-view-archive (fn-own-view o))))
                     (fn-scj-marks-below c (fn-cat-count fn-cat))
                     (fn-scj-seqs-below c (fn-own-view-version (fn-own-view o)))))
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

; Each result: (node invariant, view facts, join at the count, the catalog's history
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

;; -----------------------------------------------------------------------------
;; The whole transfer decision (fn-peer-decide-transfer-cat-is-decide-transfer,
;; fn-peer-decide-transfer-under-cat-is-under, fn-pta-decide-cat-is-pta-decide):
;; peer-inbound-tests' configuration (*pt-cfg*, peer innA feeding fn.*) over
;; the owner above.  The catalog's rows are read back for the join's two
;; executable conjuncts beside its equation.

; An article as *pt-noloop* with its own Message-ID.
(defun ptit-article (msgid)
  (declare (xargs :mode :program))
  (fn-post-body-octets
   (pt-lines (list "Path: inn.hbox.test!origin!not-for-mail" "From: poster@example.invalid"
                   "Newsgroups: fn.letters" "Subject: loop" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
                   (concatenate 'string "Message-ID: " msgid) "" "Round and round."))))

(defconst *ptit-limits* '(64 64 65536))

(defun ptit-dec-run (index msgid carry-of fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((o (fn-ocfg-owner *pit-oc*))
         (node (fn-sn-node (fn-own-store o)))
         (view (fn-own-view o))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store o)))
                                        index fn-arena fn-cat))
         (c (ptit-rows-of 0 fn-cat))
         (carry (if (eq carry-of :fresh)
                    (fn-prc-refresh nil (fn-node-retention node))
                  carry-of))
         (mid (pt-o msgid))
         (octets (ptit-article msgid)))
    (mv (list (list (fn-node-statep node)
                    (fn-pidx-view-okp view)
                    (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                                (fn-state-articles (fn-own-view-archive view)))
                         (fn-scj-marks-below c (fn-cat-count fn-cat))
                         (fn-scj-seqs-below c (fn-own-view-version view)))
                    (fn-prc-carryp carry))
              (fn-peer-decide-transfer-cat node *pt-cfg* "innA" mid octets nil "ob" "s"
                                           view carry fn-arena fn-cat)
              (fn-peer-decide-transfer node *pt-cfg* "innA" mid octets nil "ob" "s")
              (fn-peer-decide-transfer-under-cat node *pt-cfg* "innA" mid octets nil "ob" "s"
                                                 *ptit-limits* view carry fn-arena fn-cat)
              (fn-peer-decide-transfer-under node *pt-cfg* "innA" mid octets nil "ob" "s" *ptit-limits*)
              (mv-list 2 (fn-pta-decide-cat nil nil nil nil node *pt-cfg* "innA" mid octets nil "ob" "s"
                                            *ptit-limits* view carry fn-arena fn-cat))
              (mv-list 2 (fn-pta-decide nil nil nil nil node *pt-cfg* "innA" mid octets nil "ob" "s" *ptit-limits*)))
        fn-arena fn-cat)))

(defun ptit-dec (index msgid carry-of)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (ptit-dec-run index msgid carry-of fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *ptit-ok-index* (fn-own-view-index *pit-view*))
(defconst *ptit-node* (fn-sn-node (fn-own-store (fn-ocfg-owner *pit-oc*))))

; Each result: ((node invariant, view, join, carry), the -cat decision, the
; reference, the -under-cat decision, its reference, fn-pta-decide-cat's two
; values, fn-pta-decide's).

;; 3. REACHABLE POSITIVE WITNESSES of the three transfer equalities, all four
;; hypotheses holding: a fresh article is wanted (the verdict :ungoverned:
;; no group here is governed) and a held one is had, each equal to the
;; reference at every level.
(assert-event (equal (ptit-dec *ptit-ok-index* "<fresh7@example>" :fresh)
                     '((t t t t)
                       (:want nil) (:want nil) (:want nil) (:want nil)
                       ((:want nil) :ungoverned) ((:want nil) :ungoverned))))
(assert-event (equal (ptit-dec *ptit-ok-index* *pit-held* :fresh)
                     '((t t t t)
                       (:have :history) (:have :history) (:have :history) (:have :history)
                       ((:have :history) :none) ((:have :history) :none))))

;; 4. HYPOTHESIS REMOVAL (fn-prc-carryp), CORRUPTED STATE: a carry whose trie
;; is another ledger's (it holds the obligation id "ob", the node's ledger
;; does not).  The node, the view and the join hold, the carry does not, and
;; the -cat decision refuses :capacity where the reference wants.
(assert-event (equal (ptit-dec *ptit-ok-index* "<fresh7@example>"
                               (cons (fn-node-retention *ptit-node*)
                                     (cdr (fn-prc-refresh nil (list 10 4 (list (list "ob" "s" :archive "own-release:x" 2)) nil)))))
                     '((t t t nil)
                       (:refuse :capacity) (:want nil) (:refuse :capacity) (:want nil)
                       ((:refuse :capacity) :none) ((:want nil) :ungoverned))))

;; 5. HYPOTHESIS REMOVAL (fn-scj-joinp) for the transfer decision: the catalog
;; under an index that shows nothing; node, view and carry hold, the join
;; fails, and a held article is wanted where the reference has it.
(assert-event (equal (ptit-dec (fn-midx-build nil) *pit-held* :fresh)
                     '((t t nil t)
                       (:want nil) (:have :history) (:want nil) (:have :history)
                       ((:want nil) :ungoverned) ((:have :history) :none))))
