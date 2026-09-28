; served-catalog-join-entry-tests.lisp -- teeth for books/served-catalog-
; join-entry.lisp (E for the join at the opens; lane sca-join-3).
;
; The fixture REPLAYS: catalog-entries-tests' journal under the default
; configuration, extended to two articles, opened by the host's full open
; (the arena cleared, the journal interned, the owner installed by
; fn-ock-recover-extended over the rows, the catalog loaded by
; fn-sca-load-held-rows under the installed view's index), so fn-ocl-relation
; holds of the owner (evaluated), unlike sca-join-2's fixtures.
;
;   1. REACHABLE WITNESS of fn-scj-joinp-at-full-open (every antecedent and
;      every conjunct of fn-scj-joinp's body evaluated, on live stobjs: the
;      catalog's view at its count is the view's two visible articles,
;      newest first; every mark below the count; every row's sequence
;      below the view's version), and of the antecedents of
;      fn-scj-joinp-at-idle-current-owner and fn-scj-joinp-of-load on the
;      installed owner.
;   2. HYPOTHESIS REMOVAL for fn-scj-joinp-of-load, each over the same
;      owner with every retained hypothesis checked, the omitted one false
;      and the conclusion false: a row carrying a withdrawal
;      (fn-scj-rows-clearp); a row sequenced past the view's version
;      (fn-scj-rows-seqs-below); an index not built from the visible list
;      (the empty index); a visible list that is not the acceptance's filter.

(in-package "ACL2")

(include-book "catalog-entries-tests")
(include-book "../../books/served-catalog-join-entry")

(defconst *scje-w1* (cet-record 1 1 "<two@example>"))
(defconst *scje-ws* (list *cet-w0* *scje-w1*))
(defconst *scje-payloads* (list (fn-record-payload *cet-w0*) (fn-record-payload *scje-w1*)))

; The bodies of the defun-nx predicates, executed.
(defun scje-acc-rowsp (acc c)
  (declare (xargs :mode :program))
  (and (equal (fn-state-articles acc) (fn-scj-rows-arts c))
       (fn-scj-nexts-matchp (fn-state-groups acc) (fn-state-nexts acc) c)
       (fn-scj-rows-keys-inp c (fn-state-groups acc))
       t))

(defun scje-view-currentp (o)
  (declare (xargs :mode :program))
  (let ((files (fn-sn-files (fn-own-store o))))
    (and (equal (fn-own-view-version (fn-own-view o)) (len (fn-sf-records files)))
         (equal (fn-own-view-frontier (fn-own-view o)) (fn-sf-frontier files)))))

(defun scje-rows-of (i fn-cat)
  (declare (xargs :stobjs fn-cat :mode :program))
  (if (< i (fn-cat-count fn-cat))
      (cons (fn-cat-at i fn-cat) (scje-rows-of (+ 1 i) fn-cat))
    nil))

; Load ROWS under INDEX over the arena holding the payloads; answer the
; three conjuncts of fn-scj-joinp's body for VIEW, the loaded rows, and the
; row relation with ACC.
(defun scje-run (rows index view acc fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arn-seal-many *scje-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows rows index fn-arena fn-cat))
         (c (scje-rows-of 0 fn-cat)))
    (mv (list (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
                     (fn-state-articles (fn-own-view-archive view)))
              (fn-scj-marks-below c (fn-cat-count fn-cat))
              (fn-scj-seqs-below c (fn-own-view-version view))
              (scje-acc-rowsp acc c)
              (len (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat))
              (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena)
                   (fn-rows-composites-okp rows fn-arena)
                   (equal (fn-rows-wire-of rows fn-arena) *scje-ws*)))
        fn-arena fn-cat)))

(defun scje-exec (rows index view acc)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scje-run rows index view acc fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

; -----------------------------------------------------------------------------
; 1. The full open of the two-article journal.

(defconst *scje-rows* (cet-rows *scje-ws*))
(defconst *scje-oc*
  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture *cet-configs* nil) *cet-configs* *scje-rows*)
                           *cet-configs* 8 4))
(defconst *scje-o* (fn-ocfg-owner *scje-oc*))
(defconst *scje-view* (fn-own-view *scje-o*))
(defconst *scje-srows* (fn-sf-records (fn-sn-files (fn-own-store *scje-o*))))
(defconst *scje-acc* (fn-node-acceptance (fn-sn-node (fn-own-store *scje-o*))))

; fn-scj-joinp-at-full-open's antecedent.
(assert-event (and (true-listp *scje-ws*)
                   (not (equal *scje-rows* :bad))
                   (not (equal *scje-oc* :fault))))
; fn-scj-joinp-at-idle-current-owner's antecedent (the row hypotheses over
; the arena holding the payloads).
(assert-event (fn-ocl-relation *scje-oc*))
(assert-event (fn-own-store-idlep (fn-own-store *scje-o*)))
(assert-event (fn-scar-view-indexedp *scje-o*))
(assert-event (scje-view-currentp *scje-o*))
(assert-event (fn-scj-rows-clearp *scje-srows*))
(assert-event (equal *scje-srows* *scje-rows*))
; Non-vacuous: both articles are visible, and the view lists them newest first.
(assert-event (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive *scje-view*)))
                     '("<two@example>" "<one@example>")))
(assert-event (equal (fn-own-view-version *scje-view*) 2))
; fn-scj-joinp-of-load's remaining antecedents.
(assert-event (fn-article-listp (fn-state-groups *scje-acc*) (fn-state-articles *scje-acc*)))
(assert-event (equal (fn-state-articles (fn-own-view-archive *scje-view*))
                     (fn-ctl-visible-articles (fn-state-articles *scje-acc*)
                                              (fn-own-view-withdrawals *scje-view*)
                                              (fn-own-view-verdicts *scje-view*))))
(assert-event (fn-scj-rows-seqs-below *scje-srows* (fn-own-view-version *scje-view*)))
; The conclusion: the join's three conjuncts, and the row relation it uses.
(assert-event (equal (scje-exec *scje-srows* (fn-own-view-index *scje-view*) *scje-view* *scje-acc*)
                     (list t t t t 2 t)))

; -----------------------------------------------------------------------------
; 2. Hypothesis removal (fn-scj-joinp-of-load).

(defun scje-with-row (rows i row)
  (declare (xargs :mode :program))
  (update-nth i row rows))

; (a) A row carrying a withdrawal mark (0 . 0): the relation still holds (it
; reads no withdrawal), the sequences are below, the view's facts hold; the
; loaded row is invisible at every version, so the view at the count lacks
; <one@example>.
(defconst *scje-marked*
  (scje-with-row *scje-srows* 0 (fn-held-with-withdrawn (nth 0 *scje-srows*) (cons 0 0))))
(assert-event (not (fn-scj-rows-clearp *scje-marked*)))
(assert-event (fn-scj-rows-seqs-below *scje-marked* (fn-own-view-version *scje-view*)))
(assert-event (equal (scje-exec *scje-marked* (fn-own-view-index *scje-view*) *scje-view* *scje-acc*)
                     (list nil t t t 1 t)))

; (b) A row sequenced past the view's version: every other hypothesis holds,
; the sequences conjunct fails.
(defconst *scje-late*
  (scje-with-row *scje-srows* 1
                 (fn-held-make 7 1 1 "<two@example>" 1 '("fn.letters")
                               (fn-record-obligation-id (nth 1 *scje-srows*))
                               (fn-record-content-subject (nth 1 *scje-srows*))
                               (fn-record-release-evidence (nth 1 *scje-srows*))
                               (fn-record-charge (nth 1 *scje-srows*))
                               (fn-record-stamp (nth 1 *scje-srows*))
                               (fn-held-facts (nth 1 *scje-srows*))
                               (fn-held-context (nth 1 *scje-srows*))
                               nil nil)))
(assert-event (equal (fn-scj-row-art (nth 1 *scje-late*)) (fn-scj-row-art (nth 1 *scje-srows*))))
(assert-event (fn-scj-rows-clearp *scje-late*))
(assert-event (not (fn-scj-rows-seqs-below *scje-late* (fn-own-view-version *scje-view*))))
(assert-event (equal (scje-exec *scje-late* (fn-own-view-index *scje-view*) *scje-view* *scje-acc*)
                     (list t t nil t 2 nil)))

; (c) The empty index, not built from the visible list: the rows load
; hidden, the view at the count is empty.
(assert-event (not (equal nil (fn-midx-build (fn-state-articles (fn-own-view-archive *scje-view*))))))
(assert-event (equal (scje-exec *scje-srows* nil *scje-view* *scje-acc*)
                     (list nil t t t 0 t)))

; (d) A visible list that is not the acceptance's filter: the two articles
; oldest first (its index built from it, the rows clear and sequenced, the
; relation holding); the catalog shows them newest first.
(defconst *scje-arts* (fn-state-articles (fn-own-view-archive *scje-view*)))
(defconst *scje-reversed*
  (update-nth 2 (fn-ctl-visible-state-of *scje-acc* (reverse *scje-arts*))
              (update-nth 4 (fn-midx-build (reverse *scje-arts*)) *scje-view*)))
(assert-event (equal (fn-state-articles (fn-own-view-archive *scje-reversed*)) (reverse *scje-arts*)))
(assert-event (not (equal (fn-state-articles (fn-own-view-archive *scje-reversed*))
                          (fn-ctl-visible-articles (fn-state-articles *scje-acc*)
                                                   (fn-own-view-withdrawals *scje-reversed*)
                                                   (fn-own-view-verdicts *scje-reversed*)))))
(assert-event (equal (fn-own-view-index *scje-reversed*)
                     (fn-midx-build (fn-state-articles (fn-own-view-archive *scje-reversed*)))))
(assert-event (equal (fn-own-view-version *scje-reversed*) (fn-own-view-version *scje-view*)))
(assert-event (equal (scje-exec *scje-srows* (fn-own-view-index *scje-reversed*) *scje-reversed* *scje-acc*)
                     (list nil t t t 2 t)))
