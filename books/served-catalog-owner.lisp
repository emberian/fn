; served-catalog-owner.lisp -- the catalog at the owner's entries (step 8 of
; the catalog slice, the R side; planning/evidence/catalog-slice-2026-09-26.md).
;
; The host maintains the catalog at three entries, each an ACL2 decision the
; host only plumbs (host/owner-host.lisp):
;   E  fn-sco-load-history      at recovery (fn-owner-install-extended): the
;                               catalog of the installed store's history,
;                               from empty;
;   T2 fn-sco-complete          at fn-owner-finish-submission: the pending
;                               PreparedCommit completed by the completing
;                               record's token -- HIDDEN when the owner's
;                               refreshed view no longer shows its
;                               Message-ID (R1: a cancel that arrived before
;                               its target; the row is committed withdrawn at
;                               its own index and no view shows it, as the
;                               owner's refresh shows it at no version);
;   T4 fn-sco-withdraw-targets  after T2: the completed article's withdrawal
;                               targets (books/control-visible.lisp puts the
;                               newest article's withdrawals first in the
;                               view's list) that the view no longer shows are
;                               withdrawn at the count, the cancel's row as
;                               BY.
; The prepare is books/catalog-commit.lisp fn-cat-prepare itself, called at
; fn-owner-prepare-buffer over the payload buffer.
;
; R (books/catalog-relation.lisp fn-cat-history-relation) is established by E
; (fn-cat-ocl-relation-at-recover) and preserved by T2 in both forms
; (fn-cat-ocl-relation-of-article-finish, fn-cat-relation-of-complete-hidden)
; and by T4 (fn-cat-ocl-relation-of-withdraw), all in books/catalog-entries
; and catalog-relation; the theorems below are this book's shapes of those
; keystones over the functions the host calls.
;
; The JOIN -- that the view a pin names in the catalog (books/served-catalog-
; chain.lisp fn-scr-view-of) holds the pinned archive's articles, the
; hypothesis fn-scr-catalogp carries -- is stated here as fn-sco-join and is
; an OPEN proof target (the boundary owner's R3): its teeth are in the test
; book; what continues without it is the served path under the hypothesis.

(in-package "ACL2")

(include-book "served-catalog-chain")
(include-book "catalog-entries")

; -----------------------------------------------------------------------------
; E: the catalog of a history, from empty.

; Each article record's row, visible when the recovered owner's view shows
; its Message-ID, hidden otherwise (a cancel the history made effective).
(defun fn-sco-load-rows (records view-index keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (consp records)
      (if (fn-record-p (car records))
          (mv-let (fn-arena fn-cat)
            (if (fn-midx-lookup (fn-record-msgid (car records)) view-index)
                (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
              (fn-cat-load-row-hidden (car records) keyring generation fn-arena fn-cat))
            (fn-sco-load-rows (cdr records) view-index keyring generation fn-arena fn-cat))
        (fn-sco-load-rows (cdr records) view-index keyring generation fn-arena fn-cat))
    (mv fn-arena fn-cat)))

(defun fn-sco-load-history (records view-index keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (fn-sco-load-rows records view-index keyring generation fn-arena fn-cat)))

; The fold's induction, carrying the history appended so far
; (books/catalog-relation.lisp fn-crl-load-ind).
(local (defun fn-sco-load-ind (records history view-index keyring generation fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp records)
       (if (fn-record-p (car records))
           (mv-let (fn-arena fn-cat)
             (if (fn-midx-lookup (fn-record-msgid (car records)) view-index)
                 (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
               (fn-cat-load-row-hidden (car records) keyring generation fn-arena fn-cat))
             (fn-sco-load-ind (cdr records) (append history (list (car records)))
                              view-index keyring generation fn-arena fn-cat))
         (fn-sco-load-ind (cdr records) (append history (list (car records)))
                          view-index keyring generation fn-arena fn-cat))
     (mv fn-arena fn-cat))))

; KEYSTONE (E): the fold establishes R over the history it loads, whatever
; the view hides (catalog-relation's two step theorems; catalog-entries'
; non-article step).
(defthm fn-sco-load-rows-establishes-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-sco-load-rows records view-index keyring generation fn-arena fn-cat)
             (fn-cat-history-relation (append history records) fn-arena2 fn-cat2)))
  :hints (("Goal" :induct (fn-sco-load-ind records history view-index keyring generation
                                           fn-arena fn-cat)
           :expand ((fn-sco-load-rows records view-index keyring generation fn-arena fn-cat))
           :in-theory (e/d (fn-sco-load-rows)
                           (fn-cat-history-relation fn-cat-load-row fn-cat-load-row-hidden
                            fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-held-listp)))
          ("Subgoal *1/1" :use ((:instance fn-cat-load-row-keeps-relation
                                          (w (car records)) (records history))
                                (:instance fn-cat-load-row-hidden-keeps-relation
                                          (w (car records)) (records history))))))

(defthm fn-sco-load-history-establishes-relation
  (implies (natp generation)
           (mv-let (fn-arena2 fn-cat2)
             (fn-sco-load-history records view-index keyring generation fn-arena fn-cat)
             (fn-cat-history-relation records fn-arena2 fn-cat2)))
  :hints (("Goal" :use ((:instance fn-sco-load-rows-establishes-relation
                                   (history nil) (fn-arena (fn-arena-clear fn-arena))
                                   (fn-cat (fn-cat-clear fn-cat)))
                        (:instance fn-cat-relation-at-init))
           :in-theory (e/d (fn-sco-load-history fn-arena-clear fn-cat-clear
                            create-fn-arena create-fn-cat)
                           (fn-cat-history-relation fn-sco-load-rows)))))

; -----------------------------------------------------------------------------
; T2 and R1: the completion, hidden when the view no longer shows the row.

(defun fn-sco-complete (token pending view-index fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (fn-pc-optionp pending)
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p)))))
  (if (and pending
           (not (fn-midx-lookup (fn-record-msgid (fn-pc-held pending)) view-index)))
      (fn-cat-complete-hidden token pending (fn-pc-expected pending) fn-cat)
    (fn-cat-complete token pending fn-cat)))

(defthm fn-sco-complete-keeps-the-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w))
           (fn-cat-history-relation (append records (list w)) fn-arena
                                    (mv-nth 2 (fn-sco-complete token pending view-index fn-cat))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-sco-complete fn-cat-relation-of-complete
                                fn-cat-relation-of-complete-hidden fn-pc-p-fields)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; T4: the completed article's withdrawal targets the view no longer shows.

; The targets of the withdrawals CAUSE contributed: the view's list holds the
; newest article's first (books/control-visible.lisp fn-ctl-refresh-
; withdrawals, fn-ctl-prepend), so the scan stops at the first other cause.
(defun fn-sco-targets-of (cause ws)
  (declare (xargs :guard t))
  (if (and (consp ws) (fn-ctl-withdrawalp (car ws))
           (equal (fn-ctl-w-cause (car ws)) cause))
      (cons (fn-ctl-w-target (car ws)) (fn-sco-targets-of cause (cdr ws)))
    nil))

(defun fn-sco-withdraw-targets (targets view-index by fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp by)))
  (if (consp targets)
      (let ((fn-cat
             (if (fn-midx-lookup (car targets) view-index)
                 fn-cat
               (let ((seq (fn-cat-view-last-visible
                           (fn-cat-msgid-seqs (car targets) fn-cat)
                           (fn-cat-count fn-cat) fn-cat)))
                 (if (and (natp seq) (< seq (fn-cat-count fn-cat)))
                     (fn-cat-withdraw seq by fn-cat)
                   fn-cat)))))
        (fn-sco-withdraw-targets (cdr targets) view-index by fn-cat))
    fn-cat))

(defthm fn-sco-withdraw-targets-keeps-the-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat) (natp by))
           (fn-cat-history-relation records fn-arena
                                    (fn-sco-withdraw-targets targets view-index by fn-cat)))
  :hints (("Goal" :induct (fn-sco-withdraw-targets targets view-index by fn-cat)
           :in-theory (union-theories
                       '(fn-sco-withdraw-targets fn-cat-relation-of-withdraw)
                       (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The join (OPEN): the view a pin names holds the pinned archive's articles.
; Stated over the owner's current view: its version and archive.  Proving it
; is the R-side completion of step 8; until then it is the hypothesis the
; served chain carries (fn-scr-catalogp), with teeth in the test book.

(defun-nx fn-sco-join (o fn-arena fn-cat)
  (equal (fn-state-articles (fn-own-view-archive (fn-own-view o)))
         (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version (fn-own-view o)) fn-cat)
                               fn-arena fn-cat)))
