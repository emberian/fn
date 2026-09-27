; served-catalog-owner-tests.lisp -- teeth for books/served-catalog-owner.lisp
; (step 8 of the catalog slice, the R side and the join).
;
; An owner built through its own event protocol (as tests/acl2/catalog-
; entries-tests.lisp builds one): three articles in two groups, each posted
; and completed.  The catalog is loaded from the same store's records with
; the owner's view index (E at recovery); then R holds, the number table is
; fresh, and THE JOIN: the catalog's view at the version the owner's view
; carries IS the owner's visible archive, article for article
; (fn-sca-join; the hypothesis the served chain carries, fn-scr-catalogp).
; A view that hides a Message-ID loads that row hidden (R1's form), and the
; join then holds against an archive without it.

(in-package "ACL2")

(include-book "../../books/served-catalog-owner")
(include-book "std/testing/must-fail" :dir :system)

;; A wire record: the payload names its Message-ID and carries one body line.
(defun scot-payload (msgid)
  (append (fn-record-string-octets (concatenate 'string "Message-ID: " msgid))
          '(13 10 13 10 72 105 13 10)))

(defun scot-record (sequence txid msgid groups)
  (fn-record-make sequence txid txid msgid (scot-payload msgid) groups
                  (concatenate 'string "own-pin:" msgid)
                  (concatenate 'string "own-content:" msgid)
                  (concatenate 'string "own-release:" msgid)
                  2 841000000))

(defun scot-post-events (record)
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare record))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))
        '(:complete)))

;; One article posted and completed by the host's finish, as
;; fn-owner-finish-submission completes it.
(defun scot-post (o record)
  (cdr (fn-ccar-own-finish
        (fn-own-run (fn-own-step o '(:begin 1)) (butlast (scot-post-events record) 1))
        nil)))

(defconst *scot-groups* '("fn.letters" "fn.test"))
(defconst *scot-w0* (scot-record 0 0 "<a@x>" '("fn.test")))
(defconst *scot-w1* (scot-record 1 1 "<b@x>" '("fn.test" "fn.letters")))
(defconst *scot-w2* (scot-record 2 2 "<c@x>" '("fn.letters")))

(defconst *scot-open*
  (fn-own-step (cdr (fn-own-open (fn-own-start (fn-sn-initial *scot-groups* 10) 4) nil))
               '(:open)))
(defconst *scot-o* (scot-post (scot-post (scot-post *scot-open* *scot-w0*) *scot-w1*) *scot-w2*))
(defconst *scot-view* (fn-own-view *scot-o*))
(defconst *scot-records* (fn-sf-records (fn-sn-files (fn-own-store *scot-o*))))

;; The owner: idle, three article records, its view at the record count with
;; three visible articles, newest first.
(assert-event (fn-own-store-idlep (fn-own-store *scot-o*)))
(assert-event (equal (fn-sf-article-records *scot-records*) (list *scot-w0* *scot-w1* *scot-w2*)))
(assert-event (equal (fn-own-view-version *scot-view*) (len *scot-records*)))
(assert-event (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive *scot-view*)))
                     '("<c@x>" "<b@x>" "<a@x>")))

;; The catalog from the same records under the owner's view index, and what
;; the join compares.
(defun scot-run (records view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (fn-arena fn-cat)
    (fn-sca-load-history records (fn-own-view-index view) nil 0 fn-arena fn-cat)
    (let ((v (fn-scr-view-of (fn-own-view-version view) fn-cat)))
      (mv (list (fn-cat-count fn-cat)
                (fn-cat-history-relation records fn-arena fn-cat)
                (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" fn-cat)
                                          (fn-cat-count fn-cat) fn-cat)
                v
                (fn-cat-view-articles v fn-arena fn-cat))
          fn-arena fn-cat))))

(defun scot-exec (records view)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scot-run records view fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *scot-r* (scot-exec *scot-records* *scot-view*))

;; R, <b@x>'s row (1) visible at the count, the view of the version (every row), and THE JOIN.
(assert-event (equal (nth 0 *scot-r*) 3))
(assert-event (equal (nth 1 *scot-r*) t))
(assert-event (equal (nth 2 *scot-r*) 1))
(assert-event (equal (nth 3 *scot-r*) 3))
(assert-event (equal (nth 4 *scot-r*) (fn-state-articles (fn-own-view-archive *scot-view*))))

;; A view that hides <b@x> (its index built without it) loads that row hidden:
;; the catalog's view is the archive without it, and R still holds.
(defconst *scot-hidden-view*
  (let ((arts (fn-state-articles (fn-own-view-archive *scot-view*))))
    (fn-own-view-make-visible
     (fn-own-view-version *scot-view*) (fn-own-view-frontier *scot-view*)
     (fn-own-view-archive *scot-view*) nil
     (fn-midx-build (list (car arts) (caddr arts)))
     (fn-own-view-group-index *scot-view*) nil nil nil nil)))

(defconst *scot-rh* (scot-exec *scot-records* *scot-hidden-view*))

(assert-event (equal (nth 0 *scot-rh*) 3))
(assert-event (equal (nth 1 *scot-rh*) t))
(assert-event (equal (nth 3 *scot-rh*) 3))
(assert-event (equal (fn-article-msgids (nth 4 *scot-rh*)) '("<c@x>" "<a@x>")))
(assert-event (equal (nth 4 *scot-rh*)
                     (let ((arts (fn-state-articles (fn-own-view-archive *scot-view*))))
                       (list (car arts) (caddr arts)))))

;; The load's keystone needs a natural generation (the row's context fails
;; fn-hc-p otherwise); the completion's needs the pending's token.
(must-fail
 (defthm scot-load-needs-natp-generation
   (mv-let (fn-arena2 fn-cat2)
     (fn-sca-load-history records view-index keyring generation fn-arena fn-cat)
     (fn-cat-history-relation records fn-arena2 fn-cat2))))

(must-fail
 (defthm scot-complete-needs-the-token
   (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                 (fn-pc-p pending)
                 (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                 (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                 (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                 (fn-record-p w))
            (fn-cat-history-relation (append records (list w)) fn-arena
                                     (mv-nth 2 (fn-sca-complete token pending view-index fn-cat))))
   :hints (("Goal" :do-not-induct t))))

;; -----------------------------------------------------------------------------
;; The finish the host calls (fn-sca-finish): T4 before T2, and R1.
;;
;; The catalog of the three-article history, then a fourth row completed.
;; CANCEL AFTER ITS TARGET: the refreshed view shows <d@x> and no longer
;; <b@x> (row 1); the targets are ("<b@x>").  R1: a completed row whose
;; Message-ID the view does not show (<e@x>).  REVERSED: the same cancel with
;; T2 before T4 -- the order fn-sca-finish exists to exclude.

(defconst *scot-w3* (scot-record 3 3 "<d@x>" '("fn.test")))
(defconst *scot-w4* (scot-record 3 3 "<e@x>" '("fn.test")))
(defconst *scot-o4* (scot-post *scot-o* *scot-w3*))
(defconst *scot-index-without-b*
  (let ((arts (fn-state-articles (fn-own-view-archive (fn-own-view *scot-o4*)))))
    (fn-midx-build (list (car arts) (cadr arts) (cadddr arts)))))

(assert-event (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive (fn-own-view *scot-o4*))))
                     '("<d@x>" "<c@x>" "<b@x>" "<a@x>")))
(assert-event (and (fn-midx-lookup "<d@x>" *scot-index-without-b*)
                   (not (fn-midx-lookup "<b@x>" *scot-index-without-b*))
                   (not (fn-midx-lookup "<e@x>" (fn-own-view-index *scot-view*)))))

(defun scot-finish-run (w view-index targets reversedp fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (fn-arena fn-cat)
    (fn-sca-load-history *scot-records* (fn-own-view-index *scot-view*) nil 0 fn-arena fn-cat)
    (mv-let (held fn-arena)
      (fn-cat-intern-list w nil 0 fn-arena)
      (let* ((count (fn-cat-count fn-cat))
             (pending (fn-pc-make (cons (nfix (fn-record-txid w)) count) count held nil nil))
             (token (fn-pc-token pending))
             (pinned (fn-cat-view-articles count fn-arena fn-cat))
             (fresh-before (fn-article-msgids (fn-cat-view-articles (+ 1 count) fn-arena fn-cat)))
             (b-seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" fn-cat) count fn-cat)))
        (mv-let (word pending2 fn-cat)
          (if reversedp
              (mv-let (word pending2 fn-cat)
                (fn-sca-complete token pending view-index fn-cat)
                (let ((fn-cat (fn-sca-withdraw-targets targets view-index count fn-cat)))
                  (mv word pending2 fn-cat)))
            (fn-sca-finish token pending view-index targets fn-cat))
          (mv (list (car word) pending2 count (fn-cat-count fn-cat) b-seq
                    (and (fn-cat-visible-at 1 count fn-cat) t)
                    (and (fn-cat-visible-at 1 (+ 1 count) fn-cat) t)
                    (and (fn-cat-visible-at count (+ 1 count) fn-cat) t)
                    (and (fn-cat-visible-at count (+ 2 count) fn-cat) t)
                    (equal (fn-cat-view-articles count fn-arena fn-cat) pinned)
                    (fn-article-msgids (fn-cat-view-articles (+ 1 count) fn-arena fn-cat))
                    fresh-before)
              fn-arena fn-cat))))))

(defun scot-finish-exec (w view-index targets reversedp)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scot-finish-run w view-index targets reversedp fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

;; Cancel after its target, T4 before T2: the completion is an :article
;; delta, nothing stays pending, the count goes 3 -> 4; <b@x>'s row (1) is
;; the target's last visible row, visible at the pinned version 3 and NOT at
;; 4, the first version showing the new row; the pinned view is unchanged;
;; the fresh view is d, c, a.
(defconst *scot-f* (scot-finish-exec *scot-w3* *scot-index-without-b* '("<b@x>") nil))
(assert-event (equal *scot-f* (list :article nil 3 4 1 t nil t t t '("<d@x>" "<c@x>" "<a@x>")
                                    '("<c@x>" "<b@x>" "<a@x>"))))

;; REVERSED (T2 then T4): <b@x> is still visible at version 4 -- the fresh
;; reader's pin shows the withdrawn target.  This is why the host calls
;; fn-sca-finish.
(defconst *scot-rev* (scot-finish-exec *scot-w3* *scot-index-without-b* '("<b@x>") t))
(assert-event (equal (nth 6 *scot-rev*) t))
(assert-event (equal (nth 10 *scot-rev*) '("<d@x>" "<c@x>" "<b@x>" "<a@x>")))

;; R1: the view does not show <e@x>; its row (3) is committed and visible at
;; no version (4, 5); the fresh view is the pinned one.
(defconst *scot-h* (scot-finish-exec *scot-w4* (fn-own-view-index *scot-view*) nil nil))
(assert-event (equal *scot-h* (list :article nil 3 4 1 t t nil nil t '("<c@x>" "<b@x>" "<a@x>")
                                    '("<c@x>" "<b@x>" "<a@x>"))))

;; A stale token refuses and changes nothing.
(defun scot-stale-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (fn-arena fn-cat)
    (fn-sca-load-history *scot-records* (fn-own-view-index *scot-view*) nil 0 fn-arena fn-cat)
    (mv-let (held fn-arena)
      (fn-cat-intern-list *scot-w3* nil 0 fn-arena)
      (let ((pending (fn-pc-make (cons 3 3) 3 held nil nil)))
        (mv-let (word pending2 fn-cat)
          (fn-sca-finish (cons 99 3) pending *scot-index-without-b* '("<b@x>") fn-cat)
          (mv (list (car word) (equal pending2 pending) (fn-cat-count fn-cat)
                    (and (fn-cat-visible-at 1 4 fn-cat) t))
              fn-arena fn-cat))))))

(defun scot-stale-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scot-stale-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(defconst *scot-stale* (scot-stale-exec))
(assert-event (equal *scot-stale* (list :stale-token t 3 t)))

;; Hypothesis-removal witnesses for the finish's keystones, each on the
;; reachable catalog above with every retained hypothesis holding:
;; - "past the count" (hides-the-targets): *scot-f* shows <b@x> at the pinned
;;   version 3 (element 5 is t);
;; - the token (hides-the-targets): *scot-stale* refuses, and <b@x> stays
;;   visible at version 4;
;; - "the view no longer shows it" (hides-the-targets): below, the same
;;   cancel under a view that still shows <b@x> leaves it visible at 4;
;; - "the view does not show it" (hides-the-hidden-row): *scot-f*'s completed
;;   row is visible at version 4 (element 7 is t);
;; - "at or below the count" (keeps-pinned-views): below, version 4 differs
;;   before and after the finish.
;; NOT separated: "not yet withdrawn" (hides-the-targets); a row visible at
;; the count and already withdrawn is withdrawn AT the count on every
;; reachable catalog, which no witness can exercise without corrupting one.
(defconst *scot-index-with-b*
  (fn-own-view-index (fn-own-view *scot-o4*)))
(defconst *scot-shown* (scot-finish-exec *scot-w3* *scot-index-with-b* '("<b@x>") nil))
(assert-event (equal (nth 6 *scot-shown*) t))
(assert-event (equal (nth 10 *scot-shown*) '("<d@x>" "<c@x>" "<b@x>" "<a@x>")))
;; Version 4 before the finish (element 11: c, b, a) and after it (element
;; 10: d, c, a) differ.
(assert-event (not (equal (nth 10 *scot-f*) (nth 11 *scot-f*))))
