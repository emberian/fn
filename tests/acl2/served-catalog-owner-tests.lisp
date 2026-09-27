; served-catalog-owner-tests.lisp -- teeth for books/served-catalog-owner.lisp
; (step 8 of the catalog slice, the R side and the join).
;
; An owner built through its own event protocol (as tests/acl2/catalog-
; entries-tests.lisp builds one): three articles in two groups, each posted
; and completed.  The catalog is loaded from the same store's records with
; the owner's view index (E at recovery); then R holds, the number table is
; fresh, and THE JOIN: the catalog's view at the version the owner's view
; carries IS the owner's visible archive, article for article
; (fn-sco-join; the hypothesis the served chain carries, fn-scc-catalogp).
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
    (fn-sco-load-history records (fn-own-view-index view) nil 0 fn-arena fn-cat)
    (let ((v (fn-scc-view-of (fn-own-view-version view) fn-cat)))
      (mv (list (fn-cat-count fn-cat)
                (fn-cat-history-relation records fn-arena fn-cat)
                (fn-cnx-freshp fn-cat)
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

;; R, freshness, the view of the version (every row), and THE JOIN.
(assert-event (equal (nth 0 *scot-r*) 3))
(assert-event (equal (nth 1 *scot-r*) t))
(assert-event (equal (nth 2 *scot-r*) t))
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
     (fn-sco-load-history records view-index keyring generation fn-arena fn-cat)
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
                                     (mv-nth 2 (fn-sco-complete token pending view-index fn-cat))))))
