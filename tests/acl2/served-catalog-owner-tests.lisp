; served-catalog-owner-tests.lisp -- teeth for books/served-catalog-owner.lisp
; (step 8 of the catalog slice, the R side and the join).
;
; An owner built through its own event protocol (as tests/acl2/catalog-
; entries-tests.lisp builds one): three articles in two groups, each posted
; and completed.  After the records flip the store retains ROWS: each POST
; prepares the row the entry interns (fn-intern-row-at at the arena's count,
; handle = sequence here) and the arena holds the payloads those handles
; name.  The catalog is loaded from the same store's rows with the owner's
; view index (E at recovery, fn-sca-load-held-rows: no byte read, nothing
; sealed); then R holds over the rows' wire events, the number table is
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
;; fn-owner-finish-submission completes it: the store prepares ROW over an
;; arena holding PAYLOADS (the payload ROW names included, as after the
;; host's seal).  No submission is in flight here, so the finish's word is
;; :fault; the completed owner is the one it installs.
(defun scot-post (payloads o row fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
    (mv (cdr (fn-ccar-own-finish
              (fn-own-run (fn-own-step o '(:begin 1) fn-arena) (butlast (scot-post-events row) 1)
                          fn-arena)
              nil fn-arena))
        fn-arena)))

(defun scot-payloads-of (ws)
  (declare (xargs :verify-guards nil))
  (if (consp ws) (cons (fn-record-payload (car ws)) (scot-payloads-of (cdr ws))) nil))

;; Post wire record W (sequence = its handle) after the wire records PRIOR.
(defun scot-post-exec (o w prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (scot-post (scot-payloads-of (append prior (list w))) o
                 (fn-intern-row-at w nil 0 (len prior)) fn-arena)
      r)))

(include-book "arena-lift")
(bpr-lift fn-own-step 2)

(defconst *scot-groups* '("fn.letters" "fn.test"))
(defconst *scot-w0* (scot-record 0 0 "<a@x>" '("fn.test")))
(defconst *scot-w1* (scot-record 1 1 "<b@x>" '("fn.test" "fn.letters")))
(defconst *scot-w2* (scot-record 2 2 "<c@x>" '("fn.letters")))

(defconst *scot-open*
  (in-arena-fn-own-step nil (cdr (fn-own-open (fn-own-start (fn-sn-initial *scot-groups* 10) 4) nil))
                        '(:open)))
(defconst *scot-ws3* (list *scot-w0* *scot-w1* *scot-w2*))
(defconst *scot-payloads* (scot-payloads-of *scot-ws3*))
(defconst *scot-o* (scot-post-exec (scot-post-exec (scot-post-exec *scot-open* *scot-w0* nil)
                                                   *scot-w1* (list *scot-w0*))
                                   *scot-w2* (list *scot-w0* *scot-w1*)))
(defconst *scot-view* (fn-own-view *scot-o*))
(defconst *scot-records* (fn-sf-records (fn-sn-files (fn-own-store *scot-o*))))

;; The owner: idle, three article records, its view at the record count with
;; three visible articles, newest first.
(assert-event (fn-own-store-idlep (fn-own-store *scot-o*)))
(defun scot-wires (payloads rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena)
      (let ((fn-arena (fn-arn-seal-many payloads fn-arena)))
        (mv (fn-rows-wire-of rows fn-arena) fn-arena))
      r)))
(assert-event (fn-held-listp *scot-records*))
(assert-event (equal (scot-wires *scot-payloads* *scot-records*) *scot-ws3*))
(assert-event (equal (fn-own-view-version *scot-view*) (len *scot-records*)))
(assert-event (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive *scot-view*)))
                     '("<c@x>" "<b@x>" "<a@x>")))

;; The catalog from the same records under the owner's view index, and what
;; the join compares.
(defun scot-run (records view fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arn-seal-many *scot-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows records (fn-own-view-index view) fn-arena fn-cat)))
    (let ((v (fn-scr-view-of (fn-own-view-version view) fn-cat)))
      (mv (list (fn-cat-count fn-cat)
                (fn-cat-history-relation (fn-rows-wire-of records fn-arena) fn-arena fn-cat)
                (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" fn-cat)
                                          (fn-cat-count fn-cat) fn-cat)
                v
                (fn-cat-view-articles v fn-arena fn-cat)
                ;; the E keystone's hypotheses, on this real history
                (and (fn-arena-p fn-arena) (fn-sf-record-valuesp records)
                     (fn-rows-handles-inp records fn-arena)
                     (fn-wire-event-listp (fn-rows-wire-of records fn-arena)) t)
                ;; the view's archive with each handle read as its bytes
                (fn-articles-wire-of (fn-state-articles (fn-own-view-archive view)) fn-arena))
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

;; R, <b@x>'s row (1) visible at the count, the view of the version (every
;; row), and the join ALPHA-WISE: after the records flip the owner's archive
;; articles carry the HANDLE in the payload position, the catalog's view
;; materializes the bytes, so the catalog's view is the archive with each
;; handle read through the arena (store-intern's fn-articles-wire-of), and
;; NOT the archive itself -- fn-sca-join as stated (archive = catalog view)
;; is false on the flipped store (an open finding, reported).
(assert-event (equal (nth 0 *scot-r*) 3))
(assert-event (equal (nth 1 *scot-r*) t))
(assert-event (equal (nth 2 *scot-r*) 1))
(assert-event (equal (nth 3 *scot-r*) 3))
(assert-event (equal (nth 4 *scot-r*) (nth 6 *scot-r*)))
(assert-event (not (equal (nth 4 *scot-r*) (fn-state-articles (fn-own-view-archive *scot-view*)))))
;; The positive witness of fn-sca-load-held-rows-establishes-relation on the
;; owner's own history: every hypothesis holds (element 5) and R holds
;; (element 1).
(assert-event (equal (nth 5 *scot-r*) t))

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
                     (let ((arts (nth 6 *scot-rh*)))
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
(defconst *scot-o4* (scot-post-exec *scot-o* *scot-w3* *scot-ws3*))
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
  ;; Recovery (E), then the host's POST path: the store's row at the arena's
  ;; count, the one seal, the prepare after it (T1).
  (let* ((fn-arena (fn-arn-seal-many *scot-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows *scot-records* (fn-own-view-index *scot-view*) fn-arena fn-cat))
         (row (fn-intern-row-at w nil 0 (fn-arena-count fn-arena)))
         (fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
    (progn$
      (let* ((count (fn-cat-count fn-cat))
             (pending (fn-cat-prepare-sealed w row nil nil nil fn-arena fn-cat))
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
  (let* ((fn-arena (fn-arn-seal-many *scot-payloads* fn-arena))
         (fn-cat (fn-sca-load-held-rows *scot-records* (fn-own-view-index *scot-view*) fn-arena fn-cat))
         (row (fn-intern-row-at *scot-w3* nil 0 (fn-arena-count fn-arena)))
         (fn-arena (fn-arena-seal-list (fn-record-payload *scot-w3*) fn-arena)))
    (progn$
      (let ((pending (fn-cat-prepare-sealed *scot-w3* row nil nil nil fn-arena fn-cat)))
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

;; -----------------------------------------------------------------------------
;; The records flip: T1 after the host's one seal, and E over the store's rows.
;;
;; T1 (fn-cat-prepare-sealed-names-the-sealed-handle).  A small arena holding
;; one older payload (w0's); the store's row for w1 at the count (handle 1),
;; built WITHOUT sealing (fn-intern-row-at); the host's buffer holds w1's
;; payload and is sealed with fn-arena-seal-buffer; then the prepare.

(defun scot-t1-row (w kind count)
  (declare (xargs :mode :program))
  (let ((r (fn-intern-row-at w nil 0 count)))
    (case kind
      (:older (fn-intern-row-at w nil 0 (- count 1)))
      ;; generation -1: the context fn-intern-row-at would decide under it
      (:bad-gen (fn-held-with-context r (fn-hc-make (fn-hc-verdict (fn-held-context r))
                                                    (fn-hc-delta (fn-held-context r)) -1)))
      ;; W's Message-ID not a string: the row fn-intern-row-at would build
      (:bad-msgid (fn-held-make (fn-record-sequence r) (fn-record-txid r) (fn-record-generation r)
                                nil (fn-record-payload r) (fn-record-groups r)
                                (fn-record-obligation-id r) (fn-record-content-subject r)
                                (fn-record-release-evidence r) (fn-record-charge r)
                                (fn-record-stamp r) (fn-held-facts r) (fn-held-context r)
                                nil nil))
      (otherwise r))))

;; KIND chooses the row (:good, :older, :bad-gen, :bad-msgid); SEALP whether
;; the host sealed the buffer before the prepare.
(defun scot-t1-run (w-old w kind buffer pending sealp fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-seal-list (fn-record-payload w-old) fn-arena))
         (count (fn-arena-count fn-arena))
         (row (scot-t1-row w kind count))
         (fn-octets (fn-octets-from-list buffer fn-octets))
         (fn-arena (if sealp (fn-arena-seal-buffer fn-octets fn-arena) fn-arena))
         (pc (fn-cat-prepare-sealed w row :plan :res pending fn-arena fn-cat)))
    (mv (list (and (fn-pc-p pc) t)
              (if (fn-pc-p pc) (fn-pc-token pc) pc)
              (if (fn-pc-p pc) (fn-pc-expected pc) nil)
              (if (fn-pc-p pc) (equal (fn-pc-held pc) (fn-intern-row-at w nil 0 count)) nil)
              (if (fn-pc-p pc) (fn-record-payload (fn-pc-held pc)) nil)
              (fn-arena-count fn-arena)
              (and sealp (equal (fn-arena-payload count fn-arena) buffer))
              (if (and (fn-pc-p pc) (< (fn-record-payload (fn-pc-held pc)) (fn-arena-count fn-arena)))
                  (equal (fn-held-wire-of (fn-pc-held pc) fn-arena) w)
                nil))
        fn-octets fn-arena fn-cat)))

(defun scot-t1-exec (w-old w kind buffer pending sealp)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (scot-t1-run w-old w kind buffer pending sealp fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

(defconst *scot-p1* (fn-record-payload *scot-w1*))

;; Positive witness, every antecedent holding (w1 a wire record, generation 0,
;; the buffer is w1's payload, nothing pending): a pending commit whose token
;; is (txid 1 . count 0), expected 0, holding exactly the store's row, naming
;; handle 1 = the arena's count before the seal; the arena grew to 2, handle
;; 1 holds the buffer, and the held row materializes to w1.
(assert-event (fn-record-p *scot-w1*))
(assert-event (equal (scot-t1-exec *scot-w0* *scot-w1* :good *scot-p1* nil t)
                     (list t '(1 . 0) 0 t 1 2 t t)))

;; The equation with catalog-slice's prepare on the same state: fn-cat-prepare
;; over the buffer returns the same pending and the same sealed arena.
(defun scot-t1-eq-run (w-old w fn-octets fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-octets fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-seal-list (fn-record-payload w-old) fn-arena))
         (count (fn-arena-count fn-arena))
         (row (fn-intern-row-at w nil 0 count))
         (fn-octets (fn-octets-from-list (fn-record-payload w) fn-octets)))
    (mv-let (old-pc fn-arena)
      (fn-cat-prepare w :plan :res fn-octets nil 0 nil fn-arena fn-cat)
      (let ((old-arena-count (fn-arena-count fn-arena))
            (old-payload (fn-arena-payload count fn-arena)))
        (mv (list (equal old-pc (fn-cat-prepare-sealed w row :plan :res nil fn-arena fn-cat))
                  old-arena-count
                  (equal old-payload (fn-record-payload w)))
            fn-octets fn-arena fn-cat)))))

(defun scot-t1-eq-exec (w-old w)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (with-local-stobj fn-arena
        (mv-let (result fn-octets fn-arena)
          (with-local-stobj fn-cat
            (mv-let (result fn-octets fn-arena fn-cat)
              (scot-t1-eq-run w-old w fn-octets fn-arena fn-cat)
              (mv result fn-octets fn-arena)))
          (mv result fn-octets)))
      result)))

(assert-event (equal (scot-t1-eq-exec *scot-w0* *scot-w1*) (list t 2 t)))

;; Hypothesis removal (T1):
;; - the row names an OLDER handle (0, w0's): refused :not-sealed, every
;;   other antecedent holding;
(assert-event (equal (nth 1 (scot-t1-exec *scot-w0* *scot-w1* :older *scot-p1* nil t))
                     '(:not-sealed)))
;; - a commit is pending: refused :pending;
(assert-event (equal (nth 1 (scot-t1-exec *scot-w0* *scot-w1* :good *scot-p1* '(:some-pending) t))
                     '(:pending)))
;; - the row at the count, the host never sealed: the row names no sealed
;;   handle, :not-sealed;
(assert-event (equal (nth 1 (scot-t1-exec *scot-w0* *scot-w1* :good *scot-p1* nil nil))
                     '(:not-sealed)))
;; - the buffer is not w1's payload: the pending is prepared, but the held
;;   row does not materialize to w1 (the conjunct the buffer hypothesis guards);
(assert-event (equal (scot-t1-exec *scot-w0* *scot-w1* :good (fn-record-payload *scot-w2*) nil t)
                     (list t '(1 . 0) 0 t 1 2 t nil)))
;; - a non-natural generation (the row's context decided at -1): the held
;;   row fails fn-held-p, so the result is no PreparedCommit;
(assert-event (equal (car (scot-t1-exec *scot-w0* *scot-w1* :bad-gen *scot-p1* nil t))
                     nil))
;; - W not a wire record (the row of a Message-ID that is no string): no
;;   PreparedCommit.
(assert-event (equal (car (scot-t1-exec *scot-w0* *scot-w1* :bad-msgid *scot-p1* nil t))
                     nil))

;; E over rows (fn-sca-load-held-rows-establishes-relation).  The store's
;; rows are what the open interns: three articles and a retention event
;; between them, interned into an empty arena (fn-intern-events).  The view
;; shows <a@x> and <c@x>, not <b@x>.

(defconst *scot-retention*
  (fn-store-retention-event-make :undertake 9 9 9 "own-pin:r" "own-content:r" "own-release:r" 2))
(defconst *scot-ws* (list *scot-w0* *scot-retention* *scot-w1* *scot-w2*))
(defconst *scot-index-ac*
  (fn-midx-put-chars (fn-midx-key-chars "<a@x>") :a
                     (fn-midx-put-chars (fn-midx-key-chars "<c@x>") :c nil)))

(assert-event (fn-wire-event-listp *scot-ws*))

(defun scot-e-run (ws view-index corrupt fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (mv-let (rows fn-arena)
    (fn-intern-events ws nil 0 fn-arena)
    (let* ((rows (if corrupt (append rows (list (fn-intern-row-at *scot-w2* nil 0 99))) rows))
           (count-before (fn-arena-count fn-arena))
           (fn-cat (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
      (mv (list (and (fn-arena-p fn-arena) t)
                (and (fn-sf-record-valuesp rows) t)
                (and (fn-rows-handles-inp rows fn-arena) t)
                (and (fn-wire-event-listp (fn-rows-wire-of rows fn-arena)) t)
                (and (fn-cat-history-relation (fn-rows-wire-of rows fn-arena) fn-arena fn-cat) t)
                (fn-cat-count fn-cat)
                (fn-held-withdrawn (fn-cat-at 0 fn-cat))
                (if (< 1 (fn-cat-count fn-cat)) (fn-held-withdrawn (fn-cat-at 1 fn-cat)) :none)
                (if (< 2 (fn-cat-count fn-cat)) (fn-held-withdrawn (fn-cat-at 2 fn-cat)) :none)
                (equal count-before (fn-arena-count fn-arena))
                (fn-rows-wire-of rows fn-arena))
          fn-arena fn-cat))))

(defun scot-e-exec (ws view-index corrupt)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scot-e-run ws view-index corrupt fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

;; Positive witness: every hypothesis holds of the interned rows, R holds
;; over their wire events (which ARE the four wire events), three rows are
;; committed (the retention event is skipped), <a@x> and <c@x> visible, <b@x>
;; (row 1) committed WITHDRAWN at its own index (1 . 0), and the load sealed
;; nothing.
(defconst *scot-e* (scot-e-exec *scot-ws* *scot-index-ac* nil))
(assert-event (equal (butlast *scot-e* 1) (list t t t t t 3 nil '(1 . 0) nil t)))
(assert-event (equal (car (last *scot-e*)) *scot-ws*))

;; Hypothesis removal (E): a row whose handle is outside the arena (a held
;; row naming handle 99), every other hypothesis holding: the handles
;; hypothesis fails and so does R.
(defconst *scot-e-bad* (scot-e-exec *scot-ws* *scot-index-ac* t))
(assert-event (equal (take 6 *scot-e-bad*) (list t t nil t nil 4)))
