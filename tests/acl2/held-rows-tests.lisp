; The test books' entry to the retained store (records-flip, 2026-09-27).
;
; After the flip the store machine and the acceptance state retain HELD
; ROWS (books/held-record.lisp): an article's payload position holds a handle
; into the arena, and every entry interns a wire event before the store sees
; it (books/store-intern.lisp fn-intern-event / fn-intern-events).  A test
; that used to hand wire records (or octet payloads) to the store builds its
; fixture here: the wire events interned in order on a FRESH arena, so a
; record's handle is the number of records interned before it.  Reading
; bytes back is alpha over the arena that holds the same payloads.
;
; The record intern is the production one (books/catalog-record.lisp
; fn-cat-intern-list, which fn-intern-event calls for a record); FN-HRT-EVENT
; is fn-intern-event's dispatch, stated over the books below store-intern so
; that the test corpus does not wait on store-intern's certificate.
; tests/acl2/held-rows-intern-tests.lisp proves FN-HRT-EVENTS equal to
; fn-intern-events, so every fixture here IS the entry's output.
(in-package "ACL2")
(include-book "../../books/catalog-record")
(include-book "../../books/replay")
(include-book "../../books/store-reclaim")

(defun fn-hrt-event (w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (cond ((fn-record-p w) (fn-cat-intern-list w keyring generation fn-arena))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (mv-let (held fn-arena)
                 (fn-cat-intern-list a keyring generation fn-arena)
                 (mv (fn-hstxa-make w held) fn-arena))
             (mv :bad fn-arena))))
        ((fn-wire-event-p w) (mv w fn-arena))
        (t (mv :bad fn-arena))))

(defun fn-hrt-events (ws keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom ws)
      (mv nil fn-arena)
    (mv-let (row fn-arena)
      (fn-hrt-event (car ws) keyring generation fn-arena)
      (if (eq row :bad)
          (mv :bad fn-arena)
        (mv-let (rest fn-arena)
          (fn-hrt-events (cdr ws) keyring generation fn-arena)
          (if (eq rest :bad)
              (mv :bad fn-arena)
            (mv (cons row rest) fn-arena)))))))

; ALPHA over the arena (store-intern's fn-row-wire-of and fn-articles-wire-of,
; restated below it; held-rows-intern-tests proves the equations).
(defun fn-hrt-handle-bytes (h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (fn-arena-payload h fn-arena)
    nil))

(defun fn-hrt-rows-wire-of (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom rows)
      nil
    (cons (let ((row (car rows)))
            (cond ((fn-held-p row)
                   (fn-held-wire row (fn-hrt-handle-bytes (fn-record-payload row) fn-arena)))
                  ((fn-hstxa-p row) (fn-hstxa-stxa row))
                  (t row)))
          (fn-hrt-rows-wire-of (cdr rows) fn-arena))))

(defun fn-hrt-articles-alpha (articles fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom articles)
      nil
    (let ((a (car articles)))
      (cons (fn-make-article (fn-article-msgid a)
                             (fn-hrt-handle-bytes (fn-article-payload a) fn-arena)
                             (fn-article-groups a) (fn-article-memberships a)
                             (fn-article-pin a) (fn-article-stamp a))
            (fn-hrt-articles-alpha (cdr articles) fn-arena)))))

; The row of wire record W at handle H with its bytes' facts and context
; under keyring nil at generation 0 (store-intern's fn-intern-row-at): the
; intern's row when the arena holds H payloads.
(defun fn-hrt-row-at (w h)
  (declare (xargs :verify-guards nil))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes nil 0)
                  nil nil (fn-record-binding w))))

; The rows of WS interned in order under KEYRING and GENERATION on a fresh
; arena (:bad when the intern refuses one).
(defun fn-hrt-rows (ws keyring generation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (fn-hrt-events ws keyring generation fn-arena)
      rows)))

; The row of W interned after PRIOR (under keyring nil, generation 0, as
; the open does), itself under KEYRING and GENERATION.
(defun fn-hrt-row-after-in (prior w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (fn-hrt-event w keyring generation fn-arena)))

(defun fn-hrt-row-after (prior w keyring generation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (row fn-arena)
      (fn-hrt-row-after-in prior w keyring generation fn-arena)
      row)))

; The bytes under HANDLE in the arena that interned PRIOR.
(defun fn-hrt-bytes-in (prior handle fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (if (and (natp handle) (< handle (fn-arena-count fn-arena)))
            (fn-arena-payload handle fn-arena)
          nil)
        fn-arena)))

(defun fn-hrt-bytes (prior handle)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (bytes fn-arena)
      (fn-hrt-bytes-in prior handle fn-arena)
      bytes)))

; ALPHA: the wire events ROWS stand for, read through the arena that
; interned PRIOR.
(defun fn-hrt-wire-of-in (prior rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (ignored fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore ignored))
    (mv (fn-hrt-rows-wire-of rows fn-arena) fn-arena)))

(defun fn-hrt-wire-of (prior rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (ws fn-arena)
      (fn-hrt-wire-of-in prior rows fn-arena)
      ws)))

; The duplicate/conflict verdict over the arena that interned PRIOR: D25's
; fn-rcl-action-over over alpha of the acceptance articles, which is
; store-intern's entry fn-store-existing-action by its keystone
; fn-store-existing-action-is-the-verdict-over-alpha.
(defun fn-hrt-existing-action-in (prior msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (ignored fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore ignored))
    (mv (fn-rcl-action-over msgid payload groups
                             (fn-hrt-articles-alpha
                              (fn-state-articles (fn-node-acceptance (fn-sn-node s)))
                              fn-arena))
        fn-arena)))

(defun fn-hrt-existing-action (prior msgid payload groups s)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (v fn-arena)
      (fn-hrt-existing-action-in prior msgid payload groups s fn-arena)
      v)))

; ALPHA of acceptance ARTICLES (handles to bytes) over the arena that
; interned PRIOR: the article list the pre-flip state held.
(defun fn-hrt-articles-wire-of-in (prior articles fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (ignored fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore ignored))
    (mv (fn-hrt-articles-alpha articles fn-arena) fn-arena)))

(defun fn-hrt-articles-wire-of (prior articles)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (as fn-arena)
      (fn-hrt-articles-wire-of-in prior articles fn-arena)
      as)))

; Witnesses: two records interned take handles 0 and 1, are held rows, and
; read back (alpha) to themselves; the bytes under each handle are the
; record's payload; a value the codec does not produce is refused.
(defconst *hrt-r0*
  (fn-record-make 0 0 0 "<hrt0@example.invalid>" '(65 13 10) '("fn.test")
                  "hrt-pin-0" "hrt-content-0" "hrt-release-0" 2 841000000 *fn-record-golden-binding*))
(defconst *hrt-r1*
  (fn-record-make 1 1 1 "<hrt1@example.invalid>" '(66 13 10) '("fn.test")
                  "hrt-pin-1" "hrt-content-1" "hrt-release-1" 3 841000000 *fn-record-golden-binding*))
(defconst *hrt-rows* (fn-hrt-rows (list *hrt-r0* *hrt-r1*) nil 0))
(assert-event (and (fn-held-p (car *hrt-rows*)) (fn-held-p (cadr *hrt-rows*))))
(assert-event (equal (fn-record-payload (car *hrt-rows*)) 0))
(assert-event (equal (fn-record-payload (cadr *hrt-rows*)) 1))
(assert-event (equal (fn-hrt-wire-of (list *hrt-r0* *hrt-r1*) *hrt-rows*)
                     (list *hrt-r0* *hrt-r1*)))
(assert-event (equal (fn-hrt-bytes (list *hrt-r0* *hrt-r1*) 1) '(66 13 10)))
(assert-event (equal (fn-hrt-row-after (list *hrt-r0*) *hrt-r1* nil 0)
                     (cadr *hrt-rows*)))
(assert-event (equal (fn-hrt-rows (list *hrt-r0* :not-an-event) nil 0) :bad))
(assert-event (equal (fn-article-payload
                      (car (fn-hrt-articles-wire-of
                            (list *hrt-r0* *hrt-r1*)
                            (list (fn-make-article "<hrt1@example.invalid>" 1 '("fn.test")
                                                   nil "hrt-pin-1" 841000000)))))
                     '(66 13 10)))
(assert-event (equal (fn-hrt-row-at *hrt-r1* 1) (cadr *hrt-rows*)))
