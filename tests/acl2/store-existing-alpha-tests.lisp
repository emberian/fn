; Teeth for books/store-existing-alpha.lisp: the duplicate-post checks over
; the arena.  Each keystone: a reachable witness asserting every hypothesis
; and the conclusion, then per hypothesis one value at which the other
; hypotheses hold, that one fails and the conclusion is false.
(in-package "ACL2")
(include-book "poster-bytes-tests")
(include-book "source-routes-tests")
(include-book "../../books/store-existing-alpha")
(include-book "must-fail-checked")

; Evaluate over the arena of SPEC (srt-spec's form: the journal the entry
; interned, then payloads sealed after it): the entry, D25's decision over
; alpha, the byte-identity decision over alpha, and whether the held bytes
; are a tombstone.
(defun sea-eval-in (spec msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events (car spec) nil 0 fn-arena)
    (declare (ignore rows))
    (let ((fn-arena (srt-seal-all (cdr spec) fn-arena)))
      (mv (list (fn-store-existing-action msgid payload groups s fn-arena)
                (fn-pb-action-over msgid payload groups (fn-sn-alpha-articles s fn-arena))
                (fn-sn-action-over msgid payload groups (fn-sn-alpha-articles s fn-arena))
                (fn-rcl-tombstonep
                 (fn-handle-bytes
                  (fn-article-payload
                   (fn-find-article msgid (fn-state-articles
                                           (fn-node-acceptance (fn-sn-node s)))))
                  fn-arena)))
          fn-arena))))
(defun sea-eval (spec msgid payload groups s)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (sea-eval-in spec msgid payload groups s fn-arena) r)))
(defun sea-entry (spec m p g s) (nth 0 (sea-eval spec m p g s)))
(defun sea-pb (spec m p g s) (nth 1 (sea-eval spec m p g s)))
(defun sea-sn (spec m p g s) (nth 2 (sea-eval spec m p g s)))
(defun sea-tombp (spec m p g s) (nth 3 (sea-eval spec m p g s)))

(defconst *sea-spec* (list *pbt-prior*))
(defconst *sea-held* (pbt-octets *pbt-dateless* *pbt-a*))

; The flip regression the book repairs: on the live store the list
; decisions compare with the handle, so a byte-identical resend is a
; conflict.
(assert-event (equal (fn-sn-existing-action *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*)
                     :conflict))
(assert-event (equal (fn-pb-existing-action *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*)
                     :conflict))

; -----------------------------------------------------------------------------
; fn-store-existing-action-is-pb-over-alpha.
; Witness: the held bytes resent (:duplicate), and the same source at
; another instant (:duplicate by source, where the byte decision says
; :conflict): the entry equals D25's decision over alpha.
(assert-event
 (and (stringp *pbt-msgid*)
      (not (sea-tombp *sea-spec* *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*))
      (equal (sea-entry *sea-spec* *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*) :duplicate)
      (equal (sea-pb *sea-spec* *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*) :duplicate)
      (equal (sea-entry *sea-spec* *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*) :duplicate)
      (equal (sea-pb *sea-spec* *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*) :duplicate)
      (equal (sea-sn *sea-spec* *pbt-msgid* *pbt-resend* *pbt-groups* *pbt-store*) :conflict)
      (equal (sea-entry *sea-spec* *pbt-msgid* *pbt-other* *pbt-groups* *pbt-store*) :conflict)
      (equal (sea-pb *sea-spec* *pbt-msgid* *pbt-other* *pbt-groups* *pbt-store*) :conflict)))

; Hypothesis removed: the held bytes are a tombstone (source-routes-tests'
; reclaimed dateless store).  The retry of the reclaimed article is
; :duplicate by digest at the entry; D25's live decision over alpha
; compares it with the tombstone's bytes and says :conflict.
(assert-event
 (and (stringp *srt-msgid*)
      (sea-tombp *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                 *srt-t-dateless*)
      (equal (sea-entry *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                        *srt-groups* *srt-t-dateless*)
             :duplicate)
      (equal (sea-pb *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                     *srt-groups* *srt-t-dateless*)
             :conflict)))
(must-fail-checked
 (assert-event (equal (sea-entry *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                                 *srt-groups* *srt-t-dateless*)
                      (sea-pb *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                              *srt-groups* *srt-t-dateless*))))

; Hypothesis removed: a Message-ID that is no string.  Test-only surgery:
; the store's article list is (nil); the entry finds no article under NIL
; (fn-find-article answers the nil element, which is no article), while
; alpha makes an article of it, so the decision over alpha answers.
(defun sea-index-of (x xs i)
  (if (consp xs) (if (equal (car xs) x) i (sea-index-of x (cdr xs) (1+ i))) nil))
(defun sea-with-articles (s arts)
  (let* ((node (fn-sn-node s))
         (acc (fn-node-acceptance node))
         (k (sea-index-of acc node 0))
         (j (sea-index-of (fn-state-articles acc) acc 0)))
    (update-nth 3 (update-nth k (update-nth j arts acc) node) s)))
(defconst *sea-nil-store* (sea-with-articles *pbt-store* (list nil)))
(assert-event (equal (fn-state-articles (fn-node-acceptance (fn-sn-node *sea-nil-store*)))
                     (list nil)))
(assert-event
 (and (not (stringp nil))
      (not (sea-tombp *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*))
      (null (sea-entry *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*))
      (sea-pb *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*)))
(must-fail-checked
 (assert-event (equal (sea-entry *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*)
                      (sea-pb *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*))))

; -----------------------------------------------------------------------------
; fn-store-existing-action-refines-byte-identity-over-alpha.
; Witness: held, the byte decision over alpha is :duplicate for the held
; bytes, and the entry is :duplicate; the entry and the byte decision are
; non-nil together; an unheld Message-ID is nil for both.
(assert-event
 (and (equal (sea-sn *sea-spec* *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*) :duplicate)
      (equal (sea-entry *sea-spec* *pbt-msgid* *sea-held* *pbt-groups* *pbt-store*) :duplicate)
      (null (sea-entry *sea-spec* "<sea-absent@example.invalid>" *sea-held* *pbt-groups* *pbt-store*))
      (null (sea-sn *sea-spec* "<sea-absent@example.invalid>" *sea-held* *pbt-groups* *pbt-store*))))
; Hypothesis removed (no tombstone, second conjunct): the reclaimed store,
; offered its own tombstone bytes: the byte decision over alpha says
; :duplicate, the entry decides by digest and says :conflict.
(defconst *sea-tomb-bytes* (car (cdr *srt-t-dateless-spec*)))
(assert-event
 (and (sea-tombp *srt-t-dateless-spec* *srt-msgid* *sea-tomb-bytes* *srt-groups* *srt-t-dateless*)
      (equal (sea-sn *srt-t-dateless-spec* *srt-msgid* *sea-tomb-bytes* *srt-groups* *srt-t-dateless*)
             :duplicate)
      (not (equal (sea-entry *srt-t-dateless-spec* *srt-msgid* *sea-tomb-bytes* *srt-groups*
                             *srt-t-dateless*)
                  :duplicate))))
(must-fail-checked
 (assert-event (equal (sea-entry *srt-t-dateless-spec* *srt-msgid* *sea-tomb-bytes* *srt-groups*
                                 *srt-t-dateless*)
                      :duplicate)))
; Hypothesis removed (stringp): the nil-Message-ID store: the byte decision
; over alpha answers, the entry does not, so the iff fails.
(assert-event
 (and (sea-sn *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*)
      (null (sea-entry *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*))))
(must-fail-checked
 (assert-event (iff (sea-entry *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*)
                    (sea-sn *sea-spec* nil *sea-held* *pbt-groups* *sea-nil-store*))))
