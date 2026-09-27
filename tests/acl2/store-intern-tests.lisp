; fn: witnesses and teeth for books/store-intern.lisp's two host entries
; (records-flip, flip-L1): the POST/transit prepare fn-store-prepare-interned
; and the duplicate/conflict verdict fn-store-existing-action.
;
; Every store below is reached from fn-sn-initial by the host's transitions
; (fn-sn-io's reservation and publication words, the entry, fn-sn-finish);
; the arena is a local one holding the payloads of PRIOR (wire records
; interned in order) and then what the entry sealed.  Corrupted-state
; witnesses are labelled as such.
(in-package "ACL2")
(include-book "../../books/store-intern")

(defconst *sit-groups* '("fn.letters" "fn.test"))
(defconst *sit-prior*
  (list (fn-record-make 0 0 0 "<prior@example>" '(1 2 3) *sit-groups*
                        "p-pin" "p-content" "p-release" 2 841000000)))
(defconst *sit-record*
  (fn-record-make 0 0 0 "<sit@example>" '(65 66) *sit-groups*
                  "sit-pin" "sit-content" "sit-release" 2 841000000))
(assert-event (fn-record-p *sit-record*))

(defun sit-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun sit-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defconst *sit-initial* (fn-sn-initial *sit-groups* 10))
(defconst *sit-reserved* (sit-reserve *sit-initial*))
(assert-event (fn-sn-statep *sit-reserved*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sit-reserved*)) :reserved))

; -----------------------------------------------------------------------------
; The prepare entry over a local arena: the store after it, the arena's count
; before and after, the bytes under the old count after, and the reference
; (the intern then the store's prepare) computed on a second local arena.

(defun sit-prepare-in (s w prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let ((before (fn-arena-count fn-arena)))
      (mv-let (next fn-arena)
        (fn-store-prepare-interned s w fn-arena)
        (mv (list next before (fn-arena-count fn-arena)
                  (if (< before (fn-arena-count fn-arena))
                      (fn-arena-payload before fn-arena)
                    :none))
            fn-arena)))))

(defun sit-prepare (s w prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (sit-prepare-in s w prior fn-arena)
      out)))

(defun sit-reference-in (s w prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv-let (row fn-arena)
      (fn-cat-intern-list w (fn-sn-keyring s) (fn-sn-keyring-generation s) fn-arena)
      (mv (fn-sn-prepare s row) fn-arena))))

(defun sit-reference (s w prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (next fn-arena)
      (sit-reference-in s w prior fn-arena)
      next)))

; Reachable ACCEPTANCE (fn-store-prepare-interned-acceptance-seals-one-payload,
; fn-store-prepare-interned-is-intern-then-prepare): the reserved store takes
; the record; the arena grows from 1 to 2 and handle 1 holds the record's
; bytes; the staged row names handle 1; the store is the reference's.
(defconst *sit-accepted* (sit-prepare *sit-reserved* *sit-record* *sit-prior*))
(assert-event (not (equal (nth 0 *sit-accepted*) *sit-reserved*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (nth 0 *sit-accepted*))) :record-staged))
(assert-event (equal (nth 1 *sit-accepted*) 1))
(assert-event (equal (nth 2 *sit-accepted*) 2))
(assert-event (equal (nth 3 *sit-accepted*) '(65 66)))
(assert-event (equal (fn-record-payload (fn-sf-record-candidate (fn-sn-files (nth 0 *sit-accepted*))))
                     1))
(assert-event (equal (nth 0 *sit-accepted*)
                     (sit-reference *sit-reserved* *sit-record* *sit-prior*)))

; Reachable REFUSAL (fn-store-prepare-interned-refusal-keeps-the-arena): the
; initial store is not reserved, so the prepare refuses; the arena's count
; stays 1 and nothing is sealed.  The acceptance theorem's second hypothesis
; fails here and so does its conclusion (the count does not grow).
(defconst *sit-refused* (sit-prepare *sit-initial* *sit-record* *sit-prior*))
(assert-event (equal (nth 0 *sit-refused*) *sit-initial*))
(assert-event (equal (nth 1 *sit-refused*) 1))
(assert-event (equal (nth 2 *sit-refused*) 1))
(assert-event (equal (nth 3 *sit-refused*) :none))
(assert-event (equal (nth 0 *sit-refused*)
                     (sit-reference *sit-initial* *sit-record* *sit-prior*)))
; A second refusal kind: the accepted store is no longer :reserved.
(defconst *sit-refused-2* (sit-prepare (nth 0 *sit-accepted*) *sit-record* *sit-prior*))
(assert-event (equal (nth 0 *sit-refused-2*) (nth 0 *sit-accepted*)))
(assert-event (equal (nth 2 *sit-refused-2*) (nth 1 *sit-refused-2*)))

; The refusal theorem's hypothesis fails at the acceptance above, and so does
; its conclusion there (the arena grew).
(assert-event (and (not (equal (nth 0 *sit-accepted*) *sit-reserved*))
                   (not (equal (nth 2 *sit-accepted*) (nth 1 *sit-accepted*)))))

; HYPOTHESIS REMOVAL for the keystone (fn-record-p w).  W2 is the record with
; a payload that is not an octet list: not a wire record (the retained
; hypothesis fails), yet the intern's row is a held row the store accepts
; (its payload position is a handle), so the reference prepares while the
; entry refuses: the conclusion fails.
(defconst *sit-not-record*
  (fn-record-make 0 0 0 "<sit@example>" '(300) *sit-groups*
                  "sit-pin" "sit-content" "sit-release" 2 841000000))
(assert-event (not (fn-record-p *sit-not-record*)))
(assert-event (equal (nth 0 (sit-prepare *sit-reserved* *sit-not-record* *sit-prior*))
                     *sit-reserved*))
;; The reference side is the intern's row at the arena's count (1 after
;; PRIOR: fn-cat-intern-list-is-row-at-count), evaluated by the prover (the
;; intern's guard asks for a wire record, which W2 is not).
(defthm sit-not-record-reference-prepares
  (let ((row (fn-intern-row-at *sit-not-record* nil 0 1)))
    (and (fn-held-p row)
         (not (equal (fn-sn-prepare *sit-reserved* row) *sit-reserved*))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The duplicate/conflict entry over the finished store: the article the entry
; staged completes (fn-sn-io's publication words, fn-sn-finish), and its
; acceptance article carries handle 1, whose bytes are (65 66).

(defun sit-existing-in (s prior w msgid payload groups fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv-let (next fn-arena)
      (fn-store-prepare-interned s w fn-arena)
      (let ((done (fn-sn-finish (sit-publish next))))
        (mv (list (fn-store-existing-action msgid payload groups done fn-arena)
                  (fn-rcl-action-over msgid payload groups
                                      (fn-articles-wire-of
                                       (fn-state-articles (fn-node-acceptance (fn-sn-node done)))
                                       fn-arena))
                  done)
            fn-arena)))))

(defun sit-existing (msgid payload groups)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (sit-existing-in *sit-reserved* *sit-prior* *sit-record* msgid payload groups fn-arena)
      out)))

(defconst *sit-dup* (sit-existing "<sit@example>" '(65 66) *sit-groups*))
(defconst *sit-conflict* (sit-existing "<sit@example>" '(65 67) *sit-groups*))
(defconst *sit-conflict-groups* (sit-existing "<sit@example>" '(65 66) '("fn.test")))
(defconst *sit-absent* (sit-existing "<other@example>" '(65 66) *sit-groups*))

; The article is accepted, and its payload is a handle, not bytes.
(assert-event (equal (fn-article-payload
                      (fn-find-article "<sit@example>"
                                       (fn-state-articles
                                        (fn-node-acceptance (fn-sn-node (nth 2 *sit-dup*))))))
                     1))
; KEYSTONE fn-store-existing-action-is-the-verdict-over-alpha, reachable, on
; every verdict: duplicate, conflict (bytes), conflict (groups), absent.
(assert-event (and (equal (nth 0 *sit-dup*) :duplicate) (equal (nth 1 *sit-dup*) :duplicate)))
(assert-event (and (equal (nth 0 *sit-conflict*) :conflict) (equal (nth 1 *sit-conflict*) :conflict)))
(assert-event (and (equal (nth 0 *sit-conflict-groups*) :conflict)
                   (equal (nth 1 *sit-conflict-groups*) :conflict)))
(assert-event (and (equal (nth 0 *sit-absent*) nil) (equal (nth 1 *sit-absent*) nil)))

; HYPOTHESIS REMOVAL (stringp msgid), CORRUPTED STATE: an acceptance node
; whose article list holds a NIL element (no fn-statep state does).  With the
; Message-ID NIL the entry finds that element, which is no article, and says
; nil; alpha makes an article of it and the verdict over alpha is :conflict.
(defconst *sit-corrupt*
  (fn-sn-update *sit-reserved* (fn-sn-files *sit-reserved*)
                ; node = (acceptance ...), acceptance = (_ _ articles ...)
                (list (list nil nil (list nil)))))
(defun sit-corrupt-check (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (list (fn-store-existing-action nil nil nil *sit-corrupt* fn-arena)
        (fn-rcl-action-over nil nil nil
                            (fn-articles-wire-of
                             (fn-state-articles (fn-node-acceptance (fn-sn-node *sit-corrupt*)))
                             fn-arena))
        (fn-state-articles (fn-node-acceptance (fn-sn-node *sit-corrupt*)))))
(defun sit-corrupt () (with-local-stobj fn-arena (mv-let (out fn-arena) (mv (sit-corrupt-check fn-arena) fn-arena) out)))
(assert-event (not (stringp nil)))
(assert-event (member-equal nil (nth 2 (sit-corrupt))))
(assert-event (not (equal (nth 0 (sit-corrupt)) (nth 1 (sit-corrupt)))))
