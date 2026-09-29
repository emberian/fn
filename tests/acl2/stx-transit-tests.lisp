; Witnesses and teeth for the transit half of the substrate: the lace as the
; store projected, the bridge, equivocation, the index, policy confinement
; and the commit carrier.
;
; specs/substrate-transport.md sections 2 to 4; keystones S3-1, S3-2, S3-3,
; S4-1, S5-1.
;
; The seam is constrained, so this book inherits crypto-seam-tests' TOY
; realiser (a polynomial mix digest and a sign-by-public-key scheme, neither
; cryptographic -- A-CRYPTO).  Every witness below is a statement about the
; composition, never about unforgeability or collision resistance.  A
; defconst may not call an attached function (:DOC ignored-attachment), so
; every constant that reaches the realiser is built by make-event.

(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "must-fail-checked")
(include-book "../../books/stx-epochs")
(include-book "../../books/stx-authority")
(include-book "../../books/codec-attach")
; The lace of the retained store (records-flip): the rows' lace and ALPHA.
(include-book "../../books/stx-lace-rows")
; The store's records reach the committed history image's decode
; (books/store-records-field.lisp, lane arena-store-7), whose books include
; crypto-attach: it attaches fn-digest to BLAKE3 after crypto-seam-tests
; attached the toy.  This book's witnesses are over the toy realiser, so
; it is attached again, last.
(defattach fn-digest fn-toy-mix-digest)

; -----------------------------------------------------------------------------
; Two principals, one keyring, and a store made of article records

(defun fn-stxt-line (str)
  (declare (xargs :guard t))
  (append (fn-record-string-octets (if (stringp str) str "")) '(13 10)))

(defconst *stxt-sk-a* (make-list 32 :initial-element 11))
(defconst *stxt-sk-b* (make-list 32 :initial-element 23))
(defconst *stxt-token* '(9 9))

(make-event (list 'defconst '*stxt-pk-a* (list 'quote (fn-sig-public-key *stxt-sk-a*))))
(make-event (list 'defconst '*stxt-pk-b* (list 'quote (fn-sig-public-key *stxt-sk-b*))))
(make-event (list 'defconst '*stxt-a* (list 'quote (fn-prin-id *stxt-pk-a* *stxt-token*))))
(make-event (list 'defconst '*stxt-b* (list 'quote (fn-prin-id *stxt-pk-b* *stxt-token*))))
(make-event (list 'defconst '*stxt-keyring*
                  (list 'quote (list (cons *stxt-a* *stxt-pk-a*)
                                     (cons *stxt-b* *stxt-pk-b*)))))

(assert-event (fn-prin-keyringp *stxt-keyring*))
(assert-event (not (equal *stxt-a* *stxt-b*)))

(defun fn-stxt-authored (subject body)
  (declare (xargs :guard t))
  (append (fn-stxt-line "From: someone@example.invalid")
          (append (fn-stxt-line "Newsgroups: fn.test")
                  (append (fn-stxt-line (if (stringp subject) subject "Subject: s"))
                          (append (fn-stxt-line "Message-ID: <x@example.invalid>")
                                  (append '(13 10)
                                          (fn-record-string-octets
                                           (if (stringp body) body ""))))))))

; The same authored article with an OCTET body.  A statement whose kind is
; not :article carries its payload as the article body in base64
; (fn-stx-payload-for / fn-stx-body-payload), so a policy statement's
; carrier article cannot have a prose body.
(defun fn-stxt-authored-octets (subject body)
  (declare (xargs :guard t))
  (append (fn-stxt-line "From: someone@example.invalid")
          (append (fn-stxt-line "Newsgroups: fn.test")
                  (append (fn-stxt-line (if (stringp subject) subject "Subject: s"))
                          (append (fn-stxt-line "Message-ID: <x@example.invalid>")
                                  (append '(13 10)
                                          (if (true-listp body) body nil)))))))

(defun fn-stxt-received (field authored)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "FN-Statement: ")
          (append (if (true-listp field) field nil)
                  (append '(13 10) (if (true-listp authored) authored nil)))))

; An article record as the acceptance machine holds it: the received octets
; are the payload, which is what fn-stx-delta projects from.
(defun fn-stxt-record (msgid octets)
  (declare (xargs :guard t))
  (fn-make-article msgid octets nil nil t 841000000))

; A node whose store is exactly `articles`.
(defun fn-stxt-node (articles)
  (declare (xargs :guard t))
  (fn-node-make-state (fn-make-state nil nil articles 0 nil nil) nil nil nil))

(assert-event (equal (fn-stx-store (fn-stxt-node '(1 2 3))) '(1 2 3)))

; -----------------------------------------------------------------------------
; One verified article, one unverified one

(make-event (list 'defconst '*stxt-src-1* (list 'quote (fn-stxt-authored "Subject: one" "first"))))
(make-event (list 'defconst '*stxt-s1*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 1 1 nil :article
                                             *stxt-src-1*))))
(make-event (list 'defconst '*stxt-r1*
                  (list 'quote (fn-stxt-record "<1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-s1*)
                                                  *stxt-src-1*)))))

; The verified article contributes exactly its statement.
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) *stxt-keyring*)
                     (list *stxt-s1*)))

; The SPINE, as a witness: the same bytes under a keyring that does not know
; the creator are stored and contribute nothing to the lace.  Not refused --
; the record is identical; only the authority is gone.
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) nil) nil))

; An article with no field at all: :absent, and again no authority.
(make-event (list 'defconst '*stxt-r0*
                  (list 'quote (fn-stxt-record "<0>" (fn-stxt-authored "Subject: bare" "b")))))
(assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r0*) *stxt-keyring*) nil))
(assert-event (equal (fn-stx-verdict-token
                      (fn-stx-verdict (fn-stx-parse (fn-article-payload *stxt-r0*))
                                      *stxt-keyring* 3))
                     :absent))

; -----------------------------------------------------------------------------
; S3-1: the bridge and the union of ids, on a reachable run
;
; The store is newest-first, so accepting *stxt-r1* onto a store holding
; *stxt-r0* is (cons *stxt-r1* (list *stxt-r0*)).

; The retained node holds HANDLES (records-flip): its article for a record
; carries the handle at which the arena holds the record's octets.  A run is
; its records OLDEST FIRST; the arena seals them in that order (handle k =
; record k), and the node after k acceptances lists the first k newest first.
; Every node lace below is read THROUGH the arena (books/stx-node-lace.lisp
; fn-stx-lace) inside with-local-stobj, so the laces are the real ones; the
; empty lace the old projection read from these nodes is the must-fail at
; the end of this book (PKT-892, planning/evidence/stx-vacuity-2026-09-29.md).
(defun fn-stxt-handle-article (r h)
  (declare (xargs :guard t))
  (fn-make-article (fn-article-msgid r) h (fn-article-groups r)
                   (fn-article-memberships r) (fn-article-pin r)
                   (fn-article-stamp r)))
(defun fn-stxt-handle-store (run k)
  (declare (xargs :guard (and (true-listp run) (natp k))))
  (if (zp k)
      nil
    (cons (fn-stxt-handle-article (nth (- k 1) run) (- k 1))
          (fn-stxt-handle-store run (- k 1)))))
(defun fn-stxt-seal-all (run fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom run)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (fn-article-payload (car run)) fn-arena)))
      (fn-stxt-seal-all (cdr run) fn-arena))))

; Run 1: r0 (bare), then r1 (verified), then the SAME statement offered again
; under a second Message-ID (the `:have' path).
(make-event (list 'defconst '*stxt-r1-again*
                  (list 'quote (fn-stxt-record "<1b>"
                                (fn-stxt-received (fn-stx-header-value *stxt-s1*)
                                                  *stxt-src-1*)))))
(make-event (list 'defconst '*stxt-run-1*
                  (list 'quote (list *stxt-r0* *stxt-r1* *stxt-r1-again*))))
(make-event (list 'defconst '*stxt-h1* (list 'quote (fn-stxt-handle-article *stxt-r1* 1))))
(make-event (list 'defconst '*stxt-h1-again*
                  (list 'quote (fn-stxt-handle-article *stxt-r1-again* 2))))
(make-event (list 'defconst '*stxt-node-0*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-1* 1)))))
(make-event (list 'defconst '*stxt-node-1*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-1* 2)))))
(make-event (list 'defconst '*stxt-node-1b*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-1* 3)))))
; Handles, as the machine holds them.
(assert-event (natp (fn-article-payload (car (fn-stx-store *stxt-node-1*)))))
(assert-event (fn-stx-acceptedp *stxt-node-0* *stxt-node-1* *stxt-h1*))
(assert-event (fn-stx-acceptedp *stxt-node-1* *stxt-node-1b* *stxt-h1-again*))

; The values read through the arena, one pass over run 1.
(defun stxt-run-1-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-stxt-seal-all *stxt-run-1* fn-arena)))
    (mv (list (fn-stx-lace *stxt-node-0* *stxt-keyring* fn-arena)             ; 0
              (fn-stx-lace *stxt-node-1* *stxt-keyring* fn-arena)             ; 1
              (fn-stx-article-delta *stxt-h1* *stxt-keyring* fn-arena)        ; 2
              (fn-stx-lace *stxt-node-1b* *stxt-keyring* fn-arena)            ; 3
              (fn-stx-article-delta *stxt-h1-again* *stxt-keyring* fn-arena)  ; 4
              (fn-stx-lace *stxt-node-1* nil fn-arena))                       ; 5
        fn-arena)))
(defun stxt-run-1 ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-run-1-in fn-arena) x)))
(make-event (list 'defconst '*stxt-v1* (list 'quote (stxt-run-1))))

; NON-EMPTY: the verified article's statement is in the node lace through the
; arena; the bare article contributes nothing; the same bytes under a keyring
; that does not know the creator contribute nothing (the spine).
(assert-event (equal (nth 0 *stxt-v1*) nil))
(assert-event (equal (nth 1 *stxt-v1*) (list *stxt-s1*)))
(assert-event (equal (nth 2 *stxt-v1*) (list *stxt-s1*)))
(assert-event (equal (nth 5 *stxt-v1*) nil))

; S3-1: the bridge and the union of ids, on this run: every hypothesis of
; fn-stx-lace-of-accept-is-merge holds and the conclusion is checked.
(assert-event (fn-stx-delta-freshp (nth 0 *stxt-v1*) (nth 2 *stxt-v1*)))
(assert-event (equal (nth 1 *stxt-v1*) (fn-lace-merge (nth 0 *stxt-v1*) (nth 2 *stxt-v1*))))
(assert-event (equal (fn-lace-ids (nth 1 *stxt-v1*)) (list (fn-stmt-id *stxt-s1*))))
(assert-event (iff (member-equal (fn-stmt-id *stxt-s1*) (fn-lace-ids (nth 1 *stxt-v1*)))
                   (or (member-equal (fn-stmt-id *stxt-s1*) (fn-lace-ids (nth 0 *stxt-v1*)))
                       (member-equal (fn-stmt-id *stxt-s1*) (fn-lace-ids (nth 2 *stxt-v1*))))))

; The `:have' path, exercised rather than assumed: the store grows, the lace's
; ids do not, and the freshness hypothesis of the bridge is FALSE on this run
; -- which is why it is a hypothesis and not a comment.
(assert-event (not (fn-stx-delta-freshp (nth 1 *stxt-v1*) (nth 4 *stxt-v1*))))
(assert-event (equal (fn-lace-ids (nth 3 *stxt-v1*))
                     (list (fn-stmt-id *stxt-s1*) (fn-stmt-id *stxt-s1*))))

; One must-fail case per hypothesis of fn-stx-lace-of-accept-is-merge
; (books/stx-node-lace.lisp), each an assert-event on the NEGATED CONCLUSION.
;
; Hypothesis 1, fn-stx-acceptedp, dropped: a transaction that did not publish
; leaves the store equal.  Freshness still holds here (asserted above), so
; this witness separates the first hypothesis alone, and the delta is
; non-empty so the conclusion is not about nothing.
(assert-event (not (fn-stx-acceptedp *stxt-node-0* *stxt-node-0* *stxt-h1*)))
(assert-event (consp (nth 2 *stxt-v1*)))
(assert-event (not (equal (nth 0 *stxt-v1*)
                          (fn-lace-merge (nth 0 *stxt-v1*) (nth 2 *stxt-v1*)))))

; Hypothesis 2, fn-stx-delta-freshp, dropped: the `:have' path above accepts
; (hypothesis 1 holds there) and is not fresh, and the conclusion fails --
; the lace of the reached node carries the id twice and the merge dedupes.
(assert-event (not (equal (nth 3 *stxt-v1*)
                          (fn-lace-merge (nth 1 *stxt-v1*) (nth 4 *stxt-v1*)))))

; -----------------------------------------------------------------------------
; S3-0: the accepted article comes from the TRANSITION THE HOST CALLS
;
; Every witness above reaches its "next" node with `fn-stxt-node', which
; builds a store by hand.  Such a value is NOT a node state -- the assertion
; below evaluates that -- so nothing above exercised an actual acceptance, and
; `fn-stx-acceptedp' was the assumed observation that
; books/stx-lace.lisp's comment wrongly attributed to a book that has never
; existed.  This section runs the real thing: the durable branch of
; `fn-node-complete', which is the only node step of `fn-sn-finish'
; (books/store-node.lisp line 200), which is the only node step of the host's
; `fn-store-sn-finish' (host/store-node-host.lisp line 402).
;
; Teeth for `fn-stx-durable-completion-is-an-acceptance' (books/stx-lace.lisp).

(assert-event (not (fn-node-statep (fn-stxt-node (list *stxt-r1*)))))

(defconst *stxt-live-0* (fn-node-initial-state '("fn.test") 100))
(assert-event (fn-node-statep *stxt-live-0*))

; The acceptance state holds an article's payload as an arena HANDLE
; (records-flip): the entry seals the octets and stages the handle, 0 here,
; and the lace of the live node is read through the arena (ALPHA below).
(defconst *stxt-live-1*
  (fn-node-prepare *stxt-live-0* 9 "<1>" 0
                   '("fn.test") "archive-1" "content-1" "release-1" 5 841000000))
(assert-event (fn-node-statep *stxt-live-1*))
(assert-event (not (equal *stxt-live-1* *stxt-live-0*)))
(assert-event (fn-node-pending-matchesp *stxt-live-1* 0 9))

(defconst *stxt-live-2* (fn-node-complete *stxt-live-1* 0 9 :durable))
(assert-event (fn-node-statep *stxt-live-2*))

; The keystone instance, evaluated at the transition the host calls.
(assert-event
 (fn-stx-acceptedp *stxt-live-1* *stxt-live-2*
                   (fn-article-from-pending
                    (fn-state-pending (fn-node-acceptance *stxt-live-1*)))))

; Non-degenerate: the store grows by exactly one, and the article it grows by
; carries the signed octets, so the accepted delta is a real statement and not
; the empty one that made two earlier substrate witnesses vacuous.
(assert-event (equal (len (fn-stx-store *stxt-live-1*)) 0))
(assert-event (equal (len (fn-stx-store *stxt-live-2*)) 1))
(assert-event (equal (fn-article-payload
                      (fn-article-from-pending
                       (fn-state-pending (fn-node-acceptance *stxt-live-1*))))
                     0))
; The lace of the live node, read through an arena whose handle 0 holds the
; signed octets: NON-EMPTY, and the S3-1 / S3-3 keystones checked on the run
; the node transition reached.  (Until 2026-09-29 this section asserted the
; EMPTY lace of the old projection as its expected value: PKT-892.)
(make-event (list 'defconst '*stxt-live-run* (list 'quote (list *stxt-r1*))))
(make-event (list 'defconst '*stxt-live-article*
                  (list 'quote (fn-article-from-pending
                                (fn-state-pending (fn-node-acceptance *stxt-live-1*))))))
(defun stxt-live-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-stxt-seal-all *stxt-live-run* fn-arena))
         (delta (fn-stx-article-delta *stxt-live-article* *stxt-keyring* fn-arena))
         (index-2 (fn-stx-index-add (fn-stx-index-empty) delta)))
    (mv (list (fn-stx-lace *stxt-live-1* *stxt-keyring* fn-arena)                     ; 0
              (fn-stx-lace *stxt-live-2* *stxt-keyring* fn-arena)                     ; 1
              delta                                                                   ; 2
              (fn-stx-index-invariantp (fn-stx-index-empty) *stxt-live-1*
                                       *stxt-keyring* fn-arena)                       ; 3
              (fn-stx-index-invariantp index-2 *stxt-live-2* *stxt-keyring* fn-arena) ; 4
              (fn-stx-index-invariantp (fn-stx-index-empty) *stxt-live-2*
                                       *stxt-keyring* fn-arena)                       ; 5
              (fn-stx-index-lookup index-2 (fn-stmt-id *stxt-s1*))                    ; 6
              (fn-articles-wire-of (fn-stx-store *stxt-live-2*) fn-arena))            ; 7
        fn-arena)))
(defun stxt-live ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-live-in fn-arena) x)))
(make-event (list 'defconst '*stxt-lv* (list 'quote (stxt-live))))

(assert-event (equal (nth 0 *stxt-lv*) nil))
(assert-event (equal (nth 1 *stxt-lv*) (list *stxt-s1*)))
(assert-event (equal (nth 2 *stxt-lv*) (list *stxt-s1*)))
; S3-1's conclusion on the run reached by the node transition.
(assert-event (fn-stx-delta-freshp (nth 0 *stxt-lv*) (nth 2 *stxt-lv*)))
(assert-event (equal (nth 1 *stxt-lv*) (fn-lace-merge (nth 0 *stxt-lv*) (nth 2 *stxt-lv*))))
; S3-3's preservation and agreement on the same run: the empty index is the
; node's before, the index plus the accepted delta is the node's after, the
; empty index is NOT the node's after (the invariant is load-bearing), and the
; carried index answers the lookup as the lace does.
(assert-event (nth 3 *stxt-lv*))
(assert-event (nth 4 *stxt-lv*))
(assert-event (not (nth 5 *stxt-lv*)))
(assert-event (equal (nth 6 *stxt-lv*) *stxt-s1*))
(assert-event (equal (fn-lace-lookup (nth 1 *stxt-lv*) (fn-stmt-id *stxt-s1*)) *stxt-s1*))
; ALPHA of the live node, for the loop witness at the end of this book.
(make-event (list 'defconst '*stxt-live-2-alpha* (list 'quote (nth 7 *stxt-lv*))))
(assert-event (equal (fn-stx-lace-of-store *stxt-live-2-alpha* *stxt-keyring*)
                     (list *stxt-s1*)))

; Tooth: through an arena that does not hold the handle there are no bytes
; and no statement -- the lace is the arena's denotation, not the handle's
; number.
(defun stxt-live-unsealed-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (fn-stx-lace *stxt-live-2* *stxt-keyring* fn-arena) fn-arena))
(defun stxt-live-unsealed ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-live-unsealed-in fn-arena) x)))
(assert-event (equal (stxt-live-unsealed) nil))

; -----------------------------------------------------------------------------
; The lace of the RETAINED store (books/stx-lace-rows.lisp): the wire record
; carrying the signed octets, interned under the keyring, is a row whose
; context holds the delta; the rows' lace is the statement, with no byte
; re-read, and it is the wire lace of the rows' articles through the arena.
(defconst *stxt-w1*
  (fn-record-make 1 0 9 "<1>" (fn-article-payload *stxt-r1*) '("fn.test")
                  "archive-1" "content-1" "release-1" 5 841000000))
(assert-event (fn-record-p *stxt-w1*))
; The rows' HANDLE articles, as the acceptance node would list them (newest
; first, each payload the row's handle): the correspondence hypothesis of
; fn-stx-lace-of-node-is-the-rows-lace, built to hold.
(defun fn-stxt-rows-handle-articles (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-held-p (car rows))
         (append (fn-stxt-rows-handle-articles (cdr rows))
                 (list (fn-make-article (fn-record-msgid (car rows))
                                        (fn-record-payload (car rows))
                                        (fn-record-groups (car rows))
                                        (fn-held-numbers (car rows)) t
                                        (fn-record-stamp (car rows))))))
        (t (fn-stxt-rows-handle-articles (cdr rows)))))
(defun stxt-rows-in (ws keyring fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events ws keyring 0 fn-arena)
    (let ((node (fn-stxt-node (fn-stxt-rows-handle-articles rows))))
      (mv (list rows                                                          ; 0
                (fn-rows-articles-newest-first rows fn-arena)                 ; 1
                (fn-rows-contexts-okp rows *stxt-keyring* 0 fn-arena)         ; 2
                (equal (fn-articles-wire-of (fn-stx-store node) fn-arena)
                       (fn-rows-articles-newest-first rows fn-arena))         ; 3
                (fn-stx-lace node *stxt-keyring* fn-arena))                   ; 4
          fn-arena))))
(defun stxt-rows (ws keyring)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-rows-in ws keyring fn-arena) x)))
(make-event (list 'defconst '*stxt-rows* (list 'quote (stxt-rows (list *stxt-w1*) *stxt-keyring*))))
; Positive witness of fn-sn-lace-of-rows-is-the-wire-lace: the hypothesis
; holds, both sides are the one statement.
(assert-event (nth 2 *stxt-rows*))
(assert-event (equal (fn-sn-lace-of-rows (nth 0 *stxt-rows*)) (list *stxt-s1*)))
(assert-event (equal (fn-stx-lace-of-store (nth 1 *stxt-rows*) *stxt-keyring*)
                     (list *stxt-s1*)))
; fn-sn-index-of-rows-agrees-with-lace on the same rows.
(assert-event (equal (fn-stx-index-lookup (fn-sn-index-of-rows (nth 0 *stxt-rows*))
                                          (fn-stmt-id *stxt-s1*))
                     *stxt-s1*))
; Positive witness of fn-stx-lace-of-node-is-the-rows-lace (PRF-995): both
; hypotheses hold and the node lace through the arena is the rows' lace, the
; one statement.
(assert-event (nth 3 *stxt-rows*))
(assert-event (equal (nth 4 *stxt-rows*) (fn-sn-lace-of-rows (nth 0 *stxt-rows*))))
(assert-event (equal (nth 4 *stxt-rows*) (list *stxt-s1*)))
; Tooth: rows interned under ANOTHER keyring (none) fail the context
; invariant for this one, and both conclusions fail with it: the rows' lace is
; empty while the wire lace of the same bytes under this keyring is not, and
; so is the node lace through the arena (the correspondence still holds).
(make-event (list 'defconst '*stxt-rows-nil* (list 'quote (stxt-rows (list *stxt-w1*) nil))))
(assert-event (not (nth 2 *stxt-rows-nil*)))
(assert-event (equal (fn-sn-lace-of-rows (nth 0 *stxt-rows-nil*)) nil))
(assert-event (not (equal (fn-sn-lace-of-rows (nth 0 *stxt-rows-nil*))
                          (fn-stx-lace-of-store (nth 1 *stxt-rows-nil*) *stxt-keyring*))))
(assert-event (nth 3 *stxt-rows-nil*))
(assert-event (not (equal (nth 4 *stxt-rows-nil*) (fn-sn-lace-of-rows (nth 0 *stxt-rows-nil*)))))

; The one hypothesis, dropped, on two concrete violating values.  Both calls
; are inside `fn-node-complete's guard (both states are node states), so no
; guard relaxation is needed.
;
; (a) No pending at all: the completion is a no-op and the store does not grow.
(assert-event (not (fn-node-pending-matchesp *stxt-live-0* 0 9)))
(assert-event
 (not (fn-stx-acceptedp *stxt-live-0*
                        (fn-node-complete *stxt-live-0* 0 9 :durable)
                        (fn-article-from-pending
                         (fn-state-pending (fn-node-acceptance *stxt-live-0*))))))
; (b) A pending that does not match the transaction offered: same refusal, and
; here the node DOES hold a stage, so the tooth separates the matching test
; rather than the existence of a proposal.
(assert-event (consp (fn-node-stage *stxt-live-1*)))
(assert-event (not (fn-node-pending-matchesp *stxt-live-1* 1 9)))
(assert-event
 (not (fn-stx-acceptedp *stxt-live-1*
                        (fn-node-complete *stxt-live-1* 1 9 :durable)
                        (fn-article-from-pending
                         (fn-state-pending (fn-node-acceptance *stxt-live-1*))))))

; -----------------------------------------------------------------------------
; S3-2: equivocation.  One key, one (creator, incarnation, sequence), two
; payloads: the D10 restore-from-snapshot fork, arriving at transit.

(make-event (list 'defconst '*stxt-src-f1* (list 'quote (fn-stxt-authored "Subject: fork" "left"))))
(make-event (list 'defconst '*stxt-src-f2* (list 'quote (fn-stxt-authored "Subject: fork" "right"))))
(make-event (list 'defconst '*stxt-f1*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 2 5 nil :article *stxt-src-f1*))))
(make-event (list 'defconst '*stxt-f2*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 2 5 nil :article *stxt-src-f2*))))
(make-event (list 'defconst '*stxt-rf1*
                  (list 'quote (fn-stxt-record "<f1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-f1*) *stxt-src-f1*)))))
(make-event (list 'defconst '*stxt-rf2*
                  (list 'quote (fn-stxt-record "<f2>"
                                (fn-stxt-received (fn-stx-header-value *stxt-f2*) *stxt-src-f2*)))))

; The A-CRYPTO edge is not assumed away: the two forks have distinct content
; ids under the toy digest, which is the hypothesis fn-lace-merge-drops-at-
; collision says is needed.
(assert-event (not (equal (fn-stmt-id *stxt-f1*) (fn-stmt-id *stxt-f2*))))
(assert-event (fn-lace-same-slotp *stxt-f1* *stxt-f2*))

; Run f: f1 accepted, then f2 -- the fork arrives at transit.
(make-event (list 'defconst '*stxt-run-f* (list 'quote (list *stxt-rf1* *stxt-rf2*))))
(make-event (list 'defconst '*stxt-hf2* (list 'quote (fn-stxt-handle-article *stxt-rf2* 1))))
(make-event (list 'defconst '*stxt-fork-a*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-f* 1)))))
(make-event (list 'defconst '*stxt-fork-ab*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-f* 2)))))
(assert-event (fn-stx-acceptedp *stxt-fork-a* *stxt-fork-ab* *stxt-hf2*))

(defun stxt-run-f-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((fn-arena (fn-stxt-seal-all *stxt-run-f* fn-arena))
         (alpha-a (fn-articles-wire-of (fn-stx-store *stxt-fork-a*) fn-arena))
         (alpha-ab (fn-articles-wire-of (fn-stx-store *stxt-fork-ab*) fn-arena))
         (index-a (fn-stx-index-of-store alpha-a *stxt-keyring*))
         (index-ab (fn-stx-index-of-store alpha-ab *stxt-keyring*))
         (delta (fn-stx-article-delta *stxt-hf2* *stxt-keyring* fn-arena)))
    (mv (list (fn-stx-lace *stxt-fork-a* *stxt-keyring* fn-arena)                    ; 0
              (fn-stx-lace *stxt-fork-ab* *stxt-keyring* fn-arena)                   ; 1
              delta                                                                  ; 2
              index-ab                                                               ; 3
              (fn-stx-index-invariantp index-ab *stxt-fork-ab* *stxt-keyring* fn-arena) ; 4
              (fn-stx-index-invariantp (fn-stx-index-empty) *stxt-fork-ab*
                                       *stxt-keyring* fn-arena)                      ; 5
              (fn-stx-index-invariantp (fn-stx-index-add index-a delta) *stxt-fork-ab*
                                       *stxt-keyring* fn-arena)                      ; 6
              (fn-stx-index-invariantp index-a *stxt-fork-a* *stxt-keyring* fn-arena)) ; 7
        fn-arena)))
(defun stxt-run-f ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-run-f-in fn-arena) x)))
(make-event (list 'defconst '*stxt-vf* (list 'quote (stxt-run-f))))

; Every hypothesis of fn-stx-transit-equivocation-is-detected holds on this
; run: accepted (above), fresh, s1 = f1 in the lace before, the delta is
; exactly (f2), the two are distinct and share a slot.
(assert-event (fn-stx-delta-freshp (nth 0 *stxt-vf*) (nth 2 *stxt-vf*)))
(assert-event (member-equal *stxt-f1* (nth 0 *stxt-vf*)))
(assert-event (equal (nth 2 *stxt-vf*) (list *stxt-f2*)))
; BOTH FORKS ARE KEPT, and the equivocation is visible after the merge.
(assert-event (member-equal *stxt-f1* (nth 1 *stxt-vf*)))
(assert-event (member-equal *stxt-f2* (nth 1 *stxt-vf*)))
(assert-event (fn-lace-equivocatorp (nth 1 *stxt-vf*) *stxt-a* 2))
; And it was not visible before: the hypothesis that the two are distinct and
; share a slot is doing the work.
(assert-event (not (fn-lace-equivocatorp (nth 0 *stxt-vf*) *stxt-a* 2)))
; A different incarnation is not an equivocation of this one.
(assert-event (not (fn-lace-equivocatorp (nth 1 *stxt-vf*) *stxt-a* 1)))
; Nor is another principal implicated.
(assert-event (not (fn-lace-equivocatorp (nth 1 *stxt-vf*) *stxt-b* 2)))

; -----------------------------------------------------------------------------
; S3-3: the index twin, on the same run.  The record names both ids.

(make-event (list 'defconst '*stxt-index-ab* (list 'quote (nth 3 *stxt-vf*))))
; The invariant holds of the index built over ALPHA (positive witness of
; fn-stx-index-agrees-with-lace's hypothesis), and the queries agree.
(assert-event (nth 4 *stxt-vf*))
(assert-event (equal (fn-stx-index-lookup *stxt-index-ab* (fn-stmt-id *stxt-f1*))
                     (fn-lace-lookup (nth 1 *stxt-vf*) (fn-stmt-id *stxt-f1*))))
(assert-event (fn-stx-index-equivocatorp *stxt-index-ab* *stxt-a* 2))
(assert-event (fn-stx-recorded-equivocationp *stxt-index-ab* *stxt-a* 2))
(assert-event (not (fn-stx-index-equivocatorp *stxt-index-ab* *stxt-a* 1)))
; The record is a discovery aid that names the pair, oldest id first.
(assert-event (equal (fn-stx-index-records *stxt-index-ab*)
                     (list (fn-stx-equivocation-record *stxt-f1* *stxt-f2*))))
(assert-event (equal (fn-stx-record-id-held
                      (car (fn-stx-index-records *stxt-index-ab*)))
                     (fn-stmt-id *stxt-f1*)))
(assert-event (equal (fn-stx-record-id-new
                      (car (fn-stx-index-records *stxt-index-ab*)))
                     (fn-stmt-id *stxt-f2*)))
; The invariant is load-bearing: an index that is not this store's index says
; nothing about this store's lace.
(assert-event (not (nth 5 *stxt-vf*)))
(assert-event (not (fn-stx-index-equivocatorp (fn-stx-index-empty) *stxt-a* 2)))
; fn-stx-index-invariant-preserved-by-accept on this run: the index of the
; node before, plus the accepted delta, is the node's after.
(assert-event (nth 7 *stxt-vf*))
(assert-event (nth 6 *stxt-vf*))

; -----------------------------------------------------------------------------
; S4-1: a peer cannot widen a group's policy
;
; A is the configured authority for fn.test at this node.  B is a hostile
; peer with a perfectly valid signature over a perfectly valid policy for the
; same group -- and it changes nothing, because B is not the authority.

(defconst *stxt-group* (fn-record-string-octets "fn.test"))

(make-event (list 'defconst '*stxt-policy-a*
                  (list 'quote (fn-pol-policy-encode
                                (fn-pol-make-policy *stxt-group* (list *stxt-b*) nil)))))
(make-event (list 'defconst '*stxt-pol-stmt-a*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 1 9 nil :policy
                                             *stxt-policy-a*))))
(make-event (list 'defconst '*stxt-pol-stmt-b*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 1 9 nil :policy
                                             *stxt-policy-a*))))

(defun fn-stxt-policy-record (msgid statement source)
  (declare (xargs :guard t))
  (fn-stxt-record msgid (fn-stxt-received (fn-stx-header-value statement) source)))

; The body is the base64 of the signed policy octets, which is what
; fn-stx-payload-for projects for a :policy statement.  With a prose body
; the reconstructed statement carries the wrong payload, its signature does
; not verify, fn-stx-delta is nil, and every assertion below about the
; hostile batch passes VACUOUSLY -- which is what the non-degeneracy tooth
; on *stxt-real-batch* caught.
(make-event (list 'defconst '*stxt-src-p*
                  (list 'quote (fn-stxt-authored-octets
                                "Subject: policy"
                                (fn-stx-b64-encode *stxt-policy-a*)))))
(make-event (list 'defconst '*stxt-rp-a*
                  (list 'quote (fn-stxt-policy-record "<pa>" *stxt-pol-stmt-a* *stxt-src-p*))))
(make-event (list 'defconst '*stxt-rp-b*
                  (list 'quote (fn-stxt-policy-record "<pb>" *stxt-pol-stmt-b* *stxt-src-p*))))

; A policy statement travels as an ordinary article: it decodes to a policy
; and is a candidate only for its own creator.
(assert-event (fn-pol-candidatep *stxt-pol-stmt-a* *stxt-keyring* *stxt-group* *stxt-a*))
(assert-event (not (fn-pol-candidatep *stxt-pol-stmt-b* *stxt-keyring* *stxt-group* *stxt-a*)))

; The hostile batch: B's signed policy for A's group.
(make-event (list 'defconst '*stxt-hostile-batch* (list 'quote (list *stxt-rp-b*))))
; Non-vacuity FIRST: B's statement really is in the delta.  It is stored and
; it verifies; what it does not have is authority.  Without this line the
; three assertions below hold of an EMPTY delta and say nothing, which is
; how this book stood before w10/substrate-2.
(assert-event (equal (fn-stx-batch-delta *stxt-hostile-batch* *stxt-keyring*)
                     (list *stxt-pol-stmt-b*)))
(assert-event (fn-pol-delta-without-authority-p
               (fn-stx-batch-delta *stxt-hostile-batch* *stxt-keyring*)
               *stxt-keyring* *stxt-a*))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-hostile-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     (fn-pol-current (fn-stx-lace-of-store nil *stxt-keyring*)
                                     *stxt-keyring* *stxt-group* *stxt-a*)))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-hostile-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     nil))

; The genuine authority's batch DOES change it, so the theorem is not vacuous.
(make-event (list 'defconst '*stxt-real-batch* (list 'quote (list *stxt-rp-a*))))
(assert-event (equal (fn-stx-batch-delta *stxt-real-batch* *stxt-keyring*)
                     (list *stxt-pol-stmt-a*)))
(assert-event (not (fn-pol-delta-without-authority-p
                    (fn-stx-batch-delta *stxt-real-batch* *stxt-keyring*)
                    *stxt-keyring* *stxt-a*)))
(assert-event (equal (fn-pol-current
                      (fn-stx-lace-of-store
                       (fn-stx-accept-batch nil *stxt-real-batch*) *stxt-keyring*)
                      *stxt-keyring* *stxt-group* *stxt-a*)
                     *stxt-pol-stmt-a*))
; And the offender is named.
(assert-event (equal (fn-pol-first-authority-stmt
                      (fn-stx-batch-delta *stxt-real-batch* *stxt-keyring*)
                      *stxt-keyring* *stxt-a*)
                     *stxt-pol-stmt-a*))

; The gate, on a node that holds A's policy admitting B -- the node's article
; a handle, the policy's octets in the arena.
(make-event (list 'defconst '*stxt-run-p* (list 'quote (list *stxt-rp-a*))))
(make-event (list 'defconst '*stxt-pol-node*
                  (list 'quote (fn-stxt-node (fn-stxt-handle-store *stxt-run-p* 1)))))
(make-event (list 'defconst '*stxt-src-post* (list 'quote (fn-stxt-authored "Subject: post" "hi"))))
(make-event (list 'defconst '*stxt-post-b*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 1 1 nil :article
                                             *stxt-src-post*))))
(make-event (list 'defconst '*stxt-r-post-b*
                  (list 'quote (fn-stxt-record "<pb1>"
                                (fn-stxt-received (fn-stx-header-value *stxt-post-b*)
                                                  *stxt-src-post*)))))
(make-event (list 'defconst '*stxt-article-post-b*
                  (list 'quote (fn-stx-parse (fn-article-payload *stxt-r-post-b*)))))

(defun stxt-run-p-in (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-stxt-seal-all *stxt-run-p* fn-arena)))
    (mv (list (fn-stx-lace *stxt-pol-node* *stxt-keyring* fn-arena)                    ; 0
              (fn-stx-transit-authority-ok *stxt-pol-node* *stxt-article-post-b*
                                           *stxt-keyring* *stxt-group* *stxt-a* fn-arena) ; 1
              (fn-stx-transit-authority-ok (fn-stxt-node nil) *stxt-article-post-b*
                                           *stxt-keyring* *stxt-group* *stxt-a* fn-arena) ; 2
              (fn-stx-transit-authority-ok *stxt-pol-node* *stxt-article-post-b*
                                           nil *stxt-group* *stxt-a* fn-arena)          ; 3
              (fn-stx-authority-outcome (fn-stx-index-empty) *stxt-pol-node*
                                        *stxt-article-post-b* *stxt-keyring* *stxt-group*
                                        *stxt-a* fn-arena)                              ; 4
              (fn-pol-current (fn-stx-lace *stxt-pol-node* *stxt-keyring* fn-arena)
                              *stxt-keyring* *stxt-group* *stxt-a*))                    ; 5
        fn-arena)))
(defun stxt-run-p ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (stxt-run-p-in fn-arena) x)))
(make-event (list 'defconst '*stxt-vp* (list 'quote (stxt-run-p))))

; The node lace through the arena holds A's policy statement, and the gate
; OPENS for B's post (positive witness of fn-stx-transit-admission-is-grounded:
; the policy in force is A's, a member of the lace).
(assert-event (equal (nth 0 *stxt-vp*) (list *stxt-pol-stmt-a*)))
(assert-event (nth 1 *stxt-vp*))
(assert-event (equal (nth 5 *stxt-vp*) *stxt-pol-stmt-a*))
(assert-event (member-equal (nth 5 *stxt-vp*) (nth 0 *stxt-vp*)))
(assert-event (equal (nth 4 *stxt-vp*) :admitted))
; With no policy in force the same article admits nothing.
(assert-event (not (nth 2 *stxt-vp*)))
; And an unverified statement admits nothing whatever the policy says.
(assert-event (not (nth 3 *stxt-vp*)))

; -----------------------------------------------------------------------------
; S5-1: the commit carrier
;
; A commit enters the merge only from a verified statement.

(defconst *stxt-commit*
  (fn-me-commit '(1 1 1) 0 '(2 2) :remove '(3 3)))
(assert-event (fn-me-commitp *stxt-commit*))
(assert-event (fn-stmt-okp (fn-stx-commit-decode-exact
                            (fn-stx-commit-encode *stxt-commit*))))
(assert-event (equal (fn-stmt-value (fn-stx-commit-decode-exact
                                     (fn-stx-commit-encode *stxt-commit*)))
                     *stxt-commit*))

(make-event (list 'defconst '*stxt-commit-stmt-a*
                  (list 'quote (fn-stmt-sign *stxt-sk-a* *stxt-a* 3 1 nil :policy
                                             (fn-stx-commit-encode *stxt-commit*)))))
(make-event (list 'defconst '*stxt-commit-stmt-x*
                  (list 'quote (fn-stmt-sign *stxt-sk-b* *stxt-b* 3 1 nil :policy
                                             (fn-stx-commit-encode *stxt-commit*)))))
; The carrier article's body is the base64 of THIS statement's payload --
; the commit encoding, not the policy encoding of the section above.
(make-event (list 'defconst '*stxt-src-c*
                  (list 'quote
                        (fn-stxt-authored-octets
                         "Subject: commit"
                         (fn-stx-b64-encode
                          (fn-stx-commit-encode *stxt-commit*))))))
(make-event (list 'defconst '*stxt-rc-ok*
                  (list 'quote (fn-stxt-policy-record "<c1>" *stxt-commit-stmt-a*
                                                      *stxt-src-c*))))
(make-event (list 'defconst '*stxt-rc-bad*
                  (list 'quote (fn-stxt-policy-record "<c2>" *stxt-commit-stmt-x*
                                                      *stxt-src-c*))))

; One verified and one unverified commit-bearing article: under a keyring
; that knows only A, the delta is the singleton.
(make-event (list 'defconst '*stxt-keyring-a* (list 'quote (list (cons *stxt-a* *stxt-pk-a*)))))
(make-event (list 'defconst '*stxt-commit-batch* (list 'quote (list *stxt-rc-ok* *stxt-rc-bad*))))

(assert-event (equal (fn-stx-commits-of-batch *stxt-commit-batch* *stxt-keyring-a*)
                     (list *stxt-commit*)))
; The tooth: an unverified article contributes NO commit.
(assert-event (equal (fn-stx-commits-of-batch (list *stxt-rc-bad*) *stxt-keyring-a*)
                     nil))
; And with both known, both contribute -- so the keyring hypothesis is what
; is doing the work, not the shape of the batch.
(assert-event (equal (len (fn-stx-commits-of-batch *stxt-commit-batch* *stxt-keyring*)) 2))

; The merge moves commits and NOT the chain: adoption stays local.
(defconst *stxt-site*
  (fn-me-site '(7) '(8) nil nil 4 4 nil))
(assert-event (fn-me-sitep *stxt-site*))
(assert-event (equal (fn-me-chain (fn-me-site-merge
                                   *stxt-site*
                                   (fn-stx-commits-of-batch *stxt-commit-batch*
                                                            *stxt-keyring-a*)))
                     (fn-me-chain *stxt-site*)))
(assert-event (equal (fn-me-epoch (fn-me-site-merge
                                   *stxt-site*
                                   (fn-stx-commits-of-batch *stxt-commit-batch*
                                                            *stxt-keyring-a*)))
                     0))
(assert-event (consp (fn-me-commits (fn-me-site-merge
                                     *stxt-site*
                                     (fn-stx-commits-of-batch *stxt-commit-batch*
                                                              *stxt-keyring-a*)))))
; Adoption, by contrast, does extend the chain -- so the contrast is real.
(assert-event (equal (len (fn-me-chain (fn-me-adopt *stxt-site* *stxt-commit*))) 1))

; fn-stx-index-of-store by a loop (PKT-876, PRF-352): the reversed left fold
; is the right fold on the live store above, and 50,000 articles fold.
(assert-event
 (equal (fn-stx-index-of-store *stxt-live-2-alpha* *stxt-keyring*)
        (fn-stx-index-of-store-loop (reverse *stxt-live-2-alpha*) *stxt-keyring*
                                    (fn-stx-index-empty))))
(assert-event
 (equal (fn-stx-index-of-store
         (append (make-list 50000 :initial-element (car *stxt-live-2-alpha*))
                 *stxt-live-2-alpha*)
         nil)
        (fn-stx-index-empty)))

; -----------------------------------------------------------------------------
; PKT-892, as must-fails.  Each of these PROVED on 2026-09-29 against the
; previous fn-stx-lace (the octet model applied to the node's handle articles:
; planning/evidence/stx-vacuity-2026-09-29.md), with the node lace forced
; empty.  Through the arena they are false, and the runs above are their
; counterexamples: run 1's node-1 and the live node have the lace (s1), the
; gate opens on run p, the index of run f is not the empty one.
(defun stxt-handle-articles-p (articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (and (natp (fn-article-payload (car articles)))
           (stxt-handle-articles-p (cdr articles)))
    t))
(assert-event (stxt-handle-articles-p (fn-stx-store *stxt-node-1*)))
(assert-event (stxt-handle-articles-p (fn-stx-store *stxt-live-2*)))
(must-fail-checked
 (defthm stxt-lace-of-a-handle-node-is-nil
   (implies (stxt-handle-articles-p (fn-stx-store node))
            (equal (fn-stx-lace node keyring fn-arena) nil))))
(must-fail-checked
 (defthm stxt-gate-never-opens-over-a-handle-node
   (implies (stxt-handle-articles-p (fn-stx-store node))
            (not (fn-stx-transit-authority-ok node article keyring group authority
                                              fn-arena)))))
(must-fail-checked
 (defthm stxt-index-invariant-forces-the-empty-index
   (implies (stxt-handle-articles-p (fn-stx-store node))
            (iff (fn-stx-index-invariantp index node keyring fn-arena)
                 (equal index (fn-stx-index-empty))))))
(must-fail-checked
 (defthm stxt-merge-holds-without-acceptance
   (implies (and (stxt-handle-articles-p (fn-stx-store node))
                 (stxt-handle-articles-p (fn-stx-store next))
                 (natp (fn-article-payload article)))
            (equal (fn-stx-lace next keyring fn-arena)
                   (fn-lace-merge (fn-stx-lace node keyring fn-arena)
                                  (fn-stx-article-delta article keyring fn-arena))))))
(must-fail-checked
 (defthm stxt-propagates-antecedent-unsatisfiable
   (implies (natp (fn-article-payload article))
            (not (equal (list s) (fn-stx-article-delta article keyring fn-arena))))))
