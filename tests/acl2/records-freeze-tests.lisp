; fn: teeth for books/records-freeze.lisp (the records freeze, PKT-293; lane
; records-freeze, 2026-09-26).
;
; What this book is evidence FOR.  `fn-rfz-intern-extent' and
; `fn-rfz-served-bytes-by-definition' say the interned handle's extent is
; the octets fact and its bytes are the wire payload; `fn-rfz-projection-
; bytes-by-definition' says the codec over the materialized held record is
; the wire encoding; `fn-rfz-replay-index-over-both-views' and
; `fn-rfz-replay-verdicts-over-both-views' say that under the context
; invariant the retained view's folds (contexts, no bytes) are the store's
; folds over the bytes; `fn-rfz-load-establishes-contexts' says the load
; establishes the invariant; `fn-rfz-pinned-rows-survive-seals', the two
; reclaim theorems and the versioned mapping say a pinned reader's payload
; survives reclamation.  Each gets a ground positive witness asserting its
; complete antecedent and conclusion, and for each hypothesis a witness on
; which the retained hypotheses hold, the omitted one fails and the
; conclusion fails, with a `must-fail' of the conclusion.  The exec path
; runs on a live local arena and a live local catalog.  A signed article
; (the fixture of tests/acl2/stx-tests.lisp) gives the index theorem a
; non-empty index on both sides.

(in-package "ACL2")
(include-book "../../books/records-freeze")
(include-book "crypto-seam-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-rfz-handles-inp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-wire-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-articles-of-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-contexts-okp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-lacesp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-index-of-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-verdicts-of-rows (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-verdicts-of-wire (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-row-with-handle (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-redirectsp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-rfz-resolve (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$l-seal-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$l-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-arena$c-seal-list (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground values: two articles, a retention event between them, the history.

(defconst *rft-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *rft-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10 68 13 10)))
(defconst *rft-w0* (fn-record-make 0 1 1 "<a@x>" *rft-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *rft-r1* (fn-store-retention-event-make :undertake 1 2 2 "id" "subject" "evidence" 3))
(defconst *rft-w2* (fn-record-make 2 3 3 "<c@x>" *rft-p2* '("fn.test") "o" "s" "e" 1 5))
(defconst *rft-h* (list *rft-w0* *rft-r1* *rft-w2*))
(defconst *rft-tomb* '(84 79 77 66))

(assert-event (and (fn-record-p *rft-w0*) (fn-record-p *rft-w2*) (not (fn-record-p *rft-r1*))
                   (fn-prin-keyringp nil) (fn-cbor-octet-listp *rft-tomb*)))

; The loaded state on the logical side (the fold from the empty creators):
; the arena is the two payloads, the catalog the two rows over handles 0
; and 1 with their numbers assigned.
(defun rft-held (w handle keyring generation)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) keyring generation) nil nil))
(defconst *rft-a* (list *rft-p0* *rft-p2*))
(defconst *rft-c*
  (list (fn-cat-assign (rft-held *rft-w0* 0 nil 0) nil)
        (fn-cat-assign (rft-held *rft-w2* 1 nil 0)
                       (list (fn-cat-assign (rft-held *rft-w0* 0 nil 0) nil)))))

(defthm rft-w-loaded-is-the-fold
  (mv-let (a c)
    (fn-cat-load *rft-h* nil 0 nil nil)
    (and (equal a *rft-a*) (equal c *rft-c*)
         (fn-cat-p c) (fn-rfz-handles-inp c a) (fn-rfz-contexts-okp c nil 0 a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rfz-contexts-okp))))

; -----------------------------------------------------------------------------
; 1. The handle's coordinates (no hypothesis: positive witnesses).

(defthm rft-w-extent-and-identity
  (mv-let (held a2)
    (fn-cat-intern-list *rft-w0* nil 1 nil)
    (and (equal (fn-record-payload held) 0)
         (equal (fn-arena-payload-len (fn-record-payload held) a2)
                (fn-hf-octets (fn-held-facts held)))
         (equal (fn-hf-octets (fn-held-facts held)) (len *rft-p0*))
         (equal (fn-arena-payload (fn-record-payload held) a2) *rft-p0*)))
  :rule-classes nil)

; The projection's bytes: the positive witness (a record), and the
; hypothesis removed: an improper list with a record's positions is not a
; shape, its materialization is a record, and only one side encodes.
(defthm rft-w-projection-bytes
  (and (fn-record-shapep *rft-w0*)
       (mv-let (held a2)
         (fn-cat-intern-list *rft-w0* nil 1 nil)
         (and (equal (fn-held-wire-of held a2) *rft-w0*)
              (equal (fn-record-encode (fn-held-wire-of held a2)) (fn-record-encode *rft-w0*)))))
  :rule-classes nil)

(defconst *rft-w-dotted* (append *rft-w0* 7))
(defthm rft-w-projection-bytes-without-shape
  (and (not (fn-record-shapep *rft-w-dotted*))
       (mv-let (held a2)
         (fn-cat-intern-list *rft-w-dotted* nil 1 nil)
         (and (equal (fn-held-wire-of held a2) *rft-w0*)
              (fn-record-p (fn-held-wire-of held a2))
              (not (fn-record-p *rft-w-dotted*))
              (equal (fn-record-encode *rft-w-dotted*) nil)
              (not (equal (fn-record-encode (fn-held-wire-of held a2))
                          (fn-record-encode *rft-w-dotted*))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-record-shapep))))
(must-fail
 (defthm rft-r-projection-bytes-without-shape
   (mv-let (held a2)
     (fn-cat-intern-list *rft-w-dotted* nil 1 nil)
     (equal (fn-record-encode (fn-held-wire-of held a2)) (fn-record-encode *rft-w-dotted*)))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; 2. Replay over both views.

; The verdicts: the positive witness on the loaded rows (two rows, two
; Message-IDs, each verdict the one fn-sn-finish would decide from the
; bytes under the empty keyring at generation 0).
(defthm rft-w-replay-verdicts
  (and (fn-rfz-contexts-okp *rft-c* nil 0 *rft-a*)
       (equal (fn-rfz-verdicts-of-rows *rft-c*)
              (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows *rft-c* *rft-a*) nil 0))
       (equal (fn-rfz-verdicts-of-rows *rft-c*)
              (list (cons "<a@x>" (fn-stx-verdict-of-octets *rft-p0* nil 0))
                    (cons "<c@x>" (fn-stx-verdict-of-octets *rft-p2* nil 0))))
       (not (equal (fn-stx-verdict-of-octets *rft-p0* nil 0) nil)))
  :rule-classes nil)

; The index over the loaded rows: the positive witness under the empty
; keyring (both sides the empty index: no statement verifies) ...
(defthm rft-w-replay-index-empty-keyring
  (and (fn-rfz-contexts-okp *rft-c* nil 0 *rft-a*)
       (equal (fn-rfz-index-of-rows *rft-c*)
              (fn-stx-index-of-store (fn-rfz-articles-of-rows *rft-c* *rft-a*) nil))
       (equal (fn-rfz-index-of-rows *rft-c*) (fn-stx-index-empty)))
  :rule-classes nil)

; ... and NON-EMPTY on both sides: a signed article under the keyring that
; verifies it (the fixture of tests/acl2/stx-tests.lisp), interned at
; generation 7; the index binds the statement.
(defun rft-line (str)
  (declare (xargs :guard t))
  (append (fn-record-string-octets (if (stringp str) str "")) '(13 10)))
(defconst *rft-sk* (make-list 32 :initial-element 7))
(make-event (list 'defconst '*rft-pk* (list 'quote (fn-sig-public-key *rft-sk*))))
(make-event (list 'defconst '*rft-creator* (list 'quote (fn-prin-id *rft-pk* '(1 2 3)))))
(defconst *rft-keyring* (list (cons *rft-creator* *rft-pk*)))
(assert-event (fn-prin-keyringp *rft-keyring*))
(defconst *rft-authored*
  (append (rft-line "From: agent-a@example.invalid")
          (append (rft-line "Newsgroups: fn.test")
                  (append (rft-line "Subject: hello")
                          (append (rft-line "Message-ID: <a1@example.invalid>")
                                  (append '(13 10) (fn-record-string-octets "body line")))))))
(make-event (list 'defconst '*rft-statement*
                  (list 'quote (fn-stmt-sign *rft-sk* *rft-creator* 1 1 nil :article *rft-authored*))))
(make-event (list 'defconst '*rft-field* (list 'quote (fn-stx-header-value *rft-statement*))))
(defconst *rft-signed*
  (append (fn-record-string-octets "FN-Statement: ")
          (append *rft-field* (append '(13 10) *rft-authored*))))
(defconst *rft-ws* (fn-record-make 0 1 1 "<a1@example.invalid>" *rft-signed* '("fn.test") "o" "s" "e" 1 5))
(assert-event (and (fn-record-p *rft-ws*)
                   (equal (fn-stx-delta *rft-signed* *rft-keyring*) (list *rft-statement*))))

(defconst *rft-as* (list *rft-signed*))
; The context of the signed bytes reaches the statement codec through its
; attachment, so the row is built by make-event and the witness is checked
; by evaluation (assert-event), as stx-tests does; a defthm may not use an
; attachment (:DOC ignored-attachment).
(make-event (list 'defconst '*rft-cs*
                  (list 'quote (list (fn-cat-assign (rft-held *rft-ws* 0 *rft-keyring* 7) nil)))))

; An evaluation names a stobj only by its variable, so the invariant's one
; conjunct and the row's article are written out (the arena *rft-as* holds
; the signed bytes at handle 0).
(assert-event
  (and (equal (fn-held-context (car *rft-cs*))
              (fn-held-context-of (nth 0 *rft-as*) *rft-keyring* 7))
       (equal (fn-record-payload (car *rft-cs*)) 0)
       (equal (fn-rfz-index-of-rows *rft-cs*)
              (fn-stx-index-of-store
               (list (fn-make-article (fn-record-msgid (car *rft-cs*)) (nth 0 *rft-as*)
                                      (fn-record-groups (car *rft-cs*))
                                      (fn-held-numbers (car *rft-cs*)) t
                                      (fn-record-stamp (car *rft-cs*))))
               *rft-keyring*))
       (not (equal (fn-rfz-index-of-rows *rft-cs*) (fn-stx-index-empty)))
       (equal (fn-stx-index-lookup (fn-rfz-index-of-rows *rft-cs*) (fn-stmt-id *rft-statement*))
              *rft-statement*)))

; The context invariant removed, for the verdicts: a row whose context
; carries a verdict the bytes do not decide (its delta nil, as the bytes'
; is).  The verdict fold differs from the wire view's.
(defconst *rft-c-bad*
  (list (fn-held-with-context (car *rft-c*) (fn-hc-make :verified nil 0))
        (car (cdr *rft-c*))))
(defthm rft-w-replay-verdicts-without-contexts
  (and (fn-rfz-handles-inp *rft-c-bad* *rft-a*)
       (not (fn-rfz-contexts-okp *rft-c-bad* nil 0 *rft-a*))
       (not (equal (fn-rfz-verdicts-of-rows *rft-c-bad*)
                   (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows *rft-c-bad* *rft-a*) nil 0))))
  :rule-classes nil)
(must-fail
 (defthm rft-r-replay-verdicts-without-contexts
   (equal (fn-rfz-verdicts-of-rows *rft-c-bad*)
          (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows *rft-c-bad* *rft-a*) nil 0))
   :rule-classes nil))

; The context invariant removed, for the index: the signed row's context
; with its delta emptied; the store's fold over the bytes still binds the
; statement, the retained fold does not.  The store's side verifies the
; signature through the codec's attachment, so this witness is an
; evaluation (assert-event), not a theorem and not a must-fail: a defthm
; over it would fail for want of the attachment, not for the reason.
(defconst *rft-cs-bad*
  (list (fn-held-with-context (car *rft-cs*) (fn-hc-make :verified nil 7))))
(assert-event
  (and (not (equal (fn-held-context (car *rft-cs-bad*))
                   (fn-held-context-of (nth 0 *rft-as*) *rft-keyring* 7)))
       (equal (fn-rfz-index-of-rows *rft-cs-bad*) (fn-stx-index-empty))
       (not (equal (fn-rfz-index-of-rows *rft-cs-bad*)
                   (fn-stx-index-of-store
                    (list (fn-make-article (fn-record-msgid (car *rft-cs-bad*)) (nth 0 *rft-as*)
                                           (fn-record-groups (car *rft-cs-bad*))
                                           (fn-held-numbers (car *rft-cs-bad*)) t
                                           (fn-record-stamp (car *rft-cs-bad*))))
                    *rft-keyring*)))))

; fn-rfz-handles-inp is NOT a hypothesis of the two replay theorems (the
; weakened theorems are the ones proved): the record.  A row whose handle
; is past the count reads nil by handle on both sides, and the invariant
; over that nil still equates the folds.
(defconst *rft-c-far*
  (list (fn-cat-assign (rft-held (fn-held-wire *rft-w0* nil) 9 nil 0) nil)))
(defthm rft-w-replay-handles-inp-redundant
  (and (not (fn-rfz-handles-inp *rft-c-far* *rft-a*))
       (fn-rfz-contexts-okp *rft-c-far* nil 0 *rft-a*)
       (equal (fn-rfz-index-of-rows *rft-c-far*)
              (fn-stx-index-of-store (fn-rfz-articles-of-rows *rft-c-far* *rft-a*) nil))
       (equal (fn-rfz-verdicts-of-rows *rft-c-far*)
              (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows *rft-c-far* *rft-a*) nil 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))

; The load establishes the invariant: the positive witness is
; rft-w-loaded-is-the-fold above (from the empty creators), and from a
; catalog already in the invariant:
(defthm rft-w-load-onto-loaded
  (and (fn-cat-p *rft-c*) (fn-rfz-handles-inp *rft-c* *rft-a*)
       (fn-rfz-contexts-okp *rft-c* nil 0 *rft-a*) (natp 0)
       (mv-let (a c)
         (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c*)
         (and (fn-cat-p c) (fn-rfz-handles-inp c a) (fn-rfz-contexts-okp c nil 0 a)
              (equal (fn-cat-count c) 3) (equal (fn-arena-count a) 3))))
  :rule-classes nil)

; Without the invariant on the initial catalog: the bad row stays bad.
(defthm rft-w-load-without-contexts
  (and (fn-cat-p *rft-c-bad*) (fn-rfz-handles-inp *rft-c-bad* *rft-a*)
       (not (fn-rfz-contexts-okp *rft-c-bad* nil 0 *rft-a*)) (natp 0)
       (mv-let (a c)
         (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-bad*)
         (not (fn-rfz-contexts-okp c nil 0 a))))
  :rule-classes nil)
(must-fail
 (defthm rft-r-load-without-contexts
   (mv-let (a c)
     (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-bad*)
     (fn-rfz-contexts-okp c nil 0 a))
   :rule-classes nil))

; Without every handle in the arena: a row at handle 9 stays out of it
; (the load seals one payload: the count becomes 3).
(defthm rft-w-load-without-handles
  (and (fn-cat-p *rft-c-far*) (not (fn-rfz-handles-inp *rft-c-far* *rft-a*))
       (fn-rfz-contexts-okp *rft-c-far* nil 0 *rft-a*) (natp 0)
       (mv-let (a c)
         (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-far*)
         (not (fn-rfz-handles-inp c a))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))
(must-fail
 (defthm rft-r-load-without-handles
   (mv-let (a c)
     (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-far*)
     (fn-rfz-handles-inp c a))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                      fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                      fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                      fn-held-wire-of)))))

; Without fn-cat-p on the initial catalog: a tuple with a Message-ID that
; is not one (5), handle 0 and the right context is not a row, and stays
; in the loaded catalog.
(defconst *rft-c-notrow*
  (list (rft-held (fn-record-make 0 1 1 5 *rft-p0* '("fn.test") "o" "s" "e" 1 5) 0 nil 0)))
(defthm rft-w-load-without-cat-p
  (and (not (fn-cat-p *rft-c-notrow*)) (fn-rfz-handles-inp *rft-c-notrow* *rft-a*)
       (fn-rfz-contexts-okp *rft-c-notrow* nil 0 *rft-a*) (natp 0)
       (mv-let (a c)
         (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-notrow*)
         (and (not (fn-cat-p c)) a)))
  :rule-classes nil)
(must-fail
 (defthm rft-r-load-without-cat-p
   (mv-let (a c)
     (fn-cat-load (list *rft-w0*) nil 0 *rft-a* *rft-c-notrow*)
     (and (fn-cat-p c) a))
   :rule-classes nil))

; Without a natural generation: the interned row's context is not a
; context, so the loaded catalog is not a catalog.
(defthm rft-w-load-without-natp-generation
  (and (fn-cat-p nil) (fn-rfz-handles-inp nil nil) (fn-rfz-contexts-okp nil nil -1 nil)
       (not (natp -1))
       (mv-let (a c)
         (fn-cat-load (list *rft-w0*) nil -1 nil nil)
         (and (not (fn-cat-p c)) a)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rfz-contexts-okp))))
(must-fail
 (defthm rft-r-load-without-natp-generation
   (mv-let (a c)
     (fn-cat-load (list *rft-w0*) nil -1 nil nil)
     (and (fn-cat-p c) a))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; 3. Payload identity across reclamation.

; A pinned row list survives the reclaim's seal and a later one.
(defthm rft-w-pinned-rows
  (and (fn-rfz-handles-inp *rft-c* *rft-a*)
       (equal (fn-rfz-wire-rows *rft-c* (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
              (fn-rfz-wire-rows *rft-c* *rft-a*))
       (equal (fn-rfz-wire-rows *rft-c* *rft-a*) (list *rft-w0* *rft-w2*)))
  :rule-classes nil)

; Without every handle in the arena: a row at the count reads nil before
; the seal and the tombstone after it.
(defconst *rft-c-edge* (list (fn-cat-assign (rft-held (fn-held-wire *rft-w0* nil) 2 nil 0) nil)))
(defthm rft-w-pinned-rows-without-handles
  (and (not (fn-rfz-handles-inp *rft-c-edge* *rft-a*))
       (equal (fn-record-payload (car (fn-rfz-wire-rows *rft-c-edge* *rft-a*))) nil)
       (equal (fn-record-payload
               (car (fn-rfz-wire-rows *rft-c-edge* (fn-arn-seal-many (list *rft-tomb*) *rft-a*))))
              *rft-tomb*)
       (not (equal (fn-rfz-wire-rows *rft-c-edge* (fn-arn-seal-many (list *rft-tomb*) *rft-a*))
                   (fn-rfz-wire-rows *rft-c-edge* *rft-a*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))
(must-fail
 (defthm rft-r-pinned-rows-without-handles
   (equal (fn-rfz-wire-rows *rft-c-edge* (fn-arn-seal-many (list *rft-tomb*) *rft-a*))
          (fn-rfz-wire-rows *rft-c-edge* *rft-a*))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                      fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                      fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                      fn-held-wire-of)))))

; The reclaim of row 0: the old row reads the original after the
; tombstone's seal; the row pointed at the tombstone reads the tombstone.
(defthm rft-w-reclaim
  (let ((r (car *rft-c*)))
    (and (natp (fn-record-payload r)) (< (fn-record-payload r) (fn-arena-count *rft-a*))
         (equal (fn-held-wire-of r (fn-arena-seal-list *rft-tomb* *rft-a*))
                (fn-held-wire-of r *rft-a*))
         (equal (fn-held-wire-of r *rft-a*) *rft-w0*)
         (equal (fn-held-wire-of (fn-rfz-row-with-handle r (fn-arena-count *rft-a*))
                                 (fn-arena-seal-list *rft-tomb* *rft-a*))
                (fn-held-wire r *rft-tomb*))
         (equal (fn-held-wire r *rft-tomb*)
                (fn-record-make 0 1 1 "<a@x>" *rft-tomb* '("fn.test") "o" "s" "e" 1 5))))
  :rule-classes nil)

; Without the handle below the count (the old-view theorem): a row at the
; count reads the tombstone after the seal, so the two reads differ.
(defthm rft-w-reclaim-without-handle-below
  (let ((r (car *rft-c-edge*)))
    (and (natp (fn-record-payload r)) (not (< (fn-record-payload r) (fn-arena-count *rft-a*)))
         (not (equal (fn-held-wire-of r (fn-arena-seal-list *rft-tomb* *rft-a*))
                     (fn-held-wire-of r *rft-a*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))
(must-fail
 (defthm rft-r-reclaim-without-handle-below
   (let ((r (car *rft-c-edge*)))
     (equal (fn-held-wire-of r (fn-arena-seal-list *rft-tomb* *rft-a*))
            (fn-held-wire-of r *rft-a*)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                      fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                      fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                      fn-held-wire-of)))))

; Without a natural handle (the old-view theorem): nth of a negative is
; the car, so a negative handle reads handle 0's bytes before and after;
; the conclusion happens to hold there, so the witness is the guard's:
; a handle that is not a natural is not a handle (fn-held-p).  Recorded,
; not a must-fail: the weakened theorem (natp dropped) was NOT proved and
; the hypothesis stays, because fn-arena-payload's guard needs it.
(defthm rft-w-reclaim-negative-handle
  (let ((r (fn-rfz-row-with-handle (car *rft-c*) -1)))
    (and (not (natp (fn-record-payload r)))
         (not (fn-held-p r))
         (equal (fn-held-wire-of r *rft-a*) *rft-w0*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))

; The versioned mapping: a reclaim recorded at version 2; readers at
; versions 2 and 3.
(defthm rft-w-resolve
  (and (<= 2 2) (equal (fn-rfz-resolve 0 (list (cons 2 2)) 2) 0)
       (< 2 3) (equal (fn-rfz-resolve 0 (list (cons 2 2)) 3) 2)
       (equal (fn-arena-payload (fn-rfz-resolve 0 (list (cons 2 2)) 2)
                                (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
              *rft-p0*)
       (equal (fn-arena-payload (fn-rfz-resolve 0 (list (cons 2 2)) 3)
                                (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
              *rft-tomb*))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))

(defthm rft-w-resolve-before-without-order
  (and (not (<= 3 2)) (not (equal (fn-rfz-resolve 0 (list (cons 2 2)) 3) 0)))
  :rule-classes nil)
(must-fail
 (defthm rft-r-resolve-before-without-order
   (equal (fn-rfz-resolve 0 (list (cons 2 2)) 3) 0)
   :rule-classes nil))

(defthm rft-w-resolve-after-without-order
  (and (not (< 2 2)) (not (equal (fn-rfz-resolve 0 (list (cons 2 2)) 2) 2)))
  :rule-classes nil)
(must-fail
 (defthm rft-r-resolve-after-without-order
   (equal (fn-rfz-resolve 0 (list (cons 2 2)) 2) 2)
   :rule-classes nil))

; The resolved payload survives later seals; without the handle below the
; count it does not.
(defthm rft-w-resolved-survives
  (and (natp 0) (< 0 (fn-arena-count *rft-a*))
       (equal (fn-arena-payload 0 (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
              (fn-arena-payload 0 *rft-a*))
       (natp 2) (not (< 2 (fn-arena-count *rft-a*)))
       (not (equal (fn-arena-payload 2 (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
                   (fn-arena-payload 2 *rft-a*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                     fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                     fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                     fn-held-wire-of))))
(must-fail
 (defthm rft-r-resolved-survives-without-handle-below
   (equal (fn-arena-payload 2 (fn-arn-seal-many (list *rft-tomb* '(9)) *rft-a*))
          (fn-arena-payload 2 *rft-a*))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-arena-payload-is-nth fn-arena-count-is-len
                                      fn-arn-seal-many-is-append fn-arena-seal-list-is-append
                                      fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                                      fn-held-wire-of)))))

; -----------------------------------------------------------------------------
; The exec path: the load on live stobjs (the generic's own list
; foundation here; the byte array in books/payload-arena-attach.lisp), the
; rows read back through the catalog's exports, the folds and the reads.

(defun rft-rows (i n fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (>= i n) nil (cons (fn-cat-at i fn-cat) (rft-rows (+ i 1) n fn-cat))))

(defun rft-run (fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (fn-cat-load *rft-h* nil 0 fn-arena fn-cat)
      (let* ((rows (rft-rows 0 (fn-cat-count fn-cat) fn-cat))
             (before (list (fn-rfz-handles-inp rows fn-arena)
                           (fn-rfz-contexts-okp rows nil 0 fn-arena)
                           (equal (fn-rfz-index-of-rows rows)
                                  (fn-stx-index-of-store (fn-rfz-articles-of-rows rows fn-arena) nil))
                           (equal (fn-rfz-verdicts-of-rows rows)
                                  (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows rows fn-arena) nil 0))
                           (fn-rfz-wire-rows rows fn-arena)
                           (fn-arena-payload-len 0 fn-arena)))
             ; the reclaim of row 0: the tombstone sealed, then another commit
             (fn-arena (fn-arena-seal-list *rft-tomb* fn-arena))
             (fn-arena (fn-arena-seal-list '(9) fn-arena))
             (after (list (equal (fn-rfz-wire-rows rows fn-arena) (list *rft-w0* *rft-w2*))
                          (fn-arena-payload (fn-rfz-resolve 0 (list (cons 2 2)) 2) fn-arena)
                          (fn-arena-payload (fn-rfz-resolve 0 (list (cons 2 2)) 3) fn-arena)
                          (fn-arena-count fn-arena))))
        (mv (list before after) fn-arena fn-cat)))))

(defun rft-exec ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (rft-run fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

(assert-event
 (equal (rft-exec)
        (list (list t t t t (list *rft-w0* *rft-w2*) (len *rft-p0*))
              (list t *rft-p0* *rft-tomb* 4))))
