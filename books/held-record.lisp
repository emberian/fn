; fn: the held record's SHAPE (records-flip, 2026-09-27; D33; PKT-635).
;
; Two views of one record.  The WIRE record is `fn-record-p'
; (books/records-shape.lisp): an octet-list payload, the codec's domain.
; The HELD record is what the store's history, the acceptance state and the
; catalog retain: the same eleven positions, read by the SAME positional
; accessors (`fn-record-sequence' .. `fn-record-stamp' are `mbe' selectors
; with guard t, so they read either view), with the payload position holding
; a natural, a HANDLE into the arena (books/payload-arena.lisp), and four
; positions after it:
;
;   11 facts     (octets body-start body-lines control)  decided ONCE from the bytes at intern
;   12 context   (verdict delta generation)        decided at intern under the keyring in force
;   13 numbers   ((group . n) ...)                 assigned by the catalog's commit; nil before
;   14 withdrawn nil | (at . by)                   the version at which a cancel withdrew it
;
; Its recognizer is `fn-held-p', never `fn-record-p': the predicate that
; means "contains octets" is not reused to mean "contains an integer".
;
; This book is the shape alone, so that books/store-events.lisp can name
; `fn-held-p' as the history's article disjunct without the arena, the lace
; parser or the served splitter.  What is decided FROM bytes (the facts of a
; payload, the context under a keyring, alpha through the arena, the intern)
; is books/catalog-record.lisp, which includes this one.
;
; The retained accepted-statement event is `fn-hstxa-p': the wire composite
; (`fn-stxa-p', books/stx-accept-records.lisp; kept whole for the identity
; fold, which verifies its statement) beside its article INTERNED as a held
; record.  A bare `fn-stxa-p' is never a retained event: replaying one would
; hand the composite's octet list to `fn-accept-prepare', which after the
; flip refuses everything but a handle.
(in-package "ACL2")
(include-book "records-shape")
(include-book "payload-kinds")
(include-book "defrecord")
(include-book "stx-accept-records")

; -----------------------------------------------------------------------------
; The byte facts' shape.
(defun fn-hf-startp (x)
  (declare (xargs :guard t))
  (or (null x) (natp x)))

; CONTROL is what the control vocabulary reads from the bytes
; (books/control-authority.lisp fn-ctl-control-of): (TARGET KEYS LOCKS), the
; article's one withdrawal target, its RFC 8315 Cancel-Key entries and its
; Cancel-Lock entries.  Decided once at intern like the others, so the owner's
; refresh, which holds no arena, reads a cancel's target and a target's locks
; from the rows (flip-L8-2, 2026-09-27).
(fn-defrecord fn-hf
  :constructor (fn-hf-make octets body-start body-lines control)
  :fields ((fn-hf-octets natp)
           (fn-hf-body-start fn-hf-startp)
           (fn-hf-body-lines natp)
           (fn-hf-control true-listp))
  :recognizer fn-hf-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

;
; NOV is the overview COLUMN (lane served-columns, 2026-09-27): what the
; served OVER/XOVER, HDR/XHDR and XPAT read of an article instead of its
; octets, decided at the same intern from the same parse
; (books/catalog-record.lisp fn-hnov-of; books/served-columns.lisp says the
; served replies built from it are the replies built from the bytes).  It
; is the FOURTH element of the control position, not a field of its own:
; the facts' shape is persisted in a state checkpoint's event table, and a
; fifth field made an older checkpoint unreadable, which a store whose log
; segments below it were dropped cannot fall back from (measured
; 2026-09-28: "open refused reason=checkpoint-damaged").  CONTROL is a true
; list whose first three elements the control vocabulary reads
; (fn-ctl-at 0..2), so both images read both shapes.  Absent (a
; three-element control, an older checkpoint's row, fn-held-plain's nil):
; the column is not decided and a served reader reads the bytes, as before.
(defun fn-hnov-flagp (x)
  (declare (xargs :guard t))
  (booleanp x))

(fn-defrecord fn-hnov
  :constructor (fn-hnov-make tomb ok subject from date msgid references)
  :fields ((fn-hnov-tomb fn-hnov-flagp)
           (fn-hnov-ok fn-hnov-flagp)
           (fn-hnov-subject stringp)
           (fn-hnov-from stringp)
           (fn-hnov-date stringp)
           (fn-hnov-msgid stringp)
           (fn-hnov-references stringp))
  :recognizer fn-hnov-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(defun fn-hf-nov (facts)
  (declare (xargs :guard t))
  (fn-cbor-ag-car (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-cbor-ag-cdr (fn-hf-control facts))))))

; -----------------------------------------------------------------------------
; The context's shape: what the finish decides from the bytes, decided at
; intern under the keyring and generation in force.

(defun fn-hc-anyp (x)
  (declare (xargs :guard t) (ignore x))
  t)

; The verdict is what fn-stx-verdict-of-octets (books/stx-lace.lisp) decides:
; a token of *fn-stx-verdicts* at a natural generation, which is what the
; store's verdict list holds (fn-sn-verdict-listp, books/store-node.lisp).
; The delta is a lace (books/lace.lisp; what fn-stx-delta returns), so the
; index fold over rows needs no gate on it.
(defun fn-hc-verdictp (v)
  (declare (xargs :guard t))
  (and (member-equal (fn-stx-verdict-token v) *fn-stx-verdicts*)
       (natp (fn-stx-verdict-generation v))
       t))

(fn-defrecord fn-hc
  :constructor (fn-hc-make verdict delta generation)
  :fields ((fn-hc-verdict fn-hc-verdictp)
           (fn-hc-delta fn-lace-p)
           (fn-hc-generation natp))
  :recognizer fn-hc-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; -----------------------------------------------------------------------------
; The held record.

(defun fn-held-numbersp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x)) (posp (cdr (car x)))
         (fn-held-numbersp (cdr x)))))

(defun fn-held-withdrawnp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x) (natp (car x)) (natp (cdr x)))))

(fn-defrecord fn-held
  :constructor (fn-held-make sequence txid generation msgid payload groups
                             obligation-id content-subject release-evidence
                             charge stamp facts context numbers withdrawn)
  :fields ((fn-held-sequence fn-record-uint64p)
           (fn-held-txid fn-record-uint64p)
           (fn-held-generation fn-record-uint64p)
           (fn-held-msgid fn-record-msgidp)
           (fn-held-payload fn-payload-handle-p)
           (fn-held-groups fn-record-groups-validp)
           (fn-held-obligation-id fn-record-metadata-bytes-p)
           (fn-held-content-subject fn-record-metadata-bytes-p)
           (fn-held-release-evidence fn-record-metadata-bytes-p)
           (fn-held-charge fn-record-uint64p)
           (fn-held-stamp fn-record-stampp)
           (fn-held-facts fn-hf-p)
           (fn-held-context fn-hc-p)
           (fn-held-numbers fn-held-numbersp)
           (fn-held-withdrawn fn-held-withdrawnp))
  :recognizer fn-held-p
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; The eleven wire positions are read by the wire accessors: one vocabulary
; (a held accessor rewrites to the wire one; the wire's rules then apply).
(defthm fn-held-accessors-are-the-wire-accessors
  (and (equal (fn-held-sequence h) (fn-record-sequence h))
       (equal (fn-held-txid h) (fn-record-txid h))
       (equal (fn-held-generation h) (fn-record-generation h))
       (equal (fn-held-msgid h) (fn-record-msgid h))
       (equal (fn-held-payload h) (fn-record-payload h))
       (equal (fn-held-groups h) (fn-record-groups h))
       (equal (fn-held-obligation-id h) (fn-record-obligation-id h))
       (equal (fn-held-content-subject h) (fn-record-content-subject h))
       (equal (fn-held-release-evidence h) (fn-record-release-evidence h))
       (equal (fn-held-charge h) (fn-record-charge h))
       (equal (fn-held-stamp h) (fn-record-stamp h)))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))

; The recognizer executes (its field recognizers are the wire record's,
; all guard-verified); a list of held records; what a row of one satisfies.
(verify-guards fn-held-p)

(defun fn-held-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (fn-held-p (car xs)) (fn-held-listp (cdr xs)))))

(defthm fn-held-listp-forward-true-listp
  (implies (fn-held-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-held-p-of-nth-of-held-listp
  (implies (and (fn-held-listp xs) (natp i) (< i (len xs)))
           (fn-held-p (nth i xs)))
  :hints (("Goal" :in-theory (disable fn-held-p))))

(defthm fn-held-listp-of-update-nth
  (implies (and (fn-held-listp xs) (fn-held-p h) (natp i) (< i (len xs)))
           (fn-held-listp (update-nth i h xs)))
  :hints (("Goal" :in-theory (disable fn-held-p))))

(defthm fn-held-listp-of-append-one
  (implies (and (fn-held-listp xs) (fn-held-p h))
           (fn-held-listp (append xs (list h))))
  :hints (("Goal" :in-theory (disable fn-held-p))))

; A held record's head is a natural (its sequence), which tells it from every
; symbol-headed event by shape.
(defthm fn-held-p-forward-natural-head
  (implies (fn-held-p x) (natp (car x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory '(fn-held-p fn-held-shapep fn-record-uint64p
                               fn-held-sequence fn-record-sequence
                               fn-cbor-ag-car natp))))

; The context's fields, without opening the recognizer.
(defthm fn-hc-p-fields
  (implies (fn-hc-p c)
           (and (member-equal (fn-stx-verdict-token (fn-hc-verdict c)) *fn-stx-verdicts*)
                (natp (fn-stx-verdict-generation (fn-hc-verdict c)))
                (fn-lace-p (fn-hc-delta c))
                (natp (fn-hc-generation c))))
  :hints (("Goal" :in-theory (enable fn-hc-p fn-hc-verdictp))))

(defthm fn-held-p-fields
  (implies (fn-held-p h)
           (and (natp (fn-record-payload h))
                (fn-hf-p (fn-held-facts h))
                (fn-hc-p (fn-held-context h))
                (fn-held-numbersp (fn-held-numbers h))
                (fn-held-withdrawnp (fn-held-withdrawn h))))
  :hints (("Goal" :in-theory (enable fn-held-p))))

; -----------------------------------------------------------------------------
; ALPHA: the wire record a held record stands for, given its bytes.

(defun fn-held-wire (h payload)
  (declare (xargs :guard t))
  (fn-record-make (fn-record-sequence h) (fn-record-txid h)
                  (fn-record-generation h) (fn-record-msgid h) payload
                  (fn-record-groups h) (fn-record-obligation-id h)
                  (fn-record-content-subject h) (fn-record-release-evidence h)
                  (fn-record-charge h) (fn-record-stamp h)))

; On a wire record, replacing the payload by its own is the identity.
(defthm fn-held-wire-of-wire-record
  (implies (fn-record-shapep w)
           (equal (fn-held-wire w (fn-record-payload w)) w))
  :hints (("Goal" :in-theory (enable fn-held-wire))))

; The wire accessors of a held record built by the constructor.
(defthm fn-record-accessors-of-held-make
  (let ((h (fn-held-make sequence txid generation msgid payload groups
                         obligation-id content-subject release-evidence
                         charge stamp facts context numbers withdrawn)))
    (and (equal (fn-record-sequence h) sequence)
         (equal (fn-record-txid h) txid)
         (equal (fn-record-generation h) generation)
         (equal (fn-record-msgid h) msgid)
         (equal (fn-record-payload h) payload)
         (equal (fn-record-groups h) groups)
         (equal (fn-record-obligation-id h) obligation-id)
         (equal (fn-record-content-subject h) content-subject)
         (equal (fn-record-release-evidence h) release-evidence)
         (equal (fn-record-charge h) charge)
         (equal (fn-record-stamp h) stamp)
         (equal (fn-held-facts h) facts)
         (equal (fn-held-context h) context)
         (equal (fn-held-numbers h) numbers)
         (equal (fn-held-withdrawn h) withdrawn)))
  :hints (("Goal" :in-theory (enable fn-record-internals fn-held-internals))))


; -----------------------------------------------------------------------------
; A row with one position replaced.

(defun fn-held-with-numbers (h numbers)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                numbers (fn-held-withdrawn h)))

(defun fn-held-with-withdrawn (h withdrawn)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                (fn-held-numbers h) withdrawn))

(defun fn-held-with-context (h context)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) context
                (fn-held-numbers h) (fn-held-withdrawn h)))

; The held row of a wire record with HANDLE and no bytes read: the facts of
; an unread payload (its octet count, no split, no lines, no control) and the context
; that no statement was seen (verdict :absent at generation 0, no delta).
; For the test books and for an entry that has a handle but decides nothing
; from the bytes; the intern (books/catalog-record.lisp) reads them.
(defun fn-held-plain (w handle)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w)
                (fn-record-obligation-id w) (fn-record-content-subject w)
                (fn-record-release-evidence w) (fn-record-charge w)
                (fn-record-stamp w)
                (fn-hf-make (len (fn-record-payload w)) nil 0 nil)
                (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0)
                nil nil))

(defthm fn-held-p-of-held-plain
  (implies (and (fn-record-p w) (natp handle))
           (fn-held-p (fn-held-plain w handle)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-record-p fn-record-internals fn-held-internals
                                     fn-hf-p fn-hc-p fn-hf-startp fn-hc-verdictp
                                     fn-held-numbersp fn-held-withdrawnp
                                     fn-stx-make-verdict fn-stx-verdict-token
                                     fn-stx-verdict-generation))))

; A recontexted row is a held record with the same wire positions, facts,
; numbers and withdrawal, and the new context.
(defthm fn-held-with-context-fields
  (let ((r (fn-held-with-context h ctx)))
    (and (equal (fn-record-sequence r) (fn-record-sequence h))
         (equal (fn-record-txid r) (fn-record-txid h))
         (equal (fn-record-generation r) (fn-record-generation h))
         (equal (fn-record-msgid r) (fn-record-msgid h))
         (equal (fn-record-payload r) (fn-record-payload h))
         (equal (fn-record-groups r) (fn-record-groups h))
         (equal (fn-record-obligation-id r) (fn-record-obligation-id h))
         (equal (fn-record-content-subject r) (fn-record-content-subject h))
         (equal (fn-record-release-evidence r) (fn-record-release-evidence h))
         (equal (fn-record-charge r) (fn-record-charge h))
         (equal (fn-record-stamp r) (fn-record-stamp h))
         (equal (fn-held-facts r) (fn-held-facts h))
         (equal (fn-held-context r) ctx)
         (equal (fn-held-numbers r) (fn-held-numbers h))
         (equal (fn-held-withdrawn r) (fn-held-withdrawn h))))
  :hints (("Goal" :in-theory (enable fn-held-with-context))))

(defthm fn-held-p-of-with-context
  (implies (and (fn-held-p h) (fn-hc-p ctx))
           (fn-held-p (fn-held-with-context h ctx)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-context
                                     fn-record-internals fn-held-internals))))

; -----------------------------------------------------------------------------
; The retained accepted-statement event.

(defun fn-hstxa-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)
       (eq (car x) :hstxa)
       (fn-stxa-p (car (cdr x)))
       (fn-held-p (car (cdr (cdr x))))))

(defun fn-hstxa-make (stxa held)
  (declare (xargs :guard t))
  (list :hstxa stxa held))

(defun fn-hstxa-stxa (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (cdr x)) (car (cdr x)) nil) nil))

(defun fn-hstxa-held (x)
  (declare (xargs :guard t))
  (if (consp x) (if (consp (cdr x)) (if (consp (cdr (cdr x))) (car (cdr (cdr x))) nil) nil) nil))

(defthm fn-hstxa-accessors-of-make
  (and (equal (fn-hstxa-stxa (fn-hstxa-make stxa held)) stxa)
       (equal (fn-hstxa-held (fn-hstxa-make stxa held)) held)))

(defthm fn-hstxa-p-of-make
  (equal (fn-hstxa-p (fn-hstxa-make stxa held))
         (and (fn-stxa-p stxa) (fn-held-p held))))

(defthm fn-hstxa-p-fields
  (implies (fn-hstxa-p x)
           (and (fn-stxa-p (fn-hstxa-stxa x))
                (fn-held-p (fn-hstxa-held x))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-hstxa-p-forward-shape
  (implies (fn-hstxa-p x)
           (and (consp x) (true-listp x) (equal (len x) 3) (eq (car x) :hstxa)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held))

; -----------------------------------------------------------------------------
; Proof vocabulary: the held record's recognizer and shape, opened by a book
; that reasons about a row's fields, the way `fn-record-shape-vocabulary'
; (books/records-shape.lisp) is for the wire record.
; Withdrawn on include, like the wire record's recognizer (books/records-shape
; .lisp): opened, fn-held-p unfolds fifteen field recognizers, two of them
; recursive (fn-lace-p, fn-held-numbersp), and a goal that merely dispatches
; on the event kind then carries them all (books/replay.lisp's first theorem
; ran past 300 s with it open, run-20260927T035647Z-7bc9).  The forward
; shape facts (consp, true-listp) stay: fn-held-p-forward-shape and the
; field facts fn-held-p-fields.  A book that reasons about a row's fields
; enables fn-held-vocabulary locally.
(in-theory (disable (:d fn-held-p) (:d fn-held-shapep) (:d fn-held-numbersp)
                    (:d fn-held-withdrawnp) (:d fn-hf-p) (:d fn-hf-shapep)
                    (:d fn-hf-startp) (:d fn-hc-p) (:d fn-hc-shapep) (:d fn-hc-anyp) (:d fn-hc-verdictp)))

(deftheory fn-held-vocabulary
  '((:d fn-held-p) (:d fn-held-shapep) (:d fn-held-numbersp) (:d fn-held-withdrawnp)
    (:d fn-hf-p) (:d fn-hf-shapep) (:d fn-hf-startp)
    (:d fn-hc-p) (:d fn-hc-shapep) (:d fn-hc-anyp) (:d fn-hc-verdictp)
    (:d fn-hstxa-p) (:d fn-hstxa-make) (:d fn-hstxa-stxa) (:d fn-hstxa-held)))
