; Experimental receiver-side BP request context and durable receipt decision.
; The request codec is fn-bpa; Store article admission remains fn-bpi.  This is
; deliberately separate from fn-bp's sender-side receipt-evidence workflow.
(in-package "ACL2")
(include-book "bp-adu")
(include-book "bp-ingress")
; A context holds its request by REFERENCE (PKT-646, PRF-249).
(include-book "bp-request-ref")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; Local receiver configuration: (destination-eid policy-id issuer-eid).
(defun fn-bpr-config-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-bpr-config-destination (x) (fn-bpa-nth 0 x))
(defun fn-bpr-config-policy-id (x) (fn-bpa-nth 1 x))
(defun fn-bpr-config-issuer (x) (fn-bpa-nth 2 x))
(defun fn-bpr-make-config (destination policy issuer)
  (list destination policy issuer))

(defthm fn-bpr-config-shapep-of-fn-bpr-make-config
  (fn-bpr-config-shapep (fn-bpr-make-config destination policy issuer)))
(defthm fn-bpr-config-destination-of-fn-bpr-make-config
  (equal (fn-bpr-config-destination (fn-bpr-make-config destination policy issuer)) destination))
(defthm fn-bpr-config-policy-id-of-fn-bpr-make-config
  (equal (fn-bpr-config-policy-id (fn-bpr-make-config destination policy issuer)) policy))
(defthm fn-bpr-config-issuer-of-fn-bpr-make-config
  (equal (fn-bpr-config-issuer (fn-bpr-make-config destination policy issuer)) issuer))
(defthm fn-bpr-config-shapep-forward-shape
  (implies (fn-bpr-config-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpr-config-accessors-forward-consp
  (and (implies (fn-bpr-config-destination x) (consp x))
       (implies (fn-bpr-config-policy-id x) (consp x))
       (implies (fn-bpr-config-issuer x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpr-config-destination x) (consp x))
                                    :trigger-terms ((fn-bpr-config-destination x)))
                 (:forward-chaining :corollary (implies (fn-bpr-config-policy-id x) (consp x))
                                    :trigger-terms ((fn-bpr-config-policy-id x)))
                 (:forward-chaining :corollary (implies (fn-bpr-config-issuer x) (consp x))
                                    :trigger-terms ((fn-bpr-config-issuer x)))))
(in-theory (disable (:d fn-bpr-config-shapep) (:d fn-bpr-config-destination) (:d fn-bpr-config-policy-id) (:d fn-bpr-config-issuer)
                    (:d fn-bpr-make-config)))
(defun fn-bpr-configp (x)
  (and (fn-bpr-config-shapep x)
       (fn-bpa-metadatap (fn-bpr-config-destination x))
       (fn-bpa-metadatap (fn-bpr-config-policy-id x))
       (fn-bpa-metadatap (fn-bpr-config-issuer x))))

; Durable request context: (work-id msgid subject archive-id peer-eid policy-id
; origin-incarnation authorization-context terms-id exact-request).
(defthm fn-bpr-configp-forward-shape
  (implies (fn-bpr-configp x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpr-configp fn-bpr-config-shapep))))

(defun fn-bpr-context-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)))
(defun fn-bpr-context-work-id (x) (fn-bpa-nth 0 x))
(defun fn-bpr-context-msgid (x) (fn-bpa-nth 1 x))
(defun fn-bpr-context-subject (x) (fn-bpa-nth 2 x))
(defun fn-bpr-context-archive-id (x) (fn-bpa-nth 3 x))
(defun fn-bpr-context-peer-eid (x) (fn-bpa-nth 4 x))
(defun fn-bpr-context-policy-id (x) (fn-bpa-nth 5 x))
(defun fn-bpr-context-incarnation (x) (fn-bpa-nth 6 x))
(defun fn-bpr-context-auth-context (x) (fn-bpa-nth 7 x))
(defun fn-bpr-context-terms-id (x) (fn-bpa-nth 8 x))
(defun fn-bpr-context-request-ref (x) (fn-bpa-nth 9 x))
(defun fn-bpr-make-context (work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)
  (list work-id msgid subject archive-id peer policy incarnation auth-context
        terms request))

(defthm fn-bpr-context-shapep-of-fn-bpr-make-context
  (fn-bpr-context-shapep (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)))
(defthm fn-bpr-context-work-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-work-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) work-id))
(defthm fn-bpr-context-msgid-of-fn-bpr-make-context
  (equal (fn-bpr-context-msgid (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) msgid))
(defthm fn-bpr-context-subject-of-fn-bpr-make-context
  (equal (fn-bpr-context-subject (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) subject))
(defthm fn-bpr-context-archive-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-archive-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) archive-id))
(defthm fn-bpr-context-peer-eid-of-fn-bpr-make-context
  (equal (fn-bpr-context-peer-eid (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) peer))
(defthm fn-bpr-context-policy-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-policy-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) policy))
(defthm fn-bpr-context-incarnation-of-fn-bpr-make-context
  (equal (fn-bpr-context-incarnation (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) incarnation))
(defthm fn-bpr-context-auth-context-of-fn-bpr-make-context
  (equal (fn-bpr-context-auth-context (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) auth-context))
(defthm fn-bpr-context-terms-id-of-fn-bpr-make-context
  (equal (fn-bpr-context-terms-id (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) terms))
(defthm fn-bpr-context-request-of-fn-bpr-make-context
  (equal (fn-bpr-context-request-ref (fn-bpr-make-context work-id msgid subject archive-id peer policy
                                     incarnation auth-context terms request)) request))
(defthm fn-bpr-context-shapep-forward-shape
  (implies (fn-bpr-context-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpr-context-accessors-forward-consp
  (and (implies (fn-bpr-context-work-id x) (consp x))
       (implies (fn-bpr-context-msgid x) (consp x))
       (implies (fn-bpr-context-subject x) (consp x))
       (implies (fn-bpr-context-archive-id x) (consp x))
       (implies (fn-bpr-context-peer-eid x) (consp x))
       (implies (fn-bpr-context-policy-id x) (consp x))
       (implies (fn-bpr-context-incarnation x) (consp x))
       (implies (fn-bpr-context-auth-context x) (consp x))
       (implies (fn-bpr-context-terms-id x) (consp x))
       (implies (fn-bpr-context-request-ref x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpr-context-work-id x) (consp x))
                                    :trigger-terms ((fn-bpr-context-work-id x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-msgid x) (consp x))
                                    :trigger-terms ((fn-bpr-context-msgid x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-subject x) (consp x))
                                    :trigger-terms ((fn-bpr-context-subject x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-archive-id x) (consp x))
                                    :trigger-terms ((fn-bpr-context-archive-id x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-peer-eid x) (consp x))
                                    :trigger-terms ((fn-bpr-context-peer-eid x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-policy-id x) (consp x))
                                    :trigger-terms ((fn-bpr-context-policy-id x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-incarnation x) (consp x))
                                    :trigger-terms ((fn-bpr-context-incarnation x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-auth-context x) (consp x))
                                    :trigger-terms ((fn-bpr-context-auth-context x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-terms-id x) (consp x))
                                    :trigger-terms ((fn-bpr-context-terms-id x)))
                 (:forward-chaining :corollary (implies (fn-bpr-context-request-ref x) (consp x))
                                    :trigger-terms ((fn-bpr-context-request-ref x)))))
(in-theory (disable (:d fn-bpr-context-shapep) (:d fn-bpr-context-work-id) (:d fn-bpr-context-msgid) (:d fn-bpr-context-subject) (:d fn-bpr-context-archive-id) (:d fn-bpr-context-peer-eid) (:d fn-bpr-context-policy-id) (:d fn-bpr-context-incarnation) (:d fn-bpr-context-auth-context) (:d fn-bpr-context-terms-id) (:d fn-bpr-context-request-ref)
                    (:d fn-bpr-make-context)))

(defun fn-bpr-contextp (config x)
  (and (fn-bpr-context-shapep x)
       (fn-bpa-metadatap (fn-bpr-context-work-id x))
       (fn-bpa-metadatap (fn-bpr-context-msgid x))
       (fn-bpa-metadatap (fn-bpr-context-subject x))
       (fn-bpa-metadatap (fn-bpr-context-archive-id x))
       (fn-bpa-metadatap (fn-bpr-context-peer-eid x))
       (equal (fn-bpr-context-policy-id x) (fn-bpr-config-policy-id config))
       (fn-bpa-metadatap (fn-bpr-context-incarnation x))
       (fn-bpa-metadatap (fn-bpr-context-auth-context x))
       (fn-bpa-metadatap (fn-bpr-context-terms-id x))
       (fn-bpaj-request-refp (fn-bpr-context-request-ref x))))
(defthm fn-bpr-contextp-forward-shape
  (implies (fn-bpr-contextp config x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpr-contextp fn-bpr-context-shapep))))

(defun fn-bpr-context-listp (config xs)
  (if (consp xs)
      (and (fn-bpr-contextp config (car xs))
           (fn-bpr-context-listp config (cdr xs)))
    (null xs)))
(defun fn-bpr-find-context (work-id xs)
  (if (consp xs)
      (if (equal work-id (fn-bpr-context-work-id (car xs)))
          (car xs)
        (fn-bpr-find-context work-id (cdr xs)))
    nil))
(defun fn-bpr-find-context-msgid (msgid xs)
  (if (consp xs)
      (if (equal msgid (fn-bpr-context-msgid (car xs)))
          (car xs)
        (fn-bpr-find-context-msgid msgid (cdr xs)))
    nil))

; State: (config durable-contexts durable-receipts pending-receipt).
(defun fn-bpr-state-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)))
(defun fn-bpr-state-config (x) (fn-bpa-nth 0 x))
(defun fn-bpr-state-contexts (x) (fn-bpa-nth 1 x))
(defun fn-bpr-state-receipts (x) (fn-bpa-nth 2 x))
(defun fn-bpr-state-pending (x) (fn-bpa-nth 3 x))
(defun fn-bpr-make-state (config contexts receipts pending)
  (list config contexts receipts pending))

(defthm fn-bpr-state-shapep-of-fn-bpr-make-state
  (fn-bpr-state-shapep (fn-bpr-make-state config contexts receipts pending)))
(defthm fn-bpr-state-config-of-fn-bpr-make-state
  (equal (fn-bpr-state-config (fn-bpr-make-state config contexts receipts pending)) config))
(defthm fn-bpr-state-contexts-of-fn-bpr-make-state
  (equal (fn-bpr-state-contexts (fn-bpr-make-state config contexts receipts pending)) contexts))
(defthm fn-bpr-state-receipts-of-fn-bpr-make-state
  (equal (fn-bpr-state-receipts (fn-bpr-make-state config contexts receipts pending)) receipts))
(defthm fn-bpr-state-pending-of-fn-bpr-make-state
  (equal (fn-bpr-state-pending (fn-bpr-make-state config contexts receipts pending)) pending))
(defthm fn-bpr-state-shapep-forward-shape
  (implies (fn-bpr-state-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpr-state-accessors-forward-consp
  (and (implies (fn-bpr-state-config x) (consp x))
       (implies (fn-bpr-state-contexts x) (consp x))
       (implies (fn-bpr-state-receipts x) (consp x))
       (implies (fn-bpr-state-pending x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpr-state-config x) (consp x))
                                    :trigger-terms ((fn-bpr-state-config x)))
                 (:forward-chaining :corollary (implies (fn-bpr-state-contexts x) (consp x))
                                    :trigger-terms ((fn-bpr-state-contexts x)))
                 (:forward-chaining :corollary (implies (fn-bpr-state-receipts x) (consp x))
                                    :trigger-terms ((fn-bpr-state-receipts x)))
                 (:forward-chaining :corollary (implies (fn-bpr-state-pending x) (consp x))
                                    :trigger-terms ((fn-bpr-state-pending x)))))
(in-theory (disable (:d fn-bpr-state-shapep) (:d fn-bpr-state-config) (:d fn-bpr-state-contexts) (:d fn-bpr-state-receipts) (:d fn-bpr-state-pending)
                    (:d fn-bpr-make-state)))
(defun fn-bpr-receipt-entry-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-bpr-receipt-entry-context (x) (fn-bpa-nth 0 x))
(defun fn-bpr-receipt-entry-receipt (x) (fn-bpa-nth 1 x))
(defun fn-bpr-make-receipt-entry (context receipt) (list context receipt))

(defthm fn-bpr-receipt-entry-shapep-of-fn-bpr-make-receipt-entry
  (fn-bpr-receipt-entry-shapep (fn-bpr-make-receipt-entry context receipt)))
(defthm fn-bpr-receipt-entry-context-of-fn-bpr-make-receipt-entry
  (equal (fn-bpr-receipt-entry-context (fn-bpr-make-receipt-entry context receipt)) context))
(defthm fn-bpr-receipt-entry-receipt-of-fn-bpr-make-receipt-entry
  (equal (fn-bpr-receipt-entry-receipt (fn-bpr-make-receipt-entry context receipt)) receipt))
(defthm fn-bpr-receipt-entry-shapep-forward-shape
  (implies (fn-bpr-receipt-entry-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-bpr-receipt-entry-accessors-forward-consp
  (and (implies (fn-bpr-receipt-entry-context x) (consp x))
       (implies (fn-bpr-receipt-entry-receipt x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-bpr-receipt-entry-context x) (consp x))
                                    :trigger-terms ((fn-bpr-receipt-entry-context x)))
                 (:forward-chaining :corollary (implies (fn-bpr-receipt-entry-receipt x) (consp x))
                                    :trigger-terms ((fn-bpr-receipt-entry-receipt x)))))
(in-theory (disable (:d fn-bpr-receipt-entry-shapep) (:d fn-bpr-receipt-entry-context) (:d fn-bpr-receipt-entry-receipt)
                    (:d fn-bpr-make-receipt-entry)))
(defun fn-bpr-receipt-entryp (config x)
  (and (fn-bpr-receipt-entry-shapep x)
       (fn-bpr-contextp config (fn-bpr-receipt-entry-context x))
       (fn-bpa-receiptp (fn-bpr-receipt-entry-receipt x))))
(defthm fn-bpr-receipt-entryp-forward-shape
  (implies (fn-bpr-receipt-entryp config x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpr-receipt-entryp fn-bpr-receipt-entry-shapep))))

(defun fn-bpr-receipt-listp (config xs)
  (if (consp xs)
      (and (fn-bpr-receipt-entryp config (car xs))
           (fn-bpr-receipt-listp config (cdr xs)))
    (null xs)))
(defun fn-bpr-statep (x)
  (and (fn-bpr-state-shapep x)
       (fn-bpr-configp (fn-bpr-state-config x))
       (fn-bpr-context-listp (fn-bpr-state-config x) (fn-bpr-state-contexts x))
       (fn-bpr-receipt-listp (fn-bpr-state-config x) (fn-bpr-state-receipts x))
       (or (null (fn-bpr-state-pending x))
           (fn-bpr-receipt-entryp (fn-bpr-state-config x)
                                  (fn-bpr-state-pending x)))))
(defthm fn-bpr-statep-forward-shape
  (implies (fn-bpr-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bpr-statep fn-bpr-state-shapep))))

(defun fn-bpr-initial-state (config)
  (if (fn-bpr-configp config) (fn-bpr-make-state config nil nil nil) nil))

(defun fn-bpr-context-from-request (record request)
  (fn-bpr-make-context
   (fn-bpa-request-work-id request) (fn-record-msgid record)
   (fn-bpa-request-subject request) (fn-record-obligation-id record)
   (fn-bpa-request-source-eid request) (fn-bpa-request-policy-id request)
   (fn-bpa-request-incarnation request) (fn-bpa-request-auth-context request)
   (fn-bpa-request-terms-id request) (fn-bpaj-request-ref request)))

; PKT-646 (D27): a context holds its request's REFERENCE (HEAD LENGTH
; DIGEST, books/bp-request-ref.lisp), never the request ADU.  A context
; bound at replay from a durable record that holds only the reference
; reads its metadata from the reference's HEAD; for a request, the two
; constructions agree (`fn-bpr-context-from-ref-of-request-ref').
(defun fn-bpr-context-from-ref (record ref)
  (let ((m (fn-bpaj-ref-metadata ref)))
    (fn-bpr-make-context
     (fn-bpa-request-work-id m) (fn-record-msgid record)
     (fn-bpa-request-subject m) (fn-record-obligation-id record)
     (fn-bpa-request-source-eid m) (fn-bpa-request-policy-id m)
     (fn-bpa-request-incarnation m) (fn-bpa-request-auth-context m)
     (fn-bpa-request-terms-id m) ref)))

(defthm fn-bpr-context-from-ref-of-request-ref
  (implies (fn-bpa-requestp request)
           (equal (fn-bpr-context-from-ref record (fn-bpaj-request-ref request))
                  (fn-bpr-context-from-request record request)))
  :hints (("Goal" :use ((:instance fn-bpaj-ref-metadata-of-request-ref))
           :in-theory (disable fn-bpaj-ref-metadata-of-request-ref
                               fn-bpaj-request-ref fn-bpa-requestp))))

; The article record a Store event commits: a plain article record is its
; own; a signed acceptance composite (kind 4, `fn-stxa-p') commits the
; article record it carries, decoded as replay decodes it
; (`fn-replay-composite-record', books/replay.lisp, which installs that
; record in the node).  Every other event commits no article record and
; maps to itself, which is never `fn-record-p'.  Cost: a composite's
; article record octets are decoded when a walk reaches it.
;
; After the records flip the history retains a signed article's composite as
; the ROW `fn-hstxa-p' (books/held-record.lisp): its article is the held row
; the intern made of the article record above (books/store-intern.lisp
; fn-intern-event), so a signed article stays in the history's article
; records exactly as a plain one's held row does.  Their WIRE forms (alpha
; through the arena) are this fold over the wire history:
; books/history-fold-refinement.lisp fn-bpr-article-records-over-alpha.
(defun fn-bpr-event-article (event)
  (declare (xargs :guard t))
  (cond ((fn-hstxa-p event) (fn-hstxa-held event))
        ((fn-stxa-p event) (fn-replay-composite-record event))
        (t event)))

; The article records of a Store history, one per event, in order.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-bpr-article-records-loop (events acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp events)
      (fn-bpr-article-records-loop (cdr events)
                                   (cons (fn-bpr-event-article (car events)) acc))
    (revappend acc nil)))

(defun fn-bpr-article-records (events)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp events)
           (cons (fn-bpr-event-article (car events))
                 (fn-bpr-article-records (cdr events)))
         nil)
       :exec (fn-bpr-article-records-loop events nil)))

(local
 (defthm fn-bpr-article-records-loop-is-revappend
   (equal (fn-bpr-article-records-loop events acc)
          (revappend acc (fn-bpr-article-records events)))
   :hints (("Goal" :induct (fn-bpr-article-records-loop events acc)
                   :in-theory (union-theories '(fn-bpr-article-records-loop fn-bpr-article-records revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-bpr-article-records-loop)

(verify-guards fn-bpr-article-records
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-bpr-article-records)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-bpr-article-records-loop-is-revappend (acc nil))))))


;;; The retained row a WIRE record names (records-flip).  The receiver is
;;; handed the wire record -- the request journal persists it through the
;;; record codec (books/bp-receipt-records.lisp fn-bprr-decode-value), and a
;;; handle is no durable identity -- while the Store history retains held
;;; rows whose payload is an arena handle.  A row stands for RECORD when it
;;; is a held row and its wire form through the arena (`fn-row-wire-of') is
;;; RECORD: the flipped Store retains every article as a held row.  Executed
;;; without reading a non-matching row's bytes: the row's other fields are
;;; compared with RECORD's first (RECORD's own payload in the payload
;;; position), and only a row that matches them has its bytes read.
(defun fn-bpr-row-stands-for (row record fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic (and (fn-held-p row) (equal (fn-row-wire-of row fn-arena) record))
       :exec (and (fn-held-p row)
                  (equal (fn-held-wire row (fn-record-payload record)) record)
                  (equal (fn-row-bytes row fn-arena) (fn-record-payload record)))))

(local (defthm fn-bpr-payload-of-held-wire
  (equal (fn-record-payload (fn-held-wire h payload)) payload)
  :hints (("Goal" :in-theory (enable fn-held-wire)))))

(verify-guards fn-bpr-row-stands-for
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of) (fn-held-wire fn-row-bytes fn-held-p fn-record-payload)))))

; Some row of ROWS stands for RECORD.
(defun fn-bpr-rows-stand-for (record rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (or (fn-bpr-row-stands-for (car rows) record fn-arena)
          (fn-bpr-rows-stand-for record (cdr rows) fn-arena))
    nil))

; Toward ALPHA of the rows: a record some row stands for is a member of the
; rows' wire forms (the converse, over a Store's history, is
; books/bp-receipt-alpha.lisp fn-bpr-store-record-acceptedp-is-acceptance-over-alpha).
(defthm fn-bpr-rows-stand-for-is-member-of-alpha
  (implies (fn-bpr-rows-stand-for record rows fn-arena)
           (member-equal record (fn-rows-wire-of rows fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rows-wire-of) (fn-row-wire-of fn-held-p)))))

;; The row standing for RECORD (the first), and the facts the receiver books
;; reason with: a member row that stands for RECORD witnesses the search, the
;; search survives a larger row list, and a held row's committed node article
;; is RECORD's through the arena.
(defun fn-bpr-row-standing-for (record rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (if (fn-bpr-row-stands-for (car rows) record fn-arena)
          (car rows)
        (fn-bpr-row-standing-for record (cdr rows) fn-arena))
    nil))

(defthm fn-bpr-row-standing-for-witnesses
  (implies (fn-bpr-rows-stand-for record rows fn-arena)
           (and (member-equal (fn-bpr-row-standing-for record rows fn-arena) rows)
                (fn-bpr-row-stands-for (fn-bpr-row-standing-for record rows fn-arena)
                                       record fn-arena)))
  :hints (("Goal" :in-theory (disable fn-bpr-row-stands-for))))

(defthm fn-bpr-rows-stand-for-of-member
  (implies (and (member-equal row rows)
                (fn-bpr-row-stands-for row record fn-arena))
           (fn-bpr-rows-stand-for record rows fn-arena))
  :hints (("Goal" :in-theory (disable fn-bpr-row-stands-for))))

(defthm fn-bpr-rows-stand-for-of-subset
  (implies (and (fn-bpr-rows-stand-for record rows1 fn-arena)
                (subsetp-equal rows1 rows2))
           (fn-bpr-rows-stand-for record rows2 fn-arena))
  :hints (("Goal" :in-theory (disable fn-bpr-row-stands-for))))

(local (defthm fn-bpr-payload-of-held-wire-2
  (equal (fn-record-payload (fn-held-wire h payload)) payload)
  :hints (("Goal" :in-theory (enable fn-held-wire)))))

(defthm fn-bpr-accessors-of-held-wire
  (and (equal (fn-record-msgid (fn-held-wire h payload)) (fn-record-msgid h))
       (equal (fn-record-groups (fn-held-wire h payload)) (fn-record-groups h))
       (equal (fn-record-content-subject (fn-held-wire h payload)) (fn-record-content-subject h))
       (equal (fn-record-obligation-id (fn-held-wire h payload)) (fn-record-obligation-id h))
       (equal (fn-record-txid (fn-held-wire h payload)) (fn-record-txid h)))
  :hints (("Goal" :in-theory (enable fn-held-wire))))

; A held row the node committed (its article's payload is the row's handle)
; is committed as its wire form through the arena.
(defthm fn-bpr-node-committed-row-is-wire-committed
  (implies (and (fn-held-p row)
                (fn-bpi-node-record-committedp node row))
           (fn-bpi-node-wire-committedp node (fn-row-wire-of row fn-arena) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-bpi-node-record-committedp fn-bpi-node-wire-committedp
                                   fn-row-wire-of fn-row-bytes fn-handle-bytes)
                                  (fn-held-p fn-find-article fn-node-find-binding fn-node-statep
                                   fn-held-wire fn-record-msgid fn-record-groups fn-record-payload
                                   fn-record-content-subject fn-record-obligation-id)))))

(defthm fn-bpr-row-stands-for-held-accessors
  (implies (fn-bpr-row-stands-for row record fn-arena)
           (and (equal (fn-record-msgid record) (fn-record-msgid row))
                (equal (fn-record-groups record) (fn-record-groups row))
                (equal (fn-record-content-subject record) (fn-record-content-subject row))
                (equal (fn-record-obligation-id record) (fn-record-obligation-id row))
                (equal (fn-record-txid record) (fn-record-txid row))
                (equal (fn-record-payload record) (fn-row-bytes row fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of)
                                  (fn-held-p fn-row-bytes fn-held-wire fn-record-msgid
                                   fn-record-groups fn-record-payload fn-record-content-subject
                                   fn-record-obligation-id fn-record-txid)))))

; The explicit A-POLICY value is trusted laboratory input.  Request wire fields
; are checked for exact contextual agreement but never authorize acceptance.
; A signed article is committed as a kind-4 composite, not as a plain record;
; its article record is a member of the history's article records, so the
; receiver binds it as it binds a plain one (PKT-247).
;
; RECORD is a WIRE record; the history's article records are retained rows
; and the node's article payloads are handles, so both are read through the
; arena: a row of the history's article records stands for RECORD
; (`fn-bpr-rows-stand-for'), and the node's article, its bytes read through
; the arena, agrees with RECORD (`fn-bpi-node-wire-committedp').  The
; receipt keystone fn-bpr-store-record-acceptedp-is-acceptance-over-alpha
; (books/bp-receipt-alpha.lisp) says this is the pre-flip predicate over
; ALPHA of the Store.
(defun fn-bpr-store-record-acceptedp (store record fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  ; Store file completion history is deliberately transient: recovery rebuilds
  ; the durable node from its published namespace and bindings.  Receiver
  ; context replay therefore grounds acceptance in that recovered durable
  ; article/archive binding and authoritative recovered record list, rather
  ; than in a pre-crash success observation.  A non-ready file machine cannot
  ; issue a receiver receipt, even if its node still has a matching article.
  (and (fn-sn-statep store) (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (fn-bpr-rows-stand-for
        record (fn-bpr-article-records (fn-sf-records (fn-sn-files store))) fn-arena)
       (fn-bpi-node-wire-committedp (fn-sn-node store) record fn-arena)))
(defun fn-bpr-request-acceptablep (store config record request policy-authorizedp fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (equal policy-authorizedp t) (fn-bpr-configp config)
       (fn-bpa-requestp request) (fn-record-p record)
       (fn-bpr-store-record-acceptedp store record fn-arena)
       (equal (fn-bpa-request-destination-eid request)
              (fn-bpr-config-destination config))
       (equal (fn-bpa-request-policy-id request)
              (fn-bpr-config-policy-id config))
       (equal (fn-bpa-request-subject request)
              (fn-record-content-subject record))
       (equal (fn-bpa-request-article request) (fn-record-payload record))))

; The identity/conflict transition is shared by historical raw-byte contexts
; and the transit context.  Only their Store-payload admission predicates
; differ; both preserve the original request for receipt construction.
(defun fn-bpr-bind-context (st context)
    (let* ((prior (fn-bpr-find-context (fn-bpr-context-work-id context)
                                       (fn-bpr-state-contexts st)))
           (by-msgid (fn-bpr-find-context-msgid (fn-bpr-context-msgid context)
                                                (fn-bpr-state-contexts st))))
      (if prior
          (if (equal prior context) (list :duplicate st) (list :conflict st))
        (if by-msgid
            (list :conflict st)
          (list :accepted
                (fn-bpr-make-state
                 (fn-bpr-state-config st)
                 (cons context (fn-bpr-state-contexts st))
                 (fn-bpr-state-receipts st) nil))))))
(defun fn-bpr-bind-request-context (st record request)
  (fn-bpr-bind-context st (fn-bpr-context-from-request record request)))

; Result tags: :accepted, :duplicate, :conflict, :refused.  The context is
; retained only after actual Store durable acceptance and a local A-POLICY.
(defun fn-bpr-accept-request (st store record request policy-authorizedp fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (not (and (fn-bpr-statep st) (not (consp (fn-bpr-state-pending st)))
                (fn-bpr-request-acceptablep store (fn-bpr-state-config st)
                                             record request policy-authorizedp fn-arena)))
      (list :refused st)
    (fn-bpr-bind-request-context st record request)))

;; The request a context's reference resolves to over RECORD's payload, or
;; nil.  Proof vocabulary: the receiver invariants ground a context in the
;; Store record it was bound to by resolving its reference there (a context
;; bound from the request whose article IS the record's payload resolves to
;; exactly that request, `fn-bpr-context-resolve-of-derived-context').
(defun fn-bpr-context-resolve (context record)
  (let ((ref (fn-bpr-context-request-ref context)))
    (fn-bpaj-ref-request (car ref) (cadr ref) (caddr ref)
                         (fn-record-payload record))))

(defthm fn-bpr-context-resolve-of-derived-context
  (implies (and (fn-bpa-requestp request)
                (equal (fn-bpa-request-article request)
                       (fn-record-payload record)))
           (equal (fn-bpr-context-resolve
                   (fn-bpr-context-from-request record request) record)
                  request))
  :hints (("Goal" :use ((:instance fn-bpaj-ref-request-resolves-exactly))
           :in-theory (disable fn-bpaj-ref-request-resolves-exactly
                               fn-bpaj-ref-request fn-bpaj-request-ref
                               fn-bpa-requestp))))

;; A TRANSIT context's Store record holds the relay projection, not the
;; request's article, so its acceptance compares the record's payload with
;; the projection's pinned LENGTH and DIGEST (the transit intent's), and
;; binds the context from the request's REFERENCE: nothing here holds or
;; reads the request's bytes.
(defun fn-bpr-projected-ref-acceptablep
    (store config record ref stored-length stored-digest policy-authorizedp
           fn-arena)
  ; fn-arena: the store's records are interned rows after the records flip.
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((m (fn-bpaj-ref-metadata ref)))
    (and (equal policy-authorizedp t) (fn-bpr-configp config)
         (fn-bpaj-request-refp ref) (fn-record-p record)
         (fn-bpr-store-record-acceptedp store record fn-arena)
         (equal (fn-bpa-request-destination-eid m)
                (fn-bpr-config-destination config))
         (equal (fn-bpa-request-policy-id m)
                (fn-bpr-config-policy-id config))
         (equal (len (fn-record-payload record)) stored-length)
         (equal (fn-frame-digest (fn-record-payload record)) stored-digest))))

(defun fn-bpr-accept-projected-ref
    (st store record ref stored-length stored-digest policy-authorizedp
        fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (not (and (fn-bpr-statep st) (not (consp (fn-bpr-state-pending st)))
                (fn-bpr-projected-ref-acceptablep
                 store (fn-bpr-state-config st) record ref
                 stored-length stored-digest policy-authorizedp fn-arena)))
      (list :refused st)
    (fn-bpr-bind-context st (fn-bpr-context-from-ref record ref))))

(defun fn-bpr-receipt-for (context config receipt-id)
  (fn-bpa-make-receipt receipt-id (fn-bpr-context-work-id context)
                       (fn-bpr-context-subject context)
                       (fn-bpr-config-issuer config)
                       ; The receipt goes to the receiver endpoint (the
                       ; request destination), not to its source transport
                       ; provenance.  Source remains retained in context.
                       (fn-bpr-config-destination config)
                       (fn-bpr-context-policy-id context)
                       (fn-bpr-context-incarnation context)
                       (fn-bpr-context-auth-context context)
                       (fn-bpr-context-terms-id context)))
(defun fn-bpr-find-receipt (work-id entries)
  (if (consp entries)
      (if (equal work-id (fn-bpr-context-work-id
                          (fn-bpr-receipt-entry-context (car entries))))
          (car entries)
        (fn-bpr-find-receipt work-id (cdr entries)))
    nil))

; Receipt intent must be persisted before its committed publication decision.
(defun fn-bpr-prepare-receipt (st work-id receipt-id policy-authorizedp)
  (if (or (not (fn-bpr-statep st)) (not (equal policy-authorizedp t))
          (consp (fn-bpr-state-pending st)))
      st
    (let ((context (fn-bpr-find-context work-id (fn-bpr-state-contexts st))))
      (if (or (not context) (fn-bpr-find-receipt work-id (fn-bpr-state-receipts st)))
          st
        (let ((receipt (fn-bpr-receipt-for context (fn-bpr-state-config st) receipt-id)))
          (if (fn-bpa-receiptp receipt)
              (fn-bpr-make-state (fn-bpr-state-config st)
                                 (fn-bpr-state-contexts st)
                                 (fn-bpr-state-receipts st)
                                 (fn-bpr-make-receipt-entry context receipt))
            st))))))
(defun fn-bpr-commit-receipt (st work-id receipt-id outcome)
  (if (not (and (fn-bpr-statep st) (consp (fn-bpr-state-pending st))))
      st
    (let ((pending (fn-bpr-state-pending st)))
      ; Completion identifies the exact pending receipt.  A stale completion
      ; cannot resolve a later intent for a different work/receipt pair.
      (if (not (and (equal work-id
                          (fn-bpr-context-work-id
                           (fn-bpr-receipt-entry-context pending)))
                    (equal receipt-id
                          (fn-bpa-receipt-id
                           (fn-bpr-receipt-entry-receipt pending)))))
          st
        (if (equal outcome :committed)
            (fn-bpr-make-state (fn-bpr-state-config st)
                               (fn-bpr-state-contexts st)
                               (cons pending (fn-bpr-state-receipts st)) nil)
          (if (equal outcome :absent)
              (fn-bpr-make-state (fn-bpr-state-config st)
                                 (fn-bpr-state-contexts st)
                                 (fn-bpr-state-receipts st) nil)
            st))))))

; Regeneration requires the accepted context of the same request -- by
; reference: the same metadata and an article of the same length and digest
; (a different article of one length and digest is a collision, A-CRYPTO,
; `fn-bpaj-one-reference-is-one-request-or-a-digest-collision') -- and a committed
; receipt.  The new BP BID is purposely not an input to this article/receipt
; decision; transport retry cannot create a second charge or decision.
(defun fn-bpr-receipt-adu (st request)
  (let ((context (and (fn-bpa-requestp request)
                      (fn-bpr-find-context (fn-bpa-request-work-id request)
                                           (fn-bpr-state-contexts st)))))
    (if (and (fn-bpr-statep st) context
             (equal (fn-bpaj-request-ref request)
                    (fn-bpr-context-request-ref context)))
        (let ((entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                          (fn-bpr-state-receipts st))))
          (if entry (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)) nil))
      nil)))

; Export theory.  Records are opaque above (shape and accessor-of-constructor
; lemmas exported, definitions withdrawn).  Recognizers, the initial state and
; the receiver transitions are proof vocabulary: the receiver books open what
; they need locally (fn-bp-receiver-vocabulary).  The list vocabulary
; (fn-bpr-context-listp, fn-bpr-receipt-listp, the three finders) stays
; enabled: proofs induct on it.
(deftheory fn-bp-receiver-vocabulary
  '(fn-bpr-configp fn-bpr-contextp fn-bpr-receipt-entryp fn-bpr-statep
    fn-bpr-initial-state fn-bpr-context-from-request fn-bpr-context-from-ref
    fn-bpr-context-resolve fn-bpr-store-record-acceptedp fn-bpr-request-acceptablep
    fn-bpr-accept-request fn-bpr-receipt-for fn-bpr-prepare-receipt
    fn-bpr-commit-receipt fn-bpr-receipt-adu))
(in-theory (disable fn-bp-receiver-vocabulary))
