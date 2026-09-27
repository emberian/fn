; Trusted bounded marshalling helpers for the composed store bridge.
; Stateful acceptance/recovery/completion live only in store-node-host.lisp.
; No untrusted input is read as Lisp: the process interface supplies decimal
; octets and fixed operation names after Python boundary validation.
;
; Every decision this file used to share with Python now has one owner in a
; certified book: framing and the integrity trailer comparison in
; `books/frame`, content identity and the charge policy in `books/identity`,
; the group table in the store's replayed configuration (`books/config`,
; `books/node-config`; `books/store-config` keeps the name/code inversion),
; and the Message-ID grammar in `books/article-fields`.  The wrappers below
; only marshal.

(in-package "ACL2")
(include-book "../books/replay")
(include-book "../books/store-intern")
(include-book "../books/store-recover-stream")
; The open's extent seals and the served read's trailer check (PRF-294);
; the commit's extent reseat (PRF-309; it includes payload-extent).
(include-book "../books/payload-commit-extent")
; The served read's entry check over the realizer's buffer (PRF-295).
(include-book "../books/payload-extent-read")
(include-book "../books/store-config")
(include-book "../books/identity")
(include-book "../books/crypto-attach")
(include-book "../books/frame-trailer")
(include-book "../books/byte-store-frame")
(include-book "../books/byte-store-txn-name")
(include-book "../books/store-budget-naming")
(include-book "../books/store-profile-facts")
(include-book "../books/store-replay-bound")
(include-book "../books/store-profile-open")
(include-book "../books/store-mount-identity")
(include-book "../books/store-profile-namespace")
(include-book "../books/native-operator")
(include-book "../books/article-fields")
(include-book "../books/post-fields")
(include-book "../books/store-log-route")
;; The log kernel the host holds (lane per-record-state; host/native/io.lisp
;; fnn-log-*): the committed records' count in place of their list.
(include-book "../books/store-log-kernel-concrete")
(include-book "../books/store-log-stream")
(include-book "../books/store-log-segments")
(include-book "../books/store-log-extend")
(include-book "../books/store-init-log-publication")

; The field checks of the Store's prepares (the metadata text domain, the
; Message-ID grammar, the composed POST verdicts) are ACL2's:
; books/post-fields.lisp (fn-pfld-).  This file defines none of them.

(defun fn-store-octets->string (xs)
  (fn-record-octets-string xs))

; The final transaction namespace is an ACL2 value.  The native host consumes
; the string wrapper; the Python bridge consumes octets so no Lisp string
; reader or duplicate decimal formatter sits on its persistence path.  The name
; is `fn-sbud-txn-name', the scan's `fn-bs-txn-name', and the sequence the host
; names is the staged record's own (`fn-sbud-pending-sequence'): the name
; written is the name the scan expects next
; (`fn-sbud-pending-name-is-the-scans-next-name').
(defun fn-store-txn-name (sequence)
  (fn-sbud-txn-name sequence))

(defun fn-store-txn-name-octets (sequence)
  (fn-record-string-octets (fn-store-txn-name sequence)))

; A final namespace observation is not parsed by the native adapter.  The
; bounded host enumeration is sorted only to make its representation stable.
; This conversion only validates octets before the scan policy compares names.
(defun fn-store-octet-lists->strings (xs)
  (if (consp xs)
      (if (not (fn-cbor-octet-listp (car xs)))
          :bad
        (let ((rest (fn-store-octet-lists->strings (cdr xs))))
          (if (equal rest :bad)
              :bad
            (cons (fn-store-octets->string (car xs)) rest))))
    (if (null xs) nil :bad)))

(defun fn-store-txn-observation (observed maximum)
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings observed)))
    (if (and (natp maximum) (true-listp observed)
             (not (equal names :bad)) (<= (len names) maximum))
        ;; The byte-store scan owns exact names and contiguous sequences.
        (fn-bs-txn-observation-pairs names 0)
      :invalid)))

; The bound and the grammar are `fn-profile-txn-observation'
; (books/store-profile-facts.lisp); this wrapper converts octets.
(defun fn-store-txn-observation-selected (observed maximum selected-lower)
  (declare (xargs :mode :program))
  (let ((names (fn-store-octet-lists->strings observed)))
    (if (and (true-listp observed) (not (equal names :bad)))
        (fn-profile-txn-observation names maximum selected-lower)
      :invalid)))

; The transaction-prefix reclaim plan is `fn-bs-pack-reclaim-plan'
; (books/byte-store-compaction-correspondence), whose namespace gate is
; `fn-profile-txn-observation'; host/native/checkpoint.lisp calls it directly.

; The record wrappers recognise and dispatch through the concrete twins of
; books/records-concrete.lisp.  What the codec decodes is a WIRE event
; (fn-rcon-wire-event-p-is-wire-event-p, -sequence-is-, -txid-is-): the
; journal's and the checkpoint's bytes.  The store machine never holds one:
; the entry interns the decoded events into the arena first
; (fn-store-intern-records below; books/store-intern.lisp fn-intern-events).
(defun fn-store-decode-records (octet-records)
  ; books/store-recover-stream.lisp fn-srs-decode: the chunked open's step
  ; decodes with the same function.
  (declare (xargs :mode :program
                  :guard (fn-octet-list-listp octet-records)))
  (fn-srs-decode octet-records))

; THE INTERN AT THE OPEN (records-flip; PKT-635): the decoded wire events
; become the store's rows, every article's payload sealed once into the
; arena (fn-intern-events; KEYSTONES fn-intern-events-materializes,
; -keep-coordinates, -contexts-okp).  The keyring at open is nil and the
; generation 0 (the host installs the operator's keyring afterwards through
; fn-store-sn-set-keyring, which recontexts every row through the arena).
; :bad when any event is refused (a composite whose article does not decode).
(defun fn-store-intern-records (records fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (fn-intern-events records nil 0 fn-arena))

; The same intern into a LOCAL arena, for a decision over a history that is
; not the live Store's (the administrative candidate reopen, the checkpoint
; generation capture): the rows are the replay's domain; the arena is dropped
; with the answer, so nothing is retained.
(defun fn-store-intern-records-local (records)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (rows fn-arena)
      (fn-intern-events records nil 0 fn-arena)
      rows)))

; A journal record's sequence, read off the WIRE event its octets decode to
; (fn-rcon-wire-event-sequence-is-wire-event-sequence, books/records-concrete):
; the host names and orders transaction files by it before any intern.  It is
; books/store-recover-stream.lisp fn-srs-record-sequence, whose check the
; streaming open makes inside its one decode (fn-srs-checked-decode,
; KEYSTONE fn-srs-checked-decode-is-the-per-file-check).
(defun fn-store-record-sequence (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-srs-record-sequence octets))

(defun fn-store-record-txid (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (let ((decoded (fn-store-event-decode-exact octets)))
    (if (and (consp decoded) (equal (car decoded) :ok)
             (consp (cdr decoded)) (fn-rcon-wire-event-p (car (cdr decoded))))
        (fn-rcon-wire-event-txid (car (cdr decoded)))
      -1)))

; -----------------------------------------------------------------------------
; Frame bridge
;
; Python supplies octets and the SHA-256 digest of the protected prefix
; (A-CRYPTO); ACL2 supplies magic, version, kind, the length field, every
; bound and the trailer comparison.  Encoders answer an octet list or :bad;
; decoders answer (:ok ...) or (:error reason), so a refusal reaches Python
; with its reason rather than as an absence.

(defun fn-store-frame-constants ()
  ; The layout numbers Python needs in order to slice a file it does not
  ; interpret: header, trailer and total overhead, then the per-schema caps.
  (list *fn-frame-header-octets* *fn-frame-trailer-octets*
        *fn-frame-overhead-octets* *fn-frame-max-store-payload*
        *fn-frame-max-workflow-payload* *fn-frame-max-receipt-payload*
        *fn-frame-max-inbound-payload* *fn-frame-max-text*
        *fn-frame-max-blob* *fn-frame-max-identity*))

(defun fn-store-frame-result (frame)
  ; (:ok payload) or (:error reason) for a frame whose payload is opaque.
  (if (fn-frame-result-okp frame)
      (list :ok (fn-frame-result-payload frame))
    frame))

(defun fn-store-frame-record-result (frame)
  ; (:ok kind values) or (:error reason) for a journal record.
  (if (fn-frame-result-okp frame)
      (list :ok (fn-frame-result-kind frame) (fn-frame-result-payload frame))
    frame))

(defun fn-store-frame-store-protected (record)
  (fn-frame-store-protected record))

(defun fn-store-frame-workflow-protected (kind values)
  (fn-frame-workflow-protected kind values))

(defun fn-store-frame-receipt-protected (kind values)
  (fn-frame-receipt-protected kind values))

(defun fn-store-frame-names-octets (names)
  (if (consp names)
      (cons (fn-record-string-octets (car names))
            (fn-store-frame-names-octets (cdr names)))
    nil))

(defun fn-store-frame-schema (kind names-table spec-table)
  ; (:ok (field-name-octets ...) (field-specification ...)) or (:error :kind).
  (let ((names (fn-frame-spec-for kind names-table))
        (spec (fn-frame-spec-for kind spec-table)))
    (if (or (equal names :none) (equal spec :none))
        (list :error :kind)
      (list :ok (fn-store-frame-names-octets names) spec))))

(defun fn-store-frame-workflow-schema (kind)
  (fn-store-frame-schema kind *fn-frame-workflow-field-names*
                         *fn-frame-workflow-specs*))

(defun fn-store-frame-receipt-schema (kind)
  (fn-store-frame-schema kind *fn-frame-receipt-field-names*
                         *fn-frame-receipt-specs*))

(defun fn-store-frame-workflow-kinds ()
  *fn-frame-workflow-kinds*)

(defun fn-store-frame-receipt-kinds ()
  *fn-frame-receipt-kinds*)

; Native application journals hold the logical record values used by
; bp-workflow-records and bp-receipt-records: text fields are ACL2 strings.
; The durable frame grammar holds text octets.  Keep that representation
; conversion here, beside the schema ACL2 owns, instead of copying field
; positions or types into raw Lisp.
(defun fn-store-frame-logical-to-wire-values (spec values)
  (declare (xargs :mode :program))
  (if (and (consp spec) (consp values))
      (cons (if (equal (car spec) :text)
                (if (stringp (car values))
                    (fn-record-string-octets (car values))
                  (car values))
              (if (and (consp (car spec))
                       (equal (cdr (car spec)) *fn-frame-authorized*)
                       (equal (car values) t))
                  :authorized
                (car values)))
            (fn-store-frame-logical-to-wire-values (cdr spec) (cdr values)))
    (if (and (null spec) (null values)) nil :bad)))

(defun fn-store-frame-wire-to-logical-values (spec values)
  (declare (xargs :mode :program))
  (if (and (consp spec) (consp values))
      (cons (if (equal (car spec) :text)
                (fn-record-octets-string (car values))
              (if (and (consp (car spec))
                       (equal (cdr (car spec)) *fn-frame-authorized*)
                       (equal (car values) :authorized))
                  t
                (car values)))
            (fn-store-frame-wire-to-logical-values (cdr spec) (cdr values)))
    (if (and (null spec) (null values)) nil :bad)))

(defun fn-store-frame-workflow-logical-protected (kind values)
  (declare (xargs :mode :program))
  (let ((spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
    (if (equal spec :none) :bad
      (fn-frame-workflow-protected
       kind (fn-store-frame-logical-to-wire-values spec values)))))

(defun fn-store-frame-receipt-logical-protected (kind values)
  (declare (xargs :mode :program))
  (let ((spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
    (if (equal spec :none) :bad
      (fn-frame-receipt-protected
       kind (fn-store-frame-logical-to-wire-values spec values)))))

(defun fn-store-frame-logical-result (answer table)
  (declare (xargs :mode :program))
  (if (and (consp answer) (equal (car answer) :ok))
      (let* ((kind (car (cdr answer)))
             (values (car (cdr (cdr answer))))
             (spec (fn-frame-spec-for kind table)))
        (if (equal spec :none) (list :error :kind)
          (list :ok kind
                (fn-store-frame-wire-to-logical-values spec values))))
    answer))

(defun fn-store-frame-store-encode (record digest)
  (fn-frame-store-encode record digest))

(defun fn-store-frame-store-decode (octets digest)
  (fn-store-frame-result (fn-frame-store-decode octets digest)))

; The open's unframe of a transaction file split at its trailer
; (host/native/io.lisp fnn-unframe-list): books/store-recover-stream.lisp
; fn-srs-unframe, KEYSTONE fn-srs-unframe-is-the-frame-decode (the frame
; decode of PREFIX then TRAILER with PREFIX's trailer, as
; fn-store-frame-store-decode above answers for the whole file and its
; digest), with the payload PREFIX's own tail.
(defun fn-store-unframe-split (prefix trailer)
  (fn-store-frame-result (fn-srs-unframe prefix trailer)))

(defun fn-store-frame-workflow-encode (kind values digest)
  (fn-frame-workflow-encode kind values digest))

(defun fn-store-frame-workflow-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-workflow-decode octets digest)))

(defun fn-store-frame-workflow-logical-decode (octets digest)
  (declare (xargs :mode :program))
  (fn-store-frame-logical-result
   (fn-store-frame-workflow-decode octets digest)
   *fn-frame-workflow-specs*))

(defun fn-store-frame-receipt-encode (kind values digest)
  (fn-frame-receipt-encode kind values digest))

(defun fn-store-frame-receipt-decode (octets digest)
  (fn-store-frame-record-result (fn-frame-receipt-decode octets digest)))

(defun fn-store-frame-receipt-logical-decode (octets digest)
  (declare (xargs :mode :program))
  (fn-store-frame-logical-result
   (fn-store-frame-receipt-decode octets digest)
   *fn-frame-receipt-specs*))

(defun fn-store-frame-inbound-prefix (bid identity bundle-length)
  (fn-frame-inbound-prefix bid identity bundle-length))

(defun fn-store-frame-inbound-open (head total-length trailer digest)
  (let ((frame (fn-frame-inbound-open head total-length trailer digest)))
    (if (fn-frame-result-okp frame)
        ; kind slot carries (BID identity), payload slot the bundle length.
        (list :ok (car (fn-frame-result-kind frame))
              (car (cdr (fn-frame-result-kind frame)))
              (fn-frame-result-payload frame))
      frame)))

; -----------------------------------------------------------------------------
; Identity, charge and group bridge

; The identity derivation, whole, in logic.
;
; Until books/crypto-attach.lisp existed, `fn-frame-digest' was a constrained
; function with no realiser, so the host had to hash: ACL2 handed back the
; fixed preimage head and Python (tools/frame_bridge.py) or the native host
; (host/native/io.lisp) appended the payload and ran its own SHA-256.  That
; was a second owner for a value ACL2 defines, which AGENTS.md forbids.  The
; two wrappers below derive the identity end to end from the payload, and the
; two prefix/digest wrappers that follow are kept ONLY so an old session
; script does not break; nothing in this tree calls them any more.
(defun fn-store-subject-id-of-payload (payload)
  ; The canonical subject-v1 identity of an article payload, preimage and
  ; digest both in ACL2.  The payload crosses the bridge; see
  ; planning/lanes/HANDOFF-w9-digest.md for the measured cost.
  (if (and (fn-cbor-octet-listp payload)
           (<= (len payload) *fn-cbor-max-uint*))
      (fn-id-subject-of-payload payload)
    nil))

(defun fn-store-obligation-id-of (msgid subject)
  ; The canonical obligation-v1 identity, preimage and digest both in ACL2.
  (if (and (fn-cbor-octet-listp msgid)
           (<= (len msgid) *fn-cbor-max-uint*)
           (fn-cbor-octet-listp subject)
           (<= (len subject) *fn-cbor-max-uint*))
      (fn-id-obligation-of msgid subject)
    nil))

(defun fn-store-subject-prefix (length)
  ; Superseded by fn-store-subject-id-of-payload; retained for compatibility.
  (if (and (natp length) (<= length *fn-cbor-max-uint*))
      (fn-id-subject-prefix length)
    nil))

(defun fn-store-subject-id (digest)
  (if (fn-id-digestp digest) (fn-id-subject digest) nil))

(defun fn-store-obligation-preimage (msgid subject)
  (if (and (fn-cbor-octet-listp msgid)
           (<= (len msgid) *fn-cbor-max-uint*)
           (fn-cbor-octet-listp subject)
           (<= (len subject) *fn-cbor-max-uint*))
      (fn-id-obligation-preimage msgid subject)
    nil))

(defun fn-store-obligation-id (digest)
  (if (fn-id-digestp digest) (fn-id-obligation digest) nil))

(defun fn-store-charge (length)
  (if (natp length) (fn-charge-for-payload length) 0))

(defun fn-store-group-name-octets (groups)
  (if (consp groups)
      (cons (fn-record-string-octets (car groups))
            (fn-store-group-name-octets (cdr groups)))
    nil))

(defun fn-store-identity-text (identity)
  ; The one rendering of a canonical identity into a string, for the three
  ; boundaries that cannot carry octets: the store record metadata fields, the
  ; workflow journal JSON and the NNTP header value.
  (if (fn-cbor-octet-listp identity) (fn-id-text identity) nil))

; Durable store metadata.  `tools/run_store.py' calls only these wrappers for
; config.json and allocation-frontier.json.  Their grammar, bounds, profile
; table, CBOR frontier encoding, integrity trailer and decoder are all in
; books/byte-store-frame.lisp; this host file only gives the bridge stable
; entry-point names.
(defun fn-store-metadata-config-frame (profile)
  (fn-bs-config-frame-for-profile profile))

(defun fn-store-metadata-config-decode (octets)
  (fn-bs-config-decode octets))

;; The open of config.json every open path reads (PKT-471,
;; books/store-profile-open.lisp): (:opened VALUES), (:refused REASON) for a
;; saved profile whose record bound the poll reply cannot carry or a profile
;; frame of another format (D34), or (:rejected) for a frame that is no saved
;; profile.  The refusal's line is ACL2's and names the reinstall and import.
(defun fn-store-metadata-config-open (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-spo-config-open octets))

(defun fn-store-metadata-config-refusal-text (verdict)
  (fn-spo-refusal-text verdict))

;; The Python `init --profile WORD': WORD's octets are read by the native
;; operator's own preset parser (`fn-nop-profile-preset-word',
;; development|scale|default) and the frame is the one `init' writes for that
;; preset, or NIL for a word that names none.  With no word, `init' writes
;; `fn-bs-initial-config-octets', as the native `store init' entry does.
(defun fn-store-metadata-config-frame-for-word (octets)
  (let ((preset (fn-nop-profile-preset-word (fn-record-octets-string octets))))
    (if preset (fn-bs-config-frame-for-profile preset) nil)))

(defun fn-store-metadata-initial-config-frame ()
  (fn-bs-initial-config-octets))

;; The commit route of an opened store (lane commit-onto-log): T for a
;; format-9 profile, whose commits go through the record log.
(defun fn-store-profile-logp (values)
  (fn-bs-profile-logp values))

;; The log's next txid at an open (lane commit-onto-log): one past the largest
;; txid of every record the log holds, of every event kind (the codec's
;; dispatch, as fn-store-decode-records decodes them), or FLOOR.  The core's
;; own recovered next txid (books/store-log-txid.lisp fn-lgt-next-after)
;; reads article records only (PKT-836); the log holds retention, identity,
;; consumer and topic events too, and a txid below one of them must never be
;; handed out again.
(defun fn-store-log-next-txid-loop (records acc)
  (declare (xargs :mode :program))
  (if (consp records)
      (let* ((decoded (fn-store-event-decode-exact (car records)))
             (txid (and (consp decoded) (equal (car decoded) :ok) (consp (cdr decoded))
                        (fn-rcon-wire-event-p (car (cdr decoded)))
                        (fn-rcon-wire-event-txid (car (cdr decoded))))))
        (fn-store-log-next-txid-loop (cdr records)
                                     (if (natp txid) (max acc (+ 1 txid)) acc)))
    acc))

(defun fn-store-log-next-txid (records floor)
  (declare (xargs :mode :program))
  (fn-store-log-next-txid-loop records (nfix floor)))

;; The same fold one record at a time (the format-9 open streams its records,
;; host/native/io.lisp fnn-recover-log): (fn-store-log-next-txid-loop R ACC)
;; is the steps over R in order, by its definition; and the join of two
;; frontiers (the fold's, the checkpoint's, the log kernel's next).
(defun fn-store-log-next-txid-step (record acc)
  (declare (xargs :mode :program))
  (fn-store-log-next-txid-loop (list record) (nfix acc)))

;; The same fold over records the replay has already decoded
;; (books/store-recover-stream.lisp fn-srs-decode: each record's
;; fn-store-event-decode-exact, kept when it is :ok with a wire event, which is
;; exactly when fn-store-log-next-txid-loop's step reads that event's txid; any
;; other record makes the chunk :bad and the open faults), so the streamed
;; open decodes each record once.
(defun fn-store-log-next-txid-of-events (events acc)
  (declare (xargs :mode :program))
  (if (consp events)
      (fn-store-log-next-txid-of-events
       (cdr events)
       (let ((txid (fn-rcon-wire-event-txid (car events))))
         (if (natp txid) (max acc (+ 1 txid)) acc)))
    acc))

(defun fn-store-log-next-txid-join (a b)
  (declare (xargs :mode :program))
  (max (nfix a) (nfix b)))

;; The record log's layout (books/store-log-route.lisp).
(defun fn-store-log-segment-name () (fn-olr-segment-name))
(defun fn-store-log-unit () (fn-olr-unit))
(defun fn-store-log-initial-extent () (fn-olr-initial-extent))

;; The store profile (D27, format 8): every value the host reads from it is
;; one of these accessors over the decoded values, never a list position.
(defun fn-store-profile-admittedp (values)
  (fn-bs-profile-admittedp values))

(defun fn-store-profile-init-verdict (request)
  (fn-bs-profile-init-verdict request))

(defun fn-store-profile-max-transactions (values)
  (fn-bs-profile-max-transactions values))

(defun fn-store-profile-max-article-octets (values)
  (fn-bs-profile-max-article-octets values))

;; R, the segment size of the state checkpoint (P3).
(defun fn-store-profile-max-record-octets (values)
  (fn-bs-profile-max-record-octets values))

;; The operator's namespace counts (D27, PRF-102).  The host reads each once
;; from the profile it opened and hands the natural to the ACL2 subject that
;; refuses at it (fn-nco-observe, fn-native-admin-publication-authorize,
;; fn-native-auth-load, fn-native-auth-admin-set-password, and for the
;; consumer count fn-cp-register-within through fn-col-register, called from
;; host/owner-host.lisp fn-owner-consumer-local-register).
(defun fn-store-profile-max-consumers (values)
  (fn-bs-profile-max-consumers values))

(defun fn-store-profile-max-config-generations (values)
  (fn-bs-profile-max-config-generations values))

(defun fn-store-profile-max-credentials (values)
  (fn-bs-profile-max-credentials values))

(defun fn-store-profile-report (values)
  (fn-bs-profile-report values))

;; The Python store's view (tools/run_store.py): the persisted format (8, the
;; one format), then T, H, R and A, every one ACL2's reading.
(defun fn-store-profile-summary (values)
  (list (if (fn-bs-profile-validp values) 8
          (if (fn-bs-profile-admittedp values) 7 0))
        (fn-bs-profile-max-transactions values)
        (fn-bs-profile-max-history-octets values)
        (fn-bs-profile-max-record-octets values)
        (fn-bs-profile-max-article-octets values)))

(defun fn-store-metadata-frontier-frame (n)
  (fn-bs-frontier-encode n))

(defun fn-store-metadata-frontier-decode (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (fn-bs-frontier-decode octets))

(defun fn-store-metadata-frontier-next (n)
  (fn-bs-frontier-next n))

(defun fn-store-publication-admissibility (profile committed-count
                                                   prospective-payload-octets)
  (if (fn-bs-publication-admissiblep profile committed-count
                                     prospective-payload-octets)
      :admissible
    :refused))

;; The replay bound every open checks per record: H plus T records' encoding
;; overhead (books/store-replay-bound.lisp; every history the profile admits
;; is within it, `fn-srb-admitted-history-is-within-the-bound').
(defun fn-store-profile-replay-within-bound (profile aggregate)
  (fn-srb-replay-within-boundp profile aggregate))

(defun fn-store-publication-kind-ceiling (kind)
  (fn-store-publication-ceiling kind))

;; The open's per-file read bound under the persisted PROFILE: one FNST frame
;; whose payload is at most the profile's per-record ceiling.  Every committed
;; transaction file was published under `fn-bs-publication-admissiblep' (its
;; record at most `fn-bs-profile-record-ceiling', asserted on the actual bytes
;; by host/native/io.lisp `fnn-publish'), and the profile is written once, at
;; init or import (D34), so no committed file exceeds this bound.
;; A profile that is not valid yields the frame overhead alone, and the open
;; refuses every file.
(defun fn-store-profile-read-bound (profile)
  (+ *fn-frame-overhead-octets* (fn-bs-profile-record-ceiling profile)))


(defun fn-store-group-codes (name-octets domain-octets)
  (declare (xargs :guard (and (fn-octet-list-listp name-octets) (fn-octet-list-listp domain-octets)) :verify-guards nil))
  ; Distinct group names, as octet lists, become their codes in the replayed
  ; allocation domain the caller was handed at open (`fn-store-cfg-domain').
  ; Python carries that list back verbatim; it never computes a code.
  (let ((names (fn-store-octet-lists->strings name-octets))
        (domain (fn-store-octet-lists->strings domain-octets)))
    (if (or (equal names :bad) (equal domain :bad))
        :bad
      (fn-store-codes-from-groups names domain))))

; The whole POST admission boundary is `fn-sbud-post-boundary'
; (books/store-budget-naming.lisp), over the persisted PROFILE the caller was
; handed at open; both hosts call it by that name.  No host constant enters it.
