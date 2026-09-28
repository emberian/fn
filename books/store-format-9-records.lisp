; fn: the records of a format-9 archive, translated to format 10 at `store
; import' (lane format-bump-10; the coordinator's option (a) of 2026-09-28,
; D34: export on the release that made the store, import here).
;
; Format 9 derived every content identity with SHA-256 (algorithm octet 1,
; books/identity.lisp); format 10 derives them with BLAKE3 (algorithm 2).  An
; article record stores its two identities as text (`fn-record-obligation-
; id', `fn-record-content-subject': fn-id-text of the identity), and a
; retention event names the obligation and the subject it holds or
; releases.  Nothing in format 10 reads algorithm 1, so the import re-derives
; each article's identities from its own octets exactly as a format-10 node
; derives them when it accepts the article (the subject from the payload,
; `fn-id-subject-of-payload'; the obligation from the Message-ID and the
; subject, `fn-id-obligation-of'), keeps every other field, and rewrites each
; retention event's obligation and subject through the map the translated
; articles define.  An identity a retention event names that no earlier
; article defined is refused by name (`:unknown-identity'), never guessed;
; a kind whose translation is not written yet (signed composites, verdicts,
; keyring snapshots, topic events: their identities are checked at replay
; against re-derivations) is refused by name (`:untranslatable-kind'), never
; imported with format-9 identities in it.  Consumer events carry no
; identity and pass unchanged.
;
; What "identical" means across the migration (specs/storage.md STO-028):
; the imported store's history is the translated records; every field but
; the re-derived identities is the archive's (fn-f9r-article-keeps-every-
; other-field), and each re-derived identity is the one a format-10 node
; writes for that article (fn-f9r-article-identities-are-format-10s).
(in-package "ACL2")
(include-book "store-events")
(include-book "identity")
(local (include-book "identity-invariants"))

; The subject a payload derives is octets (the seam's digest is 32 octets).
(local
 (defthm fn-f9r-subject-of-payload-octets
   (fn-cbor-octet-listp (fn-id-subject-of-payload p))
   :hints (("Goal" :in-theory (e/d (fn-id-subject-of-payload fn-id-digestp)
                                   (fn-id-subject-shape))
            :use ((:instance fn-id-subject-shape
                             (digest (fn-frame-digest (fn-id-subject-preimage p)))))))))

; -----------------------------------------------------------------------------
; An article's identities, as format 10 derives them

(defun fn-f9r-subject (record)
  (declare (xargs :guard t :verify-guards nil))
  (let ((payload (fn-record-payload record)))
    (if (and (fn-cbor-octet-listp payload) (<= (len payload) *fn-cbor-max-uint*))
        (fn-id-subject-of-payload payload)
      nil)))

(defun fn-f9r-obligation (record subject)
  (declare (xargs :guard t :verify-guards nil))
  (let ((msgid (fn-record-string-octets (fn-record-msgid record))))
    (if (and (fn-cbor-octet-listp msgid) (<= (len msgid) *fn-cbor-max-uint*)
             (fn-cbor-octet-listp subject) (<= (len subject) *fn-cbor-max-uint*))
        (fn-id-obligation-of msgid subject)
      nil)))

(defun fn-f9r-text (identity)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-cbor-octet-listp identity)
      (fn-record-octets-string (fn-id-text identity))
    nil))

; The article record with its two identities re-derived, every other field
; kept.
(defun fn-f9r-article (record)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((subject (fn-f9r-subject record))
         (obligation (fn-f9r-obligation record subject)))
    (fn-record-make (fn-record-sequence record)
                    (fn-record-txid record)
                    (fn-record-generation record)
                    (fn-record-msgid record)
                    (fn-record-payload record)
                    (fn-record-groups record)
                    (fn-f9r-text obligation)
                    (fn-f9r-text subject)
                    (fn-record-release-evidence record)
                    (fn-record-charge record)
                    (fn-record-stamp record))))

; KEYSTONE (the translation keeps the article).  Every field but the two
; identities is the archive's.
(defthm fn-f9r-article-keeps-every-other-field
  (and (equal (fn-record-sequence (fn-f9r-article r)) (fn-record-sequence r))
       (equal (fn-record-txid (fn-f9r-article r)) (fn-record-txid r))
       (equal (fn-record-generation (fn-f9r-article r)) (fn-record-generation r))
       (equal (fn-record-msgid (fn-f9r-article r)) (fn-record-msgid r))
       (equal (fn-record-payload (fn-f9r-article r)) (fn-record-payload r))
       (equal (fn-record-groups (fn-f9r-article r)) (fn-record-groups r))
       (equal (fn-record-release-evidence (fn-f9r-article r))
              (fn-record-release-evidence r))
       (equal (fn-record-charge (fn-f9r-article r)) (fn-record-charge r))
       (equal (fn-record-stamp (fn-f9r-article r)) (fn-record-stamp r)))
  :hints (("Goal" :in-theory (e/d (fn-f9r-article)
                                  (fn-f9r-subject fn-f9r-obligation fn-f9r-text)))))

; KEYSTONE (the identities are format 10's).  The translated article's
; content subject is the text of `fn-id-subject-of-payload' of its payload,
; and its obligation the text of `fn-id-obligation-of' its Message-ID and
; that subject: the derivation books/hybrid-store.lisp checks at replay
; (fn-hsig-carried-record-metadatap) and a format-10 node writes at
; acceptance, now under BLAKE3.
(defthm fn-f9r-article-identities-are-format-10s
  (implies (and (fn-cbor-octet-listp (fn-record-payload r))
                (<= (len (fn-record-payload r)) *fn-cbor-max-uint*)
                (fn-cbor-octet-listp (fn-record-string-octets (fn-record-msgid r)))
                (<= (len (fn-record-string-octets (fn-record-msgid r))) *fn-cbor-max-uint*))
           (let ((subject (fn-id-subject-of-payload (fn-record-payload r))))
             (and (equal (fn-record-content-subject (fn-f9r-article r))
                         (fn-record-octets-string (fn-id-text subject)))
                  (equal (fn-record-obligation-id (fn-f9r-article r))
                         (fn-record-octets-string
                          (fn-id-text
                           (fn-id-obligation-of
                            (fn-record-string-octets (fn-record-msgid r))
                            subject)))))))
  :hints (("Goal" :in-theory (e/d (fn-f9r-article fn-f9r-subject fn-f9r-obligation fn-f9r-text)
                           (fn-id-subject-of-payload fn-id-obligation-of fn-id-text)))))

; -----------------------------------------------------------------------------
; Retention events: their identity texts through the articles' map

; A text that is a format-9 (algorithm 1) identity: lowercase hex whose
; octets carry the subject or obligation label, the separator, version 1 and
; algorithm 1.
(defun fn-f9r-v1-identity-textp (text)
  (declare (xargs :guard t :verify-guards nil))
  (let ((octets (fn-record-string-octets text)))
    (and (fn-id-hex-listp octets)
         (evenp (len octets))
         (let ((id (fn-id-from-text octets)))
           (and (true-listp id)
                (or (and (equal (len id) *fn-id-subject-octets*)
                         (equal (take 13 id) *fn-id-subject-label*)
                         (equal (nthcdr 13 (take 16 id)) (list 0 1 1)))
                    (and (equal (len id) *fn-id-obligation-octets*)
                         (equal (take 16 id) *fn-id-obligation-label*)
                         (equal (nthcdr 16 (take 19 id)) (list 0 1 1)))))))))

; TEXT through MAP: its image, itself when it is no format-9 identity, or
; :unknown-identity for a format-9 identity no article defined.
(defun fn-f9r-map-text (text map)
  (declare (xargs :guard (alistp map) :verify-guards nil))
  (let ((hit (assoc-equal text map)))
    (cond (hit (cdr hit))
          ((fn-f9r-v1-identity-textp text) :unknown-identity)
          (t text))))

(defun fn-f9r-retention (event map)
  (declare (xargs :guard (alistp map) :verify-guards nil))
  (let ((obligation (fn-f9r-map-text (fn-store-event-obligation-id event) map))
        (subject (fn-f9r-map-text (fn-store-event-subject event) map)))
    (if (or (equal obligation :unknown-identity) (equal subject :unknown-identity))
        :unknown-identity
      (fn-store-retention-event-make (fn-store-event-kind event)
                                     (fn-store-event-sequence event)
                                     (fn-store-event-txid event)
                                     (fn-store-event-generation event)
                                     obligation subject
                                     (fn-store-event-evidence event)
                                     (fn-store-event-charge event)))))

; -----------------------------------------------------------------------------
; The archive's records

; Translate the decoded wire EVENTS in order, the map accumulated from the
; articles: the translated events, or (:refused REASON SEQUENCE).
(defun fn-f9r-events (events map)
  (declare (xargs :guard (alistp map) :verify-guards nil))
  (if (atom events)
      nil
    (let ((ev (car events)))
      (cond ((fn-record-p ev)
             (let* ((new (fn-f9r-article ev))
                    (map (list* (cons (fn-record-obligation-id ev)
                                      (fn-record-obligation-id new))
                                (cons (fn-record-content-subject ev)
                                      (fn-record-content-subject new))
                                map))
                    (rest (fn-f9r-events (cdr events) map)))
               (if (and (consp rest) (equal (car rest) :refused))
                   rest
                 (cons new rest))))
            ((fn-store-retention-event-p ev)
             (let ((new (fn-f9r-retention ev map)))
               (if (equal new :unknown-identity)
                   (list :refused :unknown-identity (fn-wire-event-sequence ev))
                 (let ((rest (fn-f9r-events (cdr events) map)))
                   (if (and (consp rest) (equal (car rest) :refused))
                       rest
                     (cons new rest))))))
            ((fn-cpe-eventp ev)
             (let ((rest (fn-f9r-events (cdr events) map)))
               (if (and (consp rest) (equal (car rest) :refused))
                   rest
                 (cons ev rest))))
            (t (list :refused :untranslatable-kind (fn-wire-event-sequence ev)))))))

(defun fn-f9r-decode-all (records)
  ; RECORDS: ((SEQUENCE . OCTETS) ...); the decoded events, or :bad.
  (declare (xargs :guard t :verify-guards nil))
  (if (atom records)
      nil
    (let* ((octets (if (consp (car records)) (cdar records) nil))
           (decoded (fn-store-event-decode-exact octets))
           (rest (fn-f9r-decode-all (cdr records))))
      (if (and (consp decoded) (equal (car decoded) :ok) (consp (cdr decoded))
               (not (equal rest :bad)))
          (cons (cadr decoded) rest)
        :bad))))

(defun fn-f9r-encode-all (events)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom events)
      nil
    (cons (cons (fn-wire-event-sequence (car events))
                (fn-store-event-encode (car events)))
          (fn-f9r-encode-all (cdr events)))))

; The import's records for a format-9 archive's RECORDS: ((SEQUENCE .
; OCTETS) ...) translated, or (:refused REASON [SEQUENCE]).
(defun fn-f9r-records (records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((events (fn-f9r-decode-all records)))
    (if (equal events :bad)
        (list :refused :record-codec)
      (let ((translated (fn-f9r-events events nil)))
        (if (and (consp translated) (equal (car translated) :refused))
            translated
          (fn-f9r-encode-all translated))))))

; A history with no identity in it (consumer events only) translates to
; itself.
(defthm fn-f9r-events-of-consumer-events
  (implies (and (consp events) (fn-cpe-eventp (car events))
                (not (fn-record-p (car events)))
                (not (fn-store-retention-event-p (car events))))
           (equal (fn-f9r-events events map)
                  (let ((rest (fn-f9r-events (cdr events) map)))
                    (if (and (consp rest) (equal (car rest) :refused))
                        rest
                      (cons (car events) rest)))))
  :hints (("Goal" :expand ((fn-f9r-events events map)))))
