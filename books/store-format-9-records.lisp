; fn: the records of a format-9 archive, translated to format 10 at `store
; import' (lanes format-bump-10 and format10-import; the coordinator's option
; (a) of 2026-09-28, D34: export on the release that made the store, import
; here).
;
; Format 9 derived every content identity with SHA-256 (algorithm octet 1,
; books/identity.lisp); format 10 derives them with BLAKE3 (algorithm 2), and
; nothing in format 10 reads algorithm 1.  The translation is decided per
; kind (specs/storage.md STO-028, "Migration from format 9"):
;
;   article (fn-r)       its subject and obligation re-derived from its own
;                        payload and Message-ID exactly as a format-10 node
;                        derives them at acceptance; every other field kept
;                        (fn-f9r-article-keeps-every-other-field,
;                        fn-f9r-article-identities-are-format-10s).
;   retention (fn-e 0/1) its obligation and subject rewritten through the map
;                        the earlier articles define; a format-9 identity no
;                        article defined is refused (:unknown-identity).
;   accepted composite   (fn-e 4, schema 0, schema 1 verified, schema 1
;                        carried) the embedded article translated as above,
;                        the composite's content subject and authored-source
;                        identity re-derived (fn-hsig-authored-source-id, the
;                        derivation replay checks); the authored source, its
;                        signatures (inside the article's payload), the
;                        verdict, the keyring generation and the profile are
;                        carried verbatim.  The D09 signed preimage is the
;                        domain tag, principal, keys and source
;                        (books/hybrid-signature.lisp fn-hsig-signed-preimage):
;                        no identity is in it, so no signature is re-made and
;                        none needs a key this node does not hold
;                        (fn-f9r-composite-keeps-what-it-binds,
;                        fn-f9r-composite-identities-are-format-10s).  A
;                        composite whose translation does not bind its article
;                        and verdict (fn-stxa-bindsp) is refused
;                        (:composite-binding), never imported unbound.
;   statement verdict    (fn-e 2) carried verbatim: it names a Message-ID, a
;                        token, a keyring generation, a profile and a detail
;                        (a principal, or the verified keys and signatures of
;                        a schema-0 composite): no content identity.
;   keyring snapshot     (fn-e 3: enrollment, succession, revocation, the
;                        kind-3 half of a key statement) carried verbatim: a
;                        principal and its two public keys.  A principal is a
;                        32-octet name, not an identity this format derives;
;                        a local account's default principal
;                        (books/accounts.lisp fn-acct-local-principal) WAS
;                        derived under SHA-256, so the snapshot keeps the
;                        format-9 principal and the login now derives another:
;                        that credential is re-enrolled (the migration's loss,
;                        not the record's).
;   consumer (fnce)      carried verbatim (no identity).
;   topic install (fnto 2) carried verbatim (a uid and an entropy id).
;   topic anchor/admit   (fnto 0/1) REFUSED (:signed-format-9-identity).  An
;                        anchor or admission is re-prepared at replay from its
;                        root's or report's SIGNED source, which names the
;                        controller key set, the topic, the policy and the
;                        parents by their format-9 identities; format 10
;                        derives those identities under BLAKE3 and cannot
;                        parse an algorithm-1 one (fn-id-labelledp), and the
;                        source cannot be re-signed without its author's keys.
;                        There is no faithful translation; the refusal names
;                        the record's sequence.
;
; What "identical" means across the migration (specs/storage.md STO-028):
; the imported store's history is the translated records; every field but
; the re-derived identities is the archive's, and each re-derived identity is
; the one a format-10 node writes for that record.
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

(local
 (defthm fn-f9r-subject-of-payload-len
   (equal (len (fn-id-subject-of-payload p)) *fn-id-subject-octets*)
   :hints (("Goal" :in-theory (e/d (fn-id-subject-of-payload fn-id-digestp)
                                   (fn-id-subject-shape))
            :use ((:instance fn-id-subject-shape
                             (digest (fn-frame-digest (fn-id-subject-preimage p)))))))))

(local
 (defthm fn-f9r-obligation-of-octets
   (fn-cbor-octet-listp (fn-id-obligation-of m s))
   :hints (("Goal" :in-theory (e/d (fn-id-obligation-of fn-id-digestp)
                                   (fn-id-obligation-shape))
            :use ((:instance fn-id-obligation-shape
                             (digest (fn-frame-digest (fn-id-obligation-preimage m s)))))))))

; -----------------------------------------------------------------------------
; An article's identities, as format 10 derives them

(defun fn-f9r-subject (record)
  (declare (xargs :guard t))
  (let ((payload (fn-record-payload record)))
    (if (and (fn-cbor-octet-listp payload) (<= (len payload) *fn-cbor-max-uint*))
        (fn-id-subject-of-payload payload)
      nil)))

(defun fn-f9r-obligation (record subject)
  (declare (xargs :guard t))
  (let ((msgid (fn-record-string-octets (fn-record-msgid record))))
    (if (and (fn-cbor-octet-listp msgid) (<= (len msgid) *fn-cbor-max-uint*)
             (fn-cbor-octet-listp subject) (<= (len subject) *fn-cbor-max-uint*))
        (fn-id-obligation-of msgid subject)
      nil)))

(defun fn-f9r-text (identity)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp identity)
      (fn-record-octets-string (fn-id-text identity))
    nil))

; The article record with its two identities re-derived, every other field
; kept.
(defun fn-f9r-article (record)
  (declare (xargs :guard t))
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
                           (fn-id-subject-of-payload fn-id-obligation-of fn-id-text
                            fn-record-string-octets)))))

; -----------------------------------------------------------------------------
; Retention events: their identity texts through the articles' map

; A text that is a format-9 (algorithm 1) identity: lowercase hex whose
; octets carry the subject or obligation label, the separator, version 1 and
; algorithm 1.
(defun fn-f9r-v1-identity-textp (text)
  (declare (xargs :guard t))
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
  (declare (xargs :guard t))
  (let ((hit (hons-get text map)))
    (cond (hit (cdr hit))
          ((fn-f9r-v1-identity-textp text) :unknown-identity)
          (t text))))

; Guard-verified here for the translation (books/store-budget.lisp verifies
; the encoder too; either order is redundant, never a conflict).
(verify-guards fn-store-retention-event-make)
(verify-guards fn-store-event-kind-code)
(verify-guards fn-store-retention-event-encode)
(verify-guards fn-store-event-encode)

(defun fn-f9r-retention (event map)
  (declare (xargs :guard t))
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

;; -----------------------------------------------------------------------------
;; Accepted composites (fn-e kind 4)

; The composite's authored-source identity as format 10 derives it: the
; derivation the replay checks (books/hybrid-store.lisp
; fn-hsig-authored-source-id); a schema-0 composite has none.
(defun fn-f9r-authored-id (e)
  (declare (xargs :guard t))
  (if (equal (fn-stxa-authored-source e) :legacy)
      (fn-stxa-authored-id e)
    (fn-hsig-authored-source-id (fn-stxa-authored-source e))))

; The embedded article of composite E, decoded, or nil.
(defun fn-f9r-composite-article (e)
  (declare (xargs :guard t))
  (let ((rr (fn-record-decode-exact (fn-stxa-article-record e))))
    (if (fn-record-result-okp rr) (fn-record-result-record rr) nil)))

; Composite E with its embedded article translated and its two identities
; re-derived, every other field carried.
(defun fn-f9r-composite (e)
  (declare (xargs :guard t))
  (let ((new (fn-f9r-article (fn-f9r-composite-article e))))
    (fn-stxa-make-full (fn-stxa-sequence e)
                       (fn-stxa-txid e)
                       (fn-stxa-generation e)
                       (fn-stxa-keyring-generation e)
                       (fn-stxa-profile e)
                       (fn-record-string-octets (fn-record-content-subject new))
                       (fn-record-encode new)
                       (fn-stxa-verdict-event e)
                       (fn-stxa-authored-source e)
                       (fn-f9r-authored-id e))))

; KEYSTONE (the composite keeps what it binds).  The coordinates, the keyring
; generation, the profile, the exact verdict bytes and the exact authored
; source are the archive's; the embedded article is the translated archive
; article (so its payload -- the received carrier with both signatures -- its
; Message-ID, groups, evidence, charge and stamp are the archive's).
(defthm fn-f9r-composite-keeps-what-it-binds
  (let ((new (fn-f9r-composite e)))
    (and (equal (fn-stxa-sequence new) (fn-stxa-sequence e))
         (equal (fn-stxa-txid new) (fn-stxa-txid e))
         (equal (fn-stxa-generation new) (fn-stxa-generation e))
         (equal (fn-stxa-keyring-generation new) (fn-stxa-keyring-generation e))
         (equal (fn-stxa-profile new) (fn-stxa-profile e))
         (equal (fn-stxa-verdict-event new) (fn-stxa-verdict-event e))
         (equal (fn-stxa-authored-source new) (fn-stxa-authored-source e))
         (equal (fn-stxa-schema new) (fn-stxa-schema e))
         (equal (fn-stxa-article-record new)
                (fn-record-encode (fn-f9r-article (fn-f9r-composite-article e))))))
  :hints (("Goal" :in-theory (e/d (fn-f9r-composite fn-stxa-schema)
                                  (fn-f9r-article fn-f9r-composite-article
                                   fn-f9r-authored-id)))))

; KEYSTONE (the composite's identities are format 10's).  Its content subject
; is its translated article's, and its authored-source identity is the one
; replay derives from the carried source (schema 0: none, as before).
(defthm fn-f9r-composite-identities-are-format-10s
  (let ((new (fn-f9r-composite e)))
    (and (equal (fn-stxa-content-subject new)
                (fn-record-string-octets
                 (fn-record-content-subject
                  (fn-f9r-article (fn-f9r-composite-article e)))))
         (equal (fn-stxa-authored-id new)
                (if (equal (fn-stxa-authored-source e) :legacy)
                    (fn-stxa-authored-id e)
                  (fn-hsig-authored-source-id (fn-stxa-authored-source e))))))
  :hints (("Goal" :in-theory (e/d (fn-f9r-composite fn-f9r-authored-id)
                                  (fn-f9r-article fn-f9r-composite-article
                                   fn-hsig-authored-source-id)))))

;; -----------------------------------------------------------------------------
;; Topic anchors and admissions

; OCTETS are a topic anchor or admission (fnto, kind 0 or 1), whatever
; identities they name: format 10's decoder refuses an algorithm-1 source
; identity, so these are recognised by their envelope.
(defun fn-f9r-signed-topic-octetsp (octets)
  (declare (xargs :guard t))
  (let ((decoded (fn-stmt-decode-items *fn-th-topic-max-items* octets)))
    (and (fn-stmt-okp decoded)
         (let ((items (fn-stmt-value decoded)))
           (and (consp items) (consp (cdr items)) (consp (cddr items))
                (equal (car items) (cons :bytes *fn-th-topic-magic*))
                (member-equal (caddr items) (list (cons :uint 0) (cons :uint 1))))))))

; The sequence a format-9 topic anchor or admission names (its envelope's
; fourth item), or nil: `store import' names an archive record by the
; sequence ACL2 reads off it (host/store-host.lisp
; fn-store-archive-record-sequence), and format 10 cannot decode these.
(defun fn-f9r-signed-topic-sequence (octets)
  (declare (xargs :guard t))
  (if (fn-f9r-signed-topic-octetsp octets)
      (let ((items (fn-stmt-value (fn-stmt-decode-items *fn-th-topic-max-items* octets))))
        (if (and (consp (cdddr items)) (consp (cadddr items))
                 (equal (car (cadddr items)) :uint)
                 (natp (cdr (cadddr items))))
            (cdr (cadddr items))
          nil))
    nil))

;; -----------------------------------------------------------------------------
;; One record

; The map from each translated article's format-9 identity texts to its
; format-10 ones (a fast alist; retention events read it).
(defun fn-f9r-map-article (old new map)
  (declare (xargs :guard t))
  (hons-acons (fn-record-obligation-id old) (fn-record-obligation-id new)
              (hons-acons (fn-record-content-subject old)
                          (fn-record-content-subject new)
                          map)))

; The kinds carried verbatim.
(defun fn-f9r-verbatim-kindp (ev)
  (declare (xargs :guard t))
  (or (fn-stxe-p ev) (fn-stxk-p ev) (fn-cpe-eventp ev)
      (fn-th-local-admin-eventp ev)))

; The translation of one archive record's OCTETS: (:ok OCTETS MAP) or
; (:refused REASON).
(defun fn-f9r-step (octets map)
  (declare (xargs :guard t))
  ; The event decoder is not guard-verified (books/store-events.lisp: its
  ; item accessors take any index); ec-call runs its executable counterpart,
  ; so this loop and everything else here is.
  (let ((decoded (ec-call (fn-store-event-decode-exact octets))))
    (if (not (and (consp decoded) (equal (car decoded) :ok) (consp (cdr decoded))))
        (list :refused (if (fn-f9r-signed-topic-octetsp octets)
                           :signed-format-9-identity
                         :record-codec))
      (let ((ev (cadr decoded)))
        (cond ((fn-record-p ev)
               (let ((new (fn-f9r-article ev)))
                 (list :ok (fn-record-encode new) (fn-f9r-map-article ev new map))))
              ((fn-store-retention-event-p ev)
               (let ((new (fn-f9r-retention ev map)))
                 (if (equal new :unknown-identity)
                     (list :refused :unknown-identity)
                   (list :ok (fn-store-event-encode new) map))))
              ((fn-stxa-p ev)
               (let ((old (fn-f9r-composite-article ev))
                     (new (fn-f9r-composite ev)))
                 (if (and old (fn-stxa-bindsp new))
                     (list :ok (fn-stxa-encode new)
                           (fn-f9r-map-article old (fn-f9r-article old) map))
                   (list :refused :composite-binding))))
              ((fn-f9r-verbatim-kindp ev) (list :ok octets map))
              ((fn-th-topic-eventp ev) (list :refused :signed-format-9-identity))
              (t (list :refused :untranslatable-kind)))))))

; KEYSTONE (verdicts, keyring snapshots, consumer events and the topic
; install carry verbatim).  A record of a kind that names no content identity
; imports as exactly its archive octets.
(defthm fn-f9r-step-carries-identity-free-kinds-verbatim
  (let ((decoded (fn-store-event-decode-exact octets)))
    (implies (and (equal (car decoded) :ok) (consp (cdr decoded))
                  (not (fn-record-p (cadr decoded)))
                  (not (fn-store-retention-event-p (cadr decoded)))
                  (not (fn-stxa-p (cadr decoded)))
                  (fn-f9r-verbatim-kindp (cadr decoded)))
             (equal (fn-f9r-step octets map) (list :ok octets map))))
  :hints (("Goal" :in-theory (e/d (fn-f9r-step)
                                  (fn-store-event-decode-exact fn-f9r-verbatim-kindp
                                   fn-record-p fn-store-retention-event-p fn-stxa-p)))))

; KEYSTONE (a composite imports bound).  A composite the translation admits
; binds its article and its verdict (fn-stxa-bindsp, the check replay runs),
; and it is the translated composite: the refusal :composite-binding is the
; only other outcome.
(defthm fn-f9r-step-of-a-composite
  (let ((decoded (fn-store-event-decode-exact octets)))
    (implies (and (equal (car decoded) :ok) (consp (cdr decoded))
                  (not (fn-record-p (cadr decoded)))
                  (not (fn-store-retention-event-p (cadr decoded)))
                  (fn-stxa-p (cadr decoded)))
             (let ((step (fn-f9r-step octets map)))
               (or (equal step (list :refused :composite-binding))
                   (and (equal (car step) :ok)
                        (equal (cadr step) (fn-stxa-encode (fn-f9r-composite (cadr decoded))))
                        (fn-stxa-bindsp (fn-f9r-composite (cadr decoded))))))))
  :hints (("Goal" :in-theory (e/d (fn-f9r-step)
                                  (fn-store-event-decode-exact fn-f9r-composite
                                   fn-f9r-composite-article fn-stxa-bindsp
                                   fn-f9r-map-article fn-f9r-article
                                   fn-record-p fn-store-retention-event-p fn-stxa-p
                                   fn-stxa-encode)))))

;; -----------------------------------------------------------------------------
;; The archive's records

; RECORDS: ((SEQUENCE . OCTETS) ...), in order; ACC the translated ones,
; newest first.  A loop, not a list recursion: an archive has as many records
; as the store (1M records at the largest fixture).
(defun fn-f9r-loop (records map acc)
  (declare (xargs :guard t))
  (if (atom records)
      (prog2$ (fast-alist-free map) (cons :ok acc))
    (let* ((seq (if (consp (car records)) (caar records) nil))
           (octets (if (consp (car records)) (cdar records) nil))
           (step (fn-f9r-step octets map)))
      (if (equal (car step) :ok)
          (fn-f9r-loop (cdr records) (caddr step)
                       (cons (cons seq (cadr step)) acc))
        (prog2$ (fast-alist-free map)
                (list :refused (cadr step) seq))))))

; The import's records for a format-9 archive's RECORDS: ((SEQUENCE .
; OCTETS) ...) translated, in order, or (:refused REASON SEQUENCE).
(defun fn-f9r-records (records)
  (declare (xargs :guard t))
  (let ((r (fn-f9r-loop records nil nil)))
    (if (equal (car r) :ok) (rev (cdr r)) r)))

; The translation keeps the archive's sequences, in order.
(defthm fn-f9r-loop-keeps-sequences
  (let ((r (fn-f9r-loop records map acc)))
    (implies (equal (car r) :ok)
             (equal (strip-cars (cdr r))
                    (append (rev (strip-cars records)) (strip-cars acc)))))
  :hints (("Goal" :induct (fn-f9r-loop records map acc)
           :in-theory (e/d (fn-f9r-loop)
                           (fn-f9r-step fast-alist-free
                            fn-f9r-step-carries-identity-free-kinds-verbatim
                            fn-f9r-step-of-a-composite)))))
