; fn: `store export' and `store import' (D34, fresh deploys; design
; 2026-09-26 consolidation section 6, P-D's default).
;
; A deploy is: stop, remove, install the release, `init' or `store import',
; start.  The data that must survive a reinstall travels as an archive: a
; directory holding the store's profile frame (config.json's exact octets),
; its allocation frontier frame (allocation-frontier.json's exact octets, so
; the burned reservations stay burned), each configuration record's exact
; file octets, and each committed record's
; exact octets (the codec seam's bytes, as the open reads them: the selected
; pack's records and then the suffix files, every kind), in sequence order,
; with a MANIFEST of digest lines ACL2 renders (the seam's digest: BLAKE3).  The store identity and the
; consumer state are records, so they travel with them (P-D).  Feed journals
; and BP spools do not (a reinstall re-peers).
;
; ACL2 decides the archive: the entry names (`fn-sxp-entries': "profile",
; "config/NAME", "records/<the transaction name of the sequence>"), the
; MANIFEST's octets (`fn-sxp-manifest': per entry the lowercase hex of the
; digest, two spaces, the name, LF -- `b3sum -c' reads it), and the
; import's plan (`fn-sxp-import-plan'): the refusals by name, or the profile
; the new store is born under with the configuration records and the records
; to replay, in order.  The host (host/native/io.lisp
; `fnn-command-store-export', `fnn-command-store-import') reads and writes
; files and calls these; it computes nothing they compute.
;
; The import builds the new store beside its path (ROOT.import-XXXX): the
; plan's profile, frontier and configuration records written as `init'
; writes its files, each record framed (ACL2's frame, the one `fnn-publish'
; writes) at its transaction name, then the ordinary open (`fnn-recover':
; full replay through `fn-store-sn-recover', the committed-history marker's
; catch-up) admits it or refuses it by name, and only an admitted store is
; renamed onto ROOT.  So no new decision exists: the replay that admits the
; imported history is the one every open runs, and the relation the Store's
; open establishes is established by the ordinary open entry.  (Not the
; publish program per record: `fnn-publish' commits a transaction the
; owner prepared in this process, and an archived record is not prepared,
; it is replayed.  An interrupted import leaves only ROOT.import-XXXX,
; never a store at ROOT.)
;
; What the digest is: the crypto seam's `fn-digest', BLAKE3 under
; books/crypto-attach in the image.  In this logic it is constrained only by
; its shape, so the MANIFEST equality proves nothing about integrity against
; an adversary (AGENTS.md: an abstract model proves nothing about real
; hashes); it is a transport check.  The semantic check of an imported
; history is the replay at the import's open.
(in-package "ACL2")
(include-book "store-profile-facts")
(include-book "crypto-seam")
(include-book "identity")
(include-book "store-format-9")
(include-book "store-format-9-records")

; -----------------------------------------------------------------------------
; Names and entries

(defun fn-sxp-chars-octets (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (cons (if (characterp (car chars)) (char-code (car chars)) 0)
            (fn-sxp-chars-octets (cdr chars)))
    nil))

(defun fn-sxp-text-octets (text)
  (declare (xargs :guard t))
  (if (stringp text) (fn-sxp-chars-octets (coerce text 'list)) nil))

(defconst *fn-sxp-profile-name* '(112 114 111 102 105 108 101))      ; profile
(defconst *fn-sxp-frontier-name* '(102 114 111 110 116 105 101 114)) ; frontier
(defconst *fn-sxp-config-prefix* '(99 111 110 102 105 103 47))       ; config/
(defconst *fn-sxp-records-prefix* '(114 101 99 111 114 100 115 47))  ; records/

; A record's entry name: records/ and the store's own transaction name of its
; sequence (books/byte-store-txn-name.lisp).
(defun fn-sxp-record-name (sequence)
  (declare (xargs :guard t :verify-guards nil))
  (append *fn-sxp-records-prefix*
          (fn-sxp-text-octets (fn-bs-txn-name-impl (nfix sequence)))))

(defun fn-sxp-config-name (name)
  (declare (xargs :guard t))
  (append *fn-sxp-config-prefix* (fn-sxp-text-octets name)))

; CONFIGS: ((NAME . OCTETS) ...), the configuration records as the open's
; observation names them.  RECORDS: ((SEQUENCE . OCTETS) ...), each record's
; sequence as ACL2's decoder reads it (host/store-host.lisp
; `fn-store-record-sequence').
(defun fn-sxp-config-entries (configs)
  (declare (xargs :guard t))
  (if (consp configs)
      (cons (cons (fn-sxp-config-name (if (consp (car configs)) (caar configs) nil))
                  (if (consp (car configs)) (cdar configs) nil))
            (fn-sxp-config-entries (cdr configs)))
    nil))

(defun fn-sxp-record-entries (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (cons (cons (fn-sxp-record-name (if (consp (car records)) (caar records) 0))
                  (if (consp (car records)) (cdar records) nil))
            (fn-sxp-record-entries (cdr records)))
    nil))

(defun fn-sxp-entries (profile frontier configs records)
  (declare (xargs :guard t :verify-guards nil))
  (list* (cons *fn-sxp-profile-name* profile)
         (cons *fn-sxp-frontier-name* frontier)
         (append (fn-sxp-config-entries configs)
                 (fn-sxp-record-entries records))))
; -----------------------------------------------------------------------------
; The archive's format (D34: one store format; D38 as proposed: the import
; reads the previous format's archive).
;
; An archive is format 10 when its profile frame opens under this format's
; digest and decodes (`fn-bs-config-decode'), and format 9 when it opens
; under the SHA-256 trailer format 9 sealed with and names fn-store-9
; (books/store-format-9.lisp).  The MANIFEST of a format-9 archive is its
; SHA-256 lines (the digest format 9's image rendered them with), so the
; import checks each entry under the archive's own digest, and writes the
; new store under this format's.

(defun fn-sxp-archive-format-9p (profile)
  (declare (xargs :guard t))
  (and (not (fn-bs-config-decode profile))
       (equal (fn-f9-saved-format-word profile) *fn-bs-meta-format-9*)))

; The profile the import reads from an archive's profile frame: this
; format's, or the format-10 translation of a format-9 one
; (`fn-f9-config-decode'); NIL when it is neither.
(defun fn-sxp-config-decode-archive (profile)
  (declare (xargs :guard t))
  (if (fn-sxp-archive-format-9p profile)
      (fn-f9-config-decode profile)
    (fn-bs-config-decode profile)))

(defthm fn-sxp-config-decode-archive-is-valid
  (implies (fn-sxp-config-decode-archive profile)
           (fn-bs-profile-validp (fn-sxp-config-decode-archive profile)))
  :hints (("Goal" :use ((:instance fn-f9-config-decode-is-valid (octets profile)))
           :in-theory (e/d (fn-bs-config-decode)
                           (fn-f9-config-decode-is-valid fn-bs-profile-validp
                            fn-f9-config-decode fn-frame-open
                            fn-frame-fields-parse fn-bs-meta-frame-okp)))))

; The profile the import writes: this format's word over the fields (every
; profile the import reads is already format 10; kept so the plan names the
; word it writes).
(defun fn-sxp-log-profile (values)
  (declare (xargs :guard t))
  (if (consp values) (cons *fn-bs-meta-format-10* (cdr values)) values))

; -----------------------------------------------------------------------------
; The MANIFEST

(defun fn-sxp-octets-or-nil (octets)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp octets) octets nil))

; An entry's digest under the archive's format: this format's seam
; (`fn-digest'), or format 9's SHA-256.
(defun fn-sxp-entry-digest (f9p octets)
  (declare (xargs :guard t))
  (if f9p
      (fn-f9-trailer (fn-sxp-octets-or-nil octets))
    (fn-digest (fn-sxp-octets-or-nil octets))))

(defun fn-sxp-manifest-line-under (f9p entry)
  (declare (xargs :guard t))
  (let ((name (if (consp entry) (car entry) nil))
        (octets (if (consp entry) (cdr entry) nil)))
    (append (fn-id-hex-octets (fn-sxp-entry-digest f9p octets))
            (list 32 32)
            (fn-sxp-octets-or-nil name)
            (list 10))))

(defun fn-sxp-manifest-under (f9p entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (append (fn-sxp-manifest-line-under f9p (car entries))
              (fn-sxp-manifest-under f9p (cdr entries)))
    nil))

; What `store export' renders (host/native/io.lisp): this format's lines.
(defun fn-sxp-manifest (entries)
  (declare (xargs :guard t))
  (fn-sxp-manifest-under nil entries))

; The name of the first entry whose line the MANIFEST octets do not carry at
; its place, or the MANIFEST's own name when every line matched and octets
; remain; NIL when the MANIFEST is exactly the entries'.
(defun fn-sxp-prefixp (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp ys) (equal (car xs) (car ys)) (fn-sxp-prefixp (cdr xs) (cdr ys)))
    t))

(defconst *fn-sxp-manifest-name* '(77 65 78 73 70 69 83 84)) ; MANIFEST

(defun fn-sxp-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) xs (fn-sxp-drop (1- n) (if (consp xs) (cdr xs) nil))))

(defun fn-sxp-manifest-mismatch (f9p entries manifest)
  (declare (xargs :guard t :measure (len entries)))
  (if (consp entries)
      (let ((line (fn-sxp-manifest-line-under f9p (car entries))))
        (if (fn-sxp-prefixp line manifest)
            (fn-sxp-manifest-mismatch f9p (cdr entries)
                                      (fn-sxp-drop (len line) manifest))
          (if (consp (car entries)) (caar entries) nil)))
    (if (consp manifest) *fn-sxp-manifest-name* nil)))

; -----------------------------------------------------------------------------
; Sequence

; RECORDS in strictly increasing sequence: the first sequence that is not, or
; NIL.  (Gaps are the burned reservations of the exported store; the import
; reproduces them by advancing the frontier.)
(defun fn-sxp-out-of-sequence (records previous)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((seq (if (consp (car records)) (caar records) nil)))
        (if (and (natp seq) (or (null previous) (and (natp previous) (< previous seq))))
            (fn-sxp-out-of-sequence (cdr records) seq)
          (if (natp seq) seq 0)))
    nil))

(defun fn-sxp-increasingp (records)
  (declare (xargs :guard t))
  (null (fn-sxp-out-of-sequence records nil)))

(defun fn-sxp-config-names-increasingp (configs previous)
  (declare (xargs :guard t))
  (if (consp configs)
      (let ((name (if (consp (car configs)) (caar configs) nil)))
        (and (stringp name)
             (or (null previous) (and (stringp previous) (string< previous name) t))
             (fn-sxp-config-names-increasingp (cdr configs) name)))
    t))

;; -----------------------------------------------------------------------------
;; The archive's profile is fn-sxp-config-decode-archive above: this format's,
;; or the format-10 translation of a format-9 one.  The reader of the layout
;; before batch AS (thirteen fields, format 8; compression-extents-2's proposed
;; D38) is retired with format 10: the import reads the previous release's
;; export only (D34); a format-8 archive imports through a format-9 release
;; first (batch AY, compression-extents-2 x format-bump-10).

; The current layout reads as the open's decoder reads it.
(defthm fn-sxp-config-decode-archive-of-a-current-frame
  (implies (fn-bs-config-decode octets)
           (equal (fn-sxp-config-decode-archive octets) (fn-bs-config-decode octets)))
  :hints (("Goal" :in-theory (e/d (fn-sxp-config-decode-archive fn-sxp-archive-format-9p)
                                  (fn-bs-config-decode fn-bs-profile-validp)))))

; -----------------------------------------------------------------------------
; The import's plan

; Why an archive's profile does not import, by name: a format-9 profile's
; translation refusal (books/store-format-9.lisp fn-f9-profile-refusal), or
; `:store-format' for a frame of no format this image reads.
(defun fn-sxp-profile-refusal (profile)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sxp-archive-format-9p profile)
      (or (fn-f9-profile-refusal (fn-f9-profile-values profile)) :store-format)
    :store-format))

; What `store import' does with an archive it read: MANIFEST, the profile
; frame, the FRONTIER frame, CONFIGS and RECORDS as the host read them from the archive's files
; (in the order of their names), and REQUEST the operator's field overrides
; over the archive's profile (base :current).
;   (:import VALUES FRONTIER CONFIGS RECORDS)
;                                      a new store under VALUES holding
;                                      FRONTIER, CONFIGS and RECORDS
;   (:refused :manifest-mismatch NAME) an entry the MANIFEST does not carry
;                                      under the archive's digest
;   (:refused :record-translation REASON SEQUENCE)
;                                      a format-9 record the translation
;                                      refuses (books/store-format-9-records)
;   (:refused :record-out-of-sequence N)
;   (:refused :config-out-of-sequence)
;   (:refused :profile REASON)         a profile the codec cannot represent
;                                      (REASON the relation it fails by name,
;                                      :store-format for another format)
(defun fn-sxp-import-plan (manifest profile frontier configs records request)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((f9p (fn-sxp-archive-format-9p profile))
         (mismatch (fn-sxp-manifest-mismatch
                    f9p (fn-sxp-entries profile frontier configs records) manifest))
         ; The archive's profile: this format's, or a format-9 one translated
         ; (fn-sxp-config-decode-archive).
         (saved (fn-sxp-config-decode-archive profile))
         ; A format-9 archive's records with their identities re-derived under
         ; this format's digest (books/store-format-9-records.lisp), after the
         ; MANIFEST was checked over the archive's own octets.
         (records (if f9p (fn-f9r-records records) records)))
    (cond (mismatch (list :refused :manifest-mismatch mismatch))
          ((and f9p (consp records) (equal (car records) :refused))
           (list :refused :record-translation
                 (if (consp (cdr records)) (cadr records) nil)
                 (if (consp (cdr records)) (caddr records) nil)))
          ((fn-sxp-out-of-sequence records nil)
           (list :refused :record-out-of-sequence
                 (fn-sxp-out-of-sequence records nil)))
          ((not (fn-sxp-config-names-increasingp configs nil))
           (list :refused :config-out-of-sequence))
          ((null saved) (list :refused :profile (fn-sxp-profile-refusal profile)))
          ((not (fn-bs-profile-requestp request))
           (list :refused :profile :request))
          ((null (cadr request))
           (list :import (fn-sxp-log-profile saved) frontier configs records))
          (t (let ((values (fn-bs-profile-resolve request saved)))
               (if (and (consp values) (equal (car values) :invalid))
                   (list :refused :profile
                         (if (consp (cdr values)) (cadr values) :request))
                 (list :import (fn-sxp-log-profile values)
                       frontier configs records)))))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-205): the import of an export replays the same history.
;
; For a store whose profile is a valid format-10 profile (fn-bs-profile-logp
; reads the profile only when it is valid: every store the open admits) and
; whose records are in strictly increasing sequence with configuration names
; in order (what the open's observation returns), the plan the import takes
; over the archive the export wrote -- the same entries, and the MANIFEST
; ACL2 rendered for them -- with no field raised is: born under the same
; profile, with the same configuration records, replaying exactly the same
; records in the same order.  The replay is the ordinary open over the log
; the import writes, so the imported store's committed records
; (fn-sf-records) are the exported ones, and every served fact that is a
; function of the replayed history (fn-store-sn-recover's arguments: the
; records and the configuration records) is equal.
(local
 (defthm fn-sxp-prefixp-of-append
   (fn-sxp-prefixp xs (append xs ys))))

(local
 (defthm fn-sxp-drop-len-append
   (equal (fn-sxp-drop (len xs) (append xs ys)) ys)))

(local
 (defthm fn-sxp-manifest-mismatch-of-manifest
   (equal (fn-sxp-manifest-mismatch f9p entries (fn-sxp-manifest-under f9p entries))
          nil)
   :hints (("Goal" :in-theory (disable fn-sxp-manifest-line-under)))))

(local
 (defthm fn-sxp-valid-profile-facts
   (implies (fn-bs-profile-validp values)
            (and (consp values)
                 (equal (car values) *fn-bs-meta-format-10*)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-profile-validp fn-bs-profile-invalid-reason
                                      fn-bs-meta-formatp)
                   :expand ((fn-bs-meta-nth 0 values)
                            (fn-frame-values-okp *fn-bs-meta-profile-spec* values))))))

(local
 (defthm fn-sxp-log-profile-of-valid
   (implies (fn-bs-profile-validp values)
            (equal (fn-sxp-log-profile values) values))
   :hints (("Goal" :use fn-sxp-valid-profile-facts
            :in-theory (disable fn-bs-profile-validp)))))

(local
 (defthm fn-sxp-logp-is-valid
   (implies (fn-bs-profile-logp values)
            (fn-bs-profile-validp values))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bs-profile-logp fn-bs-profile-of
                                 (:e fn-bs-meta-nth) (:e equal))
                               (theory 'minimal-theory))))))

(defthm fn-sxp-import-of-export-replays-the-same-history
  (implies (and (fn-bs-profile-logp values)
                (fn-sxp-increasingp records)
                (fn-sxp-config-names-increasingp configs nil))
           (equal (fn-sxp-import-plan
                   (fn-sxp-manifest
                    (fn-sxp-entries (fn-bs-config-encode values) frontier
                                    configs records))
                   (fn-bs-config-encode values) frontier configs records
                   '(:current nil))
                  (list :import values frontier configs records)))
  :hints (("Goal" :use (fn-sxp-logp-is-valid
                        (:instance fn-bs-config-decode-of-encode))
           :in-theory (e/d (fn-sxp-increasingp fn-sxp-config-decode-archive
                            fn-sxp-archive-format-9p)
                           (fn-sxp-logp-is-valid fn-bs-config-decode-of-encode
                            fn-sxp-manifest-under fn-sxp-entries
                            fn-bs-config-encode fn-bs-config-decode
                            fn-bs-profile-validp fn-bs-profile-logp
                            fn-f9-saved-format-word)))))

; KEYSTONE (D38's witness, format 9 -> 10: the migration across the
; reinstall).  For every format-9 profile that translates (no refusal by
; name, books/store-format-9.lisp fn-f9-profile-refusal) and records in
; strictly increasing sequence with configuration names in order, the plan
; the import takes over the archive the format-9 release exported -- its
; profile frame sealed under SHA-256 (fn-f9-config-frame) and its MANIFEST of
; SHA-256 lines -- with no field raised is: born under the format-10
; translation of that profile (every field but the two dropped ones), with
; the same configuration records, replaying exactly the same records in the
; same order, each re-derived under this format's digest
; (books/store-format-9-records.lisp fn-f9r-records: the translation keeps
; every field but the identities, which are the ones a format-10 node
; derives).
(local
 (defthm fn-sxp-f9-frame-is-not-decoded
   (implies (null (fn-f9-profile-refusal values9))
            (not (fn-bs-config-decode (fn-f9-config-frame values9))))
   :hints (("Goal" :use (fn-f9-saved-format-word-of-config-frame
                         (:instance fn-f9-format-9-frame-does-not-decode
                                    (octets (fn-f9-config-frame values9))))
            :in-theory (e/d (fn-f9-profile-refusal)
                            (fn-f9-saved-format-word-of-config-frame
                             fn-f9-format-9-frame-does-not-decode
                             fn-bs-config-decode fn-f9-config-frame
                             fn-f9-saved-format-word fn-bs-profile-invalid-reason))))))

(defthm fn-sxp-import-of-a-format-9-export
  (implies (and (null (fn-f9-profile-refusal values9))
                (not (equal (car (fn-f9r-records records)) :refused))
                (fn-sxp-increasingp (fn-f9r-records records))
                (fn-sxp-config-names-increasingp configs nil))
           (equal (fn-sxp-import-plan
                   (fn-sxp-manifest-under
                    t (fn-sxp-entries (fn-f9-config-frame values9) frontier
                                      configs records))
                   (fn-f9-config-frame values9) frontier configs records
                   '(:current nil))
                  (list :import (fn-f9-profile-of values9) frontier configs
                        (fn-f9r-records records))))
  :hints (("Goal" :use (fn-sxp-f9-frame-is-not-decoded
                        fn-f9-config-decode-of-a-format-9-frame
                        fn-f9-saved-format-word-of-config-frame
                        (:instance fn-sxp-log-profile-of-valid
                                   (values (fn-f9-profile-of values9))))
           :in-theory (e/d (fn-sxp-increasingp fn-sxp-config-decode-archive
                            fn-sxp-archive-format-9p fn-f9-profile-refusal)
                           (fn-sxp-f9-frame-is-not-decoded
                            fn-f9-config-decode-of-a-format-9-frame
                            fn-f9-saved-format-word-of-config-frame
                            fn-sxp-log-profile-of-valid
                            fn-sxp-manifest-under fn-sxp-entries fn-f9r-records
                            fn-f9-config-frame fn-f9-config-decode
                            fn-f9-saved-format-word fn-f9-profile-of
                            fn-bs-config-decode fn-bs-profile-validp
                            fn-bs-profile-invalid-reason fn-frame-values-okp)))))

(defthm fn-sxp-log-profile-is-a-valid-log-profile
  (implies (fn-bs-profile-validp values)
           (and (fn-bs-profile-validp (fn-sxp-log-profile values))
                (fn-bs-profile-logp (fn-sxp-log-profile values))
                (equal (cdr (fn-sxp-log-profile values)) (cdr values))))
  :hints (("Goal" :use (fn-sxp-log-profile-of-valid fn-sxp-valid-profile-facts)
           :in-theory (e/d (fn-bs-profile-logp fn-bs-profile-of)
                           (fn-sxp-log-profile-of-valid fn-bs-profile-validp
                            fn-sxp-log-profile)))))
