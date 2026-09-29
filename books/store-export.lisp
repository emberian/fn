; fn: `store export' and `store import': backup and restore of a store of
; this format (D34: one format, fresh deploys, no migrations; design
; 2026-09-26 consolidation section 6, P-D's default).
;
; An archive is a store's data as files, for a store of this build's format
; only (an archive whose profile frame this format does not decode is
; refused `:profile :store-format', never translated): a directory holding
; the store's profile frame (config.json's exact octets), its allocation
; frontier frame (allocation-frontier.json's exact octets, so
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

; -----------------------------------------------------------------------------
; Names and entries

; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-sxp-chars-octets-loop (chars acc)
  (declare (xargs :guard t))
  (if (consp chars)
      (fn-sxp-chars-octets-loop (cdr chars)
       (cons (if (characterp (car chars)) (char-code (car chars)) 0) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-sxp-chars-octets (chars)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp chars)
           (cons (if (characterp (car chars)) (char-code (car chars)) 0)
                 (fn-sxp-chars-octets (cdr chars)))
         nil)
       :exec (fn-sxp-chars-octets-loop chars nil)))

(defthm fn-sxp-chars-octets-loop-is-rev-onto
  (equal (fn-sxp-chars-octets-loop chars acc)
         (fn-ag-rev-onto acc (fn-sxp-chars-octets chars)))
  :hints (("Goal" :induct (fn-sxp-chars-octets-loop chars acc)
                  :in-theory (union-theories
                              '(fn-sxp-chars-octets-loop fn-sxp-chars-octets fn-ag-rev-onto not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-sxp-chars-octets
  :hints (("Goal" :in-theory (union-theories
                              '(fn-sxp-chars-octets fn-ag-rev-onto fn-sxp-chars-octets-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

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
  (declare (xargs :guard t))
  (append *fn-sxp-records-prefix*
          (fn-sxp-text-octets (fn-bs-txn-name-impl (nfix sequence)))))

(defun fn-sxp-config-name (name)
  (declare (xargs :guard t))
  (append *fn-sxp-config-prefix* (fn-sxp-text-octets name)))

; CONFIGS: ((NAME . OCTETS) ...), the configuration records as the open's
; observation names them.  RECORDS: ((SEQUENCE . OCTETS) ...), each record's
; sequence as ACL2's decoder reads it (host/store-host.lisp
; `fn-store-record-sequence').
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-sxp-config-entries-loop (configs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp configs)
      (fn-sxp-config-entries-loop (cdr configs)
                                  (cons (cons (fn-sxp-config-name (if (consp (car configs))
                                                                      (caar configs)
                                                                    nil))
                                              (if (consp (car configs))
                                                  (cdar configs)
                                                nil))
                                        acc))
    (revappend acc nil)))

(defun fn-sxp-config-entries (configs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp configs)
           (cons (cons (fn-sxp-config-name (if (consp (car configs)) (caar configs) nil))
                       (if (consp (car configs)) (cdar configs) nil))
                 (fn-sxp-config-entries (cdr configs)))
         nil)
       :exec (fn-sxp-config-entries-loop configs nil)))

(local
 (defthm fn-sxp-config-entries-loop-is-revappend
   (equal (fn-sxp-config-entries-loop configs acc)
          (revappend acc (fn-sxp-config-entries configs)))
   :hints (("Goal" :induct (fn-sxp-config-entries-loop configs acc)
                   :in-theory (union-theories '(fn-sxp-config-entries-loop fn-sxp-config-entries revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-sxp-config-entries-loop)

(verify-guards fn-sxp-config-entries
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-sxp-config-entries)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-sxp-config-entries-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-sxp-record-entries-loop (records acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp records)
      (fn-sxp-record-entries-loop (cdr records)
                                  (cons (cons (fn-sxp-record-name (if (consp (car records))
                                                                      (caar records)
                                                                    0))
                                              (if (consp (car records))
                                                  (cdar records)
                                                nil))
                                        acc))
    (revappend acc nil)))

(defun fn-sxp-record-entries (records)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp records)
           (cons (cons (fn-sxp-record-name (if (consp (car records)) (caar records) 0))
                       (if (consp (car records)) (cdar records) nil))
                 (fn-sxp-record-entries (cdr records)))
         nil)
       :exec (fn-sxp-record-entries-loop records nil)))

(local
 (defthm fn-sxp-record-entries-loop-is-revappend
   (equal (fn-sxp-record-entries-loop records acc)
          (revappend acc (fn-sxp-record-entries records)))
   :hints (("Goal" :induct (fn-sxp-record-entries-loop records acc)
                   :in-theory (union-theories '(fn-sxp-record-entries-loop fn-sxp-record-entries revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-sxp-record-entries-loop)

(verify-guards fn-sxp-record-entries
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-sxp-record-entries)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-sxp-record-entries-loop-is-revappend (acc nil))))))


(defun fn-sxp-entries (profile frontier configs records)
  (declare (xargs :guard t))
  (list* (cons *fn-sxp-profile-name* profile)
         (cons *fn-sxp-frontier-name* frontier)
         (append (fn-sxp-config-entries configs)
                 (fn-sxp-record-entries records))))
; -----------------------------------------------------------------------------
; The MANIFEST

(defun fn-sxp-octets-or-nil (octets)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp octets) octets nil))

; An entry's MANIFEST line: the lowercase hex of its digest under the seam
; (`fn-digest'), two spaces, its name, LF.
(defun fn-sxp-manifest-line (entry)
  (declare (xargs :guard t))
  (let ((name (if (consp entry) (car entry) nil))
        (octets (if (consp entry) (cdr entry) nil)))
    (append (fn-id-hex-octets (fn-digest (fn-sxp-octets-or-nil octets)))
            (list 32 32)
            (fn-sxp-octets-or-nil name)
            (list 10))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-sxp-manifest-loop (entries acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp entries)
      (fn-sxp-manifest-loop (cdr entries)
                                  (fn-ag-rev-onto (fn-sxp-manifest-line
                                                                              (car entries))
                                                  acc))
    (revappend acc nil)))

; What `store export' renders (host/native/io.lisp) and the import checks.
(defun fn-sxp-manifest (entries)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp entries)
           (append (fn-sxp-manifest-line (car entries))
                   (fn-sxp-manifest (cdr entries)))
         nil)
       :exec (fn-sxp-manifest-loop entries nil)))

(local
 (defthm fn-sxp-manifest-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-sxp-manifest-loop-is-revappend
   (equal (fn-sxp-manifest-loop entries acc)
          (revappend acc (fn-sxp-manifest entries)))
   :hints (("Goal" :induct (fn-sxp-manifest-loop entries acc)
                   :in-theory (union-theories '(fn-sxp-manifest-loop fn-sxp-manifest revappend car-cons cdr-cons fn-sxp-manifest-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))

(verify-guards fn-sxp-manifest-loop)

(verify-guards fn-sxp-manifest
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-sxp-manifest)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-sxp-manifest-loop-is-revappend (acc nil))))))


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

(defun fn-sxp-manifest-mismatch (entries manifest)
  (declare (xargs :guard t :measure (len entries)))
  (if (consp entries)
      (let ((line (fn-sxp-manifest-line (car entries))))
        (if (fn-sxp-prefixp line manifest)
            (fn-sxp-manifest-mismatch (cdr entries)
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

; -----------------------------------------------------------------------------
; The import's plan

; What `store import' does with an archive it read: MANIFEST, the profile
; frame, the FRONTIER frame, CONFIGS and RECORDS as the host read them from the archive's files
; (in the order of their names), and REQUEST the operator's field overrides
; over the archive's profile (base :current).
;   (:import VALUES FRONTIER CONFIGS RECORDS)
;                                      a new store under VALUES holding
;                                      FRONTIER, CONFIGS and RECORDS
;   (:refused :manifest-mismatch NAME) an entry the MANIFEST does not carry
;   (:refused :record-out-of-sequence N)
;   (:refused :config-out-of-sequence)
;   (:refused :profile REASON)         a profile the codec cannot represent
;                                      (REASON the relation it fails by name),
;                                      or :store-format for a profile frame
;                                      this format does not decode (an
;                                      archive of another format: none is
;                                      read, D34)
(defun fn-sxp-import-plan (manifest profile frontier configs records request)
  (declare (xargs :guard t))
  (let ((mismatch (fn-sxp-manifest-mismatch
                   (fn-sxp-entries profile frontier configs records) manifest))
        (saved (fn-bs-config-decode profile)))
    (cond (mismatch (list :refused :manifest-mismatch mismatch))
          ((fn-sxp-out-of-sequence records nil)
           (list :refused :record-out-of-sequence
                 (fn-sxp-out-of-sequence records nil)))
          ((not (fn-sxp-config-names-increasingp configs nil))
           (list :refused :config-out-of-sequence))
          ((null saved) (list :refused :profile :store-format))
          ((not (fn-bs-profile-requestp request))
           (list :refused :profile :request))
          ((null (cadr request))
           (list :import saved frontier configs records))
          (t (let ((values (fn-bs-profile-resolve request saved)))
               (if (and (consp values) (equal (car values) :invalid))
                   (list :refused :profile
                         (if (consp (cdr values)) (cadr values) :request))
                 (list :import values frontier configs records)))))))

; -----------------------------------------------------------------------------
; KEYSTONE (PRF-205): the import of an export replays the same history.
;
; For a store whose profile is a valid profile of this format
; (fn-bs-profile-logp reads the profile only when it is valid: every store
; the open admits) and
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
   (equal (fn-sxp-manifest-mismatch entries (fn-sxp-manifest entries))
          nil)
   :hints (("Goal" :in-theory (disable fn-sxp-manifest-line)))))

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
           :in-theory (e/d (fn-sxp-increasingp)
                           (fn-sxp-logp-is-valid fn-bs-config-decode-of-encode
                            fn-sxp-manifest fn-sxp-entries
                            fn-bs-config-encode fn-bs-config-decode
                            fn-bs-profile-validp fn-bs-profile-logp)))))
