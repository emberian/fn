; fn: the store's GENESIS, position 0 of its record log (lane format-bump-10,
; store format 10; ember's decision of 2026-09-27: non-determinism is
; RECORDED -- seeds, nonces, salts, generated ids, clock readings enter the
; log as event content or configuration events -- with a genesis event at
; position 0 when the format bumps; secrets never enter the log; derived
; indexes are node-local).
;
; WHAT IT IS.  journal/000000.log, segment 0 of the log: exactly one FNLG
; frame (books/store-log.lisp *fn-lg-magic*, version 1) of KIND 3, whose
; payload is the zero chain *fn-lg-genesis* followed by the genesis record,
; the frame-field record (books/frame-fields.lisp)
;
;     magic "fn-g" (text), format word (text), node identity (blob, 32),
;     schema digest (blob, 32), profile digest (blob, 32), history salt
;     (u64 field, below 2^32), created-at (u64 field: the wall-clock
;     reading at `init' in DTN seconds since 2000-01-01, the unit of the
;     configuration stamps), image revision (text)
;
; and whose trailer (the frame's last 32 octets, `fn-frame-digest' of its
; protected prefix) is the chain value segment 1's first entry names as its
; predecessor.  So every record the log holds is chained to the genesis, and
; the genesis to nothing.  The file is written once, by `init' or `store
; import', published by a no-replace link like config.json, and never
; rewritten; segment 0 is not a segment index the rotation or the drop
; names (books/store-log-segments.lisp fn-lgs-segment-index is positive), so
; a checkpoint's drop never removes it.
;
; WHAT IS RECORDED AND WHY.  The node identity is 32 octets the host draws
; from the CSPRNG at `init' (a generated id: recorded, not secret).  The
; history salt is 32 bits from the CSPRNG: the offset basis of the history
; stobj's Message-ID hash (books/history-columns.lisp fn-hist-hash; the
; constant 0 before format 10), which keys only the node's derived index and
; no answer (PKT-774).  The created-at reading and the image revision (the
; source revision the creating image recorded, or "unknown") are provenance.
; The schema digest is `fn-digest' of this format's schema text
; (*fn-gen-schema-octets*); the profile digest is `fn-digest' of config.json's
; frame.  NOT recorded: the credential salts (host/native/admin.lisp
; fnn-csprng-octets "credential salt") and the node secret: account and key
; material, node-local, never in the log.
;
; WHO READS IT.  The open (`fn-gen-open', host/native/io.lisp
; fnn-recover-log through host/store-host.lisp fn-store-genesis-open): the
; format, the schema digest against this image's and the profile digest
; against the config.json the open decoded are checked, each refused by
; name; the trailer seeds the chain of segment 1.  The history salt is read
; at the owner's install (host/owner-host.lisp fn-hist-load).  Nothing else
; reads a genesis field (tests/test_native_replay_determinism.py: two stores
; holding the same records under different genesis records fold the same
; state digest).
(in-package "ACL2")
(include-book "store-log")
(include-book "byte-store-frame")
(include-book "crypto-seam")
(local (include-book "frame-invariants"))
(local (include-book "cbor-invariants"))
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The record

(defconst *fn-gen-kind* 3)
(defconst *fn-gen-magic* '(102 110 45 103))            ; fn-g
(defconst *fn-gen-spec*
  '(:text :text :blob :blob :blob :nat :nat :text))
(defconst *fn-gen-max-payload* 512)
(defconst *fn-gen-salt-modulus* 4294967296)

; The file name of segment 0 in journal/.
(defconst *fn-gen-file-name* "000000.log")
(defun fn-gen-file-name ()
  (declare (xargs :guard t))
  *fn-gen-file-name*)

(defun fn-gen-nth (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (if (consp x) (car x) nil)
    (fn-gen-nth (1- n) (if (consp x) (cdr x) nil))))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-gen-take-loop (n xs acc)
  (declare (xargs :guard (and (natp n) (true-listp acc)) :verify-guards nil))
  (if (zp n)
      (revappend acc nil)
    (fn-gen-take-loop (1- n)
                      (if (consp xs) (cdr xs) nil)
                      (cons (if (consp xs) (car xs) nil) acc))))

(defun fn-gen-take (n xs)
  (declare (xargs :verify-guards nil :guard (natp n)))
  (mbe :logic
       (if (zp n) nil
         (cons (if (consp xs) (car xs) nil)
               (fn-gen-take (1- n) (if (consp xs) (cdr xs) nil))))
       :exec (fn-gen-take-loop n xs nil)))

(local
 (defthm fn-gen-take-loop-is-revappend
   (equal (fn-gen-take-loop n xs acc)
          (revappend acc (fn-gen-take n xs)))
   :hints (("Goal" :induct (fn-gen-take-loop n xs acc)
                   :in-theory (union-theories '(fn-gen-take-loop fn-gen-take revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-gen-take-loop)

(verify-guards fn-gen-take
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-gen-take)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-gen-take-loop-is-revappend (acc nil))))))


(defun fn-gen-make (format node schema profile salt created revision)
  (declare (xargs :guard t))
  (list *fn-gen-magic* format node schema profile salt created revision))

(defun fn-gen-format (g) (declare (xargs :guard t)) (fn-gen-nth 1 g))
(defun fn-gen-node (g) (declare (xargs :guard t)) (fn-gen-nth 2 g))
(defun fn-gen-schema (g) (declare (xargs :guard t)) (fn-gen-nth 3 g))
(defun fn-gen-profile-digest (g) (declare (xargs :guard t)) (fn-gen-nth 4 g))
(defun fn-gen-salt (g) (declare (xargs :guard t)) (nfix (fn-gen-nth 5 g)))
(defun fn-gen-created (g) (declare (xargs :guard t)) (nfix (fn-gen-nth 6 g)))
(defun fn-gen-revision (g) (declare (xargs :guard t)) (fn-gen-nth 7 g))

(defun fn-gen-digest-fieldp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x) (equal (len x) 32)))

; A genesis record: the fields fit their codecs, the magic is fn-g, the
; three digests are 32 octets and the salt is 32 bits.
(defun fn-gen-p (g)
  (declare (xargs :guard t))
  (and (fn-frame-values-okp *fn-gen-spec* g)
       (equal (fn-gen-nth 0 g) *fn-gen-magic*)
       (fn-gen-digest-fieldp (fn-gen-node g))
       (fn-gen-digest-fieldp (fn-gen-schema g))
       (fn-gen-digest-fieldp (fn-gen-profile-digest g))
       (natp (fn-gen-nth 5 g))
       (< (fn-gen-nth 5 g) *fn-gen-salt-modulus*)
       (<= (+ *fn-frame-trailer-octets* (len (fn-frame-fields-octets *fn-gen-spec* g)))
           *fn-gen-max-payload*)))

(defun fn-gen-payload (g)
  (declare (xargs :guard (fn-gen-p g) :verify-guards nil))
  (append *fn-lg-genesis* (fn-frame-fields-octets *fn-gen-spec* g)))

; The file `init' writes: the kind-3 frame, unpadded (segment 0 is never
; appended to).
(defun fn-gen-frame (g)
  (declare (xargs :guard (fn-gen-p g) :verify-guards nil))
  (fn-frame-seal *fn-lg-magic* *fn-lg-version* *fn-gen-kind* (fn-gen-payload g)))

; The chain value segment 1 starts from.
(defun fn-gen-trailer (frame)
  (declare (xargs :guard t))
  (nthcdr (nfix (- (len frame) *fn-frame-trailer-octets*)) (true-list-fix frame)))

; -----------------------------------------------------------------------------
; The schema this image writes and reads.  A change to any structure format
; 10 persists (the profile's fields, the entry kinds, the record envelopes,
; the checkpoint schema, the identity algorithm, the digest) changes this
; text, and the open refuses a store of another schema by name.

(defconst *fn-gen-schema-octets*
  (coerce
   "fn-store-10;profile=max-transactions,max-history-octets,max-record-octets,max-article-octets,max-groups-per-article,max-group-name-octets,max-open-suffix,max-consumers,max-bp-rows,max-config-generations,max-credentials,max-policy-members,max-header-fields,max-header-lines,max-header-octets;log=FNLG/1:record=1,batch=2,genesis=3;genesis=fn-g/0;record=FNST;event=fn-r,fn-e;identity=v1;digest=fn-digest"
   'list))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-gen-schema-chars-octets-loop (chars acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp chars)
      (fn-gen-schema-chars-octets-loop (cdr chars)
                                       (cons (if (characterp (car chars))
                                                 (char-code (car chars))
                                               0)
                                             acc))
    (revappend acc nil)))

(defun fn-gen-schema-chars-octets (chars)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp chars)
           (cons (if (characterp (car chars)) (char-code (car chars)) 0)
                 (fn-gen-schema-chars-octets (cdr chars)))
         nil)
       :exec (fn-gen-schema-chars-octets-loop chars nil)))

(local
 (defthm fn-gen-schema-chars-octets-loop-is-revappend
   (equal (fn-gen-schema-chars-octets-loop chars acc)
          (revappend acc (fn-gen-schema-chars-octets chars)))
   :hints (("Goal" :induct (fn-gen-schema-chars-octets-loop chars acc)
                   :in-theory (union-theories '(fn-gen-schema-chars-octets-loop fn-gen-schema-chars-octets revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-gen-schema-chars-octets-loop)

(verify-guards fn-gen-schema-chars-octets
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-gen-schema-chars-octets)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-gen-schema-chars-octets-loop-is-revappend (acc nil))))))


; This image's schema digest.  A function, not a constant: a defconst never
; evaluates the digest's attachment.
(defun fn-gen-image-schema-digest ()
  (declare (xargs :guard t))
  (fn-digest (fn-gen-schema-chars-octets *fn-gen-schema-octets*)))

; The profile digest of the profile a store runs under: its config.json frame.
(defun fn-gen-profile-digest-of (profile)
  (declare (xargs :guard t :verify-guards nil))
  (fn-digest (fn-bs-config-encode profile)))

; -----------------------------------------------------------------------------
; What `init' and `store import' write

; The genesis record for the host's recorded readings: NODE (32 CSPRNG
; octets), SALT (4 CSPRNG octets, read here big-endian as the 32-bit salt), CREATED (the
; clock reading) and REVISION (the image's source revision as octets), under
; the profile PROFILE the store is born with.  NIL when a reading does not
; fit the record (a node identity that is not 32 octets, a revision that is
; not frame text): the host faults, the store is not made.
(defun fn-gen-salt-of (octets)
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp octets) (equal (len octets) 4))
      (fn-cbor-u32-from octets)
    :bad))

(defun fn-gen-record-for (node salt created revision profile)
  (declare (xargs :guard t :verify-guards nil))
  (let ((g (fn-gen-make *fn-bs-meta-format-10* node
                        (fn-gen-image-schema-digest)
                        (fn-gen-profile-digest-of profile)
                        (fn-gen-salt-of salt)
                        (nfix created)
                        revision)))
    (if (and (fn-bs-profile-validp profile) (fn-gen-p g)) g nil)))

; The file's octets for those readings, or NIL.
(defun fn-gen-octets-for (node salt created revision profile)
  (declare (xargs :guard t :verify-guards nil))
  (let ((g (fn-gen-record-for node salt created revision profile)))
    (if g (fn-gen-frame g) nil)))

; -----------------------------------------------------------------------------
; The open

; The genesis record a file holds, or a refusal:
;   (:genesis G TRAILER)          the file is a genesis frame of this format,
;                                 schema and profile; TRAILER seeds segment 1
;   (:refused :genesis-damaged)   no kind-3 FNLG frame from the zero chain
;                                 holding a genesis record (a torn or
;                                 corrupted file; an init that did not finish
;                                 has no file at all, the host's branch)
;   (:refused :genesis-format)    a genesis of another format word
;   (:refused :schema-digest)     a genesis of another schema
;   (:refused :profile-digest)    config.json is not the profile the store
;                                 was born with
(defun fn-gen-decode (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp octets))
      nil
    (let ((r (fn-frame-open octets *fn-gen-max-payload*)))
      (if (and (fn-frame-result-okp r)
               (equal (fn-frame-result-magic r) *fn-lg-magic*)
               (equal (fn-frame-result-version r) *fn-lg-version*)
               (equal (fn-frame-result-kind r) *fn-gen-kind*)
               (equal (fn-gen-take *fn-frame-trailer-octets* (fn-frame-result-payload r))
                      *fn-lg-genesis*))
          (let ((parsed (fn-frame-fields-parse
                         *fn-gen-spec*
                         (nthcdr *fn-frame-trailer-octets* (fn-frame-result-payload r)))))
            (if (and (fn-frame-parse-okp parsed)
                     (fn-gen-p (fn-frame-parse-value parsed)))
                (fn-frame-parse-value parsed)
              nil))
        nil))))

(defun fn-gen-open (octets profile)
  (declare (xargs :guard t :verify-guards nil))
  (let ((g (fn-gen-decode octets)))
    (cond ((null g) (list :refused :genesis-damaged))
          ((not (equal (fn-gen-format g) *fn-bs-meta-format-10*))
           (list :refused :genesis-format))
          ((not (equal (fn-gen-schema g) (fn-gen-image-schema-digest)))
           (list :refused :schema-digest))
          ((not (equal (fn-gen-profile-digest g) (fn-gen-profile-digest-of profile)))
           (list :refused :profile-digest))
          (t (list :genesis g (fn-gen-trailer octets))))))

(defun fn-gen-refusal-text (verdict)
  (declare (xargs :guard t))
  (cond ((equal verdict '(:refused :genesis-damaged))
         "open refused reason=genesis-damaged: journal/000000.log is not this store's genesis record")
        ((equal verdict '(:refused :genesis-format))
         "open refused reason=genesis-format: the genesis names another store format; export with the release that made the store, then import here")
        ((equal verdict '(:refused :schema-digest))
         "open refused reason=schema-digest: the store was made under another schema; export with the release that made it, then import here")
        ((equal verdict '(:refused :profile-digest))
         "open refused reason=profile-digest: config.json is not the profile this store was born with")
        (t nil)))

; -----------------------------------------------------------------------------
; The round trip

(local
 (defthm fn-gen-take-32-of-append-genesis
   (equal (fn-gen-take 32 (append *fn-lg-genesis* body)) *fn-lg-genesis*)))

(local
 (defthm fn-gen-nthcdr-32-of-append-genesis
   (equal (nthcdr 32 (append *fn-lg-genesis* body)) body)))

(defthm fn-gen-p-facts
  (implies (fn-gen-p g)
           (and (fn-frame-values-okp *fn-gen-spec* g)
                (<= (+ *fn-frame-trailer-octets* (len (fn-frame-fields-octets *fn-gen-spec* g)))
                    *fn-gen-max-payload*)))
  :rule-classes :forward-chaining)

(local
 (defthm fn-gen-payload-facts
   (implies (fn-gen-p g)
            (and (fn-cbor-octet-listp (fn-gen-payload g))
                 (<= (len (fn-gen-payload g)) *fn-gen-max-payload*)))
   :hints (("Goal" :use ((:instance fn-frame-fields-octets-are-octets
                                    (specs *fn-gen-spec*) (values g)))
            :in-theory (e/d (fn-gen-payload fn-cbor-octet-listp-append)
                            (fn-frame-fields-octets-are-octets fn-gen-p
                             fn-frame-fields-octets))))))

(local
 (defthm fn-gen-payload-parts
   (and (equal (fn-gen-take 32 (fn-gen-payload g)) *fn-lg-genesis*)
        (equal (nthcdr 32 (fn-gen-payload g))
               (fn-frame-fields-octets *fn-gen-spec* g)))
   :hints (("Goal" :in-theory (e/d (fn-gen-payload) (fn-frame-fields-octets))))))

(local
 (defthm fn-gen-seal-octet-listp
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (fn-cbor-octet-listp (fn-frame-seal magic version kind payload)))
   :hints (("Goal"
            :use ((:instance fn-frame-digestp-of-fn-frame-digest
                             (octets (fn-frame-protected magic version kind payload)))
                  (:instance fn-cbor-u32-bytes-are-octets (n (len payload))))
            :in-theory (e/d (fn-frame-seal fn-frame-encode fn-frame-protected
                             fn-frame-header fn-frame-inputp fn-frame-magicp
                             fn-frame-digestp fn-cbor-octet-listp-append)
                            (fn-frame-digestp-of-fn-frame-digest
                             fn-cbor-u32-bytes-are-octets))))))

(defthm fn-gen-decode-of-frame
  (implies (fn-gen-p g)
           (equal (fn-gen-decode (fn-gen-frame g)) g))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-open-of-seal
                            (magic *fn-lg-magic*) (version *fn-lg-version*)
                            (kind *fn-gen-kind*) (payload (fn-gen-payload g))
                            (max-payload *fn-gen-max-payload*))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-gen-spec*) (values g))
                 fn-gen-payload-facts
                 (:instance fn-gen-seal-octet-listp
                            (magic *fn-lg-magic*) (version *fn-lg-version*)
                            (kind *fn-gen-kind*) (payload (fn-gen-payload g))
                            (max-payload *fn-gen-max-payload*)))
           :in-theory (e/d (fn-gen-decode fn-gen-frame fn-frame-inputp fn-frame-magicp)
                           (fn-frame-open-of-seal fn-frame-fields-parse-of-octets
                            fn-gen-seal-octet-listp fn-gen-payload
                            fn-gen-payload-facts fn-gen-p fn-frame-seal
                            fn-frame-open fn-frame-fields-parse fn-frame-fields-octets)))))

; KEYSTONE (init, then open).  The file `init' and `store import' write for a
; genesis record of this format, this image's schema and the profile the
; store is born with opens, at every later open of that profile, as that
; record, and its trailer is the chain value segment 1 starts from (under
; A-CRYPTO: `fn-frame-open-of-seal').
(defthm fn-gen-open-of-the-genesis-init-writes
  (implies (and (fn-gen-p g)
                (equal (fn-gen-format g) *fn-bs-meta-format-10*)
                (equal (fn-gen-schema g) (fn-gen-image-schema-digest))
                (equal (fn-gen-profile-digest g) (fn-gen-profile-digest-of profile)))
           (equal (fn-gen-open (fn-gen-frame g) profile)
                  (list :genesis g (fn-gen-trailer (fn-gen-frame g)))))
  :hints (("Goal" :use fn-gen-decode-of-frame
           :in-theory (e/d (fn-gen-open)
                           (fn-gen-decode-of-frame fn-gen-decode fn-gen-frame
                            fn-gen-p fn-gen-image-schema-digest
                            fn-gen-profile-digest-of)))))

; The same, over the host's call: whatever readings the host draws, when
; `fn-gen-octets-for' writes a file (the readings fit the record), the open
; of that file under the same profile answers the record it wrote.
(defthm fn-gen-open-of-octets-for
  (implies (fn-gen-record-for node salt created revision profile)
           (equal (fn-gen-open (fn-gen-octets-for node salt created revision profile)
                               profile)
                  (list :genesis (fn-gen-record-for node salt created revision profile)
                        (fn-gen-trailer
                         (fn-gen-octets-for node salt created revision profile)))))
  :hints (("Goal" :use ((:instance fn-gen-open-of-the-genesis-init-writes
                                   (g (fn-gen-record-for node salt created revision
                                                         profile))))
           :in-theory (e/d (fn-gen-octets-for fn-gen-record-for fn-gen-make
                            fn-gen-format fn-gen-schema fn-gen-profile-digest fn-gen-nth)
                           (fn-gen-open-of-the-genesis-init-writes fn-gen-open
                            fn-gen-frame fn-gen-p fn-gen-image-schema-digest
                            fn-gen-profile-digest-of fn-bs-profile-validp)))))

; The history salt a genesis carries is 32 bits: the stobj's hash reads it as
; its offset basis (books/history-columns.lisp fn-hist-hash takes any
; natural; the stobj's field is (unsigned-byte 32)).
(defthm fn-gen-salt-is-32-bits
  (implies (fn-gen-p g)
           (and (natp (fn-gen-salt g))
                (< (fn-gen-salt g) *fn-gen-salt-modulus*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-gen-p fn-gen-salt))))

; The salt the open hands the owner: the record's, or 0 when the open did
; not answer a genesis (the host never installs then: it refused).
(defun fn-gen-verdict-salt (verdict)
  (declare (xargs :guard t))
  (if (and (consp verdict) (equal (car verdict) :genesis) (consp (cdr verdict)))
      (mod (fn-gen-salt (cadr verdict)) *fn-gen-salt-modulus*)
    0))

(defthm fn-gen-verdict-salt-is-32-bits
  (unsigned-byte-p 32 (fn-gen-verdict-salt verdict))
  :hints (("Goal" :in-theory (enable fn-gen-verdict-salt))))

(verify-guards fn-gen-payload
  :hints (("Goal" :in-theory (enable fn-gen-p))))
(verify-guards fn-gen-frame
  :hints (("Goal" :use fn-gen-payload-facts
           :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                           (fn-gen-payload-facts fn-gen-payload fn-gen-p)))))
(verify-guards fn-gen-profile-digest-of)
(verify-guards fn-gen-record-for)
(defthm fn-gen-record-for-is-a-record
  (implies (fn-gen-record-for node salt created revision profile)
           (fn-gen-p (fn-gen-record-for node salt created revision profile)))
  :hints (("Goal" :in-theory (e/d (fn-gen-record-for)
                                  (fn-gen-p fn-gen-make fn-gen-image-schema-digest
                                   fn-gen-profile-digest-of fn-bs-profile-validp)))))

(verify-guards fn-gen-octets-for
  :hints (("Goal" :in-theory (e/d () (fn-gen-p fn-gen-frame fn-gen-record-for)))))
(verify-guards fn-gen-decode
  :hints (("Goal" :use ((:instance fn-frame-decode-payload-octets
                                   (digest (fn-frame-digest (fn-frame-protected-prefix octets)))
                                   (max-payload *fn-gen-max-payload*)))
           :in-theory (e/d (fn-frame-open) (fn-frame-decode-payload-octets fn-gen-p)))))
(verify-guards fn-gen-open)
