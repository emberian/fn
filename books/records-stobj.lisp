; fn: the record codec over the octet buffer (D27 boundary 7; the megaspike,
; D28).  Prefix `fn-rcs-'.
;
; The list codec (books/records.lisp) encodes a record as a fourteen-way
; `append' of CBOR items, each item itself an `append' of its head and its
; content (the payload copied once more), and decodes one by `take'/`nthcdr'
; slices, one copy per item.  Here the encoder writes each item straight
; into the buffer stobj (books/octets-stobj): the CBOR head from
; `fn-cbor-encode-argument' (one to five octets), a string field by `char'
; at an index, the payload by one write per octet of its list.  The decoder
; reads by position: every field is checked in place and only the values
; the record holds are built, the strings straight from the buffer
; (`fn-oct-slice-string') and the payload once, as the octet list the
; logical record holds (`fn-oct-slice-list-down').  The reference's bounds
; (`*fn-record-max-octets*' on the whole and on each bytes item,
; `*fn-record-max-payload*', `*fn-record-max-groups*') are checked at the
; same points, before any allocation.
;
; `fn-rcs-store-seal-record' and `fn-rcs-unframe-record' are the two host
; entries: the pending record to a sealed frame in the buffer (write), and
; a frame in the buffer to the record it carries (recovery).  The
; correspondence theorems at the end are stated against
; `fn-record-encode-impl' and `fn-record-decode-exact-impl', the functions
; the seam's attachments run (books/records-seam, books/records-attach,
; books/records-attach-concrete).

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "frame-stobj")
(include-book "records-codec-concrete")

; -----------------------------------------------------------------------------
; Encoder

(defun fn-rcs-put-arg (major n fn-octets)
  ; The CBOR head of an item of major type MAJOR and argument N.
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-frs-append-octets (fn-cbor-encode-argument major n) fn-octets))

(defun fn-rcs-put-uint (n fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-rcs-put-arg 0 n fn-octets))

(defun fn-rcs-put-string (s fn-octets)
  ; A bytes item whose content is the string's character codes, read in place.
  (declare (xargs :stobjs fn-octets :guard t))
  (if (stringp s)
      (let ((fn-octets (fn-rcs-put-arg 2 (length s) fn-octets)))
        (fn-oct-append-string s fn-octets))
    fn-octets))

(defun fn-rcs-put-octets (xs fn-octets)
  ; A bytes item whose content is the octet list, one write per octet.
  (declare (xargs :stobjs fn-octets :guard t))
  (if (fn-cbor-octet-listp xs)
      (let ((fn-octets (fn-rcs-put-arg 2 (len xs) fn-octets)))
        (fn-oct-append-list xs fn-octets))
    fn-octets))

(defun fn-rcs-put-strings (xs fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (if (atom xs)
      fn-octets
    (let ((fn-octets (fn-rcs-put-string (car xs) fn-octets)))
      (fn-rcs-put-strings (cdr xs) fn-octets))))

; The encoded size, computed before anything is written, so the whole-record
; bound is checked where the reference checks it (after its append) with the
; same answer.
(defun fn-rcs-arg-size (n)
  (declare (xargs :guard t))
  (if (not (natp n)) 0 (if (< n 24) 1 (if (< n 256) 2 (if (< n 65536) 3 5)))))

(defun fn-rcs-string-size (s)
  (declare (xargs :guard t))
  (if (stringp s) (+ (fn-rcs-arg-size (length s)) (length s)) 0))

(defun fn-rcs-strings-size (xs)
  (declare (xargs :guard t))
  (if (atom xs) 0 (+ (fn-rcs-string-size (car xs)) (fn-rcs-strings-size (cdr xs)))))

(defun fn-rcs-encoded-size (record)
  (declare (xargs :guard t))
  (+ (fn-rcs-arg-size (len *fn-record-magic*)) (len *fn-record-magic*)
     (fn-rcs-arg-size (fn-record-schema-octet record))
     (fn-rcs-arg-size (fn-record-sequence record))
     (fn-rcs-arg-size (fn-record-txid record))
     (fn-rcs-arg-size (fn-record-generation record))
     (fn-rcs-string-size (fn-record-msgid record))
     (fn-rcs-arg-size (len (fn-record-payload record))) (len (fn-record-payload record))
     (fn-rcs-arg-size (len (fn-record-groups record)))
     (fn-rcs-strings-size (fn-record-groups record))
     (fn-rcs-string-size (fn-record-obligation-id record))
     (fn-rcs-string-size (fn-record-content-subject record))
     (fn-rcs-string-size (fn-record-release-evidence record))
     (fn-rcs-arg-size (fn-record-charge record))
     (if (equal (fn-record-stamp record) :legacy) 0
       (fn-rcs-arg-size (fn-record-stamp record)))))

(defun fn-rcs-encode-into (record fn-octets)
  ; Append the record's encoding to the buffer.  (mv okp fn-octets): okp is
  ; nil, and nothing is written, exactly when the reference encodes nothing.
  (declare (xargs :stobjs fn-octets :guard t))
  (if (or (not (fn-rcon-record-p record))
          (< *fn-record-max-octets* (fn-rcs-encoded-size record)))
      (mv nil fn-octets)
    (let* ((fn-octets (fn-rcs-put-octets *fn-record-magic* fn-octets))
           (fn-octets (fn-rcs-put-uint (fn-record-schema-octet record) fn-octets))
           (fn-octets (fn-rcs-put-uint (fn-record-sequence record) fn-octets))
           (fn-octets (fn-rcs-put-uint (fn-record-txid record) fn-octets))
           (fn-octets (fn-rcs-put-uint (fn-record-generation record) fn-octets))
           (fn-octets (fn-rcs-put-string (fn-record-msgid record) fn-octets))
           (fn-octets (fn-rcs-put-octets (fn-record-payload record) fn-octets))
           (fn-octets (fn-rcs-put-uint (len (fn-record-groups record)) fn-octets))
           (fn-octets (fn-rcs-put-strings (fn-record-groups record) fn-octets))
           (fn-octets (fn-rcs-put-string (fn-record-obligation-id record) fn-octets))
           (fn-octets (fn-rcs-put-string (fn-record-content-subject record) fn-octets))
           (fn-octets (fn-rcs-put-string (fn-record-release-evidence record) fn-octets))
           (fn-octets (fn-rcs-put-uint (fn-record-charge record) fn-octets))
           (fn-octets (if (equal (fn-record-stamp record) :legacy)
                          fn-octets
                        (fn-rcs-put-uint (fn-record-stamp record) fn-octets))))
      (mv t fn-octets))))

(defun fn-rcs-store-seal-record (record fn-octets)
  ; The host's write entry: the buffer becomes the sealed store frame of
  ; RECORD.  (mv okp fn-octets).
  (declare (xargs :stobjs fn-octets :guard t))
  (let* ((fn-octets (fn-octets-clear fn-octets))
         (fn-octets (fn-frs-append-zeros *fn-frame-header-octets* fn-octets)))
    (mv-let (okp fn-octets)
      (fn-rcs-encode-into record fn-octets)
      (if (not okp)
          (mv nil fn-octets)
        (fn-frs-store-seal fn-octets)))))

; -----------------------------------------------------------------------------
; Decoder, by position.  Every reader takes the range [i, n) and returns
; (mv error value next).  Positions are clamped into the range at each use
; (`fn-rcs-pos'), which is the identity on every value a reader returns and
; makes each guard a fact about the clamp; the dev lane proves the readers'
; range facts and drops the clamps.

(defun fn-rcs-pos (x n)
  (declare (xargs :guard (natp n)))
  (if (and (natp x) (<= x n)) x n))

(defun fn-rcs-read-arg (additional i n fn-octets)
  ; `fn-cbor-decode-argument' in place: (mv error value next).
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp additional) (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (cond ((< additional 24) (mv nil additional i))
        ((= additional 24)
         (if (< i n)
             (mv nil (fn-frs-byte (fn-octets-get i fn-octets)) (+ i 1))
           (mv :truncated 0 i)))
        ((= additional 25)
         (if (<= (+ i 2) n)
             (mv nil (+ (* 256 (fn-frs-byte (fn-octets-get i fn-octets)))
                        (fn-frs-byte (fn-octets-get (+ i 1) fn-octets)))
                 (+ i 2))
           (mv :truncated 0 i)))
        ((= additional 26)
         (if (<= (+ i 4) n)
             (mv nil (fn-frs-get-u32 i fn-octets) (+ i 4))
           (mv :truncated 0 i)))
        (t (mv :unsupported 0 i))))

(defun fn-rcs-read-item (i n fn-octets)
  ; `fn-cbor-decode-prechecked' in place with the record's item budget:
  ; (mv error kind value next), where a :uint item's value is the integer
  ; and a :bytes item's value is the start of its content and NEXT its end.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (if (<= n i)
      (mv :truncated nil 0 i)
    (let ((head (fn-frs-byte (fn-octets-get i fn-octets))))
      (if (< head 32)
          (mv-let (err arg next)
            (fn-rcs-read-arg head (+ i 1) n fn-octets)
            (cond (err (mv err nil 0 i))
                  ((not (fn-cbor-canonical-argumentp head (nfix arg)))
                   (mv :noncanonical nil 0 i))
                  (t (mv nil :uint (nfix arg) (fn-rcs-pos next n)))))
        (if (and (< 63 head) (< head 96))
            (mv-let (err length next)
              (fn-rcs-read-arg (- head 64) (+ i 1) n fn-octets)
              (let ((next (fn-rcs-pos next n)) (length (nfix length)))
                (cond (err (mv err nil 0 i))
                      ((not (fn-cbor-canonical-argumentp (- head 64) length))
                       (mv :noncanonical nil 0 i))
                      ((< *fn-record-max-octets* length) (mv :limit nil 0 i))
                      ((< (- n next) length) (mv :truncated nil 0 i))
                      (t (mv nil :bytes next (+ next length))))))
          (mv :unsupported nil 0 i))))))

(defun fn-rcs-read-uint (i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (mv-let (err kind value next)
    (fn-rcs-read-item i n fn-octets)
    (cond (err (mv err 0 i))
          ((not (equal kind :uint)) (mv :field-type 0 i))
          (t (mv nil (nfix value) (fn-rcs-pos next n))))))

(defun fn-rcs-read-bytes (i n fn-octets)
  ; (mv error start end): the content range of a bytes item; END is also
  ; the position after the item.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (mv-let (err kind value next)
    (fn-rcs-read-item i n fn-octets)
    (cond (err (mv err i i))
          ((not (equal kind :bytes)) (mv :field-type i i))
          (t (let* ((start (fn-rcs-pos value n))
                    (end (fn-rcs-pos next n))
                    (end (if (< end start) start end)))
               (mv nil start end))))))

(defun fn-rcs-read-strings (count i n acc fn-octets)
  ; COUNT bytes items as strings, each a group name: (mv error names next).
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp count) (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)) (true-listp acc))
                  :measure (nfix count)))
  (if (zp count)
      (mv nil (revappend acc nil) i)
    (mv-let (err start end)
      (fn-rcs-read-bytes i n fn-octets)
      (if err
          (mv err nil i)
        (let* ((start (fn-rcs-pos start n))
               (end (fn-rcs-pos end n))
               (end (if (< end start) start end))
               (name (fn-oct-slice-string start end fn-octets)))
          (if (not (fn-record-group-namep name))
              (mv :group nil i)
            (fn-rcs-read-strings (1- count) end n (cons name acc) fn-octets)))))))

; The facts the decoders' guards need about the readers, so that no guard
; proof opens a reader: a clamped position is a natural at most N, a read
; unsigned is a natural, the group names are a true list.
(defthm fn-rcs-pos-facts
  (implies (natp n)
           (and (natp (fn-rcs-pos x n))
                (<= (fn-rcs-pos x n) n)))
  :rule-classes ((:rewrite :corollary (implies (natp n) (and (integerp (fn-rcs-pos x n)) (<= 0 (fn-rcs-pos x n)))))
                 (:type-prescription :corollary (implies (natp n) (natp (fn-rcs-pos x n))))
                 (:linear :corollary (implies (natp n) (<= (fn-rcs-pos x n) n)))))

(in-theory (disable fn-rcs-pos fn-rcs-read-arg fn-rcs-read-item))

(defthm fn-rcs-read-uint-value-natp
  (natp (mv-nth 1 (fn-rcs-read-uint i n fn-octets)))
  :rule-classes ((:rewrite) (:type-prescription))
  :hints (("Goal" :in-theory (enable fn-rcs-read-uint))))

(in-theory (disable fn-rcs-read-uint fn-rcs-read-bytes))

(defthm fn-rcs-read-strings-names-true-listp
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (fn-rcs-read-strings count i n acc fn-octets))))
  :hints (("Goal" :induct (fn-rcs-read-strings count i n acc fn-octets)
           :in-theory (enable fn-rcs-read-strings))))

(in-theory (disable fn-rcs-read-strings))

(defun fn-rcs-slice-string (start end n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp n) (<= n (fn-octets-len fn-octets)))))
  (let* ((start (fn-rcs-pos start n))
         (end (fn-rcs-pos end n))
         (end (if (< end start) start end)))
    (fn-oct-slice-string start end fn-octets)))

(defun fn-rcs-decode-tail (schema sequence txid generation msgid payload i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (mv-let (err count next)
    (fn-rcs-read-uint i n fn-octets)
    (if err
        (fn-record-parse-error :group-count)
      (if (< *fn-record-max-groups* count)
          (fn-record-parse-error :groups-limit)
        (mv-let (err groups next)
          (fn-rcs-read-strings count (fn-rcs-pos next n) n nil fn-octets)
          (if err
              (fn-record-parse-error err)
            (if (not (no-duplicatesp-equal groups))
                (fn-record-parse-error :duplicate-group)
              (mv-let (err id-start id-end)
                (fn-rcs-read-bytes (fn-rcs-pos next n) n fn-octets)
                (if err
                    (fn-record-parse-error err)
                  (mv-let (err subject-start subject-end)
                    (fn-rcs-read-bytes (fn-rcs-pos id-end n) n fn-octets)
                    (if err
                        (fn-record-parse-error err)
                      (mv-let (err evidence-start evidence-end)
                        (fn-rcs-read-bytes (fn-rcs-pos subject-end n) n fn-octets)
                        (if err
                            (fn-record-parse-error err)
                          (mv-let (err charge next)
                            (fn-rcs-read-uint (fn-rcs-pos evidence-end n) n fn-octets)
                            (if err
                                (fn-record-parse-error err)
                              (mv-let (stamp-err stamp next)
                                (if (equal schema 0)
                                    (mv nil :legacy next)
                                  (fn-rcs-read-uint (fn-rcs-pos next n) n fn-octets))
                                (let ((record
                                       (fn-record-make
                                        sequence txid generation msgid payload groups
                                        (fn-rcs-slice-string id-start id-end n fn-octets)
                                        (fn-rcs-slice-string subject-start subject-end n fn-octets)
                                        (fn-rcs-slice-string evidence-start evidence-end n fn-octets)
                                        charge stamp)))
                                  (if stamp-err
                                      (fn-record-parse-error stamp-err)
                                    (if (not (equal (fn-rcs-pos next n) n))
                                        (fn-record-parse-error :trailing)
                                      (if (fn-rcon-record-p record)
                                          (fn-record-result-ok record)
                                        (fn-record-parse-error :invalid)))))))))))))))))))))

(defun fn-rcs-decode-after-header (schema i n fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (mv-let (err sequence next)
    (fn-rcs-read-uint i n fn-octets)
    (if err
        (fn-record-parse-error err)
      (mv-let (err txid next)
        (fn-rcs-read-uint (fn-rcs-pos next n) n fn-octets)
        (if err
            (fn-record-parse-error err)
          (mv-let (err generation next)
            (fn-rcs-read-uint (fn-rcs-pos next n) n fn-octets)
            (if err
                (fn-record-parse-error err)
              (mv-let (err msgid-start msgid-end)
                (fn-rcs-read-bytes (fn-rcs-pos next n) n fn-octets)
                (if err
                    (fn-record-parse-error err)
                  (let ((msgid (fn-rcs-slice-string msgid-start msgid-end n fn-octets)))
                    (if (not (fn-record-msgidp msgid))
                        (fn-record-parse-error :msgid)
                      (mv-let (err payload-start payload-end)
                        (fn-rcs-read-bytes (fn-rcs-pos msgid-end n) n fn-octets)
                        (if err
                            (fn-record-parse-error err)
                          (let* ((payload-start (fn-rcs-pos payload-start n))
                                 (payload-end (fn-rcs-pos payload-end n))
                                 (payload-end (if (< payload-end payload-start)
                                                  payload-start payload-end)))
                            (if (< *fn-record-max-payload* (- payload-end payload-start))
                                (fn-record-parse-error :payload)
                              (fn-rcs-decode-tail
                               schema sequence txid generation msgid
                               (fn-oct-slice-list-down payload-start payload-end nil fn-octets)
                               payload-end n fn-octets))))))))))))))))

(defun fn-rcs-decode-exact (i n fn-octets)
  ; `fn-record-decode-exact-impl' of the range [i, n), in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-octets-len fn-octets)))))
  (if (< *fn-record-max-octets* (- n i))
      (fn-record-parse-error :limit)
    (mv-let (err start end)
      (fn-rcs-read-bytes i n fn-octets)
      (if err
          (fn-record-parse-error err)
        (let* ((start (fn-rcs-pos start n))
               (end (fn-rcs-pos end n))
               (end (if (< end start) start end)))
          (if (not (and (equal (- end start) (len *fn-record-magic*))
                        (fn-oct-prefix-equalp start *fn-record-magic* fn-octets)))
              (fn-record-parse-error :magic)
            (mv-let (err version next)
              (fn-rcs-read-uint end n fn-octets)
              (if err
                  (fn-record-parse-error err)
                (if (not (member-equal version '(0 1)))
                    (fn-record-parse-error :unknown-version)
                  (fn-rcs-decode-after-header version (fn-rcs-pos next n) n fn-octets))))))))))

(defun fn-rcs-unframe-record (fn-octets)
  ; The host's recovery entry: the buffer holds one transaction file.
  ; (mv kind value): (:record r) when the frame carries an article record;
  ; (:octets xs) with the frame's record octets when it carries another
  ; store event kind (the host layer decodes those through the list codec);
  ; (:frame-error reason) when the frame is refused.
  (declare (xargs :stobjs fn-octets))
  (let ((frame (fn-frs-store-decode fn-octets)))
    (if (not (fn-frs-okp frame))
        (mv :frame-error (if (and (consp frame) (consp (cdr frame))) (car (cdr frame)) :unknown))
      (let* ((start (fn-rcs-pos (fn-frs-start frame) (fn-octets-len fn-octets)))
             (end (fn-rcs-pos (fn-frs-end frame) (fn-octets-len fn-octets)))
             (end (if (< end start) start end))
             (decoded (fn-rcs-decode-exact start end fn-octets)))
        (if (fn-record-result-okp decoded)
            (mv :record (fn-record-result-record decoded))
          (mv :octets (fn-oct-slice-list-down start end nil fn-octets)))))))

; -----------------------------------------------------------------------------
; The correspondence.

;; SPIKE: defers the two theorems below.  Statements: the in-place encoder
;; appends exactly `fn-record-encode-impl' of the record, succeeding exactly
;; when the reference encodes; the in-place decoder of the whole buffer is
;; `fn-record-decode-exact-impl' of the list.  The dev lane proves the
;; encoder by the fourteen items (`fn-rcs-put-arg' is `fn-cbor-encode-argument'
;; appended, `fn-rcs-put-string' is the `(:bytes . codes)' item,
;; `fn-rcs-encoded-size' is `len' of the encoding) and the decoder by the
;; reader lemmas (each `fn-rcs-read-*' is its `fn-record-read-*' on
;; `(nthcdr i list)' with NEXT the position of the rest).
(skip-proofs
 (progn
   (defthm fn-rcs-encode-into-is-record-encode-impl
     (implies (fn-record-p record)
              (and (equal (mv-nth 0 (fn-rcs-encode-into record fn-octets))
                          (not (null (fn-record-encode-impl record))))
                   (equal (fn-octets-list (mv-nth 1 (fn-rcs-encode-into record fn-octets)))
                          (append (fn-octets-list fn-octets)
                                  (fn-record-encode-impl record))))))
   (defthm fn-rcs-decode-exact-is-record-decode-exact-impl
     (equal (fn-rcs-decode-exact 0 (len (fn-octets-list fn-octets)) fn-octets)
            (fn-record-decode-exact-impl (fn-octets-list fn-octets))))))

; The write entry, as a consequence of the two seals: the buffer after
; `fn-rcs-store-seal-record' is the frame the host wrote before this book,
; `fn-frame-encode' of the record's encoding under the SHA-256 trailer.
;; SPIKE: defers fn-rcs-store-seal-record-is-sealed-frame (from
;; fn-rcs-encode-into-is-record-encode-impl and fn-frs-store-seal-is-frame-encode).
(skip-proofs
 (defthm fn-rcs-store-seal-record-is-sealed-frame
   (implies (and (fn-record-p record)
                 (fn-record-encode-impl record)
                 (<= (len (fn-record-encode-impl record)) *fn-frame-max-store-payload*))
            (and (equal (mv-nth 0 (fn-rcs-store-seal-record record fn-octets)) t)
                 (equal (fn-octets-list (mv-nth 1 (fn-rcs-store-seal-record record fn-octets)))
                        (fn-frame-encode
                         *fn-frame-magic-store* *fn-frame-version* *fn-frame-store-kind*
                         (fn-record-encode-impl record)
                         (fn-sha256 (fn-frame-protected
                                     *fn-frame-magic-store* *fn-frame-version*
                                     *fn-frame-store-kind*
                                     (fn-record-encode-impl record)))))))))
