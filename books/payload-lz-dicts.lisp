; fn: the shipped preset dictionaries, by digest (lane compress, PRF-912,
; STO-037).  Prefix `fn-lzd-'.
;
; A stored payload is DEFLATE over a preset dictionary (RFC 1950 section
; 2.2's FDICT, RFC 9842's dictionary-by-digest shape): the payload's frame
; (books/payload-lz-record.lisp) names its dictionary by DICT-ID, the first
; four octets of the dictionary's BLAKE3 digest read big-endian; ID 0 is the
; empty dictionary.  The table is the release's: append-only, kept forever
; (a payload is never transcoded at rest), each dictionary at most 64 KiB
; (the inflater's preset is its last 32 KiB), no learned, per-group or
; on-node dictionary (docs/extensions/nntp-compress-dict.md).
;
; Baseline 1 is built from text fn owns by a recorded recipe
; (tools/build_compress_dict.py; its inputs and their digests in
; planning/evidence/compress-dict/baseline-1.json).  Its digest is computed
; here by fn's BLAKE3 (books/blake3.lisp) and checked against the recorded
; one when the book is certified, so the ID is ACL2's, not the builder's.
;
; `fn-lzd-table' is the table as the frame books take it ((ID . OCTETS)
; ...); `fn-lzd-current-id' is the dictionary new payloads are made under.

(in-package "ACL2")
(include-book "blake3")
(include-book "payload-lz-dict-1")

(defun fn-lzd-id-of-digest (digest)
  ; The first four octets of a 32-octet digest, big-endian.
  (declare (xargs :guard t))
  (let ((d (fn-b3-fix-octets digest)))
    (if (<= 4 (len d))
        (+ (* 16777216 (nfix (nth 0 d))) (* 65536 (nfix (nth 1 d)))
           (* 256 (nfix (nth 2 d))) (nfix (nth 3 d)))
      0)))

(defconst *fn-lzd-baseline-1-id* (fn-lzd-id-of-digest *fn-lzd-baseline-1-blake3*))

; The recorded digest is BLAKE3 of the octets (computed at certification).
(assert-event (equal (fn-blake3 *fn-lzd-baseline-1*) *fn-lzd-baseline-1-blake3*))
(assert-event (equal (len *fn-lzd-baseline-1*) 32768))
; The builder's DICT-ID (baseline-1.json "dict_id").
(assert-event (equal *fn-lzd-baseline-1-id* 2220533217))

; The shipped entries: (ID DIGEST OCTETS), oldest first.  Append only.
(defconst *fn-lzd-shipped*
  (list (list *fn-lzd-baseline-1-id* *fn-lzd-baseline-1-blake3* *fn-lzd-baseline-1*)))

(defun fn-lzd-shipped ()
  (declare (xargs :guard t))
  *fn-lzd-shipped*)

(defun fn-lzd-table-of (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (let ((e (car entries)))
        (cons (cons (if (consp e) (nfix (car e)) 0)
                    (if (and (consp e) (consp (cdr e)) (consp (cddr e)))
                        (fn-b3-fix-octets (caddr e))
                      nil))
              (fn-lzd-table-of (cdr entries))))
    nil))

(defun fn-lzd-table ()
  ; ID 0 (the empty dictionary), then every shipped one.
  (declare (xargs :guard t))
  (cons (cons 0 nil) (fn-lzd-table-of *fn-lzd-shipped*)))

(defun fn-lzd-current-id ()
  ; New payloads are made under the latest shipped dictionary.
  (declare (xargs :guard t))
  *fn-lzd-baseline-1-id*)

(defun fn-lzd-lookup (id)
  ; The octets of dictionary ID, or nil when the table has none.
  (declare (xargs :guard t))
  (cdr (assoc-equal id (fn-lzd-table))))

; Every ID is distinct and a u32; every dictionary is octets of at most
; 64 KiB; every shipped ID is its digest's.
(defun fn-lzd-entries-okp (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (let ((e (car entries)))
        (and (true-listp e) (equal (len e) 3)
             (natp (car e)) (< (car e) 4294967296) (< 0 (car e))
             (equal (car e) (fn-lzd-id-of-digest (cadr e)))
             (fn-b3-octet-listp (caddr e))
             (<= (len (caddr e)) 65536)
             (equal (fn-blake3 (caddr e)) (cadr e))
             (fn-lzd-entries-okp (cdr entries))))
    t))

(defun fn-lzd-ids (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (cons (if (consp (car entries)) (caar entries) nil) (fn-lzd-ids (cdr entries)))
    nil))

(assert-event (and (fn-lzd-entries-okp *fn-lzd-shipped*)
                   (no-duplicatesp-equal (cons 0 (fn-lzd-ids *fn-lzd-shipped*)))))

(defthm fn-lzd-table-current
  (equal (fn-lzd-lookup (fn-lzd-current-id)) *fn-lzd-baseline-1*))

(in-theory (disable fn-lzd-table fn-lzd-current-id fn-lzd-lookup))
