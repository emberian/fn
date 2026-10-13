; LB-LOG-MODEL: owner C; retires when LA1 and LA6 land, owner P.
; A segment has its actual octets and its committed-entry directory.  The
; directory is the logical result of LA's record parser, not a resident
; catalog copy.  Each entry records its ordinal, protected prefix position
; and length, stored-range position and length, payload handle, stored
; payload, and log-home fields.  Range readers below read the segment's
; OCTETS, independently of these semantic parser results.
;
; Stored payload means the acceptance result, including injection lines.
; Articles use CRLF and dot stuffing with no terminator.  A reclaim MOVE
; stores the raw tombstone.  The home frame includes every log-home field;
; catalog correspondence must compare these fields with the original row.
(in-package "ACL2")
(include-book "catalog-logic")
(include-book "nntp-article-pass")
(include-book "reclaim-tombstone")
(include-book "payload-extent")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-nntp-stuffed-section (kind payload)
  (declare (xargs :guard t :verify-guards nil))
  (let ((section (fn-nntp-section-of-bytes payload kind)))
    (if (equal (car section) :ok)
        (fn-nntp-stuff-lines (cadr section))
      nil)))

(defun fn-lb-log-model-wire (payload startp)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp payload)
      (append (if (and startp (eql (car payload) 46)) '(46) nil)
              (cons (car payload)
                    (fn-lb-log-model-wire (cdr payload) (eql (car payload) 10))))
    nil))

(defun fn-la-payload-wire (stored-payload)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lb-log-model-wire stored-payload t))

(defun fn-la-tombstone-raw (tombstone)
  (declare (xargs :guard t))
  tombstone)

(defun fn-lb-log-model-homes (row)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-record-obligation-id row)
        (fn-record-content-subject row)
        (fn-record-release-evidence row)
        (fn-held-context row)
        (let ((control (true-list-fix (fn-hf-control (fn-held-facts row)))))
          (list (len control)
                (take (min 3 (len control)) control)
                (nthcdr 4 control)))))

; Self-delimiting, unlimited-width naturals.  This is the temporary
; adapter's value encoder; it imposes no u64 or checkpoint-codec ceiling.
(defun fn-lb-log-model-nat-octets (n)
  (declare (xargs :guard (natp n) :verify-guards nil
                  :measure (nfix n)))
  (if (and (natp n) (>= n 128))
      (cons (+ 128 (mod n 128))
            (fn-lb-log-model-nat-octets (floor n 128)))
    (list (nfix n))))

(defun fn-lb-log-model-text-octets (text)
  (declare (xargs :guard (stringp text) :verify-guards nil))
  (append (fn-lb-log-model-nat-octets (length text))
          (fn-record-string-octets text)))

(defun fn-lb-log-model-value-octets (value)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((null value) '(0))
        ((consp value)
         (cons 1 (append (fn-lb-log-model-value-octets (car value))
                         (fn-lb-log-model-value-octets (cdr value)))))
        ((integerp value)
         (cons (if (< value 0) 3 2)
               (fn-lb-log-model-nat-octets (if (< value 0) (- -1 value) value))))
        ((rationalp value)
         (cons 4 (append (fn-lb-log-model-value-octets (numerator value))
                         (fn-lb-log-model-value-octets (denominator value)))))
        ((complex-rationalp value)
         (cons 5 (append (fn-lb-log-model-value-octets (realpart value))
                         (fn-lb-log-model-value-octets (imagpart value)))))
        ((characterp value) (list 6 (char-code value)))
        ((stringp value) (cons 7 (fn-lb-log-model-text-octets value)))
        (t (cons 8 (append (fn-lb-log-model-text-octets (symbol-package-name value))
                           (fn-lb-log-model-text-octets (symbol-name value)))))))

(defun fn-lb-log-model-home-frame (row)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-cat-rowp row)
      (let ((bytes (fn-lb-log-model-value-octets (fn-lb-log-model-homes row))))
        (append (fn-lb-log-model-nat-octets (len bytes)) bytes))
    :bad))

; Segment: (ID OCTETS ENTRIES).  Entry:
; (ORDINAL ENTRY-OFF PROTECTED-LEN RANGE-OFF RANGE-LEN HANDLE PAYLOAD HOMES SEQUENCE).
; Its committed-entry directory is supplied by the named LA parser adapter.
(defun fn-lb-log-model-entryp (entry)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp entry) (equal (len entry) 9)
       (natp (nth 0 entry)) (natp (nth 1 entry)) (natp (nth 2 entry))
       (natp (nth 3 entry)) (natp (nth 4 entry)) (natp (nth 5 entry))
       (fn-cbor-octet-listp (nth 6 entry))
       (true-listp (nth 7 entry)) (equal (len (nth 7 entry)) 5)
       (fn-record-uint64p (nth 8 entry))))

(defun fn-lb-log-model-entriesp (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (and (fn-lb-log-model-entryp (car entries))
           (fn-lb-log-model-entriesp (cdr entries)))
    (null entries)))

(defun fn-lb-log-model-segsp (segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (and (true-listp (car segs)) (equal (len (car segs)) 3)
           (unsigned-byte-p 64 (caar segs))
           (fn-cbor-octet-listp (cadar segs))
           (fn-lb-log-model-entriesp (caddar segs))
           (fn-lb-log-model-segsp (cdr segs)))
    (null segs)))

(defun fn-lb-log-model-segment (segment segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (if (equal segment (caar segs)) (car segs)
        (fn-lb-log-model-segment segment (cdr segs)))
    nil))

(defun fn-lb-log-model-entry (entry entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (if (equal entry (caar entries)) (car entries)
        (fn-lb-log-model-entry entry (cdr entries)))
    nil))

(defun fn-lb-log-model-read-range (segment offset length segs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((seg (fn-lb-log-model-segment segment segs))
         (bytes (cadr seg)))
    (if (and seg (natp offset) (natp length)
             (<= (+ offset length) (len bytes)))
        (take length (nthcdr offset bytes))
      :bad)))

(defun fn-lb-log-model-home-entry (position entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (if (equal position (+ (nfix (nth 3 (car entries)))
                             (nfix (nth 4 (car entries)))))
          (car entries)
        (fn-lb-log-model-home-entry position (cdr entries)))
    nil))

(defun fn-lb-log-model-read-home-frame (position segs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((seg (fn-lb-log-model-segment (car position) segs))
         (entry (fn-lb-log-model-home-entry (cadr position) (caddr seg)))
         (end (+ (nfix (nth 1 entry)) (nfix (nth 2 entry)))))
    (if (and entry (natp (cadr position)) (<= (cadr position) end))
        (fn-lb-log-model-read-range (car position) (cadr position)
                                    (- end (cadr position)) segs)
      :bad)))

(defun fn-lb-log-model-handle-entry (handle entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (if (equal handle (nth 5 (car entries))) (car entries)
        (fn-lb-log-model-handle-entry handle (cdr entries)))
    nil))

(defun fn-lb-log-model-payload-entry (handle segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (or (fn-lb-log-model-handle-entry handle (caddar segs))
          (fn-lb-log-model-payload-entry handle (cdr segs)))
    nil))

(defun fn-lb-log-model-payload-segment (handle segs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp segs)
      (if (fn-lb-log-model-handle-entry handle (caddar segs))
          (caar segs)
        (fn-lb-log-model-payload-segment handle (cdr segs)))
    nil))

(defun fn-lb-log-payload (row log)
  (declare (xargs :guard t :verify-guards nil))
  (nth 6 (fn-lb-log-model-payload-entry (fn-record-payload row) log)))

(defun fn-lb-entry-protected-len (seg entry log)
  (declare (xargs :guard t :verify-guards nil))
  (nfix (nth 2 (fn-lb-log-model-entry entry
                      (caddr (fn-lb-log-model-segment seg log))))))

(defun fn-lb-entry-octets (seg entry log)
  (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-lb-log-model-entry entry
                (caddr (fn-lb-log-model-segment seg log)))))
    (if e
        (fn-lb-log-model-read-range seg (nth 1 e)
          (+ (nfix (nth 2 e)) *fn-frame-trailer-octets*) log)
      nil)))

; Adapter PRE: version and payload kind, followed by the original sequence.
; This provisional record is removed with LB-LOG-MODEL at LA1/LA6.  A MOVE
; preserves the sequence and home suffix, while a reclaim supplies the new
; sealed tombstone handle and its raw range.
(defun fn-lb-log-model-pre (row payload)
  (declare (xargs :guard t :verify-guards nil))
  (append (list 70 76 66 1 (if (fn-rcl-tombstonep payload) 1 0))
          (fn-lb-log-model-nat-octets (fn-record-sequence row))))

(defun fn-lb-log-model-append-to-segment (row payload segment)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bytes (cadr segment)) (entries (caddr segment))
         (pre (fn-lb-log-model-pre row payload))
         (range (if (fn-rcl-tombstonep payload)
                    (fn-la-tombstone-raw payload) (fn-la-payload-wire payload)))
         (home (fn-lb-log-model-home-frame row))
         (prefix (append pre range home))
         (entry (list (len entries) (len bytes) (len prefix)
                      (+ (len bytes) (len pre)) (len range)
                      (fn-record-payload row) payload (fn-lb-log-model-homes row)
                      (fn-record-sequence row))))
    (list (car segment)
          (append bytes prefix (fn-blake3-stobj prefix))
          (append entries (list entry)))))

(defun fn-lb-log-model-append (row payload segment-id log)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp log)
      (if (equal segment-id (caar log))
          (cons (fn-lb-log-model-append-to-segment row payload (car log)) (cdr log))
        (cons (car log) (fn-lb-log-model-append row payload segment-id (cdr log))))
    (list (fn-lb-log-model-append-to-segment row payload (list segment-id nil nil)))))

(defun fn-lb-log-model-recycle (segment-id log)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp log)
      (if (equal segment-id (caar log)) (cdr log)
        (cons (car log) (fn-lb-log-model-recycle segment-id (cdr log))))
    nil))

(defun fn-lb-arena-is-log (fn-arena rows log)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  ;; every row's payload bytes in FN-ARENA are its stored payload in LOG
  (if (consp rows)
      (and (equal (fn-nntp-payload-bytes (fn-record-payload (car rows)) fn-arena)
                  (fn-lb-log-payload (car rows) log))
           (fn-lb-arena-is-log fn-arena (cdr rows) log))
    t))
