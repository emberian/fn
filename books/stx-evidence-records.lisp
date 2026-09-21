; fn: durable statement-verdict event payload for the Store event sum.
;
; The outer Store envelope is `fn-e`, version 0, kind 2.  This book owns the
; kind-2 payload and nothing in the legacy `fn-r` article-record grammar.
; Unknown profile tags are preserved as bytes.  They are evidence, never
; authority: fn-stxe-profile-supportedp is deliberately false until D09
; selects a production signature profile.

(in-package "ACL2")
(include-book "stx-lace")
(include-book "defrecord")

(defconst *fn-stxe-magic* '(102 110 45 101)) ; "fn-e"
(defconst *fn-stxe-version* 0)
(defconst *fn-stxe-kind* 2)
(defconst *fn-stxe-max-octets* 65538)
(defconst *fn-stxe-max-profile* 64)
(defconst *fn-stxe-max-detail* 8192)

(defun fn-stxe-tokenp (x)
  (declare (xargs :guard t))
  (member-equal x *fn-stx-verdicts*))

(defun fn-stxe-token-code (x)
  (declare (xargs :guard t))
  (cond ((equal x :verified) 1)
        ((equal x :unverified) 2)
        ((equal x :absent) 3)
        (t 0)))

(defun fn-stxe-code-token (x)
  (declare (xargs :guard t))
  (cond ((equal x 1) :verified)
        ((equal x 2) :unverified)
        ((equal x 3) :absent)
        (t nil)))

(defun fn-stxe-bounded-octetsp (x bound)
  (declare (xargs :guard (natp bound)))
  (and (fn-cbor-octet-listp x) (consp x) (<= (len x) bound)))

(fn-defrecord fn-stxe
  :constructor (fn-stxe-make sequence txid generation msgid token detail
                             keyring-generation profile)
  :fields ((fn-stxe-sequence fn-record-uint32p)
           (fn-stxe-txid fn-record-uint32p)
           (fn-stxe-generation fn-record-uint32p)
           (fn-stxe-msgid fn-record-msgidp)
           (fn-stxe-token fn-stxe-tokenp)
           (fn-stxe-detail
            (fn-stxe-bounded-octetsp (fn-stxe-detail x)
                                     *fn-stxe-max-detail*))
           (fn-stxe-keyring-generation fn-record-uint32p)
           (fn-stxe-profile
            (fn-stxe-bounded-octetsp (fn-stxe-profile x)
                                     *fn-stxe-max-profile*)))
  :recognizer fn-stxe-p)

; D09 remains open.  A decoder must retain an unknown tag, while every
; authority consumer must refuse it until a selected profile is registered.
(defun fn-stxe-profile-supportedp (profile)
  (declare (ignore profile) (xargs :guard t))
  nil)

(defun fn-stxe-authority-verdict (e)
  (declare (xargs :guard t))
  (if (and (fn-stxe-p e)
           (fn-stxe-profile-supportedp (fn-stxe-profile e)))
      (fn-stxe-token e)
    :unsupported-profile))

(defun fn-stxe-verdict-detail-octets (verdict)
  (declare (xargs :guard t))
  (if (equal (fn-stx-verdict-token verdict) :verified)
      (let ((detail (fn-stx-verdict-detail verdict)))
        (if (fn-stxe-bounded-octetsp detail *fn-stxe-max-detail*)
            detail
          *fn-stx-token-unknown*))
    (fn-stx-reason-token (fn-stx-verdict-detail verdict))))

(defun fn-stxe-from-verdict (sequence txid generation msgid verdict profile)
  (declare (xargs :guard t))
  (fn-stxe-make sequence txid generation msgid
                (fn-stx-verdict-token verdict)
                (fn-stxe-verdict-detail-octets verdict)
                (fn-stx-verdict-generation verdict)
                profile))

(defun fn-stxe-items (e)
  (declare (xargs :guard (fn-stxe-p e)))
  (list (cons :bytes *fn-stxe-magic*)
        (cons :uint *fn-stxe-version*)
        (cons :uint *fn-stxe-kind*)
        (cons :uint (fn-stxe-sequence e))
        (cons :uint (fn-stxe-txid e))
        (cons :uint (fn-stxe-generation e))
        (cons :bytes (fn-record-string-octets (fn-stxe-msgid e)))
        (cons :uint (fn-stxe-token-code (fn-stxe-token e)))
        (cons :bytes (fn-stxe-detail e))
        (cons :uint (fn-stxe-keyring-generation e))
        (cons :bytes (fn-stxe-profile e))))

(defun fn-stxe-encode-items (items)
  (declare (xargs :guard t))
  (if (consp items)
      (append (fn-cbor-encode (car items))
              (fn-stxe-encode-items (cdr items)))
    nil))

(defun fn-stxe-encode-items-bounded (items item-budget)
  (declare (xargs :guard (natp item-budget)))
  (if (consp items)
      (append (fn-cbor-encode-bounded (car items) item-budget)
              (fn-stxe-encode-items-bounded (cdr items) item-budget))
    nil))

(defun fn-stxe-encode (e)
  (declare (xargs :guard t))
  (if (fn-stxe-p e) (fn-stxe-encode-items (fn-stxe-items e)) nil))

(defun fn-stxe-items-p (items)
  (declare (xargs :guard t))
  (and (true-listp items) (equal (len items) 11)
       (fn-stmt-bytes-item-p (nth 0 items))
       (equal (fn-cbor-ag-cdr (nth 0 items)) *fn-stxe-magic*)
       (fn-stmt-uint-item-p (nth 1 items))
       (equal (fn-cbor-ag-cdr (nth 1 items)) *fn-stxe-version*)
       (fn-stmt-uint-item-p (nth 2 items))
       (equal (fn-cbor-ag-cdr (nth 2 items)) *fn-stxe-kind*)
       (fn-stmt-uint-item-p (nth 3 items))
       (fn-stmt-uint-item-p (nth 4 items))
       (fn-stmt-uint-item-p (nth 5 items))
       (fn-stmt-bytes-item-p (nth 6 items))
       (fn-record-msgidp (fn-record-octets-string (fn-cbor-ag-cdr (nth 6 items))))
       (fn-stmt-uint-item-p (nth 7 items))
       (fn-stxe-tokenp (fn-stxe-code-token (fn-cbor-ag-cdr (nth 7 items))))
       (fn-stmt-bytes-item-p (nth 8 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 8 items)) *fn-stxe-max-detail*)
       (fn-stmt-uint-item-p (nth 9 items))
       (fn-stmt-bytes-item-p (nth 10 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 10 items)) *fn-stxe-max-profile*)))

(defun fn-stxe-of-items (items)
  (declare (xargs :guard t))
  (if (not (fn-stxe-items-p items))
      (fn-stmt-error :statement-verdict)
    (fn-stmt-ok
     (fn-stxe-make (fn-cbor-ag-cdr (nth 3 items))
                   (fn-cbor-ag-cdr (nth 4 items))
                   (fn-cbor-ag-cdr (nth 5 items))
                   (fn-record-octets-string (fn-cbor-ag-cdr (nth 6 items)))
                   (fn-stxe-code-token (fn-cbor-ag-cdr (nth 7 items)))
                   (fn-cbor-ag-cdr (nth 8 items))
                   (fn-cbor-ag-cdr (nth 9 items))
                   (fn-cbor-ag-cdr (nth 10 items))))))

(defun fn-stxe-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxe-max-octets*))
      (fn-stmt-error :limit)
    (let ((decoded (fn-stmt-decode-items 11 octets)))
      (if (not (fn-stmt-okp decoded))
          decoded
        (fn-stxe-of-items (fn-stmt-value decoded))))))

(in-theory (disable (:d fn-stxe-tokenp) (:d fn-stxe-token-code)
                    (:d fn-stxe-code-token) (:d fn-stxe-bounded-octetsp)
                    (:d fn-stxe-profile-supportedp)
                    (:d fn-stxe-authority-verdict)
                    (:d fn-stxe-verdict-detail-octets)
                    (:d fn-stxe-from-verdict) (:d fn-stxe-items)
                    (:d fn-stxe-encode-items) (:d fn-stxe-encode-items-bounded)
                    (:d fn-stxe-encode) (:d fn-stxe-items-p)
                    (:d fn-stxe-of-items) (:d fn-stxe-decode-exact)))
