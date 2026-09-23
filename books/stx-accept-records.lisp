; fn: atomic accepted-article plus historical-verdict Store event.
;
; fn-e version 0 kind 4 contains the exact legacy fn-r bytes and the exact
; kind-2 verdict bytes under one parent sequence/transaction/generation.  A
; Store implementation appends and frames this parent once.  Standalone kind
; 2 remains evidence and is not an accepted-article historical verdict.

(in-package "ACL2")
(include-book "stx-keyring-records")
(include-book "records-seam")
(local (in-theory (enable fn-record-record-vocabulary
                          fn-record-codec-vocabulary)))

(defconst *fn-stxa-magic* '(102 110 45 101)) ; "fn-e"
(defconst *fn-stxa-version* 0)
(defconst *fn-stxa-kind* 4)
(defconst *fn-stxa-max-octets* 196608)

(fn-defrecord fn-stxa
  :constructor (fn-stxa-make sequence txid generation keyring-generation
                             profile content-subject article-record verdict-event)
  :fields ((fn-stxa-sequence fn-record-uint32p)
           (fn-stxa-txid fn-record-uint32p)
           (fn-stxa-generation fn-record-uint32p)
           (fn-stxa-keyring-generation fn-record-uint32p)
           (fn-stxa-profile
            (fn-stxe-bounded-octetsp (fn-stxa-profile x)
                                     *fn-stxk-max-profile*))
           (fn-stxa-content-subject
            (fn-stxe-bounded-octetsp (fn-stxa-content-subject x)
                                     *fn-record-max-metadata*))
           (fn-stxa-article-record
            (fn-stxe-bounded-octetsp (fn-stxa-article-record x)
                                     *fn-record-max-octets*))
           (fn-stxa-verdict-event
            (fn-stxe-bounded-octetsp (fn-stxa-verdict-event x)
                                     *fn-stxe-max-octets*)))
  :recognizer fn-stxa-p)

(defun fn-stxa-items (e)
  (declare (xargs :guard (fn-stxa-p e)))
  (list (cons :bytes *fn-stxa-magic*)
        (cons :uint *fn-stxa-version*)
        (cons :uint *fn-stxa-kind*)
        (cons :uint (fn-stxa-sequence e))
        (cons :uint (fn-stxa-txid e))
        (cons :uint (fn-stxa-generation e))
        (cons :uint (fn-stxa-keyring-generation e))
        (cons :bytes (fn-stxa-profile e))
        (cons :bytes (fn-stxa-content-subject e))
        (cons :bytes (fn-stxa-article-record e))
        (cons :bytes (fn-stxa-verdict-event e))))

(defun fn-stxa-encode (e)
  (declare (xargs :guard t))
  (if (fn-stxa-p e)
      (fn-stxe-encode-items-bounded (fn-stxa-items e) *fn-stxe-max-octets*)
    nil))

(defun fn-stxa-items-p (items)
  (declare (xargs :guard t))
  (and (true-listp items) (equal (len items) 11)
       (fn-stmt-bytes-item-p (nth 0 items))
       (equal (fn-cbor-ag-cdr (nth 0 items)) *fn-stxa-magic*)
       (fn-stmt-uint-item-p (nth 1 items))
       (equal (fn-cbor-ag-cdr (nth 1 items)) *fn-stxa-version*)
       (fn-stmt-uint-item-p (nth 2 items))
       (equal (fn-cbor-ag-cdr (nth 2 items)) *fn-stxa-kind*)
       (fn-stmt-uint-item-p (nth 3 items))
       (fn-stmt-uint-item-p (nth 4 items))
       (fn-stmt-uint-item-p (nth 5 items))
       (fn-stmt-uint-item-p (nth 6 items))
       (fn-stmt-bytes-item-p (nth 7 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 7 items))
                                *fn-stxk-max-profile*)
       (fn-stmt-bytes-item-p (nth 8 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 8 items))
                                *fn-record-max-metadata*)
       (fn-stmt-bytes-item-p (nth 9 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 9 items))
                                *fn-record-max-octets*)
       (fn-stmt-bytes-item-p (nth 10 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 10 items))
                                *fn-stxe-max-octets*)))

(defun fn-stxa-of-items (items)
  (declare (xargs :guard t))
  (if (not (fn-stxa-items-p items))
      (fn-stmt-error :accepted-article)
    (fn-stmt-ok
     (fn-stxa-make (fn-cbor-ag-cdr (nth 3 items))
                   (fn-cbor-ag-cdr (nth 4 items))
                   (fn-cbor-ag-cdr (nth 5 items))
                   (fn-cbor-ag-cdr (nth 6 items))
                   (fn-cbor-ag-cdr (nth 7 items))
                   (fn-cbor-ag-cdr (nth 8 items))
                   (fn-cbor-ag-cdr (nth 9 items))
                   (fn-cbor-ag-cdr (nth 10 items))))))

(defun fn-stxa-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxa-max-octets*))
      (fn-stmt-error :limit)
    (let ((decoded (fn-stmt-decode-items-bounded
                    11 octets *fn-stxa-max-octets* *fn-stxe-max-octets*)))
      (if (not (fn-stmt-okp decoded))
          decoded
        (fn-stxa-of-items (fn-stmt-value decoded))))))

; One ACL2-owned binding check for the dispatcher and replay.  It prevents
; substitution of an article, verdict, profile or keyring generation beneath
; a valid parent.  The raw child encodings are retained and must be canonical;
; the host neither computes nor compares any of these fields.
(defun fn-stxa-bindsp (e)
  (declare (xargs :guard t))
  (and
   (fn-stxa-p e)
   (let* ((rr (fn-record-decode-exact (fn-stxa-article-record e)))
          (vr (fn-stxe-decode-exact (fn-stxa-verdict-event e))))
     (and (fn-record-result-okp rr)
          (fn-stmt-okp vr)
          (let ((record (fn-record-result-record rr))
                (verdict (fn-stmt-value vr)))
            (and (fn-record-p record)
                 (fn-stxe-p verdict)
                 (equal (fn-record-encode record)
                        (fn-stxa-article-record e))
                 (equal (fn-stxe-encode verdict)
                        (fn-stxa-verdict-event e))
                 (equal (fn-stxa-sequence e) (fn-record-sequence record))
                 (equal (fn-stxa-sequence e) (fn-stxe-sequence verdict))
                 (equal (fn-stxa-txid e) (fn-record-txid record))
                 (equal (fn-stxa-txid e) (fn-stxe-txid verdict))
                 (equal (fn-stxa-generation e)
                        (fn-record-generation record))
                 (equal (fn-stxa-generation e)
                        (fn-stxe-generation verdict))
                 (equal (fn-record-msgid record) (fn-stxe-msgid verdict))
                 (equal (fn-stxa-keyring-generation e)
                        (fn-stxe-keyring-generation verdict))
                 (equal (fn-stxa-profile e) (fn-stxe-profile verdict))
                 (equal (fn-stxa-content-subject e)
                        (fn-record-string-octets
                         (fn-record-content-subject record)))))))))

(in-theory (disable (:d fn-stxa-items) (:d fn-stxa-encode)
                    (:d fn-stxa-items-p) (:d fn-stxa-of-items)
                    (:d fn-stxa-decode-exact) (:d fn-stxa-bindsp)))
