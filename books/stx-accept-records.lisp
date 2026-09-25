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
(defconst *fn-stxa-carried-version* 1)
(defconst *fn-stxa-kind* 4)
; Codec ceilings, never data bounds (D27).  The kind-4 composite embeds one
; encoded article record and, for a signed article, its authored source.
; Each child's bound is the width of the codec that carries it: the record
; codec's u32 (`*fn-record-max-octets*', books/records-shape) and the v2
; carrier's u32 source length (`*fn-hsig-v2-max-source*', equal to this one by
; `fn-stxa-authored-source-bound-is-the-v2-carrier-width', books/hybrid-store).
; The composite's own ceiling is the widest the frames that carry it accept:
; the Store frame's u32 payload less the consumer poll reply's 9 header octets
; and widest cursor (346, books/consumer-position), so every composite is a
; poll report the local-control frame carries.  How large an article a store
; admits is the operator's: the profile's A at the POST boundary
; (`fn-sbud-post-boundary') and its R over the encoded composite
; (`fn-sbud-signed-event-boundary', books/store-budget-naming).
(defconst *fn-stxa-max-octets* (- *fn-cbor-max-uint* (+ 9 346)))
(defconst *fn-stxa-max-article-record* *fn-record-max-octets*)
(defconst *fn-stxa-max-authored-source* *fn-cbor-max-uint*)
; Every item's CBOR budget: the widest byte string a u32 head can carry.  An
; item within the old 65,538 budget encodes to the same octets under it.
(defconst *fn-stxa-max-item* *fn-cbor-max-uint*)

(fn-defrecord fn-stxa
  :constructor (fn-stxa-make-full sequence txid generation keyring-generation
                                  profile content-subject article-record
                                  verdict-event authored-source authored-id)
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
                                     *fn-stxa-max-article-record*))
           (fn-stxa-verdict-event
            (fn-stxe-bounded-octetsp (fn-stxa-verdict-event x)
                                     *fn-stxe-max-octets*))
           (fn-stxa-authored-source
            (or (equal (fn-stxa-authored-source x) :legacy)
                (and (fn-cbor-octet-listp (fn-stxa-authored-source x))
                     (consp (fn-stxa-authored-source x))
                     (<= (len (fn-stxa-authored-source x))
                         *fn-stxa-max-authored-source*))))
           (fn-stxa-authored-id
            (if (equal (fn-stxa-authored-source x) :legacy)
                (null (fn-stxa-authored-id x))
              (fn-stxe-bounded-octetsp (fn-stxa-authored-id x)
                                       *fn-record-max-metadata*))))
  :recognizer fn-stxa-p)

; Existing kind-4 version-0 constructors and bytes remain unchanged.
(defun fn-stxa-make (sequence txid generation keyring-generation profile
                              content-subject article-record verdict-event)
  (declare (xargs :guard t))
  (fn-stxa-make-full sequence txid generation keyring-generation profile
                     content-subject article-record verdict-event :legacy nil))

(defun fn-stxa-make-carried
    (sequence txid generation keyring-generation profile content-subject
              article-record verdict-event authored-source authored-id)
  (declare (xargs :guard t))
  (fn-stxa-make-full sequence txid generation keyring-generation profile
                     content-subject article-record verdict-event
                     authored-source authored-id))

(defun fn-stxa-schema (e)
  (declare (xargs :guard t))
  (if (equal (fn-stxa-authored-source e) :legacy)
      *fn-stxa-version* *fn-stxa-carried-version*))

(defun fn-stxa-items (e)
  (declare (xargs :guard (fn-stxa-p e)))
  (append
   (list (cons :bytes *fn-stxa-magic*)
        (cons :uint (fn-stxa-schema e))
        (cons :uint *fn-stxa-kind*)
        (cons :uint (fn-stxa-sequence e))
        (cons :uint (fn-stxa-txid e))
        (cons :uint (fn-stxa-generation e))
        (cons :uint (fn-stxa-keyring-generation e))
        (cons :bytes (fn-stxa-profile e))
        (cons :bytes (fn-stxa-content-subject e))
        (cons :bytes (fn-stxa-article-record e))
         (cons :bytes (fn-stxa-verdict-event e)))
   (if (equal (fn-stxa-authored-source e) :legacy) nil
     (list (cons :bytes (fn-stxa-authored-source e))
           (cons :bytes (fn-stxa-authored-id e))))))

(defun fn-stxa-encode (e)
  (declare (xargs :guard t))
  (if (fn-stxa-p e)
      (fn-stxe-encode-items-bounded (fn-stxa-items e) *fn-stxa-max-item*)
    nil))

(defun fn-stxa-items-p (items)
  (declare (xargs :guard t))
  (and (true-listp items)
       (or (and (equal (len items) 11)
                (equal (fn-cbor-ag-cdr (nth 1 items)) *fn-stxa-version*))
           (and (equal (len items) 13)
                (equal (fn-cbor-ag-cdr (nth 1 items))
                       *fn-stxa-carried-version*)))
       (fn-stmt-bytes-item-p (nth 0 items))
       (equal (fn-cbor-ag-cdr (nth 0 items)) *fn-stxa-magic*)
       (fn-stmt-uint-item-p (nth 1 items))
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
                                *fn-stxa-max-article-record*)
       (fn-stmt-bytes-item-p (nth 10 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 10 items))
                                *fn-stxe-max-octets*)
       (or (equal (len items) 11)
           (and (fn-stmt-bytes-item-p (nth 11 items))
                (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 11 items))
                                         *fn-stxa-max-authored-source*)
                (consp (fn-cbor-ag-cdr (nth 11 items)))
                (fn-stmt-bytes-item-p (nth 12 items))
                (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 12 items))
                                         *fn-record-max-metadata*)))))

(defun fn-stxa-of-items (items)
  (declare (xargs :guard t))
  (if (not (fn-stxa-items-p items))
      (fn-stmt-error :accepted-article)
    (fn-stmt-ok
     (fn-stxa-make-full (fn-cbor-ag-cdr (nth 3 items))
                   (fn-cbor-ag-cdr (nth 4 items))
                   (fn-cbor-ag-cdr (nth 5 items))
                   (fn-cbor-ag-cdr (nth 6 items))
                   (fn-cbor-ag-cdr (nth 7 items))
                   (fn-cbor-ag-cdr (nth 8 items))
                   (fn-cbor-ag-cdr (nth 9 items))
                   (fn-cbor-ag-cdr (nth 10 items))
                   (if (equal (len items) 11) :legacy
                     (fn-cbor-ag-cdr (nth 11 items)))
                   (if (equal (len items) 11) nil
                     (fn-cbor-ag-cdr (nth 12 items)))))))

(defun fn-stxa-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxa-max-octets*))
      (fn-stmt-error :limit)
    (let ((decoded (fn-stmt-decode-items-bounded
                    13 octets *fn-stxa-max-octets* *fn-stxa-max-item*)))
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
