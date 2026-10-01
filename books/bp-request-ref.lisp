; PKT-646, PRF-249 (D27): a BP request by REFERENCE, never by copy.
;
; Every durable record of the BP application join (the FNRJ transit intent
; and context, books/bp-native-app.lisp) and the receiver's context
; (books/bp-receipt.lisp, slot 9) carry a request's REFERENCE
; (HEAD LENGTH DIGEST), never the request ADU: HEAD the ADU's eight metadata
; items encoded exactly as the ADU encodes them (`fn-bpa-encode-fields'; at
; most 8 x 259 octets by the ADU grammar), LENGTH and DIGEST the article's
; length and `fn-frame-digest' (A-CRYPTO, books/frame-octets).  The article's
; bytes are the held payload the delivery already made durable: the
; delivered bundle (the inbound identity) in the BP node's held journal
; while the delivery is held, and the Store record the context names
; (Message-ID, txid, generation) once the Store committed it.
;
; This book is the vocabulary and its keystone, low enough for the receiver
; to include: `fn-bpaj-ref-request' resolves a reference over held bytes,
; and `fn-bpaj-ref-request-resolves-exactly' is its exactness.  The names
; keep the join's prefix: they were the join's before the receiver needed
; them.
(in-package "ACL2")
(include-book "bp-adu")
(include-book "frame-octets")
(set-verify-guards-eagerness 0)

; The eight metadata items of a request, as the ADU encodes them.
(defun fn-bpaj-head-fields (request)
  (declare (xargs :guard t))
  (list (fn-record-string-octets (fn-bpa-request-work-id request))
        (fn-record-string-octets (fn-bpa-request-subject request))
        (fn-record-string-octets (fn-bpa-request-source-eid request))
        (fn-record-string-octets (fn-bpa-request-destination-eid request))
        (fn-record-string-octets (fn-bpa-request-policy-id request))
        (fn-record-string-octets (fn-bpa-request-incarnation request))
        (fn-record-string-octets (fn-bpa-request-auth-context request))
        (fn-record-string-octets (fn-bpa-request-terms-id request))))

(defun fn-bpaj-head-octets (request)
  (declare (xargs :guard t))
  (fn-bpa-encode-fields (fn-bpaj-head-fields request)))

; The metadata items HEAD encodes, or nil.
(defun fn-bpaj-head-read (head)
  (declare (xargs :guard t))
  (let ((parsed (and (fn-cbor-octet-listp head)
                     (fn-bpa-read-fields 8 head))))
    (and (fn-record-parse-okp parsed)
         (null (fn-record-parse-rest parsed))
         (fn-record-parse-value parsed))))

(defun fn-bpaj-head-metadatap (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-bpa-metadatap (fn-record-octets-string (car fields)))
           (fn-bpaj-head-metadatap (cdr fields)))
    (null fields)))

(defun fn-bpaj-headp (head)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and (equal (len fields) 8) (fn-bpaj-head-metadatap fields))))

(defun fn-bpaj-head-work-id (head)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and (consp fields) (fn-record-octets-string (car fields)))))

; The reference of a request message: (HEAD LENGTH DIGEST).
(defun fn-bpaj-request-ref (request)
  (declare (xargs :guard t))
  (list (fn-bpaj-head-octets request)
        (len (fn-bpa-request-article request))
        (fn-frame-digest (fn-bpa-request-article request))))

; RESOLUTION: the request message the reference names over ARTICLE, the
; held payload's bytes, or nil when ARTICLE is not the referenced one (its
; length or digest differs) or the whole is no request.
(defun fn-bpaj-ref-request (head length digest article)
  (declare (xargs :guard t))
  (let ((fields (fn-bpaj-head-read head)))
    (and fields
         (fn-cbor-octet-listp article)
         (equal (len article) length)
         (equal (fn-frame-digest article) digest)
         (let ((request (fn-bpa-request-from-fields
                         (append fields (list article)))))
           (and (fn-bpa-requestp request) request)))))

; A live request is the one an intent references: the same metadata, and an
; article of the same length and digest.
(defun fn-bpaj-request-ref-matchesp (request head length digest)
  (declare (xargs :guard t))
  (and (fn-bpa-requestp request)
       (equal (fn-bpaj-request-ref request) (list head length digest))))

; A reference's shape: a HEAD of eight metadata items, a LENGTH within the
; ADU's article bound, and a digest.
(defun fn-bpaj-request-refp (ref)
  (declare (xargs :guard t))
  (and (true-listp ref) (equal (len ref) 3)
       (fn-cbor-octet-listp (car ref))
       (fn-bpaj-headp (car ref))
       (natp (cadr ref))
       (<= (cadr ref) *fn-bpa-max-article*)
       (fn-frame-digestp (caddr ref))))

; The metadata a reference carries, read as a request whose article is
; empty: the receiver reads a context's metadata from here
; (`fn-bpr-context-from-ref'), never from the bytes.
(defun fn-bpaj-ref-metadata (ref)
  (declare (xargs :guard t))
  (fn-bpa-request-from-fields
   (append (fn-bpaj-head-read (and (consp ref) (car ref))) (list nil))))

; ----------------------------------------------------------------------------
; The keystone and its lemmas (moved from books/bp-request-reference.lisp).

(local (in-theory (enable fn-bpa-encoded-fields-are-octets)))

(local
 (defthm fn-bprf-append-nil-when-true-listp
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-bprf-encode-fields-true-listp
   (true-listp (fn-bpa-encode-fields fields))
   :hints (("Goal" :in-theory (disable fn-record-item-encode)))))

(local
 (defthm fn-bprf-byte-field-listp-of-append
   (implies (and (true-listp xs)
                 (fn-bpa-byte-field-listp (append xs ys)))
            (fn-bpa-byte-field-listp xs))
   :hints (("Goal" :in-theory (disable fn-record-payloadp)))))

(local
 (defthm fn-bprf-request-fields-are-head-and-article
   (equal (fn-bpa-request-fields request)
          (append (fn-bpaj-head-fields request)
                  (list (fn-bpa-request-article request))))
   :hints (("Goal" :in-theory (enable fn-bpa-request-fields
                                      fn-bpaj-head-fields)))))

(local
 (defthm fn-bprf-head-fields-byte-fields
   (implies (fn-bpa-requestp request)
            (fn-bpa-byte-field-listp (fn-bpaj-head-fields request)))
   :hints (("Goal"
            :use ((:instance fn-bpa-request-fields-domain)
                  (:instance fn-bprf-byte-field-listp-of-append
                             (xs (fn-bpaj-head-fields request))
                             (ys (list (fn-bpa-request-article request)))))
            :in-theory (disable fn-bpa-request-fields-domain
                                fn-bprf-byte-field-listp-of-append
                                fn-bpaj-head-fields fn-bpa-requestp
                                fn-bpa-byte-field-listp)))))

(local
 (defthm fn-bprf-head-fields-len
   (equal (len (fn-bpaj-head-fields request)) 8)))

(local
 (defthm fn-bprf-head-read-of-head-octets
   (implies (fn-bpa-requestp request)
            (equal (fn-bpaj-head-read (fn-bpaj-head-octets request))
                   (fn-bpaj-head-fields request)))
   :hints (("Goal"
            :use ((:instance fn-bpa-read-encoded-fields-wide
                             (fields (fn-bpaj-head-fields request))
                             (rest nil)))
            :in-theory (e/d (fn-bpaj-head-read fn-bpaj-head-octets)
                            (fn-bpa-read-encoded-fields-wide
                             fn-bpaj-head-fields fn-bpa-requestp
                             fn-bpa-read-fields fn-bpa-encode-fields))))))

(local
 (defthm fn-bprf-request-article-octets
   (implies (fn-bpa-requestp request)
            (fn-cbor-octet-listp (fn-bpa-request-article request)))
   :hints (("Goal" :in-theory (enable fn-bpa-requestp fn-record-payloadp)))))

(local
 (defthm fn-bprf-head-fields-consp
   (consp (fn-bpaj-head-fields request))))

; KEYSTONE.  A request's reference resolves over its own article to it.
(defthm fn-bpaj-ref-request-resolves-exactly
  (implies (fn-bpa-requestp request)
           (equal (fn-bpaj-ref-request
                   (car (fn-bpaj-request-ref request))
                   (cadr (fn-bpaj-request-ref request))
                   (caddr (fn-bpaj-request-ref request))
                   (fn-bpa-request-article request))
                  request))
  :hints (("Goal"
           :use ((:instance fn-bpa-request-fields-reconstruct)
                 (:instance fn-bprf-request-fields-are-head-and-article)
                 (:instance fn-bprf-request-article-octets))
           :in-theory (e/d (fn-bpaj-ref-request fn-bpaj-request-ref)
                           (fn-bpa-request-fields-reconstruct
                            fn-bprf-request-article-octets fn-bpa-request-article
                            fn-bprf-request-fields-are-head-and-article
                            fn-bpaj-head-read fn-bpaj-head-octets
                            fn-bpaj-head-fields fn-bpa-requestp
                            fn-bpa-request-from-fields
                            fn-bpa-request-fields)))))

(local
 (defthm fn-bprf-metadata-round-trip
   (implies (fn-bpa-metadatap m)
            (equal (fn-record-octets-string (fn-record-string-octets m)) m))
   :hints (("Goal" :use ((:instance fn-record-string-round-trip (text m)))
            :in-theory (e/d (fn-bpa-metadatap)
                            (fn-record-string-round-trip
                             fn-record-string-octets fn-record-octets-string
                             fn-record-octet-stringp))))))
(local
 (defthm fn-bprf-head-fields-metadata
   (implies (fn-bpa-requestp request)
            (fn-bpaj-head-metadatap (fn-bpaj-head-fields request)))
   :hints (("Goal" :in-theory (e/d (fn-bpaj-head-fields fn-bpaj-head-metadatap
                                    fn-bpa-requestp)
                                   (fn-bpa-metadatap fn-record-string-octets
                                    fn-record-octets-string))))))
(local
 (defthm fn-bprf-request-article-bound
   (implies (fn-bpa-requestp request)
            (<= (len (fn-bpa-request-article request)) *fn-bpa-max-article*))
   :hints (("Goal" :in-theory (enable fn-bpa-requestp)))))
; The reference of a request is a reference.
(defthm fn-bpaj-request-ref-is-a-reference
  (implies (fn-bpa-requestp request)
           (fn-bpaj-request-refp (fn-bpaj-request-ref request)))
  :hints (("Goal" :use ((:instance fn-bprf-head-read-of-head-octets)
                        (:instance fn-bprf-head-fields-metadata)
                        (:instance fn-bprf-request-article-octets)
                        (:instance fn-bprf-request-article-bound))
           :in-theory (e/d (fn-bpaj-request-ref fn-bpaj-headp fn-bpaj-head-octets
                            fn-frame-digestp)
                           (fn-bprf-request-article-bound fn-bpa-request-article fn-bprf-head-read-of-head-octets
                            fn-bprf-head-fields-metadata
                            fn-bprf-request-article-octets
                            fn-bpaj-head-read fn-bpaj-head-fields
                            fn-bpaj-head-metadatap fn-bpa-requestp)))))
; The metadata a request's reference carries is the request's.
(defthm fn-bpaj-ref-metadata-of-request-ref
  (implies (fn-bpa-requestp request)
           (let ((m (fn-bpaj-ref-metadata (fn-bpaj-request-ref request))))
             (and (equal (fn-bpa-request-work-id m)
                         (fn-bpa-request-work-id request))
                  (equal (fn-bpa-request-subject m)
                         (fn-bpa-request-subject request))
                  (equal (fn-bpa-request-source-eid m)
                         (fn-bpa-request-source-eid request))
                  (equal (fn-bpa-request-destination-eid m)
                         (fn-bpa-request-destination-eid request))
                  (equal (fn-bpa-request-policy-id m)
                         (fn-bpa-request-policy-id request))
                  (equal (fn-bpa-request-incarnation m)
                         (fn-bpa-request-incarnation request))
                  (equal (fn-bpa-request-auth-context m)
                         (fn-bpa-request-auth-context request))
                  (equal (fn-bpa-request-terms-id m)
                         (fn-bpa-request-terms-id request)))))
  :hints (("Goal" :use ((:instance fn-bprf-head-read-of-head-octets))
           :in-theory (e/d (fn-bpaj-ref-metadata fn-bpaj-request-ref
                            fn-bpaj-head-fields fn-bpa-request-from-fields
                            fn-bpa-requestp)
                           (fn-bprf-head-read-of-head-octets
                            fn-bpaj-head-read fn-bpaj-head-octets
                            fn-bpa-metadatap fn-record-string-octets
                            fn-record-octets-string)))))
(local
 (defthm fn-bprf-head-metadatap-nth
   (implies (and (fn-bpaj-head-metadatap fs) (natp i) (< i (len fs)))
            (fn-bpa-metadatap (fn-record-octets-string (fn-bpa-nth i fs))))
   :hints (("Goal" :induct (fn-bpa-nth i fs)
            :in-theory (e/d (fn-bpa-nth fn-bpa-car fn-bpa-cdr)
                            (fn-bpa-metadatap fn-record-octets-string))))))
(local
 (defthm fn-bprf-nth-of-append-short
   (implies (and (natp i) (< i (len xs)))
            (equal (fn-bpa-nth i (append xs ys)) (fn-bpa-nth i xs)))
   :hints (("Goal" :induct (fn-bpa-nth i xs)
            :in-theory (enable fn-bpa-nth fn-bpa-car fn-bpa-cdr)))))
; Every metadata item a reference carries is a metadata item.
(defthm fn-bpaj-ref-metadata-is-metadata
  (implies (fn-bpaj-request-refp ref)
           (let ((m (fn-bpaj-ref-metadata ref)))
             (and (fn-bpa-metadatap (fn-bpa-request-work-id m))
                  (fn-bpa-metadatap (fn-bpa-request-subject m))
                  (fn-bpa-metadatap (fn-bpa-request-source-eid m))
                  (fn-bpa-metadatap (fn-bpa-request-destination-eid m))
                  (fn-bpa-metadatap (fn-bpa-request-policy-id m))
                  (fn-bpa-metadatap (fn-bpa-request-incarnation m))
                  (fn-bpa-metadatap (fn-bpa-request-auth-context m))
                  (fn-bpa-metadatap (fn-bpa-request-terms-id m)))))
  :hints (("Goal"
           :use ((:instance fn-bprf-head-metadatap-nth (i 0) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 1) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 2) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 3) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 4) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 5) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 6) (fs (fn-bpaj-head-read (car ref))))
                 (:instance fn-bprf-head-metadatap-nth (i 7) (fs (fn-bpaj-head-read (car ref)))))
           :in-theory (e/d (fn-bpaj-ref-metadata fn-bpaj-request-refp fn-bpaj-headp
                            fn-bpa-request-from-fields)
                           (fn-bprf-head-metadatap-nth fn-bpaj-head-read
                            fn-bpaj-head-metadatap fn-bpa-metadatap
                            fn-record-octets-string)))))
(in-theory (disable fn-bpaj-request-refp fn-bpaj-ref-metadata))
