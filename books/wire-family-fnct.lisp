; fn: the FNCT control frame as the wire-grammar `frame' node (Mini M5,
; planning/design/wire-grammar-2026-10-04.md section 4, families 3).
;
; Every FNCT family the host speaks is fn-frame-protected PAYLOAD followed by
; the BLAKE3 trailer of it (books/frame-fields.lisp, books/native-control.lisp
; fn-nctrl-seal), opened by fn-frame-decode against the trailer of its own
; protected prefix.  This book proves, once, that this framing IS the
; interpreter's :frame node:
;
;   fn-wf-fnct-encode-is-host-framing   fn-wg-encode at the :frame grammar is
;                                       the host's protected prefix of the
;                                       payload encoding, then its digest;
;   fn-wf-fnct-decode-inversion         a frame the host opens is the sealing
;                                       of the fields it answers (canonicity
;                                       of the host's framing);
;   fn-wf-fnct-wg-accept-is-host-open,
;   fn-wf-fnct-host-open-is-wg-accept   the two readers agree on a whole frame;
;
; so each family book (wire-family-consumer, ...) proves only its payload
; agreement and instantiates these.
;
; This book owns the prefix `fn-wf-fnct-' (with the other `fn-wf-' books).

(in-package "ACL2")
(include-book "wire-grammar")
(include-book "wire-family-fncu") ; fn-wf-be-bytes-4
(include-book "native-control")

(defthm fn-wf-fnct-protected-is-wg
  (implies (and (true-listp magic) (natp (len p)) (< (len p) 4294967296))
           (equal (fn-wg-frame-protected magic version kind p)
                  (fn-frame-protected magic version kind p)))
  :hints (("Goal" :in-theory (enable fn-wg-frame-protected fn-frame-protected fn-frame-header
                                     fn-wg-app-is-append))))

(local
 (defthm fn-wf-fnct-len-10
   (implies (and (true-listp head) (equal (len head) 10))
            (equal (list (nth 0 head) (nth 1 head) (nth 2 head) (nth 3 head) (nth 4 head)
                         (nth 5 head) (nth 6 head) (nth 7 head) (nth 8 head) (nth 9 head))
                   head))
   :rule-classes nil
   :hints (("Goal" :expand ((nth 0 head) (nth 1 head) (nth 2 head) (nth 3 head) (nth 4 head)
                            (nth 5 head) (nth 6 head) (nth 7 head) (nth 8 head) (nth 9 head)
                            (len head) (len (cdr head)) (len (cddr head)) (len (cdddr head))
                            (len (cddddr head)) (len (cdr (cddddr head)))
                            (len (cddr (cddddr head))) (len (cdddr (cddddr head)))
                            (len (cddddr (cddddr head))) (len (cdr (cddddr (cddddr head))))
                            (len (cddr (cddddr (cddddr head)))))))))

(local
 (defthm fn-wf-fnct-head-fields-of-list
   (implies (and (fn-cbor-octetp a) (fn-cbor-octetp b) (fn-cbor-octetp c) (fn-cbor-octetp d)
                 (fn-cbor-octetp e) (fn-cbor-octetp f) (fn-cbor-octetp g) (fn-cbor-octetp h)
                 (fn-cbor-octetp i) (fn-cbor-octetp j))
            (equal (fn-frame-header
                    (fn-frame-item 0 (fn-frame-head-fields (list a b c d e f g h i j)))
                    (fn-frame-item 1 (fn-frame-head-fields (list a b c d e f g h i j)))
                    (fn-frame-item 2 (fn-frame-head-fields (list a b c d e f g h i j)))
                    (fn-cbor-u32-from
                     (fn-frame-item 3 (fn-frame-head-fields (list a b c d e f g h i j)))))
                   (list a b c d e f g h i j)))
   :hints (("Goal" :in-theory (enable fn-frame-head-fields fn-frame-header fn-frame-item
                                      fn-frame-split fn-cbor-octet-listp)
            :use ((:instance fn-frame-u32-bytes-of-u32-from (xs (list g h i j))))))))

(local
 (defthm fn-wf-fnct-octetp-of-nth
   (implies (and (fn-cbor-octet-listp x) (< (nfix i) (len x))) (fn-cbor-octetp (nth i x)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp nth)))))

(defthm fn-wf-fnct-head-fields-inversion
  (implies (and (fn-cbor-octet-listp head) (equal (len head) 10))
           (let ((f (fn-frame-head-fields head)))
             (equal (fn-frame-header (fn-frame-item 0 f) (fn-frame-item 1 f) (fn-frame-item 2 f)
                                     (fn-cbor-u32-from (fn-frame-item 3 f)))
                    head)))
  :hints (("Goal" :use (fn-wf-fnct-len-10
                        (:instance fn-wf-fnct-head-fields-of-list
                                   (a (nth 0 head)) (b (nth 1 head)) (c (nth 2 head))
                                   (d (nth 3 head)) (e (nth 4 head)) (f (nth 5 head))
                                   (g (nth 6 head)) (h (nth 7 head)) (i (nth 8 head))
                                   (j (nth 9 head))))
           :in-theory (disable fn-wf-fnct-head-fields-of-list fn-frame-head-fields
                               fn-frame-header fn-cbor-u32-from))))

(defthm fn-wf-fnct-decode-ok-facts
  (let* ((r (fn-frame-decode x digest mx))
         (h (car (fn-frame-split 10 x)))
         (tl (cdr (fn-frame-split 10 x)))
         (f (fn-frame-head-fields h))
         (n (nfix (fn-cbor-u32-from (fn-frame-item 3 f))))
         (b (fn-frame-split n tl)))
    (implies (fn-frame-result-okp r)
             (and (fn-cbor-octet-listp x)
                  (fn-frame-split 10 x)
                  f
                  b
                  (equal (cdr b) digest)
                  (equal (fn-frame-result-magic r) (fn-frame-item 0 f))
                  (equal (fn-frame-result-version r) (fn-frame-item 1 f))
                  (equal (fn-frame-result-kind r) (fn-frame-item 2 f))
                  (equal (fn-frame-result-payload r) (car b)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-frame-decode fn-frame-ok fn-frame-result-magic
                                   fn-frame-result-version fn-frame-result-kind
                                   fn-frame-result-payload fn-frame-item)
                                  (fn-frame-head-fields fn-cbor-u32-from fn-frame-split)))))

; Canonicity of the host's framing: an opened frame is its fields, sealed.
(defthm fn-wf-fnct-decode-inversion
  (let ((r (fn-frame-decode x digest mx)))
    (implies (fn-frame-result-okp r)
             (equal (append (fn-frame-protected (fn-frame-result-magic r) (fn-frame-result-version r)
                                                (fn-frame-result-kind r) (fn-frame-result-payload r))
                            digest)
                    x)))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-fnct-decode-ok-facts
                 (:instance fn-wf-fnct-head-fields-inversion (head (car (fn-frame-split 10 x))))
                 (:instance fn-frame-split-reassembles (n 10) (xs x))
                 (:instance fn-frame-split-prefix-octets (n 10) (xs x))
                 (:instance fn-frame-split-prefix-len (n 10) (xs x))
                 (:instance fn-frame-split-suffix-true-listp (n 10) (xs x))
                 (:instance fn-frame-head-fields-shape (head (car (fn-frame-split 10 x))))
                 (:instance fn-frame-u32-from-is-natural
                            (xs (fn-frame-item 3 (fn-frame-head-fields (car (fn-frame-split 10 x))))))
                 (:instance fn-frame-split-prefix-len
                            (n (nfix (fn-cbor-u32-from (fn-frame-item 3 (fn-frame-head-fields
                                                                         (car (fn-frame-split 10 x)))))))
                            (xs (cdr (fn-frame-split 10 x))))
                 (:instance fn-frame-split-reassembles
                            (n (nfix (fn-cbor-u32-from (fn-frame-item 3 (fn-frame-head-fields
                                                                         (car (fn-frame-split 10 x)))))))
                            (xs (cdr (fn-frame-split 10 x)))))
           :in-theory (e/d (fn-frame-protected)
                           (fn-wf-fnct-head-fields-inversion fn-frame-split-reassembles
                            fn-frame-split-prefix-octets fn-frame-split-prefix-len
                            fn-frame-head-fields-shape fn-frame-u32-from-is-natural
                            fn-frame-split-suffix-true-listp fn-frame-decode fn-frame-header
                            fn-frame-head-fields fn-cbor-u32-from fn-frame-split)))))

(defthm fn-wf-fnct-encode-is-host-framing
  (implies (and (fn-wg-grammarp g) (fn-wg-valuep g v)
                (< (len (fn-wg-encode g v)) 4294967296))
           (equal (fn-wg-encode (list :frame (list 70 78 67 84) 1 k mx g) v)
                  (append (fn-frame-protected (list 70 78 67 84) 1 k (fn-wg-encode g v))
                          (fn-frame-digest (fn-frame-protected (list 70 78 67 84) 1 k
                                                               (fn-wg-encode g v))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-wg-encode-opener-frame fn-wg-arg fn-wg-app-is-append)
                           (fn-wg-encode fn-frame-protected))
           :use ((:instance fn-wf-fnct-protected-is-wg (magic (list 70 78 67 84)) (version 1)
                            (kind k) (p (fn-wg-encode g v)))
                 fn-wg-encode-octets
                 (:instance fn-frame-protected-true-listp (magic (list 70 78 67 84)) (version 1)
                            (kind k) (payload (fn-wg-encode g v)))))))

(defthm fn-wf-fnct-frame-facts
  (implies (and (fn-wg-grammarp g) (fn-cbor-octetp k) (natp mx) (< mx 4294967296))
           (and (fn-wg-grammarp (list :frame (list 70 78 67 84) 1 k mx g))
                (equal (fn-wg-valuep (list :frame (list 70 78 67 84) 1 k mx g) v)
                       (and (fn-wg-valuep g v) (<= (len (fn-wg-encode g v)) mx)))))
  :hints (("Goal" :in-theory (enable fn-wg-grammarp-opener-frame fn-wg-valuep-opener-frame
                                     fn-wg-arg fn-wg-limit fn-cbor-octetp))))

; -----------------------------------------------------------------------------
; Agreement of the two readers of a whole FNCT frame.  The host opens a frame
; with the trailer it re-derives over the frame's own protected prefix
; (fn-frame-trailer of fn-frame-protected-prefix, books/frame-trailer.lisp);
; the interpreter reads it at the :frame grammar.  For every well-formed
; payload grammar G, any kind and any MX the host's cap HM covers:
;
;   fn-wf-fnct-wg-accept-is-host-open   the interpreter accepts X whole as V
;                                       => the host opens X, payload = the
;                                       encoding of V;
;   fn-wf-fnct-host-open-is-wg-accept   the host opens X with payload P and G
;                                       accepts P whole as V within MX
;                                       => the interpreter accepts X whole as V.
;
; So a family book proves only that its host payload codec is G's
; (fn-wg-encode / fn-wg-decode at G) and the frame-level agreement follows.

(defthm fn-wf-fnct-whole-accept-is-encoding
  (implies (and (fn-wg-grammarp f) (fn-cbor-octet-listp x)
                (equal (fn-wg-decode f x) (fn-wg-ok v nil)))
           (and (fn-wg-valuep f v)
                (equal (fn-wg-encode f v) x)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wg-encode-of-decode (g f) (xs x))
                 (:instance fn-wg-encode-octets (g f)))
           :in-theory (disable fn-wg-encode-of-decode fn-wg-encode-octets
                               fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp))))

(defthm fn-wf-fnct-wg-accept-is-host-open
  (implies (and (fn-wg-grammarp g) (fn-cbor-octetp k) (natp mx) (< mx 4294967296)
                (fn-cbor-octet-listp x)
                (equal (fn-wg-decode (list :frame (list 70 78 67 84) 1 k mx g) x) (fn-wg-ok v nil))
                (natp hm) (<= mx hm) (<= hm 4294967295))
           (equal (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm)
                  (fn-frame-ok (list 70 78 67 84) 1 k (fn-wg-encode g v))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-whole-accept-is-encoding (f (list :frame (list 70 78 67 84) 1 k mx g)))
                 (:instance fn-wf-fnct-frame-facts)
                 (:instance fn-wf-fnct-encode-is-host-framing)
                 (:instance fn-wg-encode-octets)
                 (:instance fn-frame-decode-of-host-framing (magic (list 70 78 67 84)) (version 1) (kind k)
                            (payload (fn-wg-encode g v)) (max-payload hm))
                 (:instance fn-wf-fnct-protected-is-wg (magic (list 70 78 67 84)) (version 1) (kind k)
                            (p (fn-wg-encode g v)))
                 (:instance fn-wg-frame-protected-octets (magic (list 70 78 67 84)) (version 1) (kind k)
                            (payload (fn-wg-encode g v)))
                 (:instance fn-frame-trailer-of-octets
                            (octets (fn-frame-protected (list 70 78 67 84) 1 k (fn-wg-encode g v)))))
           :in-theory (e/d (fn-frame-inputp fn-frame-magicp)
                           (fn-wf-fnct-frame-facts fn-wf-fnct-encode-is-host-framing
                            fn-wg-encode-octets fn-frame-decode-of-host-framing fn-wf-fnct-protected-is-wg
                            fn-wg-frame-protected-octets fn-frame-trailer-of-octets fn-wg-frame-protected
                            fn-wg-decode-opener-frame fn-wg-encode-opener-frame fn-wg-valuep-opener-frame
                            fn-wg-grammarp-opener-frame
                            fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp fn-wg-ok
                            fn-frame-decode fn-frame-protected fn-frame-protected-prefix
                            fn-frame-trailer fn-frame-digest)))))

(defthm fn-wf-fnct-decode-ok-digestp
  (implies (fn-frame-result-okp (fn-frame-decode x digest mx))
           (and (fn-frame-digestp digest)
                (natp mx) (<= mx 4294967295)
                (fn-cbor-octet-listp x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-frame-decode) (fn-frame-head-fields fn-cbor-u32-from fn-frame-split)))))

(defthm fn-wf-fnct-trailer-when-digestp
  (implies (fn-frame-digestp (fn-frame-trailer y))
           (equal (fn-frame-trailer y) (fn-frame-digest y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-frame-trailer fn-frame-digestp))))

(defthm fn-wf-fnct-protected-prefix-is-split
  (equal (fn-frame-protected-prefix x)
         (car (fn-frame-split (- (len x) 32) x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-frame-protected-prefix) (fn-frame-split))
           :do-not-induct t
           :cases ((< (len x) 32)))
          ("Subgoal 1" :expand ((fn-frame-split (- (len x) 32) x) (fn-frame-split 0 x)))))

(defthm fn-wf-fnct-host-open-is-sealed
  (let* ((r (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm))
         (pr (fn-frame-protected (fn-frame-result-magic r) (fn-frame-result-version r)
                                 (fn-frame-result-kind r) (fn-frame-result-payload r))))
    (implies (fn-frame-result-okp r)
             (equal (append pr (fn-frame-digest pr)) x)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-decode-inversion (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (mx hm))
                 (:instance fn-wf-fnct-decode-ok-digestp (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (mx hm))
                 (:instance fn-frame-decode-trailer-is-the-supplied-digest (octets x) (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (max-payload hm))
                 (:instance fn-wf-fnct-trailer-when-digestp (y (fn-frame-protected-prefix x)))
                 fn-wf-fnct-protected-prefix-is-split)
           :in-theory (disable fn-wf-fnct-decode-inversion fn-frame-encode-of-decode fn-frame-trailer-of-octets
                            fn-frame-decode-trailer-is-the-supplied-digest fn-frame-protected-prefix
                            fn-frame-decode fn-frame-protected fn-frame-trailer fn-frame-digest fn-frame-split
                            fn-frame-result-okp fn-frame-result-magic fn-frame-result-version
                            fn-frame-result-kind fn-frame-result-payload))))

(defthm fn-wf-fnct-host-open-is-wg-accept
  (implies (and (fn-wg-grammarp g) (fn-cbor-octetp k) (natp mx) (< mx 4294967296)
                (equal (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm)
                       (fn-frame-ok (list 70 78 67 84) 1 k p))
                (equal (fn-wg-decode g p) (fn-wg-ok v nil))
                (<= (len p) mx))
           (equal (fn-wg-decode (list :frame (list 70 78 67 84) 1 k mx g) x)
                  (fn-wg-ok v nil)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-host-open-is-sealed)
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (max-payload hm))
                 (:instance fn-wf-fnct-whole-accept-is-encoding (f g) (x p))
                 (:instance fn-wf-fnct-encode-is-host-framing)
                 (:instance fn-wf-fnct-frame-facts)
                 (:instance fn-wg-decode-of-encode-whole (g (list :frame (list 70 78 67 84) 1 k mx g))))
           :in-theory (disable fn-wf-fnct-encode-is-host-framing fn-wf-fnct-frame-facts
                               fn-wg-decode-of-encode-whole fn-frame-decode-payload-octets
                               fn-wg-decode-opener-frame fn-wg-encode-opener-frame fn-wg-valuep-opener-frame
                               fn-wg-grammarp-opener-frame
                               fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp fn-wg-ok
                               fn-frame-decode fn-frame-protected fn-frame-protected-prefix
                               fn-frame-trailer fn-frame-digest))))

; -----------------------------------------------------------------------------
; The host's sealing and opening, as a family book uses them: the host seals
; a payload as protected prefix plus fn-frame-trailer of it (fn-nctrl-seal,
; fn-ncl-poll-seal), and an opened FNCT frame is exactly that sealing of its
; payload.

(defthm fn-wf-fnct-host-seal-is-wg-encode
  (implies (and (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octetp k) (natp mx) (< mx 4294967296)
                (<= (len (fn-wg-encode g v)) mx))
           (and (fn-wg-valuep (list :frame (list 70 78 67 84) 1 k mx g) v)
                (equal (append (fn-frame-protected (list 70 78 67 84) 1 k (fn-wg-encode g v))
                               (fn-frame-trailer
                                (fn-frame-protected (list 70 78 67 84) 1 k (fn-wg-encode g v))))
                       (fn-wg-encode (list :frame (list 70 78 67 84) 1 k mx g) v))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-frame-facts)
                 (:instance fn-wf-fnct-encode-is-host-framing)
                 (:instance fn-wg-encode-octets)
                 (:instance fn-wf-fnct-protected-is-wg (magic (list 70 78 67 84)) (version 1) (kind k)
                            (p (fn-wg-encode g v)))
                 (:instance fn-wg-frame-protected-octets (magic (list 70 78 67 84)) (version 1) (kind k)
                            (payload (fn-wg-encode g v)))
                 (:instance fn-frame-trailer-of-octets
                            (octets (fn-frame-protected (list 70 78 67 84) 1 k (fn-wg-encode g v)))))
           :in-theory (disable fn-wf-fnct-frame-facts fn-wf-fnct-encode-is-host-framing
                               fn-wg-encode-octets fn-wf-fnct-protected-is-wg
                               fn-wg-frame-protected-octets fn-frame-trailer-of-octets fn-wg-frame-protected
                               fn-wg-decode-opener-frame fn-wg-encode-opener-frame fn-wg-valuep-opener-frame
                               fn-wg-grammarp-opener-frame
                               fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp
                               fn-frame-protected fn-frame-trailer fn-frame-digest))))

(defthm fn-wf-fnct-protected-octets-fields
  (implies (fn-cbor-octet-listp (fn-frame-protected (list 70 78 67 84) 1 k p))
           (and (fn-cbor-octetp k) (fn-cbor-octet-listp p)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-frame-protected fn-frame-header))))

(defthm fn-wf-fnct-opened-is-host-seal
  (let* ((r (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm))
         (p (fn-frame-result-payload r)))
    (implies (and (fn-frame-result-okp r)
                  (equal (fn-frame-result-magic r) (list 70 78 67 84))
                  (equal (fn-frame-result-version r) 1)
                  (equal (fn-frame-result-kind r) k))
             (and (fn-cbor-octet-listp p)
                  (<= (len p) hm)
                  (fn-cbor-octetp k)
                  (equal (append (fn-frame-protected (list 70 78 67 84) 1 k p)
                                 (fn-frame-trailer (fn-frame-protected (list 70 78 67 84) 1 k p)))
                         x))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-host-open-is-sealed)
                 (:instance fn-wf-fnct-decode-ok-digestp (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (mx hm))
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (max-payload hm))
                 (:instance fn-frame-decode-bounds-its-payload (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x))) (max-payload hm))
                 (:instance fn-wf-fnct-protected-octets-fields
                            (p (fn-frame-result-payload (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm))))
                 (:instance fn-frame-protected-true-listp (magic (list 70 78 67 84)) (version 1) (kind k)
                            (payload (fn-frame-result-payload (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm))))
                 (:instance fn-frame-trailer-of-octets
                            (octets (fn-frame-protected (list 70 78 67 84) 1 k
                                                        (fn-frame-result-payload (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm))))))
           :in-theory (disable fn-frame-trailer-of-octets fn-frame-decode-payload-octets fn-frame-decode-bounds-its-payload
                               fn-frame-decode fn-frame-protected fn-frame-trailer fn-frame-digest
                               fn-frame-protected-prefix
                               fn-frame-result-okp fn-frame-result-magic fn-frame-result-version
                               fn-frame-result-kind fn-frame-result-payload))))

(defthm fn-wf-fnct-nctrl-seal-is-host-framing
  (implies (and (fn-cbor-octetp k) (fn-cbor-octet-listp p)
                (<= (len p) *fn-nctrl-max-payload*))
           (equal (fn-nctrl-seal k p)
                  (append (fn-frame-protected (list 70 78 67 84) 1 k p)
                          (fn-frame-trailer (fn-frame-protected (list 70 78 67 84) 1 k p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-nctrl-seal) (fn-frame-protected fn-frame-trailer)))))
