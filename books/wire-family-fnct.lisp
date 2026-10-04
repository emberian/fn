; fn: the FNCT control frame as the wire-grammar `frame' node (Mini M5,
; planning/design/wire-grammar-2026-10-04.md section 4, families 3).
;
; Every FNCT family the host speaks is fn-frame-protected PAYLOAD followed by
; the BLAKE3 trailer of it (books/frame-fields.lisp, books/native-control.lisp
; fn-nctrl-seal), opened by fn-frame-decode against the trailer of its own
; protected prefix.  This book proves, once, that this framing IS the
; interpreter's :frame node:
;
;   fn-wf-fnct-seal-is-wg-frame      sealing the encoding of a value is
;                                    fn-wg-encode at the :frame grammar;
;   fn-wf-fnct-open-inversion        a frame the host opens is the sealing of
;                                    the fields it answers (canonicity of the
;                                    host's framing);
;
; so each family book (wire-family-consumer, ...) proves only its payload
; agreement and instantiates these.
;
; This book owns the prefix `fn-wf-fnct-' (with the other `fn-wf-' books).

(in-package "ACL2")
(include-book "wire-grammar")
(include-book "wire-family-fncu") ; fn-wf-be-bytes-4
(include-book "native-control")

; -----------------------------------------------------------------------------
; WIP (lane mini-contract-2, 2026-10-04): every event below was admitted in a
; lat1 REPL session (proof_repl, not a certificate) except the last, which is
; the open step.  The book is not certified and is in no Makefile root yet.

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

; OPEN STEP (refused in the REPL at 34 s, 8.2M steps; checkpoint not yet
; read): a frame the interpreter accepts whole is the frame the host opens.
; Next: read the checkpoint (build/proof-repl/fnct/last-output.txt on lat1);
; likely the :use of fn-wg-encode-of-decode needs its hypotheses fed
; (grammarp of the frame from fn-wf-fnct-frame-facts) under a minimal theory.
;
; (defthm fn-wf-fnct-wg-accept-is-host-open
;   (implies (and (fn-wg-grammarp g) (fn-cbor-octetp k) (natp mx) (< mx 4294967296)
;                 (fn-cbor-octet-listp x)
;                 (equal (fn-wg-decode (list :frame (list 70 78 67 84) 1 k mx g) x) (fn-wg-ok v nil))
;                 (natp hm) (<= mx hm) (<= hm 4294967295))
;            (equal (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) hm)
;                   (fn-frame-ok (list 70 78 67 84) 1 k (fn-wg-encode g v)))))
