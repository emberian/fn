; fn: the local consumer's FNCT families as exported wire grammars (Mini M5,
; planning/design/wire-grammar-2026-10-04.md section 4, families 3).
;
; The codecs are books/consumer-local-control.lisp, which the host calls.
; This book states each family's grammar in the language of
; books/wire-grammar.lisp and proves the host codec agrees with the
; interpreter at it: the encoder is fn-wg-encode on the value the host's
; arguments name, and the decoder accepts exactly the frames fn-wg-decode
; accepts whole, answering the same value under a named projection.
;
; This book owns the prefix `fn-wf-cs' (with the other `fn-wf-' books).

(in-package "ACL2")
(include-book "wire-family-fnct")
(include-book "consumer-local-control")

; -----------------------------------------------------------------------------
; fnct.consumer.status-reply (FNCT kind 9, payload at most 13 octets): a status
; code, and for `accepted' three uint32 fields (the committed ack, the journal
; frontier, the event distance) with ack <= frontier and distance = frontier
; - ack.  The first family with a `where'.  The value of
; (fn-ncl-status-reply-encode STATUS ACK FRONTIER GAP) is
; (fn-wf-cs-status-value STATUS ACK FRONTIER GAP): (STATUS (ACK FRONTIER GAP))
; or (STATUS NIL).

(defconst *fn-wf-cs-u32* '(:uint 4 0 4294967295))
(defconst *fn-wf-cs-status-payload*
  `(:tag 1
    (0 :accepted (:where (:seq ,*fn-wf-cs-u32* ,*fn-wf-cs-u32* ,*fn-wf-cs-u32*)
                         (:le 0 1) (:diff 2 1 0)))
    (1 :refused (:seq))
    (2 :uncertain (:seq))
    (3 :fault (:seq))))
(defconst *fn-wf-cs-status-reply-grammar*
  `(:frame (70 78 67 84) 1 9 13 ,*fn-wf-cs-status-payload*))
(defthm fn-wf-cs-status-grammarp
  (and (fn-wg-grammarp *fn-wf-cs-status-payload*)
       (fn-wg-grammarp *fn-wf-cs-status-reply-grammar*)))
(defun fn-wf-cs-status-value (status ack frontier gap)
  (declare (xargs :guard t))
  (list status (if (eq status :accepted) (list ack frontier gap) nil)))
(defun fn-wf-cs-status-payload (status ack frontier gap)
  (if (eq status :accepted)
      (append (list (fn-ncl-status-code status)) (fn-cbor-u32-bytes ack)
              (fn-cbor-u32-bytes frontier) (fn-cbor-u32-bytes gap))
    (list (fn-ncl-status-code status))))

(defthm fn-wf-cs-status-payload-agrees
  (implies (not (equal (fn-ncl-status-reply-encode status ack frontier gap) :bad))
           (and (fn-wg-valuep *fn-wf-cs-status-payload* (fn-wf-cs-status-value status ack frontier gap))
                (equal (fn-wg-encode *fn-wf-cs-status-payload* (fn-wf-cs-status-value status ack frontier gap))
                       (fn-wf-cs-status-payload status ack frontier gap))
                (fn-cbor-octet-listp (fn-wf-cs-status-payload status ack frontier gap))
                (<= (len (fn-wf-cs-status-payload status ack frontier gap)) 13)))
  :hints (("Goal" :in-theory (e/d (fn-ncl-status-reply-encode fn-ncl-status-code fn-cp-uintp
                                   fn-wg-encode-opener-tag fn-wg-encode-opener-where fn-wg-encode-opener-seq
                                   fn-wg-encode-opener-uint
                                   fn-wg-valuep-opener-tag fn-wg-valuep-opener-where fn-wg-valuep-opener-seq
                                   fn-wg-valuep-opener-uint fn-wg-app-is-append fn-wg-next fn-wg-tag-next
                                   fn-cbor-u32-bytes-are-octets fn-cp-u32-bytes-four)
                                  (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cbor-u32-bytes)))))

(defthm fn-wf-cs-status-encode-agrees
  (implies (not (equal (fn-ncl-status-reply-encode status ack frontier gap) :bad))
           (and (fn-wg-valuep *fn-wf-cs-status-reply-grammar*
                              (fn-wf-cs-status-value status ack frontier gap))
                (equal (fn-ncl-status-reply-encode status ack frontier gap)
                       (fn-wg-encode *fn-wf-cs-status-reply-grammar*
                                     (fn-wf-cs-status-value status ack frontier gap)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-status-payload-agrees
                 (:instance fn-wf-fnct-host-seal-is-wg-encode (g *fn-wf-cs-status-payload*) (k 9) (mx 13)
                            (v (fn-wf-cs-status-value status ack frontier gap))))
           :in-theory (e/d (fn-nctrl-seal)
                           (fn-wf-cs-status-payload-agrees fn-wf-fnct-host-seal-is-wg-encode
                            fn-wf-cs-status-value fn-wg-encode fn-wg-valuep fn-wg-encode-opener-frame
                            fn-wg-valuep-opener-frame fn-frame-protected fn-frame-trailer))
           :expand ((fn-ncl-status-reply-encode status ack frontier gap)))))

(defthm fn-wf-cs-status-encode-is-seal
  (implies (not (equal (fn-ncl-status-reply-encode s a f g) :bad))
           (equal (fn-ncl-status-reply-encode s a f g)
                  (fn-nctrl-seal 9 (fn-wf-cs-status-payload s a f g))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-status-reply-encode) (fn-nctrl-seal fn-cbor-u32-bytes)))))
(defthm fn-wf-cs-status-accepted-payload-canonical
  (let* ((fields (fn-cp-read-fields (cdr p) '(:uint :uint :uint)))
         (vals (fn-cp-nth 1 fields)))
    (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 0)
                  (equal (car fields) :ok) (null (fn-cp-nth 2 fields)))
             (equal (fn-wf-cs-status-payload :accepted (fn-cp-nth 0 vals) (fn-cp-nth 1 vals) (fn-cp-nth 2 vals))
                    p)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cp-read-fields-inverse (xs (cdr p)) (kinds '(:uint :uint :uint)))
                 (:instance fn-wf-cp-read-fields-shape (xs (cdr p)) (kinds '(:uint :uint :uint))))
           :in-theory (e/d (fn-cp-fields-encode fn-cp-nth fn-ncl-status-code)
                           (fn-wf-cp-read-fields-inverse fn-wf-cp-read-fields-shape fn-cp-read-fields
                            fn-cbor-u32-bytes)))))
(defthm fn-wf-cs-status-other-payload-canonical
  (implies (and (fn-cbor-octet-listp p) (consp p) (fn-ncl-code-status (car p))
                (not (equal (car p) 0)) (null (cdr p)))
           (equal (fn-wf-cs-status-payload (fn-ncl-code-status (car p)) nil nil nil) p))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ncl-code-status fn-ncl-status-code))))

(defthm fn-wf-cs-status-encode-not-bad
  (implies (if (eq s :accepted)
               (and (fn-cp-uintp a) (fn-cp-uintp f) (<= a f) (equal g (- f a)))
             (and (member-eq s '(:refused :uncertain :fault)) (null a) (null f) (null g)))
           (not (equal (fn-ncl-status-reply-encode s a f g) :bad)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ncl-status-accepted-payload-inputp (ack a) (frontier f) (gap g)))
           :in-theory (e/d (fn-ncl-status-reply-encode fn-nctrl-seal fn-ncl-status-code fn-cp-uintp fn-frame-protected fn-frame-header)
                           (fn-frame-trailer fn-cbor-u32-bytes fn-cbor-u32-bytes-are-octets)))))

(defthm fn-wf-cs-status-decode-answer-is-payload
  (let* ((r (fn-ncl-status-reply-decode x))
         (p (fn-frame-result-payload (fn-ncl-status-open x))))
    (implies (equal (car r) :consumer-status-reply)
             (and (fn-frame-result-okp (fn-ncl-status-open x))
                  (not (equal (fn-ncl-status-reply-encode (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)) :bad))
                  (equal (fn-ncl-status-reply-encode (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r))
                         (fn-nctrl-seal 9 p)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-status-accepted-payload-canonical
                            (p (fn-frame-result-payload (fn-ncl-status-open x))))
                 (:instance fn-wf-cs-status-other-payload-canonical
                            (p (fn-frame-result-payload (fn-ncl-status-open x))))
                 (:instance fn-wf-cs-status-encode-not-bad
                            (s (nth 1 (fn-ncl-status-reply-decode x))) (a (nth 2 (fn-ncl-status-reply-decode x)))
                            (f (nth 3 (fn-ncl-status-reply-decode x))) (g (nth 4 (fn-ncl-status-reply-decode x))))
                 (:instance fn-wf-cs-status-encode-is-seal
                            (s (nth 1 (fn-ncl-status-reply-decode x))) (a (nth 2 (fn-ncl-status-reply-decode x)))
                            (f (nth 3 (fn-ncl-status-reply-decode x))) (g (nth 4 (fn-ncl-status-reply-decode x)))))
           :in-theory (e/d (fn-ncl-status-reply-decode fn-ncl-code-status fn-ncl-status-code)
                           (fn-ncl-status-open fn-wf-cs-status-payload fn-nctrl-seal fn-ncl-status-reply-encode
                            fn-cp-read-fields fn-cp-nth fn-cbor-u32-bytes)))))
(defthm fn-wf-cs-status-open-is-frame-decode
  (implies (fn-frame-result-okp (fn-ncl-status-open x))
           (and (equal (fn-ncl-status-open x)
                       (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) 13))
                (equal (fn-frame-result-magic (fn-ncl-status-open x)) (list 70 78 67 84))
                (equal (fn-frame-result-version (fn-ncl-status-open x)) 1)
                (equal (fn-frame-result-kind (fn-ncl-status-open x)) 9)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-status-open)
                                  (fn-frame-decode fn-frame-trailer fn-frame-protected-prefix)))))

(defthm fn-wf-cs-status-decode-canonical
  (let ((r (fn-ncl-status-reply-decode x)))
    (implies (equal (car r) :consumer-status-reply)
             (and (not (equal (fn-ncl-status-reply-encode (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)) :bad))
                  (equal (fn-ncl-status-reply-encode (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)) x))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-status-decode-answer-is-payload
                 fn-wf-cs-status-open-is-frame-decode
                 (:instance fn-wf-fnct-opened-is-host-seal (k 9) (hm 13))
                 (:instance fn-wf-fnct-nctrl-seal-is-host-framing (k 9)
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) 13)))))
           :in-theory (union-theories '((:e fn-cbor-octetp) (:e <) (:e len) (:e binary-+)
                                        (:e fn-cbor-octet-listp))
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-wf-cs-two-list
   (implies (and (consp v) (true-listp (cdr v)) (equal (len v) 2))
            (equal (list (car v) (cadr v)) v))
   :rule-classes nil
   :hints (("Goal" :expand ((len v) (len (cdr v)) (len (cddr v)))))))

(defthm fn-wf-cs-status-value-args
  (implies (fn-wg-valuep *fn-wf-cs-status-payload* v)
           (and (equal (fn-wf-cs-status-value (car v) (nth 0 (cadr v)) (nth 1 (cadr v)) (nth 2 (cadr v))) v)
                (not (equal (fn-ncl-status-reply-encode (car v) (nth 0 (cadr v)) (nth 1 (cadr v)) (nth 2 (cadr v)))
                            :bad))))
  :rule-classes nil
  :hints (("Goal" :use (fn-wf-cs-two-list
                 (:instance fn-wf-cs-status-encode-not-bad
                                   (s (car v)) (a (nth 0 (cadr v))) (f (nth 1 (cadr v))) (g (nth 2 (cadr v)))))
           :in-theory (e/d (fn-wg-valuep-opener-tag fn-wg-valuep-opener-where fn-wg-valuep-opener-seq
                            fn-wg-valuep-opener-uint fn-wg-next fn-wg-tag-next fn-cp-uintp)
                           (fn-wg-valuep fn-ncl-status-reply-encode)))))
(defthm fn-wf-cs-status-frame-value-args
  (implies (fn-wg-valuep *fn-wf-cs-status-reply-grammar* v)
           (fn-wg-valuep *fn-wf-cs-status-payload* v))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-wf-fnct-frame-facts (g *fn-wf-cs-status-payload*) (k 9) (mx 13)))
           :in-theory (disable fn-wf-fnct-frame-facts fn-wg-valuep fn-wg-valuep-opener-frame))))

(defthm fn-wf-cs-status-host-roundtrip-of-value
  (implies (fn-wg-valuep *fn-wf-cs-status-payload* v)
           (equal (fn-ncl-status-reply-decode
                   (fn-ncl-status-reply-encode (car v) (nth 0 (cadr v)) (nth 1 (cadr v)) (nth 2 (cadr v))))
                  (list :consumer-status-reply (car v) (nth 0 (cadr v)) (nth 1 (cadr v)) (nth 2 (cadr v)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ncl-status-accepted-reply-roundtrip
                                   (ack (nth 0 (cadr v))) (frontier (nth 1 (cadr v))) (gap (nth 2 (cadr v))))
                        (:instance fn-ncl-status-nonaccepted-reply-roundtrip (status (car v))))
           :in-theory (e/d (fn-wg-valuep-opener-tag fn-wg-valuep-opener-where fn-wg-valuep-opener-seq
                            fn-wg-valuep-opener-uint fn-wg-next fn-wg-tag-next fn-cp-uintp)
                           (fn-wg-valuep fn-ncl-status-reply-encode fn-ncl-status-reply-decode)))))
(defthm fn-wf-cs-status-host-accept-implies-wg
  (let ((r (fn-ncl-status-reply-decode x)))
    (implies (equal (car r) :consumer-status-reply)
             (equal (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)
                    (fn-wg-ok (fn-wf-cs-status-value (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)) nil))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-status-decode-canonical
                 (:instance fn-wf-cs-status-encode-agrees
                            (status (nth 1 (fn-ncl-status-reply-decode x))) (ack (nth 2 (fn-ncl-status-reply-decode x)))
                            (frontier (nth 3 (fn-ncl-status-reply-decode x))) (gap (nth 4 (fn-ncl-status-reply-decode x))))
                 (:instance fn-wg-decode-of-encode-whole (g *fn-wf-cs-status-reply-grammar*)
                            (v (fn-wf-cs-status-value (nth 1 (fn-ncl-status-reply-decode x)) (nth 2 (fn-ncl-status-reply-decode x))
                                                      (nth 3 (fn-ncl-status-reply-decode x)) (nth 4 (fn-ncl-status-reply-decode x))))))
           :in-theory (union-theories '(fn-wf-cs-status-grammarp) (theory 'minimal-theory)))))
(defthm fn-wf-cs-status-wg-accept-implies-host
  (let ((w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
    (implies (and (fn-cbor-octet-listp x) (equal w (fn-wg-ok v nil)))
             (equal (fn-ncl-status-reply-decode x)
                    (list :consumer-status-reply (car v) (nth 0 (cadr v)) (nth 1 (cadr v)) (nth 2 (cadr v))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fnct-whole-accept-is-encoding (f *fn-wf-cs-status-reply-grammar*))
                 (:instance fn-wf-cs-status-frame-value-args)
                 (:instance fn-wf-cs-status-value-args)
                 (:instance fn-wf-cs-status-host-roundtrip-of-value)
                 (:instance fn-wf-cs-status-encode-agrees
                            (status (car v)) (ack (nth 0 (cadr v))) (frontier (nth 1 (cadr v))) (gap (nth 2 (cadr v)))))
           :in-theory (union-theories '(fn-wf-cs-status-grammarp) (theory 'minimal-theory)))))

; KEYSTONE (agreement).  The host's status-reply decoder accepts exactly the
; octets the exported grammar accepts whole, with the same value.
(defthm fn-wf-cs-status-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-ncl-status-reply-decode x))
                 (w (fn-wg-decode *fn-wf-cs-status-reply-grammar* x)))
             (and (iff (equal (car r) :consumer-status-reply)
                       (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car r) :consumer-status-reply)
                           (equal (fn-wg-value w)
                                  (fn-wf-cs-status-value (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-status-host-accept-implies-wg
                 (:instance fn-wf-cs-status-wg-accept-implies-host
                            (v (fn-wg-value (fn-wg-decode *fn-wf-cs-status-reply-grammar* x))))
                 (:instance fn-wg-decode-answers (g *fn-wf-cs-status-reply-grammar*) (xs x)))
           :in-theory (union-theories '(fn-wg-result-accessors car-cons cdr-cons fn-wg-ok fn-wg-refused fn-wg-okp
                                        (:e equal) (:e car))
                                      (theory 'minimal-theory)))))
