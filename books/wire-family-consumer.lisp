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

; -----------------------------------------------------------------------------
; fnct.consumer.reply (FNCT kind 5, payload at most 513 octets): a status
; code, and for `accepted' an optional fncu cursor (the cursor family's
; grammar, so the cursor inside agrees by fn-wf-fncu-decode-agrees).  The
; value of (fn-ncl-reply-encode STATUS CURSOR) and of the decoder's answer
; (:consumer-reply STATUS CURSOR) is (fn-wf-cs-reply-value STATUS CURSOR):
; (STATUS ((the cursor's grammar value))) or (STATUS NIL).

(defconst *fn-wf-cs-reply-payload*
  `(:tag 1
    (0 :accepted (:maybe ,*fn-wf-fncu-grammar*))
    (1 :refused (:seq))
    (2 :uncertain (:seq))
    (3 :fault (:seq))))
(defconst *fn-wf-cs-reply-grammar*
  `(:frame (70 78 67 84) 1 5 513 ,*fn-wf-cs-reply-payload*))
(defthm fn-wf-cs-reply-grammarp
  (and (fn-wg-grammarp *fn-wf-cs-reply-payload*)
       (fn-wg-grammarp *fn-wf-cs-reply-grammar*)))

(defthm fn-wf-cs-reply-payload-decode
  (implies (fn-cbor-octet-listp p)
           (equal (fn-wg-decode *fn-wf-cs-reply-payload* p)
                  (cond ((not (consp p)) (fn-wg-malformed))
                        ((equal (car p) 0)
                         (if (consp (cdr p))
                             (let ((r (fn-wg-decode *fn-wf-fncu-grammar* (cdr p))))
                               (if (fn-wg-okp r)
                                   (fn-wg-ok (list :accepted (list (fn-wg-value r))) (fn-wg-rest r))
                                 r))
                           (fn-wg-ok (list :accepted nil) nil)))
                        ((member (car p) '(1 2 3))
                         (fn-wg-ok (list (fn-ncl-code-status (car p)) nil) (cdr p)))
                        (t (fn-wg-malformed)))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-tag fn-wg-decode-opener-maybe fn-wf-wg-decode-empty-seq
                                   fn-wg-tag-next fn-wg-take fn-wg-drop fn-wg-be-value fn-wg-rev
                                   fn-ncl-code-status)
                                  (fn-wg-decode (:e fn-wg-decode)))
           :expand ((fn-wg-take 1 p) (fn-wg-drop 1 p)))))

(defun fn-wf-cs-reply-value (status cursor)
  (declare (xargs :guard t))
  (list status (if (consp cursor)
                   (list (fn-wf-fncu-value (cadr (fn-cp-cursor-decode cursor))))
                 nil)))
(defthm fn-wf-cs-reply-payload-agrees
  (implies (fn-cbor-octet-listp p)
           (let ((w (fn-wg-decode *fn-wf-cs-reply-payload* p)))
             (and (iff (and (fn-wg-okp w) (null (fn-wg-rest w)))
                       (and (consp p) (fn-ncl-code-status (car p))
                            (or (null (cdr p))
                                (and (eq (fn-ncl-code-status (car p)) :accepted)
                                     (eq (car (fn-cp-cursor-decode (cdr p))) :ok)))))
                  (implies (and (fn-wg-okp w) (null (fn-wg-rest w)))
                           (equal (fn-wg-value w)
                                  (fn-wf-cs-reply-value (fn-ncl-code-status (car p)) (cdr p)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fncu-decode-agrees (x (cdr p)))
                 (:instance fn-wg-encode-of-decode (g *fn-wf-fncu-grammar*) (xs (cdr p)))
                 (:instance fn-wf-fncu-value-is-a-cursor
                            (v (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* (cdr p))))))
           :in-theory (e/d (fn-wf-cs-reply-payload-decode fn-ncl-code-status fn-wg-result-accessors)
                           (fn-wg-decode fn-wf-fncu-decode-agrees fn-cp-cursor-decode fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor
                            fn-wf-fncu-value fn-wf-fncu-cursor fn-wg-valuep fn-wg-encode
                            fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value)))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value fn-wg-malformed fn-wg-refused)))))

(defthm fn-wf-cs-reply-decode-shape
  (implies (fn-cbor-octet-listp x)
           (let* ((r (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) *fn-nctrl-max-payload*))
                  (p (fn-frame-result-payload r)))
             (equal (equal (car (fn-ncl-reply-decode x)) :consumer-reply)
                    (and (fn-frame-result-okp r)
                         (equal (fn-frame-result-magic r) (list 70 78 67 84))
                         (equal (fn-frame-result-version r) 1)
                         (equal (fn-frame-result-kind r) 5)
                         (<= (len p) 513)
                         (consp p) (fn-ncl-code-status (car p))
                         (or (null (cdr p))
                             (and (eq (fn-ncl-code-status (car p)) :accepted)
                                  (eq (car (fn-cp-cursor-decode (cdr p))) :ok)))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-frame-decode-payload-octets (octets x)
                                   (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                                   (max-payload *fn-nctrl-max-payload*)))
           :in-theory (e/d (fn-ncl-reply-decode fn-nctrl-open)
                           (fn-frame-decode fn-frame-trailer fn-frame-protected-prefix fn-cp-cursor-decode
                            fn-frame-decode-payload-octets)))))
(defthm fn-wf-cs-reply-decode-answer
  (implies (equal (car (fn-ncl-reply-decode x)) :consumer-reply)
           (let ((p (fn-frame-result-payload
                     (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) *fn-nctrl-max-payload*))))
             (equal (fn-ncl-reply-decode x)
                    (list :consumer-reply (fn-ncl-code-status (car p)) (cdr p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-reply-decode fn-nctrl-open)
                                  (fn-frame-decode fn-frame-trailer fn-frame-protected-prefix fn-cp-cursor-decode)))))

(defthm fn-wf-cs-cursor-ok-bounds
  (implies (equal (car (fn-cp-cursor-decode c)) :ok)
           (and (fn-cbor-at-mostp c 512) (consp c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cp-cursor-decode) (fn-cp-read-fields fn-cp-cursorp)))))

(defthm fn-wf-cs-cursor-ok-facts
  (implies (equal (car (fn-cp-cursor-decode c)) :ok)
           (let ((v (fn-wf-fncu-value (cadr (fn-cp-cursor-decode c)))))
             (and (fn-wg-valuep *fn-wf-fncu-grammar* v)
                  (equal (fn-wg-encode *fn-wf-fncu-grammar* v) c)
                  (fn-cbor-octet-listp c)
                  (consp c)
                  (<= (len c) 512))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cp-cursor-decode-inversion (x c))
                 (:instance fn-cp-cursor-encode-decode-roundtrip (x c))
                 fn-wf-cs-cursor-ok-bounds
                 (:instance fn-wf-fncu-encode-agrees (c (cadr (fn-cp-cursor-decode c))))
                 (:instance fn-cp-at-most-length (xs c) (bound 512)))
           :in-theory (e/d ()
                           (fn-cp-cursor-decode fn-wf-fncu-encode-agrees fn-cp-cursor-encode-decode-roundtrip fn-cp-cursorp
                            fn-cp-cursor-encode fn-wg-encode fn-wg-valuep fn-cp-read-fields fn-cp-at-most-length)))))

(defthm fn-wf-cs-reply-payload-encode-agrees
  (implies (not (equal (fn-ncl-reply-encode status cursor) :bad))
           (and (fn-wg-valuep *fn-wf-cs-reply-payload* (fn-wf-cs-reply-value status cursor))
                (equal (fn-wg-encode *fn-wf-cs-reply-payload* (fn-wf-cs-reply-value status cursor))
                       (cons (fn-ncl-status-code status) cursor))
                (fn-cbor-octet-listp (cons (fn-ncl-status-code status) cursor))
                (<= (len (cons (fn-ncl-status-code status) cursor)) 513)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-cursor-ok-facts (c cursor)))
           :in-theory (e/d (fn-ncl-reply-encode fn-ncl-status-code fn-wf-cs-reply-value
                            fn-wg-encode-opener-tag fn-wg-encode-opener-maybe fn-wf-wg-encode-empty-seq
                            fn-wg-valuep-opener-tag fn-wg-valuep-opener-maybe
                            fn-wg-tag-next fn-wg-app-is-append)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value)))))
; KEYSTONE (agreement).  The host's reply encoder, when it encodes, is
; fn-wg-encode at the grammar.
(defthm fn-wf-cs-reply-encode-agrees
  (implies (not (equal (fn-ncl-reply-encode status cursor) :bad))
           (and (fn-wg-valuep *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value status cursor))
                (equal (fn-ncl-reply-encode status cursor)
                       (fn-wg-encode *fn-wf-cs-reply-grammar* (fn-wf-cs-reply-value status cursor)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-reply-payload-encode-agrees
                 (:instance fn-wf-fnct-host-seal-is-wg-encode (g *fn-wf-cs-reply-payload*) (k 5) (mx 513)
                            (v (fn-wf-cs-reply-value status cursor)))
                 (:instance fn-wf-fnct-nctrl-seal-is-host-framing (k 5) (p (cons (fn-ncl-status-code status) cursor))))
           :in-theory (e/d (fn-ncl-reply-encode)
                           (fn-wf-cs-reply-payload-encode-agrees fn-wf-fnct-host-seal-is-wg-encode
                            fn-wf-cs-reply-value fn-wg-encode fn-wg-valuep fn-wg-encode-opener-frame
                            fn-wg-valuep-opener-frame fn-frame-protected fn-frame-trailer fn-nctrl-seal
                            fn-ncl-status-code fn-cp-cursor-decode)))))

; KEYSTONE (agreement).  The host's consumer-reply decoder accepts exactly the
; octets the exported grammar accepts whole, with the same value.
(defthm fn-wf-cs-reply-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-ncl-reply-decode x))
                 (w (fn-wg-decode *fn-wf-cs-reply-grammar* x)))
             (and (iff (equal (car r) :consumer-reply)
                       (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car r) :consumer-reply)
                           (equal (fn-wg-value w) (fn-wf-cs-reply-value (nth 1 r) (nth 2 r)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-reply-decode-shape fn-wf-cs-reply-decode-answer
                 (:instance fn-wf-fnct-whole-decode (g *fn-wf-cs-reply-payload*) (k 5) (mx 513)
                            (hm *fn-nctrl-max-payload*))
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                            (max-payload *fn-nctrl-max-payload*))
                 (:instance fn-wf-cs-reply-payload-agrees
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x))
                                                 *fn-nctrl-max-payload*)))))
           :in-theory (union-theories '(fn-wf-cs-reply-grammarp car-cons cdr-cons (:e nth) nth-0-cons nth-add1
                                        (:e fn-cbor-octetp) (:e natp) (:e <) (:e zp) (:e binary-+) (:e eq))
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; fnct.consumer.request (FNCT kind 4, payload at most 1024 octets; the host
; reads a request under 513 octets except the bound commands 7 and 8): a
; command code, then its fields -- consumer and group ids (1..64 octets,
; one-octet length), the account secret of the bound commands (1..496
; octets, two-octet length) and the fncu cursor of ack and bound-ack.  The
; decoder's answer (:consumer KIND FIRST SECOND) and the encoder's arguments
; have the grammar value (fn-wf-cs-request-value KIND FIRST SECOND).

(local
 (defthm fn-wf-cs-wg-take-is-take
   (implies (<= (nfix n) (len xs))
            (equal (fn-wg-take n xs) (take n xs)))
   :hints (("Goal" :induct (fn-wg-take n xs)))))
(local
 (defthm fn-wf-cs-wg-drop-is-nthcdr
   (implies (true-listp xs)
            (equal (fn-wg-drop n xs) (nthcdr n xs)))
   :hints (("Goal" :induct (fn-wg-drop n xs)))))
(local
 (defthm fn-wf-cs-octets-of-take
   (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
            (fn-cbor-octet-listp (take n xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(defconst *fn-wf-cs-id* '(:bytes 1 1 64 :any))
(defconst *fn-wf-cs-secret* '(:bytes 2 1 496 :any))
(defthm fn-wf-cs-id-decode
  (implies (fn-cbor-octet-listp b)
           (equal (fn-wg-decode *fn-wf-cs-id* b)
                  (if (equal (car (fn-cp-read-id b)) :ok)
                      (fn-wg-ok (fn-cp-nth 1 (fn-cp-read-id b)) (fn-cp-nth 2 (fn-cp-read-id b)))
                    (fn-wg-malformed))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-bytes fn-cp-read-id fn-cp-nth fn-wg-be-value
                                   fn-wg-le-value fn-wg-rev)
                                  (fn-wg-decode))
           :expand ((fn-wg-take 1 b) (fn-wg-drop 1 b)))))
(defthm fn-wf-cs-secret-decode
  (implies (fn-cbor-octet-listp b)
           (equal (fn-wg-decode *fn-wf-cs-secret* b)
                  (if (equal (car (fn-ncl-read-secret b)) :ok)
                      (fn-wg-ok (fn-cp-nth 1 (fn-ncl-read-secret b)) (fn-cp-nth 2 (fn-ncl-read-secret b)))
                    (fn-wg-malformed))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-bytes fn-ncl-read-secret fn-cp-nth fn-wg-be-value
                                   fn-wg-le-value fn-wg-rev)
                                  (fn-wg-decode))
           :expand ((fn-wg-take 2 b) (fn-wg-take 1 (cdr b)) (fn-wg-drop 2 b) (fn-wg-drop 1 (cdr b))))))

(defconst *fn-wf-cs-request-payload*
  `(:tag 1
    (0 :register (:seq ,*fn-wf-cs-id* ,*fn-wf-cs-id*))
    (1 :ack ,*fn-wf-fncu-grammar*)
    (2 :position (:seq ,*fn-wf-cs-id*))
    (3 :unregister (:seq ,*fn-wf-cs-id*))
    (4 :bootstrap (:seq))
    (5 :poll (:seq ,*fn-wf-cs-id*))
    (6 :status (:seq ,*fn-wf-cs-id*))
    (7 :bound-poll (:seq ,*fn-wf-cs-id* ,*fn-wf-cs-secret*))
    (8 :bound-ack (:seq ,*fn-wf-cs-secret* ,*fn-wf-fncu-grammar*))))
(defconst *fn-wf-cs-request-grammar*
  `(:frame (70 78 67 84) 1 4 1024 ,*fn-wf-cs-request-payload*))
(defthm fn-wf-cs-request-grammarp
  (and (fn-wg-grammarp *fn-wf-cs-request-payload*)
       (fn-wg-grammarp *fn-wf-cs-request-grammar*)))
(defun fn-wf-cs-request-arm (code)
  (declare (xargs :guard t))
  (cadr (cdr (assoc-equal code (cddr *fn-wf-cs-request-payload*)))))
(defthm fn-wf-cs-request-payload-decode
  (implies (fn-cbor-octet-listp p)
           (equal (fn-wg-decode *fn-wf-cs-request-payload* p)
                  (if (and (consp p) (fn-ncl-code-command (car p)))
                      (let ((r (fn-wg-decode (fn-wf-cs-request-arm (car p)) (cdr p))))
                        (if (fn-wg-okp r)
                            (fn-wg-ok (list (fn-ncl-code-command (car p)) (fn-wg-value r)) (fn-wg-rest r))
                          r))
                    (fn-wg-malformed))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-tag fn-wg-tag-next fn-wg-take fn-wg-drop
                                   fn-wg-be-value fn-wg-rev fn-ncl-code-command fn-wf-cs-request-arm)
                                  (fn-wg-decode (:e fn-wg-decode)))
           :expand ((fn-wg-take 1 p) (fn-wg-drop 1 p)))))

(defun fn-wf-cs-request-value (kind first second)
  (declare (xargs :guard t))
  (case kind
    (:register (list :register (list first second)))
    (:ack (list :ack (fn-wf-fncu-value (cadr (fn-cp-cursor-decode first)))))
    ((:position :unregister :poll :status) (list kind (list first)))
    (:bootstrap (list :bootstrap nil))
    (:bound-poll (list :bound-poll (list first second)))
    (:bound-ack (list :bound-ack (list second (fn-wf-fncu-value (cadr (fn-cp-cursor-decode first))))))
    (otherwise nil)))
(defun fn-wf-cs-request-host (p)
  (fn-ncl-request-payload-decode (fn-frame-ok '(70 78 67 84) 1 4 p)))
(local
 (defthm fn-wf-cs-len-take
   (equal (len (take n x)) (nfix n))))
(local
 (defthm fn-wf-cs-len-nthcdr
   (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
   :hints (("Goal" :induct (nthcdr n x)))))
(local
 (defthm fn-wf-cs-read-id-len
   (implies (equal (car (fn-cp-read-id b)) :ok)
            (and (equal (len b) (+ 1 (len (fn-cp-nth 1 (fn-cp-read-id b))) (len (fn-cp-nth 2 (fn-cp-read-id b)))))
                 (<= (len (fn-cp-nth 1 (fn-cp-read-id b))) 64)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-cp-read-id fn-cp-nth)))))

(local
 (defthm fn-wf-cs-cp-nth-0
   (equal (fn-cp-nth 0 x) (car x))
   :hints (("Goal" :in-theory (enable fn-cp-nth)))))
(local
 (defthm fn-wf-cs-octets-of-nthcdr
   (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr n x)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local
 (defthm fn-wf-cs-read-id-rest-octets
   (implies (fn-cbor-octet-listp b)
            (fn-cbor-octet-listp (fn-cp-nth 2 (fn-cp-read-id b))))
   :hints (("Goal" :in-theory (enable fn-cp-read-id fn-cp-nth)))))
(local
 (defthm fn-wf-cs-read-secret-rest-octets
   (implies (fn-cbor-octet-listp b)
            (fn-cbor-octet-listp (fn-cp-nth 2 (fn-ncl-read-secret b))))
   :hints (("Goal" :in-theory (enable fn-ncl-read-secret fn-cp-nth)))))

(defthm fn-wf-cs-request-register-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 0) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p)))
                 (:instance fn-wf-cs-read-id-len (b (fn-cp-nth 2 (fn-cp-read-id (cdr p))))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq2 fn-wf-cs-id-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value))))
  :rule-classes nil)

(defthm fn-wf-cs-request-position-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 2) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-unregister-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 3) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-poll-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 5) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-status-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 6) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-bootstrap-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 4) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ()
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-ack-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 1) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fncu-decode-agrees (x (cdr p)))
                 (:instance fn-wg-encode-of-decode (g *fn-wf-fncu-grammar*) (xs (cdr p)))
                 (:instance fn-wf-fncu-value-is-a-cursor (v (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* (cdr p)))))
                 (:instance fn-wf-cs-cursor-ok-bounds (c (cdr p)))
                 (:instance fn-cp-at-most-length (xs (cdr p)) (bound 512)))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-bound-poll-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 7) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-read-id-len (b (cdr p))))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-bound-ack-agrees
  (implies (and (fn-cbor-octet-listp p) (consp p) (equal (car p) 8) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-fncu-decode-agrees (x (fn-cp-nth 2 (fn-ncl-read-secret (cdr p)))))
                 (:instance fn-wg-encode-of-decode (g *fn-wf-fncu-grammar*) (xs (fn-cp-nth 2 (fn-ncl-read-secret (cdr p)))))
                 (:instance fn-wf-fncu-value-is-a-cursor (v (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* (fn-cp-nth 2 (fn-ncl-read-secret (cdr p)))))))
                 (:instance fn-wf-cs-cursor-ok-bounds (c (fn-cp-nth 2 (fn-ncl-read-secret (cdr p)))))
                 (:instance fn-cp-at-most-length (xs (fn-cp-nth 2 (fn-ncl-read-secret (cdr p)))) (bound 512)))
           :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host fn-ncl-request-payload-decode
                            fn-wf-cs-request-arm fn-wf-wg-decode-seq1 fn-wf-wg-decode-seq2 fn-wf-wg-decode-empty-seq
                            fn-wf-cs-id-decode fn-wf-cs-secret-decode fn-ncl-code-command
                            fn-wg-result-accessors)
                           (fn-wg-decode fn-cp-read-id fn-ncl-read-secret fn-cp-nth fn-wg-okp fn-wg-ok fn-wg-rest
                            fn-wg-value fn-cp-cursor-decode fn-wf-fncu-decode-agrees fn-wf-fncu-value fn-wf-fncu-cursor
                            fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor fn-wg-valuep fn-wg-encode))))
  :rule-classes nil)

(defthm fn-wf-cs-request-other-refused
  (implies (and (fn-cbor-octet-listp p)
                (not (and (consp p) (member (car p) '(0 1 2 3 4 5 6 7 8)))))
           (and (not (equal (car (fn-wf-cs-request-host p)) :consumer))
                (not (fn-wg-okp (fn-wg-decode *fn-wf-cs-request-payload* p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-wf-cs-request-payload-decode fn-wf-cs-request-host
                                   fn-ncl-request-payload-decode fn-ncl-code-command)
                                  (fn-wg-decode)))))
(defthm fn-wf-cs-request-payload-agrees
  (implies (and (fn-cbor-octet-listp p) (<= (len p) 1024))
           (let ((h (fn-wf-cs-request-host p))
                 (w (fn-wg-decode *fn-wf-cs-request-payload* p)))
             (and (iff (equal (car h) :consumer) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car h) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 h) (nth 2 h) (nth 3 h)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-request-other-refused fn-wf-cs-request-register-agrees fn-wf-cs-request-ack-agrees
                 fn-wf-cs-request-position-agrees fn-wf-cs-request-unregister-agrees
                 fn-wf-cs-request-bootstrap-agrees fn-wf-cs-request-poll-agrees fn-wf-cs-request-status-agrees
                 fn-wf-cs-request-bound-poll-agrees fn-wf-cs-request-bound-ack-agrees)
           :in-theory (union-theories '((:e member-equal) member-equal) (theory 'minimal-theory)))))

(defthm fn-wf-cs-request-decode-is-host
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) *fn-nctrl-max-payload*)))
             (equal (fn-ncl-request-decode x)
                    (if (and (fn-frame-result-okp r)
                             (equal (fn-frame-result-magic r) (list 70 78 67 84))
                             (equal (fn-frame-result-version r) 1)
                             (equal (fn-frame-result-kind r) 4))
                        (fn-wf-cs-request-host (fn-frame-result-payload r))
                      (list :refused :frame)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-request-decode fn-nctrl-open fn-wf-cs-request-host
                                   fn-ncl-request-payload-decode)
                                  (fn-frame-decode fn-frame-trailer fn-frame-protected-prefix
                                   fn-cp-read-id fn-ncl-read-secret fn-cp-cursor-decode)))))
(defthm fn-wf-cs-request-host-size
  (implies (equal (car (fn-wf-cs-request-host p)) :consumer)
           (<= (len p) 1024))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-wf-cs-request-host fn-ncl-request-payload-decode)
                                  (fn-cp-read-id fn-ncl-read-secret fn-cp-cursor-decode)))))
; KEYSTONE (agreement).  The host's request decoder answers :consumer for
; exactly the frames the exported grammar accepts whole, with the same value.
(defthm fn-wf-cs-request-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-ncl-request-decode x))
                 (w (fn-wg-decode *fn-wf-cs-request-grammar* x)))
             (and (iff (equal (car r) :consumer)
                       (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (equal (car r) :consumer)
                           (equal (fn-wg-value w) (fn-wf-cs-request-value (nth 1 r) (nth 2 r) (nth 3 r)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-request-decode-is-host
                 (:instance fn-wf-fnct-whole-decode (g *fn-wf-cs-request-payload*) (k 4) (mx 1024)
                            (hm *fn-nctrl-max-payload*))
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                            (max-payload *fn-nctrl-max-payload*))
                 (:instance fn-wf-cs-request-host-size
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x))
                                                 *fn-nctrl-max-payload*))))
                 (:instance fn-wf-cs-request-payload-agrees
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x))
                                                 *fn-nctrl-max-payload*)))))
           :in-theory (union-theories '(fn-wf-cs-request-grammarp car-cons cdr-cons
                                        (:e fn-cbor-octetp) (:e natp) (:e <) (:e equal))
                                      (theory 'minimal-theory)))))

(local
 (defthm fn-wf-cs-consp-len
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))
(defthm fn-wf-cs-id-encode
  (implies (fn-cp-idp x)
           (and (fn-wg-valuep *fn-wf-cs-id* x)
                (equal (fn-wg-encode *fn-wf-cs-id* x) (fn-cp-id-bytes x))
                (fn-cbor-octet-listp (fn-cp-id-bytes x))
                (<= (len (fn-cp-id-bytes x)) 65)))
  :hints (("Goal" :use ((:instance fn-cp-at-most-length (xs x) (bound 64)))
           :in-theory (e/d (fn-wg-encode-opener-bytes fn-wg-valuep-opener-bytes fn-cp-idp fn-cp-id-bytes
                            fn-wg-app-is-append)
                           (fn-cp-at-most-length)))))

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-wf-cs-secret-encode
  (implies (fn-ncl-secretp x)
           (and (fn-wg-valuep *fn-wf-cs-secret* x)
                (equal (fn-wg-encode *fn-wf-cs-secret* x) (fn-ncl-secret-bytes x))
                (fn-cbor-octet-listp (fn-ncl-secret-bytes x))
                (<= (len (fn-ncl-secret-bytes x)) 498)))
  :hints (("Goal" :in-theory (e/d (fn-wg-encode-opener-bytes fn-wg-valuep-opener-bytes fn-ncl-secretp
                                     fn-ncl-secret-bytes fn-wg-app-is-append)
                           (fn-wg-be-bytes))))))

(defun fn-wf-cs-request-payload (kind first second)
  (let ((code (fn-ncl-command-code kind)))
    (case kind
      (:bootstrap (list code))
      (:register (append (list code) (fn-cp-id-bytes first) (fn-cp-id-bytes second)))
      (:ack (cons code first))
      ((:position :unregister :poll :status) (cons code (fn-cp-id-bytes first)))
      (:bound-poll (append (list code) (fn-cp-id-bytes first) (fn-ncl-secret-bytes second)))
      (:bound-ack (append (list code) (fn-ncl-secret-bytes second) first))
      (otherwise nil))))
(defthm fn-wf-cs-request-encode-is-seal
  (implies (not (equal (fn-ncl-request-encode kind first second) :bad))
           (equal (fn-ncl-request-encode kind first second)
                  (fn-nctrl-seal 4 (fn-wf-cs-request-payload kind first second))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-request-encode) (fn-nctrl-seal fn-cp-cursor-decode)))))

(defthm fn-wf-cs-request-payload-encode-bootstrap
  (implies (and (equal kind :bootstrap) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ()
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-register
  (implies (and (equal kind :register) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)) (:instance fn-wf-cs-id-encode (x second)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-ack
  (implies (and (equal kind :ack) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-cursor-ok-facts (c first)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-position
  (implies (and (equal kind :position) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-unregister
  (implies (and (equal kind :unregister) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-poll
  (implies (and (equal kind :poll) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-status
  (implies (and (equal kind :status) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-bound-poll
  (implies (and (equal kind :bound-poll) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-id-encode (x first)) (:instance fn-wf-cs-secret-encode (x second)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-payload-encode-bound-ack
  (implies (and (equal kind :bound-ack) (not (equal (fn-ncl-request-encode kind first second) :bad)))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-cs-cursor-ok-facts (c first)) (:instance fn-wf-cs-secret-encode (x second)))
           :in-theory (e/d (fn-ncl-request-encode fn-ncl-command-code fn-wf-cs-request-value fn-wf-cs-request-payload
                            fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-tag-next
                            fn-wf-wg-encode-seq1 fn-wf-wg-encode-seq2 fn-wf-wg-encode-empty-seq
                            fn-wg-app-is-append fn-wf-be-bytes-1)
                           (fn-nctrl-seal fn-wg-encode fn-wg-valuep fn-cp-cursor-decode fn-wf-fncu-value
                            fn-wf-cs-id-encode fn-wf-cs-secret-encode
                            fn-cp-id-bytes fn-ncl-secret-bytes fn-wg-be-bytes)))))

(defthm fn-wf-cs-request-encode-other-bad
  (implies (not (member kind '(:bootstrap :register :ack :position :unregister :poll :status :bound-poll :bound-ack)))
           (equal (fn-ncl-request-encode kind first second) :bad))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ncl-request-encode) (fn-nctrl-seal fn-cp-cursor-decode)))))
(defthm fn-wf-cs-request-payload-encode-agrees
  (implies (not (equal (fn-ncl-request-encode kind first second) :bad))
           (let ((p (fn-wf-cs-request-payload kind first second))
                 (v (fn-wf-cs-request-value kind first second)))
             (and (fn-wg-valuep *fn-wf-cs-request-payload* v)
                  (equal (fn-wg-encode *fn-wf-cs-request-payload* v) p)
                  (fn-cbor-octet-listp p)
                  (<= (len p) 1024))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-request-encode-other-bad fn-wf-cs-request-payload-encode-bootstrap fn-wf-cs-request-payload-encode-register fn-wf-cs-request-payload-encode-ack fn-wf-cs-request-payload-encode-position fn-wf-cs-request-payload-encode-unregister fn-wf-cs-request-payload-encode-poll fn-wf-cs-request-payload-encode-status fn-wf-cs-request-payload-encode-bound-poll fn-wf-cs-request-payload-encode-bound-ack)
           :in-theory (union-theories '(member-equal) (theory 'minimal-theory)))))

; KEYSTONE (agreement).  The host's request encoder, when it encodes, is
; fn-wg-encode at the grammar.
(defthm fn-wf-cs-request-encode-agrees
  (implies (not (equal (fn-ncl-request-encode kind first second) :bad))
           (and (fn-wg-valuep *fn-wf-cs-request-grammar* (fn-wf-cs-request-value kind first second))
                (equal (fn-ncl-request-encode kind first second)
                       (fn-wg-encode *fn-wf-cs-request-grammar* (fn-wf-cs-request-value kind first second)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cs-request-payload-encode-agrees fn-wf-cs-request-encode-is-seal
                 (:instance fn-wf-fnct-host-seal-is-wg-encode (g *fn-wf-cs-request-payload*) (k 4) (mx 1024)
                            (v (fn-wf-cs-request-value kind first second)))
                 (:instance fn-wf-fnct-nctrl-seal-is-host-framing (k 4)
                            (p (fn-wf-cs-request-payload kind first second))))
           :in-theory (union-theories '(fn-wf-cs-request-grammarp (:e fn-cbor-octetp) (:e natp) (:e <))
                                      (theory 'minimal-theory)))))
