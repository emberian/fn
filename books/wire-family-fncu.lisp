; fn: the `fncu' consumer cursor as an exported wire grammar (Mini M5,
; planning/design/wire-grammar-2026-10-04.md section 4, family fncu.cursor).
;
; The cursor's codec is books/consumer-position.lisp (fn-cp-cursor-encode,
; fn-cp-cursor-decode), which the host calls.  This book states its grammar
; in the language of books/wire-grammar.lisp and proves the two agree:
;
;   fn-wf-fncu-encode-agrees    the host's encoder is fn-wg-encode at the
;                               grammar, on every cursor;
;   fn-wf-fncu-decode-agrees    the host's decoder accepts exactly the octets
;                               fn-wg-decode accepts with nothing left, with
;                               the same cursor;
;
; so the generic round trips are the cursor's, and the one the cursor lacked
; (C-0c, redregg/work/FN-660-RESPONSE-20261004.md) is proved here:
;
;   fn-cp-cursor-encode-decode-roundtrip   an accepted cursor's octets are
;                                          the encoding of what they decode to.
;
; A cursor (:cursor H I C P Q QV VV E POS) is the grammar value
; (NIL H I C P Q QV VV E POS): the :const header's value, then the fields.
;
; This book owns the prefix `fn-wf-' with the other wire-family books
; (docs/prefixes.md).

(in-package "ACL2")
(include-book "wire-grammar")
(include-book "consumer-position")

(defconst *fn-wf-fncu-grammar*
  '(:seq (:const (102 110 99 117 1))      ; "fncu", version 1
         (:bytes 1 1 64 :any)              ; history
         (:bytes 1 1 64 :any)              ; incarnation
         (:bytes 1 1 64 :any)              ; consumer
         (:bytes 1 1 64 :any)              ; principal
         (:bytes 1 1 64 :any)              ; query
         (:uint 4 0 4294967295)            ; query version
         (:uint 4 0 4294967295)            ; view version
         (:uint 4 1 4294967295)            ; registration epoch
         (:uint 4 0 4294967295)))          ; position

(defthm fn-wf-fncu-grammarp
  (fn-wg-grammarp *fn-wf-fncu-grammar*))

(defun fn-wf-fncu-value (cursor)
  (declare (xargs :guard t))
  (cons nil (if (consp cursor) (cdr cursor) nil)))

(defun fn-wf-fncu-cursor (value)
  (declare (xargs :guard t))
  (cons :cursor (if (consp value) (cdr value) nil)))

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-wf-be-bytes-1
  (implies (and (natp n) (< n 256))
           (equal (fn-wg-be-bytes 1 n) (list n)))
  :hints (("Goal" :in-theory (enable fn-wg-be-bytes fn-wg-le-bytes fn-wg-rev))))
(defthm fn-wf-be-bytes-4
  (implies (and (natp n) (< n 4294967296))
           (equal (fn-wg-be-bytes 4 n) (fn-cbor-u32-bytes n)))
  :hints (("Goal" :in-theory (enable fn-wg-be-bytes fn-wg-rev fn-cbor-u32-bytes)
           :expand ((fn-wg-le-bytes 4 n) (fn-wg-le-bytes 3 (floor n 256))
                    (fn-wg-le-bytes 2 (floor (floor n 256) 256))
                    (fn-wg-le-bytes 1 (floor (floor (floor n 256) 256) 256))
                    (fn-wg-le-bytes 0 (floor (floor (floor (floor n 256) 256) 256) 256)))))))

(defthm fn-wf-at-mostp-len
  (implies (fn-cbor-at-mostp x n) (<= (len x) (nfix n)))
  :rule-classes :linear)
(defthm fn-wf-consp-len
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)
(defthm fn-wf-fncu-encode-agrees-fields
   (implies (fn-cp-cursorp (fn-cp-cursor h i cn p q qv vv e pos))
            (and (fn-wg-valuep *fn-wf-fncu-grammar* (list nil h i cn p q qv vv e pos))
                 (equal (fn-cp-cursor-encode (fn-cp-cursor h i cn p q qv vv e pos))
                        (fn-wg-encode *fn-wf-fncu-grammar*
                                      (list nil h i cn p q qv vv e pos)))))
   :hints (("Goal" :in-theory (enable fn-wg-encode-opener-seq fn-wg-valuep-opener-seq
                                      fn-cp-cursor-encode fn-cp-cursorp fn-cp-cursor
                                      fn-cp-idp fn-cp-uintp
                                      fn-cp-id-bytes fn-wg-app-is-append fn-wg-next))))

(defthm fn-wf-fncu-encode-agrees
  (implies (fn-cp-cursorp c)
           (and (fn-wg-valuep *fn-wf-fncu-grammar* (fn-wf-fncu-value c))
                (equal (fn-cp-cursor-encode c)
                       (fn-wg-encode *fn-wf-fncu-grammar* (fn-wf-fncu-value c)))))
  :hints (("Goal" :use ((:instance fn-wf-fncu-encode-agrees-fields
                                   (h (fn-cp-nth 1 c)) (i (fn-cp-nth 2 c)) (cn (fn-cp-nth 3 c))
                                   (p (fn-cp-nth 4 c)) (q (fn-cp-nth 5 c)) (qv (fn-cp-nth 6 c))
                                   (vv (fn-cp-nth 7 c)) (e (fn-cp-nth 8 c)) (pos (fn-cp-nth 9 c)))
                        fn-cp-cursor-rebuild)
           :in-theory (e/d (fn-cp-cursor fn-cp-nth) (fn-wf-fncu-encode-agrees-fields fn-cp-cursor-rebuild
                                       fn-cp-cursorp fn-cp-cursor-encode)))))

(defthm fn-wf-append-take-nthcdr
  (implies (<= (nfix n) (len x))
           (equal (append (take n x) (nthcdr n x)) x)))
(defthm fn-wf-u32-bytes-of-from-reassemble
  (implies (and (fn-cbor-octet-listp xs) (<= 4 (len xs)))
           (equal (append (fn-cbor-u32-bytes (fn-cbor-u32-from xs)) (nthcdr 4 xs)) xs))
  :hints (("Goal" :use fn-cbor-u32-to-from-octets
           :expand ((nthcdr 4 xs) (nthcdr 3 (cdr xs)) (nthcdr 2 (cddr xs)) (nthcdr 1 (cdddr xs))
                    (fn-cbor-octet-listp xs))
           :in-theory (disable fn-cbor-u32-to-from-octets fn-cbor-u32-bytes fn-cbor-u32-from))))
(defthm fn-wf-len-take
  (equal (len (take n x)) (nfix n)))
(defthm fn-wf-cp-read-fields-inverse
  (implies (and (fn-cbor-octet-listp xs)
                (equal (car (fn-cp-read-fields xs kinds)) :ok))
           (equal (append (fn-cp-fields-encode (fn-cp-nth 1 (fn-cp-read-fields xs kinds)) kinds)
                          (fn-cp-nth 2 (fn-cp-read-fields xs kinds)))
                  xs))
  :hints (("Goal" :induct (fn-cp-read-fields xs kinds)
           :in-theory (enable fn-cp-read-fields fn-cp-read-id fn-cp-read-u32 fn-cp-id-bytes
                              fn-cp-fields-encode fn-cp-nth))))

(defthm fn-wf-cp-read-fields-shape
  (implies (equal (car (fn-cp-read-fields xs kinds)) :ok)
           (and (true-listp (fn-cp-nth 1 (fn-cp-read-fields xs kinds)))
                (equal (len (fn-cp-nth 1 (fn-cp-read-fields xs kinds))) (len kinds))))
  :hints (("Goal" :induct (fn-cp-read-fields xs kinds)
           :in-theory (enable fn-cp-read-fields fn-cp-read-id fn-cp-read-u32 fn-cp-nth))))
(defthm fn-wf-nine-nths
  (implies (and (true-listp v) (equal (len v) 9))
           (equal (list (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v) (fn-cp-nth 3 v)
                        (fn-cp-nth 4 v) (fn-cp-nth 5 v) (fn-cp-nth 6 v) (fn-cp-nth 7 v)
                        (fn-cp-nth 8 v))
                  v))
  :hints (("Goal" :in-theory (enable fn-cp-nth)
           :expand ((len v) (len (cdr v)) (len (cddr v)) (len (cdddr v)) (len (cddddr v))
                    (len (cdr (cddddr v))) (len (cddr (cddddr v))) (len (cdddr (cddddr v)))
                    (len (cddddr (cddddr v))) (len (cdr (cddddr (cddddr v))))))))
(defthm fn-wf-header-reassemble
  (implies (and (<= 5 (len x)) (equal (take 4 x) m))
           (equal (append m (cons (fn-cp-nth 4 x) (nthcdr 5 x))) x))
  :hints (("Goal" :in-theory (enable fn-cp-nth)
           :expand ((take 4 x) (take 3 (cdr x)) (take 2 (cddr x)) (take 1 (cdddr x))
                    (nthcdr 5 x) (nthcdr 4 (cdr x)) (nthcdr 3 (cddr x)) (nthcdr 2 (cdddr x))
                    (nthcdr 1 (cddddr x))))))

(defthm fn-wf-cp-cursor-decode-inversion
  (let* ((f (fn-cp-read-fields (nthcdr 5 x) '(:id :id :id :id :id :uint :uint :uint :uint)))
         (v (fn-cp-nth 1 f)))
    (implies (equal (car (fn-cp-cursor-decode x)) :ok)
             (and (fn-cbor-octet-listp x)
                  (equal (take 4 x) *fn-cp-magic*)
                  (equal (fn-cp-nth 4 x) *fn-cp-version*)
                  (equal (car f) :ok)
                  (not (consp (fn-cp-nth 2 f)))
                  (fn-cp-cursorp (cadr (fn-cp-cursor-decode x)))
                  (equal (cadr (fn-cp-cursor-decode x))
                         (fn-cp-cursor (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v)
                                       (fn-cp-nth 3 v) (fn-cp-nth 4 v) (fn-cp-nth 5 v)
                                       (fn-cp-nth 6 v) (fn-cp-nth 7 v) (fn-cp-nth 8 v))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-cp-cursor-decode car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

(defthm fn-wf-cp-read-fields-rest-true-listp
  (implies (and (true-listp xs) (equal (car (fn-cp-read-fields xs kinds)) :ok))
           (true-listp (fn-cp-nth 2 (fn-cp-read-fields xs kinds))))
  :hints (("Goal" :induct (fn-cp-read-fields xs kinds)
           :in-theory (enable fn-cp-read-fields fn-cp-read-id fn-cp-read-u32 fn-cp-nth))))
(defthm fn-wf-cp-nth-of-cursor
  (and (equal (fn-cp-nth 1 (fn-cp-cursor a b c d e f g h i)) a)
       (equal (fn-cp-nth 2 (fn-cp-cursor a b c d e f g h i)) b)
       (equal (fn-cp-nth 3 (fn-cp-cursor a b c d e f g h i)) c)
       (equal (fn-cp-nth 4 (fn-cp-cursor a b c d e f g h i)) d)
       (equal (fn-cp-nth 5 (fn-cp-cursor a b c d e f g h i)) e)
       (equal (fn-cp-nth 6 (fn-cp-cursor a b c d e f g h i)) f)
       (equal (fn-cp-nth 7 (fn-cp-cursor a b c d e f g h i)) g)
       (equal (fn-cp-nth 8 (fn-cp-cursor a b c d e f g h i)) h)
       (equal (fn-cp-nth 9 (fn-cp-cursor a b c d e f g h i)) i))
  :hints (("Goal" :in-theory (enable fn-cp-nth fn-cp-cursor))))

(defthm fn-wf-cp-encode-of-read
  (implies (and (true-listp v) (equal (len v) 9)
                (equal (append (fn-cp-fields-encode v '(:id :id :id :id :id :uint :uint :uint :uint))
                               rest)
                       (nthcdr 5 x))
                (true-listp rest) (not (consp rest))
                (fn-cp-cursorp (fn-cp-cursor (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v)
                                             (fn-cp-nth 3 v) (fn-cp-nth 4 v) (fn-cp-nth 5 v)
                                             (fn-cp-nth 6 v) (fn-cp-nth 7 v) (fn-cp-nth 8 v)))
                (<= 5 (len x))
                (equal (take 4 x) *fn-cp-magic*)
                (equal (fn-cp-nth 4 x) *fn-cp-version*))
           (equal (fn-cp-cursor-encode
                   (fn-cp-cursor (fn-cp-nth 0 v) (fn-cp-nth 1 v) (fn-cp-nth 2 v)
                                 (fn-cp-nth 3 v) (fn-cp-nth 4 v) (fn-cp-nth 5 v)
                                 (fn-cp-nth 6 v) (fn-cp-nth 7 v) (fn-cp-nth 8 v)))
                  x))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-header-reassemble (m *fn-cp-magic*))
                 fn-wf-nine-nths)
           :in-theory (disable fn-cp-cursorp fn-cp-cursor fn-cp-fields-encode
                               fn-wf-header-reassemble fn-wf-nine-nths fn-wf-fncu-encode-agrees fn-wf-fncu-encode-agrees-fields))))

(defthm fn-wf-octets-true-listp-of-nthcdr
  (implies (fn-cbor-octet-listp x) (true-listp (nthcdr n x))))
(defthm fn-wf-octets-of-nthcdr
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr n x))))
(defthm fn-wf-cp-read-fields-of-empty
  (implies (and (not (consp xs)) (equal (car kinds) :id))
           (not (equal (car (fn-cp-read-fields xs kinds)) :ok)))
  :hints (("Goal" :expand ((fn-cp-read-fields xs kinds))
           :in-theory (enable fn-cp-read-id))))

(defthm fn-wf-nthcdr-of-atom
  (implies (not (consp x)) (not (consp (nthcdr n x)))))
(defthm fn-wf-len-when-nthcdr-consp
  (implies (consp (nthcdr n x)) (< (nfix n) (len x)))
  :rule-classes nil
  :hints (("Goal" :induct (nthcdr n x))))

; C-0c (redregg/work/FN-660-RESPONSE-20261004.md): the direction the cursor
; lacked.  An accepted cursor's octets are the encoding of the cursor they
; decode to, so the cursor's grammar is canonical.
(defthm fn-cp-cursor-encode-decode-roundtrip
  (implies (equal (car (fn-cp-cursor-decode x)) :ok)
           (equal (fn-cp-cursor-encode (cadr (fn-cp-cursor-decode x))) x))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-cp-cursor-decode-inversion
                 (:instance fn-wf-len-when-nthcdr-consp (n 5))
                 (:instance fn-wf-cp-read-fields-of-empty (xs (nthcdr 5 x))
                            (kinds '(:id :id :id :id :id :uint :uint :uint :uint)))
                 (:instance fn-wf-cp-encode-of-read
                            (v (fn-cp-nth 1 (fn-cp-read-fields (nthcdr 5 x) '(:id :id :id :id :id :uint :uint :uint :uint))))
                            (rest (fn-cp-nth 2 (fn-cp-read-fields (nthcdr 5 x) '(:id :id :id :id :id :uint :uint :uint :uint)))))
                 (:instance fn-wf-cp-read-fields-inverse
                            (xs (nthcdr 5 x))
                            (kinds '(:id :id :id :id :id :uint :uint :uint :uint)))
                 (:instance fn-wf-cp-read-fields-shape
                            (xs (nthcdr 5 x))
                            (kinds '(:id :id :id :id :id :uint :uint :uint :uint)))
                 (:instance fn-wf-cp-read-fields-rest-true-listp
                            (xs (nthcdr 5 x))
                            (kinds '(:id :id :id :id :id :uint :uint :uint :uint))))
           :in-theory (disable fn-cp-cursor-decode fn-cp-read-fields fn-cp-cursor-encode
                               fn-cp-fields-encode fn-cp-cursorp fn-cp-cursor fn-cp-nth
                               fn-wf-fncu-encode-agrees fn-wf-fncu-encode-agrees-fields
                               fn-cp-cursor-encode-fields))))

(defthm fn-wf-at-mostp-of-len
  (implies (and (natp n) (<= (len x) n)) (fn-cbor-at-mostp x n)))
(defthm fn-wf-fncu-value-is-a-cursor
  (implies (fn-wg-valuep *fn-wf-fncu-grammar* v)
           (and (fn-cp-cursorp (fn-wf-fncu-cursor v))
                (equal (fn-wf-fncu-value (fn-wf-fncu-cursor v)) v)))
  :hints (("Goal" :in-theory (enable fn-wg-valuep-opener-seq fn-wg-next fn-cp-cursorp
                                     fn-cp-nth fn-cp-idp fn-cp-uintp))))

(defthm fn-wf-fncu-wg-decode-of-host-encode
  (implies (fn-cp-cursorp c)
           (equal (fn-wg-decode *fn-wf-fncu-grammar* (fn-cp-cursor-encode c))
                  (fn-wg-ok (fn-wf-fncu-value c) nil)))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-fncu-encode-agrees
                 (:instance fn-wg-decode-of-encode (g *fn-wf-fncu-grammar*)
                            (v (fn-wf-fncu-value c)) (r nil))
                 (:instance fn-wg-encode-octets (g *fn-wf-fncu-grammar*) (v (fn-wf-fncu-value c))))
           :in-theory (union-theories '(fn-wf-fncu-grammarp fn-wg-app-nil fn-wg-octet-listp-true-listp
                                        (:executable-counterpart fn-wg-delimitedp)
                                        (:executable-counterpart fn-cbor-octet-listp)
                                        (:executable-counterpart fn-wg-grammarp))
                                      (theory 'minimal-theory)))))

(defthm fn-wf-fncu-host-accept-implies-wg
  (implies (equal (car (fn-cp-cursor-decode x)) :ok)
           (equal (fn-wg-decode *fn-wf-fncu-grammar* x)
                  (fn-wg-ok (fn-wf-fncu-value (cadr (fn-cp-cursor-decode x))) nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-cp-cursor-encode-decode-roundtrip
                 fn-wf-cp-cursor-decode-inversion
                 (:instance fn-wf-fncu-wg-decode-of-host-encode (c (cadr (fn-cp-cursor-decode x)))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-wf-fncu-wg-accept-implies-host
   (implies (and (fn-cbor-octet-listp x)
                 (fn-wg-okp (fn-wg-decode *fn-wf-fncu-grammar* x))
                 (null (fn-wg-rest (fn-wg-decode *fn-wf-fncu-grammar* x))))
            (equal (fn-cp-cursor-decode x)
                   (list :ok (fn-wf-fncu-cursor (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* x))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-wg-encode-of-decode (g *fn-wf-fncu-grammar*) (xs x))
                  (:instance fn-wf-fncu-value-is-a-cursor
                             (v (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* x))))
                  (:instance fn-wf-fncu-encode-agrees
                             (c (fn-wf-fncu-cursor (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* x)))))
                  (:instance fn-cp-cursor-decode-encode-roundtrip
                             (c (fn-wf-fncu-cursor (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* x))))))
            :in-theory (disable fn-wg-encode-of-decode fn-wf-fncu-value-is-a-cursor
                                fn-wf-fncu-encode-agrees fn-cp-cursor-decode-encode-roundtrip
                                fn-cp-cursor-decode fn-cp-cursor-encode fn-cp-cursorp
                                fn-wf-fncu-cursor fn-wf-fncu-value
                                fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp))))

(defthm fn-wf-fncu-cursor-of-value
  (implies (fn-cp-cursorp c)
           (equal (fn-wf-fncu-cursor (fn-wf-fncu-value c)) c))
  :hints (("Goal" :in-theory (enable fn-cp-cursorp fn-cp-nth))))

; KEYSTONE (agreement).  The host's cursor decoder accepts exactly the octets
; the exported grammar accepts whole, and answers the same cursor.
(defthm fn-wf-fncu-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (and (iff (equal (car (fn-cp-cursor-decode x)) :ok)
                     (and (fn-wg-okp (fn-wg-decode *fn-wf-fncu-grammar* x))
                          (null (fn-wg-rest (fn-wg-decode *fn-wf-fncu-grammar* x)))))
                (implies (equal (car (fn-cp-cursor-decode x)) :ok)
                         (equal (cadr (fn-cp-cursor-decode x))
                                (fn-wf-fncu-cursor
                                 (fn-wg-value (fn-wg-decode *fn-wf-fncu-grammar* x)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-fncu-host-accept-implies-wg
                 fn-wf-fncu-wg-accept-implies-host
                 fn-wf-cp-cursor-decode-inversion
                 (:instance fn-wf-fncu-cursor-of-value (c (cadr (fn-cp-cursor-decode x)))))
           :in-theory (union-theories '(fn-wg-result-accessors car-cons cdr-cons)
                                      (theory 'minimal-theory)))))
