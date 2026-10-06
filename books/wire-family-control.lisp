; fn: the reasoned and lined control replies as exported wire grammars (Mini
; M5, planning/design/wire-grammar-2026-10-04.md section 4, families 3).
;
; FNCT kind 18 (books/native-control-reason.lisp: the status, then the
; reason word) and kind 23 (books/native-control-line.lisp: the status, the
; reason word, then one printable line) are written in the frame-field
; grammar (books/frame-fields.lisp): a status enumeration octet (1 + its
; position in *fn-nctrl-statuses*) and u32-length blobs.  This book states
; each as a grammar of books/wire-grammar.lisp and proves the host codec
; agrees with the interpreter at it.  The kind-22 consumer request, which
; these replies answer, is books/wire-family-consumer.lisp's.
;
; This book owns the prefix `fn-wf-ctl-' (with the other `fn-wf-' books).

(in-package "ACL2")
(include-book "wire-family-fnct")
(include-book "native-control-line")

; -----------------------------------------------------------------------------
; Frame fields as grammar nodes, once.  A status enumeration field
; (cons :enum NAMES) is (:enum 1 1 NAMES); a u32-length blob field
; (cons :blob M) is (:bytes 4 1 M :any).  For any list of such specs the
; host's fn-frame-fields-parse accepts exactly what the interpreter accepts
; whole at (:seq ...) of their nodes, with the same values, and
; fn-frame-fields-octets is fn-wg-encode there.

(local
 (defthm fn-wf-ctl-len-nthcdr
   (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
   :hints (("Goal" :induct (nthcdr n x)))))
(local
 (defthm fn-wf-ctl-len-take
   (equal (len (take n x)) (nfix n))))
(local
 (defthm fn-wf-ctl-wg-take-is-take
   (implies (<= (nfix n) (len xs))
            (equal (fn-wg-take n xs) (take n xs)))))
(local
 (defthm fn-wf-ctl-wg-drop-is-nthcdr
   (implies (true-listp xs)
            (equal (fn-wg-drop n xs) (nthcdr n xs)))))
(local
 (defthm fn-wf-ctl-split
   (implies (and (natp n) (true-listp xs))
            (equal (fn-frame-split n xs)
                   (if (<= n (len xs)) (cons (take n xs) (nthcdr n xs)) nil)))
   :hints (("Goal" :induct (fn-frame-split n xs) :in-theory (enable fn-frame-split)))))
(local
 (defthm fn-wf-ctl-item-is-nth
   (equal (fn-frame-item n xs) (nth n xs))
   :hints (("Goal" :in-theory (enable fn-frame-item nth)))))
(local
 (defthm fn-wf-ctl-octets-of-take
   (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
            (fn-cbor-octet-listp (take n xs)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local
 (defthm fn-wf-ctl-octets-of-nthcdr
   (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (nthcdr n x)))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local
 (defthm fn-wf-ctl-be-value-of-take-4
   (implies (and (fn-cbor-octet-listp xs) (<= 4 (len xs)))
            (equal (fn-wg-be-value (take 4 xs)) (fn-cbor-u32-from (take 4 xs))))
   :hints (("Goal" :in-theory (enable fn-wg-be-value fn-wg-le-value fn-wg-rev fn-cbor-u32-from
                                      fn-cbor-octet-listp)
            :expand ((take 4 xs) (take 3 (cdr xs)) (take 2 (cddr xs)) (take 1 (cdddr xs)))))))
(defconst *fn-wf-ctl-status* `(:enum 1 1 ,*fn-nctrl-statuses*))
(defun fn-wf-ctl-blob (m) (declare (xargs :guard t)) (list :bytes 4 1 m :any))
(defthm fn-wf-ctl-blob-field
  (implies (and (fn-cbor-octet-listp b) (posp m) (<= m 4294967295))
           (let ((f (fn-frame-field-parse (cons :blob m) b)))
             (equal (fn-wg-decode (fn-wf-ctl-blob m) b)
                    (if (fn-frame-parse-okp f)
                        (fn-wg-ok (fn-frame-parse-value f) (fn-frame-parse-rest f))
                      (fn-wg-malformed)))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-bytes fn-frame-field-parse fn-frame-parse-okp
                                   fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok fn-frame-parse-error
                                   fn-frame-parse-counted fn-frame-wide-blob-specp fn-wf-ctl-blob fn-wg-arg fn-wg-op)
                                  (fn-wg-decode fn-cbor-u32-from fn-wg-be-value))
           :do-not-induct t
           :use ((:instance fn-frame-u32-from-is-natural (xs (take 4 b)))))))
(local
 (defthm fn-wf-ctl-blob-field-len
   (implies (and (fn-cbor-octet-listp b) (posp m)
                 (fn-frame-parse-okp (fn-frame-field-parse (cons :blob m) b)))
            (let ((f (fn-frame-field-parse (cons :blob m) b)))
              (and (equal (len b) (+ 4 (len (fn-frame-parse-value f)) (len (fn-frame-parse-rest f))))
                   (<= (len (fn-frame-parse-value f)) m)
                   (fn-cbor-octet-listp (fn-frame-parse-rest f)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-frame-field-parse fn-frame-parse-okp
                                    fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok fn-frame-parse-error
                                    fn-frame-parse-counted fn-frame-wide-blob-specp)
                                   (fn-cbor-u32-from))))))
(local
 (defthm fn-wf-ctl-enum-field-len
   (implies (and (fn-cbor-octet-listp b)
                 (fn-frame-parse-okp (fn-frame-field-parse (cons :enum s) b)))
            (let ((f (fn-frame-field-parse (cons :enum s) b)))
              (and (equal (len b) (+ 1 (len (fn-frame-parse-rest f))))
                   (fn-cbor-octet-listp (fn-frame-parse-rest f)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-frame-field-parse fn-frame-parse-okp fn-frame-wide-blob-specp
                                      fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok
                                      fn-frame-parse-error)))))
(defun fn-wf-ctl-field-grammar (spec)
  (declare (xargs :guard t))
  (if (and (consp spec) (equal (car spec) :enum))
      (list :enum 1 1 (cdr spec))
    (list :bytes 4 1 (if (consp spec) (cdr spec) 0) :any)))
(defun fn-wf-ctl-field-specp (spec)
  (declare (xargs :guard t))
  (or (and (consp spec) (equal (car spec) :enum) (true-listp (cdr spec)))
      (fn-frame-wide-blob-specp spec)))
(defun fn-wf-ctl-field-grammars (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (cons (fn-wf-ctl-field-grammar (car specs)) (fn-wf-ctl-field-grammars (cdr specs)))
    nil))
(defun fn-wf-ctl-field-specsp (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (and (fn-wf-ctl-field-specp (car specs)) (fn-wf-ctl-field-specsp (cdr specs)))
    t))
(defthm fn-wf-ctl-enum-field-any
  (implies (and (fn-cbor-octet-listp b) (true-listp s))
           (let ((f (fn-frame-field-parse (cons :enum s) b)))
             (equal (fn-wg-decode (list :enum 1 1 s) b)
                    (if (fn-frame-parse-okp f)
                        (fn-wg-ok (fn-frame-parse-value f) (fn-frame-parse-rest f))
                      (fn-wg-malformed)))))
  :hints (("Goal" :in-theory (e/d (fn-wg-decode-opener-enum fn-frame-field-parse fn-frame-parse-okp
                                   fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok fn-frame-parse-error
                                   fn-wg-be-value fn-wg-le-value fn-wg-rev fn-wg-arg fn-wg-op
                                   fn-frame-wide-blob-specp)
                                  (fn-wg-decode))
           :expand ((take 1 b)))))
(local
 (defthm fn-wf-ctl-cons-tag
   (implies (and (consp spec) (equal (car spec) tag))
            (equal (cons tag (cdr spec)) spec))))
(defthm fn-wf-ctl-field-decode
  (implies (and (fn-cbor-octet-listp b) (fn-wf-ctl-field-specp spec))
           (let ((f (fn-frame-field-parse spec b)))
             (equal (fn-wg-decode (fn-wf-ctl-field-grammar spec) b)
                    (if (fn-frame-parse-okp f)
                        (fn-wg-ok (fn-frame-parse-value f) (fn-frame-parse-rest f))
                      (fn-wg-malformed)))))
  :hints (("Goal" :do-not-induct t
           :cases ((and (consp spec) (equal (car spec) :enum))))
          ("Subgoal 1" :use ((:instance fn-wf-ctl-enum-field-any (s (cdr spec))))
           :in-theory (union-theories '(fn-wf-ctl-field-grammar fn-wf-ctl-field-specp fn-wf-ctl-cons-tag fn-frame-wide-blob-specp)
                                      (theory 'minimal-theory)))
          ("Subgoal 2" :use ((:instance fn-wf-ctl-blob-field (m (cdr spec))))
           :in-theory (union-theories '(fn-wf-ctl-field-grammar fn-wf-ctl-field-specp fn-frame-wide-blob-specp
                                        fn-wf-ctl-blob fn-wf-ctl-cons-tag posp)
                                      (theory 'minimal-theory)))))
(defthm fn-wf-wg-decode-seq-cons
  (equal (fn-wg-decode (cons :seq (cons g rest)) xs)
         (let ((r1 (fn-wg-decode g xs)))
           (if (fn-wg-okp r1)
               (let ((r2 (fn-wg-decode (cons :seq rest) (fn-wg-rest r1))))
                 (if (fn-wg-okp r2)
                     (fn-wg-ok (cons (fn-wg-value r1) (fn-wg-value r2)) (fn-wg-rest r2))
                   r2))
             r1)))
  :hints (("Goal" :in-theory (enable fn-wg-decode-opener-seq fn-wg-next fn-wg-arg fn-wg-op))))
(defthm fn-wf-wg-decode-seq-nil
  (equal (fn-wg-decode (cons :seq nil) xs) (fn-wg-ok nil xs))
  :hints (("Goal" :in-theory (enable fn-wf-wg-decode-empty-seq))))
(in-theory (disable fn-wf-wg-decode-seq-cons fn-wf-wg-decode-seq-nil))
(defthm fn-wf-ctl-fields-decode
  (implies (and (fn-cbor-octet-listp b) (fn-wf-ctl-field-specsp specs))
           (let ((f (fn-frame-fields-parse-aux specs b)))
             (equal (fn-wg-decode (cons :seq (fn-wf-ctl-field-grammars specs)) b)
                    (if (fn-frame-parse-okp f)
                        (fn-wg-ok (fn-frame-parse-value f) (fn-frame-parse-rest f))
                      (fn-wg-malformed)))))
  :hints (("Goal" :induct (fn-frame-fields-parse-aux specs b)
           :expand ((fn-wf-ctl-field-grammars specs) (fn-frame-fields-parse-aux specs b))
           :in-theory (e/d (fn-frame-fields-parse-aux fn-wf-ctl-field-grammars fn-wf-ctl-field-specsp
                            fn-wf-wg-decode-seq-cons fn-wf-wg-decode-seq-nil fn-wg-result-accessors fn-frame-field-parse-rest-octets
                            fn-frame-parse-okp-of-ok fn-frame-parse-value-of-ok fn-frame-parse-rest-of-ok)
                           (fn-wg-decode fn-frame-field-parse fn-wf-ctl-field-grammar fn-wf-ctl-field-specp
                            fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok
                            fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value)))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest fn-frame-parse-ok
                                    fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value fn-wg-malformed fn-wg-refused)))))
(defun fn-wf-ctl-specs-width (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (+ (if (and (consp (car specs)) (equal (car (car specs)) :enum)) 1
           (+ 4 (nfix (if (consp (car specs)) (cdr (car specs)) 0))))
         (fn-wf-ctl-specs-width (cdr specs)))
    0))
(defthm fn-wf-ctl-fields-len
  (implies (and (fn-cbor-octet-listp b) (fn-wf-ctl-field-specsp specs)
                (fn-frame-parse-okp (fn-frame-fields-parse-aux specs b)))
           (<= (len b) (+ (fn-wf-ctl-specs-width specs)
                          (len (fn-frame-parse-rest (fn-frame-fields-parse-aux specs b))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-frame-fields-parse-aux specs b)
           :in-theory (e/d (fn-frame-fields-parse-aux fn-wf-ctl-field-specsp fn-wf-ctl-field-specp
                            fn-frame-wide-blob-specp fn-frame-field-parse-rest-octets
                            fn-frame-parse-okp-of-ok fn-frame-parse-value-of-ok fn-frame-parse-rest-of-ok)
                           (fn-frame-field-parse fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest
                            fn-frame-parse-ok)))
          ("Subgoal *1/3" :use ((:instance fn-wf-ctl-enum-field-len (s (cdr (car specs))))
                                (:instance fn-wf-ctl-blob-field-len (m (cdr (car specs))))
                                (:instance fn-wf-ctl-cons-tag (spec (car specs)) (tag :enum))
                                (:instance fn-wf-ctl-cons-tag (spec (car specs)) (tag :blob))))))
(defthm fn-wf-ctl-fields-agree
  (implies (and (fn-cbor-octet-listp p) (fn-wf-ctl-field-specsp specs))
           (let ((f (fn-frame-fields-parse specs p))
                 (w (fn-wg-decode (cons :seq (fn-wf-ctl-field-grammars specs)) p)))
             (and (iff (fn-frame-parse-okp f) (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (fn-frame-parse-okp f)
                           (and (equal (fn-wg-value w) (fn-frame-parse-value f))
                                (<= (len p) (fn-wf-ctl-specs-width specs)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-wf-ctl-fields-decode (:instance fn-wf-ctl-fields-len (b p)))
           :in-theory (e/d (fn-frame-fields-parse fn-wg-result-accessors fn-frame-parse-error-is-failure)
                           (fn-wf-ctl-fields-decode fn-wg-decode fn-frame-fields-parse-aux
                            fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value fn-wf-ctl-field-grammars
                            fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest)))
          (and stable-under-simplificationp
               '(:in-theory (enable fn-wg-okp fn-wg-ok fn-wg-rest fn-wg-value fn-wg-malformed fn-wg-refused)))))
(defthm fn-wf-ctl-fields-value-shape
  (implies (fn-frame-parse-okp (fn-frame-fields-parse-aux specs b))
           (and (true-listp (fn-frame-parse-value (fn-frame-fields-parse-aux specs b)))
                (equal (len (fn-frame-parse-value (fn-frame-fields-parse-aux specs b))) (len specs))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-frame-fields-parse-aux specs b)
           :in-theory (e/d (fn-frame-fields-parse-aux fn-frame-parse-okp-of-ok fn-frame-parse-value-of-ok)
                           (fn-frame-field-parse fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest
                            fn-frame-parse-ok)))))
(local
 (defthm fn-wf-ctl-enum-index-nonzero-member
   (iff (equal (fn-frame-enum-index v s) 0) (not (member-equal v s)))
   :hints (("Goal" :in-theory (enable fn-frame-enum-index)))))
(local
 (defthm fn-wf-ctl-at-most-len
   (implies (fn-cbor-at-mostp x n) (<= (len x) (nfix n)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))
(local
 (defthm fn-wf-ctl-enum-index-is-position
   (implies (member-equal v s)
            (equal (fn-frame-enum-index v s) (+ 1 (fn-wg-position v s))))
   :hints (("Goal" :in-theory (enable fn-frame-enum-index fn-wg-position)))))
(local
 (defthm fn-wf-ctl-consp-len
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))
(defthm fn-wf-ctl-field-encode
  (implies (and (fn-wf-ctl-field-specp spec) (fn-frame-field-okp spec v)
                (or (not (equal (car spec) :enum)) (< (len (cdr spec)) 255)))
           (and (fn-wg-valuep (fn-wf-ctl-field-grammar spec) v)
                (equal (fn-wg-encode (fn-wf-ctl-field-grammar spec) v)
                       (fn-frame-field-octets spec v))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-wf-ctl-field-grammar fn-wf-ctl-field-specp fn-frame-field-okp
                            fn-frame-field-octets fn-frame-wide-blob-specp fn-frame-blob-withinp
                            fn-frame-enum-specp
                            fn-wg-encode-opener-enum fn-wg-encode-opener-bytes fn-wg-valuep-opener-enum
                            fn-wg-valuep-opener-bytes fn-wg-app-is-append fn-wg-arg fn-wg-op)
                           (fn-wg-encode fn-wg-valuep fn-cbor-u32-bytes fn-wg-be-bytes fn-wg-position
                            fn-frame-enum-index)))))
(defun fn-wf-ctl-enum-small (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (and (or (not (and (consp (car specs)) (equal (car (car specs)) :enum)))
               (< (len (cdr (car specs))) 255))
           (fn-wf-ctl-enum-small (cdr specs)))
    t))
(defthm fn-wf-wg-encode-seq-cons
  (and (equal (fn-wg-encode (cons :seq (cons g rest)) v)
              (fn-wg-app (fn-wg-encode g (car v)) (fn-wg-encode (cons :seq rest) (cdr v))))
       (equal (fn-wg-valuep (cons :seq (cons g rest)) v)
              (and (consp v) (fn-wg-valuep g (car v)) (fn-wg-valuep (cons :seq rest) (cdr v)))))
  :hints (("Goal" :in-theory (e/d (fn-wg-next fn-wg-arg fn-wg-op) (fn-wg-encode-opener-seq fn-wg-valuep-opener-seq))
           :expand ((fn-wg-encode (cons :seq (cons g rest)) v) (fn-wg-valuep (cons :seq (cons g rest)) v)))))
(defthm fn-wf-wg-encode-seq-nil
  (and (equal (fn-wg-encode (cons :seq nil) v) nil)
       (equal (fn-wg-valuep (cons :seq nil) v) (null v)))
  :hints (("Goal" :in-theory (enable fn-wf-wg-encode-empty-seq))))
(in-theory (disable fn-wf-wg-encode-seq-cons fn-wf-wg-encode-seq-nil))
(local
 (defthm fn-wf-ctl-field-octets-true-listp
   (implies (and (fn-wf-ctl-field-specp spec) (fn-frame-field-okp spec v))
            (true-listp (fn-frame-field-octets spec v)))
   :hints (("Goal" :in-theory (enable fn-wf-ctl-field-specp fn-frame-field-okp fn-frame-field-octets
                                      fn-frame-wide-blob-specp fn-frame-blob-withinp fn-frame-enum-specp)))))
(defthm fn-wf-ctl-fields-encode
  (implies (and (fn-wf-ctl-field-specsp specs) (fn-wf-ctl-enum-small specs)
                (fn-frame-values-okp specs values))
           (and (fn-wg-valuep (cons :seq (fn-wf-ctl-field-grammars specs)) values)
                (equal (fn-wg-encode (cons :seq (fn-wf-ctl-field-grammars specs)) values)
                       (fn-frame-fields-octets specs values))))
  :hints (("Goal" :induct (fn-frame-fields-octets specs values)
           :do-not '(generalize eliminate-destructors fertilize)
           :expand ((fn-wf-ctl-field-grammars specs))
           :in-theory (e/d (fn-frame-fields-octets fn-frame-values-okp fn-wf-ctl-field-specsp fn-wf-ctl-enum-small
                            fn-wf-wg-encode-seq-cons fn-wf-wg-encode-seq-nil fn-wg-app-is-append)
                           (fn-wg-encode fn-wg-valuep fn-frame-field-octets fn-frame-field-okp
                            fn-wf-ctl-field-grammar fn-wf-ctl-field-specp)))))

; -----------------------------------------------------------------------------
; fnct.reasoned-reply (FNCT kind 18, payload at most 517 octets): the status
; and the reason word.

(defconst *fn-wf-ctl-reasoned-payload*
  (cons :seq (fn-wf-ctl-field-grammars *fn-nctrl-reasoned-reply-spec*)))
(defconst *fn-wf-ctl-reasoned-reply-grammar*
  `(:frame (70 78 67 84) 1 18 517 ,*fn-wf-ctl-reasoned-payload*))
(defthm fn-wf-ctl-reasoned-grammarp
  (and (fn-wg-grammarp *fn-wf-ctl-reasoned-payload*)
       (fn-wg-grammarp *fn-wf-ctl-reasoned-reply-grammar*)
       (fn-wf-ctl-field-specsp *fn-nctrl-reasoned-reply-spec*)
       (fn-wf-ctl-enum-small *fn-nctrl-reasoned-reply-spec*)
       (equal (fn-frame-specs-width *fn-nctrl-reasoned-reply-spec*) 517)))
(defthm fn-wf-ctl-reasoned-payload-agrees
  (implies (fn-cbor-octet-listp p)
           (let ((h (fn-nctrl-reasoned-reply-payload-decode (fn-frame-ok '(70 78 67 84) 1 18 p)))
                 (w (fn-wg-decode *fn-wf-ctl-reasoned-payload* p)))
             (and (iff (not (equal h :bad))
                       (and (fn-wg-okp w) (null (fn-wg-rest w)) (<= (len p) 517)))
                  (implies (not (equal h :bad))
                           (equal (fn-wg-value w) h)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-fields-agree (specs *fn-nctrl-reasoned-reply-spec*))
                 (:instance fn-wf-ctl-fields-value-shape (specs *fn-nctrl-reasoned-reply-spec*) (b p)))
           :in-theory (e/d (fn-nctrl-reasoned-reply-payload-decode fn-frame-fields-parse
                            fn-frame-parse-error-is-failure)
                           (fn-wf-ctl-fields-agree fn-wg-decode fn-frame-fields-parse-aux
                            fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest)))))
(defthm fn-wf-ctl-open-is-frame-decode
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x)) *fn-nctrl-max-payload*)))
             (equal (fn-nctrl-open x k)
                    (if (and (fn-frame-result-okp r)
                             (equal (fn-frame-result-magic r) (list 70 78 67 84))
                             (equal (fn-frame-result-version r) 1)
                             (equal (fn-frame-result-kind r) k))
                        (fn-frame-ok (list 70 78 67 84) 1 k (fn-frame-result-payload r))
                      (fn-frame-error :control-frame)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-wf-fnct-decode-ok-is-frame-ok
                                   (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                                   (mx *fn-nctrl-max-payload*)))
           :in-theory (e/d (fn-nctrl-open) (fn-frame-decode fn-frame-trailer fn-frame-protected-prefix)))))
(defthm fn-wf-ctl-bad-of-error
  (implies (not (fn-frame-result-okp r))
           (and (equal (fn-nctrl-reasoned-reply-payload-decode r) :bad)
                (equal (fn-ncline-reply-payload-decode r) :bad)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nctrl-reasoned-reply-payload-decode fn-ncline-reply-payload-decode))))
; KEYSTONE (agreement), kind 18.
(defthm fn-wf-ctl-reasoned-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-nctrl-reasoned-reply-payload-decode (fn-nctrl-open x 18)))
                 (w (fn-wg-decode *fn-wf-ctl-reasoned-reply-grammar* x)))
             (and (iff (not (equal r :bad))
                       (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (not (equal r :bad))
                           (equal (fn-wg-value w) r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-open-is-frame-decode (k 18))
                 (:instance fn-wf-fnct-whole-decode (g *fn-wf-ctl-reasoned-payload*) (k 18) (mx 517)
                            (hm *fn-nctrl-max-payload*))
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                            (max-payload *fn-nctrl-max-payload*))
                 (:instance fn-wf-ctl-reasoned-payload-agrees
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x))
                                                 *fn-nctrl-max-payload*))))
                 (:instance fn-wf-ctl-bad-of-error (r '(:error :control-frame))))
           :in-theory (union-theories '(fn-wf-ctl-reasoned-grammarp (:e fn-cbor-octetp) (:e natp) (:e <) (:e equal)
                                        (:e fn-frame-error) (:e fn-frame-result-okp))
                                      (theory 'minimal-theory)))))
; KEYSTONE (agreement), kind 18.
(defthm fn-wf-ctl-reasoned-encode-agrees
  (implies (not (equal (fn-native-control-reasoned-reply-encode status reason) :bad))
           (let ((v (list status (fn-nctrl-reason-word reason))))
             (and (fn-wg-valuep *fn-wf-ctl-reasoned-reply-grammar* v)
                  (equal (fn-native-control-reasoned-reply-encode status reason)
                         (fn-wg-encode *fn-wf-ctl-reasoned-reply-grammar* v)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-fields-encode (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-frame-fields-octets-within-width (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-frame-fields-octets-are-octets (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-wf-fnct-host-seal-is-wg-encode (g *fn-wf-ctl-reasoned-payload*) (k 18) (mx 517)
                            (v (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-wf-fnct-nctrl-seal-is-host-framing (k 18)
                            (p (fn-frame-fields-octets *fn-nctrl-reasoned-reply-spec*
                                                       (list status (fn-nctrl-reason-word reason))))))
           :in-theory (e/d (fn-native-control-reasoned-reply-encode)
                           (fn-wf-ctl-fields-encode fn-wf-fnct-host-seal-is-wg-encode fn-nctrl-seal fn-wg-encode
                            fn-wg-valuep fn-frame-fields-octets-within-width fn-frame-fields-octets-are-octets
                            fn-wg-encode-opener-frame fn-wg-valuep-opener-frame fn-frame-protected fn-frame-trailer
                            fn-frame-fields-octets fn-frame-values-okp fn-nctrl-reason-word)))))

; -----------------------------------------------------------------------------
; fnct.line-reply (FNCT kind 23, payload at most 1545 octets): the status,
; the reason word and one printable line (1..1024 octets).  The encoder
; sends kind 18 instead when it has no line; with a line it sends this.

(defconst *fn-wf-ctl-lined-payload*
  (cons :seq (fn-wf-ctl-field-grammars *fn-ncline-reply-spec*)))
(defconst *fn-wf-ctl-lined-reply-grammar*
  `(:frame (70 78 67 84) 1 23 1545 ,*fn-wf-ctl-lined-payload*))
(defthm fn-wf-ctl-lined-grammarp
  (and (fn-wg-grammarp *fn-wf-ctl-lined-payload*)
       (fn-wg-grammarp *fn-wf-ctl-lined-reply-grammar*)
       (fn-wf-ctl-field-specsp *fn-ncline-reply-spec*)
       (fn-wf-ctl-enum-small *fn-ncline-reply-spec*)
       (equal (fn-frame-specs-width *fn-ncline-reply-spec*) 1545)))
(defthm fn-wf-ctl-lined-payload-agrees
  (implies (fn-cbor-octet-listp p)
           (let ((h (fn-ncline-reply-payload-decode (fn-frame-ok '(70 78 67 84) 1 23 p)))
                 (w (fn-wg-decode *fn-wf-ctl-lined-payload* p)))
             (and (iff (not (equal h :bad))
                       (and (fn-wg-okp w) (null (fn-wg-rest w)) (<= (len p) 1545)))
                  (implies (not (equal h :bad))
                           (equal (fn-wg-value w) h)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-fields-agree (specs *fn-ncline-reply-spec*))
                 (:instance fn-wf-ctl-fields-value-shape (specs *fn-ncline-reply-spec*) (b p)))
           :in-theory (e/d (fn-ncline-reply-payload-decode fn-frame-fields-parse
                            fn-frame-parse-error-is-failure)
                           (fn-wf-ctl-fields-agree fn-wg-decode fn-frame-fields-parse-aux
                            fn-frame-parse-okp fn-frame-parse-value fn-frame-parse-rest)))))
; KEYSTONE (agreement), kind 23.
(defthm fn-wf-ctl-lined-decode-agrees
  (implies (fn-cbor-octet-listp x)
           (let ((r (fn-ncline-reply-payload-decode (fn-nctrl-open x 23)))
                 (w (fn-wg-decode *fn-wf-ctl-lined-reply-grammar* x)))
             (and (iff (not (equal r :bad))
                       (and (fn-wg-okp w) (null (fn-wg-rest w))))
                  (implies (not (equal r :bad))
                           (equal (fn-wg-value w) r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-open-is-frame-decode (k 23))
                 (:instance fn-wf-fnct-whole-decode (g *fn-wf-ctl-lined-payload*) (k 23) (mx 1545)
                            (hm *fn-nctrl-max-payload*))
                 (:instance fn-frame-decode-payload-octets (octets x)
                            (digest (fn-frame-trailer (fn-frame-protected-prefix x)))
                            (max-payload *fn-nctrl-max-payload*))
                 (:instance fn-wf-ctl-lined-payload-agrees
                            (p (fn-frame-result-payload
                                (fn-frame-decode x (fn-frame-trailer (fn-frame-protected-prefix x))
                                                 *fn-nctrl-max-payload*))))
                 (:instance fn-wf-ctl-bad-of-error (r '(:error :control-frame))))
           :in-theory (union-theories '(fn-wf-ctl-lined-grammarp (:e fn-cbor-octetp) (:e natp) (:e <) (:e equal)
                                        (:e fn-frame-error) (:e fn-frame-result-okp))
                                      (theory 'minimal-theory)))))
; KEYSTONE (agreement), kind 23.
(defthm fn-wf-ctl-lined-encode-agrees
  (implies (and (fn-ncline-line line)
                (not (equal (fn-native-control-lined-reply-encode status reason line) :bad)))
           (let ((v (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
             (and (fn-wg-valuep *fn-wf-ctl-lined-reply-grammar* v)
                  (equal (fn-native-control-lined-reply-encode status reason line)
                         (fn-wg-encode *fn-wf-ctl-lined-reply-grammar* v)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wf-ctl-fields-encode (specs *fn-ncline-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
                 (:instance fn-frame-fields-octets-within-width (specs *fn-ncline-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
                 (:instance fn-frame-fields-octets-are-octets (specs *fn-ncline-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
                 (:instance fn-wf-fnct-host-seal-is-wg-encode (g *fn-wf-ctl-lined-payload*) (k 23) (mx 1545)
                            (v (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
                 (:instance fn-wf-fnct-nctrl-seal-is-host-framing (k 23)
                            (p (fn-frame-fields-octets *fn-ncline-reply-spec*
                                                       (list status (fn-nctrl-reason-word reason)
                                                             (fn-ncline-line line))))))
           :in-theory (e/d (fn-native-control-lined-reply-encode)
                           (fn-wf-ctl-fields-encode fn-wf-fnct-host-seal-is-wg-encode fn-nctrl-seal fn-wg-encode
                            fn-wg-valuep fn-frame-fields-octets-within-width fn-frame-fields-octets-are-octets
                            fn-wg-encode-opener-frame fn-wg-valuep-opener-frame fn-frame-protected fn-frame-trailer
                            fn-frame-fields-octets fn-frame-values-okp fn-nctrl-reason-word fn-ncline-line
                            fn-native-control-reasoned-reply-encode)))))
