; fn: the codec of article kind `opaque' v1 -- the wire-grammar interpreter at
; *fn-ak-grammar*, and nothing else (D50; planning/design/
; zmq-surface-2026-10-04.md section 2).
;
; There is no second encoder or decoder of the kind.  fn-ak-encode is
; fn-wg-encode at the kind's grammar of the grammar value of the row values
; and the payload; fn-ak-decode is fn-wg-decode at that grammar, then the
; kind's refinement of the grammar (fn-ak-rows-check: From a mailbox-list,
; Newsgroups a newsgroup-list, Message-ID a msg-id), each refusal by name.
; A source whose FN-Kind row names another version of `opaque' is refused
; :kind-version, another kind :kind (design section 2, "Version word").
;
; Keystones:
;   fn-ak-decode-of-encode     every value of the kind round-trips;
;   fn-ak-encode-of-decode     an accepted source IS the encoding of what it
;                              decoded to (canonicity: one value, one source);
;   fn-ak-grammar-encode-is-the-layout
;                              the interpreter's octets are fn-ak-layout's,
;                              so the acceptance keystones PRF-1320..1322
;                              (stated of fn-ak-layout) are the codec's.

(in-package "ACL2")
(include-book "article-kind")
(include-book "wire-grammar")
(local (include-book "arithmetic-5/top" :dir :system))

; The grammar is one the interpreter's theorems are about.
(defthm fn-ak-grammar-is-a-grammar
  (fn-wg-grammarp *fn-ak-grammar*))

; -----------------------------------------------------------------------------
; The grammar value: per row, nil for its constant line (a :version or :fixed
; row) or nil for its "NAME: " and then its value (any other row); nil for
; the blank line; the payload.

(defun fn-ak-grammar-row-values (rows vals)
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((v (if (consp vals) (car vals) nil))
            (more (fn-ak-grammar-row-values (cdr rows) (if (consp vals) (cdr vals) nil))))
        (if (member-eq (fn-ak-row-kind (car rows)) '(:version :fixed))
            (cons nil more)
          (list* nil v more)))
    nil))

(defun fn-ak-grammar-value (vals payload)
  (declare (xargs :guard t))
  (append (fn-ak-grammar-row-values *fn-ak-v1-rows* vals) (list nil payload)))

; Its inverse: (mv VALS REST), the fixed rows' values from the table.
(defun fn-ak-row-values-of (rows gv)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (member-eq (fn-ak-row-kind (car rows)) '(:version :fixed))
          (mv-let (vals rest)
            (fn-ak-row-values-of (cdr rows) (if (consp gv) (cdr gv) nil))
            (mv (cons (fn-ak-row-arg (car rows)) vals) rest))
        (let ((tail (if (consp gv) (cdr gv) nil)))
          (mv-let (vals rest)
            (fn-ak-row-values-of (cdr rows) (if (consp tail) (cdr tail) nil))
            (mv (cons (if (consp tail) (car tail) nil) vals) rest))))
    (mv nil gv)))

(defun fn-ak-payload-of (gv)
  (declare (xargs :guard t))
  (mv-let (vals rest) (fn-ak-row-values-of *fn-ak-v1-rows* gv)
    (declare (ignore vals))
    (if (and (consp rest) (consp (cdr rest))) (cadr rest) nil)))

(defun fn-ak-vals-of (gv)
  (declare (xargs :guard t))
  (mv-let (vals rest) (fn-ak-row-values-of *fn-ak-v1-rows* gv)
    (declare (ignore rest))
    vals))

; -----------------------------------------------------------------------------
; The codec

(defun fn-ak-payloadp (payload)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp payload)
       (<= (len payload) *fn-article-max-octets*)))

; The source of the kind at VALS and PAYLOAD; nil outside the kind.
(defun fn-ak-encode (vals payload)
  (declare (xargs :guard t))
  (if (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals) (fn-ak-payloadp payload))
      (fn-wg-encode *fn-ak-grammar* (fn-ak-grammar-value vals payload))
    nil))

; The FN-Kind row's value among the first header lines of SOURCE, or nil.
(defconst *fn-ak-kind-prefix* '(70 78 45 75 105 110 100 58 32))   ; "FN-Kind: "

(defun fn-ak-line (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 13)))
      (cons (car xs) (fn-ak-line (cdr xs)))
    nil))

(defun fn-ak-after-line (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 13)))
      (fn-ak-after-line (cdr xs))
    (if (and (consp xs) (consp (cdr xs))) (cddr xs) nil)))

(defthm fn-ak-after-line-shorter
  (<= (len (fn-ak-after-line xs)) (len xs))
  :rule-classes :linear)

(defun fn-ak-prefixp (p xs)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp xs) (equal (car p) (car xs)) (fn-ak-prefixp (cdr p) (cdr xs)))
    t))

(defun fn-ak-kind-row-value (xs fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (let ((line (fn-ak-line xs)))
    (cond ((or (zp fuel) (atom line)) nil)
          ((fn-ak-prefixp *fn-ak-kind-prefix* line)
           (fn-ak-drop (len *fn-ak-kind-prefix*) line))
          (t (fn-ak-kind-row-value (fn-ak-after-line xs) (1- fuel))))))

; The refusal of a source the grammar refuses: :kind-version when its FN-Kind
; row names another version of `opaque', :kind when it names anything else,
; :malformed otherwise.
(defun fn-ak-refusal (source)
  (declare (xargs :guard t))
  (let* ((row (nth 5 *fn-ak-v1-rows*))
         (v (fn-ak-kind-row-value source 16))
         (stem (fn-ak-row-stem row)))
    (cond ((or (null v) (equal v (fn-ak-row-arg row))) :malformed)
          ((fn-ak-prefixp stem v) :kind-version)
          (t :kind))))

; (:ok VALS PAYLOAD) or (:refused REASON).
(defun fn-ak-decode (source)
  (declare (xargs :guard t))
  (let ((r (fn-wg-decode *fn-ak-grammar* source)))
    (if (and (fn-cbor-octet-listp source) (fn-wg-okp r) (null (fn-wg-rest r)))
        (let* ((gv (fn-wg-value r))
               (vals (fn-ak-vals-of gv))
               (bad (fn-ak-rows-check *fn-ak-v1-rows* vals)))
          (if bad
              (list :refused bad)
            (list :ok vals (fn-ak-payload-of gv))))
      (list :refused (fn-ak-refusal source)))))

; -----------------------------------------------------------------------------
; Keystones

; The grammar value of a value of the kind is a value of the grammar, and
; reads back.

(local
 (defthm fn-ak-sp-vchar-listp-is-header
   (implies (fn-ak-sp-vchar-listp xs) (fn-wg-header-octetsp xs))))

(local
 (defthm fn-ak-row-valuep-is-a-line
   (implies (fn-ak-row-valuep row v)
            (and (consp v)
                 (fn-cbor-octet-listp v)
                 (fn-wg-header-octetsp v)
                 (<= (len v) (fn-ak-row-fuel row))))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ak-wg-valuep-seq
   (implies (and (consp g) (equal (car g) :seq))
            (equal (fn-wg-valuep g v)
                   (if (consp (cdr g))
                       (and (consp v)
                            (fn-wg-valuep (cadr g) (car v))
                            (fn-wg-valuep (cons :seq (cddr g)) (cdr v)))
                     (null v))))
   :hints (("Goal" :expand ((fn-wg-valuep g v))
                   :in-theory (enable fn-wg-op fn-wg-arg fn-wg-next)))))

(local
 (defthm fn-ak-wg-valuep-leaf
   (implies (and (consp g) (member-equal (car g) '(:const :line :base64-lines)))
            (equal (fn-wg-valuep g v)
                   (case (car g)
                     (:const (null v))
                     (:line (and (fn-cbor-octet-listp v)
                                 (fn-wg-class-okp (fn-wg-arg 3 g) v)
                                 (<= (nfix (fn-wg-arg 1 g)) (len v))
                                 (<= (len v) (nfix (fn-wg-arg 2 g)))))
                     (otherwise (and (fn-cbor-octet-listp v)
                                     (<= (nfix (fn-wg-arg 2 g)) (len v))
                                     (<= (len v) (nfix (fn-wg-arg 3 g))))))))
   :hints (("Goal" :expand ((fn-wg-valuep g v))
                   :in-theory (enable fn-wg-op)))))

(local
 (defthm fn-ak-row-valuep-is-a-line-len
   (implies (fn-ak-row-valuep row v)
            (< 0 (len v)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ak-grammar-value-is-a-value
   (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                 (fn-ak-payloadp payload))
            (fn-wg-valuep *fn-ak-grammar* (fn-ak-grammar-value vals payload)))
   :hints (("Goal" :in-theory (disable fn-ak-row-valuep)))))

(local
 (defthm fn-ak-row-values-of-grammar-row-values
   (implies (fn-ak-rows-valuesp rows vals)
            (equal (fn-ak-row-values-of rows (append (fn-ak-grammar-row-values rows vals) tail))
                   (mv vals tail)))
   :hints (("Goal" :in-theory (enable fn-ak-rows-valuesp)))))

(local
 (defthm fn-ak-vals-of-grammar-value
   (implies (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
            (and (equal (fn-ak-vals-of (fn-ak-grammar-value vals payload)) vals)
                 (equal (fn-ak-payload-of (fn-ak-grammar-value vals payload)) payload)))
   :hints (("Goal" :in-theory (disable fn-ak-row-values-of fn-ak-grammar-row-values
                                       fn-ak-rows-valuesp (:e fn-ak-rows-valuesp))))))

(local
 (defthm fn-ak-wg-app-nil
   (implies (true-listp x) (equal (fn-wg-app x nil) x))
   :hints (("Goal" :in-theory (enable fn-wg-app-is-append)))))

(local
 (defthm fn-ak-rows-valuesp-consp
   (implies (and (fn-ak-rows-valuesp rows vals) (consp rows)) (consp vals))
   :rule-classes :forward-chaining))

; KEYSTONE: every value of the kind round-trips through the codec.
(defthm fn-ak-decode-of-encode
  (implies (and (fn-ak-rows-valuesp *fn-ak-v1-rows* vals)
                (fn-ak-payloadp payload))
           (equal (fn-ak-decode (fn-ak-encode vals payload))
                  (list :ok vals payload)))
  :hints (("Goal" :in-theory (disable fn-wg-decode-of-encode fn-wg-encode fn-wg-decode
                                      fn-ak-grammar-value fn-ak-vals-of fn-ak-payload-of
                                      fn-ak-rows-valuesp (:e fn-ak-rows-valuesp) fn-ak-payloadp
                                      fn-ak-rows-check (:e fn-ak-rows-check))
                  :use ((:instance fn-wg-decode-of-encode
                                   (g *fn-ak-grammar*)
                                   (v (fn-ak-grammar-value vals payload))
                                   (r nil))
                        (:instance fn-wg-encode-octets
                                   (g *fn-ak-grammar*)
                                   (v (fn-ak-grammar-value vals payload)))))))

; Canonicity, through the value: a grammar value of the kind reads back.
(local
 (defthm fn-ak-grammar-value-of-a-value
   (implies (fn-wg-valuep *fn-ak-grammar* gv)
            (and (equal (fn-ak-grammar-value (fn-ak-vals-of gv) (fn-ak-payload-of gv)) gv)
                 (fn-ak-payloadp (fn-ak-payload-of gv))))))

(local
 (defthm fn-ak-encode-of-a-value
   (implies (and (fn-wg-valuep *fn-ak-grammar* gv)
                 (not (fn-ak-rows-check *fn-ak-v1-rows* (fn-ak-vals-of gv))))
            (equal (fn-ak-encode (fn-ak-vals-of gv) (fn-ak-payload-of gv))
                   (fn-wg-encode *fn-ak-grammar* gv)))
   :hints (("Goal" :in-theory (disable fn-ak-grammar-value fn-ak-vals-of fn-ak-payload-of
                                       fn-ak-payloadp fn-wg-encode
                                       fn-ak-wg-valuep-seq fn-ak-wg-valuep-leaf
                                       fn-ak-rows-valuesp (:e fn-ak-rows-valuesp)
                                       fn-ak-rows-check (:e fn-ak-rows-check))))))

; KEYSTONE: canonicity -- an accepted source is the encoding of its value.
(defthm fn-ak-encode-of-decode
  (implies (equal (car (fn-ak-decode source)) :ok)
           (equal (fn-ak-encode (cadr (fn-ak-decode source))
                                (caddr (fn-ak-decode source)))
                  source))
  :hints (("Goal" :in-theory (disable fn-wg-encode-of-decode fn-wg-encode fn-wg-decode
                                      fn-ak-encode fn-ak-vals-of fn-ak-payload-of
                                      fn-ak-wg-valuep-seq fn-ak-wg-valuep-leaf
                                      fn-ak-rows-check (:e fn-ak-rows-check) fn-ak-refusal)
                  :use ((:instance fn-wg-encode-of-decode
                                   (g *fn-ak-grammar*) (xs source))
                        (:instance fn-wg-encode-octets
                                   (g *fn-ak-grammar*)
                                   (v (fn-wg-value (fn-wg-decode *fn-ak-grammar* source))))))))

; The interpreter's base64 lines are the layout's frame.

(local
 (defthm fn-ak-take-whole
   (implies (and (true-listp x) (<= (len x) (nfix n)))
            (equal (fn-ak-take n x) x))))

(local
 (defthm fn-ak-drop-whole
   (implies (<= (len x) (nfix n))
            (not (consp (fn-ak-drop n x))))))

(local
 (defthm fn-ak-wg-take-is-take
   (implies (<= (nfix n) (len x))
            (equal (fn-wg-take n x) (fn-ak-take n x)))))

(local
 (defthm fn-ak-wg-drop-is-drop
   (implies (true-listp x)
            (equal (fn-wg-drop n x) (fn-ak-drop n x)))))

(local
 (defthm fn-ak-true-listp-of-drop
   (implies (true-listp x) (true-listp (fn-ak-drop n x)))))

(local
 (defthm fn-ak-wg-lines-is-the-frame
   (implies (true-listp text)
            (equal (fn-wg-lines 76 text) (fn-ak-frame text)))
   :hints (("Goal" :induct (fn-ak-frame text)
                   :in-theory (enable fn-wg-app-is-append)))))
(local
 (defthm fn-ak-row-valuep-true-listp
   (implies (fn-ak-row-valuep row v) (true-listp v))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ak-row-valuep-fixed
   (implies (and (fn-ak-row-valuep row v)
                 (member-equal (fn-ak-row-kind row) '(:version :fixed)))
            (equal v (fn-ak-row-arg row)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-ak-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; KEYSTONE (the bridge): the interpreter's octets are the layout's, so the
; acceptance keystones PRF-1320..1322 (stated of fn-ak-layout) are the codec's.
(defthm fn-ak-grammar-encode-is-the-layout
  (implies (fn-ak-payloadp payload)
           (equal (fn-ak-encode vals payload)
                  (fn-ak-layout vals payload)))
  :hints (("Goal" :in-theory (e/d (fn-wg-app-is-append fn-wg-encode-opener-seq fn-wg-encode-opener-const
                                   fn-wg-encode-opener-line fn-wg-encode-opener-base64-lines)
                                  (fn-ak-row-valuep fn-ot-b64-encode)))))
