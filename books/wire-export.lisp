; fn: the exported wire grammars, rendered by ACL2 (Mini M5;
; planning/design/wire-grammar-2026-10-04.md section 3).
;
; specs/wire-grammar.json is `fn-wgx-file' below: its octets are an ACL2
; value.  tools/protocol_emit.py --wire evaluates it through tools/acl2 and
; only writes (or, with --check, compares) the octets; nothing outside ACL2
; decides a byte of the file.
;
; The file is the language name and version, the frame trailer's digest, one
; entry per FAMILY (its grammar in the JSON form of the language, the ACL2
; names of its codec and of the theorems that make the grammar the codec, and
; its vectors), the exchanges (which reply families answer which request
; family), and the word tables (exit classes).  A vector is
; fn-wg-encode evaluated here on a value the family table names, with the
; family name and the language version; a frame family adds the first
; vector with its last trailer octet's low bit flipped and the same octets
; less their last one, each with the refusal fn-wg-decode answers for them.
;
; KEYSTONE fn-wgx-vectors-decode: every accepted vector decodes, whole, to
; its value, and every refusal vector is refused with the reason the file
; prints (a ground fact of the table, by evaluation).
;
; `fn-wgx-file-digest' is BLAKE3-256 (`fn-frame-digest') of the file's
; octets; the running image reports it in the store-identity reply
; (books/store-identity.lisp), so one command pins the grammar file too.
;
; This book owns the prefix `fn-wgx-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "wire-grammar")
(include-book "wire-family-fncu")
(include-book "wire-family-identity")
(include-book "outcome-class")

(defconst *fn-wgx-language* "fn-wire-grammar")
(defconst *fn-wgx-version* 1)

; -----------------------------------------------------------------------------
; Text as octets

(defun fn-wgx-chars (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (cons (if (characterp (car cs)) (char-code (car cs)) 63)
            (fn-wgx-chars (cdr cs)))
    nil))

(defun fn-wgx-str (s)
  (declare (xargs :guard t))
  (if (stringp s) (fn-wgx-chars (coerce s 'list)) nil))

(defun fn-wgx-nat (n)
  (declare (xargs :guard t))
  (fn-wgx-chars (explode-nonnegative-integer (nfix n) 10 nil)))

(defun fn-wgx-hex-digit (n)
  (declare (xargs :guard t))
  (let ((n (nfix n))) (if (< n 10) (+ 48 n) (+ 87 (min n 15)))))

(defun fn-wgx-hex (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (let ((o (nfix (car octets))))
        (list* (fn-wgx-hex-digit (floor (mod o 256) 16))
               (fn-wgx-hex-digit (mod o 16))
               (fn-wgx-hex (cdr octets))))
    nil))

(defun fn-wgx-quote (octets)
  ; A JSON string of octets that need no escape (names, hex, the fixed text).
  (declare (xargs :guard t))
  (append (list 34) (true-list-fix octets) (list 34)))

(defun fn-wgx-name (x)
  ; A keyword's lower-case print name, quoted: :accepted -> "accepted".
  (declare (xargs :guard t))
  (fn-wgx-quote (fn-wgx-str (if (symbolp x) (string-downcase (symbol-name x)) ""))))

(defun fn-wgx-hexq (octets)
  (declare (xargs :guard t))
  (fn-wgx-quote (fn-wgx-hex octets)))

(defun fn-wgx-join (items)
  ; ITEMS (each a list of octets) joined by commas.
  (declare (xargs :guard t))
  (if (consp items)
      (if (consp (cdr items))
          (append (true-list-fix (car items)) (list 44) (fn-wgx-join (cdr items)))
        (true-list-fix (car items)))
    nil))

(defun fn-wgx-array (items)
  (declare (xargs :guard t))
  (append (list 91) (fn-wgx-join items) (list 93)))

(defun fn-wgx-field (key value)
  ; "KEY":VALUE, KEY a string.
  (declare (xargs :guard t))
  (append (fn-wgx-quote (fn-wgx-str key)) (list 58) (true-list-fix value)))

(defun fn-wgx-object (fields)
  (declare (xargs :guard t))
  (append (list 123) (fn-wgx-join fields) (list 125)))

(defun fn-wgx-names (xs)
  (declare (xargs :guard t))
  (if (consp xs) (cons (fn-wgx-name (car xs)) (fn-wgx-names (cdr xs))) nil))

; -----------------------------------------------------------------------------
; A grammar in the language's JSON form

(defun fn-wgx-nat-list (xs)
  (declare (xargs :guard t))
  (if (consp xs) (cons (fn-wgx-nat (car xs)) (fn-wgx-nat-list (cdr xs))) nil))

(defun fn-wgx-check-json (check)
  (declare (xargs :guard t))
  (let ((c (true-list-fix check)))
    (fn-wgx-array (cons (fn-wgx-name (car c)) (fn-wgx-nat-list (cdr c))))))

(defun fn-wgx-checks-json (checks)
  (declare (xargs :guard t))
  (if (consp checks)
      (cons (fn-wgx-check-json (car checks)) (fn-wgx-checks-json (cdr checks)))
    nil))

(mutual-recursion
 (defun fn-wgx-grammar-json (g)
   (declare (xargs :guard t :measure (+ 1 (* 2 (acl2-count g))) :verify-guards nil))
   (let ((op (fn-wg-op g)))
     (cond
      ((equal op :const) (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-hexq (fn-wg-arg 1 g)))))
      ((member-equal op '(:uint :base64-lines))
       (fn-wgx-array (list* (fn-wgx-name op)
                            (fn-wgx-nat-list (list (fn-wg-arg 1 g) (fn-wg-arg 2 g)
                                                   (fn-wg-arg 3 g))))))
      ((equal op :bytes)
       (fn-wgx-array (append (list (fn-wgx-name op))
                             (fn-wgx-nat-list (list (fn-wg-arg 1 g) (fn-wg-arg 2 g)
                                                    (fn-wg-arg 3 g)))
                             (list (fn-wgx-name (fn-wg-arg 4 g))))))
      ((member-equal op '(:rest :line))
       (fn-wgx-array (append (list (fn-wgx-name op))
                             (fn-wgx-nat-list (list (fn-wg-arg 1 g) (fn-wg-arg 2 g)))
                             (list (fn-wgx-name (fn-wg-arg 3 g))))))
      ((equal op :enum)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-nat (fn-wg-arg 1 g))
                           (fn-wgx-nat (fn-wg-arg 2 g))
                           (fn-wgx-array (fn-wgx-names (fn-wg-arg 3 g))))))
      ((equal op :seq)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-array (fn-wgx-seq-json g)))))
      ((equal op :tag)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-nat (fn-wg-arg 1 g))
                           (fn-wgx-array (fn-wgx-arms-json g)))))
      ((equal op :maybe)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-grammar-json (fn-wg-arg 1 g)))))
      ((equal op :where)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-grammar-json (fn-wg-arg 1 g))
                           (fn-wgx-array (fn-wgx-checks-json (fn-wg-where-checks g))))))
      ((equal op :frame)
       (fn-wgx-array (list (fn-wgx-name op) (fn-wgx-hexq (fn-wg-arg 1 g))
                           (fn-wgx-nat (fn-wg-arg 2 g)) (fn-wgx-nat (fn-wg-arg 3 g))
                           (fn-wgx-nat (fn-wg-arg 4 g))
                           (fn-wgx-grammar-json (fn-wg-arg 5 g)))))
      (t (fn-wgx-str "null")))))
 (defun fn-wgx-seq-json (g)
   ; The elements of a :seq node, each in JSON form.
   (declare (xargs :guard t :measure (* 2 (acl2-count g))))
   (if (and (consp g) (consp (cdr g)))
       (cons (fn-wgx-grammar-json (fn-wg-arg 1 g)) (fn-wgx-seq-json (fn-wg-next g)))
     nil))
 (defun fn-wgx-arms-json (g)
   ; The arms of a :tag node: [CODE,"name",G].
   (declare (xargs :guard t :measure (* 2 (acl2-count g))))
   (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
       (cons (fn-wgx-array (list (fn-wgx-nat (fn-wg-arg 0 (fn-wg-arg 2 g)))
                                 (fn-wgx-name (fn-wg-arg 1 (fn-wg-arg 2 g)))
                                 (fn-wgx-grammar-json (fn-wg-arg 2 (fn-wg-arg 2 g)))))
             (fn-wgx-arms-json (fn-wg-tag-next g)))
     nil)))

; -----------------------------------------------------------------------------
; A value in the language's JSON form, read through its grammar

(mutual-recursion
 (defun fn-wgx-value-json (g v)
   (declare (xargs :guard t :measure (+ 1 (* 2 (acl2-count g))) :verify-guards nil))
   (let ((op (fn-wg-op g)))
     (cond
      ((equal op :const) (fn-wgx-str "null"))
      ((equal op :uint) (fn-wgx-nat v))
      ((member-equal op '(:bytes :rest :line :base64-lines)) (fn-wgx-hexq v))
      ((equal op :enum) (fn-wgx-name v))
      ((equal op :seq) (fn-wgx-array (fn-wgx-seq-value-json g v)))
      ((equal op :tag) (fn-wgx-arm-value-json g v))
      ((equal op :maybe)
       (fn-wgx-array (if (consp v) (list (fn-wgx-value-json (fn-wg-arg 1 g) (car v))) nil)))
      ((equal op :where) (fn-wgx-value-json (fn-wg-arg 1 g) v))
      ((equal op :frame) (fn-wgx-value-json (fn-wg-arg 5 g) v))
      (t (fn-wgx-str "null")))))
 (defun fn-wgx-seq-value-json (g v)
   (declare (xargs :guard t :measure (* 2 (acl2-count g))))
   (if (and (consp g) (consp (cdr g)))
       (cons (fn-wgx-value-json (fn-wg-arg 1 g) (if (consp v) (car v) nil))
             (fn-wgx-seq-value-json (fn-wg-next g) (if (consp v) (cdr v) nil)))
     nil))
 (defun fn-wgx-arm-value-json (g v)
   ; ["name",VALUE] for the arm whose name is V's first element.
   (declare (xargs :guard t :measure (* 2 (acl2-count g))))
   (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
       (if (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
           (fn-wgx-array (list (fn-wgx-name (fn-wg-arg 1 (fn-wg-arg 2 g)))
                               (fn-wgx-value-json (fn-wg-arg 2 (fn-wg-arg 2 g))
                                                  (if (and (consp v) (consp (cdr v)))
                                                      (cadr v) nil))))
         (fn-wgx-arm-value-json (fn-wg-tag-next g) v))
     (fn-wgx-str "null"))))

; -----------------------------------------------------------------------------
; The families
;
; An entry is (NAME GRAMMAR ENCODE DECODE AGREEMENT VALUES): NAME the family's
; name (a string), GRAMMAR its tree, ENCODE and DECODE the ACL2 functions the
; host calls for it, AGREEMENT the theorems that make GRAMMAR that codec (nil
; for a family whose codec IS the interpreter at GRAMMAR), VALUES the values
; its vectors encode.

(defconst *fn-wgx-fncu-values*
  (list (list nil '(1) (make-list 64 :initial-element 255) '(2 3) '(4) '(5 6 7)
              0 9 1 4294967295)
        (list nil '(17 34) '(51) '(68) '(85) '(102) 1 1 4294967295 0)))

(defconst *fn-wgx-identity-values*
  (list (list :accepted
              (list (fn-wgx-str "fn-store-10")
                    (make-list 32 :initial-element 1) (make-list 32 :initial-element 2)
                    (make-list 32 :initial-element 3) (make-list 32 :initial-element 4)
                    (make-list 32 :initial-element 5)
                    (fn-wgx-str "0123456789abcdef0123456789abcdef01234567")
                    (fn-wgx-str "unknown")
                    (make-list 32 :initial-element 6)))
        (list :accepted
              (list (fn-wgx-str "fn-store-10")
                    (make-list 32 :initial-element 1) (make-list 32 :initial-element 2)
                    (make-list 32 :initial-element 3) nil nil
                    (fn-wgx-str "unknown") (fn-wgx-str "unknown")
                    (make-list 32 :initial-element 6)))
        (list :refused :no-genesis)))

(defconst *fn-wgx-families*
  (list
   (list "fncu.cursor" *fn-wf-fncu-grammar*
         'fn-cp-cursor-encode 'fn-cp-cursor-decode
         '(fn-wf-fncu-encode-agrees fn-wf-fncu-decode-agrees
           fn-cp-cursor-decode-encode-roundtrip fn-cp-cursor-encode-decode-roundtrip)
         *fn-wgx-fncu-values*)
   (list "fnct.store-identity.request" *fn-wf-identity-request-grammar*
         'fn-wg-encode 'fn-wg-decode nil (list nil))
   (list "fnct.store-identity.reply" *fn-wf-identity-reply-grammar*
         'fn-wg-encode 'fn-wg-decode nil *fn-wgx-identity-values*)))

(defconst *fn-wgx-exchanges*
  '(("fnct.store-identity.request" "fnct.store-identity.reply")))

(defun fn-wgx-entry-name (e) (declare (xargs :guard t)) (fn-wg-arg 0 e))
(defun fn-wgx-entry-grammar (e) (declare (xargs :guard t)) (fn-wg-arg 1 e))
(defun fn-wgx-entry-values (e) (declare (xargs :guard t)) (fn-wg-arg 5 e))

; -----------------------------------------------------------------------------
; Vectors

(defun fn-wgx-flip-last (xs)
  ; XS with its last octet's low bit flipped.
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs))
          (cons (car xs) (fn-wgx-flip-last (cdr xs)))
        (list (logxor 1 (nfix (car xs)))))
    nil))

(defun fn-wgx-drop-last (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs))) (cons (car xs) (fn-wgx-drop-last (cdr xs))) nil))

(defun fn-wgx-family-head (name)
  (declare (xargs :guard t))
  (list (fn-wgx-field "family" (fn-wgx-quote (fn-wgx-str name)))
        (fn-wgx-field "version" (fn-wgx-nat *fn-wgx-version*))))

(defun fn-wgx-accept-vectors (name g values)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp values)
      (cons (fn-wgx-object
             (append (fn-wgx-family-head name)
                     (list (fn-wgx-field "value" (fn-wgx-value-json g (car values)))
                           (fn-wgx-field "octets"
                                         (fn-wgx-hexq (fn-wg-encode g (car values)))))))
            (fn-wgx-accept-vectors name g (cdr values)))
    nil))

(defun fn-wgx-refusal-vector (name g octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wgx-object
   (append (fn-wgx-family-head name)
           (list (fn-wgx-field "octets" (fn-wgx-hexq octets))
                 (fn-wgx-field "refused"
                               (fn-wgx-name (fn-wg-arg 1 (fn-wg-decode g octets))))))))

(defun fn-wgx-refusal-octets (g values)
  ; For a frame family: the first vector, its trailer flipped; then truncated.
  (declare (xargs :guard t :verify-guards nil))
  (if (and (equal (fn-wg-op g) :frame) (consp values))
      (let ((e (fn-wg-encode g (car values))))
        (list (fn-wgx-flip-last e) (fn-wgx-drop-last e)))
    nil))

(defun fn-wgx-refusal-vectors (name g list)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp list)
      (cons (fn-wgx-refusal-vector name g (car list))
            (fn-wgx-refusal-vectors name g (cdr list)))
    nil))

; -----------------------------------------------------------------------------
; The file

(defun fn-wgx-family-json (e)
  (declare (xargs :guard t :verify-guards nil))
  (let ((name (fn-wgx-entry-name e)) (g (fn-wgx-entry-grammar e))
        (values (fn-wgx-entry-values e)))
    (fn-wgx-object
     (list (fn-wgx-field "name" (fn-wgx-quote (fn-wgx-str name)))
           (fn-wgx-field "grammar" (fn-wgx-grammar-json g))
           (fn-wgx-field "acl2"
                         (fn-wgx-object
                          (list (fn-wgx-field "encode" (fn-wgx-name (fn-wg-arg 2 e)))
                                (fn-wgx-field "decode" (fn-wgx-name (fn-wg-arg 3 e)))
                                (fn-wgx-field "agreement"
                                              (fn-wgx-array (fn-wgx-names (fn-wg-arg 4 e))))
                                (fn-wgx-field "round-trips"
                                              (fn-wgx-array
                                               (fn-wgx-names '(fn-wg-decode-of-encode
                                                               fn-wg-encode-of-decode)))))))
           (fn-wgx-field "vectors"
                         (fn-wgx-array
                          (append (fn-wgx-accept-vectors name g values)
                                  (fn-wgx-refusal-vectors
                                   name g (fn-wgx-refusal-octets g values)))))))))

(defun fn-wgx-families-json (es)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp es) (cons (fn-wgx-family-json (car es)) (fn-wgx-families-json (cdr es))) nil))

(defun fn-wgx-strings (xs)
  (declare (xargs :guard t))
  (if (consp xs) (cons (fn-wgx-quote (fn-wgx-str (car xs))) (fn-wgx-strings (cdr xs))) nil))

(defun fn-wgx-exchanges-json (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-wgx-object
             (list (fn-wgx-field "request" (fn-wgx-quote (fn-wgx-str (fn-wg-arg 0 (car xs)))))
                   (fn-wgx-field "replies"
                                 (fn-wgx-array (fn-wgx-strings
                                                (if (consp (car xs)) (cdr (car xs)) nil))))))
            (fn-wgx-exchanges-json (cdr xs)))
    nil))

(defun fn-wgx-codes-json (pairs)
  ; {"accepted":0,...} from ((:accepted . 0) ...).
  (declare (xargs :guard t))
  (if (consp pairs)
      (cons (append (fn-wgx-name (if (consp (car pairs)) (car (car pairs)) nil)) (list 58)
                    (fn-wgx-nat (if (consp (car pairs)) (cdr (car pairs)) 0)))
            (fn-wgx-codes-json (cdr pairs)))
    nil))

(defun fn-wgx-lines (items)
  ; ITEMS joined by a comma and a newline: one family per line.
  (declare (xargs :guard t))
  (if (consp items)
      (if (consp (cdr items))
          (append (true-list-fix (car items)) (list 44 10) (fn-wgx-lines (cdr items)))
        (true-list-fix (car items)))
    nil))

(defun fn-wgx-file ()
  (declare (xargs :guard t :verify-guards nil))
  (append
   (fn-wgx-str "{")
   (fn-wgx-field "format" (fn-wgx-quote (fn-wgx-str *fn-wgx-language*))) (list 44)
   (fn-wgx-field "version" (fn-wgx-nat *fn-wgx-version*)) (list 44)
   (fn-wgx-field "trailer" (fn-wgx-quote (fn-wgx-str "blake3-256"))) (list 44 10)
   (fn-wgx-quote (fn-wgx-str "families")) (list 58 91) (list 10)
   (fn-wgx-lines (fn-wgx-families-json *fn-wgx-families*)) (list 10)
   (fn-wgx-str "],") (list 10)
   (fn-wgx-field "exchanges" (fn-wgx-array (fn-wgx-exchanges-json *fn-wgx-exchanges*)))
   (list 44 10)
   (fn-wgx-field "words"
                 (fn-wgx-object
                  (list (fn-wgx-field "exit-classes"
                                      (fn-wgx-object (fn-wgx-codes-json *fn-outcome-codes*))))))
   (fn-wgx-str "}") (list 10)))

; -----------------------------------------------------------------------------
; The vectors are what the file says

(defun fn-wgx-accepts-okp (g values)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp values)
      (and (fn-wg-valuep g (car values))
           (equal (fn-wg-decode g (fn-wg-encode g (car values)))
                  (fn-wg-ok (car values) nil))
           (fn-wgx-accepts-okp g (cdr values)))
    t))

(defun fn-wgx-refusals-okp (g list)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp list)
      (and (not (fn-wg-okp (fn-wg-decode g (car list))))
           (fn-wgx-refusals-okp g (cdr list)))
    t))

(defun fn-wgx-families-okp (es)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp es)
      (let ((g (fn-wgx-entry-grammar (car es))) (values (fn-wgx-entry-values (car es))))
        (and (fn-wg-grammarp g)
             (fn-wgx-accepts-okp g values)
             (fn-wgx-refusals-okp g (fn-wgx-refusal-octets g values))
             (fn-wgx-families-okp (cdr es))))
    t))

; KEYSTONE (by evaluation): every family's grammar is well formed, every
; accepted vector decodes whole to its value, and every refusal vector is
; refused.
(defthm fn-wgx-vectors-decode
  (fn-wgx-families-okp *fn-wgx-families*)
  :rule-classes nil)

; The file's octets, once, and their digest: what the running image reports.
(defconst *fn-wgx-file-octets* (fn-wgx-file))
(defconst *fn-wgx-file-digest* (fn-frame-digest *fn-wgx-file-octets*))

(defthm fn-wgx-file-digest-shape
  (and (fn-cbor-octet-listp *fn-wgx-file-digest*)
       (equal (len *fn-wgx-file-digest*) 32))
  :rule-classes nil)

; The file's text for the emitter (tools/protocol_emit.py --wire): the hex of
; its octets, so the host's printer decides nothing about them.
(defun fn-wgx-code-chars (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (code-char (let ((x (nfix (car xs)))) (if (< x 256) x 63)))
            (fn-wgx-code-chars (cdr xs)))
    nil))

(defun fn-wgx-file-hex ()
  (declare (xargs :guard t))
  (coerce (fn-wgx-code-chars (fn-wgx-hex *fn-wgx-file-octets*)) 'string))
