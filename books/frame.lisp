; fn: the one durable frame grammar, owned by ACL2.
;
; Four Python-only grammars previously decided how a durable byte string was
; framed: FNST (the store transaction file), FNWF (the sender workflow
; journal), FNRJ (the receiver journal) and FNBI (a staged inbound bundle).
; This book replaces all four with a single layout and one pair of functions.
;
;   FRAME := MAGIC(4) VERSION(1) KIND(1) LENGTH(4, big-endian) PAYLOAD(LENGTH)
;            TRAILER(32)
;
; Representation choice: a direct octet layout, not `fn-cbor-*` items.  Two
; reasons, both structural.  First, the frame's job is to bound the payload
; before anything allocates; building it on the CBOR decoder would make that
; bound depend on the very parser the frame exists to protect, and the store
; payload is itself a CBOR record, so the frame would parse its own contents.
; Second, a fixed-width big-endian field has exactly one encoding of each
; accepted value, so canonicality here is structural rather than a rejected
; alternative form: `fn-frame-encode-of-decode` is proved, not assumed.  The
; CBOR primitives are still reused for the octet recognizers, for the
; big-endian conversions, and for the cons-bounded preflight.
;
; FNWF and FNRJ frames under this grammar are byte-identical to the Python
; frames they replace.  FNST gains the kind octet it lacked (the store config
; format moves to `fn-store-experiment-3`) and FNBI moves its BID length into
; a payload text field.
;
; The 32-octet trailer is SHA-256 in deployment.  ACL2 does not compute it:
; `fn-frame-digest` is a constrained function whose only constraints are its
; output shape, recorded as A-CRYPTO.  The host supplies candidate digest
; octets and ACL2 owns every other frame decision, including the comparison.
; `fn-frame-seal` and `fn-frame-open` state the specification against the
; constrained function; `fn-frame-encode` and `fn-frame-decode` are what the
; host calls, and the theorems relating them name `fn-frame-digest` and its
; hypothesis explicitly.

(in-package "ACL2")
(include-book "cbor-invariants")
(include-book "wildmat")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Layout constants

(defconst *fn-frame-magic-octets* 4)
(defconst *fn-frame-trailer-octets* 32)
; MAGIC(4) VERSION(1) KIND(1) LENGTH(4)
(defconst *fn-frame-header-octets* 10)
(defconst *fn-frame-overhead-octets* 42)

; A payload ceiling above every schema's own cap.  Callers pass their smaller
; cap; this constant only keeps the cons preflight a fixed amount of work.
(defconst *fn-frame-max-payload* 4194304)

; Field-level caps, matching the durable journals they describe.
(defconst *fn-frame-max-text* 512)
(defconst *fn-frame-max-blob* 131072)
(defconst *fn-frame-max-nat* 18446744073709551615)

(defconst *fn-frame-u32-modulus* 4294967296)

; -----------------------------------------------------------------------------
; A-CRYPTO: the integrity trailer function

; The only thing ACL2 knows about the trailer function is that it yields 32
; octets.  Collision resistance, preimage resistance and the concrete SHA-256
; algorithm are outside the logic; no theorem below claims any of them.  The
; local witness proves the constraints are satisfiable.
(encapsulate
  (((fn-frame-digest *) => *))
  (local (defun fn-frame-digest (octets)
           (declare (ignore octets))
           '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
  (defthm fn-frame-digest-octet-listp
    (fn-cbor-octet-listp (fn-frame-digest octets)))
  (defthm fn-frame-digest-length
    (equal (len (fn-frame-digest octets)) *fn-frame-trailer-octets*)))

(defun fn-frame-digestp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-frame-trailer-octets*)))

(defun fn-frame-magicp (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (equal (len xs) *fn-frame-magic-octets*)))

; -----------------------------------------------------------------------------
; Bounded splitting
;
; One helper takes the first `n` octets off a list or reports that fewer than
; `n` are present.  It allocates at most `n` conses and examines at most `n`,
; so every caller below can put its bound check in front of its split.

(defun fn-frame-split (n xs)
  (declare (xargs :guard (and (natp n) (true-listp xs))))
  (if (zp n)
      (cons nil xs)
    (if (consp xs)
        (let ((rest (fn-frame-split (1- n) (cdr xs))))
          (and rest (cons (cons (car xs) (car rest)) (cdr rest))))
      nil)))

; A total positional accessor.  Every result record below is read through it,
; so no guard obligation anywhere depends on the shape of a value that failed
; to parse.
(defun fn-frame-item (n xs)
  (declare (xargs :guard (natp n)))
  (if (consp xs)
      (if (zp n) (car xs) (fn-frame-item (- n 1) (cdr xs)))
    nil))

; -----------------------------------------------------------------------------
; Structural facts about the splitter.  These are the shape lemmas every guard
; below needs; the value-level round trips live in `frame-invariants`.

(defthm fn-frame-octet-listp-true-listp
  (implies (fn-cbor-octet-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-frame-at-mostp-bounds-len
  (implies (and (fn-cbor-at-mostp xs bound) (natp bound))
           (<= (len xs) bound))
  :rule-classes :linear)

(defthm fn-frame-split-prefix-len
  (implies (fn-frame-split n xs)
           (equal (len (car (fn-frame-split n xs))) (nfix n))))

(defthm fn-frame-split-prefix-true-listp
  (true-listp (car (fn-frame-split n xs))))

(defthm fn-frame-split-suffix-true-listp
  (implies (true-listp xs)
           (true-listp (cdr (fn-frame-split n xs)))))

(defthm fn-frame-split-prefix-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-frame-split n xs))
           (fn-cbor-octet-listp (car (fn-frame-split n xs)))))

(defthm fn-frame-split-suffix-octets
  (implies (and (fn-cbor-octet-listp xs) (fn-frame-split n xs))
           (fn-cbor-octet-listp (cdr (fn-frame-split n xs)))))

; A successful split, stated both as the term callers test and as the cons it
; produces.  Rewriting a term to T is sound only in a propositional context,
; so the first form cannot turn `(car (fn-frame-split ...))` into `(car t)`.
(defthm fn-frame-split-exists
  (implies (<= (nfix n) (len xs))
           (fn-frame-split n xs)))

(defthm fn-frame-split-exists-consp
  (implies (<= (nfix n) (len xs))
           (consp (fn-frame-split n xs))))

(defthm fn-frame-split-suffix-len
  (implies (fn-frame-split n xs)
           (equal (len (cdr (fn-frame-split n xs)))
                  (- (len xs) (nfix n)))))

(defthm fn-frame-split-reassembles
  (implies (and (true-listp xs) (fn-frame-split n xs))
           (equal (append (car (fn-frame-split n xs))
                          (cdr (fn-frame-split n xs)))
                  xs)))

(defthm fn-frame-not-consp-when-len-zero
  (implies (equal (len a) 0) (not (consp a)))
  :hints (("Goal" :expand ((len a)))))

(defthm fn-frame-split-of-append
  (implies (and (true-listp a) (equal (len a) (nfix n)))
           (equal (fn-frame-split n (append a b)) (cons a b)))
  :hints (("Goal" :induct (fn-frame-split n a)
           :in-theory (enable fn-frame-split))))

; `len` counts conses, so a known length supplies the cons structure that the
; fixed-width big-endian readers' guards require.
(defthm fn-frame-len-2-conses
  (implies (equal (len xs) 2)
           (and (consp xs) (consp (cdr xs))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs))))))

(defthm fn-frame-len-4-conses
  (implies (equal (len xs) 4)
           (and (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs))))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                           (len (cdr (cdr (cdr xs))))))))

(defthm fn-frame-len-8-conses
  (implies (equal (len xs) 8)
           (and (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs))))))
  :hints (("Goal" :expand ((len xs) (len (cdr xs)) (len (cdr (cdr xs)))
                           (len (cdr (cdr (cdr xs))))))))

; Every fact the splitter is used for is now a lemma.  Opening its definition
; on a literal length would unroll it and defeat those lemmas, so from here it
; is reasoned about only through them.
(local (in-theory (disable fn-frame-split)))

(defthm fn-frame-symbol-listp-true-listp
  (implies (symbol-listp xs) (true-listp xs))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-frame-u16-from-natp
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs)))
           (natp (fn-cbor-u16-from xs)))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-u32-from-natp
  (implies (and (fn-cbor-octet-listp xs) (consp xs) (consp (cdr xs))
                (consp (cdr (cdr xs))) (consp (cdr (cdr (cdr xs)))))
           (natp (fn-cbor-u32-from xs)))
  :rule-classes (:rewrite :type-prescription))

; -----------------------------------------------------------------------------
; Unsigned big-endian fields beyond the CBOR profile's 32-bit argument

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

; Two CBOR 32-bit arguments, high half first.  The outer `mod` on the high
; half is a no-op for every value in the field's domain; it is written so that
; the guard obligation is the modulus bound rather than a division bound.
(defun fn-frame-u64-bytes (n)
  (declare (xargs :guard (and (natp n) (<= n *fn-frame-max-nat*))
                  :verify-guards nil))
  (append (fn-cbor-u32-bytes (mod (floor (nfix n) *fn-frame-u32-modulus*)
                                  *fn-frame-u32-modulus*))
          (fn-cbor-u32-bytes (mod (nfix n) *fn-frame-u32-modulus*))))

(verify-guards fn-frame-u64-bytes
  :hints (("Goal" :in-theory (disable floor))))

(defthm fn-frame-octet-listp-of-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b))))

(defthm fn-frame-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-frame-u16-bytes-len
  (equal (len (fn-cbor-u16-bytes n)) 2)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u16-bytes) (floor mod)))))

(defthm fn-frame-u32-bytes-len
  (equal (len (fn-cbor-u32-bytes n)) 4)
  :hints (("Goal" :in-theory (e/d (fn-cbor-u32-bytes) (floor mod)))))

(defthm fn-frame-u64-bytes-are-octets
  (fn-cbor-octet-listp (fn-frame-u64-bytes n))
  :hints (("Goal" :in-theory (e/d (fn-frame-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes)))))

(defthm fn-frame-u64-bytes-len
  (equal (len (fn-frame-u64-bytes n)) 8)
  :hints (("Goal" :in-theory (e/d (fn-frame-u64-bytes)
                                  (floor mod fn-cbor-u32-bytes)))))

; The shape of every big-endian field is now a lemma, so nothing below has to
; reason about quotients and remainders again.
(local (in-theory (disable fn-cbor-u16-bytes fn-cbor-u32-bytes
                           fn-frame-u64-bytes)))

(defun fn-frame-u64-from (xs)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs) (equal (len xs) 8))
                  :verify-guards nil))
  (let ((split (fn-frame-split 4 xs)))
    (+ (* *fn-frame-u32-modulus* (fn-cbor-u32-from (car split)))
       (fn-cbor-u32-from (cdr split)))))

(verify-guards fn-frame-u64-from)

; -----------------------------------------------------------------------------
; Field grammar for journal payloads
;
; A field specification is one of
;   :text          u16 length (1..512) then that many octets, valid UTF-8
;   :blob          u32 length (1..131072) then that many octets
;   :nat           eight octets, big-endian
;   (:enum . ks)   one octet, the 1-based position of a keyword in `ks`
; and a record payload is a list of specifications with a positional list of
; values.  The enumerations are 1-based positions so that code injectivity is
; a consequence of the keyword list having no duplicates rather than a second
; hand-maintained table.

(defun fn-frame-enum-specp (spec)
  (declare (xargs :guard t))
  (and (consp spec)
       (equal (car spec) :enum)
       (symbol-listp (cdr spec))
       (consp (cdr spec))
       (no-duplicatesp-equal (cdr spec))
       (<= (len (cdr spec)) 255)))

(defun fn-frame-specp (spec)
  (declare (xargs :guard t))
  (or (equal spec :text)
      (equal spec :blob)
      (equal spec :nat)
      (fn-frame-enum-specp spec)))

(defun fn-frame-spec-listp (specs)
  (declare (xargs :guard t))
  (if (consp specs)
      (and (fn-frame-specp (car specs))
           (fn-frame-spec-listp (cdr specs)))
    (null specs)))

; Text is UTF-8 by the wildmat book's RFC 3629 decoder.  The bound in front
; of it is this book's, so no second UTF-8 table exists anywhere in the tree.
(defun fn-frame-textp (octets)
  (declare (xargs :guard t))
  (and (fn-cbor-at-mostp octets *fn-frame-max-text*)
       (fn-cbor-octet-listp octets)
       (consp octets)
       (fn-wildmat-result-okp (fn-wildmat-decode-aux octets nil))))

(defun fn-frame-blobp (octets)
  (declare (xargs :guard t))
  (and (fn-cbor-at-mostp octets *fn-frame-max-blob*)
       (fn-cbor-octet-listp octets)
       (consp octets)))

(defun fn-frame-natp (n)
  (declare (xargs :guard t))
  (and (natp n) (<= n *fn-frame-max-nat*)))

(defun fn-frame-enum-index (value keys)
  ; 1-based position, or 0 when absent.
  (declare (xargs :guard (true-listp keys)))
  (if (consp keys)
      (if (equal value (car keys))
          1
        (let ((rest (fn-frame-enum-index value (cdr keys))))
          (if (equal rest 0) 0 (+ 1 rest))))
    0))

(defthm fn-frame-enum-index-natp
  (natp (fn-frame-enum-index value keys))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-frame-enum-index-bound
  (<= (fn-frame-enum-index value keys) (len keys))
  :rule-classes :linear)

(defun fn-frame-field-okp (spec value)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal spec :text)
      (fn-frame-textp value)
    (if (equal spec :blob)
        (fn-frame-blobp value)
      (if (equal spec :nat)
          (fn-frame-natp value)
        (and (fn-frame-enum-specp spec)
             (not (equal (fn-frame-enum-index value (cdr spec)) 0)))))))

(verify-guards fn-frame-field-okp)

(defun fn-frame-field-octets (spec value)
  (declare (xargs :guard (fn-frame-field-okp spec value)
                  :verify-guards nil))
  (if (equal spec :text)
      (append (fn-cbor-u16-bytes (len value)) value)
    (if (equal spec :blob)
        (append (fn-cbor-u32-bytes (len value)) value)
      (if (equal spec :nat)
          (fn-frame-u64-bytes value)
        (list (fn-frame-enum-index value (cdr spec)))))))

(verify-guards fn-frame-field-octets)

(defun fn-frame-parse-ok (value rest)
  (declare (xargs :guard t))
  (list :ok value rest))
(defun fn-frame-parse-error (reason)
  (declare (xargs :guard t))
  (list :error reason))
(defun fn-frame-parse-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-frame-parse-value (x)
  (declare (xargs :guard t))
  (fn-frame-item 1 x))
(defun fn-frame-parse-rest (x)
  (declare (xargs :guard t))
  (fn-frame-item 2 x))

(defun fn-frame-parse-counted (octets count maximum)
  ; Shared tail of the two length-prefixed field types.  The declared count is
  ; compared with its cap before the split allocates anything.
  (declare (xargs :guard (and (fn-cbor-octet-listp octets)
                              (natp count) (natp maximum))))
  (if (or (equal count 0) (< maximum count))
      (fn-frame-parse-error :field-length)
    (let ((split (fn-frame-split count octets)))
      (if (null split)
          (fn-frame-parse-error :truncated)
        (fn-frame-parse-ok (car split) (cdr split))))))

(defun fn-frame-field-parse (spec octets)
  (declare (xargs :guard (and (fn-frame-specp spec)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (equal spec :text)
      (let ((head (fn-frame-split 2 octets)))
        (if (null head)
            (fn-frame-parse-error :truncated)
          (let ((parsed (fn-frame-parse-counted
                         (cdr head) (nfix (fn-cbor-u16-from (car head)))
                         *fn-frame-max-text*)))
            (if (not (fn-frame-parse-okp parsed))
                parsed
              (if (not (fn-frame-textp (fn-frame-parse-value parsed)))
                  (fn-frame-parse-error :malformed-utf8)
                parsed)))))
    (if (equal spec :blob)
        (let ((head (fn-frame-split 4 octets)))
          (if (null head)
              (fn-frame-parse-error :truncated)
            (fn-frame-parse-counted (cdr head)
                                    (nfix (fn-cbor-u32-from (car head)))
                                    *fn-frame-max-blob*)))
      (if (equal spec :nat)
          (let ((head (fn-frame-split 8 octets)))
            (if (null head)
                (fn-frame-parse-error :truncated)
              (fn-frame-parse-ok (fn-frame-u64-from (car head)) (cdr head))))
        (if (not (consp octets))
            (fn-frame-parse-error :truncated)
          (let ((code (car octets)))
            (if (or (not (posp code)) (< (len (cdr spec)) code))
                (fn-frame-parse-error :unknown-enumeration)
              (fn-frame-parse-ok (fn-frame-item (- code 1) (cdr spec))
                                 (cdr octets)))))))))

(verify-guards fn-frame-field-parse
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from))))

(defthm fn-frame-field-parse-rest-octets
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-field-parse spec octets)))
           (fn-cbor-octet-listp
            (fn-frame-parse-rest (fn-frame-field-parse spec octets)))))

(defun fn-frame-values-okp (specs values)
  (declare (xargs :guard (fn-frame-spec-listp specs) :verify-guards nil))
  (if (consp specs)
      (and (consp values)
           (fn-frame-field-okp (car specs) (car values))
           (fn-frame-values-okp (cdr specs) (cdr values)))
    (null values)))

(verify-guards fn-frame-values-okp)

(defun fn-frame-fields-octets (specs values)
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-frame-values-okp specs values))
                  :verify-guards nil))
  (if (consp specs)
      (append (fn-frame-field-octets (car specs) (car values))
              (fn-frame-fields-octets (cdr specs) (cdr values)))
    nil))

(verify-guards fn-frame-fields-octets)

(defthm fn-frame-field-octets-are-octets
  (implies (and (fn-frame-specp spec) (fn-frame-field-okp spec value))
           (fn-cbor-octet-listp (fn-frame-field-octets spec value)))
  :hints (("Goal" :in-theory (e/d (fn-frame-field-octets fn-frame-field-okp
                                   fn-frame-specp fn-frame-textp
                                   fn-frame-blobp fn-frame-natp
                                   fn-frame-enum-specp)
                                  (floor mod fn-cbor-u16-bytes
                                   fn-cbor-u32-bytes fn-frame-u64-bytes)))))

(defthm fn-frame-fields-octets-are-octets
  (implies (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))
           (fn-cbor-octet-listp (fn-frame-fields-octets specs values)))
  :hints (("Goal" :induct (fn-frame-values-okp specs values)
           :in-theory (disable fn-frame-field-octets))))

(defun fn-frame-fields-parse-aux (specs octets)
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-cbor-octet-listp octets))
                  :verify-guards nil))
  (if (consp specs)
      (let ((parsed (fn-frame-field-parse (car specs) octets)))
        (if (not (fn-frame-parse-okp parsed))
            parsed
          (let ((rest (fn-frame-fields-parse-aux
                       (cdr specs) (fn-frame-parse-rest parsed))))
            (if (not (fn-frame-parse-okp rest))
                rest
              (fn-frame-parse-ok (cons (fn-frame-parse-value parsed)
                                       (fn-frame-parse-value rest))
                                 (fn-frame-parse-rest rest))))))
    (fn-frame-parse-ok nil octets)))

(verify-guards fn-frame-fields-parse-aux)

(defun fn-frame-fields-parse (specs octets)
  ; A record payload is exactly its fields: a trailing octet is a refusal,
  ; not a value silently disregarded.
  (declare (xargs :guard (and (fn-frame-spec-listp specs)
                              (fn-cbor-octet-listp octets))))
  (let ((parsed (fn-frame-fields-parse-aux specs octets)))
    (if (not (fn-frame-parse-okp parsed))
        parsed
      (if (null (fn-frame-parse-rest parsed))
          parsed
        (fn-frame-parse-error :trailing)))))

; -----------------------------------------------------------------------------
; Frame encoder

(defun fn-frame-header (magic version kind length)
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (natp length)
                              (<= length *fn-cbor-max-uint*))
                  :verify-guards nil))
  (append magic (cons version (cons kind (fn-cbor-u32-bytes length)))))

(verify-guards fn-frame-header)

(defun fn-frame-inputp (magic version kind payload max-payload)
  (declare (xargs :guard t))
  (and (fn-frame-magicp magic)
       (fn-cbor-octetp version)
       (fn-cbor-octetp kind)
       (fn-cbor-octet-listp payload)
       (natp max-payload)
       (<= max-payload *fn-frame-max-payload*)
       (<= (len payload) max-payload)))

(defun fn-frame-protected (magic version kind payload)
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (append (fn-frame-header magic version kind (len payload)) payload))

(verify-guards fn-frame-protected)

(defun fn-frame-encode (magic version kind payload digest)
  ; The host entry point.  `digest` is the host's 32 octets over the protected
  ; prefix; `fn-frame-encode-is-seal` says what must be true of it.
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*)
                              (fn-frame-digestp digest))
                  :verify-guards nil))
  (append (fn-frame-protected magic version kind payload) digest))

(verify-guards fn-frame-encode)

(defun fn-frame-seal (magic version kind payload)
  ; The specification encoder, stated against A-CRYPTO.  Not executable.
  (declare (xargs :guard (and (fn-frame-magicp magic)
                              (fn-cbor-octetp version)
                              (fn-cbor-octetp kind)
                              (fn-cbor-octet-listp payload)
                              (<= (len payload) *fn-cbor-max-uint*))
                  :verify-guards nil))
  (fn-frame-encode magic version kind payload
                   (fn-frame-digest
                    (fn-frame-protected magic version kind payload))))

(verify-guards fn-frame-seal)

; -----------------------------------------------------------------------------
; Frame decoder

(defun fn-frame-ok (magic version kind payload)
  (declare (xargs :guard t))
  (list :ok magic version kind payload))
(defun fn-frame-error (reason)
  (declare (xargs :guard t))
  (list :error reason))
(defun fn-frame-result-okp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :ok)))
(defun fn-frame-result-magic (x)
  (declare (xargs :guard t))
  (fn-frame-item 1 x))
(defun fn-frame-result-version (x)
  (declare (xargs :guard t))
  (fn-frame-item 2 x))
(defun fn-frame-result-kind (x)
  (declare (xargs :guard t))
  (fn-frame-item 3 x))
(defun fn-frame-result-payload (x)
  (declare (xargs :guard t))
  (fn-frame-item 4 x))

(defun fn-frame-head-fields (head)
  ; (magic version kind length-octets) from a 10-octet header, or nil.
  (declare (xargs :guard (fn-cbor-octet-listp head) :verify-guards nil))
  (let ((magic (fn-frame-split *fn-frame-magic-octets* head)))
    (if (null magic)
        nil
      (let ((version-kind (fn-frame-split 2 (cdr magic))))
        (if (null version-kind)
            nil
          (let ((length-octets (fn-frame-split 4 (cdr version-kind))))
            (if (or (null length-octets) (cdr length-octets))
                nil
              (list (car magic)
                    (fn-frame-item 0 (car version-kind))
                    (fn-frame-item 1 (car version-kind))
                    (car length-octets)))))))))

(verify-guards fn-frame-head-fields)

(defthm fn-frame-head-fields-shape
  (implies (and (fn-cbor-octet-listp head) (fn-frame-head-fields head))
           (and (fn-cbor-octet-listp
                 (fn-frame-item 3 (fn-frame-head-fields head)))
                (equal (len (fn-frame-item 3 (fn-frame-head-fields head)))
                       4))))

(defun fn-frame-decode (octets digest max-payload)
  ; The host entry point.  Every bound is checked before the corresponding
  ; split allocates: the cons preflight before octet validation, the declared
  ; payload length against `max-payload` and against the actual remainder
  ; before the payload split.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (natp max-payload) (<= max-payload *fn-frame-max-payload*)))
      (fn-frame-error :bound)
    (if (not (fn-cbor-at-mostp octets
                               (+ *fn-frame-overhead-octets* max-payload)))
        (fn-frame-error :limit)
      (if (not (fn-cbor-octet-listp octets))
          (fn-frame-error :malformed)
        (let ((head (fn-frame-split *fn-frame-header-octets* octets)))
          (if (null head)
              (fn-frame-error :truncated)
            (let ((fields (fn-frame-head-fields (car head))))
              (if (null fields)
                  (fn-frame-error :truncated)
                (let ((declared (nfix (fn-cbor-u32-from
                                       (fn-frame-item 3 fields)))))
                  (if (< max-payload declared)
                      (fn-frame-error :limit)
                    (if (not (equal (len (cdr head))
                                    (+ declared *fn-frame-trailer-octets*)))
                        ; A header that declares more payload than the octets
                        ; still hold is a cut frame, not a disagreement about
                        ; a bound: `:truncated` there, and `:length` only for
                        ; octets past the frame the header describes.
                        (if (< (len (cdr head))
                               (+ declared *fn-frame-trailer-octets*))
                            (fn-frame-error :truncated)
                          (fn-frame-error :length))
                      (if (not (fn-frame-digestp digest))
                          (fn-frame-error :digest)
                        (let ((body (fn-frame-split declared (cdr head))))
                          (if (null body)
                              (fn-frame-error :truncated)
                            (if (not (equal (cdr body) digest))
                                (fn-frame-error :integrity)
                              (fn-frame-ok (fn-frame-item 0 fields)
                                           (fn-frame-item 1 fields)
                                           (fn-frame-item 2 fields)
                                           (car body)))))))))))))))))

(verify-guards fn-frame-decode
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from
                                      fn-frame-head-fields))))

(defthm fn-frame-decode-payload-octets
  (implies (fn-frame-result-okp (fn-frame-decode octets digest max-payload))
           (fn-cbor-octet-listp
            (fn-frame-result-payload (fn-frame-decode octets digest
                                                      max-payload))))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from
                                      fn-frame-head-fields))))

(defun fn-frame-protected-prefix (octets)
  ; Everything a trailer covers: the frame minus its last 32 octets.
  (declare (xargs :guard (fn-cbor-octet-listp octets) :verify-guards nil))
  (let ((split (fn-frame-split
                (nfix (- (len octets) *fn-frame-trailer-octets*)) octets)))
    (if (null split) nil (car split))))

(verify-guards fn-frame-protected-prefix)

(defun fn-frame-open (octets max-payload)
  ; The specification decoder, stated against A-CRYPTO.  Not executable.
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (fn-frame-decode octets
                   (fn-frame-digest (fn-frame-protected-prefix octets))
                   max-payload))

; -----------------------------------------------------------------------------
; Whole records: a kind selects a field specification, and a frame carries the
; encoded fields.  The two journal schemas below are the ones the durable
; adapters use; the store frame's payload is an opaque CBOR record and needs
; no field specification.

(defconst *fn-frame-magic-store* '(70 78 83 84))    ; FNST
(defconst *fn-frame-magic-workflow* '(70 78 87 70)) ; FNWF
(defconst *fn-frame-magic-receipt* '(70 78 82 74))  ; FNRJ
(defconst *fn-frame-magic-inbound* '(70 78 66 73))  ; FNBI

(defconst *fn-frame-version* 1)

(defconst *fn-frame-store-kind* 1)
(defconst *fn-frame-inbound-kind* 1)

(defconst *fn-frame-max-store-payload* 65538)
(defconst *fn-frame-max-workflow-payload* 16342)
(defconst *fn-frame-max-receipt-payload* 269958)
(defconst *fn-frame-max-inbound-payload* 4194304)
; The canonical primary-block identity of a staged inbound bundle, as
; `books/bp-primary.lisp` encodes it: a CBOR array of an endpoint ID and three
; or five unsigned integers.  The endpoint's scheme-specific part is the only
; unbounded part and that codec caps it at 1024 octets, so this cap leaves
; room for the array and integer heads and still keeps the frame head small
; enough to cross the decimal octet bridge in one call.
(defconst *fn-frame-max-identity* 1152)

(defconst *fn-frame-transport-statuses*
  '(:intent :bpa-submit-replied :bpa-accepted :attempted :forwarded
    :delivered :deleted :expired :unknown :no-contact :inbound-persisted
    :dequeued :restart-observed))
(defconst *fn-frame-phases* '(:ordinary :recovery))
(defconst *fn-frame-results* '(:durable :aborted :committed :absent))
(defconst *fn-frame-receipt-outcomes* '(:committed :absent))
(defconst *fn-frame-authorized* '(:authorized))

(defconst *fn-frame-workflow-kinds*
  '(:config :enqueue :attempt :transport :receipt-intent :outcome
    :retry-request))

(defconst *fn-frame-workflow-specs*
  (list
   (cons :config '(:text :text :text :text :nat :text :text))
   (cons :enqueue '(:nat :nat :text :text :text :text :text :text :text :text))
   (cons :attempt '(:nat :nat :text :text :nat :text :text :text :nat))
   (cons :transport
         (list :text :text :nat (cons :enum *fn-frame-transport-statuses*)))
   (cons :receipt-intent
         '(:nat :nat :text :text :text :text :text :text :text :text :text))
   (cons :outcome
         (list :nat :nat (cons :enum *fn-frame-phases*)
               (cons :enum *fn-frame-results*)))
   (cons :retry-request '(:text :text :nat :text))))

(defconst *fn-frame-receipt-kinds*
  '(:config :request-context :receipt-intent :receipt-decision))

(defconst *fn-frame-receipt-specs*
  (list
   (cons :config '(:text :text :text))
   (cons :request-context
         (list :text :blob :blob (cons :enum *fn-frame-authorized*)))
   (cons :receipt-intent
         (list :text :text :blob (cons :enum *fn-frame-authorized*)))
   (cons :receipt-decision
         (list :text :text (cons :enum *fn-frame-receipt-outcomes*)))))

(defun fn-frame-spec-for (kind table)
  (declare (xargs :guard t))
  (if (consp table)
      (if (and (consp (car table)) (equal (car (car table)) kind))
          (cdr (car table))
        (fn-frame-spec-for kind (cdr table)))
    :none))

(defthm fn-frame-spec-for-workflow-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-frame-workflow-specs*) :none))
           (fn-frame-spec-listp
            (fn-frame-spec-for kind *fn-frame-workflow-specs*))))

(defthm fn-frame-spec-for-receipt-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-frame-receipt-specs*) :none))
           (fn-frame-spec-listp
            (fn-frame-spec-for kind *fn-frame-receipt-specs*))))

; The outcome record's phase and result are not independent: an ordinary
; outcome is durable or aborted and a recovery outcome is committed or absent.
; Both the encoder and the decoder apply this, so a journal cannot hold a
; combination replay would have to interpret.
(defun fn-frame-outcome-pairp (phase result)
  (declare (xargs :guard t))
  (or (and (equal phase :ordinary)
           (or (equal result :durable) (equal result :aborted)))
      (and (equal phase :recovery)
           (or (equal result :committed) (equal result :absent)))))

(defun fn-frame-workflow-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values)
         (or (not (equal kind :outcome))
             (fn-frame-outcome-pairp (fn-frame-item 2 values)
                                     (fn-frame-item 3 values))))))

(verify-guards fn-frame-workflow-record-okp)

(defun fn-frame-receipt-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-frame-receipt-record-okp)

; -----------------------------------------------------------------------------
; The concrete entry points the host wrappers call

(defun fn-frame-store-encode (record digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp record))
          (not (fn-cbor-at-mostp record *fn-frame-max-store-payload*))
          (not (fn-frame-digestp digest)))
      :bad
    (fn-frame-encode *fn-frame-magic-store* *fn-frame-version*
                     *fn-frame-store-kind* record digest)))

(verify-guards fn-frame-store-encode)

(defun fn-frame-store-decode (octets digest)
  (declare (xargs :guard t))
  (let ((frame (fn-frame-decode octets digest *fn-frame-max-store-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-frame-magic-store*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)
                    (equal (fn-frame-result-kind frame) *fn-frame-store-kind*)))
          (fn-frame-error :magic)
        frame))))

(defun fn-frame-workflow-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-workflow-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-workflow-kinds*)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-frame-magic-workflow* *fn-frame-version* code
                         (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-workflow-specs*)
                          values)
                         digest)))))

(verify-guards fn-frame-workflow-encode)

(defun fn-frame-workflow-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest
                                *fn-frame-max-workflow-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame)
                           *fn-frame-magic-workflow*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-frame-workflow-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1)
                                        *fn-frame-workflow-kinds*))
                   (spec (fn-frame-spec-for kind *fn-frame-workflow-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (if (not (fn-frame-workflow-record-okp
                              kind (fn-frame-parse-value parsed)))
                        (fn-frame-error :outcome-pair)
                      (fn-frame-ok *fn-frame-magic-workflow* *fn-frame-version*
                                   kind
                                   (fn-frame-parse-value parsed)))))))))))))

(verify-guards fn-frame-workflow-decode)

(defun fn-frame-receipt-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-receipt-record-okp kind values)
                (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-receipt-kinds*)))
      (if (equal code 0)
          :bad
        (fn-frame-encode *fn-frame-magic-receipt* *fn-frame-version* code
                         (fn-frame-fields-octets
                          (fn-frame-spec-for kind *fn-frame-receipt-specs*)
                          values)
                         digest)))))

(verify-guards fn-frame-receipt-encode)

(defun fn-frame-receipt-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest
                                *fn-frame-max-receipt-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame)
                           *fn-frame-magic-receipt*)
                    (equal (fn-frame-result-version frame) *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-frame-receipt-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1)
                                        *fn-frame-receipt-kinds*))
                   (spec (fn-frame-spec-for kind *fn-frame-receipt-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (fn-frame-ok *fn-frame-magic-receipt* *fn-frame-version*
                                 kind
                                 (fn-frame-parse-value parsed))))))))))))

(verify-guards fn-frame-receipt-decode)

; An inbound bundle is up to four mebibytes, which cannot cross the decimal
; octet bridge.  ACL2 still owns every decision about the frame: it builds the
; whole protected prefix through the BID text field, and on the way back in it
; validates magic, version, kind, the declared length, the BID field and the
; trailer.  The host concatenates and compares bytes it never interprets.
(defun fn-frame-inbound-prefix (bid ident bundle-length)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-frame-textp bid)
                (fn-frame-blobp ident)
                (<= (len ident) *fn-frame-max-identity*)
                (natp bundle-length)
                (<= (+ 2 (len bid) 4 (len ident) bundle-length)
                    *fn-frame-max-inbound-payload*)))
      :bad
    (let ((fields (append (fn-frame-field-octets :text bid)
                          (fn-frame-field-octets :blob ident))))
      (append (fn-frame-header *fn-frame-magic-inbound* *fn-frame-version*
                               *fn-frame-inbound-kind*
                               (+ (len fields) bundle-length))
              fields))))

(verify-guards fn-frame-inbound-prefix)

(defun fn-frame-inbound-open (head total-length trailer digest)
  ; `head` is a bounded prefix of the stored frame (the host sends at most
  ; header + the two ident fields), `total-length` its whole size, `trailer`
  ; its last 32 octets and `digest` the host's digest over everything but those
  ; 32.  The BID is the transport handle the agent issued; the ident is what
  ; the bundle itself says it is, and the two are returned together so that a
  ; caller cannot read one without the other.
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp head)
                (fn-cbor-at-mostp head (+ *fn-frame-header-octets* 2
                                          *fn-frame-max-text* 4
                                          *fn-frame-max-identity*))
                (natp total-length)
                (fn-frame-digestp trailer)
                (fn-frame-digestp digest)))
      (fn-frame-error :malformed)
    (if (not (equal trailer digest))
        (fn-frame-error :integrity)
      (let ((split (fn-frame-split *fn-frame-header-octets* head)))
        (if (null split)
            (fn-frame-error :truncated)
          (let ((fields (fn-frame-head-fields (car split))))
            (if (null fields)
                (fn-frame-error :truncated)
              (if (not (and (equal (fn-frame-item 0 fields)
                                   *fn-frame-magic-inbound*)
                            (equal (fn-frame-item 1 fields) *fn-frame-version*)
                            (equal (fn-frame-item 2 fields)
                                   *fn-frame-inbound-kind*)))
                  (fn-frame-error :magic)
                (let ((declared (nfix (fn-cbor-u32-from
                                       (fn-frame-item 3 fields)))))
                  (if (< *fn-frame-max-inbound-payload* declared)
                      (fn-frame-error :limit)
                    (if (not (equal total-length
                                    (+ *fn-frame-overhead-octets* declared)))
                        ; Same distinction as `fn-frame-decode`: fewer octets
                        ; than the header declares is truncation.
                        (if (< total-length
                               (+ *fn-frame-overhead-octets* declared))
                            (fn-frame-error :truncated)
                          (fn-frame-error :length))
                      (let ((parsed (fn-frame-field-parse :text (cdr split))))
                        (if (not (fn-frame-parse-okp parsed))
                            (fn-frame-error :field-length)
                          (let ((blob (fn-frame-field-parse
                                         :blob (fn-frame-parse-rest parsed))))
                            (if (not (fn-frame-parse-okp blob))
                                (fn-frame-error :field-length)
                              (let ((bid (fn-frame-parse-value parsed))
                                    (ident (fn-frame-parse-value blob)))
                                (if (< *fn-frame-max-identity* (len ident))
                                    (fn-frame-error :limit)
                                  (if (< declared
                                         (+ 2 (len bid) 4 (len ident)))
                                      (fn-frame-error :length)
                                    (fn-frame-ok
                                     *fn-frame-magic-inbound*
                                     *fn-frame-version*
                                     (list bid ident)
                                     (- declared
                                        (+ 2 (len bid)
                                           4 (len ident))))))))))))))))))))))

(verify-guards fn-frame-inbound-open
  :hints (("Goal" :in-theory (disable fn-cbor-u16-from fn-cbor-u32-from
                                      fn-frame-head-fields))))

; -----------------------------------------------------------------------------
; Protected prefixes
;
; The host computes the trailer, so it needs the exact octets the trailer
; covers.  These return that prefix; appending 32 digest octets to it is
; `fn-frame-encode`, which `fn-frame-*-encode-is-protected-plus-digest` in
; `frame-invariants` proves.  No other part of the frame is the host's.

(defun fn-frame-store-protected (record)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-cbor-octet-listp record))
          (not (fn-cbor-at-mostp record *fn-frame-max-store-payload*)))
      :bad
    (fn-frame-protected *fn-frame-magic-store* *fn-frame-version*
                        *fn-frame-store-kind* record)))

(verify-guards fn-frame-store-protected)

(defun fn-frame-workflow-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-workflow-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-workflow-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-workflow-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-workflow-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-workflow* *fn-frame-version* code
                            payload)))))

(verify-guards fn-frame-workflow-protected)

(defun fn-frame-receipt-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-receipt-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-receipt-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-receipt-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-receipt-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-receipt* *fn-frame-version* code
                            payload)))))

(verify-guards fn-frame-receipt-protected)

; -----------------------------------------------------------------------------
; The field names a host uses to label a decoded record
;
; The names are presentation only; the grammar above decides every byte.  They
; live here so that no adapter keeps its own ordered field list: the host asks
; for the names and the specification together, and `frame-tests` checks that
; the two lists have the same length for every kind.

(defconst *fn-frame-workflow-field-names*
  (list
   (cons :config '("local-eid" "peer-eid" "policy-id" "receipt-authority"
                   "bp-lifetime" "incarnation" "authorization-context"))
   (cons :enqueue '("txid" "tx-generation" "work-id" "msgid"
                    "immutable-subject" "archive-obligation-id"
                    "forward-obligation-id" "peer-eid" "policy-id" "terms-id"))
   (cons :attempt '("txid" "tx-generation" "work-id" "attempt-id"
                    "attempt-generation" "local-eid" "peer-eid" "policy-id"
                    "bp-lifetime"))
   (cons :transport '("work-id" "attempt-id" "attempt-generation" "status"))
   (cons :receipt-intent '("txid" "tx-generation" "receipt-id" "work-id"
                           "immutable-subject" "issuer-eid" "peer-eid"
                           "policy-id" "incarnation" "authorization-context"
                           "terms-id"))
   (cons :outcome '("txid" "tx-generation" "phase" "result"))
   (cons :retry-request '("work-id" "attempt-id" "attempt-generation"
                          "policy-id"))))

(defconst *fn-frame-receipt-field-names*
  (list
   (cons :config '("destination-eid" "policy-id" "issuer-eid"))
   (cons :request-context '("inbound-bid" "request-adu" "store-record"
                            "policy-authorized"))
   (cons :receipt-intent '("work-id" "receipt-id" "receipt-adu"
                           "policy-authorized"))
   (cons :receipt-decision '("work-id" "receipt-id" "outcome"))))
