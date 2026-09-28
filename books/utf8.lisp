; fn: bounded RFC 3629 UTF-8 decoding over octet lists.
;
; The decoder that `books/wildmat.lisp' (RFC 3977 wildmat parsing and
; matching) and `books/frame-fields.lisp' (frame text fields) share.  It was
; the UTF-8 section of the wildmat book; it is its own book so that a frame
; field's text check does not put the glob matcher, and every book above the
; matcher, into the frame codec's include closure.  Every name keeps its
; `fn-wildmat-' prefix: the registries, the ledger and the includers key on
; the names, and nothing but the book boundary moved (lane architect,
; 2026-09-28).
;
; The parser decodes UTF-8 into Unicode scalar values and rejects malformed,
; overlong, surrogate and out-of-range encodings (RFC 3977 section 9
; incorporates RFC 3629's restricted productions).  Inputs are lists of
; octets, never Lisp strings; the local profile caps a decoded argument at 497
; octets (RFC 3977 section 3.1).  No Lisp reader, evaluator or interning is
; used.

(in-package "ACL2")
(include-book "cbor")

(defconst *fn-wildmat-max-octets* 497)
(defconst *fn-wildmat-max-codepoint* 1114111)

; -----------------------------------------------------------------------------
; Bounded octets, tagged results, and UTF-8 decoding

; Reuse the shared bounded-octet primitives.  Keeping these small wrappers
; gives this book a domain-specific public vocabulary without a second octet
; implementation.
(defun fn-wildmat-octetp (x) (fn-cbor-octetp x))
(defun fn-wildmat-octet-listp (xs) (fn-cbor-octet-listp xs))
(defun fn-wildmat-at-mostp (xs bound)
  (declare (xargs :guard (natp bound) :verify-guards nil))
  (fn-cbor-at-mostp xs bound))

(defun fn-wildmat-ok (value) (list :ok value))
(defun fn-wildmat-error (reason) (list :error reason))
(defun fn-wildmat-result-okp (result)
  (and (consp result) (equal (car result) :ok)))
(defun fn-wildmat-result-value (result)
  (declare (xargs :guard (true-listp result) :verify-guards nil))
  (car (cdr result)))

; A UTF-8 step includes its unconsumed input so decoding can be structural and
; does not need indexing or an unbounded numeric conversion.
(defun fn-wildmat-utf8-ok (codepoint rest) (list :ok codepoint rest))
(defun fn-wildmat-utf8-rest (result)
  (declare (xargs :guard (true-listp result) :verify-guards nil))
  (car (cdr (cdr result))))

(defun fn-wildmat-utf8-tailp (byte)
  (and (integerp byte) (<= 128 byte) (<= byte 191)))

(defun fn-wildmat-utf8-2p (xs)
  (declare (xargs :guard (and (consp xs) (integerp (car xs))) :verify-guards nil))
  (and (consp xs) (consp (cdr xs))
       (<= 194 (car xs)) (<= (car xs) 223)
       (fn-wildmat-utf8-tailp (car (cdr xs)))))

(defun fn-wildmat-utf8-3-tailsp (xs)
  (and (consp xs) (consp (cdr xs)) (consp (cdr (cdr xs)))
       (fn-wildmat-utf8-tailp (car (cdr xs)))
       (fn-wildmat-utf8-tailp (car (cdr (cdr xs))))))

(defun fn-wildmat-utf8-4-tailsp (xs)
  (and (consp xs) (consp (cdr xs)) (consp (cdr (cdr xs)))
       (consp (cdr (cdr (cdr xs))))
       (fn-wildmat-utf8-tailp (car (cdr xs)))
       (fn-wildmat-utf8-tailp (car (cdr (cdr xs))))
       (fn-wildmat-utf8-tailp (car (cdr (cdr (cdr xs)))))))

(defun fn-wildmat-utf8-2-value (xs)
  (declare (xargs :guard (and (consp xs) (consp (cdr xs))
                              (integerp (car xs))
                              (integerp (car (cdr xs)))) :verify-guards nil))
  (+ (* 64 (- (car xs) 192))
     (- (car (cdr xs)) 128)))

(defun fn-wildmat-utf8-3-value (xs)
  (declare (xargs :guard (and (consp xs) (consp (cdr xs))
                              (consp (cdr (cdr xs)))
                              (integerp (car xs))
                              (integerp (car (cdr xs)))
                              (integerp (car (cdr (cdr xs))))) :verify-guards nil))
  (+ (* 4096 (- (car xs) 224))
     (* 64 (- (car (cdr xs)) 128))
     (- (car (cdr (cdr xs))) 128)))

(defun fn-wildmat-utf8-4-value (xs)
  (declare (xargs :guard (and (consp xs) (consp (cdr xs))
                              (consp (cdr (cdr xs)))
                              (consp (cdr (cdr (cdr xs))))
                              (integerp (car xs))
                              (integerp (car (cdr xs)))
                              (integerp (car (cdr (cdr xs))))
                              (integerp (car (cdr (cdr (cdr xs)))))) :verify-guards nil))
  (+ (* 262144 (- (car xs) 240))
     (* 4096 (- (car (cdr xs)) 128))
     (* 64 (- (car (cdr (cdr xs))) 128))
     (- (car (cdr (cdr (cdr xs)))) 128)))

; RFC 3977 section 9 incorporates RFC 3629's restricted UTF-8 productions.
; The leading-byte-specific second-byte ranges reject overlong forms,
; surrogates, and values above U+10FFFF before a scalar value is returned.
(defun fn-wildmat-utf8-next (octets)
  ; The public decoder preflights its whole octet list.  Keep this internal
  ; step's successful-result contract sound on arbitrary ACL2 arguments too.
  (if (not (and (consp octets)
                (fn-wildmat-octetp (car octets))))
      (fn-wildmat-error :malformed-utf8)
    (let ((first (car octets)))
      (if (< first 128)
          (fn-wildmat-utf8-ok first (cdr octets))
        (if (fn-wildmat-utf8-2p octets)
            (fn-wildmat-utf8-ok (fn-wildmat-utf8-2-value octets)
                                (cdr (cdr octets)))
          (if (and (fn-wildmat-utf8-3-tailsp octets)
                   (or (and (equal first 224)
                            (<= 160 (car (cdr octets))))
                       (and (<= 225 first) (<= first 236))
                       (and (equal first 237)
                            (<= (car (cdr octets)) 159))
                       (and (<= 238 first) (<= first 239))))
              (fn-wildmat-utf8-ok (fn-wildmat-utf8-3-value octets)
                                  (cdr (cdr (cdr octets))))
            (if (and (fn-wildmat-utf8-4-tailsp octets)
                     (or (and (equal first 240)
                              (<= 144 (car (cdr octets))))
                         (and (<= 241 first) (<= first 243))
                         (and (equal first 244)
                              (<= (car (cdr octets)) 143))))
                (fn-wildmat-utf8-ok (fn-wildmat-utf8-4-value octets)
                                    (cdr (cdr (cdr (cdr octets)))))
              (fn-wildmat-error :malformed-utf8))))))))

(defun fn-wildmat-decode-aux (octets codepoints-rev)
  (declare (xargs :measure (acl2-count octets)
                  :guard (true-listp codepoints-rev)
                  :verify-guards nil))
  (if (consp octets)
      (let ((next (fn-wildmat-utf8-next octets)))
        (if (fn-wildmat-result-okp next)
            (fn-wildmat-decode-aux (fn-wildmat-utf8-rest next)
                                    (cons (fn-wildmat-result-value next)
                                          codepoints-rev))
          next))
    (fn-wildmat-ok (reverse codepoints-rev))))

; This public decoder is also useful to a caller that wants to distinguish
; command-token validation from generic wildmat matching.
(defun fn-wildmat-decode (octets)
  (if (not (fn-wildmat-at-mostp octets *fn-wildmat-max-octets*))
      (fn-wildmat-error :limit)
    (if (not (fn-wildmat-octet-listp octets))
        (fn-wildmat-error :malformed-octets)
      (fn-wildmat-decode-aux octets nil))))

(defun fn-wildmat-codepointp (x)
  (and (natp x) (<= x *fn-wildmat-max-codepoint*)))

(defun fn-wildmat-codepoint-listp (xs)
  (if (consp xs)
      (and (fn-wildmat-codepointp (car xs))
           (fn-wildmat-codepoint-listp (cdr xs)))
    (null xs)))

(defthm fn-wildmat-guard-octet-listp-true-listp
  (implies (fn-wildmat-octet-listp octets)
           (true-listp octets))
  :hints (("Goal" :induct (fn-cbor-octet-listp octets)
           :in-theory (enable fn-wildmat-octet-listp fn-cbor-octet-listp))))

(defthm fn-wildmat-guard-utf8-next-success-rest-true-listp
  (implies (and (true-listp octets)
                (fn-wildmat-result-okp (fn-wildmat-utf8-next octets)))
           (true-listp
            (fn-wildmat-utf8-rest (fn-wildmat-utf8-next octets))))
  :hints (("Goal"
           :in-theory (enable fn-wildmat-utf8-next
                               fn-wildmat-result-okp
                               fn-wildmat-utf8-rest
                               fn-wildmat-utf8-ok
                               fn-wildmat-error))))

(defthm fn-wildmat-guard-decode-aux-success-true-listp
  (implies (and (true-listp octets)
                (true-listp codepoints-rev)
                (fn-wildmat-result-okp
                 (fn-wildmat-decode-aux octets codepoints-rev)))
           (true-listp
            (fn-wildmat-result-value
             (fn-wildmat-decode-aux octets codepoints-rev))))
  :hints (("Goal"
           :induct (fn-wildmat-decode-aux octets codepoints-rev)
           :in-theory (enable fn-wildmat-decode-aux
                               fn-wildmat-result-okp
                               fn-wildmat-result-value))))

(defthm fn-wildmat-guard-decode-success-true-listp
  (implies (and (fn-wildmat-octet-listp octets)
                (fn-wildmat-result-okp (fn-wildmat-decode octets)))
           (true-listp (fn-wildmat-result-value (fn-wildmat-decode octets))))
  :hints (("Goal"
           :use ((:instance fn-wildmat-guard-octet-listp-true-listp)
                 (:instance fn-wildmat-guard-decode-aux-success-true-listp
                            (codepoints-rev nil)))
           :in-theory (enable fn-wildmat-decode
                               fn-wildmat-result-okp
                               fn-wildmat-result-value))))

; Isolated guard-graph probe.
(verify-guards fn-wildmat-octetp)
(verify-guards fn-wildmat-octet-listp)
(verify-guards fn-wildmat-at-mostp)
(verify-guards fn-wildmat-ok)
(verify-guards fn-wildmat-error)
(verify-guards fn-wildmat-result-okp)
(verify-guards fn-wildmat-result-value)
(verify-guards fn-wildmat-utf8-ok)
(verify-guards fn-wildmat-utf8-rest)
(verify-guards fn-wildmat-utf8-tailp)
(verify-guards fn-wildmat-utf8-2p)
(verify-guards fn-wildmat-utf8-3-tailsp)
(verify-guards fn-wildmat-utf8-4-tailsp)
(verify-guards fn-wildmat-utf8-2-value)
(verify-guards fn-wildmat-utf8-3-value)
(verify-guards fn-wildmat-utf8-4-value)
(verify-guards fn-wildmat-utf8-next)
(verify-guards fn-wildmat-decode-aux)
(verify-guards fn-wildmat-decode)
(verify-guards fn-wildmat-codepointp)
(verify-guards fn-wildmat-codepoint-listp)

(defthm fn-wildmat-octet-listp-forward-shape
  (implies (fn-wildmat-octet-listp octets)
           (true-listp octets))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-wildmat-guard-octet-listp-true-listp)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-wildmat-decode-aux)
                    (:definition fn-wildmat-utf8-3-value)
                    (:definition fn-wildmat-utf8-4-tailsp)
                    (:definition fn-wildmat-utf8-4-value)
                    (:definition fn-wildmat-utf8-next)))
