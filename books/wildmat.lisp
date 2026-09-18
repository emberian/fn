; fn: bounded executable RFC 3977 wildmat parsing and matching.
;
; RFC 3977 sections 4.1 and 4.2 define the accepted grammar and the anchored,
; rightmost-pattern matching rule.  This book implements exactly that base
; grammar: `*` and `?` are wildcards and `!` is permitted only immediately
; after a separating comma.  It deliberately does not implement bracket sets,
; backslash quoting, or other extension syntax described as possible in section
; 4.3.
;
; Inputs and targets are lists of octets, not Lisp strings.  The local profile
; caps each at 497 octets (the RFC 3977 section 3.1 argument limit).  A bounded
; list-shape preflight happens before octet validation or UTF-8 traversal.  The
; parser then decodes UTF-8 into Unicode scalar values, rejects malformed,
; overlong, surrogate, and out-of-range encodings, and applies the grammar to
; whole characters.  In particular, `?` consumes one scalar value and `*`
; never splits a UTF-8 sequence.  No Lisp reader, evaluator, or interning is
; used.
;
; `fn-wildmat-parse` returns `(:ok patterns)` or `(:error reason)`.  A pattern
; is `(:positive items)` or `(:negative items)`; items are scalar values with
; 42 and 63 denoting `*` and `?`.  `fn-wildmat-match` parses and matches source
; and target in one call, returning `(:ok boolean)` or the relevant error.
; `fn-wildmat-match-parsed` accepts the successful parser value.
;
; RFC 3977 section 3.1 bans a BOM in a command line where non-ASCII is
; permitted.  That command-context restriction belongs to the NNTP command
; boundary.  This generic RFC 3977 section 4 matcher does not strip or invent a
; BOM: U+FEFF is a valid non-ASCII wildmat-exact and matches only itself.

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
(defun fn-wildmat-at-mostp (xs bound) (fn-cbor-at-mostp xs bound))

(defun fn-wildmat-ok (value) (list :ok value))
(defun fn-wildmat-error (reason) (list :error reason))
(defun fn-wildmat-result-okp (result)
  (and (consp result) (equal (car result) :ok)))
(defun fn-wildmat-result-value (result) (car (cdr result)))

; A UTF-8 step includes its unconsumed input so decoding can be structural and
; does not need indexing or an unbounded numeric conversion.
(defun fn-wildmat-utf8-ok (codepoint rest) (list :ok codepoint rest))
(defun fn-wildmat-utf8-rest (result) (car (cdr (cdr result))))

(defun fn-wildmat-utf8-tailp (byte)
  (and (integerp byte) (<= 128 byte) (<= byte 191)))

(defun fn-wildmat-utf8-2p (xs)
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
  (+ (* 64 (- (car xs) 192))
     (- (car (cdr xs)) 128)))

(defun fn-wildmat-utf8-3-value (xs)
  (+ (* 4096 (- (car xs) 224))
     (* 64 (- (car (cdr xs)) 128))
     (- (car (cdr (cdr xs))) 128)))

(defun fn-wildmat-utf8-4-value (xs)
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
  (declare (xargs :measure (acl2-count octets)))
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

; -----------------------------------------------------------------------------
; RFC grammar parser

(defun fn-wildmat-exactp (codepoint)
  (or (and (natp codepoint) (<= 128 codepoint))
      (and (integerp codepoint) (<= 34 codepoint) (<= codepoint 41))
      (equal codepoint 43)
      (and (integerp codepoint) (<= 45 codepoint) (<= codepoint 62))
      (and (integerp codepoint) (<= 64 codepoint) (<= codepoint 90))
      (and (integerp codepoint) (<= 94 codepoint) (<= codepoint 126))))

(defun fn-wildmat-itemp (codepoint)
  (or (fn-wildmat-exactp codepoint)
      (equal codepoint 42)
      (equal codepoint 63)))

(defun fn-wildmat-items-p (items)
  (if (consp items)
      (and (fn-wildmat-itemp (car items))
           (fn-wildmat-items-p (cdr items)))
    (null items)))

(defun fn-wildmat-make-pattern (positivep items)
  (list (if positivep :positive :negative) items))
(defun fn-wildmat-pattern-sign (pattern) (car pattern))
(defun fn-wildmat-pattern-items (pattern) (car (cdr pattern)))
(defun fn-wildmat-pattern-positivep (pattern)
  (equal (fn-wildmat-pattern-sign pattern) :positive))
(defun fn-wildmat-patternp (pattern)
  (and (true-listp pattern)
       (equal (len pattern) 2)
       (or (equal (fn-wildmat-pattern-sign pattern) :positive)
           (equal (fn-wildmat-pattern-sign pattern) :negative))
       (consp (fn-wildmat-pattern-items pattern))
       (fn-wildmat-items-p (fn-wildmat-pattern-items pattern))))
(defun fn-wildmat-pattern-listp (patterns)
  (if (consp patterns)
      (and (fn-wildmat-patternp (car patterns))
           (fn-wildmat-pattern-listp (cdr patterns)))
    (null patterns)))
(defun fn-wildmat-parsedp (patterns)
  (and (consp patterns) (fn-wildmat-pattern-listp patterns)))

; Scan one nonempty pattern.  The result is (:end items), (:more items rest),
; or an error.  The parser only ever calls this after the optional negation
; marker has been consumed, so `!` cannot be an item in any position.
(defun fn-wildmat-scan-pattern (codepoints items-rev)
  (declare (xargs :measure (acl2-count codepoints)))
  (if (consp codepoints)
      (if (equal (car codepoints) 44)
          (if (consp items-rev)
              (list :more (reverse items-rev) (cdr codepoints))
            (fn-wildmat-error :syntax))
        (if (fn-wildmat-itemp (car codepoints))
            (fn-wildmat-scan-pattern (cdr codepoints)
                                      (cons (car codepoints) items-rev))
          (fn-wildmat-error :syntax)))
    (if (consp items-rev)
        (list :end (reverse items-rev))
      (fn-wildmat-error :syntax))))

(defun fn-wildmat-scan-endp (scan)
  (and (consp scan) (equal (car scan) :end)))
(defun fn-wildmat-scan-morep (scan)
  (and (consp scan) (equal (car scan) :more)))
(defun fn-wildmat-scan-items (scan) (car (cdr scan)))
(defun fn-wildmat-scan-rest (scan) (car (cdr (cdr scan))))

(defun fn-wildmat-parse-one (codepoints positivep fuel)
  ; Every recursive call follows a nonempty constituent and one comma.  Fuel
  ; makes that finite grammar recursion explicit to ACL2 without relying on a
  ; theorem about the scanner's returned suffix.  The public entry supplies the
  ; fixed input bound, so valid inputs cannot exhaust it.
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (fn-wildmat-error :limit)
    (let ((scan (fn-wildmat-scan-pattern codepoints nil)))
      (if (fn-wildmat-scan-endp scan)
          (fn-wildmat-ok
           (list (fn-wildmat-make-pattern positivep
                                          (fn-wildmat-scan-items scan))))
        (if (fn-wildmat-scan-morep scan)
            (let* ((rest (fn-wildmat-scan-rest scan))
                   (negativep (and (consp rest) (equal (car rest) 33)))
                   (following (fn-wildmat-parse-one
                               (if negativep (cdr rest) rest)
                               (if negativep nil t)
                               (1- fuel))))
              (if (fn-wildmat-result-okp following)
                  (fn-wildmat-ok
                   (cons (fn-wildmat-make-pattern positivep
                                                  (fn-wildmat-scan-items scan))
                         (fn-wildmat-result-value following)))
                following))
          (fn-wildmat-error :syntax))))))

(defun fn-wildmat-parse-codepoints (codepoints)
  (fn-wildmat-parse-one codepoints t *fn-wildmat-max-octets*))

(defun fn-wildmat-parse (octets)
  (let ((decoded (fn-wildmat-decode octets)))
    (if (fn-wildmat-result-okp decoded)
        (fn-wildmat-parse-codepoints (fn-wildmat-result-value decoded))
      decoded)))

; -----------------------------------------------------------------------------
; Polynomial dynamic-programming matcher

; A row records the reachable consumed target prefixes after some pattern
; items.  Its length is one more than the target length.  Each item allocates
; one fresh row and scans the target once, so a pattern of m items and target of
; n code points takes O(m*n) list work rather than exponential star
; backtracking.  The 497-octet preflight bounds both dimensions in this profile.
(defun fn-wildmat-false-row (target)
  (if (consp target)
      (cons nil (fn-wildmat-false-row (cdr target)))
    nil))
(defun fn-wildmat-initial-row (target)
  (cons t (fn-wildmat-false-row target)))
(defun fn-wildmat-bool-or (left right)
  (if left t (if right t nil)))

(defun fn-wildmat-item-character-matchp (item codepoint)
  (if (equal item 63)
      t
    (if (fn-wildmat-exactp item)
        (if (equal item codepoint) t nil)
      nil)))

(defun fn-wildmat-step-character-aux (target previous item)
  (if (consp target)
      (cons (if (and (consp previous)
                     (fn-wildmat-item-character-matchp item (car target)))
                (if (car previous) t nil)
              nil)
            (fn-wildmat-step-character-aux (cdr target) (cdr previous) item))
    nil))

(defun fn-wildmat-step-character (target previous item)
  (cons nil (fn-wildmat-step-character-aux target previous item)))

; For a star, next[j] = previous[j] OR next[j-1].  `carry` is next[j-1], and
; the tail of previous starts at previous[j], making this a single row scan.
(defun fn-wildmat-step-star-aux (target previous-tail carry)
  (if (consp target)
      (let ((next (fn-wildmat-bool-or (car previous-tail) carry)))
        (cons next (fn-wildmat-step-star-aux (cdr target)
                                             (cdr previous-tail) next)))
    nil))

(defun fn-wildmat-step-star (target previous)
  (cons (car previous)
        (fn-wildmat-step-star-aux target (cdr previous) (car previous))))

(defun fn-wildmat-pattern-row (items target row)
  (if (consp items)
      (fn-wildmat-pattern-row
       (cdr items) target
       (if (equal (car items) 42)
           (fn-wildmat-step-star target row)
         (fn-wildmat-step-character target row (car items))))
    row))

(defun fn-wildmat-row-last (row)
  (if (consp (cdr row))
      (fn-wildmat-row-last (cdr row))
    (car row)))

(defun fn-wildmat-pattern-matchp (items target)
  (if (fn-wildmat-row-last
       (fn-wildmat-pattern-row items target (fn-wildmat-initial-row target)))
      t
    nil))

; Search from the right recursively.  The returned pattern record is always a
; nonempty list, so NIL remains an unambiguous "no pattern matched" marker.
(defun fn-wildmat-rightmost-match (patterns target)
  (if (consp patterns)
      (let ((right (fn-wildmat-rightmost-match (cdr patterns) target)))
        (if right
            right
          (if (fn-wildmat-pattern-matchp (fn-wildmat-pattern-items (car patterns))
                                          target)
              (car patterns)
            nil)))
    nil))

(defun fn-wildmat-match-codepoints (patterns target)
  (let ((rightmost (fn-wildmat-rightmost-match patterns target)))
    (if rightmost
        (if (fn-wildmat-pattern-positivep rightmost) t nil)
      nil)))

(defun fn-wildmat-match-parsed (patterns target-octets)
  (if (not (fn-wildmat-parsedp patterns))
      (fn-wildmat-error :malformed-patterns)
    (let ((decoded-target (fn-wildmat-decode target-octets)))
      (if (fn-wildmat-result-okp decoded-target)
          (fn-wildmat-ok
           (fn-wildmat-match-codepoints patterns
                                        (fn-wildmat-result-value decoded-target)))
        decoded-target))))

(defun fn-wildmat-match (wildmat-octets target-octets)
  (let ((parsed (fn-wildmat-parse wildmat-octets)))
    (if (fn-wildmat-result-okp parsed)
        (fn-wildmat-match-parsed (fn-wildmat-result-value parsed) target-octets)
      parsed)))

; A small executable base fact for the RFC's anchored-star semantics.  This is
; deliberately modest: it does not claim the general DP work/correspondence
; proof, which remains future bounded-parser evidence.
(defthm fn-wildmat-star-matches-empty
  (equal (fn-wildmat-pattern-matchp '(42) nil) t))
