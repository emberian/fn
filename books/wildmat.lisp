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

; -----------------------------------------------------------------------------
; RFC grammar parser

; RFC 3977 section 4.1's `<wildmat-exact>`, verbatim: %x22-29 / %x2B /
; %x2D-3E / %x40-5A / %x5E-7E / UTF8-non-ascii, "exclude ! * , ? [ \ ]".
; This is the NEWSGROUP-NAME profile and nothing widens it: section 9.8 reads
; it as `newsgroup-name = 1*wildmat-exact`.
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

; -----------------------------------------------------------------------------
; The header-value profile (decision D19, planning/decisions.md)
;
; RFC 3977 section 4.1 justifies its exclusions with "This should not be a
; problem, since these characters cannot occur in newsgroup names, which is
; the only current use of wildmats."  RFC 2980 section 2.9's XPAT is the other
; use: it matches a HEADER VALUE, which is prose, contains SP, and routinely
; contains `[' and `]'.  Section 2.9 also says "If there are additional
; arguments the are joined together separated by a single space to form one
; complete pattern", so a multi-token XPAT pattern ALWAYS carries an SP.
; Section 4.3 licenses the widening explicitly: "An NNTP server or extension
; MAY extend the syntax or semantics of wildmats provided that all wildmats
; that meet the requirements of Section 4.1 have the meaning ascribed to them
; by Section 4.2."
;
; The profile is one rule: a pattern is a fragment of a command line, so every
; printable US-ASCII character, SP, and every UTF-8 non-ASCII character is a
; literal, less the four wildmat metacharacters `!' (%x21), `*' (%x2A),
; `,' (%x2C) and `?' (%x3F).  Controls and DEL stay out, as they are out of
; section 4.1.  Against `fn-wildmat-exactp' that is exactly four more code
; points: %x20 SP, %x5B `[', %x5C `\' and %x5D `]'.
;
; The cost is named in D19: section 4.1 omitted `[', `\' and `]' because "A
; future extension to this specification may provide semantics for these
; characters".  Reading them as literals in the header profile spends that
; reserved syntax there.  It is spent knowingly: `[PATCH]' in a Subject is the
; ordinary case and refusing it is the same defect as refusing SP, and section
; 4.1 conformance is untouched either way because no section 4.1 wildmat can
; contain them.
(defun fn-wildmat-text-exactp (codepoint)
  (or (and (natp codepoint) (<= 128 codepoint))
      (equal codepoint 32)
      (and (integerp codepoint) (<= 34 codepoint) (<= codepoint 41))
      (equal codepoint 43)
      (and (integerp codepoint) (<= 45 codepoint) (<= codepoint 62))
      (and (integerp codepoint) (<= 64 codepoint) (<= codepoint 126))))

(defun fn-wildmat-text-itemp (codepoint)
  (or (fn-wildmat-text-exactp codepoint)
      (equal codepoint 42)
      (equal codepoint 63)))

(defun fn-wildmat-text-items-p (items)
  (if (consp items)
      (and (fn-wildmat-text-itemp (car items))
           (fn-wildmat-text-items-p (cdr items)))
    (null items)))

; The set of code points a section 4.1 `wildmat' production can contain: an
; item, the separating comma, or the negation marker.  `fn-wildmat-parse'
; tests this before scanning, which is how the newsgroup-name entry keeps
; section 4.1 exactly while sharing one scanner with the header profile.
(defun fn-wildmat-rfc3977-codepointp (codepoint)
  (or (fn-wildmat-itemp codepoint)
      (equal codepoint 44)
      (equal codepoint 33)))

(defun fn-wildmat-rfc3977-codepointsp (codepoints)
  (if (consp codepoints)
      (and (fn-wildmat-rfc3977-codepointp (car codepoints))
           (fn-wildmat-rfc3977-codepointsp (cdr codepoints)))
    (null codepoints)))

(defun fn-wildmat-make-pattern (positivep items)
  (list (if positivep :positive :negative) items))
(defun fn-wildmat-pattern-sign (pattern)
  (declare (xargs :guard (true-listp pattern) :verify-guards nil))
  (car pattern))
(defun fn-wildmat-pattern-items (pattern)
  (declare (xargs :guard (true-listp pattern) :verify-guards nil))
  (car (cdr pattern)))
(defun fn-wildmat-pattern-positivep (pattern)
  (declare (xargs :guard (true-listp pattern) :verify-guards nil))
  (equal (fn-wildmat-pattern-sign pattern) :positive))
; RECORD SHAPE, not grammar conformance.  These recognize any pattern record
; either entry point can produce, so they carry the WIDER item set; every
; theorem that hypothesises one is thereby stronger than it was.  The section
; 4.1-profiled shape is `fn-wildmat-rfc3977-pattern-listp' below, and
; `fn-wildmat-parse-yields-rfc3977-patterns' is what says the newsgroup-name
; entry still produces it.
(defun fn-wildmat-patternp (pattern)
  (and (true-listp pattern)
       (equal (len pattern) 2)
       (or (equal (fn-wildmat-pattern-sign pattern) :positive)
           (equal (fn-wildmat-pattern-sign pattern) :negative))
       (consp (fn-wildmat-pattern-items pattern))
       (fn-wildmat-text-items-p (fn-wildmat-pattern-items pattern))))
(defun fn-wildmat-pattern-listp (patterns)
  (if (consp patterns)
      (and (fn-wildmat-patternp (car patterns))
           (fn-wildmat-pattern-listp (cdr patterns)))
    (null patterns)))
(defun fn-wildmat-rfc3977-patternp (pattern)
  (and (fn-wildmat-patternp pattern)
       (fn-wildmat-items-p (fn-wildmat-pattern-items pattern))))
(defun fn-wildmat-rfc3977-pattern-listp (patterns)
  (if (consp patterns)
      (and (fn-wildmat-rfc3977-patternp (car patterns))
           (fn-wildmat-rfc3977-pattern-listp (cdr patterns)))
    (null patterns)))
(defun fn-wildmat-parsedp (patterns)
  (and (consp patterns) (fn-wildmat-pattern-listp patterns)))

; Scan one nonempty pattern.  The result is (:end items), (:more items rest),
; or an error.  The parser only ever calls this after the optional negation
; marker has been consumed, so `!` cannot be an item in any position.
(defun fn-wildmat-scan-pattern (codepoints items-rev)
  (declare (xargs :measure (acl2-count codepoints)
                  :guard (true-listp items-rev)
                  :verify-guards nil))
  (if (consp codepoints)
      (if (equal (car codepoints) 44)
          (if (consp items-rev)
              (list :more (reverse items-rev) (cdr codepoints))
            (fn-wildmat-error :syntax))
        (if (fn-wildmat-text-itemp (car codepoints))
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
(defun fn-wildmat-scan-items (scan)
  (declare (xargs :guard (true-listp scan) :verify-guards nil))
  (car (cdr scan)))
(defun fn-wildmat-scan-rest (scan)
  (declare (xargs :guard (true-listp scan) :verify-guards nil))
  (car (cdr (cdr scan))))

(defun fn-wildmat-parse-one (codepoints positivep fuel)
  ; Every recursive call follows a nonempty constituent and one comma.  Fuel
  ; makes that finite grammar recursion explicit to ACL2 without relying on a
  ; theorem about the scanner's returned suffix.  The public entry supplies the
  ; fixed input bound, so valid inputs cannot exhaust it.
  (declare (xargs :measure (nfix fuel)
                  :guard (natp fuel)
                  :verify-guards nil))
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

; THE NEWSGROUP-NAME ENTRY.  RFC 3977 section 4.1 governs here and nothing
; loosens: the precheck refuses any code point outside the section 4.1
; `wildmat' production before the shared scanner runs, so this function
; accepts and rejects exactly the octet lists it accepted and rejected before
; the header profile existed, with the same `:error' reason in every case.
; Callers: books/peer-config.lisp:134, books/peer-inbound.lisp:134 (through
; fn-wildmat-match), books/owner-feed.lisp:703 (likewise),
; books/nntp-responses.lisp:212, :235 and :1684.
(defun fn-wildmat-parse (octets)
  (let ((decoded (fn-wildmat-decode octets)))
    (if (fn-wildmat-result-okp decoded)
        (if (fn-wildmat-rfc3977-codepointsp (fn-wildmat-result-value decoded))
            (fn-wildmat-parse-codepoints (fn-wildmat-result-value decoded))
          (fn-wildmat-error :syntax))
      decoded)))

; THE HEADER-VALUE ENTRY (D19).  Same grammar structure -- comma alternation,
; post-comma `!', `*' and `?' -- over the wider literal set.  One caller:
; fn-nntp-xpat-response, books/nntp-responses.lisp:1620, which is the line
; RFC 2980 section 2.9 hands the joined pattern to.
(defun fn-wildmat-parse-text (octets)
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

; Before D19 this read `(fn-wildmat-exactp item)'.  It reads the header-value
; set now, which is what makes a matched SP a match at all.  It is unchanged
; on every section 4.1 item, and
; `fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items' below states
; that with the previous body verbatim as its right-hand side.
(defun fn-wildmat-item-character-matchp (item codepoint)
  (if (equal item 63)
      t
    (if (fn-wildmat-text-exactp item)
        (if (equal item codepoint) t nil)
      nil)))

(defun fn-wildmat-step-character-aux (target previous item)
  (declare (xargs :guard (and (true-listp target)
                              (true-listp previous)
                              (equal (len previous) (1+ (len target))))
                  :verify-guards nil))
  (if (consp target)
      (cons (if (and (consp previous)
                     (fn-wildmat-item-character-matchp item (car target)))
                (if (car previous) t nil)
              nil)
            (fn-wildmat-step-character-aux (cdr target) (cdr previous) item))
    nil))

(defun fn-wildmat-step-character (target previous item)
  (declare (xargs :guard (and (true-listp target)
                              (true-listp previous)
                              (equal (len previous) (1+ (len target))))
                  :verify-guards nil))
  (cons nil (fn-wildmat-step-character-aux target previous item)))

; For a star, next[j] = previous[j] OR next[j-1].  `carry` is next[j-1], and
; the tail of previous starts at previous[j], making this a single row scan.
(defun fn-wildmat-step-star-aux (target previous-tail carry)
  (declare (xargs :guard (and (true-listp target)
                              (true-listp previous-tail)
                              (equal (len previous-tail) (len target)))
                  :verify-guards nil))
  (if (consp target)
      (let ((next (fn-wildmat-bool-or (car previous-tail) carry)))
        (cons next (fn-wildmat-step-star-aux (cdr target)
                                             (cdr previous-tail) next)))
    nil))

(defun fn-wildmat-step-star (target previous)
  (declare (xargs :guard (and (true-listp target)
                              (true-listp previous)
                              (equal (len previous) (1+ (len target))))
                  :verify-guards nil))
  (cons (car previous)
        (fn-wildmat-step-star-aux target (cdr previous) (car previous))))

(defun fn-wildmat-pattern-row (items target row)
  (declare (xargs :guard (and (true-listp items)
                              (true-listp target)
                              (true-listp row)
                              (equal (len row) (1+ (len target))))
                  :verify-guards nil))
  (if (consp items)
      (fn-wildmat-pattern-row
       (cdr items) target
       (if (equal (car items) 42)
           (fn-wildmat-step-star target row)
         (fn-wildmat-step-character target row (car items))))
    row))

(defun fn-wildmat-row-last (row)
  (declare (xargs :guard (and (true-listp row) (consp row))
                  :verify-guards nil))
  (if (consp (cdr row))
      (fn-wildmat-row-last (cdr row))
    (car row)))

(defun fn-wildmat-pattern-matchp (items target)
  (declare (xargs :guard (and (true-listp items) (true-listp target))
                  :verify-guards nil))
  (if (fn-wildmat-row-last
       (fn-wildmat-pattern-row items target (fn-wildmat-initial-row target)))
      t
    nil))

; Search from the right recursively.  The returned pattern record is always a
; nonempty list, so NIL remains an unambiguous "no pattern matched" marker.
(defun fn-wildmat-rightmost-match (patterns target)
  (declare (xargs :guard (and (fn-wildmat-pattern-listp patterns)
                              (true-listp target))
                  :verify-guards nil))
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
  (declare (xargs :guard (and (fn-wildmat-pattern-listp patterns)
                              (true-listp target))
                  :verify-guards nil))
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

; -----------------------------------------------------------------------------
; How the two profiles relate, and why the newsgroup-name path does not move
;
; D19's whole safety argument is these three facts: the header-value profile
; CONTAINS section 4.1's; the two agree on every section 4.1 item, so the
; widened matcher test is the old one there; and `fn-wildmat-parse' therefore
; behaves as it did.  RFC 3977 section 4.3 asks for exactly this -- "all
; wildmats that meet the requirements of Section 4.1 have the meaning ascribed
; to them by Section 4.2".

(defthm fn-wildmat-exactp-implies-text-exactp
  (implies (fn-wildmat-exactp codepoint)
           (fn-wildmat-text-exactp codepoint))
  :hints (("Goal" :in-theory (enable fn-wildmat-exactp
                                      fn-wildmat-text-exactp))))

(defthm fn-wildmat-itemp-implies-text-itemp
  (implies (fn-wildmat-itemp codepoint)
           (fn-wildmat-text-itemp codepoint))
  :hints (("Goal" :in-theory (enable fn-wildmat-itemp
                                      fn-wildmat-text-itemp))))

(defthm fn-wildmat-items-p-implies-text-items-p
  (implies (fn-wildmat-items-p items)
           (fn-wildmat-text-items-p items))
  :hints (("Goal" :induct (fn-wildmat-items-p items)
           :in-theory (enable fn-wildmat-items-p
                               fn-wildmat-text-items-p))))

(defthm fn-wildmat-rfc3977-pattern-listp-implies-pattern-listp
  (implies (fn-wildmat-rfc3977-pattern-listp patterns)
           (fn-wildmat-pattern-listp patterns))
  :hints (("Goal" :induct (fn-wildmat-rfc3977-pattern-listp patterns)
           :in-theory (enable fn-wildmat-rfc3977-pattern-listp
                               fn-wildmat-rfc3977-patternp
                               fn-wildmat-pattern-listp))))

; The containment is STRICT and the four extra code points are named, so the
; inclusion above is not the inclusion of a set in itself.
(defthm fn-wildmat-text-exactp-is-strictly-wider
  (and (fn-wildmat-text-exactp 32)
       (fn-wildmat-text-exactp 91)
       (fn-wildmat-text-exactp 92)
       (fn-wildmat-text-exactp 93)
       (not (fn-wildmat-exactp 32))
       (not (fn-wildmat-exactp 91))
       (not (fn-wildmat-exactp 92))
       (not (fn-wildmat-exactp 93)))
  :rule-classes nil)

; ... and it adds nothing else: the four are the whole difference, so the
; header profile is not a licence to accept a control octet, DEL, or any of
; the four metacharacters.
(defthm fn-wildmat-text-exactp-adds-exactly-four-code-points
  (implies (and (not (equal codepoint 32))
                (not (equal codepoint 91))
                (not (equal codepoint 92))
                (not (equal codepoint 93)))
           (equal (fn-wildmat-text-exactp codepoint)
                  (fn-wildmat-exactp codepoint)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-wildmat-exactp
                                      fn-wildmat-text-exactp))))

; THE CONSERVATION KEYSTONE.  The right-hand side is the body this function
; had before D19, verbatim.  Every item of a pattern `fn-wildmat-parse'
; produced satisfies `fn-wildmat-itemp', so no newsgroup-name match changed.
; `fn-wildmat-pattern-row' dispatches 42 to the star step and never reaches
; this function with it, but the hypothesis is not needed: 42 is in neither
; set, so the two sides agree there too.
(defthm fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items
  (implies (fn-wildmat-itemp item)
           (equal (fn-wildmat-item-character-matchp item codepoint)
                  (if (equal item 63)
                      t
                    (if (fn-wildmat-exactp item)
                        (if (equal item codepoint) t nil)
                      nil))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-wildmat-item-character-matchp
                                      fn-wildmat-itemp
                                      fn-wildmat-exactp
                                      fn-wildmat-text-exactp))))

; A small executable base fact for the RFC's anchored-star semantics.  This is
; deliberately modest: it does not claim the general DP work/correspondence
; proof, which remains future bounded-parser evidence.
(defthm fn-wildmat-star-matches-empty
  (equal (fn-wildmat-pattern-matchp '(42) nil) t))

; Guard support for the row-shape contract.  These are ordinary ACL2
; theorems about the unchanged logical DP definitions.
(defthm fn-wildmat-guard-step-character-aux-length
  (equal (len (fn-wildmat-step-character-aux target previous item))
         (len target))
  :hints (("Goal" :induct (fn-wildmat-step-character-aux target previous item)
           :in-theory (enable fn-wildmat-step-character-aux))))

(defthm fn-wildmat-guard-step-character-length
  (equal (len (fn-wildmat-step-character target previous item))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wildmat-step-character))))

(defthm fn-wildmat-guard-step-star-aux-length
  (equal (len (fn-wildmat-step-star-aux target previous-tail carry))
         (len target))
  :hints (("Goal" :induct (fn-wildmat-step-star-aux target previous-tail carry)
           :in-theory (enable fn-wildmat-step-star-aux))))

(defthm fn-wildmat-guard-step-star-length
  (equal (len (fn-wildmat-step-star target previous))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wildmat-step-star))))

(defthm fn-wildmat-guard-pattern-row-length
  (implies (equal (len row) (1+ (len target)))
           (equal (len (fn-wildmat-pattern-row items target row))
                  (1+ (len target))))
  :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
           :in-theory (enable fn-wildmat-pattern-row))))

(defthm fn-wildmat-guard-items-p-true-listp
  (implies (fn-wildmat-items-p items)
           (true-listp items))
  :hints (("Goal" :induct (fn-wildmat-items-p items)
           :in-theory (enable fn-wildmat-items-p))))

(defthm fn-wildmat-guard-text-items-p-true-listp
  (implies (fn-wildmat-text-items-p items)
           (true-listp items))
  :hints (("Goal" :induct (fn-wildmat-text-items-p items)
           :in-theory (enable fn-wildmat-text-items-p))))

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
(verify-guards fn-wildmat-exactp)
(verify-guards fn-wildmat-itemp)
(verify-guards fn-wildmat-items-p)
(verify-guards fn-wildmat-text-exactp)
(verify-guards fn-wildmat-text-itemp)
(verify-guards fn-wildmat-text-items-p)
(verify-guards fn-wildmat-rfc3977-codepointp)
(verify-guards fn-wildmat-rfc3977-codepointsp)
(verify-guards fn-wildmat-make-pattern)
(verify-guards fn-wildmat-pattern-sign)
(verify-guards fn-wildmat-pattern-items)
(verify-guards fn-wildmat-pattern-positivep)
(verify-guards fn-wildmat-patternp)
(verify-guards fn-wildmat-pattern-listp)
(verify-guards fn-wildmat-rfc3977-patternp)
(verify-guards fn-wildmat-rfc3977-pattern-listp)
(verify-guards fn-wildmat-parsedp)
(verify-guards fn-wildmat-scan-pattern)
(verify-guards fn-wildmat-scan-endp)
(verify-guards fn-wildmat-scan-morep)
(verify-guards fn-wildmat-scan-items)
(verify-guards fn-wildmat-scan-rest)
(verify-guards fn-wildmat-parse-one)
(verify-guards fn-wildmat-parse-codepoints)
(verify-guards fn-wildmat-parse)
(verify-guards fn-wildmat-parse-text)
(verify-guards fn-wildmat-false-row)
(verify-guards fn-wildmat-initial-row)
(verify-guards fn-wildmat-bool-or)
(verify-guards fn-wildmat-item-character-matchp)
(verify-guards fn-wildmat-step-character-aux)
(verify-guards fn-wildmat-step-character)
(verify-guards fn-wildmat-step-star-aux)
(verify-guards fn-wildmat-step-star)
(verify-guards fn-wildmat-pattern-row)
(verify-guards fn-wildmat-row-last)
(verify-guards fn-wildmat-pattern-matchp)
(verify-guards fn-wildmat-rightmost-match)
(verify-guards fn-wildmat-match-codepoints)
(verify-guards fn-wildmat-match-parsed
  :hints (("Goal"
           :use ((:instance fn-wildmat-guard-decode-success-true-listp
                            (octets target-octets))))))
(verify-guards fn-wildmat-match)

; -----------------------------------------------------------------------------
; Export theory.
;
; `fn-wildmat-guard-items-p-true-listp` and
; `fn-wildmat-guard-octet-listp-true-listp` are two limbs of the
; `true-listp`-backchaining fan-out measured in `books/nntp-invariants.lisp`
; and `books/nntp-effects.lisp` (each `(true-listp X)` they meet opens a
; recursive recognizer on a bare variable); `fn-wildmat-guard-pattern-row-
; length` is the `len`-backchaining rule `tools/ledger.py --check` reports at
; `books/wildmat.lisp:462`.  All three exist to discharge guards in this book
; and are withdrawn here under one name.  The type-reasoning role of the first
; two is exported back as `:forward-chaining` shape facts
; (`docs/proof-style.md` section 1).

(defthm fn-wildmat-items-p-forward-shape
  (implies (fn-wildmat-items-p items)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-wildmat-guard-items-p-true-listp)))

(defthm fn-wildmat-text-items-p-forward-shape
  (implies (fn-wildmat-text-items-p items)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-wildmat-guard-text-items-p-true-listp)))

(defthm fn-wildmat-octet-listp-forward-shape
  (implies (fn-wildmat-octet-listp octets)
           (true-listp octets))
  :rule-classes :forward-chaining
  :hints (("Goal" :by fn-wildmat-guard-octet-listp-true-listp)))

(deftheory fn-wildmat-guard-backchaining
  '(fn-wildmat-guard-items-p-true-listp
    fn-wildmat-guard-text-items-p-true-listp
    fn-wildmat-guard-octet-listp-true-listp
    fn-wildmat-guard-pattern-row-length))

(in-theory (disable fn-wildmat-guard-backchaining))
