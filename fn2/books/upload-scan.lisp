; The upload's header scan and the article's definite verdict (layer D,
; quest D4 1/n; fn2/docs/d-machines-nntp.md section 14.3.2). A library over
; the pool, like conn-answer.lisp: the upload machine calls it through one
; declared operation, and tests/upload-scan-unit.lisp drives it on a local
; pool. The article is the dot-unstuffed source the poster sent, CRLF line
; ends, in the upload's first chunk; the header section must lie in that
; chunk (a profile check: the chunk is at least the header cap).
;
; The scan is a bounded continuation over physical header lines. Its state
; is twelve scalars (the upload row's fields): OFF, the next line's first
; octet; FIELD, the open field's code; VISIBLE, whether the open field has a
; visible octet yet; FIELDS and LINES, the counts; SEEN, the field bits; and
; the exact value ranges of the first Message-ID, Newsgroups and Path
; fields. Header syntax is fn1's (specs/article-parser.md, "Header syntax"):
; field-name ":" (WSP body / ""), continuations start with WSP, header
; octets are SP, HTAB or VCHAR, a field closes only once its value holds a
; VCHAR, at most 998 octets per physical line, and the three header limits.
; The verdict applies the definite refusals in the order of H's model
; (fn2/tests/model/nntp_model.py, _article_block); the identity, group and
; clock checks after it are the transaction's.
(in-package "ACL2")
(include-book "grammar")
(fn2-book-layer :d)

; The header limits (specs/article-parser.md's defaults; the store profile's
; fields 13-15 in fn1, profile keys here once D7's configuration lands).
(defconst *fn2-upload-header-octets* 16384)
(defconst *fn2-upload-header-lines* 256)
(defconst *fn2-upload-header-fields* 64)
; RFC 5322 section 2.1.1: a physical line is at most 998 octets before CRLF.
(defconst *fn2-upload-line-max* 998)
; The scan never examines more than one line's worth past what remains of
; its budget: a call scans a further line only while this much is left.
(defconst *fn2-upload-line-cost* (+ 2 *fn2-upload-line-max*))

; The fields whose values or presence the verdict and the transaction read,
; by code (their position here); every other field is *fn2-upload-field-other*.
(defconst *fn2-upload-field-names*
  '("MESSAGE-ID" "NEWSGROUPS" "PATH" "FROM" "SUBJECT" "DATE" "XREF"
    "INJECTION-DATE" "INJECTION-INFO" "APPROVED" "CONTROL"))
(defconst *fn2-upload-field-mid* 0)
(defconst *fn2-upload-field-ng* 1)
(defconst *fn2-upload-field-path* 2)
(defconst *fn2-upload-field-from* 3)
(defconst *fn2-upload-field-subject* 4)
(defconst *fn2-upload-field-date* 5)
(defconst *fn2-upload-field-xref* 6)
(defconst *fn2-upload-field-injection-date* 7)
(defconst *fn2-upload-field-injection-info* 8)
(defconst *fn2-upload-field-approved* 9)
(defconst *fn2-upload-field-control* 10)
(defconst *fn2-upload-field-other* 11)
; No field is open (before the first field line).
(defconst *fn2-upload-field-none* 12)
; SEEN's bits: bit F once field F is seen, bit (16 + F) once it is seen
; twice; bit 12 when the first Message-ID is folded, bit 13 when the first
; Path is.
(defconst *fn2-upload-seen-mid-folded* 12)
(defconst *fn2-upload-seen-path-folded* 13)
(defconst *fn2-upload-seen-dup* 16)

(defun fn2-upload-bit (seen b)
  (declare (xargs :guard (and (natp seen) (natp b))))
  (logbitp b seen))
(defun fn2-upload-set-bit (seen b)
  (declare (xargs :guard (and (natp seen) (natp b) (< b 32))))
  (if (logbitp b (nfix seen)) (nfix seen) (+ (nfix seen) (expt 2 (nfix b)))))
(defthm fn2-upload-set-bit-natp (natp (fn2-upload-set-bit seen b)) :rule-classes :type-prescription)
(in-theory (disable fn2-upload-set-bit))

; ------------------------------------------------------------------------
; Octet classes over a range of the slot.
(defun fn2-upload-wspp (b) (declare (xargs :guard (natp b))) (or (= b 32) (= b 9)))
(defun fn2-upload-vcharp (b) (declare (xargs :guard (natp b))) (and (<= 33 b) (<= b 126)))
(defun fn2-upload-ftextp (b) (declare (xargs :guard (natp b))) (and (fn2-upload-vcharp b) (not (= b 58))))

; Every octet of [i, i+left) is SP, HTAB or VCHAR: (mv ok visible), VISIBLE
; or'ed with whether any is a VCHAR.
(defun fn2-upload-octets (left i visible slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (mv t visible)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (not (and ok (or (fn2-upload-wspp b) (fn2-upload-vcharp b)))) (mv nil visible)
        (fn2-upload-octets (- left 1) (+ 1 i) (or visible (fn2-upload-vcharp b))
                           slot gen okind oslot ogen fn2-pool)))))

; The colon ending a field name that starts at I within LEFT octets:
; (mv ok colon); OK only for a nonempty name of ftext octets.
(defun fn2-upload-name (left i start slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp start))))
  (if (zp left) (mv nil 0)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (cond ((not ok) (mv nil 0))
            ((= b 58) (mv (< start i) (nfix i)))
            ((fn2-upload-ftextp b) (fn2-upload-name (- left 1) (+ 1 i) start slot gen okind oslot ogen fn2-pool))
            (t (mv nil 0))))))
(defthm fn2-upload-name-natp (natp (mv-nth 1 (fn2-upload-name left i start slot gen okind oslot ogen fn2-pool)))
  :rule-classes :type-prescription)

; The code of the field named by [ns, ns+nl), compared case-insensitively.
(defun fn2-upload-field-code-loop (names k ns nl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (string-listp names) (natp k) (natp ns) (natp nl))))
  (cond ((atom names) *fn2-upload-field-other*)
        ((fn2-gram-match ns nl (car names) slot gen okind oslot ogen fn2-pool) (nfix k))
        (t (fn2-upload-field-code-loop (cdr names) (+ 1 (nfix k)) ns nl slot gen okind oslot ogen fn2-pool))))
(defthm fn2-upload-field-code-loop-bound
  (implies (and (natp k) (<= (+ k (len names)) *fn2-upload-field-other*))
           (and (natp (fn2-upload-field-code-loop names k ns nl slot gen okind oslot ogen fn2-pool))
                (<= (fn2-upload-field-code-loop names k ns nl slot gen okind oslot ogen fn2-pool)
                    *fn2-upload-field-other*)))
  :rule-classes ((:rewrite :corollary
                  (implies (and (natp k) (<= (+ k (len names)) *fn2-upload-field-other*))
                           (natp (fn2-upload-field-code-loop names k ns nl slot gen okind oslot ogen fn2-pool))))
                 (:linear :corollary
                  (implies (and (natp k) (<= (+ k (len names)) *fn2-upload-field-other*))
                           (<= (fn2-upload-field-code-loop names k ns nl slot gen okind oslot ogen fn2-pool)
                               *fn2-upload-field-other*)))))
(defun fn2-upload-field-code (ns nl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ns) (natp nl))))
  (fn2-upload-field-code-loop *fn2-upload-field-names* 0 ns nl slot gen okind oslot ogen fn2-pool))
(defthm fn2-upload-field-code-bound
  (and (natp (fn2-upload-field-code ns nl slot gen okind oslot ogen fn2-pool))
       (<= (fn2-upload-field-code ns nl slot gen okind oslot ogen fn2-pool) *fn2-upload-field-other*))
  :rule-classes ((:type-prescription :corollary (natp (fn2-upload-field-code ns nl slot gen okind oslot ogen fn2-pool)))
                 (:linear :corollary (<= (fn2-upload-field-code ns nl slot gen okind oslot ogen fn2-pool)
                                         *fn2-upload-field-other*))))
(in-theory (disable fn2-upload-field-code))

; ------------------------------------------------------------------------
; One physical header line at OFF. Returns (mv status off field visible
; fields lines seen mo ml no nl po pl cost): STATUS :line (a line consumed),
; :header-done (the blank line: OFF is the body's first octet), :more (no
; CRLF yet within the filled octets), or a refusal word (:malformed,
; :line-length, :header-fields, :header-lines, :header-octets). COST is
; the octets examined.
(in-theory (disable fn2-upload-octets fn2-upload-name fn2-upload-bit fn2-pool-scan fn2-gram-fill fn2-gram-match))
(defthm fn2-upload-octets-booleans
  (booleanp (mv-nth 0 (fn2-upload-octets left i visible slot gen okind oslot ogen fn2-pool)))
  :hints (("Goal" :in-theory (enable fn2-upload-octets)))
  :rule-classes :type-prescription)
(defmacro fn2-upload-line-mv (status off field visible fields lines seen mo ml no nl po pl cost)
  `(mv ,status ,off ,field ,visible ,fields ,lines ,seen ,mo ,ml ,no ,nl ,po ,pl ,cost))

(defun fn2-upload-line (off field visible fields lines seen mo ml no nl po pl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp off) (natp field) (natp fields) (natp lines)
                              (natp seen) (natp mo) (natp ml) (natp no) (natp nl) (natp po) (natp pl))
                  :guard-hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-compare fn2-gram-read
                                                            fn2-upload-field-code fn2-upload-set-bit)))))
  (b* ((nfill (fn2-gram-fill slot fn2-pool))
       (avail (if (< off nfill) (- nfill off) 0))
       (n (if (< avail *fn2-upload-line-cost*) avail *fn2-upload-line-cost*))
       ((mv code at) (if (zp n) (mv :ok 0)
                       (fn2-pool-scan slot gen off n *fn2-pool-scan-crlf* okind oslot ogen fn2-pool)))
       (at (nfix at))
       ((unless (eq code :ok)) (fn2-upload-line-mv :fault off field visible fields lines seen mo ml no nl po pl n))
       ((when (<= n at))
        ;; no CRLF among the n octets: a line past the cap is refused; else
        ;; wait for more octets
        (if (<= *fn2-upload-line-cost* avail)
            (fn2-upload-line-mv :line-length off field visible fields lines seen mo ml no nl po pl n)
          (fn2-upload-line-mv :more off field visible fields lines seen mo ml no nl po pl n)))
       (len at) (next (+ off len 2)) (cost (+ len 2))
       ((when (< *fn2-upload-line-max* len))
        (fn2-upload-line-mv :line-length off field visible fields lines seen mo ml no nl po pl cost))
       ((when (< *fn2-upload-header-octets* next))
        (fn2-upload-line-mv :header-octets off field visible fields lines seen mo ml no nl po pl cost))
       ;; a field closes only with a visible octet in its value
       (closed (or (equal field *fn2-upload-field-none*) visible))
       ((when (zp len))
        (if closed (fn2-upload-line-mv :header-done next *fn2-upload-field-none* nil fields lines seen mo ml no nl po pl cost)
          (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost)))
       (lines (+ 1 lines))
       ((when (< *fn2-upload-header-lines* lines))
        (fn2-upload-line-mv :header-lines off field visible fields lines seen mo ml no nl po pl cost))
       ((mv ok b) (fn2-gram-read slot gen off okind oslot ogen fn2-pool))
       ((unless ok) (fn2-upload-line-mv :fault off field visible fields lines seen mo ml no nl po pl cost)))
    (if (fn2-upload-wspp b)
        ;; a continuation of the open field
        (b* (((when (equal field *fn2-upload-field-none*))
              (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
             ((mv ok visible) (fn2-upload-octets len off visible slot gen okind oslot ogen fn2-pool))
             ((unless ok) (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
             (first (not (fn2-upload-bit seen (+ *fn2-upload-seen-dup* (min field 15)))))
             (seen (cond ((and first (equal field *fn2-upload-field-mid*))
                          (fn2-upload-set-bit seen *fn2-upload-seen-mid-folded*))
                         ((and first (equal field *fn2-upload-field-path*))
                          (fn2-upload-set-bit seen *fn2-upload-seen-path-folded*))
                         (t seen)))
             ;; the first Newsgroups' range covers its folded value
             (nl (if (and first (equal field *fn2-upload-field-ng*)) (- (+ off len) no) nl)))
          (fn2-upload-line-mv :line next field visible fields lines seen mo ml no (nfix nl) po pl cost))
      ;; a field line: the previous field must be closed
      (b* (((unless closed) (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
           (fields (+ 1 fields))
           ((when (< *fn2-upload-header-fields* fields))
            (fn2-upload-line-mv :header-fields off field visible fields lines seen mo ml no nl po pl cost))
           ((mv ok colon) (fn2-upload-name len off off slot gen okind oslot ogen fn2-pool))
           (colon (nfix colon))
           ((unless ok) (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
           (end (+ off len))
           ((mv ok2 b2) (if (< (+ 1 colon) end) (fn2-gram-read slot gen (+ 1 colon) okind oslot ogen fn2-pool) (mv t 32)))
           ((unless (and ok2 (fn2-upload-wspp b2)))
            (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
           (vlen (nfix (- end (+ 1 colon))))
           ((mv ok visible) (fn2-upload-octets vlen (+ 1 colon) nil slot gen okind oslot ogen fn2-pool))
           ((unless ok) (fn2-upload-line-mv :malformed off field visible fields lines seen mo ml no nl po pl cost))
           (code (fn2-upload-field-code off (nfix (- colon off)) slot gen okind oslot ogen fn2-pool))
           (again (and (< code *fn2-upload-field-other*) (fn2-upload-bit seen code)))
           (seen (cond ((not (< code *fn2-upload-field-other*)) seen)
                       (again (fn2-upload-set-bit seen (+ *fn2-upload-seen-dup* code)))
                       (t (fn2-upload-set-bit seen code))))
           ;; H's model strips one leading SP from a value (fields() in
           ;; nntp_model.py); the ranges are of that value
           (vstart (if (and (< (+ 1 colon) end) (= b2 32)) (+ 2 colon) (+ 1 colon)))
           (vl (nfix (- end vstart)))
           (first (not again)))
        (fn2-upload-line-mv :line next code visible fields lines seen
                            (if (and first (equal code *fn2-upload-field-mid*)) vstart mo)
                            (if (and first (equal code *fn2-upload-field-mid*)) vl ml)
                            (if (and first (equal code *fn2-upload-field-ng*)) vstart no)
                            (if (and first (equal code *fn2-upload-field-ng*)) vl nl)
                            (if (and first (equal code *fn2-upload-field-path*)) vstart po)
                            (if (and first (equal code *fn2-upload-field-path*)) vl pl)
                            cost)))))

(in-theory (disable fn2-upload-line))
; The scan: lines while at least a line's worth of BUDGET remains. Returns
; (mv status off field visible fields lines seen mo ml no nl po pl spent);
; STATUS :budget when the budget ran out between lines.
(defun fn2-upload-scan (budget off field visible fields lines seen mo ml no nl po pl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix budget)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp budget) (natp off) (natp field) (natp fields)
                              (natp lines) (natp seen) (natp mo) (natp ml) (natp no) (natp nl) (natp po) (natp pl))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn2-upload-line)))))
  (if (< (nfix budget) *fn2-upload-line-cost*)
      (fn2-upload-line-mv :budget off field visible fields lines seen mo ml no nl po pl 0)
    (b* (((mv status off2 field2 visible2 fields2 lines2 seen2 mo2 ml2 no2 nl2 po2 pl2 cost)
          (fn2-upload-line off field visible fields lines seen mo ml no nl po pl slot gen okind oslot ogen fn2-pool)))
      (if (and (eq status :line) (posp cost))
          (b* (((mv status off field visible fields lines seen mo ml no nl po pl spent)
                (fn2-upload-scan (- (nfix budget) (min cost (nfix budget))) (nfix off2) (nfix field2) visible2 (nfix fields2)
                                 (nfix lines2) (nfix seen2) (nfix mo2) (nfix ml2) (nfix no2) (nfix nl2) (nfix po2) (nfix pl2)
                                 slot gen okind oslot ogen fn2-pool)))
            (fn2-upload-line-mv status off field visible fields lines seen mo ml no nl po pl (+ cost (nfix spent))))
        (fn2-upload-line-mv status off2 field2 visible2 fields2 lines2 seen2 mo2 ml2 no2 nl2 po2 pl2 cost)))))

; ------------------------------------------------------------------------
; Message-ID syntax as the stored-article check reads it (H's model,
; stored_msgid): "<" dot-atom "@" (dot-atom / "[" dtext* "]") ">", at most
; 250 octets; atext is RFC 5322's.
(defun fn2-upload-atextp (b)
  (declare (xargs :guard (natp b)))
  (or (and (<= 65 b) (<= b 90)) (and (<= 97 b) (<= b 122)) (and (<= 48 b) (<= b 57))
      (member b '(33 35 36 37 38 39 42 43 45 47 61 63 94 95 96 123 124 125 126))))
; [i, i+left) is a dot-atom: atoms of atext joined by single dots. PREV is
; :start, :dot or :atext.
(defun fn2-upload-dot-atom (left i prev slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (eq prev :atext)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (cond ((not ok) nil)
            ((= b 46) (and (eq prev :atext) (fn2-upload-dot-atom (- left 1) (+ 1 i) :dot slot gen okind oslot ogen fn2-pool)))
            ((fn2-upload-atextp b) (fn2-upload-dot-atom (- left 1) (+ 1 i) :atext slot gen okind oslot ogen fn2-pool))
            (t nil)))))
(defun fn2-upload-dtext (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (and ok (or (and (<= 33 b) (<= b 61)) (and (<= 63 b) (<= b 90)) (and (<= 94 b) (<= b 126)))
           (fn2-upload-dtext (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool)))))
(defun fn2-upload-msgid-p (s l slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp l))))
  (b* (((unless (and (<= 5 l) (<= l 250))) nil)
       ((mv ok1 lt) (fn2-gram-read slot gen s okind oslot ogen fn2-pool))
       ((mv ok2 gt) (fn2-gram-read slot gen (+ s l -1) okind oslot ogen fn2-pool))
       ((unless (and ok1 ok2 (= lt 60) (= gt 62))) nil)
       ;; the left part is a dot-atom, so the first "@" splits
       ((mv found at) (fn2-gram-find (- l 2) (+ 1 s) 64 slot gen okind oslot ogen fn2-pool))
       ((unless (and found (< (+ 1 s) at) (< (+ 1 at) (+ s l -1)))) nil)
       ((unless (fn2-upload-dot-atom (- at (+ 1 s)) (+ 1 s) :start slot gen okind oslot ogen fn2-pool)) nil)
       (rs (+ 1 at)) (rl (- (+ s l -1) rs))
       ((mv ok3 open) (fn2-gram-read slot gen rs okind oslot ogen fn2-pool))
       ((mv ok4 close) (fn2-gram-read slot gen (+ rs rl -1) okind oslot ogen fn2-pool)))
    (and ok3 ok4
         (if (= open 91)
             (and (<= 2 rl) (= close 93) (fn2-upload-dtext (- rl 2) (+ 1 rs) slot gen okind oslot ogen fn2-pool))
           (fn2-upload-dot-atom rl rs :start slot gen okind oslot ogen fn2-pool)))))

; [s, s+l) with WSP trimmed from both ends: (mv s2 l2).
(defun fn2-upload-trim-left (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (mv (nfix i) 0)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (if (and ok (fn2-upload-wspp b)) (fn2-upload-trim-left (- left 1) (+ 1 i) slot gen okind oslot ogen fn2-pool)
        (mv (nfix i) (nfix left))))))
(defun fn2-upload-trim-right (l s slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix l)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp l) (natp s))))
  (if (zp l) 0
    (mv-let (ok b) (fn2-gram-read slot gen (+ s l -1) okind oslot ogen fn2-pool)
      (if (and ok (fn2-upload-wspp b)) (fn2-upload-trim-right (- l 1) s slot gen okind oslot ogen fn2-pool)
        (nfix l)))))
(defun fn2-upload-trim (s l slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp l))))
  (mv-let (s2 l2) (fn2-upload-trim-left l s slot gen okind oslot ogen fn2-pool)
    (mv s2 (fn2-upload-trim-right l2 s2 slot gen okind oslot ogen fn2-pool))))

; A Path value as H's model reads it ([^\s!]+(![^\s!]+)*): nonempty
; components without whitespace, joined by single "!".
(defun fn2-upload-path-loop (left i prev slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) (eq prev :text)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (cond ((not ok) nil)
            ((= b 33) (and (eq prev :text) (fn2-upload-path-loop (- left 1) (+ 1 i) :bang slot gen okind oslot ogen fn2-pool)))
            ((or (= b 32) (and (<= 9 b) (<= b 13))) nil)
            (t (fn2-upload-path-loop (- left 1) (+ 1 i) :text slot gen okind oslot ogen fn2-pool))))))
; Whether [s, s+l) contains "POSTED", case-insensitively (H's model:
; b"POSTED" in path.upper()).
(defun fn2-upload-posted (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (cond ((< (nfix left) 6) nil)
        ((fn2-gram-match i 6 "POSTED" slot gen okind oslot ogen fn2-pool) t)
        (t (fn2-upload-posted (- (nfix left) 1) (+ 1 (nfix i)) slot gen okind oslot ogen fn2-pool))))
(defun fn2-upload-path-ok (s l slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp l))))
  (and (fn2-upload-path-loop l s :start slot gen okind oslot ogen fn2-pool)
       (not (fn2-upload-posted l s slot gen okind oslot ogen fn2-pool))))

; ------------------------------------------------------------------------
; The definite verdict once the block's terminator is framed (H's model's
; order). RULE is :post, :ihave or :takethis; STATUS the scan's last status;
; LEN the source length and BOUND the article bound. For transit, the
; command's Message-ID is [cs, cs+cl) of CSLOT under (ck cs-owner cg).
; Returns (mv word injected): WORD :ok or the refusal; INJECTED, for POST,
; whether Xref or an Injection field is present (refused by the transaction
; after its group check, as the model orders it).
(defun fn2-upload-seen-p (seen f) (declare (xargs :guard (and (natp seen) (natp f)))) (fn2-upload-bit seen f))
(defun fn2-upload-dup-p (seen)
  (declare (xargs :guard (natp seen)))
  (or (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-from*))
      (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-subject*))
      (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-ng*))
      (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-mid*))
      (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-date*))
      (fn2-upload-bit seen (+ *fn2-upload-seen-dup* *fn2-upload-field-path*))))

(defun fn2-upload-verdict (rule status seen mo ml po pl len bound cslot cgen cs cl ck co cg slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp seen) (natp mo) (natp ml) (natp po) (natp pl)
                              (natp len) (natp bound) (natp cs) (natp cl))))
  (b* ((transit (not (eq rule :post)))
       (injected (and (not transit)
                      (or (fn2-upload-seen-p seen *fn2-upload-field-xref*)
                          (fn2-upload-seen-p seen *fn2-upload-field-injection-date*)
                          (fn2-upload-seen-p seen *fn2-upload-field-injection-info*))))
       ((when (< bound len)) (mv :too-large injected))
       ((when (member-eq status '(:malformed :line-length :header-fields :header-lines :header-octets)))
        (mv status injected))
       ;; no blank line before the terminator
       ((unless (eq status :header-done)) (mv :malformed injected))
       ((unless (and (fn2-upload-seen-p seen *fn2-upload-field-from*)
                     (fn2-upload-seen-p seen *fn2-upload-field-subject*)
                     (fn2-upload-seen-p seen *fn2-upload-field-ng*)))
        (mv :missing injected))
       ((when (and transit (not (and (fn2-upload-seen-p seen *fn2-upload-field-mid*)
                                     (fn2-upload-seen-p seen *fn2-upload-field-date*)
                                     (fn2-upload-seen-p seen *fn2-upload-field-path*)))))
        (mv :missing injected))
       ((when (fn2-upload-dup-p seen)) (mv :duplicate-field injected))
       ((when (and (not transit) (fn2-upload-seen-p seen *fn2-upload-field-path*)
                   (or (fn2-upload-seen-p seen *fn2-upload-seen-path-folded*)
                       (not (fn2-upload-path-ok po pl slot gen okind oslot ogen fn2-pool)))))
        (mv :path injected))
       ((mv ms mlen) (if (fn2-upload-seen-p seen *fn2-upload-field-mid*)
                         (fn2-upload-trim mo ml slot gen okind oslot ogen fn2-pool)
                       (mv mo 0)))
       ((when (and transit
                   (not (and (equal mlen cl)
                             (mv-let (code order at)
                               (fn2-pool-compare slot gen ms okind oslot ogen cslot cgen cs ck co cg mlen fn2-pool)
                               (declare (ignore at))
                               (and (eq code :ok) (eq order :equal)))))))
        (mv :mismatch injected))
       ((when (and (fn2-upload-seen-p seen *fn2-upload-field-mid*)
                   (or (fn2-upload-seen-p seen *fn2-upload-seen-mid-folded*)
                       (not (fn2-upload-msgid-p ms mlen slot gen okind oslot ogen fn2-pool)))))
        (mv :message-id injected)))
    (mv :ok injected)))

(verify-guards fn2-upload-scan)
(assert-event
 (fn2-assert-compliant-p
  '(fn2-upload-octets fn2-upload-name fn2-upload-field-code fn2-upload-line fn2-upload-scan
    fn2-upload-dot-atom fn2-upload-dtext fn2-upload-msgid-p fn2-upload-trim fn2-upload-path-ok
    fn2-upload-verdict)
  (w state)))
