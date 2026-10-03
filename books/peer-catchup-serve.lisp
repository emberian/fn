; fn: the serving half of peer catch-up (PRF-325, NNT-053;
; specs/peering.md "Catching up from a peer").
;
; A node that is new, or has been away, asks a peer for the peer's articles
; as a stream of batches instead of one NEWNEWS listing and one ARTICLE per
; Message-ID.  The command is the private extension (RFC 3977 section 3.3.1:
; an X-prefixed keyword)
;
;   XFNCATCHUP WILDMAT FROM CHAIN QUANTUM
;
; answered, on the connection's pinned view, with one multi-line response
; (RFC 3977 section 3.1.1: dot-stuffed lines, then ".")
;
;   291 NEXT END more|done CHAIN'
;   R <msgid> <line-count>        one header line per record, then
;   <the article's lines>         exactly line-count lines of the article
;   ...
;   .
;
; POSITIONS.  The view's articles are held newest first
; (`fn-state-articles'); a position is an ordinal OLDEST first, so the
; article accepted first is position 0 and the view's length END is the
; peer's log position for this reader.  FROM, NEXT, END and a line count are
; u64 values written as sixteen hexadecimal digits; QUANTUM is decimal.  A
; batch examines the entries from
; FROM on and answers NEXT, the first entry it did not examine; `done' when
; NEXT is END.  Positions count every entry of the view, the ones not served
; included, so they do not depend on WILDMAT and are stable while the view
; only grows.  Local article numbers never appear: a record is a Message-ID
; and the stored octets (the Xref field, which carries numbers, is never
; stored; specs/peering.md section 2.3).
;
; WHAT IS SERVED.  An entry is served exactly when the session could fetch it
; with ARTICLE <msgid> on the same view (books/nntp.lisp
; `fn-nntp-archive-command-pinned''s Message-ID arms): its Message-ID is a
; valid identifier, it is in the view's Message-ID trie (a withdrawn article
; is not), it is not reclaimed (D13), its octets are CRLF-framed, and it is available at a number in a group WILDMAT
; matches (NEWNEWS' test, `fn-nntp-newnews-candidatep').  The view is the
; one the connection pinned, restricted by the login's READ rule
; (books/group-access.lisp), so catch-up serves nothing ARTICLE would not.
;
; THE DIGEST.  CHAIN is 32 octets, hexadecimal on the wire; a record extends
; it as
;
;   c' = BLAKE3(c || BLAKE3(article octets) || msgid octets)
;
; from 32 zero octets.  The peer answers CHAIN' = the chain over this
; batch's records continued from the requester's CHAIN; the requester
; recomputes it over what it received (books/peer-catchup.lisp) and refuses
; a mismatch by name before offering anything of the batch.  The chain over
; a whole catch-up is the digest of the article set it imported, in the
; peer's log order.
;
; WORK.  A batch serves records while their octets stay within QUANTUM
; (capped at `*fn-cu-max-quantum*', local policy), and always at least one
; examined entry, so every batch makes progress and none is silently cut:
; an article larger than the quantum is served whole, alone.
;
; What is proved here (keystones; the host calls `fn-cu-serve-reply' through
; books/nntp.lisp `fn-nntp-command-pinned', the served step's dispatcher):
;   fn-cu-select-serves-only-retrievable   every served article is an entry of
;                                           the view the session could fetch
;   fn-cu-select-makes-progress            NEXT > FROM whenever FROM < END
;   fn-cu-select-stays-within-the-quantum  records after the first fit QUANTUM
(in-package "ACL2")
(include-book "peer-u64-codec")
(include-book "nntp-responses")
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "control-served")
(include-book "group-bucket-index")
(include-book "msgid-index")
(include-book "blake3-stobj")

; -----------------------------------------------------------------------------
; Policy

; The most octets of article one batch serves beyond its first record: a
; work quantum (D27), not a data cap.  A requester's smaller QUANTUM wins.
(defconst *fn-cu-max-quantum* 1048576)

(defconst *fn-cu-zero-chain*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

; -----------------------------------------------------------------------------
; Small total helpers

(defun fn-cu-list (x)
  (declare (xargs :guard t))
  (if (true-listp x) x nil))

(defun fn-cu-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-cu-rev (cdr x) (cons (car x) acc)) acc))

(defun fn-cu-drop (n x)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom x)) x (fn-cu-drop (1- n) (cdr x))))

; A decimal token (1..19 digits) to its value, or nil.
(defun fn-cu-digits-value (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (consp xs)
      (if (and (natp (car xs)) (<= 48 (car xs)) (<= (car xs) 57))
          (fn-cu-digits-value (cdr xs) (+ (* 10 acc) (- (car xs) 48)))
        nil)
    acc))

(defun fn-cu-decimal-value (token)
  (declare (xargs :guard t))
  (if (and (consp token) (true-listp token) (<= (len token) 19))
      (fn-cu-digits-value token 0)
    nil))

(defthm fn-cu-digits-value-type
  (implies (natp acc)
           (or (null (fn-cu-digits-value xs acc))
               (natp (fn-cu-digits-value xs acc))))
  :rule-classes nil)

(defthm fn-cu-decimal-value-type
  (or (null (fn-cu-decimal-value token))
      (natp (fn-cu-decimal-value token)))
  :hints (("Goal" :use ((:instance fn-cu-digits-value-type (xs token) (acc 0)))))
  :rule-classes :type-prescription)

; Hexadecimal, lower case, two digits an octet.
(defun fn-cu-hex-digit (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (if (< n 10) (+ 48 n) (+ 87 (min n 15)))))

(defun fn-cu-hex (octets)
  (declare (xargs :guard t))
  (if (consp octets)
      (let ((o (nfix (car octets))))
        (list* (fn-cu-hex-digit (floor (min o 255) 16))
               (fn-cu-hex-digit (mod (min o 255) 16))
               (fn-cu-hex (cdr octets))))
    nil))

(defun fn-cu-hex-value (c)
  (declare (xargs :guard t))
  (cond ((and (natp c) (<= 48 c) (<= c 57)) (- c 48))
        ((and (natp c) (<= 97 c) (<= c 102)) (- c 87))
        (t nil)))

; The octets of an even-length lower-case hexadecimal token, or :bad.
; Executes by a loop (lane depth-debt, PRF-919): a hex argument's octets,
; two per step; the loop stops at the first bad pair, which the recursion
; answers :bad for as well.  Equal by fn-cu-unhex-loop-is-rev-onto.
(defun fn-cu-unhex-loop (xs acc)
  (declare (xargs :guard t))
  (cond ((atom xs) (fn-ag-rev-onto acc nil))
        ((atom (cdr xs)) :bad)
        (t (let ((hi (fn-cu-hex-value (car xs)))
                 (lo (fn-cu-hex-value (cadr xs))))
             (if (and hi lo)
                 (fn-cu-unhex-loop (cddr xs) (cons (+ (* 16 hi) lo) acc))
               :bad)))))

(defun fn-cu-unhex (xs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (cond ((atom xs) nil)
             ((atom (cdr xs)) :bad)
             (t (let ((hi (fn-cu-hex-value (car xs)))
                      (lo (fn-cu-hex-value (cadr xs)))
                      (rest (fn-cu-unhex (cddr xs))))
                  (if (and hi lo (not (equal rest :bad)))
                      (cons (+ (* 16 hi) lo) rest)
                    :bad))))
       :exec (fn-cu-unhex-loop xs nil)))

(defthm fn-cu-unhex-loop-is-rev-onto
  (equal (fn-cu-unhex-loop xs acc)
         (let ((r (fn-cu-unhex xs)))
           (if (equal r :bad) :bad (fn-ag-rev-onto acc r))))
  :hints (("Goal" :induct (fn-cu-unhex-loop xs acc)
                  :in-theory (union-theories
                              '(fn-cu-unhex-loop fn-cu-unhex fn-ag-rev-onto
                                atom not car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cu-unhex
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cu-unhex fn-ag-rev-onto fn-cu-unhex-loop-is-rev-onto
                                atom not car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; A position or a count on the wire: a u64 as sixteen hexadecimal digits,
; so every rendered line has a fixed width and no value is rendered short.
(defconst *fn-cu-u64-limit* 18446744073709551616)

(defun fn-cu-u64-hex (n)
  (declare (xargs :guard t))
  (fn-cu-hex (fn-cu-u64-octets n)))

; The value of a sixteen-digit hexadecimal token, or nil.
(defun fn-cu-u64-value (token)
  (declare (xargs :guard t))
  (if (and (true-listp token) (equal (len token) 16))
      (let ((octets (fn-cu-unhex token)))
        (if (equal octets :bad) nil (fn-cu-octets-value octets 0)))
    nil))

; A chain value: exactly 32 octets.
(defun fn-cu-chainp (x)
  (declare (xargs :guard t))
  (and (fn-octet-listp x) (equal (len x) 32)))

; -----------------------------------------------------------------------------
; The chain

(defun fn-cu-msgid-octets (msgid)
  (declare (xargs :guard t))
  (fn-nntp-string-octets msgid))

; KEYSTONE SUBJECT (both halves).  One record's step of the digest chain:
; MSGID the Message-ID's octets, BYTES the article's.
(defun fn-cu-chain-step (chain msgid bytes)
  (declare (xargs :guard t))
  (fn-blake3-stobj (append (fn-cu-list chain)
                           (fn-blake3-stobj bytes)
                           (fn-cu-list msgid))))

; -----------------------------------------------------------------------------
; Selecting a batch

; KEYSTONE SUBJECT.  An entry of the view is served exactly when ARTICLE
; <msgid> on the same view would return it (see the head of this book) and
; WILDMAT's groups hold it at a number.
(defun fn-cu-servedp (article groups trie fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-nntp-article-idp article)
       (fn-nntp-newnews-candidatep groups article)
       (consp (fn-midx-lookup (fn-article-msgid article) trie))
       (not (fn-nntp-article-tombstonep article fn-arena))
       (fn-nntp-article-framedp article fn-arena)
       t))

; The walk over the oldest-first ENTRIES from position POS: (mv next served
; used), SERVED newest-first (the order is turned once at the end), USED the
; octets served so far.  The first served record is always taken; a later
; one only when its octets fit what remains of QUANTUM.  An entry that is
; not served is passed over and counts as examined.
(defun fn-cu-select-aux (entries groups trie quantum pos served used fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp quantum) (natp pos) (natp used))))
  (if (atom entries)
      (mv pos served used)
    (let ((a (car entries)))
      (if (fn-cu-servedp a groups trie fn-arena)
          (let ((cost (len (fn-nntp-article-bytes a fn-arena))))
            (if (and (consp served) (< quantum (+ used cost)))
                (mv pos served used)
              (fn-cu-select-aux (cdr entries) groups trie quantum (+ 1 pos)
                                (cons a served) (+ used cost) fn-arena)))
        (fn-cu-select-aux (cdr entries) groups trie quantum (+ 1 pos)
                          served used fn-arena)))))

; KEYSTONE SUBJECT.  The batch at FROM: (mv next articles), ARTICLES oldest
; first.
(defun fn-cu-select (articles from groups trie quantum fn-arena)
  (declare (xargs :stobjs fn-arena :guard (and (natp from) (natp quantum))))
  (mv-let (next served used)
    (fn-cu-select-aux (fn-cu-drop from (fn-cu-rev articles nil))
                      groups trie quantum from nil 0 fn-arena)
    (declare (ignore used))
    (mv next (fn-cu-rev served nil))))

; The chain over ARTICLES from CHAIN.
(defun fn-cu-chain-over (chain articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (fn-cu-chain-over (fn-cu-chain-step chain (fn-cu-msgid-octets
                                                 (fn-article-msgid (car articles)))
                                          (fn-nntp-article-bytes (car articles)
                                                                 fn-arena))
                        (cdr articles) fn-arena)
    (fn-cu-list chain)))

; -----------------------------------------------------------------------------
; Rendering

(defun fn-cu-article-lines (bytes)
  ; The CRLF-framed article's lines, CRLF removed.
  (declare (xargs :guard t))
  (let ((split (fn-nntp-crlf-lines bytes)))
    (if (and (consp split) (equal (car split) :ok) (consp (cdr split)))
        (fn-cu-list (cadr split))
      nil)))

(defun fn-cu-record-header (msgid count)
  (declare (xargs :guard t))
  (append (fn-nntp-string-octets "R ")
          (fn-cu-msgid-octets msgid)
          (list 32)
          (fn-cu-u64-hex count)))

; The block's lines, record after record.
(defun fn-cu-render-lines (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (let ((lines (fn-cu-article-lines
                    (fn-nntp-article-bytes (car articles) fn-arena))))
        (cons (fn-cu-record-header (fn-article-msgid (car articles)) (len lines))
              (append lines (fn-cu-render-lines (cdr articles) fn-arena))))
    nil))

(defun fn-cu-initial-line (next end chain)
  (declare (xargs :guard t))
  (append (fn-nntp-string-octets "291 ")
          (fn-cu-u64-hex next)
          (list 32)
          (fn-cu-u64-hex end)
          (fn-nntp-string-octets (if (equal next end) " done " " more "))
          (fn-cu-hex chain)))

; -----------------------------------------------------------------------------
; The command

; The request's four arguments, parsed: (wildmat-patterns from chain quantum)
; or nil for a syntax error.
(defun fn-cu-parse-request (args)
  (declare (xargs :guard t))
  (if (and (true-listp args) (equal (len args) 4))
      (let ((patterns (fn-wildmat-parse (fn-cu-list (car args))))
            (from (fn-cu-u64-value (cadr args)))
            (chain (fn-cu-unhex (caddr args)))
            (quantum (fn-cu-decimal-value (cadddr args))))
        (if (and (fn-wildmat-result-okp patterns)
                 (natp from) (natp quantum)
                 (fn-cu-chainp chain))
            (list (fn-wildmat-result-value patterns) from chain quantum)
          nil))
    nil))

; KEYSTONE SUBJECT.  The reply to XFNCATCHUP ARGS on the pinned view ARCHIVE
; with its index INDEX: what books/nntp.lisp `fn-nntp-command-pinned' answers.
(defun fn-cu-serve-reply (session archive index args fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((request (fn-cu-parse-request args)))
    (if (not request)
        (fn-nntp-single session (fn-proto-text * :syntax))
      (let* ((articles (fn-cu-list (fn-state-articles archive)))
             (end (len articles))
             (from (nfix (cadr request))))
        (cond
         ((<= *fn-cu-u64-limit* end)
          ;; A view of 2^64 entries has no position on the wire: refused by
          ;; name, never rendered short.
          (fn-nntp-single session (fn-proto-text "XFNCATCHUP" :out-of-range)))
         ((< end from)
          (fn-nntp-single session (fn-proto-text "XFNCATCHUP" :past-end)))
         (t
          (let ((groups (fn-nntp-filter-groups-by-wildmat
                         (car request) (fn-cu-list (fn-state-groups archive))))
                (quantum (min (nfix (cadddr request)) *fn-cu-max-quantum*)))
            (mv-let (next served)
              (fn-cu-select articles from groups (fn-gidx-pin-trie index)
                            quantum fn-arena)
              (fn-nntp-multi-octets
               session
               (fn-cu-initial-line next end
                                   (fn-cu-chain-over (caddr request) served fn-arena))
               (fn-cu-render-lines served fn-arena))))))))))

; -----------------------------------------------------------------------------
; Keystones

(local
 (defthm fn-cu-select-aux-served-member
   (implies (and (member-equal a (mv-nth 1 (fn-cu-select-aux entries groups trie quantum
                                                             pos served used fn-arena)))
                 (not (member-equal a served)))
            (and (member-equal a entries)
                 (fn-cu-servedp a groups trie fn-arena)))
   :hints (("Goal" :in-theory (disable fn-cu-servedp fn-nntp-article-bytes)))))

(local
 (defthm fn-cu-member-drop
   (implies (member-equal a (fn-cu-drop n x))
            (member-equal a x))))

(local
 (defthm fn-cu-member-rev
   (iff (member-equal a (fn-cu-rev x y))
        (or (member-equal a x) (member-equal a y)))
   :hints (("Goal" :induct (fn-cu-rev x y)))))

(local
 (defthm fn-cu-len-rev
   (equal (len (fn-cu-rev x y)) (+ (len x) (len y)))
   :hints (("Goal" :induct (fn-cu-rev x y)))))

(local
 (defthm fn-cu-member-drop-rev
   (implies (member-equal a (fn-cu-drop n (fn-cu-rev x nil)))
            (member-equal a x))
   :hints (("Goal" :use ((:instance fn-cu-member-drop (x (fn-cu-rev x nil))))
            :in-theory (disable fn-cu-member-drop fn-cu-drop fn-cu-rev)))))

; KEYSTONE (what is served).  Every article a batch serves is an entry of the
; view and one the session could fetch by Message-ID (`fn-cu-servedp'): the
; view's trie holds it, it is not reclaimed, it is framed, and WILDMAT's
; groups hold it at a number.
(defthm fn-cu-select-serves-only-retrievable
  (implies (member-equal a (mv-nth 1 (fn-cu-select articles from groups trie
                                                   quantum fn-arena)))
           (and (member-equal a articles)
                (fn-cu-servedp a groups trie fn-arena)))
  :hints (("Goal" :in-theory (disable fn-cu-servedp fn-cu-select-aux fn-cu-drop fn-cu-rev)
           :use ((:instance fn-cu-select-aux-served-member
                            (entries (fn-cu-drop from (fn-cu-rev articles nil)))
                            (pos from) (served nil) (used 0))))))

(local
 (defthm fn-cu-select-aux-pos-grows
   (implies (natp pos)
            (<= pos (car (fn-cu-select-aux entries groups trie quantum
                                           pos served used fn-arena))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable fn-cu-servedp fn-nntp-article-bytes)))))

(local
 (defthm fn-cu-select-aux-progress
   (implies (and (consp entries) (natp pos) (not (consp served)))
            (< pos (car (fn-cu-select-aux entries groups trie quantum
                                          pos served used fn-arena))))
   :rule-classes :linear
   :hints (("Goal" :expand ((fn-cu-select-aux entries groups trie quantum
                                              pos served used fn-arena))
            :do-not-induct t
            :in-theory (disable fn-cu-servedp fn-nntp-article-bytes
                                fn-cu-select-aux)))))

(local
 (defthm fn-cu-consp-drop
   (implies (and (natp n) (< n (len x)))
            (consp (fn-cu-drop n x)))
   :hints (("Goal" :induct (fn-cu-drop n x)))))

(local
 (defthm fn-cu-len-rev-nil
   (equal (len (fn-cu-rev x nil)) (len x))))

; KEYSTONE (progress).  A batch below the end always examines an entry, so
; NEXT moves past FROM: a catch-up never stalls on an article it cannot serve
; or one larger than the quantum.
(defthm fn-cu-select-makes-progress
  (implies (and (natp from) (< from (len articles)))
           (< from (mv-nth 0 (fn-cu-select articles from groups trie quantum
                                           fn-arena))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cu-select-aux fn-cu-servedp fn-cu-drop fn-cu-rev)
           :use ((:instance fn-cu-select-aux-progress
                            (entries (fn-cu-drop from (fn-cu-rev articles nil)))
                            (pos from) (served nil) (used 0))))))

; The octets of a list of articles.
(defun fn-cu-octets-of (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp articles)
      (+ (len (fn-nntp-article-bytes (car articles) fn-arena))
         (fn-cu-octets-of (cdr articles) fn-arena))
    0))

(local
 (defthm fn-cu-select-aux-within
   (implies (and (natp used) (natp quantum)
                 (or (not (consp served)) (<= used quantum) (equal (len served) 1))
                 (equal used (fn-cu-octets-of served fn-arena)))
            (let ((out (mv-nth 1 (fn-cu-select-aux entries groups trie quantum
                                                   pos served used fn-arena))))
              (or (<= (fn-cu-octets-of out fn-arena) quantum)
                  (equal (len out) 1))))
   :hints (("Goal" :in-theory (disable fn-cu-servedp fn-nntp-article-bytes)))
   :rule-classes nil))

(local
 (defthm fn-cu-octets-of-rev
   (equal (fn-cu-octets-of (fn-cu-rev x y) fn-arena)
          (+ (fn-cu-octets-of x fn-arena) (fn-cu-octets-of y fn-arena)))
   :hints (("Goal" :induct (fn-cu-rev x y)
            :in-theory (disable fn-nntp-article-bytes)))))

; KEYSTONE (bounded work).  A batch serves at most QUANTUM octets of article,
; or exactly one article (one larger than the quantum is served whole and
; alone, never cut).
(defthm fn-cu-select-stays-within-the-quantum
  (implies (natp quantum)
           (let ((served (mv-nth 1 (fn-cu-select articles from groups trie
                                                 quantum fn-arena))))
             (or (<= (fn-cu-octets-of served fn-arena) quantum)
                 (equal (len served) 1))))
  :hints (("Goal" :in-theory (disable fn-cu-select-aux fn-nntp-article-bytes)
           :use ((:instance fn-cu-select-aux-within
                            (entries (fn-cu-drop from (fn-cu-rev articles nil)))
                            (pos from) (served nil) (used 0)))))
  :rule-classes nil)

(verify-guards fn-cu-serve-reply)

; The reply leaves the session as it was (it moves no cursor and selects no
; group), and it is one reply effect: the facts the dispatcher's theorems
; need with the reply closed.
(defthm fn-cu-serve-reply-preserves-session
  (and (equal (fn-nntp-result-session
               (fn-cu-serve-reply session archive index args fn-arena))
              session)
       (equal (car (fn-cu-serve-reply session archive index args fn-arena))
              session))
  :hints (("Goal" :in-theory (e/d (fn-cu-serve-reply fn-nntp-multi-octets
                                   fn-nntp-single fn-nntp-make-result
                                   fn-nntp-result-session fn-nntp-result-effects
                                   fn-nntp-reply-effect)
                                  (fn-cu-select fn-cu-chain-over
                                   fn-cu-render-lines fn-cu-initial-line
                                   fn-cu-parse-request fn-nntp-string-octets
                                   fn-nntp-crlf fn-nntp-stuff-lines fn-cu-list
                                   fn-nntp-filter-groups-by-wildmat
                                   fn-gidx-pin-trie)))))

(defthm fn-cu-serve-reply-is-one-reply
  (let ((effects (fn-nntp-result-effects
                  (fn-cu-serve-reply session archive index args fn-arena))))
    (and (consp effects)
         (null (cdr effects))
         (equal (car (car effects)) :reply)))
  :hints (("Goal" :in-theory (e/d (fn-cu-serve-reply fn-nntp-multi-octets
                                   fn-nntp-single fn-nntp-make-result
                                   fn-nntp-result-session fn-nntp-result-effects
                                   fn-nntp-reply-effect)
                                  (fn-cu-select fn-cu-chain-over
                                   fn-cu-render-lines fn-cu-initial-line
                                   fn-cu-parse-request fn-nntp-string-octets
                                   fn-nntp-crlf fn-nntp-stuff-lines fn-cu-list
                                   fn-nntp-filter-groups-by-wildmat
                                   fn-gidx-pin-trie)))))

(in-theory (disable fn-cu-serve-reply fn-cu-select fn-cu-servedp fn-cu-chain-step))
