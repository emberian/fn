; D2b: the grammar generator and mutator (layer-D brief item 2; RELEASE-PLAN
; section 2.4, form F), generic over any DEFGRAMMAR declaration.
; DEFGRAMMAR-GENERATOR reads the grammar's (:command ...) rows from the
; declaration table and emits NAME-generate and NAME-mutate over them.
;
; Syntax only. What a generated line parses to (its tag, argument count and
; argument descriptors) comes from the declaration; what a mutated line must
; be refused with comes from the spec table the caller passes, never from
; the parser. A case is (octets events replies mode): the transcript, the
; events the transcript runner must report, the reply codes it must render,
; and the mode it must end in. A random mutation (class :random) carries no
; expectation; the fuzzer checks it for totality, typing and fragmentation,
; and H's model checks its replies. Lists of octets throughout: this is a
; test view that nothing served includes. Randomness is the simulator's
; PRNG, so a case replays from (seed, class, mask, budget).
(in-package "ACL2")
(include-book "../books/grammar")
(include-book "../sim/prng")

; ------------------------------------------------------------------------
; The PRNG as one value: the four xoshiro words in a list.
(defun fn2-gg-rng (seed)
  (declare (xargs :verify-guards nil))
  (mv-let (a b c d) (fn2-prng-seed (nfix seed)) (list a b c d)))
(defun fn2-gg-below (n rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k a b c d) (fn2-prng-below (max 1 (min (nfix n) 4294967295))
                                      (nth 0 rng) (nth 1 rng) (nth 2 rng) (nth 3 rng))
    (mv (nfix k) (list a b c d))))
; An integer in [lo, hi].
(defun fn2-gg-upto (lo hi rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k rng) (fn2-gg-below (+ 1 (nfix (- hi lo))) rng) (mv (+ (nfix lo) k) rng)))
(defun fn2-gg-pick (xs rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k rng) (fn2-gg-below (len xs) rng) (mv (nth k xs) rng)))
; True with probability 1/N.
(defun fn2-gg-one-in (n rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k rng) (fn2-gg-below n rng) (mv (equal k 0) rng)))

; ------------------------------------------------------------------------
; Octets.
(defun fn2-gg-chars (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-gg-chars (cdr cs)))))
(defun fn2-gg-str (s) (declare (xargs :verify-guards nil)) (fn2-gg-chars (coerce s 'list)))
(defun fn2-gg-decimal (n)
  (declare (xargs :verify-guards nil))
  (fn2-gg-chars (explode-nonnegative-integer (nfix n) 10 nil)))
(defun fn2-gg-repeat (k byte)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) nil (cons byte (fn2-gg-repeat (- k 1) byte))))
; N in decimal, zero-padded to WIDTH.
(defun fn2-gg-padded (n width)
  (declare (xargs :verify-guards nil))
  (let ((d (fn2-gg-decimal n))) (append (fn2-gg-repeat (nfix (- width (len d))) 48) d)))
(defun fn2-gg-range-octets (lo hi)
  (declare (xargs :verify-guards nil :measure (nfix (- (+ 1 (nfix hi)) (nfix lo)))))
  (if (> (nfix lo) (nfix hi)) nil (cons (nfix lo) (fn2-gg-range-octets (+ 1 (nfix lo)) hi))))
(defun fn2-gg-remove (x xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (if (equal x (car xs)) (fn2-gg-remove x (cdr xs)) (cons (car xs) (fn2-gg-remove x (cdr xs))))))

(defconst *fn2-gg-alpha* (fn2-gg-str "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"))
(defconst *fn2-gg-name* (fn2-gg-str "abcdefghijklmnopqrstuvwxyz0123456789.-+_"))
(defconst *fn2-gg-wild* (fn2-gg-str "abcdefghijklmnopqrstuvwxyz0123456789.*?-"))
(defconst *fn2-gg-label* (fn2-gg-str "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789.-"))
(defconst *fn2-gg-printable* (fn2-gg-range-octets 33 126))
; RFC 3977 section 3.6: a Message-ID's octets between the brackets.
(defconst *fn2-gg-msgid-octets* (fn2-gg-remove 62 (fn2-gg-range-octets 33 126)))
; Block line text: printable, TAB, and 8-bit octets.
(defconst *fn2-gg-text* (cons 9 (fn2-gg-range-octets 32 126)))
(defconst *fn2-gg-high* (fn2-gg-range-octets 128 255))
(defconst *fn2-gg-crlf* '(13 10))

; K octets drawn from POOL.
(defun fn2-gg-from (k pool rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) (mv nil rng)
    (mv-let (b rng) (fn2-gg-pick pool rng)
      (mv-let (rest rng) (fn2-gg-from (- k 1) pool rng) (mv (cons b rest) rng)))))
; Upper-case letters of OCTETS turned to lower case at random (keywords are
; case-insensitive, RFC 3977 section 3.1).
(defun fn2-gg-case (octets rng)
  (declare (xargs :verify-guards nil))
  (if (atom octets) (mv nil rng)
    (mv-let (flip rng) (fn2-gg-below 2 rng)
      (mv-let (rest rng) (fn2-gg-case (cdr octets) rng)
        (let ((b (car octets)))
          (mv (cons (if (and (equal flip 1) (natp b) (<= 65 b) (<= b 90)) (+ b 32) b) rest) rng))))))
(defun fn2-gg-upcase (octets)
  (declare (xargs :verify-guards nil))
  (if (atom octets) nil
    (cons (let ((b (car octets))) (if (and (natp b) (<= 97 b) (<= b 122)) (- b 32) b))
          (fn2-gg-upcase (cdr octets)))))
(defun fn2-gg-join (parts sep)
  (declare (xargs :verify-guards nil))
  (if (atom parts) nil (if (atom (cdr parts)) (car parts) (append (car parts) sep (fn2-gg-join (cdr parts) sep)))))
(defun fn2-gg-insert (octets i bytes)
  (declare (xargs :verify-guards nil))
  (append (take (nfix i) octets) bytes (nthcdr (nfix i) octets)))

; ------------------------------------------------------------------------
; Valid arguments. Each generator returns (mv octets descriptor rng), the
; descriptor being what the parser must report for the token: (form a b),
; with a span's offset relative to the token's first octet.
(defun fn2-gg-number (rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k rng) (fn2-gg-below 4 rng)
    (case k
      (0 (mv 1 rng))
      (1 (mv *fn2-gram-article-max* rng))
      (2 (mv-let (v rng) (fn2-gg-below 999 rng) (mv (+ 1 v) rng)))
      (otherwise (mv-let (v rng) (fn2-gg-below *fn2-gram-article-max* rng) (mv (+ 1 v) rng))))))
(defun fn2-gg-msgid (short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (long rng) (fn2-gg-one-in 16 rng)
    (mv-let (n rng) (fn2-gg-upto 1 (if short 8 (if long 120 30)) rng)
      (mv-let (mid rng) (fn2-gg-from n *fn2-gg-msgid-octets* rng)
        (let ((o (append '(60) mid '(62)))) (mv o (list :span 0 (len o)) rng))))))
(defun fn2-gg-range (rng)
  (declare (xargs :verify-guards nil))
  (mv-let (lo rng) (fn2-gg-number rng)
    (mv-let (form rng) (fn2-gg-below 3 rng)
      (case form
        (0 (mv (fn2-gg-decimal lo) (list :range lo lo) rng))
        (1 (mv (append (fn2-gg-decimal lo) '(45)) (list :range lo *fn2-none*) rng))
        (otherwise
         (mv-let (d rng) (fn2-gg-below 1000 rng)
           (let ((hi (min *fn2-gram-article-max* (+ lo d))))
             (mv (append (fn2-gg-decimal lo) '(45) (fn2-gg-decimal hi)) (list :range lo hi) rng))))))))
(defun fn2-gg-wild-alts (k first rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) (mv nil rng)
    (mv-let (n rng) (fn2-gg-upto 1 6 rng)
      (mv-let (alt rng) (fn2-gg-from n *fn2-gg-wild* rng)
        (mv-let (neg rng) (fn2-gg-one-in 3 rng)
          (mv-let (rest rng) (fn2-gg-wild-alts (- k 1) nil rng)
            (mv (cons (if (and neg (not first)) (cons 33 alt) alt) rest) rng)))))))
(defun fn2-gg-token (short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (any rng) (fn2-gg-one-in 8 rng)
    (mv-let (n rng) (fn2-gg-upto 1 (if short 8 24) rng)
      (fn2-gg-from n (if any *fn2-gg-printable* *fn2-gg-name*) rng))))
(defun fn2-gg-tokens (k short rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) (mv nil rng)
    (mv-let (tok rng) (fn2-gg-token short rng)
      (mv-let (rest rng) (fn2-gg-tokens (- k 1) short rng) (mv (cons tok rest) rng)))))
(defun fn2-gg-span (o rng) (declare (xargs :verify-guards nil)) (mv o (list :span 0 (len o)) rng))

(defun fn2-gg-arg (kind short rng)
  (declare (xargs :verify-guards nil))
  (cond
   ((consp kind)                        ; (:keyword W ...)
    (mv-let (k rng) (fn2-gg-below (len (cdr kind)) rng)
      (mv-let (w rng) (fn2-gg-case (fn2-gg-str (nth k (cdr kind))) rng)
        (mv w (list :keyword k 0) rng))))
   ((eq kind :number)
    (mv-let (v rng) (fn2-gg-number rng)
      (mv-let (zero rng) (fn2-gg-one-in 8 rng)
        (mv (append (and zero (< (len (fn2-gg-decimal v)) 16) '(48)) (fn2-gg-decimal v)) (list :number v 0) rng))))
   ((eq kind :digits)
    (mv-let (v rng) (fn2-gg-below 1000000 rng) (mv (fn2-gg-decimal v) (list :number v 0) rng)))
   ((eq kind :range) (fn2-gg-range rng))
   ((eq kind :msgid) (fn2-gg-msgid short rng))
   ((member-eq kind '(:ref :ref-range))
    (mv-let (id rng) (fn2-gg-below 2 rng)
      (if (equal id 0) (fn2-gg-msgid short rng)
        (if (eq kind :ref-range) (fn2-gg-range rng)
          (mv-let (v rng) (fn2-gg-number rng) (mv (fn2-gg-decimal v) (list :number v 0) rng))))))
   ((eq kind :wildmat)
    (mv-let (k rng) (fn2-gg-upto 1 3 rng)
      (mv-let (alts rng) (fn2-gg-wild-alts k t rng) (fn2-gg-span (fn2-gg-join alts '(44)) rng))))
   ((eq kind :label)
    (mv-let (first rng) (fn2-gg-pick *fn2-gg-alpha* rng)
      (mv-let (n rng) (fn2-gg-upto 2 8 rng)
        (mv-let (rest rng) (fn2-gg-from n *fn2-gg-label* rng) (fn2-gg-span (cons first rest) rng)))))
   ((eq kind :date)                     ; RFC 3977 section 7.3: [yy]yymmdd
    (mv-let (eight rng) (fn2-gg-below 2 rng)
      (mv-let (y rng) (if (equal eight 1) (fn2-gg-upto 1970 2037 rng) (fn2-gg-below 100 rng))
        (mv-let (m rng) (fn2-gg-upto 1 12 rng)
          (mv-let (d rng) (fn2-gg-upto 1 28 rng)
            (let ((v (+ (* y 10000) (* m 100) d)) (w (if (equal eight 1) 8 6)))
              (mv (fn2-gg-padded v w) (list :date v w) rng)))))))
   ((eq kind :time)
    (mv-let (h rng) (fn2-gg-below 24 rng)
      (mv-let (m rng) (fn2-gg-below 60 rng)
        (mv-let (s rng) (fn2-gg-below 60 rng)
          (let ((v (+ (* h 10000) (* m 100) s))) (mv (fn2-gg-padded v 6) (list :time v 0) rng))))))
   ((eq kind :gmt) (mv-let (w rng) (fn2-gg-case (fn2-gg-str "GMT") rng) (mv w (list :gmt 1 0) rng)))
   ((eq kind :rest)
    (mv-let (k rng) (fn2-gg-upto 1 3 rng)
      (mv-let (toks rng) (fn2-gg-tokens k t rng) (fn2-gg-span (fn2-gg-join toks '(32)) rng))))
   (t (mv-let (o rng) (fn2-gg-token short rng) (fn2-gg-span o rng)))))

; Arguments that are not valid for their kind: each must be refused with 501.
(defconst *fn2-gg-invalid*
  '((:number "0" "2147483648" "12a" "-1" "00000000000000001")
    (:digits "1a" "x" "00000000000000001")
    (:range "0-5" "5-x" "a" "1--2" "-5")
    (:msgid "a@b" "<>" "<a" "a>" "<a>b>")
    (:ref "<a" "0" "x")
    (:ref-range "<>" "0-" "x-1")
    (:wildmat "a,,b" "!a" "a[b" "a," "a!b")
    (:label "1ab" "ab" "a_b")
    (:date "1234567" "12345" "2026102x")
    (:time "12345" "1234567" "12a456")
    (:gmt "UTC" "GMTX")
    (:keyword "BOGUS" "X")))
(defun fn2-gg-kind (arg)
  (declare (xargs :verify-guards nil))
  (let ((b (fn2-gram-arg-base arg))) (if (consp b) :keyword b)))
(defun fn2-gg-invalidable (args i)
  (declare (xargs :verify-guards nil))
  (if (atom args) nil
    (append (and (assoc-eq (fn2-gg-kind (car args)) *fn2-gg-invalid*) (list i))
            (fn2-gg-invalidable (cdr args) (+ 1 i)))))

; ------------------------------------------------------------------------
; Lines. A row of the generator table is
;   (tag keyword args mask block hand-off first-code)
; with MASK the states that admit the command and FIRST-CODE the code of its
; first declared reply (the transcript runner's responder for a parsed line).
(defun fn2-gg-row-tag (row) (declare (xargs :verify-guards nil)) (nth 0 row))
(defun fn2-gg-row-keyword (row) (declare (xargs :verify-guards nil)) (nth 1 row))
(defun fn2-gg-row-args (row) (declare (xargs :verify-guards nil)) (nth 2 row))
(defun fn2-gg-row-mask (row) (declare (xargs :verify-guards nil)) (nth 3 row))
(defun fn2-gg-row-block (row) (declare (xargs :verify-guards nil)) (nth 4 row))
(defun fn2-gg-row-hand-off (row) (declare (xargs :verify-guards nil)) (nth 5 row))
(defun fn2-gg-row-first-code (row) (declare (xargs :verify-guards nil)) (nth 6 row))
(defun fn2-gg-admitted (row mask)
  (declare (xargs :verify-guards nil))
  (logtest (ifix (fn2-gg-row-mask row)) (ifix mask)))

; Rows satisfying a property, by name.
(defun fn2-gg-select (table mask prop)
  (declare (xargs :verify-guards nil))
  (if (atom table) nil
    (let* ((row (car table)) (args (fn2-gg-row-args row)))
      (append (and (case prop
                     (:admitted (fn2-gg-admitted row mask))
                     (:plain (and (fn2-gg-admitted row mask) (not (fn2-gg-row-hand-off row))))
                     (:unblocked (and (fn2-gg-admitted row mask) (not (fn2-gg-row-hand-off row))
                                      (not (fn2-gg-row-block row))))
                     (:refused (not (fn2-gg-admitted row mask)))
                     (:required (and (fn2-gg-admitted row mask) (< 0 (fn2-gram-args-required args))))
                     (:bounded (and (fn2-gg-admitted row mask) (not (fn2-gram-args-rest-p args))))
                     (:invalidable (and (fn2-gg-admitted row mask) (fn2-gg-invalidable args 0)))
                     (:block (and (fn2-gg-admitted row mask) (fn2-gg-row-block row)))
                     (otherwise nil))
                   (list row))
              (fn2-gg-select (cdr table) mask prop)))))

; A separator: one SP, or now and then a run of SP and TAB.
(defun fn2-gg-sep (rng)
  (declare (xargs :verify-guards nil))
  (mv-let (run rng) (fn2-gg-one-in 8 rng)
    (if (not run) (mv '(32) rng)
      (mv-let (n rng) (fn2-gg-upto 1 3 rng) (fn2-gg-from n '(32 9) rng)))))

; The first N arguments of ARGS: (mv tokens rng), each token (octets desc).
(defun fn2-gg-args (args n short rng)
  (declare (xargs :verify-guards nil))
  (if (or (zp n) (atom args)) (mv nil rng)
    (mv-let (o desc rng) (fn2-gg-arg (fn2-gram-arg-base (car args)) short rng)
      (mv-let (rest rng) (fn2-gg-args (cdr args) (- n 1) short rng)
        (mv (cons (list o desc) rest) rng)))))

; Assemble keyword and tokens into a line: (mv octets descs rng), each
; descriptor's span offset made relative to the line's first octet.
(defun fn2-gg-place (tokens pos rng)
  (declare (xargs :verify-guards nil))
  (if (atom tokens) (mv nil nil rng)
    (mv-let (sep rng) (fn2-gg-sep rng)
      (let* ((o (car (car tokens))) (desc (cadr (car tokens)))
             (start (+ pos (len sep)))
             (desc (if (eq (car desc) :span) (list :span start (caddr desc)) desc)))
        (mv-let (rest descs rng) (fn2-gg-place (cdr tokens) (+ start (len o)) rng)
          (mv (append sep o rest) (cons desc descs) rng))))))

(defun fn2-gg-fields (descs i)
  (declare (xargs :verify-guards nil :measure (nfix (- 4 (nfix i)))))
  (if (>= (nfix i) 4) nil
    (append (if (consp descs) (car descs) '(:absent 0 0)) (fn2-gg-fields (if (consp descs) (cdr descs) nil) (+ 1 (nfix i))))))

; A valid line for ROW with N arguments present: (mv octets event rng), the
; event relative to the line's first octet.
(defun fn2-gg-line-n (row n short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (kw rng) (fn2-gg-case (fn2-gg-str (fn2-gg-row-keyword row)) rng)
    (mv-let (tokens rng) (fn2-gg-args (fn2-gg-row-args row) n short rng)
      (mv-let (body descs rng) (fn2-gg-place tokens (len kw) rng)
        (let* ((octets (append kw body *fn2-gg-crlf*))
               (args (fn2-gg-row-args row))
               (nargs (if (fn2-gram-args-rest-p args) (len args) (len tokens))))
          (mv octets
              (append (list :command :ok (fn2-gg-row-tag row) nargs) (fn2-gg-fields descs 0)
                      (list 0 (len octets) :ok))
              rng))))))
; Arguments present: the required ones and a random number of the optional.
(defun fn2-gg-present (row rng)
  (declare (xargs :verify-guards nil))
  (let ((args (fn2-gg-row-args row)))
    (fn2-gg-upto (fn2-gram-args-required args) (len args) rng)))
(defun fn2-gg-leading-ws (octets)
  (declare (xargs :verify-guards nil))
  (if (and (consp octets) (member (car octets) '(32 9))) (cons (car octets) (fn2-gg-leading-ws (cdr octets))) nil))
; The length of the arguments: from the first token to the CRLF.
(defun fn2-gg-args-length (octets kwlen)
  (declare (xargs :verify-guards nil))
  (let* ((rest (nthcdr kwlen octets))
         (n (- (len rest) 2)))
    (if (<= n 0) 0
      (- n (len (fn2-gg-leading-ws rest))))))
(defun fn2-gg-line (row caps short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (n rng) (fn2-gg-present row rng)
    (mv-let (octets event rng) (fn2-gg-line-n row n short rng)
      (if (and (<= (len octets) (nth 0 caps))
               (<= (fn2-gg-args-length octets (length (fn2-gg-row-keyword row))) (nth 1 caps)))
          (mv octets event rng)
        (fn2-gg-line-n row n t rng)))))

; ------------------------------------------------------------------------
; Blocks (RFC 3977 section 3.1.1): text lines, dot-stuffed, then ".CRLF".
; One line: (mv octets event rng), the event relative to the line.
(defun fn2-gg-block-line-of (content)
  (declare (xargs :verify-guards nil))
  (let ((stuffed (and (consp content) (equal (car content) 46))))
    (mv (append (and stuffed '(46)) content *fn2-gg-crlf*)
        (list :data (if stuffed 1 0) (+ (if stuffed 1 0) (len content))))))
(defun fn2-gg-text (short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (k rng) (fn2-gg-below 16 rng)
    (cond ((equal k 0) (mv nil rng))
          ((equal k 1) (mv-let (n rng) (fn2-gg-upto 1 20 rng)
                         (mv-let (t2 rng) (fn2-gg-from n *fn2-gg-text* rng) (mv (cons 46 t2) rng))))
          ((equal k 2) (mv-let (n rng) (fn2-gg-upto 1 20 rng) (fn2-gg-from n (append *fn2-gg-text* *fn2-gg-high*) rng)))
          ((and (equal k 3) (not short)) (mv-let (n rng) (fn2-gg-upto 200 998 rng) (fn2-gg-from n *fn2-gg-text* rng)))
          (t (mv-let (n rng) (fn2-gg-upto 0 60 rng) (fn2-gg-from n *fn2-gg-text* rng))))))
(defun fn2-gg-shift-fields (fields base)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (car fields)
          (cons (if (eq (car fields) :span) (+ base (nfix (cadr fields))) (cadr fields))
                (cons (caddr fields) (fn2-gg-shift-fields (cdddr fields) base))))))
(defun fn2-gg-shift (ev base)
  (declare (xargs :verify-guards nil))
  (case (car ev)
    (:command
     (append (take 4 ev)
             (fn2-gg-shift-fields (take 12 (nthcdr 4 ev)) base)
             (list (+ base (nth 16 ev)) (+ base (nth 17 ev)) (nth 18 ev))))
    (:refused (list :refused (nth 1 ev) (+ base (nth 2 ev)) (+ base (nth 3 ev))))
    (:data (list :data (+ base (nth 1 ev)) (+ base (nth 2 ev))))
    (otherwise ev)))
(defun fn2-gg-shift-all (evs base)
  (declare (xargs :verify-guards nil))
  (if (atom evs) nil (cons (fn2-gg-shift (car evs) base) (fn2-gg-shift-all (cdr evs) base))))

; K text lines: (mv octets events rng), events relative to the first line.
(defun fn2-gg-block-lines (k short pos rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) (mv nil nil rng)
    (mv-let (content rng) (fn2-gg-text short rng)
      (mv-let (o ev) (fn2-gg-block-line-of content)
        (mv-let (rest evs rng) (fn2-gg-block-lines (- k 1) short (+ pos (len o)) rng)
          (mv (append o rest) (cons (fn2-gg-shift ev pos) evs) rng))))))

; ------------------------------------------------------------------------
; Items and cases. An item is (octets events replies stop open): its events
; relative to its first octet, the reply codes it must render, whether the
; runner must stop after it, and whether it leaves a block open.
(defun fn2-gg-item (octets events replies stop open)
  (declare (xargs :verify-guards nil))
  (list octets events replies stop open))
(defun fn2-gg-command-item (row caps short rng)
  (declare (xargs :verify-guards nil))
  (mv-let (line ev rng) (fn2-gg-line row caps short rng)
    (if (not (fn2-gg-row-block row))
        (mv (fn2-gg-item line (list ev) (list (fn2-gg-row-first-code row)) (and (fn2-gg-row-hand-off row) t) nil) rng)
      (mv-let (k rng) (fn2-gg-upto 1 6 rng)
        (mv-let (body evs rng) (fn2-gg-block-lines k short (len line) rng)
          (mv (fn2-gg-item (append line body '(46 13 10))
                           (append (list ev) evs (list '(:terminator)))
                           (list (fn2-gg-row-first-code row)) nil nil)
              rng))))))

; The case of ITEMS: (octets events replies mode).
(defun fn2-gg-assemble (items octets events replies stopped open)
  (declare (xargs :verify-guards nil))
  (if (atom items)
      (list octets events replies (cond (stopped :stopped) (open :block) (t :command)))
    (let ((item (car items)))
      (if stopped (fn2-gg-assemble (cdr items) (append octets (nth 0 item)) events replies t open)
        (fn2-gg-assemble (cdr items) (append octets (nth 0 item))
                         (append events (fn2-gg-shift-all (nth 1 item) (len octets)))
                         (append replies (nth 2 item)) (nth 3 item) (nth 4 item))))))
(defun fn2-gg-items-length (items)
  (declare (xargs :verify-guards nil))
  (if (atom items) 0 (+ (len (car (car items))) (fn2-gg-items-length (cdr items)))))

; Up to K valid items from the rows of PROP, within BUDGET octets.
(defun fn2-gg-valid-items (k table caps mask prop budget rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (let ((rows (fn2-gg-select table mask prop)))
    (if (or (zp k) (atom rows)) (mv nil rng)
      (mv-let (row rng) (fn2-gg-pick rows rng)
        (mv-let (item rng) (fn2-gg-command-item row caps (< budget 1200) rng)
          (if (> (len (car item)) (nfix budget)) (mv nil rng)
            (if (nth 3 item) (mv (list item) rng)
              (mv-let (rest rng)
                (fn2-gg-valid-items (- k 1) table caps mask prop (- (nfix budget) (len (car item))) rng)
                (mv (cons item rest) rng)))))))))

; A valid transcript of one to six commands within BUDGET octets.
(defun fn2-gg-generate (table caps seed mask budget)
  (declare (xargs :verify-guards nil))
  (let ((rng (fn2-gg-rng seed)))
    (mv-let (k rng) (fn2-gg-upto 1 6 rng)
      (mv-let (items rng) (fn2-gg-valid-items k table caps mask :admitted budget rng)
        (declare (ignore rng))
        (fn2-gg-assemble items nil nil nil nil nil)))))

; ------------------------------------------------------------------------
; Mutations. CLASS names an operator; SPEC is the caller's table
;   ((class outcome reply closes citation) ...)
; giving what the spec answers to the mutated line: OUTCOME is the runner's
; code (:malformed :syntax :unknown :state), or :overflow, or for block
; lines :bad-line, :block-overflow or :open; REPLY is the code (for :state an
; alist from keyword to code); CLOSES says the connection ends there.
(defconst *fn2-gg-line-classes*
  '(:nul :bare-cr :bare-lf :bad-utf8 :empty :control :leading-ws :trailing-ws :overlong
    :args-overlong :unknown :extra-arg :missing-arg :bad-arg :state))
(defconst *fn2-gg-block-classes*
  '(:block-unstuffed :block-nul :block-bare-cr :block-bare-lf :block-overlong :block-no-terminator))
(defconst *fn2-gg-controls* '(0 1 2 3 4 5 6 7 8 11 12 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 127))
(defconst *fn2-gg-bad-utf8* '(#x80 #xbf #xc0 #xc1 #xc3 #xe2 #xed #xf0 #xf5 #xff))

; A short valid line of a row of PROP, as (mv row octets rng), or nil.
(defun fn2-gg-base-line (table caps mask prop n rng)
  (declare (xargs :verify-guards nil))
  (declare (ignorable caps))
  (let ((rows (fn2-gg-select table mask prop)))
    (if (atom rows) (mv nil nil rng)
      (mv-let (row rng) (fn2-gg-pick rows rng)
        (mv-let (k rng) (if (natp n) (mv n rng) (fn2-gg-present row rng))
          (mv-let (octets ev rng) (fn2-gg-line-n row k t rng)
            (declare (ignore ev))
            (mv row octets rng)))))))
(defun fn2-gg-keywordp (octets table)
  (declare (xargs :verify-guards nil))
  (and (consp table)
       (or (equal (fn2-gg-upcase octets) (fn2-gg-str (fn2-gg-row-keyword (car table))))
           (fn2-gg-keywordp octets (cdr table)))))

(defun fn2-gg-short-keywords (rows k)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (append (and (<= (length (fn2-gg-row-keyword (car rows))) k) (list (car rows)))
            (fn2-gg-short-keywords (cdr rows) k))))
; The mutated line of a line class: (mv octets row rng); row is the command
; used (for :state, the keyword decides the reply). Nil when the mask has
; no row the class needs.
(defun fn2-gg-mutated-line (class table caps mask rng)
  (declare (xargs :verify-guards nil))
  (case class
    ((:nul :bare-cr :bad-utf8 :control)
     (mv-let (row line rng) (fn2-gg-base-line table caps mask :admitted nil rng)
       (mv-let (i rng) (fn2-gg-below (- (len line) 1) rng)
         (mv-let (b rng) (case class (:nul (mv 0 rng)) (:bare-cr (mv 13 rng))
                           (:bad-utf8 (fn2-gg-pick *fn2-gg-bad-utf8* rng))
                           (otherwise (fn2-gg-pick (cdr *fn2-gg-controls*) rng)))
           (mv (fn2-gg-insert line i (list b)) row rng)))))
    (:bare-lf
     (mv-let (row line rng) (fn2-gg-base-line table caps mask :admitted nil rng)
       (mv (append (take (- (len line) 2) line) '(10)) row rng)))
    (:empty (mv *fn2-gg-crlf* nil rng))
    ((:leading-ws :trailing-ws)
     (mv-let (row line rng) (fn2-gg-base-line table caps mask :admitted nil rng)
       (mv-let (b rng) (fn2-gg-pick '(32 9) rng)
         (mv (if (eq class :leading-ws) (cons b line) (fn2-gg-insert line (- (len line) 2) (list b))) row rng))))
    (:overlong
     (mv-let (row line rng) (fn2-gg-base-line table caps mask :admitted nil rng)
       (mv-let (j rng) (fn2-gg-upto 1 60 rng)
         (let ((pad (- (+ (nth 0 caps) j) (len line))))
           (mv (fn2-gg-insert line (- (len line) 2) (cons 32 (fn2-gg-repeat (- pad 1) 98))) row rng)))))
    (:args-overlong
     (let ((rows (fn2-gg-short-keywords (fn2-gg-select table mask :admitted)
                                        (- (nth 0 caps) (+ (nth 1 caps) 4)))))
       (if (atom rows) (mv nil nil rng)
         (mv-let (row rng) (fn2-gg-pick rows rng)
           (let ((kw (fn2-gg-str (fn2-gg-row-keyword row))))
             (mv-let (a rng) (fn2-gg-upto (+ 1 (nth 1 caps)) (- (nth 0 caps) (+ (len kw) 3)) rng)
               (mv (append kw '(32) (fn2-gg-repeat a 97) *fn2-gg-crlf*) row rng)))))))
    (:unknown
     (mv-let (n rng) (fn2-gg-upto 3 10 rng)
       (mv-let (w rng) (fn2-gg-from n *fn2-gg-alpha* rng)
         (mv-let (row line rng) (fn2-gg-base-line table caps mask :admitted nil rng)
           (let ((w (if (fn2-gg-keywordp w table) (append w '(81 81)) w))
                 (rest (nthcdr (len (fn2-gg-str (fn2-gg-row-keyword row))) line)))
             (mv (append w rest) nil rng))))))
    (:extra-arg
     (let ((rows (fn2-gg-select table mask :bounded)))
       (if (atom rows) (mv nil nil rng)
         (mv-let (row rng) (fn2-gg-pick rows rng)
           (mv-let (line ev rng) (fn2-gg-line-n row (len (fn2-gg-row-args row)) t rng)
             (declare (ignore ev))
             (mv-let (k rng) (fn2-gg-upto 1 2 rng)
               (mv (fn2-gg-insert line (- (len line) 2)
                                  (fn2-gg-join (cons nil (fn2-gg-repeat k (list 120))) '(32)))
                   row rng)))))))
    (:missing-arg
     (let ((rows (fn2-gg-select table mask :required)))
       (if (atom rows) (mv nil nil rng)
         (mv-let (row rng) (fn2-gg-pick rows rng)
           (mv-let (line ev rng) (fn2-gg-line-n row (- (fn2-gram-args-required (fn2-gg-row-args row)) 1) t rng)
             (declare (ignore ev))
             (mv line row rng))))))
    (:bad-arg
     (let ((rows (fn2-gg-select table mask :invalidable)))
       (if (atom rows) (mv nil nil rng)
         (mv-let (row rng) (fn2-gg-pick rows rng)
           (let ((args (fn2-gg-row-args row)))
             (mv-let (i rng) (fn2-gg-pick (fn2-gg-invalidable args 0) rng)
               (mv-let (bad rng) (fn2-gg-pick (cdr (assoc-eq (fn2-gg-kind (nth i args)) *fn2-gg-invalid*)) rng)
                 (mv-let (kw rng) (fn2-gg-case (fn2-gg-str (fn2-gg-row-keyword row)) rng)
                   (mv-let (tokens rng) (fn2-gg-args args (len args) t rng)
                     (let ((tokens (update-nth i (list (fn2-gg-str bad) '(:span 0 0)) tokens)))
                       (mv-let (body descs rng) (fn2-gg-place tokens (len kw) rng)
                         (declare (ignore descs))
                         (mv (append kw body *fn2-gg-crlf*) row rng))))))))))))
    (:state
     (mv-let (row line rng) (fn2-gg-base-line table caps mask :refused nil rng)
       (mv line row rng)))
    (otherwise (mv nil nil rng))))

; The item of a mutated line under SPEC.
(defun fn2-gg-line-item (class octets row spec)
  (declare (xargs :verify-guards nil))
  (let* ((s (cdr (assoc-eq class spec)))
         (outcome (nth 0 s))
         (reply (if (eq outcome :state)
                    (cdr (assoc-equal (fn2-gg-row-keyword row) (nth 1 s)))
                  (nth 1 s))))
    (and s (natp reply)
         (fn2-gg-item octets
                      (if (eq outcome :overflow) (list '(:overflow :ok))
                        (list (list :refused outcome 0 (len octets))))
                      (list reply) (and (nth 2 s) t) nil))))

; A block item with its text line J mutated by CLASS.
(defun fn2-gg-mutated-content (class rng)
  (declare (xargs :verify-guards nil))
  (mv-let (n rng) (fn2-gg-upto 1 20 rng)
    (mv-let (a rng) (fn2-gg-from n (fn2-gg-str "abcdefghij ") rng)
      (mv-let (b rng) (fn2-gg-from n (fn2-gg-str "klmnopqrst ") rng)
        (case class
          (:block-unstuffed (mv (append '(46) a '(13 10)) rng))
          (:block-nul (mv (append a '(0) b '(13 10)) rng))
          (:block-bare-cr (mv (append a '(13) b '(13 10)) rng))
          (:block-bare-lf (mv (append a b '(10)) rng))
          (otherwise (mv-let (m rng) (fn2-gg-upto 999 1040 rng) (mv (append (fn2-gg-repeat m 120) '(13 10)) rng))))))))
(defun fn2-gg-block-item (class table caps mask spec rng)
  (declare (xargs :verify-guards nil))
  (let ((rows (fn2-gg-select table mask :block))
        (outcome (nth 0 (cdr (assoc-eq class spec)))))
    (if (or (atom rows) (not outcome)) (mv nil rng)
      (mv-let (row rng) (fn2-gg-pick rows rng)
        (mv-let (line ev rng) (fn2-gg-line row caps t rng)
          (mv-let (k1 rng) (fn2-gg-upto 0 3 rng)
            (mv-let (pre pevs rng) (fn2-gg-block-lines k1 t (len line) rng)
              (mv-let (bad rng) (if (eq class :block-no-terminator) (mv nil rng) (fn2-gg-mutated-content class rng))
                (mv-let (k2 rng) (fn2-gg-upto 0 3 rng)
                  (mv-let (post qevs rng) (fn2-gg-block-lines k2 t (+ (len line) (len pre) (len bad)) rng)
                    (mv (fn2-gg-item (append line pre bad post (if (eq outcome :open) nil '(46 13 10)))
                                     (append (list ev) pevs
                                             (case outcome
                                               (:bad-line (list '(:bad-line)))
                                               (:block-overflow (list '(:block-overflow) '(:long-line)))
                                               (otherwise nil))
                                             qevs (if (eq outcome :open) nil (list '(:terminator))))
                                     (list (fn2-gg-row-first-code row)) nil (eq outcome :open))
                        rng)))))))))))

; Random byte mutations of a valid transcript (RELEASE-PLAN section 2.4:
; byte flips, truncation, insertion of CR, LF, NUL and "."), one to three.
(defun fn2-gg-random-ops (k octets rng)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (or (zp k) (atom octets)) (mv octets rng)
    (mv-let (op rng) (fn2-gg-below 4 rng)
      (mv-let (i rng) (fn2-gg-below (len octets) rng)
        (mv-let (octets rng)
          (case op
            (0 (mv-let (x rng) (fn2-gg-upto 1 255 rng) (mv (update-nth i (logxor x (nfix (nth i octets))) octets) rng)))
            (1 (mv-let (b rng) (fn2-gg-pick '(13 10 0 46 32 9 255 128) rng) (mv (fn2-gg-insert octets i (list b)) rng)))
            (2 (mv (append (take i octets) (nthcdr (+ 1 i) octets)) rng))
            (otherwise (mv (take (max 1 i) octets) rng)))
          (fn2-gg-random-ops (- k 1) octets rng))))))

; A mutated case: zero to three valid items, the mutated item, and (unless
; the block is left open) one more valid item, so that what follows a
; refusal is observed too. Nil when the mask has no row the class needs.
(defun fn2-gg-mutate (table caps seed class mask budget spec)
  (declare (xargs :verify-guards nil))
  (let ((rng (fn2-gg-rng seed)))
    (if (eq class :random)
        (mv-let (k rng) (fn2-gg-upto 1 6 rng)
          (mv-let (items rng) (fn2-gg-valid-items k table caps mask :admitted budget rng)
            (mv-let (n rng) (fn2-gg-upto 1 3 rng)
              (mv-let (octets rng) (fn2-gg-random-ops n (car (fn2-gg-assemble items nil nil nil nil nil)) rng)
                (declare (ignore rng))
                (list octets :unchecked nil :unchecked)))))
      (mv-let (item rng)
        (if (member-eq class *fn2-gg-block-classes*)
            (fn2-gg-block-item class table caps mask spec rng)
          (mv-let (octets row rng) (fn2-gg-mutated-line class table caps mask rng)
            (mv (and octets (fn2-gg-line-item class octets row spec)) rng)))
        (if (not item) nil
          (mv-let (k rng) (fn2-gg-upto 0 3 rng)
            (mv-let (pre rng) (fn2-gg-valid-items k table caps mask :plain
                                                  (nfix (- budget (+ 600 (len (car item))))) rng)
              (mv-let (post rng) (if (nth 4 item) (mv nil rng) (fn2-gg-valid-items 1 table caps mask :plain 600 rng))
                (declare (ignore rng))
                (fn2-gg-assemble (append pre (list item) post) nil nil nil nil nil)))))))))

; ------------------------------------------------------------------------
; Checking a run against a case. OBSERVED is NAME-run's result
; (reserve1 reserve2 mode events reply-octets).
(defun fn2-gg-after-lf (octets)
  (declare (xargs :verify-guards nil))
  (if (atom octets) nil (if (equal (car octets) 10) (cdr octets) (fn2-gg-after-lf (cdr octets)))))
(defthm fn2-gg-after-lf-shorter
  (implies (consp x) (< (len (fn2-gg-after-lf x)) (len x))) :rule-classes :linear)
(defun fn2-gg-reply-codes (octets acc)
  (declare (xargs :verify-guards nil :measure (len octets)))
  ; Each reply line's status code; :bad for a line that is not "DDD ...CRLF".
  (if (atom octets) (reverse acc)
    (let* ((d (take 3 octets))
           (code (if (and (equal (len d) 3) (nat-listp d)
                          (<= 48 (nth 0 d)) (<= (nth 0 d) 57) (<= 48 (nth 1 d)) (<= (nth 1 d) 57)
                          (<= 48 (nth 2 d)) (<= (nth 2 d) 57))
                     (+ (* 100 (- (nth 0 d) 48)) (* 10 (- (nth 1 d) 48)) (- (nth 2 d) 48))
                   :bad)))
      (fn2-gg-reply-codes (fn2-gg-after-lf octets) (cons code acc)))))

(defun fn2-gg-event-ok (exp obs)
  (declare (xargs :verify-guards nil))
  (if (eq (car exp) :refused)
      (and (consp obs) (eq (car obs) :command) (eq (nth 1 obs) (nth 1 exp))
           (equal (nth 16 obs) (nth 2 exp)) (equal (nth 17 obs) (nth 3 exp)) (eq (nth 18 obs) :ok))
    (equal exp obs)))
(defun fn2-gg-events-ok (exps obss)
  (declare (xargs :verify-guards nil))
  (if (atom exps) (atom obss)
    (and (consp obss) (fn2-gg-event-ok (car exps) (car obss)) (fn2-gg-events-ok (cdr exps) (cdr obss)))))

; Nil when OBSERVED meets CASE; else which part failed.
(defun fn2-gg-check (case observed)
  (declare (xargs :verify-guards nil))
  (cond ((not (equal (nth 3 case) (nth 2 observed))) :mode)
        ((not (fn2-gg-events-ok (nth 1 case) (nth 3 observed))) :events)
        ((not (equal (nth 2 case) (fn2-gg-reply-codes (nth 4 observed) nil))) :replies)
        (t nil)))

; What every run must satisfy, whatever its input: every event declared and
; well formed, every reply rendered through its type check, one reply line
; per command or overflow event, and a stop exactly where the grammar stops
; (a malformed line, an overflow, a hand-off, a pool fault).
(defun fn2-gg-event-sound (ev none n)
  (declare (xargs :verify-guards nil))
  (case (car ev)
    (:command (and (equal (len ev) 19) (fn2-gram-parse-shape-p (nth 1 ev) (nth 2 ev) (nth 3 ev) none)
                   (eq (nth 18 ev) :ok) (natp (nth 16 ev)) (natp (nth 17 ev))
                   (< (nth 16 ev) (nth 17 ev)) (<= (nth 17 ev) n)))
    (:data (and (natp (nth 1 ev)) (natp (nth 2 ev)) (<= (nth 1 ev) (nth 2 ev)) (<= (nth 2 ev) n)))
    ((:overflow :long-line) (or (and (equal (len ev) 2) (eq (nth 1 ev) :ok))
                                (and (eq (car ev) :long-line) (equal (len ev) 1))))
    ((:terminator :bad-line :block-overflow :fault) t)
    (otherwise nil)))
(defun fn2-gg-events-sound (evs none n)
  (declare (xargs :verify-guards nil))
  (if (atom evs) t (and (fn2-gg-event-sound (car evs) none n) (fn2-gg-events-sound (cdr evs) none n))))
(defun fn2-gg-replying (evs)
  (declare (xargs :verify-guards nil))
  (if (atom evs) 0
    (+ (if (or (eq (car (car evs)) :command) (and (member-eq (car (car evs)) '(:overflow :long-line)) (equal (len (car evs)) 2))) 1 0)
       (fn2-gg-replying (cdr evs)))))
(defun fn2-gg-codes-ok (codes)
  (declare (xargs :verify-guards nil))
  (if (atom codes) t (and (natp (car codes)) (<= 100 (car codes)) (< (car codes) 600) (fn2-gg-codes-ok (cdr codes)))))
(defun fn2-gg-hand-off-tag-p (tag table)
  (declare (xargs :verify-guards nil))
  (and (consp table)
       (or (and (equal (fn2-gg-row-tag (car table)) tag) (fn2-gg-row-hand-off (car table)) t)
           (fn2-gg-hand-off-tag-p tag (cdr table)))))
(defun fn2-gg-stopper-p (ev table)
  (declare (xargs :verify-guards nil))
  (or (and (eq (car ev) :command) (eq (nth 1 ev) :malformed))
      (and (eq (car ev) :command) (eq (nth 1 ev) :ok) (fn2-gg-hand-off-tag-p (nth 2 ev) table))
      (and (member-eq (car ev) '(:overflow :long-line)) (equal (len ev) 2))
      (eq (car ev) :fault)))
(defun fn2-gg-stops-ok (evs table mode)
  (declare (xargs :verify-guards nil))
  ; No event before the last stops the run, and the run is stopped iff the last does.
  (if (atom evs) (not (eq mode :stopped))
    (if (atom (cdr evs)) (iff (fn2-gg-stopper-p (car evs) table) (eq mode :stopped))
      (and (not (fn2-gg-stopper-p (car evs) table)) (fn2-gg-stops-ok (cdr evs) table mode)))))
(defun fn2-gg-sound (observed table none n)
  (declare (xargs :verify-guards nil))
  (let ((evs (nth 3 observed)) (codes (fn2-gg-reply-codes (nth 4 observed) nil)))
    (cond ((not (member-eq (nth 2 observed) '(:command :block :stopped))) :mode)
          ((not (fn2-gg-events-sound evs none n)) :shape)
          ((not (and (fn2-gg-codes-ok codes) (equal (len codes) (fn2-gg-replying evs)))) :typing)
          ((not (fn2-gg-stops-ok evs table (nth 2 observed))) :stop)
          (t nil))))

; A seeded chunking of N octets: sizes 1..CAP (the simulator's delivery
; capacity), now and then a run of single octets.
(defun fn2-gg-chunks (n cap rng)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) (mv nil rng)
    (mv-let (small rng) (fn2-gg-one-in 3 rng)
      (mv-let (k rng) (fn2-gg-upto 1 (if small 3 (min (nfix cap) n)) rng)
        (let ((k (min (max 1 k) n)))
          (mv-let (rest rng) (fn2-gg-chunks (- n k) cap rng) (mv (cons k rest) rng)))))))

; ------------------------------------------------------------------------
; DEFGRAMMAR-GENERATOR NAME: the generator table read from NAME's declared
; (:command ...) rows, and NAME-generate / NAME-mutate over it.
(defun fn2-gg-suffix (g name)
  (declare (xargs :verify-guards nil))
  (subseq (symbol-name name) (+ 1 (length (symbol-name g))) (length (symbol-name name))))
(defun fn2-gg-state-sum (g states)
  (declare (xargs :verify-guards nil))
  (if (atom states) nil (cons (fn2-gram-const g "-state-" (car states)) (fn2-gg-state-sum g (cdr states)))))
(defun fn2-gg-table-rows (g rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let ((p (cdar rows)))
      (if (not (eq (fn2-decl-get :grammar p) g)) (fn2-gg-table-rows g (cdr rows))
        (cons `(list ,(fn2-gram-const g "-command-" (fn2-gg-suffix g (caar rows)))
                     ,(fn2-decl-get :keyword p)
                     ',(fn2-decl-get :syntax p)
                     (+ 0 ,@(fn2-gg-state-sum g (fn2-decl-get :protocol-states p)))
                     ',(car (fn2-decl-get :block p))
                     ',(car (fn2-decl-get :hand-off p))
                     ,(fn2-decl-get :code (cdr (car (fn2-decl-get :replies p)))))
              (fn2-gg-table-rows g (cdr rows)))))))
(defun fn2-gg-generator-events (g world)
  (declare (xargs :verify-guards nil))
  (let ((table (fn2-gram-const g "-gen-table"))
        (caps `(list ,(fn2-gram-const g "-line-cap") ,(fn2-gram-const g "-args-cap") ,(fn2-gram-const g "-block-line-cap"))))
    `(progn
       (defconst ,table (list ,@(fn2-gg-table-rows g (fn2-decl-rows :command world))))
       ;; A valid transcript within BUDGET octets, replayable from SEED.
       (defun ,(fn2-gram-sym g "-generate") (seed mask budget)
         (declare (xargs :verify-guards nil))
         (fn2-gg-generate ,table ,caps seed mask budget))
       ;; A transcript with one line or block line mutated by CLASS, and what
       ;; SPEC says the grammar must answer; :random mutates bytes unchecked.
       (defun ,(fn2-gram-sym g "-mutate") (seed class mask budget spec)
         (declare (xargs :verify-guards nil))
         (fn2-gg-mutate ,table ,caps seed class mask budget spec)))))
(defmacro defgrammar-generator (g)
  `(make-event (value (fn2-gg-generator-events ',g (w state)))))
