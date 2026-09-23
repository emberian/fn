; fn: the RFC 5322 section 3.4 mailbox-list, as RFC 5536 restricts it for
; the From header field (RFC 5536 section 3.1.2).
;
; RFC 5536 section 3.1.2: `from = "From:" SP mailbox-list CRLF', the
; mailbox-list of RFC 5322 section 3.4 under RFC 5536 section 2.1: the
; obsolete syntax of RFC 5322 section 4 is NOT conformant except <obs-phrase>
; (a display name like `John Q. Public' without quotes), and section 2.2
; makes the header character set US-ASCII.  So this recognizer accepts
;
;   mailbox-list = mailbox *("," mailbox)
;   mailbox      = name-addr / addr-spec
;   name-addr    = [display-name] angle-addr
;   angle-addr   = [CFWS] "<" addr-spec ">" [CFWS]
;   display-name = phrase             ; 1*word, or obs-phrase: word *(word / "." / CFWS)
;   addr-spec    = local-part "@" domain
;   local-part   = dot-atom / quoted-string
;   domain       = dot-atom / domain-literal
;
; with CFWS (WSP and nested comments, RFC 5322 section 3.2.2) anywhere RFC
; 5322 permits it between tokens, and nothing else: no obs-local-part, no
; obs-domain, no obs-route, no group syntax (a From is a mailbox-list, not an
; address-list), no empty list element, no octet above 126.
;
; It is two total passes over the field value the article parser already
; unfolded (books/article.lisp: folding CRLFs removed, continuation WSP kept),
; neither of which reads through the Lisp reader:
;
;   fn-mbx-lex     octets -> a list of token KINDS (the token's octets are
;                  not kept: nothing downstream needs them), or :fail.  One
;                  call per octet; comment nesting is a counter, so the work
;                  is linear in the value whatever the nesting.
;   fn-mbx-accept  the token kinds through a thirteen-state automaton.  The
;                  mailbox-list grammar over tokens is regular once CFWS has
;                  been dropped, because a comment is the only nesting.
;
; Dropping CFWS between tokens is exact for this grammar: every production
; above admits [CFWS] on both sides of each of its tokens (RFC 5322 sections
; 3.2.3, 3.2.4, 3.4, 3.4.1), and a dot-atom's interior dots cannot carry CFWS,
; which is why a run of atext and "." is ONE token here and is classified by
; its shape rather than split at its dots.
;
; The value is bounded before either pass: *fn-mbx-max-octets* is the header
; block bound of books/article.lisp, so no From the parser admits is refused
; for length alone, and nothing longer is scanned.

(in-package "ACL2")
(include-book "article-fields")

(defconst *fn-mbx-max-octets* 8192)

; -----------------------------------------------------------------------------
; Octet classes (RFC 5322 sections 3.2.1 to 3.2.4, 3.4.1).  atext is
; books/article-fields.lisp's `fn-af-atextp', the one owner of that class.

(defun fn-mbx-car (x)
  (declare (xargs :guard t))
  (if (consp x) (car x) nil))

(defun fn-mbx-cdr (x)
  (declare (xargs :guard t))
  (if (consp x) (cdr x) nil))

(defun fn-mbx-wspp (c)
  (declare (xargs :guard t))
  (or (equal c 32) (equal c 9)))

(defun fn-mbx-vcharp (c)
  (declare (xargs :guard t))
  (and (integerp c) (<= 33 c) (<= c 126)))

; ctext: %d33-39 / %d42-91 / %d93-126 (not "(", ")", "\").
(defun fn-mbx-ctextp (c)
  (declare (xargs :guard t))
  (and (fn-mbx-vcharp c) (not (equal c 40)) (not (equal c 41))
       (not (equal c 92))))

; qtext: %d33 / %d35-91 / %d93-126 (not DQUOTE, "\").
(defun fn-mbx-qtextp (c)
  (declare (xargs :guard t))
  (and (fn-mbx-vcharp c) (not (equal c 34)) (not (equal c 92))))

; dtext: %d33-90 / %d94-126 (not "[", "]", "\").
(defun fn-mbx-dtextp (c)
  (declare (xargs :guard t))
  (and (fn-mbx-vcharp c) (not (equal c 91)) (not (equal c 92))
       (not (equal c 93))))

(defun fn-mbx-run-octetp (c)
  (declare (xargs :guard t))
  (or (fn-af-atextp c) (equal c 46)))

; -----------------------------------------------------------------------------
; A run of atext and "." octets, classified by its shape.  The run record is
; (first-dot has-dot last-dot doubled):
;
;   :r  begins with "."            -- only inside an obs-phrase, never first
;   :a  no "." at all              -- an atom: a word, a local-part, a domain
;   :d  a valid dot-atom-text      -- a local-part or a domain; in a phrase,
;                                     word "." word (obs-phrase)
;   :p  begins with atext, and ends with "." or doubles one
;                                  -- only in a phrase ("Q." of "John Q. Public")

(defun fn-mbx-run-start (c)
  (declare (xargs :guard t))
  (let ((dot (equal c 46)))
    (list dot dot dot nil)))

(defun fn-mbx-run-extend (info c)
  (declare (xargs :guard t))
  (let ((first-dot (fn-mbx-car info))
        (has-dot (fn-mbx-car (fn-mbx-cdr info)))
        (last-dot (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr info))))
        (doubled (fn-mbx-car
                  (fn-mbx-cdr (fn-mbx-cdr (fn-mbx-cdr info))))))
    (if (equal c 46)
        (list first-dot t t (or doubled last-dot))
      (list first-dot has-dot nil doubled))))

(defun fn-mbx-run-token (info)
  (declare (xargs :guard t))
  (let ((first-dot (fn-mbx-car info))
        (has-dot (fn-mbx-car (fn-mbx-cdr info)))
        (last-dot (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr info))))
        (doubled (fn-mbx-car
                  (fn-mbx-cdr (fn-mbx-cdr (fn-mbx-cdr info))))))
    (cond (first-dot :r)
          ((not has-dot) :a)
          ((or last-dot doubled) :p)
          (t :d))))

; -----------------------------------------------------------------------------
; The lexer.  Modes: :base, :run, :qs (inside a quoted-string), :qs-esc (after
; its "\"), :comment, :comment-esc, :dl (inside a domain-literal).  `depth'
; is the comment nesting.  `acc' is the token kinds, most recent first.

; What one octet does in :base, or at the end of a run: (mode depth info
; token), token nil when nothing is emitted, or :fail.
(defun fn-mbx-base-step (c)
  (declare (xargs :guard t))
  (cond ((fn-mbx-wspp c) (list :base 0 nil nil))
        ((equal c 40) (list :comment 1 nil nil))
        ((equal c 34) (list :qs 0 nil nil))
        ((equal c 91) (list :dl 0 nil nil))
        ((equal c 60) (list :base 0 nil :lt))
        ((equal c 62) (list :base 0 nil :gt))
        ((equal c 64) (list :base 0 nil :at))
        ((equal c 44) (list :base 0 nil :comma))
        ((fn-mbx-run-octetp c) (list :run 0 (fn-mbx-run-start c) nil))
        (t :fail)))

(defun fn-mbx-rev-onto (xs acc)
  (declare (xargs :guard t))
  (if (consp xs) (fn-mbx-rev-onto (cdr xs) (cons (car xs) acc)) acc))

(defun fn-mbx-lex (x mode depth info acc)
  (declare (xargs :guard t :measure (acl2-count x)))
  (if (atom x)
      (cond ((equal mode :base) (fn-mbx-rev-onto acc nil))
            ((equal mode :run)
             (fn-mbx-rev-onto (cons (fn-mbx-run-token info) acc) nil))
            (t :fail))
    (let ((c (car x)) (rest (cdr x)))
      (cond
       ((equal mode :qs)
        (cond ((equal c 34) (fn-mbx-lex rest :base 0 nil (cons :q acc)))
              ((equal c 92) (fn-mbx-lex rest :qs-esc 0 nil acc))
              ((or (fn-mbx-qtextp c) (fn-mbx-wspp c))
               (fn-mbx-lex rest :qs 0 nil acc))
              (t :fail)))
       ((equal mode :qs-esc)
        (if (or (fn-mbx-vcharp c) (fn-mbx-wspp c))
            (fn-mbx-lex rest :qs 0 nil acc)
          :fail))
       ((equal mode :comment)
        (cond ((equal c 40) (fn-mbx-lex rest :comment (+ 1 (nfix depth)) nil acc))
              ((equal c 41)
               (if (<= (nfix depth) 1)
                   (fn-mbx-lex rest :base 0 nil acc)
                 (fn-mbx-lex rest :comment (- (nfix depth) 1) nil acc)))
              ((equal c 92) (fn-mbx-lex rest :comment-esc depth nil acc))
              ((or (fn-mbx-ctextp c) (fn-mbx-wspp c))
               (fn-mbx-lex rest :comment depth nil acc))
              (t :fail)))
       ((equal mode :comment-esc)
        (if (or (fn-mbx-vcharp c) (fn-mbx-wspp c))
            (fn-mbx-lex rest :comment depth nil acc)
          :fail))
       ((equal mode :dl)
        (cond ((equal c 93) (fn-mbx-lex rest :base 0 nil (cons :l acc)))
              ((or (fn-mbx-dtextp c) (fn-mbx-wspp c))
               (fn-mbx-lex rest :dl 0 nil acc))
              (t :fail)))
       ((and (equal mode :run) (fn-mbx-run-octetp c))
        (fn-mbx-lex rest :run 0 (fn-mbx-run-extend info c) acc))
       (t
        ; :base, or a run that ends at this octet: the run's token first,
        ; then this octet read as :base reads it.
        (let ((acc (if (equal mode :run) (cons (fn-mbx-run-token info) acc) acc))
              (s (fn-mbx-base-step c)))
          (if (atom s)
              :fail
            (fn-mbx-lex rest (fn-mbx-car s) (fn-mbx-car (fn-mbx-cdr s))
                        (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr s)))
                        (if (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr (fn-mbx-cdr s))))
                            (cons (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr (fn-mbx-cdr s))))
                                  acc)
                          acc)))))))))

; -----------------------------------------------------------------------------
; The automaton over token kinds.
;
;   :s0    a mailbox begins
;   :s1    one word or dot-atom read: a local-part or the start of a phrase
;   :s3    a phrase of which no prefix can be a local-part
;   :dom   after the "@" of a bare addr-spec
;   :de    a bare addr-spec is complete                      (accepting)
;   :al    after "<"
;   :al1   the angle-addr's local-part read
;   :ad    after its "@"
;   :ad1   its domain read
;   :after the angle-addr is closed                          (accepting)

(defun fn-mbx-wordp (k)
  (declare (xargs :guard t))
  (or (equal k :a) (equal k :q)))

(defun fn-mbx-phrase-tokenp (k)
  (declare (xargs :guard t))
  (or (equal k :a) (equal k :q) (equal k :d) (equal k :p) (equal k :r)))

(defun fn-mbx-domain-tokenp (k)
  (declare (xargs :guard t))
  (or (equal k :a) (equal k :d) (equal k :l)))

(defun fn-mbx-next (st k)
  (declare (xargs :guard t))
  (cond
   ((equal st :s0)
    (cond ((or (fn-mbx-wordp k) (equal k :d)) :s1)
          ((equal k :p) :s3)
          ((equal k :lt) :al)
          (t :fail)))
   ((equal st :s1)
    (cond ((equal k :at) :dom)
          ((equal k :lt) :al)
          ((fn-mbx-phrase-tokenp k) :s3)
          (t :fail)))
   ((equal st :s3)
    (cond ((fn-mbx-phrase-tokenp k) :s3)
          ((equal k :lt) :al)
          (t :fail)))
   ((equal st :dom) (if (fn-mbx-domain-tokenp k) :de :fail))
   ((equal st :de) (if (equal k :comma) :s0 :fail))
   ((equal st :al) (if (or (fn-mbx-wordp k) (equal k :d)) :al1 :fail))
   ((equal st :al1) (if (equal k :at) :ad :fail))
   ((equal st :ad) (if (fn-mbx-domain-tokenp k) :ad1 :fail))
   ((equal st :ad1) (if (equal k :gt) :after :fail))
   ((equal st :after) (if (equal k :comma) :s0 :fail))
   (t :fail)))

(defun fn-mbx-accept (toks st)
  (declare (xargs :guard t))
  (if (consp toks)
      (let ((next (fn-mbx-next st (car toks))))
        (and (not (equal next :fail))
             (fn-mbx-accept (cdr toks) next)))
    (or (equal st :de) (equal st :after))))

; -----------------------------------------------------------------------------
; The recognizer.  `value' is a field value as books/article.lisp unfolds it.

(defun fn-mbx-mailbox-listp (value)
  (declare (xargs :guard t))
  (and (<= (len value) *fn-mbx-max-octets*)
       (let ((toks (fn-mbx-lex value :base 0 nil nil)))
         (and (not (equal toks :fail))
              (fn-mbx-accept toks :s0)))))

; -----------------------------------------------------------------------------
; What an accepted value is.
;
; Every mailbox carries an addr-spec, so every accepted value carries its
; "@" (octet 64).  `From: yue' has none, which is the defect of 2026-09-22
; (planning/evidence/agents-on-hbox-2026-09-22.md) stated as a property.
;
; The automaton half: from any state before an addr-spec's "@", acceptance
; passes an :at token.

(defun fn-mbx-before-at-statep (st)
  (declare (xargs :guard t))
  (or (equal st :s0) (equal st :s1) (equal st :s3)
      (equal st :al) (equal st :al1)))

(local
 (defthm fn-mbx-accept-from-before-at-reads-an-at
   (implies (and (fn-mbx-accept toks st)
                 (fn-mbx-before-at-statep st))
            (member-equal :at toks))))

; The lexer half: an :at token is emitted only for an "@" octet.
(local
 (defthm fn-mbx-member-of-rev-onto
   (iff (member-equal k (fn-mbx-rev-onto xs acc))
        (or (member-equal k xs) (member-equal k acc)))
   :hints (("Goal" :induct (fn-mbx-rev-onto xs acc)))))

(local
 (defthm fn-mbx-run-token-is-not-at
   (not (equal (fn-mbx-run-token info) :at))
   :hints (("Goal" :in-theory (enable fn-mbx-run-token)))))

(local
 (defthm fn-mbx-base-step-emits-at-only-for-64
   (implies (not (equal c 64))
            (not (equal (fn-mbx-car (fn-mbx-cdr (fn-mbx-cdr (fn-mbx-cdr
                                                             (fn-mbx-base-step c)))))
                        :at)))
   :hints (("Goal" :in-theory (enable fn-mbx-base-step fn-mbx-car fn-mbx-cdr)))))

(local
 (defthm fn-mbx-lex-emits-at-only-for-an-at-octet
   (implies (and (not (equal (fn-mbx-lex x mode depth info acc) :fail))
                 (member-equal :at (fn-mbx-lex x mode depth info acc)))
            (or (member-equal :at acc) (member-equal 64 x)))
   :hints (("Goal" :induct (fn-mbx-lex x mode depth info acc)
            :in-theory (disable fn-mbx-base-step fn-mbx-run-token
                                fn-mbx-run-extend fn-mbx-car fn-mbx-cdr
                                fn-mbx-qtextp fn-mbx-ctextp fn-mbx-dtextp
                                fn-mbx-vcharp fn-mbx-wspp fn-mbx-run-octetp)))))

(defthm fn-mbx-mailbox-list-names-an-address
  (implies (fn-mbx-mailbox-listp value)
           (member-equal 64 value))
  :hints (("Goal" :in-theory (disable fn-mbx-lex fn-mbx-accept)
           :use ((:instance fn-mbx-accept-from-before-at-reads-an-at
                            (toks (fn-mbx-lex value :base 0 nil nil))
                            (st :s0))
                 (:instance fn-mbx-lex-emits-at-only-for-an-at-octet
                            (x value) (mode :base) (depth 0) (info nil)
                            (acc nil))))))

(deftheory fn-mbx-vocabulary
  '((:d fn-mbx-car) (:d fn-mbx-cdr) (:d fn-mbx-wspp) (:d fn-mbx-vcharp)
    (:d fn-mbx-ctextp) (:d fn-mbx-qtextp) (:d fn-mbx-dtextp)
    (:d fn-mbx-run-octetp) (:d fn-mbx-run-start) (:d fn-mbx-run-extend)
    (:d fn-mbx-run-token) (:d fn-mbx-base-step) (:d fn-mbx-rev-onto)
    (:d fn-mbx-lex) (:d fn-mbx-wordp) (:d fn-mbx-phrase-tokenp)
    (:d fn-mbx-domain-tokenp) (:d fn-mbx-next) (:d fn-mbx-accept)
    (:d fn-mbx-before-at-statep) (:d fn-mbx-mailbox-listp)))

(in-theory (disable fn-mbx-vocabulary))
