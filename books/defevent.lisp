; fn: `defevent' --- an event family's stable codes, generated (G6 pilot).
;
; A journal or log names each event kind by a small natural on disk, and the
; replay dispatches on it.  Until this book each family's table was written
; three or four times by hand: the encoder (kind -> code), the replay's
; decoder (code -> kind), the host's list of the kinds it accepts back
; (host/native/owner.lisp), and the numbers a test reads off a journal line
; (tests/test_native_slow_disk.py).  A renumbering, or a code reused for a
; new kind, would have been silent in all four.  Here the table is one form:
;
;   (defevent FAMILY
;     :version N                       ; the encoding's version (a positive
;                                      ; natural); a code changes meaning only
;                                      ; with a new version
;     :var V                           ; the encoder's formal
;     :codes ((KIND CODE) ...)         ; distinct keywords, distinct naturals
;     :otherwise D                     ; the encoder's answer off the table
;     [:reserved ((CODE NAME "why") ...)] ; codes no KIND may take, each
;                                      ; named: the family's other entries, and
;                                      ; every retired code (NAME its old kind)
;     [:recorded ((FIELD "why") ...)]  ; the entry's fields that carry recorded
;                                      ; nondeterminism (a clock reading): the
;                                      ; fold takes them from the entry, never
;                                      ; from the world
;     :encode ENC [:encode-style :cond | :case]
;     [:decode DEC :code-var C]        ; the replay's dispatch
;     [:recognizer REC])               ; the kinds, as a recognizer
;
; expands to
;
;   (defun ENC (V) (declare (xargs :guard t))
;     (cond ((eq V KIND) CODE) ... (t D)))      ; :cond (the default), or
;     (case V (KIND CODE) ... (otherwise D)))   ; :case
;   (defun DEC (C) (declare (xargs :guard t))
;     (cond ((eql C CODE) KIND) ... (t nil)))
;   (defun REC (V) (declare (xargs :guard t))
;     (and (member-eq V '(KIND ...)) t))
;   (assert-event ...)   ; the round trip, evaluated on every row: ENC then
;                        ; DEC is the identity, DEC of D and of every
;                        ; reserved code is nil, REC holds of every kind
;   (table fn-events 'FAMILY '(:version N :codes ... :reserved ... ...))
;
; so it adds no theorem: a book that replaces its hand-written table with
; this form keeps its theorem set, and the definitions it generates are the
; hand-written ones (tests/acl2/defevent-tests.lisp pins the expansion).
;
; REFUSED at expansion, by name: a missing :version, :var, :codes or
; :encode; a KIND that is not a keyword or a CODE that is not a natural; a
; repeated KIND or CODE; a CODE that is also :reserved; :otherwise equal to
; a CODE; :decode without :code-var; an unknown keyword.
;
; The registry half is tools/event_emit.py: it reads the same forms without
; evaluating them, generates planning/events.json, and refuses a change to
; a committed family's codes that its :version and :reserved do not account
; for (stable ids).
;
; No include-book, no rule: the helpers are :program mode.

(in-package "ACL2")

(defconst *fn-de-keys*
  '(:version :var :codes :otherwise :reserved :recorded :encode :encode-style
    :decode :code-var :recognizer))

(defun fn-de-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-de-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-de-keys*) (fn-de-unknown-keys (cddr kvs)))
        (t (cons (car kvs) (fn-de-unknown-keys (cddr kvs))))))

(defun fn-de-codesp (x)
  (declare (xargs :mode :program))
  ; ((KIND CODE) ...), KIND a keyword, CODE a natural
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (keywordp (car (car x)))
         (natp (cadr (car x)))
         (fn-de-codesp (cdr x)))))

(defun fn-de-whysp (x pred)
  (declare (xargs :mode :program))
  ; ((KEY "why") ...), KEY satisfying PRED (:nat or :symbol), why non-empty
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (if (eq pred :nat) (natp (car (car x))) (symbolp (car (car x))))
         (stringp (cadr (car x)))
         (< 0 (length (cadr (car x))))
         (fn-de-whysp (cdr x) pred))))

(defun fn-de-reservedp (x)
  (declare (xargs :mode :program))
  ; ((CODE NAME "why") ...), CODE a natural, NAME a keyword, why non-empty
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 3)
         (natp (car (car x)))
         (keywordp (cadr (car x)))
         (stringp (caddr (car x)))
         (< 0 (length (caddr (car x))))
         (fn-de-reservedp (cdr x)))))

(defun fn-de-codes-of (rows)
  (declare (xargs :mode :program))
  (if (atom rows) nil (cons (cadr (car rows)) (fn-de-codes-of (cdr rows)))))

(defun fn-de-refusal (family kvs)
  (declare (xargs :mode :program))
  (let ((codes (fn-de-get :codes kvs))
        (reserved (fn-de-get :reserved kvs)))
    (cond
     ((not (and (symbolp family) family)) (list :bad-family family))
     ((not (keyword-value-listp kvs)) (list :bad-options kvs))
     ((fn-de-unknown-keys kvs) (cons :unknown-keyword (fn-de-unknown-keys kvs)))
     ((not (posp (fn-de-get :version kvs))) (list :bad-version (fn-de-get :version kvs)))
     ((not (and (fn-de-get :var kvs) (symbolp (fn-de-get :var kvs))))
      (list :bad-var (fn-de-get :var kvs)))
     ((not (and (fn-de-get :encode kvs) (symbolp (fn-de-get :encode kvs))))
      (list :bad-encode (fn-de-get :encode kvs)))
     ((not (member-eq (fn-de-get :encode-style kvs) '(nil :cond :case)))
      (list :bad-encode-style (fn-de-get :encode-style kvs)))
     ((not (and (consp codes) (fn-de-codesp codes))) (list :bad-codes codes))
     ((not (no-duplicatesp-eq (strip-cars codes)))
      (list :duplicate-kind (strip-cars codes)))
     ((not (no-duplicatesp (fn-de-codes-of codes)))
      (list :duplicate-code (fn-de-codes-of codes)))
     ((not (fn-de-reservedp reserved)) (list :bad-reserved reserved))
     ((not (no-duplicatesp (strip-cars reserved)))
      (list :duplicate-reserved (strip-cars reserved)))
     ((intersectp (fn-de-codes-of codes) (strip-cars reserved))
      (list :code-is-reserved (intersection$ (fn-de-codes-of codes) (strip-cars reserved))))
     ((not (fn-de-whysp (fn-de-get :recorded kvs) :symbol))
      (list :bad-recorded (fn-de-get :recorded kvs)))
     ((member-equal (fn-de-get :otherwise kvs) (fn-de-codes-of codes))
      (list :otherwise-is-a-code (fn-de-get :otherwise kvs)))
     ((and (fn-de-get :decode kvs)
           (not (and (symbolp (fn-de-get :decode kvs))
                     (fn-de-get :code-var kvs)
                     (symbolp (fn-de-get :code-var kvs)))))
      (list :bad-decode (fn-de-get :decode kvs) (fn-de-get :code-var kvs)))
     ((and (fn-de-get :recognizer kvs) (not (symbolp (fn-de-get :recognizer kvs))))
      (list :bad-recognizer (fn-de-get :recognizer kvs)))
     (t nil))))

; -----------------------------------------------------------------------------
; The expansion.

(defun fn-de-cond-encode (var codes)
  (declare (xargs :mode :program))
  (if (atom codes)
      nil
    (cons `((eq ,var ,(car (car codes))) ,(cadr (car codes)))
          (fn-de-cond-encode var (cdr codes)))))

(defun fn-de-case-encode (codes)
  (declare (xargs :mode :program))
  (if (atom codes)
      nil
    (cons `(,(car (car codes)) ,(cadr (car codes)))
          (fn-de-case-encode (cdr codes)))))

(defun fn-de-cond-decode (var codes)
  (declare (xargs :mode :program))
  (if (atom codes)
      nil
    (cons `((eql ,var ,(cadr (car codes))) ,(car (car codes)))
          (fn-de-cond-decode var (cdr codes)))))

(defun fn-de-round-trips (enc dec rec codes)
  (declare (xargs :mode :program))
  ; one conjunct per row
  (if (atom codes)
      nil
    (let ((kind (car (car codes))) (code (cadr (car codes))))
      (append `((equal (,enc ,kind) ,code))
              (if dec `((equal (,dec ,code) ,kind)) nil)
              (if rec `((,rec ,kind)) nil)
              (fn-de-round-trips enc dec rec (cdr codes))))))

(defun fn-de-nils (dec codes)
  (declare (xargs :mode :program))
  (if (atom codes)
      nil
    (cons `(null (,dec ,(car codes))) (fn-de-nils dec (cdr codes)))))

(defun fn-de-expand (family kvs)
  (declare (xargs :mode :program))
  (let* ((var (fn-de-get :var kvs))
         (codes (fn-de-get :codes kvs))
         (enc (fn-de-get :encode kvs))
         (dec (fn-de-get :decode kvs))
         (cvar (fn-de-get :code-var kvs))
         (rec (fn-de-get :recognizer kvs))
         (otherwise (fn-de-get :otherwise kvs)))
    `(progn
       (defun ,enc (,var)
         (declare (xargs :guard t))
         ,(if (eq (fn-de-get :encode-style kvs) :case)
              `(case ,var ,@(fn-de-case-encode codes) (otherwise ,otherwise))
            `(cond ,@(fn-de-cond-encode var codes) (t ,otherwise))))
       ,@(if dec
             `((defun ,dec (,cvar)
                 (declare (xargs :guard t))
                 (cond ,@(fn-de-cond-decode cvar codes) (t nil))))
           nil)
       ,@(if rec
             `((defun ,rec (,var)
                 (declare (xargs :guard t))
                 (and (member-eq ,var ',(strip-cars codes)) t)))
           nil)
       (assert-event
        (and ,@(fn-de-round-trips enc dec rec codes)
             ,@(if dec
                   (fn-de-nils dec (cons otherwise (strip-cars (fn-de-get :reserved kvs))))
                 nil))
        :msg ,(concatenate 'string (symbol-name family) ": round trip"))
       (table fn-events ',family ',kvs))))

(defun fn-de-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:code-is-reserved (msg "code(s) ~&0 are :reserved: a reserved or retired ~
                             code is never taken by a kind."
                            (cdr reason)))
    (:duplicate-code (msg "two kinds share a code: ~x0." (cadr reason)))
    (:duplicate-kind (msg "a kind has two codes: ~x0." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-de-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))

(defmacro defevent (family &rest kvs)
  (let ((reason (fn-de-refusal family kvs)))
    (if reason
        `(make-event (er soft 'defevent "~x0: ~@1" ',family
                         ',(fn-de-refusal-text reason)))
      (fn-de-expand family kvs))))
