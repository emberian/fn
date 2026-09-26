; fn: teeth for books/catalog-record.lisp (wave 5, lane catalog-slice).
;
; What this book is evidence FOR.  `fn-cat-intern-list-materializes' says
; alpha of intern is the identity on a wire record: the held record built
; from W, materialized by handle from the arena the intern sealed, is W.
; `fn-cat-intern-is-intern-list' says the buffer intern and the list intern
; build the same held record (no hypothesis).  `fn-hf-split-index-is-split-
; article', `fn-hf-crlf-count-is-crlf-lines' and `fn-hf-body-lines-of-is-
; nov-body-line-count-by-definition' say the byte facts are the served
; machine's split and line count.  Each gets a ground positive witness
; asserting its complete antecedent and conclusion, and for each hypothesis
; a witness on which the retained hypotheses hold, the omitted one fails
; and the conclusion fails, with a `must-fail' of the conclusion.  The exec
; path is run on a live local arena and a live local octet buffer.

(in-package "ACL2")
(include-book "../../books/catalog-record")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-hf-split-index (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hf-crlf-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-hf-body-lines-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-held-facts-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-held-context-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-held-wire (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-held-wire-of (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-intern-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-cat-intern (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; Ground values: an article "Subject: a" CRLF CRLF "line1" CRLF "line2" CRLF,
; whose body starts at 14 and has two lines; the same with a non-octet in
; its body; a wire record carrying it.

(defconst *crt-art*
  (append (fn-record-string-octets "Subject: a") '(13 10 13 10)
          (fn-record-string-octets "line1") '(13 10)
          (fn-record-string-octets "line2") '(13 10)))
(defconst *crt-body* (nthcdr 14 *crt-art*))
(defconst *crt-art-bad* (append (take 14 *crt-art*) '(300 13 10)))
(defconst *crt-body-bad* (nthcdr 14 *crt-art-bad*))

(defconst *crt-w*
  (fn-record-make 0 1 0 "<a@x>" *crt-art* '("fn.test") "o" "s" "e" 1 5))

(assert-event (and (fn-octet-listp *crt-art*) (fn-record-p *crt-w*)
                   (fn-prin-keyringp nil)))

; -----------------------------------------------------------------------------
; The split: positive witness, complete antecedent and conclusion.
(defthm crt-w-split
  (and (fn-octet-listp *crt-art*)
       (equal (fn-nntp-split-okp (fn-nntp-split-article *crt-art*))
              (if (fn-hf-split-index *crt-art* 0) t nil))
       (equal (fn-hf-split-index *crt-art* 0) 14)
       (equal (fn-nntp-split-body (fn-nntp-split-article *crt-art*))
              (nthcdr (fn-hf-split-index *crt-art* 0) *crt-art*)))
  :rule-classes nil)

; Without the octet hypothesis: the index is found, the machine refuses.
(defthm crt-w-split-without-octets
  (and (not (fn-octet-listp *crt-art-bad*))
       (equal (fn-hf-split-index *crt-art-bad* 0) 14)
       (not (equal (fn-nntp-split-okp (fn-nntp-split-article *crt-art-bad*))
                   (if (fn-hf-split-index *crt-art-bad* 0) t nil))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-split-without-octets
   (equal (fn-nntp-split-okp (fn-nntp-split-article *crt-art-bad*))
          (if (fn-hf-split-index *crt-art-bad* 0) t nil))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The line count.
(defthm crt-w-lines
  (and (fn-octet-listp *crt-body*)
       (equal (fn-hf-crlf-count *crt-body* nil) 2)
       (equal (equal (car (fn-nntp-crlf-lines *crt-body*)) :ok)
              (if (fn-hf-crlf-count *crt-body* nil) t nil))
       (equal (len (car (cdr (fn-nntp-crlf-lines *crt-body*))))
              (fn-hf-crlf-count *crt-body* nil)))
  :rule-classes nil)

(defthm crt-w-lines-without-octets
  (and (not (fn-octet-listp *crt-body-bad*))
       (equal (fn-hf-crlf-count *crt-body-bad* nil) 1)
       (not (equal (equal (car (fn-nntp-crlf-lines *crt-body-bad*)) :ok)
                   (if (fn-hf-crlf-count *crt-body-bad* nil) t nil))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-lines-without-octets
   (equal (equal (car (fn-nntp-crlf-lines *crt-body-bad*)) :ok)
          (if (fn-hf-crlf-count *crt-body-bad* nil) t nil))
   :rule-classes nil))

; The column is fn-nov-body-line-count's expression.
(defthm crt-w-body-lines
  (and (fn-octet-listp *crt-art*)
       (equal (fn-hf-body-lines-of *crt-art*) 2)
       (equal (fn-hf-body-lines-of *crt-art*)
              (let ((split (fn-nntp-split-article *crt-art*)))
                (if (fn-nntp-split-okp split)
                    (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
                      (if (equal (car lines) :ok) (len (car (cdr lines))) 0))
                  0))))
  :rule-classes nil)

(defthm crt-w-body-lines-without-octets
  (and (not (fn-octet-listp *crt-art-bad*))
       (equal (fn-hf-body-lines-of *crt-art-bad*) 1)
       (not (equal (fn-hf-body-lines-of *crt-art-bad*)
                   (let ((split (fn-nntp-split-article *crt-art-bad*)))
                     (if (fn-nntp-split-okp split)
                         (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
                           (if (equal (car lines) :ok) (len (car (cdr lines))) 0))
                       0)))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-body-lines-without-octets
   (equal (fn-hf-body-lines-of *crt-art-bad*)
          (let ((split (fn-nntp-split-article *crt-art-bad*)))
            (if (fn-nntp-split-okp split)
                (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
                  (if (equal (car lines) :ok) (len (car (cdr lines))) 0))
              0)))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; Materialization: alpha of intern is the identity on the wire record.  The
; arena is the logical value nil (empty); the intern seals handle 0.
(defthm crt-w-materializes
  (and (fn-record-shapep *crt-w*)
       (mv-let (held fn-arena)
         (fn-cat-intern-list *crt-w* nil 0 nil)
         (and (fn-held-p held)
              (equal (fn-record-payload held) 0)
              (equal (fn-held-facts held) (list (len *crt-art*) 14 2))
              (equal (fn-hc-generation (fn-held-context held)) 0)
              (equal fn-arena (list *crt-art*))
              (equal (fn-held-wire-of held fn-arena) *crt-w*))))
  :rule-classes nil)

; Without the shape: a twelve-element tuple materializes to eleven.
(defconst *crt-w12* (append *crt-w* '(:extra)))
(defthm crt-w-materializes-without-shape
  (and (not (fn-record-shapep *crt-w12*))
       (mv-let (held fn-arena)
         (fn-cat-intern-list *crt-w12* nil 0 nil)
         (not (equal (fn-held-wire-of held fn-arena) *crt-w12*))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-materializes-without-shape
   (mv-let (held fn-arena)
     (fn-cat-intern-list *crt-w12* nil 0 nil)
     (equal (fn-held-wire-of held fn-arena) *crt-w12*))
   :rule-classes nil))

; fn-held-p-of-intern-list: without fn-record-p (a numeric Message-ID), and
; without a natural generation.
(defconst *crt-w-badid*
  (fn-record-make 0 1 0 7 *crt-art* '("fn.test") "o" "s" "e" 1 5))
(defthm crt-w-held-p
  (and (fn-record-p *crt-w*) (natp 0)
       (fn-held-p (mv-nth 0 (fn-cat-intern-list *crt-w* nil 0 nil))))
  :rule-classes nil)
(defthm crt-w-held-p-without-record-p
  (and (not (fn-record-p *crt-w-badid*)) (natp 0)
       (not (fn-held-p (mv-nth 0 (fn-cat-intern-list *crt-w-badid* nil 0 nil)))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-held-p-without-record-p
   (fn-held-p (mv-nth 0 (fn-cat-intern-list *crt-w-badid* nil 0 nil)))
   :rule-classes nil))
(defthm crt-w-held-p-without-generation
  (and (fn-record-p *crt-w*) (not (natp -1))
       (not (fn-held-p (mv-nth 0 (fn-cat-intern-list *crt-w* nil -1 nil)))))
  :rule-classes nil)
(must-fail
 (defthm crt-r-held-p-without-generation
   (fn-held-p (mv-nth 0 (fn-cat-intern-list *crt-w* nil -1 nil)))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; The executable path: the buffer intern on a live arena and a live buffer
; equals the list intern of the same wire record; the handle reads back.
(defun crt-exec-run (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (let* ((fn-arena (fn-arena-clear fn-arena)))
    (mv-let (held1 fn-arena)
      (fn-cat-intern-list *crt-w* nil 0 fn-arena)
      (mv-let (held2 fn-arena)
        (with-local-stobj fn-octets
          (mv-let (held2 fn-arena fn-octets)
            (let ((fn-octets (fn-octets-from-list *crt-art* fn-octets)))
              (mv-let (held2 fn-arena)
                (fn-cat-intern *crt-w* fn-octets nil 0 fn-arena)
                (mv held2 fn-arena fn-octets)))
            (mv held2 fn-arena)))
        (mv (list (fn-arena-count fn-arena)
                  (fn-record-payload held1) (fn-record-payload held2)
                  (equal (fn-held-wire-of held1 fn-arena) *crt-w*)
                  (equal (fn-held-wire-of held2 fn-arena) *crt-w*)
                  (equal (fn-held-facts held1) (fn-held-facts held2))
                  (equal (fn-held-context held1) (fn-held-context held2))
                  (fn-held-facts held1))
            fn-arena)))))

(defun crt-exec ()
  (with-local-stobj fn-arena
    (mv-let (result fn-arena) (crt-exec-run fn-arena) result)))

(assert-event (equal (crt-exec) (list 2 0 1 t t t t (list (len *crt-art*) 14 2))))
