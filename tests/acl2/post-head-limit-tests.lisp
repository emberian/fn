; Teeth for the POST head limit keystone books/post-head-limit.lisp
; fn-adm-source-head-within-the-head-limit, over the limits form the keystone
; reduces to (fn-adm-hl-under): the bound is attained (not slack), one octet
; less of limit refuses the parse, the at-least-one-header-line hypothesis has
; a violating value (a headerless source whose first CR LF CR LF lies past the
; bound), and a deterministic sweep of generated sources never violates the
; bound.  Each is an `assert-event' on a concrete value; none is a negated
; `must-fail' (that proves only that the prover failed).

(in-package "ACL2")
(include-book "../../books/post-head-limit")


(defun hlt-codes (l)
  (declare (xargs :guard (character-listp l) :verify-guards nil))
  (if (endp l) nil (cons (char-code (car l)) (hlt-codes (cdr l)))))

; One header line "Newsgroups: a" (13 octets), its CRLF, the empty line, a body.
(defconst *hlt-src*
  (append (hlt-codes (coerce "Newsgroups: a" 'list)) '(13 10 13 10)
          (hlt-codes (coerce "body" 'list)) '(13 10)))
; Header octets counted by the parse: 13 + 2.
(defconst *hlt-lim* (fn-article-limits 64 256 15))

; 1. Satisfiable: the hypotheses hold and the bound is attained (head end 17
;    = 2 + 15).
(assert-event (fn-article-result-okp (fn-article-parse-under *hlt-src* *hlt-lim*)))
(assert-event (consp (fn-article-header
                      (fn-article-result-article
                       (fn-article-parse-under *hlt-src* *hlt-lim*)))))
(assert-event (equal (fn-adm-head-end *hlt-src* 0) 17))
(assert-event (equal (+ 2 (fn-article-limit-octets *hlt-lim*)) 17))

; 2. Tight: one octet less of limit refuses the parse, so the premise fails
;    exactly where the bound would.
(assert-event (not (fn-article-result-okp
                    (fn-article-parse-under *hlt-src* (fn-article-limits 64 256 14)))))

; 3. Teeth of the at-least-one-line hypothesis: a source that parses with an
;    empty header (its first line is the empty line) and holds CR LF CR LF
;    far out; the head end is 46, past the bound 17.
(defconst *hlt-nohdr*
  (append '(13 10) (make-list 40 :initial-element 120) '(13 10 13 10)))
(assert-event (fn-article-result-okp (fn-article-parse-under *hlt-nohdr* *hlt-lim*)))
(assert-event (not (consp (fn-article-header
                           (fn-article-result-article
                            (fn-article-parse-under *hlt-nohdr* *hlt-lim*))))))
(assert-event (equal (fn-adm-head-end *hlt-nohdr* 0) 46))
(assert-event (< 17 (fn-adm-head-end *hlt-nohdr* 0)))

; 4. Sweep: N header lines (some folded) of varied value length, limits equal
;    to the header octets and 50 wider; the conclusion holds on every ok parse,
;    and a count of ok parses shows the sweep is not vacuous.
(defun hlt-prop (src lim)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-article-parse-under src lim)))
    (implies (and (fn-article-result-okp r)
                  (consp (fn-article-header (fn-article-result-article r))))
             (and (fn-adm-head-end src 0)
                  (<= (fn-adm-head-end src 0) (+ 2 (fn-article-limit-octets lim)))))))

(defun hlt-line (k v foldp)
  (declare (xargs :guard (and (natp k) (natp v)) :verify-guards nil))
  (append (if foldp '(32) (list 88 (+ 97 (mod k 26)) 58 32))
          (make-list (+ 1 v) :initial-element 118) '(13 10)))
(defun hlt-head (n v)
  (declare (xargs :guard (and (natp n) (natp v)) :verify-guards nil))
  (if (zp n) nil
    (append (hlt-line n (mod (* n v) 37) (and (> n 1) (equal (mod n 3) 0)))
            (hlt-head (- n 1) v))))
(defun hlt-src (n v)
  (declare (xargs :guard (and (natp n) (natp v)) :verify-guards nil))
  (append (hlt-head n v) '(13 10 98 13 10 13 10 98)))

; Returns (ok-count . violations) over v = 1..V for fixed N.
(defun hlt-row (n v ok bad)
  (declare (xargs :guard (and (natp n) (natp v) (natp ok) (true-listp bad)) :verify-guards nil))
  (if (zp v) (cons ok bad)
    (let* ((src (hlt-src n v))
           (hb (len (hlt-head n v)))
           (okp (fn-article-result-okp
                 (fn-article-parse-under src (fn-article-limits 64 256 hb)))))
      (hlt-row n (- v 1)
               (if okp (+ 1 ok) ok)
               (append (if (hlt-prop src (fn-article-limits 64 256 hb)) nil (list (list n v hb)))
                       (if (hlt-prop src (fn-article-limits 64 256 (+ hb 50))) nil (list (list n v :wide)))
                       bad)))))
(defun hlt-sweep (n v ok bad)
  (declare (xargs :guard (and (natp n) (natp v) (natp ok) (true-listp bad)) :verify-guards nil))
  (if (zp n) (cons ok bad)
    (let ((row (hlt-row n v 0 nil)))
      (hlt-sweep (- n 1) v (+ ok (car row)) (append (cdr row) bad)))))

(assert-event (equal (cdr (hlt-sweep 30 40 0 nil)) nil))
(assert-event (< 0 (car (hlt-sweep 30 40 0 nil))))
