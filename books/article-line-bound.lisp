; fn: the article parser's line bound, named (PKT-506).
;
; RFC 5322 section 2.1.1: "Each line of characters MUST be no more than 998
; characters ... excluding the CRLF" (RFC 5536 section 2.1 applies RFC 5322
; to articles).  It bounds a LINE, never a field or the data: a header field
; of any length is carried folded (RFC 5322 section 2.2.3), each physical line
; within the bound, up to the store profile's header limits (PRF-230,
; books/article.lisp `*fn-article-default-limits*').  The parser refuses a
; longer line with the code :limit (books/article.lisp
; fn-article-next-line-aux, whose fuel is *fn-article-max-line-octets*).  The
; other :limit the parser answers is its preflight, an input over the codec
; ceiling *fn-article-max-octets*.
;
; This book states what a :limit refusal means, so the injection agent can
; name it (books/injection.lisp fn-inj-parse-refusal):
;   fn-article-next-line-limit-is-a-long-line: a line refused :limit has at
;     least 999 octets before any CR or LF;
;   fn-article-parse-under-limit-is-a-long-header-line (KEYSTONE): within the
;     ceiling, a parse refused :limit met such a line among the header's
;     lines (fn-alb-long-header-linep), under any header limits.
(in-package "ACL2")
(include-book "article")

; The first N octets of OCTETS exist and none is a CR or LF: a line of at
; least N octets starts here.
(defun fn-alb-line-run-p (octets n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      t
    (and (consp octets)
         (not (equal (car octets) 13))
         (not (equal (car octets) 10))
         (fn-alb-line-run-p (cdr octets) (1- n)))))

; The header's physical lines, read as the parser reads them (one
; fn-article-next-line per line, up to the blank line): some line is longer
; than the RFC's 998 octets.  LINES-LEFT bounds the walk as the parser's does.
(defun fn-alb-long-header-linep (octets lines-left)
  (declare (xargs :guard (natp lines-left)
                  :measure (nfix lines-left)))
  (if (zp lines-left)
      nil
    (let ((next (fn-article-next-line octets)))
      (if (fn-article-line-okp next)
          (and (consp (fn-article-line-value next))
               (fn-alb-long-header-linep (fn-article-line-rest next)
                                         (1- lines-left)))
        (fn-alb-line-run-p octets (+ 1 *fn-article-max-line-octets*))))))

(local
 (defthm fn-alb-next-line-aux-limit
   (implies (and (natp left)
                 (equal (fn-article-next-line-aux octets line-rev left)
                        '(:error :limit)))
            (fn-alb-line-run-p octets (+ 1 left)))
   :hints (("Goal" :induct (fn-article-next-line-aux octets line-rev left)
            :in-theory (enable fn-article-next-line-aux fn-article-error)))))

(defthm fn-article-next-line-limit-is-a-long-line
  (implies (equal (fn-article-next-line octets) '(:error :limit))
           (fn-alb-line-run-p octets (+ 1 *fn-article-max-line-octets*)))
  :hints (("Goal" :in-theory (enable fn-article-next-line))))

; A refusal the header's field syntax gives is never :limit.
(local
 (defthm fn-alb-split-colon-code
   (not (equal (fn-article-split-colon-aux line name-rev) '(:error :limit)))
   :hints (("Goal" :in-theory (enable fn-article-split-colon-aux fn-article-error)))))

(local
 (defthm fn-alb-new-field-not-limit
   (not (equal (fn-article-new-field line) '(:error :limit)))
   :hints (("Goal" :in-theory (enable fn-article-new-field fn-article-error
                                      fn-article-split-colon-aux)
            :use ((:instance fn-alb-split-colon-code (name-rev nil)))))))

; A line the parser reads is a list; a non-empty one is a cons.
(local
 (defthm fn-alb-next-line-aux-value-true-listp
   (implies (and (true-listp line-rev)
                 (fn-article-line-okp (fn-article-next-line-aux octets line-rev left)))
            (true-listp (fn-article-line-value
                         (fn-article-next-line-aux octets line-rev left))))
   :hints (("Goal" :in-theory (enable fn-article-next-line-aux fn-article-error
                                      fn-article-line-okp fn-article-line-value)))))

(local
 (defthm fn-alb-next-line-value-true-listp
   (implies (fn-article-line-okp (fn-article-next-line octets))
            (true-listp (fn-article-line-value (fn-article-next-line octets))))
   :hints (("Goal" :in-theory (e/d (fn-article-next-line)
                                   (fn-article-next-line-aux fn-article-line-okp
                                    fn-article-line-value))
            :use ((:instance fn-alb-next-line-aux-value-true-listp
                             (line-rev nil) (left 998)))))))

(local
 (defthm fn-alb-next-line-value-consp
   (implies (and (fn-article-line-okp (fn-article-next-line octets))
                 (fn-article-line-value (fn-article-next-line octets)))
            (consp (fn-article-line-value (fn-article-next-line octets))))
   :hints (("Goal" :use fn-alb-next-line-value-true-listp
            :in-theory (disable fn-alb-next-line-value-true-listp fn-article-next-line
                                fn-article-line-okp fn-article-line-value)))))

; The header walk: a :limit from any step is a long line at that step.
(local
 (defthm fn-alb-parse-lines-limit
   (implies (equal (fn-article-parse-lines octets limits lines-left header-bytes
                                           nfields fields-rev current header-rev)
                   '(:error :limit))
            (fn-alb-long-header-linep octets lines-left))
   :hints (("Goal" :induct (fn-article-parse-lines octets limits lines-left header-bytes
                                                   nfields fields-rev current header-rev)
            :in-theory (e/d (fn-article-parse-lines fn-article-error fn-article-ok)
                            (fn-article-next-line fn-article-new-field
                             fn-article-add-fold fn-article-fold-linep
                             fn-article-body-crlfp fn-article-make
                             fn-article-header-rev-add-line
                             fn-article-finish-fields fn-article-line-okp
                             fn-article-line-value fn-article-line-rest
                             fn-article-limit-octets fn-article-limit-fields
                             fn-article-wspp))
            :expand ((fn-alb-long-header-linep octets lines-left))))))

;; KEYSTONE.  Within the codec ceiling, a parse refused :limit met a header
;; line longer than RFC 5322 section 2.1.1's 998 octets, whatever the header
;; LIMITS (their refusals are named :header-*-limit).  Subject:
;; fn-article-parse-under, which books/injection.lisp fn-inj-decide runs
;; (through fn-article-parse) on every POST and operator article
;; (fn-inj-parse-refusal names the refusal :line-length).
(defthm fn-article-parse-under-limit-is-a-long-header-line
  (implies (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
                (equal (fn-article-parse-under octets limits) '(:error :limit)))
           (fn-alb-long-header-linep octets
                                     (1+ (fn-article-limit-lines limits))))
  :hints (("Goal" :in-theory (e/d (fn-article-parse-under fn-article-error)
                                  (fn-article-parse-lines fn-alb-long-header-linep
                                   fn-cbor-at-mostp fn-cbor-octet-listp))
           :use ((:instance fn-alb-parse-lines-limit
                            (lines-left (1+ (fn-article-limit-lines limits)))
                            (header-bytes 0) (nfields 0) (fields-rev nil)
                            (current nil) (header-rev nil))))))

; The same for the reader's parse (the ceiling limits), which
; books/injection.lisp fn-inj-decide runs.
(defthm fn-article-parse-limit-is-a-long-header-line
  (implies (and (fn-cbor-at-mostp octets *fn-article-max-octets*)
                (equal (fn-article-parse octets) '(:error :limit)))
           (fn-alb-long-header-linep octets (1+ *fn-article-max-octets*)))
  :hints (("Goal" :in-theory (e/d (fn-article-parse)
                                  (fn-article-parse-under fn-alb-long-header-linep
                                   fn-cbor-at-mostp))
           :use ((:instance fn-article-parse-under-limit-is-a-long-header-line
                            (limits *fn-article-ceiling-limits*))))))
