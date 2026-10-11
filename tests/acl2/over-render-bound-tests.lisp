; over-render-bound-tests.lisp -- witnesses and teeth for books/over-render-bound.lisp
; (Builder O, row O1, KO8a/KO8).
;
; Fixture: four rows of fn.test, each filed within its own Newsgroups header (row 2 is
; cross-posted to fn.other, row 3 is a plain row with no column, row 4 a reclaim tombstone).
; KO8's whole implication is evaluated on it: the row hypothesis (the defun-sk) is proved,
; F (fn-scol-okp) holds, and every probe of both groups, with and without a server name, is
; within the bound.  Teeth: each of the row hypothesis, F and HDR >= the limits is removed
; once on a fixture that breaks only it, and the conclusion fails.  Not exhibited: A, the
; retained payload bound.  It governs only the two count fields (the decimals of the payload's
; length and body lines), and the bound's fixed slack (the 10-digit number field, the header's
; own field names inside HDR, the Xref allowance 12(HDR + 1)) exceeds their growth for every
; payload a fixture can hold.  (natp v) is the cursor's domain.

(in-package "ACL2")
(include-book "../../books/over-render-bound")

(defun ovrbt-crlf () (coerce '(#\Return #\Newline) 'string))
(defun ovrbt-article (newsgroups subject body)
  (fn-record-string-octets
   (concatenate 'string "Newsgroups: " newsgroups (ovrbt-crlf) "Subject: " subject (ovrbt-crlf)
                (ovrbt-crlf) body (ovrbt-crlf))))
(defconst *ovrbt-tomb* (append *fn-rcl-magic* (make-list 137 :initial-element 0)))

; A row: SPEC is (msgid payload groups kind) with KIND :column, :plain, or (:lie p), a
; column whose facts are those of the other bytes P.
(defun ovrbt-held (seq spec)
  (let* ((msgid (nth 0 spec)) (payload (nth 1 spec)) (groups (nth 2 spec)) (kind (nth 3 spec))
         (w (fn-record-make seq (+ 1 seq) (+ 1 seq) msgid payload groups "o" "s" "e" 1 5)))
    (if (eq kind :plain)
        (fn-held-plain w seq)
      (let ((facts-bytes (if (consp kind) (cadr kind) payload)))
        (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                      (fn-record-msgid w) seq (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of facts-bytes)
                      (fn-held-context-of facts-bytes nil 0) nil nil)))))

(defun ovrbt-cat-from (seq specs rows)
  (declare (xargs :measure (len specs)))
  (if (consp specs)
      (ovrbt-cat-from (+ 1 seq) (cdr specs)
                      (append rows (list (fn-cat-assign (ovrbt-held seq (car specs)) rows))))
    rows))
(defun ovrbt-arena (specs)
  (if (consp specs) (cons (nth 1 (car specs)) (ovrbt-arena (cdr specs))) nil))

(defun ovrbt-max-probe (group k top server v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix (- (+ 1 (nfix top)) (nfix k)))))
  (if (and (natp k) (<= k (nfix top)))
      (max (fn-ovr-probe-len group k server v fn-arena fn-cat)
           (ovrbt-max-probe group (+ 1 k) top server v fn-arena fn-cat))
    0))

; ---------------------------------------------------------------------------
; The fixture of record.
(defconst *ovrbt-specs*
  (list (list "<a@x>" (ovrbt-article "fn.test" "a" "A") '("fn.test") :column)
        (list "<b@x>" (ovrbt-article "fn.test,fn.other" "bb" "B") '("fn.test" "fn.other") :column)
        (list "<d@x>" (ovrbt-article "fn.test" "plain" "D") '("fn.test") :plain)
        (list "<e@x>" *ovrbt-tomb* '("fn.test") :column)))
(defconst *ovrbt-a* (ovrbt-arena *ovrbt-specs*))
(defconst *ovrbt-c* (ovrbt-cat-from 0 *ovrbt-specs* nil))
(defconst *ovrbt-server* '(110 102))   ; "nf"
(defconst *ovrbt-limits* (fn-article-limits 10 10 100))

(defthm ovrbt-rows-within-header
  (fn-ovr-rows-within-header 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*)
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-ovr-rows-within-header-necc)
           :cases ((equal (fn-ovr-rows-within-header-witness 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*) 0)
                   (equal (fn-ovr-rows-within-header-witness 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*) 1)
                   (equal (fn-ovr-rows-within-header-witness 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*) 2)
                   (equal (fn-ovr-rows-within-header-witness 100 *ovrbt-limits* *ovrbt-a* *ovrbt-c*) 3)))))

(defthm ovrbt-ko8-witness
  (and (fn-scol-okp *ovrbt-a* *ovrbt-c*)
       (fn-ovr-probes-within "fn.test" 0 6 *ovrbt-server* 6
                             (+ 2 (fn-ovr-nov-line-header-bound 100 100 *ovrbt-server*)) *ovrbt-a* *ovrbt-c*)
       (fn-ovr-probes-within "fn.other" 0 3 *ovrbt-server* 6
                             (+ 2 (fn-ovr-nov-line-header-bound 100 100 *ovrbt-server*)) *ovrbt-a* *ovrbt-c*)
       (fn-ovr-probes-within "fn.test" 0 6 nil 6
                             (+ 2 (fn-ovr-nov-line-header-bound 100 100 nil)) *ovrbt-a* *ovrbt-c*)
       ;; the probes are lines, not all empty: rows 1-3 render, row 4 (the tombstone) does not
       (< 0 (ovrbt-max-probe "fn.test" 1 3 *ovrbt-server* 6 *ovrbt-a* *ovrbt-c*))
       (equal (fn-ovr-probe-len "fn.test" 4 *ovrbt-server* 6 *ovrbt-a* *ovrbt-c*) 0))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))
; ---------------------------------------------------------------------------
; Teeth.
(defconst *ovrbt-long* (coerce (make-list 150 :initial-element #\s) 'string))

; HDR >= the limits removed: a 150-octet Subject parses under limits of 400 octets, every
; other hypothesis holds, and with HDR 0 its line is past the bound.
(defconst *ovrbt-t1-specs*
  (list (list "<a@x>" (ovrbt-article "fn.test" *ovrbt-long* "A") '("fn.test") :column)))
(defconst *ovrbt-t1a* (ovrbt-arena *ovrbt-t1-specs*))
(defconst *ovrbt-t1c* (ovrbt-cat-from 0 *ovrbt-t1-specs* nil))
(defthm ovrbt-ko8-limit-teeth
  (let ((a *ovrbt-t1a*) (c *ovrbt-t1c*) (limits (fn-article-limits 10 10 400)))
    (and (fn-scol-okp a c)
         (fn-ovr-rows-within-header 200 limits a c)
         (not (fn-ovr-probes-within "fn.test" 1 1 *ovrbt-server* 6
                                    (+ 2 (fn-ovr-nov-line-header-bound 0 200 *ovrbt-server*)) a c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scol-okp) (fn-ovr-rows-within-header-necc))
           :cases ((equal (fn-ovr-rows-within-header-witness 200 (fn-article-limits 10 10 400)
                                                             *ovrbt-t1a*
                                                             *ovrbt-t1c*)
                          0)))))

; The row hypothesis removed: twelve 60-octet groups the article's Newsgroups does not name
; (a signed article's groups come from its signed source, unchecked; C, 2026-10-10).  F and
; HDR >= the limits (40) hold; its Xref is past the bound; the row is not filed within its header.
(defun ovrbt-names (k)
  (if (zp k) nil
    (cons (concatenate 'string "fn." (coerce (make-list 57 :initial-element (code-char (+ 96 k))) 'string))
          (ovrbt-names (- k 1)))))
(defconst *ovrbt-t2-specs*
  (list (list "<a@x>" (ovrbt-article "fn.test" "a" "A") (cons "fn.test" (ovrbt-names 12)) :column)))
(defconst *ovrbt-t2a* (ovrbt-arena *ovrbt-t2-specs*))
(defconst *ovrbt-t2c* (ovrbt-cat-from 0 *ovrbt-t2-specs* nil))
(defthm ovrbt-ko8-row-teeth
  (let ((a *ovrbt-t2a*) (c *ovrbt-t2c*))
    (and (fn-scol-okp a c)
         (not (fn-o1-article-within-headerp (fn-cat-row-article 0 a c)
                                            (fn-nntp-article-bytes (fn-cat-row-article 0 a c) a)))
         (fn-article-result-okp (fn-article-parse-under (nth 0 a) (fn-article-limits 10 10 40)))
         (not (fn-ovr-probes-within "fn.test" 1 1 *ovrbt-server* 6
                                    (+ 2 (fn-ovr-nov-line-header-bound 40 100 *ovrbt-server*)) a c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-okp))))

; F removed: a column whose facts are those of other bytes (a 700-octet Subject) over a short
; article.  The row hypothesis and HDR >= the limits hold of the bytes; the line the column
; renders is past the bound; F fails.
(defconst *ovrbt-t3-specs*
  (list (list "<a@x>" (ovrbt-article "fn.test" "a" "A") '("fn.test")
              (list :lie (ovrbt-article "fn.test" (coerce (make-list 700 :initial-element #\s) 'string) "A")))))
(defconst *ovrbt-t3a* (ovrbt-arena *ovrbt-t3-specs*))
(defconst *ovrbt-t3c* (ovrbt-cat-from 0 *ovrbt-t3-specs* nil))
(defthm ovrbt-ko8-column-teeth
  (let ((a *ovrbt-t3a*) (c *ovrbt-t3c*))
    (and (not (fn-scol-okp a c))
         (fn-ovr-rows-within-header 100 (fn-article-limits 10 10 40) a c)
         (not (fn-ovr-probes-within "fn.test" 1 1 *ovrbt-server* 6
                                    (+ 2 (fn-ovr-nov-line-header-bound 40 100 *ovrbt-server*)) a c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-scol-okp) (fn-ovr-rows-within-header-necc))
           :cases ((equal (fn-ovr-rows-within-header-witness 100 (fn-article-limits 10 10 40)
                                                             *ovrbt-t3a*
                                                             *ovrbt-t3c*)
                          0)))))
