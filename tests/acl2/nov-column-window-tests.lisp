(in-package "ACL2")
(include-book "../../books/nov-column-window")
(include-book "served-columns-tests")

; Executable test-only interpretations of the two non-executable theorem
; vocabularies.  Their named equations keep the witnesses about the actual
; abstractions; neither interpretation is in a served entry.
(defun nbwct-remaining (pieces pos)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pieces)
      (append (if (stringp (car pieces))
                  (nthcdr (nfix pos) (fn-record-string-octets (car pieces))) (car pieces))
              (nbwct-remaining (cdr pieces) 0)) nil))

(defthm nbwct-remaining-is-the-abstraction
  (equal (nbwct-remaining pieces pos) (fn-nbw-remaining pieces pos))
  :hints (("Goal" :induct (nbwct-remaining pieces pos)
                  :in-theory (enable fn-nbw-remaining))))

(defun nbwct-f (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (and (fn-arena-p fn-arena) (fn-scol-rows-okp (scol-rows-from 0 fn-cat) fn-arena)))

(defthm nbwct-f-is-the-column-relation
  (implies (true-listp fn-cat)
           (equal (nbwct-f fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance scol-rows-from-is-nthcdr (i 0)))
                  :in-theory (e/d (fn-scol-okp nbwct-f)
                                  (fn-scol-rows-okp scol-rows-from
                                   scol-rows-from-is-nthcdr)))))

(defconst *nbwct-crlf* (coerce '(#\Return #\Newline) 'string))

(defun nbwct-article-bytes (subject)
  (declare (xargs :guard (stringp subject)))
  (fn-record-string-octets
   (concatenate 'string "From: a@example.invalid" *nbwct-crlf*
                "Newsgroups: fn.test" *nbwct-crlf* "Subject: " subject *nbwct-crlf*
                "Message-ID: <nbwct@example.invalid>" *nbwct-crlf*
                *nbwct-crlf* "line one" *nbwct-crlf* "line two" *nbwct-crlf*)))

(defun nbwct-wire ()
  (declare (xargs :guard t))
  (fn-record-make 0 1 0 "<nbwct@example.invalid>" (nbwct-article-bytes "the column")
                  '("fn.test") "o" "s" "e" 1 5))

(defun nbwct-corrupt-facts (row)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence row) (fn-record-txid row)
                (fn-record-generation row) (fn-record-msgid row)
                (fn-record-payload row) (fn-record-groups row)
                (fn-record-obligation-id row) (fn-record-content-subject row)
                (fn-record-release-evidence row) (fn-record-charge row)
                (fn-record-stamp row) (fn-held-facts-of (nbwct-article-bytes "other column"))
                (fn-held-context row) nil nil))

; This calls the actual intern/commit and column lookup.  Corruption changes
; only the decided facts; the article and its arena bytes remain intact.
(defun nbwct-refinement-case (corruptp wrong-factsp bad-verdictp fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (row fn-arena)
      (fn-cat-intern-list
       (if bad-verdictp
           (fn-record-make 0 1 0 "<nbwct@example.invalid>" '(1 2 3 255)
                           '("fn.test") "o" "s" "e" 1 5)
         (nbwct-wire)) nil 0 fn-arena)
      (let* ((row (if corruptp (nbwct-corrupt-facts row) row))
             (fn-cat (fn-cat-commit row fn-cat))
             (article (fn-make-article (fn-record-msgid row) (fn-record-payload row)
                                       (fn-record-groups row) (fn-held-numbers row)
                                       t (fn-record-stamp row)))
             (looked (fn-scol-facts article fn-cat))
             (facts (if wrong-factsp
                        (fn-held-facts-of (nbwct-article-bytes "other column")) looked))
             (lhs (nbwct-remaining
                   (fn-nbw-column-pieces 1 facts (fn-nntp-article-length article fn-arena)) 0))
             (rhs (append (fn-nov-line 1 (fn-nov-overview article fn-arena)) '(13 10))))
        (mv (list (nbwct-f fn-arena fn-cat) (equal facts looked)
                  (fn-hnov-ok (fn-hf-nov facts)) (equal lhs rhs)
                  (fn-hnov-p (fn-hf-nov facts)) lhs rhs)
            fn-arena fn-cat)))))

(assert-event
 (mv-let (r fn-arena fn-cat)
   (nbwct-refinement-case nil nil nil fn-arena fn-cat)
   (mv (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r)
            (equal (take 3 (nth 5 r)) '(49 9 116))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Literal refinement hypotheses: F, exact lookup, and decided :ok.
(assert-event
 (mv-let (r fn-arena fn-cat)
   (nbwct-refinement-case t nil nil fn-arena fn-cat)
   (mv (and (not (nth 0 r)) (nth 1 r) (nth 2 r) (not (nth 3 r))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

(assert-event
 (mv-let (r fn-arena fn-cat)
   (nbwct-refinement-case nil t nil fn-arena fn-cat)
   (mv (and (nth 0 r) (not (nth 1 r)) (nth 2 r) (not (nth 3 r))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Truthful :error cache over a payload that does not parse: F and the exact
; lookup still hold, but a row must not be emitted for this cache.
(assert-event
 (mv-let (r fn-arena fn-cat)
   (nbwct-refinement-case nil nil t fn-arena fn-cat)
   (mv (and (nth 0 r) (nth 1 r) (not (nth 2 r)) (not (nth 3 r))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Complete-row constructor's two literal hypotheses, independently.
(defthm nbwct-row-without-ok
  (let* ((facts (fn-hf-make 0 0 0
                           (list nil nil nil (fn-hnov-make nil nil "A" "" "" "" ""))))
         (article (fn-make-article "<nbwct@example.invalid>" nil nil nil t 0)))
    (and (fn-hnov-p (fn-hf-nov facts)) (not (fn-hnov-ok (fn-hf-nov facts)))
         (not (equal (fn-nbw-remaining (fn-nbw-column-pieces 1 facts 0) 0)
                     (append (fn-nov-line 1 (fn-scol-nov-overview article facts fn-arena))
                             '(13 10))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-nov-overview fn-nov-line
                                     fn-nntp-append-pieces))))

(defthm nbwct-row-without-shape-corrupted-state
  (let* ((nov '(nil t (65) "" "" "" ""))
         (facts (fn-hf-make 0 0 0 (list nil nil nil nov)))
         (article (fn-make-article "<nbwct@example.invalid>" nil nil nil t 0)))
    (and (not (fn-hnov-p nov)) (fn-hnov-ok nov)
         (not (equal (fn-nbw-remaining (fn-nbw-column-pieces 1 facts 0) 0)
                     (append (fn-nov-line 1 (fn-scol-nov-overview article facts fn-arena))
                             '(13 10))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-scol-nov-overview fn-nov-line
                                     fn-nntp-append-pieces))))
