(in-package "ACL2")
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

