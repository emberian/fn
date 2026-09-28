; Witnesses for books/served-columns.lisp (lane served-columns, PRF-332).
;
; REACHABLE: the open's list intern of three wire records into the live
; arena, each committed to the live catalog (the rows F is about: facts
; decided from the sealed bytes); the served readers over those rows answer
; FROM THE COLUMN (the lookup finds the row) and equal the byte readers:
;   an article with all five overview fields and two body lines (OVER's
;     tuple, HDR Subject / SUBJECT / :lines / :bytes, and a field outside
;     the column, Newsgroups, which reads the bytes);
;   octets that do not parse (the column's ok flag is nil: OVER and HDR
;     answer (:error) as the bytes do);
;   a reclaim tombstone (the column's tomb flag: OVER skips it).
; HYPOTHESIS REMOVAL (F): a CORRUPTED-STATE witness -- a row whose decided
; column is another article's, at the first article's handle -- falsifies
; F (checked) and the column's answer differs from the bytes' (checked);
; the keystones without F must fail.
(in-package "ACL2")
(include-book "../../books/served-columns")
(include-book "must-fail-checked")

(defun scol-octets (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))
(defconst *scol-crlf* (coerce '(#\Return #\Newline) 'string))

(defconst *scol-art*
  (scol-octets (concatenate 'string
                            "From: a@example.invalid" *scol-crlf*
                            "Newsgroups: fn.test" *scol-crlf*
                            "Subject: the column" *scol-crlf*
                            "Date: Sun, 27 Sep 2026 22:00:00 +0000" *scol-crlf*
                            "Message-ID: <scol-1@example.invalid>" *scol-crlf*
                            "References: <scol-0@example.invalid>" *scol-crlf*
                            *scol-crlf*
                            "line one" *scol-crlf* "line two" *scol-crlf*)))
(defconst *scol-garbage* '(1 2 3 255))
(defconst *scol-tomb* (append *fn-rcl-magic* (make-list 81 :initial-element 0)))

(defun scol-w (seq msgid payload)
  (declare (xargs :guard (natp seq)))
  (fn-record-make seq (+ 1 seq) 0 msgid payload '("fn.test") "o" "s" "e" 1 5))

(defconst *scol-ws*
  (list (scol-w 0 "<scol-1@example.invalid>" *scol-art*)
        (scol-w 1 "<scol-2@example.invalid>" *scol-garbage*)
        (scol-w 2 "<scol-3@example.invalid>" *scol-tomb*)))

(assert-event (and (fn-record-p (nth 0 *scol-ws*)) (fn-record-p (nth 1 *scol-ws*))
                   (fn-record-p (nth 2 *scol-ws*))
                   (fn-rcl-tombstonep *scol-tomb*)))

; The open: each wire record interned (sealed, facts decided) and committed.
(defun scol-load (ws fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (atom ws)
      (mv fn-arena fn-cat)
    (mv-let (row fn-arena)
      (fn-cat-intern-list (car ws) nil 0 fn-arena)
      (let ((fn-cat (fn-cat-commit row fn-cat)))
        (scol-load (cdr ws) fn-arena fn-cat)))))

(defun scol-article (seq fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil))
  (let ((row (fn-cat-at seq fn-cat)))
    (fn-make-article (fn-record-msgid row) (fn-record-payload row) (fn-record-groups row)
                     (fn-held-numbers row) t (fn-record-stamp row))))

(defun scol-field (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))

; Every served read of every row: (column-answer . byte-answer) pairs, and
; whether the column was the one read.
(defun scol-reads (seq fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let ((a (scol-article seq fn-cat)))
    (list (and (fn-scol-facts a fn-cat) t)
          (cons (fn-scol-tombstonep a fn-arena fn-cat) (fn-nntp-article-tombstonep a fn-arena))
          (cons (fn-scol-overview-of a fn-arena fn-cat) (fn-nov-overview a fn-arena))
          (cons (fn-scol-hdr-content (scol-field "Subject") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field "Subject") a fn-arena))
          (cons (fn-scol-hdr-content (scol-field "SUBJECT") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field "SUBJECT") a fn-arena))
          (cons (fn-scol-hdr-content (scol-field "references") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field "references") a fn-arena))
          (cons (fn-scol-hdr-content (scol-field ":lines") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field ":lines") a fn-arena))
          (cons (fn-scol-hdr-content (scol-field ":bytes") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field ":bytes") a fn-arena))
          (cons (fn-scol-hdr-content (scol-field "Newsgroups") a fn-arena fn-cat)
                (fn-nntp-hdr-content (scol-field "Newsgroups") a fn-arena)))))

; The catalog's rows as a value, oldest first: its logical value (checked
; below), so F is evaluated on exactly what it quantifies over.
(defun scol-rows-from (i fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (if (and (natp i) (< i (fn-cat-count fn-cat)))
      (cons (fn-cat-at i fn-cat) (scol-rows-from (+ 1 i) fn-cat))
    nil))

(defthm scol-nthcdr-past
  (implies (and (true-listp l) (natp i) (<= (len l) i))
           (equal (nthcdr i l) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm scol-nthcdr-as-cons
  (implies (and (natp i) (< i (len l)))
           (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 i) l))))
  :hints (("Goal" :in-theory (enable nthcdr nth))))

(defthm scol-rows-from-is-nthcdr
  (implies (and (natp i) (true-listp fn-cat))
           (equal (scol-rows-from i fn-cat) (nthcdr i fn-cat)))
  :hints (("Goal" :induct (scol-rows-from i fn-cat))))

(defun scol-pairs-agree (pairs)
  (declare (xargs :guard t))
  (if (atom pairs) t
    (and (consp (car pairs)) (equal (car (car pairs)) (cdr (car pairs)))
         (scol-pairs-agree (cdr pairs)))))

(defun scol-reachable (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (scol-load *scol-ws* fn-arena fn-cat)
      (mv (list (fn-arena-p fn-arena)
                (fn-scol-rows-okp (scol-rows-from 0 fn-cat) fn-arena)
                (scol-reads 0 fn-arena fn-cat)
                (scol-reads 1 fn-arena fn-cat)
                (scol-reads 2 fn-arena fn-cat))
          fn-arena fn-cat))))

(assert-event
 (mv-let (r fn-arena fn-cat)
   (scol-reachable fn-arena fn-cat)
   (mv (let ((art (nth 2 r)) (bad (nth 3 r)) (tomb (nth 4 r)))
         (and ;; F's antecedent, complete: the arena recognizer and every row faithful
              (nth 0 r) (nth 1 r)
              ;; the column was read for all three rows
              (nth 0 art) (nth 0 bad) (nth 0 tomb)
              ;; and every column answer is the byte answer
              (scol-pairs-agree (cdr art)) (scol-pairs-agree (cdr bad))
              (scol-pairs-agree (cdr tomb))
              ;; non-degenerate: the article's overview is the five fields, its
              ;; octet count and its two body lines
              (equal (car (nth 2 art))
                     (list :ok (scol-field "the column") (scol-field "a@example.invalid")
                           (scol-field "Sun, 27 Sep 2026 22:00:00 +0000")
                           (scol-field "<scol-1@example.invalid>")
                           (scol-field "<scol-0@example.invalid>")
                           (len *scol-art*) 2))
              (equal (car (nth 3 art)) (list :ok (scol-field "the column")))
              (equal (car (nth 6 art)) (list :ok (scol-field "2")))
              (equal (car (nth 8 art)) (list :ok (scol-field "fn.test")))
              ;; the garbage does not parse: (:error) from the column
              (equal (car (nth 2 bad)) (list :error))
              (equal (car (nth 3 bad)) (list :error))
              ;; the tombstone: the column's tomb flag
              (equal (car (nth 1 tomb)) t)
              (equal (car (nth 1 art)) nil)))
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; CORRUPTED-STATE witness (F removed): a row at the article's handle whose
; decided column is the garbage's.  F fails and the column answers what the
; bytes do not.
(defun scol-corrupt (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (row fn-arena)
      (fn-cat-intern-list (nth 0 *scol-ws*) nil 0 fn-arena)
      (let* ((bad (fn-held-make (fn-record-sequence row) (fn-record-txid row)
                                (fn-record-generation row) (fn-record-msgid row)
                                (fn-record-payload row) (fn-record-groups row)
                                (fn-record-obligation-id row) (fn-record-content-subject row)
                                (fn-record-release-evidence row) (fn-record-charge row)
                                (fn-record-stamp row)
                                (fn-held-facts-of *scol-garbage*)
                                (fn-held-context row) nil nil))
             (fn-cat (fn-cat-commit bad fn-cat))
             (a (scol-article 0 fn-cat)))
        (mv (list (fn-arena-p fn-arena)
                  (fn-scol-rows-okp (scol-rows-from 0 fn-cat) fn-arena)
                  (fn-scol-overview-of a fn-arena fn-cat)
                  (fn-nov-overview a fn-arena))
            fn-arena fn-cat)))))

(assert-event
 (mv-let (r fn-arena fn-cat)
   (scol-corrupt fn-arena fn-cat)
   (mv (and (nth 0 r)                           ; the other conjunct holds
            (not (nth 1 r))                     ; F fails
            (equal (nth 2 r) (list :error))     ; the column: the garbage's verdict
            (equal (car (nth 3 r)) :ok)         ; the bytes: the article's overview
            (not (equal (nth 2 r) (nth 3 r))))  ; the conclusion fails
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; The keystones without F.
(must-fail-checked
 (defthm scol-overview-without-f
   (equal (fn-scol-overview-of article fn-arena fn-cat)
          (fn-nov-overview article fn-arena))))

(must-fail-checked
 (defthm scol-hdr-without-f
   (equal (fn-scol-hdr-content field article fn-arena fn-cat)
          (fn-nntp-hdr-content field article fn-arena))))

(must-fail-checked
 (defthm scol-tomb-without-f
   (equal (fn-scol-tombstonep article fn-arena fn-cat)
          (fn-nntp-article-tombstonep article fn-arena))))
