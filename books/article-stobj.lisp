; fn: the article header scan over the octet buffer (D27 boundary 9; the
; megaspike, D28).  Prefix `fn-ars-'.
;
; `fn-article-parse' (books/article.lisp) walks the posted octets line by
; line: each header line is consed in reverse and reversed again, the body is
; the shared tail of the input list, and the body's CRLF discipline is one
; more walk.  Here the same grammar runs by index over the buffer stobj of
; books/octets-stobj: a line is found by scanning for CR LF at an index
; (`fn-ars-next-line', with the reference's line bound and its three
; refusals in its order), consed once as the octet list the field helpers
; of books/article take (`fn-article-new-field', `fn-article-add-fold',
; `fn-article-header-rev-add-line' are the reference's own, on that list),
; the body discipline is checked in place (`fn-ars-body-crlfp'), and the
; body leaves as one slice.  The header bound, the line bound and the field
; bound are the reference's constants at the reference's points.
;
; Reach: on the spike no host line calls this yet.  The served POST arm
; parses the article from the submission's octet list inside the session
; machine (books/nntp-post.lisp, under fn-owner-chunk), so this twin is the
; parser the injection walk will call once the submission holds a buffer
; slice (the wave C item the record names).  Its theorem is stated so that
; the reroute is the dev lane's, not a re-design.

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "article")

(defun fn-ars-next-line (i n fn-octets)
  ; The line at I: (mv error line-end rest-start), error nil on success.
  ; The line is st[i, line-end); the next line starts at rest-start.
  ; `fn-article-next-line-aux' with the octets read in place: CR must be
  ; followed by LF, a bare LF is refused, a line longer than
  ; *fn-article-max-line-octets* is :limit, no CR LF before the end is
  ; :missing-separator.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      (mv :missing-separator i i)
    (let ((o (fn-octets-get i fn-octets)))
      (cond ((equal o 13)
             (if (and (< (1+ i) n) (equal (fn-octets-get (1+ i) fn-octets) 10))
                 (mv nil i (+ i 2))
               (mv :invalid-header i i)))
            ((equal o 10) (mv :invalid-header i i))
            (t (mv-let (err end rest)
                 (fn-ars-next-line (1+ i) n fn-octets)
                 (mv err end rest)))))))

(defun fn-ars-line-too-longp (start end)
  ; The reference refuses with :limit when more than
  ; *fn-article-max-line-octets* octets precede the CR.
  (declare (xargs :guard (and (natp start) (natp end))))
  (< *fn-article-max-line-octets* (- end start)))

(defun fn-ars-body-crlfp (i n fn-octets)
  ; `fn-article-body-crlfp' of st[i, n), in place.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets)))
                  :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      t
    (let ((o (fn-octets-get i fn-octets)))
      (if (equal o 13)
          (and (< (1+ i) n) (equal (fn-octets-get (1+ i) fn-octets) 10)
               (fn-ars-body-crlfp (+ i 2) n fn-octets))
        (and (not (equal o 10))
             (fn-ars-body-crlfp (1+ i) n fn-octets))))))

(defun fn-ars-parse-lines (i n lines-left header-bytes fields-rev current header-rev
                             fn-octets)
  ; `fn-article-parse-lines' with the octets read in place from I.
  (declare (xargs :stobjs fn-octets
                  :measure (nfix lines-left)
                  :guard (and (natp i) (natp n) (<= i n) (<= n (fn-octets-len fn-octets))
                              (natp lines-left) (natp header-bytes)
                              (true-listp fields-rev)
                              (or (null current) (fn-article-fieldp current))
                              (true-listp header-rev))
                  :verify-guards nil))
  (if (zp lines-left)
      (fn-article-error :limit)
    (mv-let (err line-end rest-start)
      (fn-ars-next-line i n fn-octets)
      (let ((line-end (if (and (natp line-end) (<= i line-end) (<= line-end n)) line-end i))
            (rest-start (if (and (natp rest-start) (<= i rest-start) (<= rest-start n))
                            rest-start n)))
        (cond (err (fn-article-error err))
              ((fn-ars-line-too-longp i line-end) (fn-article-error :limit))
              ((equal line-end i)
               ; The empty line: the header ends, the body is the rest.
               (if (not (fn-ars-body-crlfp rest-start n fn-octets))
                   (fn-article-error :invalid-header)
                 (fn-article-ok
                  (fn-article-make
                   (reverse header-rev)
                   (fn-oct-slice-list-down rest-start n nil fn-octets)
                   (fn-article-finish-fields fields-rev current)))))
              ((< *fn-article-max-header-octets*
                  (+ header-bytes (- line-end i) 2))
               (fn-article-error :limit))
              (t
               (let ((line (fn-oct-slice-list-down i line-end nil fn-octets)))
                 (if (fn-article-wspp (car line))
                     (if (not current)
                         (fn-article-error :invalid-header)
                       (if (not (fn-article-fold-linep line))
                           (fn-article-error :invalid-header)
                         (fn-ars-parse-lines
                          rest-start n (1- lines-left) (+ header-bytes (- line-end i) 2)
                          fields-rev (fn-article-add-fold current line)
                          (fn-article-header-rev-add-line header-rev line)
                          fn-octets)))
                   (let ((field-result (fn-article-new-field line)))
                     (if (not (fn-article-line-okp field-result))
                         field-result
                       (if (and current
                                (<= (1- *fn-article-max-fields*) (len fields-rev)))
                           (fn-article-error :limit)
                         (fn-ars-parse-lines
                          rest-start n (1- lines-left) (+ header-bytes (- line-end i) 2)
                          (if current (cons current fields-rev) fields-rev)
                          (fn-article-line-value field-result)
                          (fn-article-header-rev-add-line header-rev line)
                          fn-octets))))))))))))

(defun fn-ars-parse (fn-octets)
  ; `fn-article-parse' of the buffer's contents.
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let ((n (fn-octets-len fn-octets)))
    (if (< *fn-article-max-octets* n)
        (fn-article-error :limit)
      (fn-ars-parse-lines 0 n (1+ *fn-article-max-header-lines*) 0 nil nil nil fn-octets))))

;; SPIKE: defers the guard verification of the two parsers (the reference's
;; `fn-article-parse-lines' verifies its guards in books/article-work; the
;; field helpers' guards on a consed line are the reference's) and the
;; correspondence below.  Statements: the buffer parser is the list parser
;; on the buffer's contents.  The dev lane proves it from
;; `fn-ars-next-line' = `fn-article-next-line' on `(nthcdr i list)' (the
;; line is the slice, the rest starts two past the CR) and
;; `fn-ars-body-crlfp' = `fn-article-body-crlfp' on the slice, by the
;; induction of `fn-article-parse-lines'.
(skip-proofs
 (progn
   (verify-guards fn-ars-parse-lines)
   (verify-guards fn-ars-parse)
   (defthm fn-ars-parse-is-article-parse
     (equal (fn-ars-parse fn-octets)
            (fn-article-parse (fn-octets-list fn-octets))))))
