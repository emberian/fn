; fn NNTP reader session core: projection from the committed acceptance state.
;
; Split out of books/nntp.lisp (2026-09-19).

(in-package "ACL2")
(include-book "nntp-session")
; -----------------------------------------------------------------------------
; Projection from the committed acceptance state

(defun fn-nntp-membership-number (group memberships)
  (mbe :logic
       (if (consp memberships)
           (if (equal group (car (car memberships)))
               (cdr (car memberships))
             (fn-nntp-membership-number group (cdr memberships)))
         0)
       :exec
       (if (consp memberships)
           (if (equal group (fn-ag-car (fn-ag-car memberships)))
               (fn-ag-cdr (fn-ag-car memberships))
             (fn-nntp-membership-number group (fn-ag-cdr memberships)))
         0)))
; The available local number of `article` in `group`, or 0.  An article is
; available at a number only when the number is a valid RFC 3977 section 6
; article number and the stored identifier can be rendered: STAT, NEXT, and
; LAST answer with that identifier and nothing else.  An article that fails
; this is excluded from group counts, water marks, LISTGROUP ranges, and
; NEXT/LAST, and a command that names its number is answered explicitly.
(defun fn-nntp-article-number (group article)
  (let ((number (fn-nntp-membership-number
                 group (fn-article-memberships article))))
    (if (and (posp number)
             (<= number *fn-nntp-max-article-number*)
             (fn-nntp-article-idp article))
        number
      0)))

(defthm fn-nntp-article-number-natp
  (natp (fn-nntp-article-number group article))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-article-number-bounded
  (<= (fn-nntp-article-number group article) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-available-number-article-is-projectable
  (implies (posp (fn-nntp-article-number group article))
           (fn-nntp-article-idp article)))
; The article committed at a raw local number, whether or not it is available.
; Retrieval by number uses this so that a request naming an unavailable article
; is answered explicitly rather than silently.
(defun fn-nntp-find-group-number (group number articles)
  (if (consp articles)
      (if (equal (fn-nntp-membership-number
                  group (fn-article-memberships (car articles)))
                 number)
          (car articles)
        (fn-nntp-find-group-number group number (cdr articles)))
    nil))
; The article available at a number.  This is the cursor's referent.
(defun fn-nntp-available-article (group number articles)
  (if (consp articles)
      (if (and (posp number)
               (equal (fn-nntp-article-number group (car articles)) number))
          (car articles)
        (fn-nntp-available-article group number (cdr articles)))
    nil))

(defthm fn-nntp-available-article-is-projectable
  (implies (consp (fn-nntp-available-article group number articles))
           (fn-nntp-article-idp (fn-nntp-available-article group number articles))))

(defun fn-nntp-insert-number (number numbers)
  (mbe :logic
       (if (consp numbers)
           (if (< number (car numbers))
               (cons number numbers)
             (cons (car numbers) (fn-nntp-insert-number number (cdr numbers))))
         (list number))
       :exec
       (if (consp numbers)
           (if (fn-ag-less number (fn-ag-car numbers))
               (cons number numbers)
             (cons (fn-ag-car numbers)
                   (fn-nntp-insert-number number (fn-ag-cdr numbers))))
         (list number))))

(defun fn-nntp-orderedp (numbers)
  (if (consp numbers)
      (if (consp (cdr numbers))
          (and (fn-ng-less-equal (car numbers) (car (cdr numbers)))
               (fn-nntp-orderedp (cdr numbers)))
        t)
    t))

(defthm fn-nntp-insert-number-preserves-ordered
  (implies (and (fn-nntp-orderedp numbers) (rationalp number))
           (fn-nntp-orderedp (fn-nntp-insert-number number numbers)))
  :hints (("Goal" :induct (fn-nntp-orderedp numbers)
           :in-theory (enable fn-nntp-orderedp fn-nntp-insert-number))))

(defthm fn-nntp-insert-number-members
  (iff (member-equal value (fn-nntp-insert-number number numbers))
       (or (equal value number) (member-equal value numbers)))
  :hints (("Goal" :induct (fn-nntp-insert-number number numbers)
           :in-theory (enable fn-nntp-insert-number))))
; One pass over the committed articles.  The count, the water marks, NEXT, and
; LAST never build or sort a number list; only LISTGROUP does, and it sorts
; only the numbers inside the range its own argument names.
(defun fn-nntp-group-count (group articles)
  (if (consp articles)
      (if (posp (fn-nntp-article-number group (car articles)))
          (+ 1 (fn-nntp-group-count group (cdr articles)))
        (fn-nntp-group-count group (cdr articles)))
    0))

(defthm fn-nntp-group-count-natp
  (natp (fn-nntp-group-count group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-count-at-most-articles
  (<= (fn-nntp-group-count group articles) (len articles))
  :rule-classes (:rewrite :linear))

(defun fn-nntp-group-low (group articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-low group (cdr articles))))
        (if (and (posp number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defthm fn-nntp-group-low-natp
  (natp (fn-nntp-group-low group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-low-bounded
  (<= (fn-nntp-group-low group articles) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-group-low-is-available
  (implies (posp (fn-nntp-group-low group articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-low group articles) articles))))

(defun fn-nntp-group-high (group articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-high group (cdr articles))))
        (if (and (posp number) (< rest number)) number rest))
    0))

(defthm fn-nntp-group-high-natp
  (natp (fn-nntp-group-high group articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-high-bounded
  (<= (fn-nntp-group-high group articles) *fn-nntp-max-article-number*)
  :rule-classes (:rewrite :linear))

(defthm fn-nntp-group-high-is-available
  (implies (posp (fn-nntp-group-high group articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-high group articles) articles))))

(defun fn-nntp-group-next-number (group current articles)
  ; The least available number strictly greater than `current`, or 0.
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-next-number group current (cdr articles))))
        (if (and (posp number)
                 (fn-ag-less current number)
                 (or (not (posp rest)) (< number rest)))
            number
          rest))
    0))

(defthm fn-nntp-group-next-number-natp
  (natp (fn-nntp-group-next-number group current articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-next-number-is-available
  (implies (posp (fn-nntp-group-next-number group current articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-next-number group current articles)
                   articles))))

(defun fn-nntp-group-last-number (group current articles)
  ; The greatest available number strictly less than `current`, or 0.
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles)))
            (rest (fn-nntp-group-last-number group current (cdr articles))))
        (if (and (posp number)
                 (fn-ag-less number current)
                 (< rest number))
            number
          rest))
    0))

(defthm fn-nntp-group-last-number-natp
  (natp (fn-nntp-group-last-number group current articles))
  :rule-classes (:type-prescription :rewrite))

(defthm fn-nntp-group-last-number-is-available
  (implies (posp (fn-nntp-group-last-number group current articles))
           (consp (fn-nntp-available-article
                   group (fn-nntp-group-last-number group current articles)
                   articles))))
; LISTGROUP's list.  Only the numbers inside the requested range are inserted,
; so the sort is charged to the command's own range and not to the archive.
(defun fn-nntp-group-range-numbers (group low high articles)
  (if (consp articles)
      (let ((number (fn-nntp-article-number group (car articles))))
        (if (and (posp number)
                 (fn-ng-less-equal low number)
                 (fn-ng-less-equal number high))
            (fn-nntp-insert-number
             number (fn-nntp-group-range-numbers group low high (cdr articles)))
          (fn-nntp-group-range-numbers group low high (cdr articles))))
    nil))

(defthm fn-nntp-group-range-numbers-are-ordered
  (fn-nntp-orderedp (fn-nntp-group-range-numbers group low high articles)))

(defthm fn-nntp-group-range-numbers-are-available
  (implies (member-equal value
                         (fn-nntp-group-range-numbers group low high articles))
           (and (posp value)
                (consp (fn-nntp-available-article group value articles))))
  :rule-classes nil)

(defun fn-nntp-number-lines (numbers)
  (if (consp numbers)
      (cons (fn-nntp-decimal-field (car numbers))
            (fn-nntp-number-lines (cdr numbers)))
    nil))

(defun fn-nntp-group-summary (archive group)
  (let ((low (fn-nntp-group-low group (fn-state-articles archive))))
    (if (posp low)
        (list (fn-nntp-group-count group (fn-state-articles archive))
              low
              (fn-nntp-group-high group (fn-state-articles archive)))
      (let ((watermark (fn-next-number group (fn-state-nexts archive))))
        (list 0 watermark (if (posp watermark) (- watermark 1) 0))))))

(defun fn-nntp-summary-count (x)
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-nntp-summary-low (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-nntp-summary-high (x)
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-nntp-group-initial (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets "211 ")
           (fn-nntp-decimal-field (fn-nntp-summary-count summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-string-octets group)))))

(defun fn-nntp-group-result (session archive group)
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-nntp-group-low group (fn-state-articles archive)))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current)))
        (fn-nntp-make-result
         next-session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf (fn-nntp-group-initial archive group))))))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-unknown-group-preserves-session
  (implies (not (member-equal group (fn-state-groups archive)))
           (equal (fn-nntp-result-session (fn-nntp-group-result session archive group))
                  session)))

(defun fn-nntp-listgroup-initial (archive group)
  (append (fn-nntp-group-initial archive group)
          (fn-nntp-string-octets " list follows")))

(defun fn-nntp-listgroup-result (session archive group range)
  (if (mbe :logic (member-equal group (fn-state-groups archive))
           :exec (fn-ag-member group (fn-state-groups archive)))
      (let* ((low (fn-nntp-group-low group (fn-state-articles archive)))
             (current (if (posp low) low nil))
             (next-session (fn-nntp-set-cursor session group current))
             (shown (fn-nntp-group-range-numbers group
                                                 (fn-nntp-range-low range)
                                                 (fn-nntp-range-high range)
                                                 (fn-state-articles archive))))
        (fn-nntp-multi-octets next-session
                              (fn-nntp-listgroup-initial archive group)
                              (fn-nntp-number-lines shown)))
    (fn-nntp-single session "411 no such newsgroup")))

(defthm fn-nntp-listgroup-unknown-preserves-session
  (implies (not (member-equal group (fn-state-groups archive)))
           (equal (fn-nntp-result-session
                   (fn-nntp-listgroup-result session archive group range))
                  session)))

(defun fn-nntp-listgroup-command (session archive args)
  (let ((all-range (list :ok 1 2147483647)))
    (if (null args)
        (let ((group (fn-nntp-session-group session)))
          (if (null group)
              (fn-nntp-single session "412 no newsgroup selected")
            (if (mbe :logic (member-equal group (fn-state-groups archive))
                     :exec (fn-ag-member group (fn-state-groups archive)))
                (fn-nntp-listgroup-result session archive group all-range)
              (fn-nntp-single session "412 no newsgroup selected"))))
      (if (and (consp args) (null (cdr args))
               (fn-nntp-printable-tokenp (car args)))
          (fn-nntp-listgroup-result session archive
                                    (fn-nntp-token-string (car args)) all-range)
        (if (and (consp args) (consp (cdr args)) (null (cdr (cdr args)))
                 (fn-nntp-printable-tokenp (car args)))
            (let ((range (fn-nntp-parse-range (car (cdr args)))))
              (if (fn-nntp-range-okp range)
                  (fn-nntp-listgroup-result session archive
                                            (fn-nntp-token-string (car args)) range)
                (fn-nntp-single session "501 syntax error")))
          (fn-nntp-single session "501 syntax error"))))))

(verify-guards fn-nntp-membership-number)

(verify-guards fn-nntp-article-number)

(verify-guards fn-nntp-find-group-number)

(verify-guards fn-nntp-available-article)

(verify-guards fn-nntp-insert-number)

(verify-guards fn-nntp-orderedp)

(verify-guards fn-nntp-group-count)

(verify-guards fn-nntp-group-low)

(verify-guards fn-nntp-group-high)

(verify-guards fn-nntp-group-next-number)

(verify-guards fn-nntp-group-last-number)

(verify-guards fn-nntp-group-range-numbers)

(verify-guards fn-nntp-number-lines)

(verify-guards fn-nntp-group-summary)

(verify-guards fn-nntp-summary-count)

(verify-guards fn-nntp-summary-low)

(verify-guards fn-nntp-summary-high)

(verify-guards fn-nntp-group-initial)

(verify-guards fn-nntp-group-result)

(verify-guards fn-nntp-listgroup-initial)

(verify-guards fn-nntp-listgroup-result)

(verify-guards fn-nntp-listgroup-command)

; ---------------------------------------------------------------------------
; Export theory
;
; The definitions this book adds are proof vocabulary for the books above it,
; not rules an includer should inherit.  They are withdrawn under one name so
; a book that reasons about the transitions re-enables exactly them in one
; line (books/nntp-invariants.lisp does).  Ground evaluation is unaffected:
; only the :definition runes are withdrawn.

(deftheory fn-nntp-projection-vocabulary
  '(fn-nntp-membership-number fn-nntp-article-number 
    fn-nntp-find-group-number fn-nntp-available-article fn-nntp-insert-number 
    fn-nntp-orderedp fn-nntp-group-count fn-nntp-group-low fn-nntp-group-high 
    fn-nntp-group-next-number fn-nntp-group-last-number 
    fn-nntp-group-range-numbers fn-nntp-number-lines fn-nntp-group-summary 
    fn-nntp-summary-count fn-nntp-summary-low fn-nntp-summary-high 
    fn-nntp-group-initial fn-nntp-group-result fn-nntp-listgroup-initial 
    fn-nntp-listgroup-result fn-nntp-listgroup-command))

(in-theory (disable fn-nntp-projection-vocabulary))
