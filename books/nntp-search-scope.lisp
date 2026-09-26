; fn: the reader's search scope (lane reader-daily, PRF-122).
;
; The web reader's search (tools/fn_web.py, Backend.search) and its thread
; view (Backend.replies) send one `XPAT <field> <low>-<high> <pattern>' after
; `GROUP <group>' and show the node's lines as they arrive.  The client keeps
; no index and decides nothing about which article is in scope, which one is
; visible or which one matches: this book states what the node's answer is.
;
; Subject.  The reply the host sends: host/native/owner.lisp calls
; fn-owner-chunk (host/owner-host.lisp), which runs fn-served-step
; (books/served.lisp) and reaches fn-nntp-step-pinned for every reader
; command that is not POST (the chain is in books/nntp-xpat.lisp's header).
; `fn-nntp-step-pinned-xpat-is-the-xpat-response' is the XPAT arm of that
; step; `fn-nntp-step-pinned-xpat-range-is-the-scope' below is the same step
; over a range, rewritten to the HDR lines of an explicit set of numbers.
;
; KEYSTONE `fn-nntp-step-pinned-xpat-range-is-the-scope'.  Over a range, the
; served reply is RFC 2980 section 2.9.1's 221 block whose lines are exactly
; XHDR's lines (fn-nntp-hdr-lines-for-numbers) for the numbers
; `fn-nss-hits' selects, in ascending number order.
; KEYSTONE `fn-nss-hits-are-the-scope'.  A number is in that set exactly
; when it lies in the requested range, the selected group's served archive
; holds an available article at it, the field renders, and the node's own
; wildmat matcher accepts the rendered field.
; KEYSTONE `fn-nss-withdrawn-number-is-never-a-hit'.  A number the same
; step answers `423 withdrawn' for (`fn-nntp-number-withdrawn-p', the arm
; books/nntp-control.lisp's keystones state) is never a hit, whatever the
; field or the pattern: search cannot resurrect a withdrawn article.
;
; What this does not say.  It says nothing about an article that has not
; arrived (the served archive does not hold it, so it is not a hit, and
; nothing distinguishes that from a number never assigned), nor about
; articles outside the requested range: a search answers for its stated
; scope only, and the reader says so on the page.
;
; Prefix `fn-nss-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "nntp-xpat")

; The numbers of the scope the node's XPAT renders a line for: the same
; recursion as fn-nntp-xpat-lines-for-numbers, returning the number instead
; of the line.
(defun fn-nss-hits (field patterns group numbers articles)
  (if (consp numbers)
      (let* ((article (fn-nntp-available-article group (car numbers) articles))
             (content (if (consp article)
                          (fn-nntp-hdr-content field article)
                        (list :error))))
        (if (and (fn-nntp-hdr-okp content)
                 (fn-nntp-xpat-matchesp patterns (fn-nntp-hdr-octets content)))
            (cons (car numbers)
                  (fn-nss-hits field patterns group (cdr numbers) articles))
          (fn-nss-hits field patterns group (cdr numbers) articles)))
    nil))

(local
 (defthm fn-nss-hdr-lines-of-a-hit
   (implies (and (consp (fn-nntp-available-article group number articles))
                 (fn-nntp-hdr-okp
                  (fn-nntp-hdr-content
                   field (fn-nntp-available-article group number articles))))
            (equal (fn-nntp-hdr-lines-for-numbers field group (cons number rest)
                                                  articles)
                   (cons (fn-nntp-hdr-line
                          (fn-nntp-decimal-field number)
                          (fn-nntp-hdr-octets
                           (fn-nntp-hdr-content
                            field
                            (fn-nntp-available-article group number articles))))
                         (fn-nntp-hdr-lines-for-numbers field group rest
                                                        articles))))
   :hints (("Goal" :expand ((fn-nntp-hdr-lines-for-numbers
                             field group (cons number rest) articles))
            :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-line
                                fn-nntp-hdr-octets fn-nntp-available-article)))))

(local
 (defthm fn-nss-hdr-lines-of-no-numbers
   (implies (not (consp numbers))
            (equal (fn-nntp-hdr-lines-for-numbers field group numbers articles)
                   nil))
   :hints (("Goal" :expand ((fn-nntp-hdr-lines-for-numbers field group numbers
                                                           articles))))))

(defthm fn-nss-xpat-lines-are-the-hdr-lines-of-the-hits
  (equal (fn-nntp-xpat-lines-for-numbers field patterns group numbers articles)
         (fn-nntp-hdr-lines-for-numbers
          field group (fn-nss-hits field patterns group numbers articles)
          articles))
  :hints (("Goal" :induct (fn-nss-hits field patterns group numbers articles)
           :expand ((fn-nntp-xpat-lines-for-numbers field patterns group numbers
                                                    articles))
           :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-line
                               fn-nntp-hdr-octets fn-nntp-xpat-matchesp
                               fn-nntp-available-article
                               fn-nntp-xpat-with-a-total-filter-is-the-hdr-block))))

; -----------------------------------------------------------------------------
; Membership: the range, the available article, the matcher.

(local
 (defthm fn-nss-member-of-insert-number
   (iff (member-equal x (fn-nntp-insert-number number numbers))
        (or (equal x number) (member-equal x numbers)))
   :hints (("Goal" :in-theory (enable fn-nntp-insert-number)))))

(local
 (defthm fn-nss-member-of-hits
   (iff (member-equal number (fn-nss-hits field patterns group numbers articles))
        (and (member-equal number numbers)
             (consp (fn-nntp-available-article group number articles))
             (fn-nntp-hdr-okp
              (fn-nntp-hdr-content
               field (fn-nntp-available-article group number articles)))
             (fn-nntp-xpat-matchesp
              patterns
              (fn-nntp-hdr-octets
               (fn-nntp-hdr-content
                field (fn-nntp-available-article group number articles))))))
   :hints (("Goal" :induct (fn-nss-hits field patterns group numbers articles)
            :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-octets
                                fn-nntp-xpat-matchesp fn-nntp-available-article)))))

(local
 (defthm fn-nss-available-article-number
   (implies (consp (fn-nntp-available-article group number articles))
            (and (posp number)
                 (equal (fn-nntp-article-number
                         group (fn-nntp-available-article group number articles))
                        number)
                 (member-equal (fn-nntp-available-article group number articles)
                               articles)))
   :hints (("Goal" :induct (fn-nntp-available-article group number articles)
            :in-theory (enable fn-nntp-available-article)))))

(local
 (defthm fn-nss-member-of-range-numbers
   (iff (member-equal number (fn-nntp-group-range-numbers group low high articles))
        (and (posp number) (<= low number) (<= number high)
             (consp (fn-nntp-available-article group number articles))))
   :hints (("Goal" :induct (fn-nntp-group-range-numbers group low high articles)
            :in-theory (enable fn-nntp-group-range-numbers fn-nntp-available-article)))))

; -----------------------------------------------------------------------------
; KEYSTONE: a number is a hit exactly when it is in scope, served and matches.

(defthm fn-nss-hits-are-the-scope
  (iff (member-equal number
                     (fn-nss-hits field patterns group
                                  (fn-nntp-group-range-numbers group low high
                                                               articles)
                                  articles))
       (and (posp number)
            (<= low number)
            (<= number high)
            (consp (fn-nntp-available-article group number articles))
            (fn-nntp-hdr-okp
             (fn-nntp-hdr-content
              field (fn-nntp-available-article group number articles)))
            (fn-nntp-xpat-matchesp
             patterns
             (fn-nntp-hdr-octets
              (fn-nntp-hdr-content
               field (fn-nntp-available-article group number articles))))))
  :hints (("Goal" :in-theory (disable fn-nntp-hdr-content fn-nntp-hdr-octets
                                      fn-nntp-xpat-matchesp
                                      fn-nntp-available-article
                                      fn-nntp-group-range-numbers))))

; KEYSTONE follows this lemma: a withdrawn number is never a hit.
; (A number the pinned step answers 423 withdrawn for is not held by the
; served archive; every hit is held there.)
(local
 (defthm fn-nss-available-is-found
   (implies (consp (fn-nntp-available-article group number articles))
            (consp (fn-nntp-find-group-number group number articles)))
   :hints (("Goal" :induct (fn-nntp-available-article group number articles)
            :in-theory (enable fn-nntp-available-article
                               fn-nntp-find-group-number
                               fn-nntp-article-number)))))

(defthm fn-nss-withdrawn-number-is-never-a-hit
  (implies (fn-nntp-number-withdrawn-p session archive index token)
           (not (member-equal (fn-nntp-decimal-value token)
                              (fn-nss-hits field patterns
                                           (fn-nntp-session-group session)
                                           numbers
                                           (fn-state-articles archive)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-number-withdrawn-p)
                                  (fn-nntp-hdr-content fn-nntp-hdr-octets
                                   fn-nntp-xpat-matchesp
                                   fn-nntp-available-article
                                   fn-nntp-find-group-number)))))

; -----------------------------------------------------------------------------
; KEYSTONE: the served step's XPAT reply over a range, as the scope's lines.

; The three hypotheses of fn-nntp-step-pinned-xpat-is-the-xpat-response this
; statement does not carry are implied by the ones it does: a keyword equal
; to XPAT is a keyword token (below), it is a token, and a pattern that
; parses is at least one argument (the empty join does not parse).

(defthm fn-nss-xpat-keyword-is-a-keyword-token
  (implies (fn-nntp-keywordp token "XPAT")
           (fn-nntp-keyword-tokenp token))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp fn-nntp-keyword-tokenp
                                     fn-nntp-keyword-tailp fn-nntp-upcase-byte
                                     fn-nntp-keyword-first-bytep
                                     fn-nntp-keyword-rest-bytep)
           :expand ((fn-nntp-upcase-keyword token)
                    (fn-nntp-upcase-keyword (cdr token))
                    (fn-nntp-upcase-keyword (cddr token))
                    (fn-nntp-upcase-keyword (cdddr token))
                    (fn-nntp-upcase-keyword (cddddr token))
                    (fn-nntp-keyword-tailp (cdr token))
                    (fn-nntp-keyword-tailp (cddr token))
                    (fn-nntp-keyword-tailp (cdddr token))
                    (fn-nntp-keyword-tailp (cddddr token))))))

(defthm fn-nntp-step-pinned-xpat-range-is-the-scope
  (let* ((args (cdr (fn-nntp-tokenize line)))
         (field (car args))
         (range (fn-nntp-parse-range (car (cdr args))))
         (parsed (fn-wildmat-parse-text (fn-nntp-xpat-join (cdr (cdr args)))))
         (group (fn-nntp-session-group session))
         (articles (fn-state-articles archive)))
    (implies (and (fn-nntp-sessionp session)
                  (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                  (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "XPAT")
                  (fn-nntp-hdr-fieldp field)
                  (fn-nntp-range-okp range)
                  (fn-wildmat-result-okp parsed)
                  group)
             (equal (fn-nntp-step-pinned session archive index verdicts env
                                         (list :command line))
                    (fn-nntp-multi
                     session (fn-nntp-hdr-initial t)
                     (fn-nntp-hdr-lines-for-numbers
                      field group
                      (fn-nss-hits field (fn-wildmat-result-value parsed) group
                                   (fn-nntp-group-range-numbers
                                    group (fn-nntp-range-low range)
                                    (fn-nntp-range-high range) articles)
                                   articles)
                      articles)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-nntp-step-pinned-xpat-is-the-xpat-response (:instance fn-nss-xpat-keyword-is-a-keyword-token (token (car (fn-nntp-tokenize line)))))
           :in-theory (e/d (fn-nntp-xpat-response fn-nntp-xpat-range)
                           (fn-nntp-step-pinned-xpat-is-the-xpat-response
                            fn-nntp-step-pinned
                            fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp
                            fn-nntp-sessionp fn-nntp-multi fn-nntp-hdr-initial
                            fn-nntp-group-range-numbers
                            fn-nntp-hdr-lines-for-numbers
                            fn-nntp-xpat-lines-for-numbers
                            fn-wildmat-parse-text fn-nntp-xpat-join
                            fn-nntp-parse-range fn-nntp-range-okp
                            fn-nntp-hdr-fieldp)))))
