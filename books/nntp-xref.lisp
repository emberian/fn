; fn: the Xref overview field of the served reader (R3, PRF-206).
;
; RFC 3977 section 8.3.2 lets an overview line carry fields after the eight
; mandatory ones, each named by LIST OVERVIEW.FMT (section 8.4).  fn's
; served dispatcher (books/nntp.lisp `fn-nntp-archive-command-pinned')
; renders a ninth field in the "full" form, the header name included:
;
;     Xref: SERVER group:number group:number ...
;
; the RFC 5536 section 3.2.14 syntax (server-name then locations).  SERVER
; is the connection's posting agent, the node's <path-identity>
; (books/owner-agent.lisp `fn-oag-listing' carries it as the listing's third
; element; `fn-oag-post-config-agent-is-the-path-identity').  The locations
; are the article's memberships at their LOCAL numbers, the numbers this
; node's reader commands and group index use (`fn-nntp-article-number',
; books/nntp-projection.lisp; the index entries of books/index.lisp
; `fn-index-article-entries'); they are never merged into a global
; numbering (AGENTS.md).  A newsreader that tracks Xref marks a cross-posted
; article read in every group it names (RFC 5536 section 3.2.14: "used to
; mark cross-posted articles as read").
;
; RFC requirement / fn guarantee / local policy:
;   * RFC 3977 section 8.3.2 (requirement): a field past the eighth is named
;     in LIST OVERVIEW.FMT and in the full form carries its name.  The served
;     LIST OVERVIEW.FMT names "Xref:full" exactly when OVER renders the field
;     (both on `fn-nntp-xref-server' of the environment).
;   * fn guarantee (PRF-206): the pairs are exactly the (group . number)
;     pairs at which the node serves the article (`fn-xref-pairs-exact'),
;     each the index entry the node's group index holds for it
;     (`fn-xref-pair-is-an-index-entry'); the line is the eight-field line
;     followed by TAB and this field (`fn-nov-served-line'); with no server
;     the renderer is the eight-field one (`...-without-a-server').
;   * local policy: the field is overview metadata only.  ARTICLE and HEAD
;     serve the stored octets as held (peering section 2.3); no Xref is
;     spliced into them, and a supplied Xref is refused at injection
;     (books/injection.lisp, RFC 5537 section 3.5 item 2).  A membership
;     whose group octets are not an Xref word (printable, no colon) is not
;     listed; `fn-record-group-namep' admits no such group.

(in-package "ACL2")
(include-book "nntp-range-indexed")


; -----------------------------------------------------------------------------
; The server name the environment carries

(defun fn-nntp-listing-server (listing)
  (declare (xargs :guard t))
  (if (and (consp listing) (consp (cdr listing)) (consp (cddr listing)))
      (car (cddr listing))
    nil))

; An Xref group word: printable US-ASCII, no colon (the location separator),
; no space.
(defun fn-xref-octetp (b)
  (declare (xargs :guard t))
  (and (integerp b) (<= 33 b) (<= b 126) (not (equal b 58))))

(defun fn-xref-octetsp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-xref-octetp (car bytes)) (fn-xref-octetsp (cdr bytes)))
    (null bytes)))

(defun fn-xref-wordp (bytes)
  (declare (xargs :guard t))
  (and (consp bytes) (fn-xref-octetsp bytes)))

; A server name: RFC 5536 section 3.2.14 makes it a <path-identity> (RFC
; 5537 section 3.2), which may carry a colon; printable US-ASCII.
(defun fn-xref-server-octetsp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (integerp (car bytes)) (<= 33 (car bytes)) (<= (car bytes) 126)
           (fn-xref-server-octetsp (cdr bytes)))
    (null bytes)))

(defun fn-xref-serverp (bytes)
  (declare (xargs :guard t))
  (and (consp bytes) (fn-xref-server-octetsp bytes)))

; The server name of the environment when it is one, else nil: a blind
; environment (`fn-nntp-env') has none, and then no field is rendered.
(defun fn-nntp-xref-server (env)
  (declare (xargs :guard t :verify-guards nil))
  (let ((server (fn-nntp-listing-server (fn-nntp-env-listing env))))
    (if (fn-xref-serverp server) server nil)))

(defthm fn-nntp-xref-server-is-a-server
  (or (null (fn-nntp-xref-server env))
      (fn-xref-serverp (fn-nntp-xref-server env)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; The pairs

; The memberships MS of ARTICLE that are served: the group is a string whose
; octets are an Xref word and the number is the article's available local
; number in it.
(defun fn-xref-pairs-of (ms article)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ms)
      (let ((m (car ms)))
        (if (and (consp m)
                 (stringp (car m))
                 (fn-xref-wordp (fn-nntp-string-octets (car m)))
                 (posp (cdr m))
                 (equal (fn-nntp-article-number (car m) article) (cdr m)))
            (cons m (fn-xref-pairs-of (cdr ms) article))
          (fn-xref-pairs-of (cdr ms) article)))
    nil))

(defun fn-xref-pairs (article)
  (declare (xargs :guard t :verify-guards nil))
  (fn-xref-pairs-of (fn-article-memberships article) article))

(defthm fn-xref-member-pairs-of
  (iff (member-equal (cons g n) (fn-xref-pairs-of ms article))
       (and (member-equal (cons g n) ms)
            (stringp g)
            (fn-xref-wordp (fn-nntp-string-octets g))
            (posp n)
            (equal (fn-nntp-article-number g article) n)))
  :hints (("Goal" :induct (fn-xref-pairs-of ms article)
           :in-theory (disable fn-nntp-article-number fn-xref-wordp
                               fn-nntp-string-octets))))

(defthm fn-xref-membership-number-is-a-member
  (implies (and (posp (fn-nntp-membership-number g ms)) (stringp g))
           (member-equal (cons g (fn-nntp-membership-number g ms)) ms))
  :hints (("Goal" :in-theory (enable fn-nntp-membership-number))))

; The keystone (PRF-206 (a)): the Xref of an article names exactly the
; groups and numbers at which the node serves it, the local number
; `fn-nntp-article-number' that GROUP, OVER, ARTICLE n and LISTGROUP number
; it by.
(defthm fn-xref-pairs-exact
  (iff (member-equal (cons g n) (fn-xref-pairs article))
       (and (stringp g)
            (fn-xref-wordp (fn-nntp-string-octets g))
            (posp n)
            (equal (fn-nntp-article-number g article) n)))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-article-number)
                           (fn-xref-wordp fn-nntp-string-octets
                                          fn-nntp-membership-number))
           :use ((:instance fn-xref-membership-number-is-a-member
                            (ms (fn-article-memberships article)))))))

; The group index side (PRF-206 (b)): each listed pair is an entry the
; index builds for the article (books/index.lisp `fn-index-article-entries',
; the rows `fn-gidx-build' buckets by group).
(defthm fn-xref-member-index-membership-entries
  (implies (member-equal (cons g n) ms)
           (member-equal (fn-index-entry g n msgid)
                         (fn-index-membership-entries msgid ms)))
  :hints (("Goal" :in-theory (enable fn-index-membership-entries))))

(defthm fn-xref-pair-is-an-index-entry
  (implies (member-equal (cons g n) (fn-xref-pairs article))
           (member-equal (fn-index-entry g n (fn-article-msgid article))
                         (fn-index-article-entries article)))
  :hints (("Goal" :in-theory (e/d (fn-index-article-entries fn-xref-pairs)
                                  (fn-xref-pairs-exact fn-xref-wordp
                                   fn-nntp-string-octets
                                   fn-nntp-article-number)))))

; -----------------------------------------------------------------------------
; The field and the line

(defun fn-xref-locations (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (append (list 32)
              (fn-nntp-string-octets (fn-ag-car (fn-ag-car pairs)))
              (list 58)
              (fn-nntp-decimal-field (fn-ag-cdr (fn-ag-car pairs)))
              (fn-xref-locations (cdr pairs)))
    nil))

(defconst *fn-xref-name* '(88 114 101 102 58 32)) ; "Xref: "

(defun fn-xref-field (server pairs)
  (declare (xargs :guard t :verify-guards nil))
  (append *fn-xref-name* (if (true-listp server) server nil)
          (fn-xref-locations pairs)))

; The served overview line: the eight fields, then, with a server, TAB and
; the Xref field of the article the line describes.
(defun fn-nov-served-line (number over server article)
  (declare (xargs :guard t :verify-guards nil))
  (if server
      (append (fn-nov-line number over)
              (cons 9 (fn-xref-field server (fn-xref-pairs article))))
    (fn-nov-line number over)))

; -----------------------------------------------------------------------------
; The served renderers

(defun fn-nov-served-lines-numbered (numbers nidx trie server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-nidx-number-article number nidx trie))
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-served-line number over server article)
                  (fn-nov-served-lines-numbered (cdr numbers) nidx trie server fn-arena))
          (fn-nov-served-lines-numbered (cdr numbers) nidx trie server fn-arena)))
    nil))

; With no server the served renderer is the eight-field renderer, so every
; keystone of `fn-nov-lines-for-numbers-numbered' holds of it.
(defthm fn-nov-served-lines-numbered-without-a-server
  (equal (fn-nov-served-lines-numbered numbers nidx trie nil fn-arena)
         (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena))
  :hints (("Goal" :in-theory (disable fn-nov-overview fn-nov-okp fn-nov-line
                                      fn-gidx-nidx-number-article
                                      fn-rcl-tombstonep))))

; Each number of the range whose article the number index resolves, and
; which is not reclaimed and has an overview, has its line: the eight fields
; and the Xref of THAT article.
(defthm fn-nov-served-lines-numbered-has-the-article-line
  (let ((article (fn-gidx-nidx-number-article n nidx trie)))
    (implies (and (member-equal n numbers)
                  (consp article)
                  (not (fn-nntp-article-tombstonep article fn-arena))
                  (fn-nov-okp (fn-nov-overview article fn-arena)))
             (member-equal (fn-nov-served-line n (fn-nov-overview article fn-arena)
                                               server article)
                           (fn-nov-served-lines-numbered numbers nidx trie
                                                         server fn-arena))))
  :hints (("Goal" :in-theory (disable fn-nov-overview fn-nov-okp
                                      fn-nov-served-line
                                      fn-gidx-nidx-number-article
                                      fn-rcl-tombstonep))))

;; The served lines ARE the eight-field lines, each followed by its suffix:
;; the eight fields of every served OVER line are what
;; `fn-nov-lines-for-numbers-numbered' renders, which
;; books/nntp-range-indexed-invariants.lisp ties to the archive fold.
(defun fn-nov-served-suffixes (numbers nidx trie server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-gidx-nidx-number-article number nidx trie))
             (over (if (and (consp article)
                            (not (fn-nntp-article-tombstonep article fn-arena)))
                       (fn-nov-overview article fn-arena)
                     (list :error))))
        (if (fn-nov-okp over)
            (cons (if server
                      (cons 9 (fn-xref-field server (fn-xref-pairs article)))
                    nil)
                  (fn-nov-served-suffixes (cdr numbers) nidx trie server fn-arena))
          (fn-nov-served-suffixes (cdr numbers) nidx trie server fn-arena)))
    nil))

(defun fn-nov-append-each (lines suffixes)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp lines)
      (cons (if (consp suffixes)
                (append (car lines) (car suffixes))
              (car lines))
            (fn-nov-append-each (cdr lines) (if (consp suffixes)
                                                (cdr suffixes)
                                              nil)))
    nil))

(defthmd fn-nov-served-lines-numbered-extend-the-eight-fields
  (equal (fn-nov-served-lines-numbered numbers nidx trie server fn-arena)
         (fn-nov-append-each
          (fn-nov-lines-for-numbers-numbered numbers nidx trie fn-arena)
          (fn-nov-served-suffixes numbers nidx trie server fn-arena)))
  :hints (("Goal" :induct (fn-nov-served-lines-numbered numbers nidx trie server fn-arena)
           :in-theory (disable fn-nov-overview fn-nov-okp fn-nov-line
                               fn-xref-field fn-xref-pairs
                               fn-gidx-nidx-number-article
                               fn-rcl-tombstonep))))

; OVER/XOVER of a range: `fn-nntp-over-range-indexed' with the served line.
(defun fn-nntp-over-range-served (session buckets trie token legacyp server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((entries (fn-gidx-bucket group buckets))
             (numbers (fn-nntp-index-group-range-numbers
                       entries group (fn-nntp-range-low range)
                       (fn-nntp-range-high range)))
             (lines (fn-nov-served-lines-numbered
                     numbers (fn-gidx-bucket-numbers group buckets) trie
                     server fn-arena)))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single
           session (if legacyp "420 no article(s) selected"
                     "423 no articles in that range")))))))

(defthm fn-nntp-over-range-served-without-a-server
  (equal (fn-nntp-over-range-served session buckets trie token legacyp nil fn-arena)
         (fn-nntp-over-range-indexed session buckets trie token legacyp fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-indexed)
                                  (fn-nov-served-lines-numbered
                                   fn-nov-lines-for-numbers-numbered
                                   fn-gidx-bucket fn-gidx-bucket-numbers
                                   fn-nntp-index-group-range-numbers
                                   fn-nntp-multi fn-nntp-single
                                   fn-nntp-parse-range)))))

; OVER/XOVER with no argument: the current article's line.
(defun fn-nntp-over-current-served (session archive server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article
                        group current (fn-state-articles archive))))
          (if (not (consp article))
              (fn-nntp-single session "420 no current article")
            (if (fn-nntp-article-tombstonep article fn-arena)
                (fn-nntp-single session "423 article reclaimed")
              (let ((over (fn-nov-overview article fn-arena)))
                (if (fn-nov-okp over)
                    (fn-nntp-multi session "224 overview information follows"
                                   (list (fn-nov-served-line current over
                                                             server article)))
                  (fn-nntp-single
                   session "503 stored article framing unavailable"))))))))))

(defthm fn-nntp-over-current-served-without-a-server
  (equal (fn-nntp-over-current-served session archive nil fn-arena)
         (fn-nntp-over-current session archive fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-current)
                                  (fn-nov-overview fn-nov-okp fn-nov-line
                                   fn-nntp-available-article fn-rcl-tombstonep
                                   fn-nntp-multi fn-nntp-single)))))

; OVER <message-id>: number 0 (RFC 3977 section 8.3.2).
(defun fn-nntp-over-msgid-served (session archive token server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (if (fn-nntp-article-tombstonep article fn-arena)
          (fn-nntp-single session "430 article reclaimed")
        (let ((over (fn-nov-overview article fn-arena)))
          (if (fn-nov-okp over)
              (fn-nntp-multi session "224 overview information follows"
                             (list (fn-nov-served-line 0 over server article)))
            (fn-nntp-single session
                            "503 stored article framing unavailable")))))))

(defthm fn-nntp-over-msgid-served-without-a-server
  (equal (fn-nntp-over-msgid-served session archive token nil fn-arena)
         (fn-nntp-over-msgid session archive token fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-nntp-over-msgid)
                                  (fn-nov-overview fn-nov-okp fn-nov-line
                                   fn-find-article fn-rcl-tombstonep
                                   fn-nntp-multi fn-nntp-single)))))

; LIST OVERVIEW.FMT when OVER renders the Xref field (RFC 3977 section 8.4:
; "Xref:full", the full form).  The sixth and seventh lines are section
; 8.4.2's compatibility form, "Bytes:" and "Lines:" ("for compatibility
; with existing implementations"; PKT-667, PRF-243): slrn 1.0.3 accepts
; only that form and otherwise disables XOVER (measured 2026-09-27, lane
; reader-clients-2).  The fields and their order are unchanged: the sixth
; is still the :bytes metadata item and the seventh :lines.
(defconst *fn-nov-fmt-xref-lines*
  '("Subject:" "From:" "Date:" "Message-ID:" "References:" "Bytes:" "Lines:"
    "Xref:full"))

(defun fn-nntp-list-overview-fmt-served (session)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-multi-octets
   session (fn-nntp-string-octets "215 order of fields in overview database")
   (fn-nov-fmt-octet-lines *fn-nov-fmt-xref-lines*)))

; -----------------------------------------------------------------------------
; Session and effects

(defthm fn-nntp-over-range-served-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-over-range-served session buckets trie token legacyp server fn-arena))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-multi
                                   fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-served-lines-numbered)))))

(defthm fn-nntp-over-current-served-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-over-current-served session archive server fn-arena))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-multi
                                   fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-overview fn-nov-served-line)))))

(defthm fn-nntp-over-msgid-served-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-over-msgid-served session archive token server fn-arena))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-single fn-nntp-multi
                                   fn-nntp-result-session fn-nntp-make-result)
                                  (fn-nov-overview fn-nov-served-line)))))

(defthm fn-nntp-list-overview-fmt-served-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-list-overview-fmt-served session))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-multi-octets
                                     fn-nntp-result-session
                                     fn-nntp-make-result))))

;; The served dispatcher's Xref arms (books/nntp.lisp
;; `fn-nntp-archive-command-pinned' asks this first): with a server name in
;; the environment, LIST OVERVIEW.FMT names Xref:full and every OVER/XOVER
;; line carries the Xref field; otherwise nil, and the dispatcher answers
;; as before.  One call in the dispatcher, so a proof that unfolds the
;; dispatcher splits on it once (the lemmas below), not on four arms.
(defun fn-nntp-xref-reply (session archive index env keyword args fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (cond
   ((and (fn-nntp-keywordp keyword "LIST")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (fn-nntp-keyword-tokenp (car args))
         (fn-nntp-keywordp (car args) "OVERVIEW.FMT"))
    (fn-nntp-list-overview-fmt-served session))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (fn-gidx-pinp index)
         (consp args) (null (cdr args))
         (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
    (fn-nntp-over-range-served
     session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index)
     (car args) (fn-nntp-keywordp keyword "XOVER") (fn-nntp-xref-server env) fn-arena))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-nntp-xref-server env)
         (null args))
    (fn-nntp-over-current-served session archive (fn-nntp-xref-server env) fn-arena))
   ((and (fn-nntp-keywordp keyword "OVER")
         (fn-nntp-xref-server env)
         (consp args) (null (cdr args))
         (not (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
         (fn-nntp-message-id-tokenp (car args)))
    (fn-nntp-over-msgid-served session archive (car args)
                               (fn-nntp-xref-server env) fn-arena))
   (t nil)))

(defthm fn-nntp-xref-reply-preserves-session
  (implies (fn-nntp-xref-reply session archive index env keyword args fn-arena)
           (equal (fn-nntp-result-session
                   (fn-nntp-xref-reply session archive index env keyword args fn-arena))
                  session))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server
                                      fn-gidx-pinp fn-nntp-parse-range
                                      fn-nntp-range-okp fn-nntp-keyword-tokenp
                                      fn-nntp-message-id-tokenp
                                      fn-nntp-over-range-served
                                      fn-nntp-over-current-served
                                      fn-nntp-over-msgid-served
                                      fn-nntp-list-overview-fmt-served
                                      fn-nntp-result-session))))

(defthm fn-nntp-xref-reply-without-a-server
  (implies (not (fn-nntp-xref-server env))
           (not (fn-nntp-xref-reply session archive index env keyword args fn-arena))))

(defthm fn-nntp-xref-reply-only-for-over-and-list
  (implies (and (not (fn-nntp-keywordp keyword "OVER"))
                (not (fn-nntp-keywordp keyword "XOVER"))
                (not (fn-nntp-keywordp keyword "LIST")))
           (not (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server))))

(defthm fn-nntp-xref-reply-only-for-over-and-overview-fmt
  (implies (and (not (fn-nntp-keywordp keyword "OVER"))
                (not (fn-nntp-keywordp keyword "XOVER"))
                (not (and (consp args)
                          (fn-nntp-keywordp (car args) "OVERVIEW.FMT"))))
           (not (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server))))

(verify-guards fn-nntp-xref-server)
(verify-guards fn-xref-pairs-of)
(verify-guards fn-xref-pairs)
(verify-guards fn-xref-locations)
(verify-guards fn-xref-field)
(verify-guards fn-nov-served-line)
(verify-guards fn-nov-served-lines-numbered)
(verify-guards fn-nntp-over-range-served)
(verify-guards fn-nntp-over-current-served)
(verify-guards fn-nntp-over-msgid-served)
(verify-guards fn-nntp-list-overview-fmt-served)
(verify-guards fn-nntp-xref-reply)

; Export: the served renderers and the server test are withdrawn, so that a
; book unfolding the pinned dispatcher sees each new arm as one call (the
; keystones above and books/nntp-xref-invariants.lisp name them); left
; enabled they expand under every dispatcher proof.
(in-theory (disable fn-nntp-xref-server fn-nntp-listing-server fn-xref-serverp fn-xref-wordp
    fn-xref-pairs fn-xref-field fn-nov-served-line fn-nov-served-lines-numbered
    fn-nov-served-suffixes fn-nov-append-each fn-nntp-over-range-served
    fn-nntp-over-current-served fn-nntp-over-msgid-served
    fn-nntp-list-overview-fmt-served fn-nntp-xref-reply))
