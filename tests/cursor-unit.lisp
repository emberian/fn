; D6 evidence: the teeth of owed-cursor.lisp's keystones (docs/d-machines-
; nntp.md section 15.7). Until the cursor serves (D6 1/n), the teeth check the
; reference against hand-written replies (RFC 3977, H's model), that each
; negative case is caught, and that the seeded store publishes through C-S3:
; the served core answers the interim 503 then, so the rows stay owed.
; Run: sh tools/certify.sh tests/cursor-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-cru-groups* (fn2-profile-get :groups *fn2-cursor-profile*))
(defun fn2-cru-tab () (declare (xargs :verify-guards nil)) (coerce (list (code-char 9)) 'string))
;; Each seed's stored source: its header, an empty line, and a body with a
;; line that starts with "." (stuffed on the wire) and one that is only ".".
(defun fn2-cru-text (subject mid)
  (declare (xargs :verify-guards nil))
  (list "From: a@example.invalid" (fn2-csp-cat (list "Subject: " subject))
        "Date: Fri, 30 Oct 2026 12:00:00 +0000" (fn2-csp-cat (list "Message-ID: " mid))
        "Newsgroups: local.test" "" (fn2-csp-cat (list "body " subject)) ".dotted" "." "end"))
;; Its overview line as the transaction's path synthesizes it: the source's
;; octets (CRLF lines, unstuffed) and body lines, and the Xref field with the
;; profile's path identity and the article's number N.
(defun fn2-cru-line7 (subject mid)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list subject (fn2-cru-tab) "a@example.invalid" (fn2-cru-tab) "Fri, 30 Oct 2026 12:00:00 +0000"
                     (fn2-cru-tab) mid (fn2-cru-tab) "" (fn2-cru-tab)
                     (fn2-csp-str (len (fn2-cs-source (fn2-cru-text subject mid)))) (fn2-cru-tab) "4")))
(defun fn2-cru-line (subject mid n)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list (fn2-cru-line7 subject mid) (fn2-cru-tab) "Xref: fn2.invalid local.test:" (fn2-csp-str n))))
(defun fn2-cru-seed (subject mid n)
  (declare (xargs :verify-guards nil))
  (list 1 mid (fn2-cru-line subject mid n) (fn2-cru-text subject mid)))
(defconst *fn2-cru-seeds*
  (list (fn2-cru-seed "one" "<a@example.invalid>" 1)
        (fn2-cru-seed "two" "<b@example.invalid>" 2)
        (fn2-cru-seed "three" "<c@example.invalid>" 3)))
(assert-event (fn2-csp-seedsp *fn2-cru-seeds* *fn2-cru-groups* nil))

; One transcript, every covered command positive and refused.
(defconst *fn2-cru-lines*
  '("LIST" "NEXT" "STAT" "OVER" "LISTGROUP" "GROUP nope.nope" "GROUP local.empty" "NEXT" "GROUP local.test" "STAT"
    "NEXT" "NEXT" "NEXT" "LAST" "LAST" "LAST" "STAT 9" "STAT <b@example.invalid>" "STAT <z@example.invalid>" "LISTGROUP"
    "LISTGROUP local.test 2-" "LIST COUNTS" "LIST newsgroups" "OVER 2-3" "OVER 7-9" "XOVER 7-9" "OVER"
    "OVER <c@example.invalid>" "ARTICLE" "HEAD 2" "BODY <b@example.invalid>" "ARTICLE 9"
    "HEAD <z@example.invalid>" "QUIT"))
(assert-event (fn2-csp-linesp *fn2-cru-lines*))
(defun fn2-cru-ov (n subject mid)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list (fn2-csp-str n) (fn2-cru-tab) (fn2-cru-line subject mid n))))
(defun fn2-cru-expected ()
  (declare (xargs :verify-guards nil))
  (list "215 list of active newsgroups follows" "local.empty 0 1 y" "local.test 3 1 y" "."
        "412 no newsgroup selected" "412 no newsgroup selected" "412 no newsgroup selected" "412 no newsgroup selected"
        "411 no such newsgroup" "211 0 1 0 local.empty" "420 no current article"
        "211 3 1 3 local.test" "223 1 <a@example.invalid> retrieved"
        "223 2 <b@example.invalid> retrieved" "223 3 <c@example.invalid> retrieved" "421 no next article"
        "223 2 <b@example.invalid> retrieved" "223 1 <a@example.invalid> retrieved" "422 no previous article"
        "423 no article with that number" "223 0 <b@example.invalid> retrieved" "430 no article with that message-id"
        "211 3 1 3 local.test list follows" "1" "2" "3" "."
        "211 3 1 3 local.test list follows" "2" "3" "."
        "215 list of active newsgroups follows" "local.empty 0 1 0 y" "local.test 3 1 3 y" "."
        "215 list of newsgroups follows" "local.empty (no description)" "local.test (no description)" "."
        "224 overview information follows" (fn2-cru-ov 2 "two" "<b@example.invalid>") (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
        "423 no articles in that range" "420 no article(s) selected"
        "224 overview information follows" (fn2-cru-ov 1 "one" "<a@example.invalid>") "."
        "224 overview information follows" (fn2-cru-ov 3 "three" "<c@example.invalid>") "."
        ;; the stored octets: the posted header in its order, the body
        ;; dot-stuffed (".dotted" and "." each doubled)
        "220 1 <a@example.invalid> article follows" "Xref: fn2.invalid local.test:1"
        "From: a@example.invalid" "Subject: one" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
        "Message-ID: <a@example.invalid>" "Newsgroups: local.test" "" "body one" "..dotted" ".." "end" "."
        "221 2 <b@example.invalid> headers follow" "Xref: fn2.invalid local.test:2"
        "From: a@example.invalid" "Subject: two" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
        "Message-ID: <b@example.invalid>" "Newsgroups: local.test" "."
        "222 0 <b@example.invalid> body follows" "body two" "..dotted" ".." "end" "."
        "423 no article with that number" "430 no article with that message-id"
        "205 closing connection"))
(defun fn2-cru-expected-wire ()
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets (cons "200 fn-nntp experimental server ready" (fn2-cru-expected))) t))

(defun fn2-cru-subst (new old xs)
  (declare (xargs :verify-guards nil))
  (if (atom xs) nil (cons (if (equal (car xs) old) new (car xs)) (fn2-cru-subst new old (cdr xs)))))
; reply-exact. Positive: the reference gives the hand-written replies.
(defun fn2-cursor-test-spec ()
  (declare (xargs :verify-guards nil))
  (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-lines*) (fn2-cru-expected-wire)))
; Negative: an empty group answered 211 0 0 0 (LOW not high + 1), and a
; reader that saw one entry past its view (a fourth article), both differ.
(defun fn2-cursor-test-spec-negative ()
  (declare (xargs :verify-guards nil))
  (let ((want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-lines*)))
    (and (not (equal want (list (fn2-cw-crlf-octets (cons "200 fn-nntp experimental server ready"
                                                          (fn2-cru-subst "211 0 0 0 local.empty" "211 0 1 0 local.empty"
                                                                        (fn2-cru-expected))))
                                t)))
         (not (equal want (fn2-cursor-spec-wire *fn2-cru-groups*
                                                (append *fn2-cru-seeds* (list (fn2-cru-seed "four" "<d@example.invalid>" 4)))
                                                *fn2-cru-lines*))))))
; The subject runs: the seeds publish through C-S3 (seeded :ok), the core
; does not stop, and the cursor serves GROUP (D6 1/n).
(defun fn2-cursor-test-seeded ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-cursor-wire-run *fn2-cursor-profile* *fn2-cru-seeds*
                                (list (list (fn2-cw-crlf-octets '("GROUP local.test" "QUIT")) nil)))))
    (and (or (eq (nth 0 r) :ok) (cw "seeded ~x0~%" (nth 0 r)))
         (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r))
                    (list (fn2-cw-crlf-octets '("200 fn-nntp experimental server ready"
                                                "211 3 1 3 local.test" "205 closing connection"))
                          t))
             (cw "wire ~x0~%" (car (nth 2 r)))))))

; range-cost. Positive: OVER 1-2147483647 (the grammar's article-number cap) over three entries is three rows
; in the reference, and the bound it allows is a constant plus 16 per row.
(defun fn2-cursor-test-range-cost ()
  (declare (xargs :verify-guards nil))
  (let ((lines (fn2-cursor-over-lines 1 2147483647)))
    (and (fn2-csp-linesp lines)
         (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* lines)
                (list (fn2-cw-crlf-octets (list "200 fn-nntp experimental server ready" "211 3 1 3 local.test"
                                                "224 overview information follows"
                                                (fn2-cru-ov 1 "one" "<a@example.invalid>") (fn2-cru-ov 2 "two" "<b@example.invalid>")
                                                (fn2-cru-ov 3 "three" "<c@example.invalid>") "." "205 closing connection"))
                      t))
         (equal (+ *fn2-cursor-visits-base* (* *fn2-cursor-visits-per-entry* 3)) 112))))
; Negative: a cursor that steps every number of the range visits at least
; once per number, which the bound refuses for this range.
(defun fn2-cursor-test-range-cost-negative ()
  (declare (xargs :verify-guards nil))
  (< (+ *fn2-cursor-visits-base* (* *fn2-cursor-visits-per-entry* 3)) (- 2147483647 1)))

; view-pinned. Positive: the reference reads only the state at the pin.
; Negative: a reader without the position limit would see the later
; publication (the reference over the union differs).
(defconst *fn2-cru-later* (list (fn2-cru-seed "four" "<d@example.invalid>" 4)))
(defconst *fn2-cru-pinned-lines* '("GROUP local.test" "OVER 1-" "NEXT" "NEXT" "NEXT" "LAST" "STAT 3" "QUIT"))
(defun fn2-cursor-test-pinned ()
  (declare (xargs :verify-guards nil))
  (and (fn2-csp-seedsp (append *fn2-cru-seeds* *fn2-cru-later*) *fn2-cru-groups* nil)
       (fn2-csp-linesp *fn2-cru-pinned-lines*) (fn2-csp-no-repin-p (cdr *fn2-cru-pinned-lines*))
       (let ((r (fn2-cursor-serve-run *fn2-cursor-profile* *fn2-cru-seeds* *fn2-cru-later*
                                (list (list (fn2-cw-crlf-octets *fn2-cru-pinned-lines*) nil)))))
         ;; the later seed was published while the client read
         (or (eq (nth 0 r) :ok) (cw "pinned seeded ~x0~%" (nth 0 r))))))
(defun fn2-cursor-test-pinned-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-pinned-lines*)
              (fn2-cursor-spec-wire *fn2-cru-groups* (append *fn2-cru-seeds* *fn2-cru-later*) *fn2-cru-pinned-lines*))))

;; Served = reference (D6 1/n-b) over the transcript less OVER <id> (the
;; article's number in the group comes with the transaction's address
;; entries), whole and in small chunks.
(defconst *fn2-cru-served-lines* *fn2-cru-lines*)
(defun fn2-cursor-test-served (sizes)
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-solo *fn2-cru-seeds* *fn2-cru-served-lines* sizes))
        (want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-served-lines*)))
    (or (equal got want) (cw "served ~x0~%want ~x1~%" got want))))
;; LIST over a directory whose rows span pages: five groups of 200-octet
;; names (two rows a page of a 1,024-octet TX after its 256-octet key area),
;; so the scan resumes from the key TX keeps across every page.
(defun fn2-cru-long-name (c)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list "long." (coerce (make-list 190 :initial-element #\x) 'string) "." (coerce (list c) 'string))))
(defconst *fn2-cru-long-groups*
  (list (cons (fn2-cru-long-name #\c) 3) (cons (fn2-cru-long-name #\a) 1) (cons (fn2-cru-long-name #\e) 5)
        (cons (fn2-cru-long-name #\b) 2) (cons (fn2-cru-long-name #\d) 4)))
(defconst *fn2-cru-long-lines* '("LIST" "LIST COUNTS" "LIST NEWSGROUPS" "GROUP local.none" "QUIT"))
(defun fn2-cursor-test-list-pages ()
  (declare (xargs :verify-guards nil))
  (let* ((profile (put-assoc-equal :groups *fn2-cru-long-groups* *fn2-cursor-profile*))
         (r (fn2-cursor-serve-run profile nil nil (list (list (fn2-cw-crlf-octets *fn2-cru-long-lines*) '(5 2)))))
         (want (fn2-cursor-spec-wire *fn2-cru-long-groups* nil *fn2-cru-long-lines*)))
    (and (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r)) want) (cw "list pages ~x0~%want ~x1~%" (car (nth 2 r)) want)))))
; Negative: the listing in the profile's order (the reference sorts by
; name) differs, so the positive checks the order the scan delivers.
(defun fn2-cursor-test-list-pages-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-csp-list-rows "ACTIVE" (fn2-csp-sort *fn2-cru-long-groups*) nil)
              (fn2-csp-list-rows "ACTIVE" *fn2-cru-long-groups* nil))))
(defun fn2-cursor-test-pinned-served ()
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-interleaved *fn2-cru-seeds* *fn2-cru-later* *fn2-cru-pinned-lines* nil))
        (want (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-seeds* *fn2-cru-pinned-lines*)))
    (or (equal got want) (cw "pinned ~x0~%want ~x1~%" got want))))
(assert-event (fn2-cursor-test-spec))
(assert-event (fn2-cursor-test-spec-negative))
(assert-event (fn2-cursor-test-seeded))
(assert-event (fn2-cursor-test-range-cost))
(assert-event (fn2-cursor-test-range-cost-negative))
(assert-event (fn2-cursor-test-pinned))
(assert-event (fn2-cursor-test-pinned-negative))
(assert-event (fn2-cursor-test-served nil))
(assert-event (fn2-cursor-test-served '(7 3 1)))
(assert-event (fn2-cursor-test-pinned-served))
(assert-event (fn2-cursor-test-list-pages))
(assert-event (fn2-cursor-test-list-pages-negative))

;; End-to-end POST -> GROUP / OVER / OVER <id> / ARTICLE / HEAD / BODY without
;; seeding: the posted source is stored and read back through B's block read,
;; the overview's Xref field (filled after stage) first, then its header in its
;; posted order and its body dot-stuffed again.
(defconst *fn2-cru-post-lines*
  '("POST"
    "From: poster@example.invalid"
    "Subject: real body test"
    "Newsgroups: local.test"
    "Message-ID: <post1@example.invalid>"
    ""
    "real line 1"
    "..dot stuffed"
    "."
    "GROUP local.test"
    "OVER 1"
    "OVER <post1@example.invalid>"
    "HEAD 1"
    "BODY 1"
    "ARTICLE 1"
    "BODY <post1@example.invalid>"
    "QUIT"))
(defun fn2-cru-post-ov (num)
  (declare (xargs :verify-guards nil))
  (fn2-csp-cat (list num (fn2-cru-tab) "real body test" (fn2-cru-tab) "poster@example.invalid"
                     (fn2-cru-tab) (fn2-cru-tab) "<post1@example.invalid>"
                     (fn2-cru-tab) (fn2-cru-tab) "145" (fn2-cru-tab) "2"
                     (fn2-cru-tab) "Xref: fn2.invalid local.test:" num)))
(defun fn2-cru-post-expected-wire ()
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets
         (list "200 fn-nntp experimental server ready"
               "340 send article to be posted"
               "240 article received OK"
               "211 1 1 1 local.test"
               "224 overview information follows"
               (fn2-cru-post-ov "1")
               "."
               "224 overview information follows"
               (fn2-cru-post-ov "1")
               "."
               "221 1 <post1@example.invalid> headers follow"
               "Xref: fn2.invalid local.test:1"
               "From: poster@example.invalid"
               "Subject: real body test"
               "Newsgroups: local.test"
               "Message-ID: <post1@example.invalid>"
               "."
               "222 1 <post1@example.invalid> body follows"
               "real line 1"
               "..dot stuffed"
               "."
               "220 1 <post1@example.invalid> article follows"
               "Xref: fn2.invalid local.test:1"
               "From: poster@example.invalid"
               "Subject: real body test"
               "Newsgroups: local.test"
               "Message-ID: <post1@example.invalid>"
               ""
               "real line 1"
               "..dot stuffed"
               "."
               "222 0 <post1@example.invalid> body follows"
               "real line 1"
               "..dot stuffed"
               "."
               "205 closing connection"))
        t))
(defun fn2-cursor-test-post-roundtrip ()
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-solo nil *fn2-cru-post-lines* nil))
        (want (fn2-cru-post-expected-wire)))
    (or (equal got want) (cw "post-roundtrip ~x0~%want ~x1~%" got want))))
(assert-event (fn2-cursor-test-post-roundtrip))

;; D6 2/n (Brick H3): LIST variants & RFC 3977 wildmat filtering, NEWGROUPS,
;; NEWNEWS, and HDR/XHDR over message-id, current article, and ranges.
(defconst *fn2-cru-h3-lines*
  '("LIST ACTIVE local.*"
    "LIST ACTIVE *,!*.empty"
    "LIST ACTIVE comp.*"
    "LIST ACTIVE.TIMES"
    "LIST ACTIVE.TIMES local.*"
    "LIST COUNTS local.t?st"
    "LIST NEWSGROUPS *,!*.test"
    "LIST SUBSCRIPTIONS"
    "LIST SUBSCRIPTIONS *.test"
    "LIST OVERVIEW.FMT"
    "LIST HEADERS"
    "LIST HEADERS MSGID"
    "LIST HEADERS RANGE"
    "LIST DISTRIB.PATS"
    "LIST DISTRIBUTIONS"
    "NEWGROUPS 20261030 000000 GMT"
    "NEWNEWS local.* 20261030 000000 GMT"
    "NEWNEWS *,!*.test 20261030 000000"
    "NEWNEWS comp.* 20261030 000000"
    "HDR Subject"
    "XHDR Subject 1-2"
    "HDR Subject <b@example.invalid>"
    "XHDR Subject <b@example.invalid>"
    "HDR From <b@example.invalid>"
    "HDR :bytes <b@example.invalid>"
    "HDR :lines <b@example.invalid>"
    "HDR :fn-verified <b@example.invalid>"
    "HDR Subject <z@example.invalid>"
    "XHDR Subject <z@example.invalid>"
    "HDR :unknown <b@example.invalid>"
    "GROUP local.empty"
    "HDR Subject"
    "XHDR Subject"
    "HDR Subject 1-3"
    "XHDR Subject 1-3"
    "GROUP local.test"
    "HDR Subject"
    "XHDR Subject"
    "HDR Subject 2-3"
    "XHDR Message-ID 1-2"
    "HDR Date 1"
    "HDR References 1"
    "HDR :bytes 2-3"
    "XHDR :lines 1-2"
    "HDR X-Absent 1-2"
    "HDR Subject 9"
    "XHDR Subject 9"
    "HDR Subject 7-9"
    "XHDR Subject 7-9"
    "QUIT"))
(defun fn2-cru-h3-expected-wire ()
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets
         (list "200 fn-nntp experimental server ready"
               "215 list of active newsgroups follows" "local.empty 0 1 y" "local.test 3 1 y" "."
               "215 list of active newsgroups follows" "local.test 3 1 y" "."
               "215 list of active newsgroups follows" "."
               "215 information follows" "."
               "215 information follows" "."
               "215 list of active newsgroups follows" "local.test 3 1 3 y" "."
               "215 list of newsgroups follows" "local.empty (no description)" "."
               "215 list of recommended newsgroups follows" "local.empty" "local.test" "."
               "215 list of recommended newsgroups follows" "local.test" "."
               "215 order of fields in overview database"
               "Subject:" "From:" "Date:" "Message-ID:" "References:" "Bytes:" "Lines:" "Xref:full" "."
               "215 field list follows" ":" ":bytes" ":lines" "."
               "215 field list follows" ":" ":bytes" ":lines" "."
               "215 field list follows" ":" ":bytes" ":lines" "."
               "503 data item not stored"
               "503 data item not stored"
               "231 list of new newsgroups follows" "."
               "230 list of new articles by message-id follows"
               "<a@example.invalid>" "<b@example.invalid>" "<c@example.invalid>" "."
               "230 list of new articles by message-id follows" "."
               "230 list of new articles by message-id follows" "."
               "412 no newsgroup selected"
               "412 no newsgroup selected"
               "225 headers follow" "0 two" "."
               "221 header follows" "<b@example.invalid> two" "."
               "225 headers follow" "0 a@example.invalid" "."
               "225 headers follow" "0 164" "."
               "225 headers follow" "0 4" "."
               "225 headers follow" "0 absent no-field" "."
               "430 no article with that message-id"
               "430 no article with that message-id"
               "503 archive projection unavailable"
               "211 0 1 0 local.empty"
               "420 no current article"
               "420 no current article"
               "423 no articles in that range"
               "420 no article(s) selected"
               "211 3 1 3 local.test"
               "225 headers follow" "1 one" "."
               "221 header follows" "1 one" "."
               "225 headers follow" "2 two" "3 three" "."
               "221 header follows" "1 <a@example.invalid>" "2 <b@example.invalid>" "."
               "225 headers follow" "1 Fri, 30 Oct 2026 12:00:00 +0000" "."
               "225 headers follow" "1 " "."
               "225 headers follow" "2 164" "3 168" "."
               "221 header follows" "1 4" "2 4" "."
               "225 headers follow" "1 " "2 " "."
               "423 no articles in that range"
               "420 no article(s) selected"
               "423 no articles in that range"
               "420 no article(s) selected"
               "205 closing connection"))
        t))
(defun fn2-cursor-test-h3 (sizes)
  (declare (xargs :verify-guards nil))
  (let ((got (fn2-cursor-wire-solo *fn2-cru-seeds* *fn2-cru-h3-lines* sizes))
        (want (fn2-cru-h3-expected-wire)))
    (or (equal got want) (cw "h3 ~x0~%want ~x1~%" got want))))
;; Negative: wildmat filtering is not a no-op (unfiltered LIST ACTIVE includes
;; local.empty whereas LIST ACTIVE *,!*.empty excludes it; NEWNEWS *,!*.test
;; excludes local.test's articles).
(defun fn2-cursor-test-h3-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (equal (fn2-cursor-wire-solo *fn2-cru-seeds* '("LIST ACTIVE *,!*.empty" "QUIT") nil)
                   (fn2-cursor-wire-solo *fn2-cru-seeds* '("LIST ACTIVE" "QUIT") nil)))
       (not (equal (fn2-cursor-wire-solo *fn2-cru-seeds* '("NEWNEWS *,!*.test 20261030 000000" "QUIT") nil)
                   (fn2-cursor-wire-solo *fn2-cru-seeds* '("NEWNEWS local.* 20261030 000000" "QUIT") nil)))))
(assert-event (fn2-cursor-test-h3 nil))
(assert-event (fn2-cursor-test-h3 '(9 4 1)))
(assert-event (fn2-cursor-test-h3-negative))

;; Brick H5: peer transit verbs CHECK, IHAVE, and TAKETHIS over the seeded store.
(defconst *fn2-cru-h5-lines*
  '("MODE STREAM"
    "CHECK <b@example.invalid>"
    "CHECK <ihave1@example.invalid>"
    "IHAVE <a@example.invalid>"
    "IHAVE <ihave1@example.invalid>"
    "Path: peer!not-for-mail"
    "From: peer@example.invalid"
    "Subject: ihave one"
    "Date: Fri, 30 Oct 2026 12:00:00 +0000"
    "Newsgroups: local.test"
    "Message-ID: <ihave1@example.invalid>"
    ""
    "ihave body"
    "."
    "CHECK <ihave1@example.invalid>"
    "TAKETHIS <take1@example.invalid>"
    "Path: peer!not-for-mail"
    "From: peer@example.invalid"
    "Subject: take one"
    "Date: Fri, 30 Oct 2026 12:00:00 +0000"
    "Newsgroups: local.test"
    "Message-ID: <take1@example.invalid>"
    ""
    "take body"
    "."
    "TAKETHIS <take1@example.invalid>"
    "Path: peer!not-for-mail"
    "From: peer@example.invalid"
    "Subject: take one"
    "Date: Fri, 30 Oct 2026 12:00:00 +0000"
    "Newsgroups: local.test"
    "Message-ID: <take1@example.invalid>"
    ""
    "take body"
    "."
    "GROUP local.test"
    "QUIT"))
(defun fn2-cru-h5-expected-wire ()
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets
         (list "200 fn-nntp experimental server ready"
               "203 streaming permitted"
               "438 <b@example.invalid>"
               "238 <ihave1@example.invalid>"
               "435 duplicate"
               "335 send it; end with <CR-LF>.<CR-LF>"
               "235 article transferred OK"
               "438 <ihave1@example.invalid>"
               "239 <take1@example.invalid>"
               "439 <take1@example.invalid>"
               "211 5 1 5 local.test"
               "205 closing connection"))
        t))
(defconst *fn2-cru-h5-profile* (put-assoc-equal :peering-interim t *fn2-cursor-profile*))
(defun fn2-cursor-test-h5 (sizes)
  (declare (xargs :verify-guards nil))
  (let* ((r (fn2-cursor-wire-run *fn2-cru-h5-profile* *fn2-cru-seeds*
                                 (list (list (fn2-cw-crlf-octets *fn2-cru-h5-lines*) sizes t))))
         (got (car (nth 2 r)))
         (want (fn2-cru-h5-expected-wire)))
    (and (eq (nth 0 r) :ok)
         (equal (nth 3 r) 0)
         (or (equal got want) (cw "h5 ~x0~%want ~x1~%" got want)))))
(defun fn2-cursor-test-h5-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-cursor-wire-run *fn2-cru-h5-profile* *fn2-cru-seeds*
                                   (list (list (fn2-cw-crlf-octets '("CHECK <b@example.invalid>" "QUIT")) nil t)))
              (fn2-cursor-wire-run *fn2-cru-h5-profile* *fn2-cru-seeds*
                                   (list (list (fn2-cw-crlf-octets '("CHECK <ihave1@example.invalid>" "QUIT")) nil t))))))
(assert-event (fn2-cursor-test-h5 nil))
(assert-event (fn2-cursor-test-h5 '(11 3 1)))
(assert-event (fn2-cursor-test-h5-negative))

; The overview's Xref field (PRF-206's ninth field, "Xref: SERVER
; group:number") is ARTICLE's and HEAD's first header line, before the
; stored source, as fn1 served it and H's model reads it (RFC 5536
; 3.2.14); BODY has none. The node's wire equals the reference's, and both
; equal the hand-written lines.
(defconst *fn2-cru-xref-seeds* (list (fn2-cru-seed "one" "<a@example.invalid>" 1)))
(defconst *fn2-cru-xref-lines* '("GROUP local.test" "ARTICLE 1" "HEAD <a@example.invalid>" "BODY 1" "QUIT"))
(defun fn2-cursor-test-xref ()
  (declare (xargs :verify-guards nil))
  (let* ((head '("From: a@example.invalid" "Subject: one" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
                 "Message-ID: <a@example.invalid>" "Newsgroups: local.test"))
         (body '("body one" "..dotted" ".." "end"))
         (want (list (fn2-cw-crlf-octets
                      (append '("200 fn-nntp experimental server ready" "211 1 1 1 local.test"
                                "220 1 <a@example.invalid> article follows" "Xref: fn2.invalid local.test:1")
                              head '("") body '(".")
                              '("221 0 <a@example.invalid> headers follow" "Xref: fn2.invalid local.test:1")
                              head '(".") '("222 1 <a@example.invalid> body follows") body
                              '("." "205 closing connection")))
                     t))
         (spec (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-xref-seeds* *fn2-cru-xref-lines*))
         (r (fn2-cursor-wire-run *fn2-cursor-profile* *fn2-cru-xref-seeds*
                                 (list (list (fn2-cw-crlf-octets *fn2-cru-xref-lines*) nil)))))
    (and (or (equal spec want) (cw "xref spec ~x0~%" spec))
         (or (eq (nth 0 r) :ok) (cw "xref seeded ~x0~%" (nth 0 r)))
         (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r)) want) (cw "xref wire ~x0~%" (car (nth 2 r)))))))
; Negative: the same article without the field in its overview serves no
; Xref line, so the wire differs.
(defun fn2-cursor-test-xref-negative ()
  (declare (xargs :verify-guards nil))
  (not (equal (fn2-cursor-spec-wire *fn2-cru-groups*
                                    (list (list 1 "<a@example.invalid>" (fn2-cru-line7 "one" "<a@example.invalid>")
                                                (fn2-cru-text "one" "<a@example.invalid>")))
                                    *fn2-cru-xref-lines*)
              (fn2-cursor-spec-wire *fn2-cru-groups* *fn2-cru-xref-seeds* *fn2-cru-xref-lines*))))
(assert-event (and (fn2-cursor-test-xref) (fn2-cursor-test-xref-negative)))
