; Teeth for the served Xref overview field (R3, PRF-206; books/nntp-xref.lisp,
; books/owner-xref-read.lisp).  A cross-posted article, the served OVER
; range / current / message-id forms and LIST OVERVIEW.FMT, with and
; without a server name; each keystone's hypotheses fail by name.
(in-package "ACL2")
(include-book "../../books/owner-xref-read")
(include-book "must-fail-checked")

(defun fn-xrt-payload (id subject)
  (append (fn-nntp-string-octets "Message-ID: ")
          (fn-nntp-string-octets id) '(13 10)
          (fn-nntp-string-octets "Subject: ")
          (fn-nntp-string-octets subject) '(13 10 13 10 88 13 10)))

(defconst *xrt-groups* '("fn.one" "fn.two" "fn.three"))
; A: cross-posted to fn.one (2) and fn.two (70).  B: fn.three only.
; The acceptance payload is a handle into the arena (records-flip,
; books/held-record.lisp): A's bytes are interned first (handle 0), B's
; second (handle 1).  *xrt-a-wire* is A with its bytes (alpha of *xrt-a*):
; the served overview is A's bytes' overview, so every expected line below
; is computed from it, as before the flip.
(defconst *xrt-a-wire*
  (fn-make-article "<xrt-a@example.invalid>"
                   (fn-xrt-payload "<xrt-a@example.invalid>" "A")
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 70))
                   t 841000000))
(defconst *xrt-a*
  (fn-make-article "<xrt-a@example.invalid>" 0
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 70))
                   t 841000000))
(defconst *xrt-b*
  (fn-make-article "<xrt-b@example.invalid>" 1
                   '("fn.three") (list (cons "fn.three" 9))
                   t 841000000))
(include-book "arena-lift")
;; The arena: handle 0 = A's bytes, 1 = B's bytes.
(defconst *sr-arena*
  (list (fn-xrt-payload "<xrt-a@example.invalid>" "A")
        (fn-xrt-payload "<xrt-b@example.invalid>" "B")))
(bpr-lift fn-nntp-archive-command 5)
(bpr-lift fn-nntp-archive-command-pinned 7)
(bpr-lift fn-nntp-over-range-served 6)
(bpr-lift fn-nov-overview 1)
(assert-event (equal (car (in-arena-fn-nov-overview *sr-arena* *xrt-a-wire*)) :ok))
(defconst *xrt-articles* (list *xrt-a* *xrt-b*))
(defconst *xrt-state*
  (fn-make-state *xrt-groups*
                 (list (cons "fn.one" 3) (cons "fn.two" 71) (cons "fn.three" 10))
                 *xrt-articles* 2 nil nil))
(defconst *xrt-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *xrt-state*) "fn.two" 70))
(defconst *xrt-pin*
  (fn-gidx-pin (fn-midx-build *xrt-articles*) (fn-gidx-build *xrt-articles*)))
(defconst *xrt-server* (fn-nntp-string-octets "news.example.org"))
(defconst *xrt-env*
  (fn-nntp-env-full nil nil nil (list nil nil *xrt-server*) nil))
(defconst *xrt-blind* (fn-nntp-env nil nil nil))

(assert-event (and (fn-statep *xrt-state*) (fn-nntp-sessionp *xrt-session*)
                   (fn-gidx-pinp *xrt-pin*)
                   (equal (fn-nntp-xref-server *xrt-env*) *xrt-server*)
                   (null (fn-nntp-xref-server *xrt-blind*))))

; The pairs: exactly A's two local numbers, in membership order.
(assert-event (equal (fn-xref-pairs *xrt-a*)
                     (list (cons "fn.one" 2) (cons "fn.two" 70))))
(assert-event (equal (fn-xref-field *xrt-server* (fn-xref-pairs *xrt-a*))
                     (fn-nntp-string-octets
                      "Xref: news.example.org fn.one:2 fn.two:70")))

(defconst *xrt-a-line*
  (append (fn-nov-line 70 (in-arena-fn-nov-overview *sr-arena* *xrt-a-wire*))
          (cons 9 (fn-nntp-string-octets
                   "Xref: news.example.org fn.one:2 fn.two:70"))))

; OVER of a range in fn.two, OVER with no argument (current = 70), and OVER
; by Message-ID (number 0), through the pinned dispatcher with a server.
(defconst *xrt-224* "224 overview information follows")
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100")))
        (fn-nntp-multi *xrt-session* *xrt-224* (list *xrt-a-line*))))
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "XOVER") nil)
        (fn-nntp-multi *xrt-session* *xrt-224* (list *xrt-a-line*))))
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "<xrt-a@example.invalid>")))
        (fn-nntp-multi
         *xrt-session* *xrt-224*
         (list (append (fn-nov-line 0 (in-arena-fn-nov-overview *sr-arena* *xrt-a-wire*))
                       (cons 9 (fn-nntp-string-octets
                                "Xref: news.example.org fn.one:2 fn.two:70")))))))
; XOVER has no message-id form (RFC 2980 section 2.8): still 501.
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "XOVER") (list (fn-nntp-string-octets "<xrt-a@example.invalid>")))
        (fn-nntp-single *xrt-session* "501 syntax error")))
; LIST OVERVIEW.FMT names Xref:full with a server, not without.
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "LIST") (list (fn-nntp-string-octets "OVERVIEW.FMT")))
        (fn-nntp-multi-octets
         *xrt-session*
         (fn-nntp-string-octets "215 order of fields in overview database")
         (fn-nov-fmt-octet-lines
          '("Subject:" "From:" "Date:" "Message-ID:" "References:" "Bytes:"
            "Lines:" "Xref:full")))))
; A blind environment answers the eight-field lines and the seven-line
; format exactly as before (the without-a-server theorems).
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-blind* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100")))
        (fn-nntp-multi *xrt-session* *xrt-224*
                       (list (fn-nov-line 70 (in-arena-fn-nov-overview *sr-arena* *xrt-a-wire*))))))
(assert-event
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-blind* (fn-nntp-string-octets "LIST") (list (fn-nntp-string-octets "OVERVIEW.FMT")))
        (fn-nntp-list-overview-fmt *xrt-session*)))

; Reachable witness of fn-xref-pairs-exact, both directions.
(assert-event
 (and (member-equal (cons "fn.two" 70) (fn-xref-pairs *xrt-a*))
      (equal (fn-nntp-article-number "fn.two" *xrt-a*) 70)
      (not (member-equal (cons "fn.two" 71) (fn-xref-pairs *xrt-a*)))
      (not (member-equal (cons "fn.three" 9) (fn-xref-pairs *xrt-a*)))
      (member-equal (fn-index-entry "fn.one" 2 "<xrt-a@example.invalid>")
                    (fn-index-article-entries *xrt-a*))))

; A membership list naming a group twice: only the available (first)
; number is listed, since only it is served.  A malformed record, never
; produced by acceptance; it shows the number condition has teeth.
(defconst *xrt-dup*
  (fn-make-article "<xrt-d@example.invalid>"
                   (fn-xrt-payload "<xrt-d@example.invalid>" "D")
                   '("fn.one")
                   (list (cons "fn.one" 5) (cons "fn.one" 6))
                   t 841000000))
(assert-event (equal (fn-xref-pairs *xrt-dup*) (list (cons "fn.one" 5))))
(must-fail-checked
 (defthm fn-xrt-pairs-without-the-number-condition
   (iff (member-equal (cons g n) (fn-xref-pairs article))
        (and (member-equal (cons g n) (fn-article-memberships article))
             (stringp g) (posp n)))
   :hints (("Goal" :in-theory (disable fn-xref-pairs-exact)))))
; A group whose octets carry a colon cannot be an Xref location.
(defconst *xrt-colon*
  (fn-make-article "<xrt-c@example.invalid>"
                   (fn-xrt-payload "<xrt-c@example.invalid>" "C")
                   '("fn:bad") (list (cons "fn:bad" 1)) t 841000000))
(assert-event (and (equal (fn-nntp-article-number "fn:bad" *xrt-colon*) 1)
                   (null (fn-xref-pairs *xrt-colon*))))

; fn-nov-served-line-is-a-clean-line: the server hypothesis is needed (a
; server carrying LF would split the line).
(assert-event
 (not (fn-nov-clean-linep
       (fn-nov-served-line 1 (in-arena-fn-nov-overview *sr-arena* *xrt-a-wire*) '(97 10 98) *xrt-a-wire*))))
(must-fail-checked
 (defthm fn-xrt-served-line-clean-without-server-word
   (implies (fn-nov-overviewp over)
            (fn-nov-clean-linep (fn-nov-served-line number over server article)))))

; fn-nntp-archive-command-pinned-over-range-served: each hypothesis.
(must-fail-checked
 (defthm fn-xrt-over-range-served-without-server
   (implies (and (fn-nntp-keywordp keyword "OVER")
                 (fn-gidx-pinp index)
                 (consp args) (null (cdr args))
                 (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
            (equal (fn-nntp-archive-command-pinned session archive index verdicts env keyword args fn-arena)
                   (fn-nntp-over-range-served session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index) (car args) nil (fn-nntp-xref-server env) fn-arena)))))
(assert-event ; the blind-env witness: the unserved answer differs
 (not (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-env* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100")))
             (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* *xrt-pin* nil *xrt-blind* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100"))))))
(assert-event ; without a pin the served range arm is not taken
 (equal (in-arena-fn-nntp-archive-command-pinned *sr-arena* *xrt-session* *xrt-state* nil nil *xrt-env* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100")))
        (in-arena-fn-nntp-archive-command *sr-arena* *xrt-session* *xrt-state* *xrt-env* (fn-nntp-string-octets "OVER") (list (fn-nntp-string-octets "1-100")))))

; fn-oag-listing-server-is-the-path-identity: its hypothesis.  Unset, the
; server is the .invalid agent, not the (empty) identity.
(must-fail-checked
 (defthm fn-xrt-listing-server-without-identity
   (equal (fn-nntp-listing-server
           (fn-inj-config-listing (fn-oag-post-config cfg max-octets)))
          (fn-record-string-octets (fn-oag-identity cfg)))))

; -----------------------------------------------------------------------------
; Indexed served lines over a reclaimed article (audit packets G5-5 and G5-6,
; lane audit-fixes).  C is a third article in fn.one at number 5 whose
; handle (2) holds a reclaim tombstone: the FN-RCL2 magic padded to the fixed
; tombstone length.  The number index and trie are the ones the owner's
; refresh builds from the article list (fn-gidx-build, fn-midx-build;
; group-number-index-tests shows refresh = build).
(defconst *xrt-tomb-octets* (append *fn-rcl-magic* (make-list 137 :initial-element 32)))
(defconst *xrt-c*
  (fn-make-article "<xrt-c@example.invalid>" 2
                   '("fn.one") (list (cons "fn.one" 5))
                   t 841000000))
(defconst *xrt-idx-articles* (list *xrt-c* *xrt-a* *xrt-b*))
(defconst *xrt-idx-arena*
  (list (fn-xrt-payload "<xrt-a@example.invalid>" "A")
        (fn-xrt-payload "<xrt-b@example.invalid>" "B")
        *xrt-tomb-octets*))
(defconst *xrt-trie* (fn-midx-build *xrt-idx-articles*))
(defconst *xrt-buckets* (fn-gidx-build *xrt-idx-articles*))
(defconst *xrt-nidx* (fn-gidx-bucket-numbers "fn.one" *xrt-buckets*))
(defconst *xrt-entries* (fn-gidx-bucket "fn.one" *xrt-buckets*))
(bpr-lift fn-nntp-article-tombstonep 1)
(bpr-lift fn-nov-served-lines-numbered 4)
(bpr-lift fn-nov-lines-for-numbers-indexed 4)
(bpr-lift fn-nntp-article-bytes 1)
(assert-event (fn-rcl-tombstonep *xrt-tomb-octets*))

; fn-nov-served-lines-numbered-has-the-article-line (PRF-206).  Positive:
; number 2 (A, live) in (2 5 7), with and without a server name: every
; hypothesis and the conclusion.
(defun xrt-has-line-hyps (n numbers nidx trie payloads)
  (declare (xargs :verify-guards nil))
  (let ((article (fn-gidx-nidx-number-article n nidx trie)))
    (and (member-equal n numbers)
         (consp article)
         (not (in-arena-fn-nntp-article-tombstonep payloads article))
         (fn-nov-okp (in-arena-fn-nov-overview payloads article)))))
(defun xrt-has-line-concl (n numbers nidx trie server payloads)
  (declare (xargs :verify-guards nil))
  (let ((article (fn-gidx-nidx-number-article n nidx trie)))
    (member-equal (fn-nov-served-line n (in-arena-fn-nov-overview payloads article)
                                      server article)
                  (in-arena-fn-nov-served-lines-numbered payloads numbers nidx trie server))))
(assert-event (and (xrt-has-line-hyps 2 '(2 5 7) *xrt-nidx* *xrt-trie* *xrt-idx-arena*)
                   (xrt-has-line-concl 2 '(2 5 7) *xrt-nidx* *xrt-trie* *xrt-server* *xrt-idx-arena*)
                   (xrt-has-line-concl 2 '(2 5 7) *xrt-nidx* *xrt-trie* nil *xrt-idx-arena*)))
; Removal of (member-equal n numbers): 2 is live and has an overview, but the
; range (5 7) does not ask for it and its line is not served.
(assert-event
 (let ((article (fn-gidx-nidx-number-article 2 *xrt-nidx* *xrt-trie*)))
   (and (not (member-equal 2 '(5 7)))
        (consp article)
        (not (in-arena-fn-nntp-article-tombstonep *xrt-idx-arena* article))
        (fn-nov-okp (in-arena-fn-nov-overview *xrt-idx-arena* article))
        (not (xrt-has-line-concl 2 '(5 7) *xrt-nidx* *xrt-trie* *xrt-server* *xrt-idx-arena*)))))
; The tombstone and (consp article) hypotheses have no separate removal
; witness: a tombstone's first octet is NUL, and the overview of C's bytes is
; (:ERROR) (evaluated below), so the okp hypothesis fails with it; an
; unindexed number (7) has no article, and the overview of NIL is not ok
; either.  Both hypotheses fail only together with okp on every state the
; parser admits; the weakened theorem was not attempted.
(assert-event
 (let ((c (fn-gidx-nidx-number-article 5 *xrt-nidx* *xrt-trie*)))
   (and (member-equal 5 '(2 5 7))
        (consp c)
        (in-arena-fn-nntp-article-tombstonep *xrt-idx-arena* c)
        (equal (in-arena-fn-nov-overview *xrt-idx-arena* c) '(:error))
        (not (fn-gidx-nidx-number-article 7 *xrt-nidx* *xrt-trie*))
        (not (fn-nov-okp (in-arena-fn-nov-overview *xrt-idx-arena* nil))))))

; fn-nov-lines-indexed-skip-a-reclaimed-article (PRF-088), the scan the served
; OVER runs.  Positive: C (number 5) is a tombstone, and the lines over
; (2 5 7) are the lines over (2 7).
(assert-event
 (and (fn-rcl-tombstonep
       (in-arena-fn-nntp-article-bytes
        *xrt-idx-arena* (fn-gidx-entry-number-article "fn.one" 5 *xrt-entries* *xrt-trie*)))
      (equal (in-arena-fn-nov-lines-for-numbers-indexed *xrt-idx-arena* "fn.one" '(2 5 7) *xrt-entries* *xrt-trie*)
             (in-arena-fn-nov-lines-for-numbers-indexed *xrt-idx-arena* "fn.one" (remove-equal 5 '(2 5 7))
                                                        *xrt-entries* *xrt-trie*))
      (equal (len (in-arena-fn-nov-lines-for-numbers-indexed *xrt-idx-arena* "fn.one" '(2 5 7)
                                                             *xrt-entries* *xrt-trie*))
             1)))
; Removal of the tombstone hypothesis: A (number 2) is live, and removing it
; changes the lines.
(assert-event
 (and (not (fn-rcl-tombstonep
            (in-arena-fn-nntp-article-bytes
             *xrt-idx-arena* (fn-gidx-entry-number-article "fn.one" 2 *xrt-entries* *xrt-trie*))))
      (not (equal (in-arena-fn-nov-lines-for-numbers-indexed *xrt-idx-arena* "fn.one" '(2 5 7) *xrt-entries* *xrt-trie*)
                  (in-arena-fn-nov-lines-for-numbers-indexed *xrt-idx-arena* "fn.one" (remove-equal 2 '(2 5 7))
                                                             *xrt-entries* *xrt-trie*)))))
