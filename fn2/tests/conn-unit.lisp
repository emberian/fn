; D3 evidence: the connection machine fn2-conn through the real assembled
; core at the adapter boundary (books/owed-conn.lisp's fn2-conn-wire-run:
; the served listener admits fn2-conn, scripted clients deliver octets to
; each Receive in given chunks, every Send is recorded on the client's
; wire, releases and Close are completed). Wire bytes are compared with
; replies written here from the spec text, as conn-answer-unit's are. The
; teeth of T1 (fn2-turn-served-safety), T8 (fn2-reply-trace-fragmentation-
; invariant, fn2-connection-privacy) and the reader-only interim are here.
; Run: sh fn2/tools/certify.sh tests/conn-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-conn")
(include-book "../sim/check-wire")

(defun fn2-cu-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-cu-octets (cdr cs)))))
(defun fn2-cu-crlf (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-cu-crlf (cdr lines)))))
(defun fn2-cu-text (lines) (declare (xargs :guard (string-listp lines))) (fn2-cu-octets (coerce (fn2-cu-crlf lines) 'list)))
(defun fn2-cu-repeat (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons x (fn2-cu-repeat (- n 1) x))))
(in-theory (disable fn2-cu-octets fn2-cu-crlf fn2-cu-text fn2-cu-repeat))

; ------------------------------------------------------------------------
; Fixtures: (name client-octets expected-wire-lines closed).
(defconst *fn2-cu-greeting* "201 fn-nntp experimental reader ready")
(defconst *fn2-cu-help*
  '("100 help text follows" "CAPABILITIES HELP QUIT MODE DATE POST" "AUTHINFO STARTTLS XREDEEM COMPRESS"
    "GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS" "ARTICLE HEAD BODY STAT" "OVER XOVER HDR XHDR XPAT"
    "IHAVE CHECK TAKETHIS" "."))
(defconst *fn2-cu-caps*
  '("101 capability list follows" "VERSION 2" "READER" "IMPLEMENTATION fn2"
    "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT SUBSCRIPTIONS"
    "OVER MSGID" "HDR" "XPAT" "NEWNEWS" "."))
(defconst *fn2-cu-fixtures*
  `((idle nil (,*fn2-cu-greeting*) nil)
    (pipelined ,(fn2-cu-text '("CAPABILITIES" "HELP" "QUIT"))
     (,*fn2-cu-greeting* ,@*fn2-cu-caps* ,@*fn2-cu-help* "205 closing connection") t)
    ; No clock observation is posted in these runs: DATE is 503.
    (date-mode ,(fn2-cu-text '("DATE" "MODE READER" "mode stream" "QUIT"))
     (,*fn2-cu-greeting* "503 no clock observation supplied" "201 posting prohibited" "501 syntax error"
      "205 closing connection") t)
    (unknown-then-quit ,(fn2-cu-text '("FROB" "GROUP misc.test" "NEXT" "QUIT"))
     (,*fn2-cu-greeting* "500 command not recognized" "503 archive projection unavailable"
      "412 no newsgroup selected" "205 closing connection") t)
    ; A NUL makes the line malformed: 501, then close; the next line is never answered.
    (malformed ,(append (fn2-cu-octets (coerce "HE" 'list)) (list 0) (fn2-cu-text '("LP" "HELP")))
     (,*fn2-cu-greeting* "501 syntax error") t)
    ; Over 512 octets: 501, then close (RFC 3977 section 3.1).
    (overflow ,(append (fn2-cu-repeat 600 65) (fn2-cu-text '("" "HELP")))
     (,*fn2-cu-greeting* "501 syntax error") t)
    ; 150 pipelined lines (1,950 octets) cross the 1,024-octet RX slot: compaction.
    (compaction ,(fn2-cu-text (append (fn2-cu-repeat 150 "MODE READER") '("QUIT")))
     (,*fn2-cu-greeting* ,@(fn2-cu-repeat 150 "201 posting prohibited") "205 closing connection") t)))

(defun fn2-cu-expected (f)
  (declare (xargs :verify-guards nil))
  (list (fn2-cu-octets (coerce (fn2-cu-crlf (nth 2 f)) 'list)) (nth 3 f)))
(defun fn2-cu-check-one (f sizes)
  (declare (xargs :verify-guards nil))
  (equal (fn2-conn-wire-solo (nth 1 f) sizes) (fn2-cu-expected f)))
(in-theory (disable fn2-cu-expected fn2-cu-check-one))
(defun fn2-cu-failures (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) nil
    (if (fn2-cu-check-one (car fixtures) nil) (fn2-cu-failures (cdr fixtures))
      (cons (list (car (car fixtures)) (fn2-conn-wire-run (list (list (nth 1 (car fixtures)) nil))))
            (fn2-cu-failures (cdr fixtures))))))
(in-theory (disable fn2-cu-failures))
(assert-event (equal (fn2-cu-failures *fn2-cu-fixtures*) nil)
              :msg (msg "conn-unit failures: ~x0" (fn2-cu-failures *fn2-cu-fixtures*)))
; The checker is not vacuous: a wrong expectation fails.
(assert-event (not (fn2-cu-check-one (list 'x (fn2-cu-text '("HELP")) (list *fn2-cu-greeting* "100 help text follows") nil) nil)))

; ------------------------------------------------------------------------
; T8 fragmentation teeth: every split point of the short transcripts, and
; bytewise arrival, give the fixture's wire; the long ones in 7- and
; 300-octet chunks. Negative: a chunker that loses its first chunk differs.
(defun fn2-cu-splits (k n f)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  (if (>= (nfix k) (nfix n)) t
    (and (fn2-cu-check-one f (list (+ 1 (nfix k))))
         (fn2-cu-splits (+ 1 (nfix k)) n f))))
(in-theory (disable fn2-cu-splits))
(defun fn2-cu-split-all (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) t
    (let ((f (car fixtures)))
      (and (or (< 80 (len (nth 1 f)))
               (and (fn2-cu-splits 0 (len (nth 1 f)) f)
                    (fn2-cu-check-one f (fn2-cu-repeat (len (nth 1 f)) 1))))
           (fn2-cu-split-all (cdr fixtures))))))
(in-theory (disable fn2-cu-split-all))
(defun fn2-conn-test-fragmentation ()
  (declare (xargs :verify-guards nil))
  (and (fn2-cu-split-all *fn2-cu-fixtures*)
       (fn2-cu-check-one (nth 6 *fn2-cu-fixtures*) (fn2-cu-repeat 400 7))
       (fn2-cu-check-one (nth 6 *fn2-cu-fixtures*) (fn2-cu-repeat 10 300))
       (fn2-cu-check-one (nth 5 *fn2-cu-fixtures*) (fn2-cu-repeat 100 7))))
(defun fn2-conn-test-fragmentation-negative ()
  (declare (xargs :verify-guards nil))
  (let ((f (nth 1 *fn2-cu-fixtures*)))
    (not (equal (fn2-conn-wire-solo (nthcdr 3 (nth 1 f)) nil) (fn2-conn-wire-solo (nth 1 f) '(3))))))
(assert-event (and (fn2-conn-test-fragmentation) (fn2-conn-test-fragmentation-negative)))

; ------------------------------------------------------------------------
; T8 privacy teeth: two clients at once; each one's wire is its solo wire.
; Negative: the comparison distinguishes the two clients' wires.
(defun fn2-cu-pair-private (f g)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-conn-wire-run (list (list (nth 1 f) nil) (list (nth 1 g) '(5))))))
    (and (equal (nth 0 (nth 1 r)) (fn2-cu-expected f))
         (equal (nth 1 (nth 1 r)) (fn2-cu-expected g))
         (fn2-conn-safe-p r))))
(defun fn2-conn-test-privacy ()
  (declare (xargs :verify-guards nil))
  (let ((x *fn2-cu-fixtures*))
    (and (fn2-cu-pair-private (nth 1 x) (nth 4 x))
         (fn2-cu-pair-private (nth 6 x) (nth 2 x))
         (fn2-cu-pair-private (nth 3 x) (nth 1 x))
         (fn2-cu-pair-private (nth 0 x) (nth 5 x)))))
(defun fn2-conn-test-privacy-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((x *fn2-cu-fixtures*)
         (r (fn2-conn-wire-run (list (list (nth 1 (nth 1 x)) nil) (list (nth 1 (nth 4 x)) nil)))))
    (not (equal (nth 1 (nth 1 r)) (fn2-cu-expected (nth 1 x))))))
(assert-event (and (fn2-conn-test-privacy) (fn2-conn-test-privacy-negative)))

; ------------------------------------------------------------------------
; T1 teeth: the fixtures alone and three at once, plus seeded random octet
; strings (every byte value), in seeded chunks, leave the core quiescent
; and never stopped. Negative: the safety predicate refuses a stopped core.
(defun fn2-cu-lcg (x) (declare (xargs :guard (natp x))) (mod (+ 12345 (* 1103515245 x)) 2147483648))
(defun fn2-cu-random (n x)
  (declare (xargs :guard (and (natp n) (natp x))))
  (if (zp n) nil (cons (mod (floor x 65536) 256) (fn2-cu-random (- n 1) (fn2-cu-lcg x)))))
(defun fn2-cu-random-transcript (seed)
  (declare (xargs :verify-guards nil))
  ; Mostly command-like lines with random octets mixed in.
  (append (fn2-cu-text '("HELP" "DATE")) (fn2-cu-random (+ 20 (mod seed 300)) seed)
          (fn2-cu-text '("QUIT"))))
(defun fn2-cu-random-safe (k)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) t
    (and (fn2-conn-safe-p (fn2-conn-wire-run
                           (list (list (fn2-cu-random-transcript (* 7919 k)) (list (+ 1 (mod k 13)) (mod k 50))))))
         (fn2-cu-random-safe (- k 1)))))
(in-theory (disable fn2-cu-lcg fn2-cu-random fn2-cu-random-transcript fn2-cu-random-safe))
(defun fn2-conn-test-served-safety ()
  (declare (xargs :verify-guards nil))
  (let ((x *fn2-cu-fixtures*))
    (and (fn2-conn-safe-p (fn2-conn-wire-run (list (list (nth 1 (nth 1 x)) '(4))
                                                    (list (nth 1 (nth 5 x)) '(1 2 3))
                                                    (list (nth 1 (nth 6 x)) '(100)))))
         (fn2-cu-random-safe 24))))
(defun fn2-conn-test-served-safety-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-conn-safe-p (list :quiet nil 7))) (not (fn2-conn-safe-p (list :fuel nil 0)))))
(assert-event (and (fn2-conn-test-served-safety) (fn2-conn-test-served-safety-negative)))

; ------------------------------------------------------------------------
; Teeth of fn2-account-ledger-matches (D7 3/n): the same mixed runs as T1,
; with closed and open clients, every chunking; negative: the predicate
; refuses a view whose holding, received or sent charge is off by one, or
; whose ledger is not conserved.
(defun fn2-conn-test-ledger-random (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) t
    (let ((octets (fn2-cu-random-transcript (+ 7 (* 131 n)))))
      (and (fn2-conn-ledger-matches-p
            (nth 3 (fn2-conn-wire-run (list (list octets (list (+ 1 (mod n 9)) 3 5))
                                            (list (nth 1 (nth 0 *fn2-cu-fixtures*)) nil)))))
           (fn2-conn-test-ledger-random (- n 1))))))
(defun fn2-conn-test-ledger-matches ()
  (declare (xargs :verify-guards nil))
  (let* ((x *fn2-cu-fixtures*)
         (view (nth 3 (fn2-conn-wire-run (list (list (nth 1 (nth 1 x)) '(4))
                                               (list (nth 1 (nth 5 x)) '(1 2 3))
                                               (list (nth 1 (nth 6 x)) '(100)))))))
    (and (fn2-conn-ledger-matches-p view)
         (< 0 (nth 2 view)) (< 0 (nth 3 view))
         (fn2-conn-test-ledger-random 8))))
(defun fn2-conn-test-ledger-matches-negative ()
  (declare (xargs :verify-guards nil))
  (let ((good (list t 1 10 20 1 10 20)))
    (and (fn2-conn-ledger-matches-p good)
         (not (fn2-conn-ledger-matches-p (update-nth 1 2 good)))
         (not (fn2-conn-ledger-matches-p (update-nth 2 9 good)))
         (not (fn2-conn-ledger-matches-p (update-nth 3 21 good)))
         (not (fn2-conn-ledger-matches-p (update-nth 0 nil good))))))
(assert-event (and (fn2-conn-test-ledger-matches) (fn2-conn-test-ledger-matches-negative)))

; ------------------------------------------------------------------------
; The reader-only interim's teeth: a first MODE STREAM gets the reader
; greeting and 501, whatever follows and however it is chunked. Negative:
; the predicate refuses a streaming answer.
(defun fn2-conn-test-reader-only ()
  (declare (xargs :verify-guards nil))
  (and (fn2-conn-reader-prefix-p (car (fn2-conn-wire-solo *fn2-conn-mode-stream-line* nil)))
       (fn2-conn-reader-prefix-p (car (fn2-conn-wire-solo (append *fn2-conn-mode-stream-line*
                                                                  (nth 1 (nth 1 *fn2-cu-fixtures*))) '(1 1 1))))
       (fn2-conn-reader-prefix-p (car (fn2-conn-wire-solo (append *fn2-conn-mode-stream-line*
                                                                  (nth 1 (nth 4 *fn2-cu-fixtures*))) '(20))))))
(defun fn2-conn-test-reader-only-negative ()
  (declare (xargs :verify-guards nil))
  (not (fn2-conn-reader-prefix-p (fn2-cu-text (list *fn2-cu-greeting* "203 streaming permitted")))))
(assert-event (and (fn2-conn-test-reader-only) (fn2-conn-test-reader-only-negative)))

; ------------------------------------------------------------------------
; WIRE over every fixture and every random transcript, and its three
; mutation controls (ROUND2 section F.1): a wrong byte in a status line, a
; missing reply, and a reply after the closing one are each caught.
(defun fn2-cu-wire-ok (octets sizes)
  (declare (xargs :verify-guards nil))
  (let ((w (fn2-conn-wire-solo octets sizes)))
    (fn2-wire-pass-p octets (nth 0 w) (nth 1 w))))
(defun fn2-cu-wire-all (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) t
    (and (fn2-cu-wire-ok (nth 1 (car fixtures)) nil) (fn2-cu-wire-all (cdr fixtures)))))
(defun fn2-cu-wire-random (k)
  (declare (xargs :verify-guards nil :measure (nfix k)))
  (if (zp k) t
    (and (fn2-cu-wire-ok (fn2-cu-random-transcript (* 7919 k)) (list (+ 1 (mod k 13)) (mod k 50)))
         (fn2-cu-wire-random (- k 1)))))
(in-theory (disable fn2-cu-wire-ok fn2-cu-wire-all fn2-cu-wire-random))
(assert-event (and (fn2-cu-wire-all *fn2-cu-fixtures*) (fn2-cu-wire-random 24)))
(defconst *fn2-cu-wire-client* (nth 1 (nth 3 *fn2-cu-fixtures*)))   ; FROB, GROUP, NEXT, QUIT
(defconst *fn2-cu-wire-good* (fn2-cu-expected (nth 3 *fn2-cu-fixtures*)))
(assert-event (fn2-wire-pass-p *fn2-cu-wire-client* (nth 0 *fn2-cu-wire-good*) t))
; A wrong byte: the second reply's code 500 becomes 5X0.
(assert-event (not (fn2-wire-pass-p *fn2-cu-wire-client*
                                    (update-nth (+ 1 (len (fn2-cu-text (list *fn2-cu-greeting*))))
                                                88 (nth 0 *fn2-cu-wire-good*)) t)))
; A missing reply: the 503 line is dropped.
(assert-event (not (fn2-wire-pass-p *fn2-cu-wire-client*
                                    (fn2-cu-text (list *fn2-cu-greeting* "500 command not recognized"
                                                       "412 no newsgroup selected" "205 closing connection")) t)))
; A reply after the closing one.
(assert-event (not (fn2-wire-pass-p *fn2-cu-wire-client*
                                    (append (nth 0 *fn2-cu-wire-good*) (fn2-cu-text '("201 again"))) t)))
; A dropped closing reply: the wire without its 205, the server closed. A
; close excuses no complete command line (the QUIT went unanswered).
(assert-event (not (fn2-wire-pass-p *fn2-cu-wire-client*
                                    (fn2-cu-text (list *fn2-cu-greeting* "500 command not recognized"
                                                       "503 archive projection unavailable"
                                                       "412 no newsgroup selected")) t)))
