; D3 evidence for the connection's decision table (fn2/books/conn-answer.lisp;
; fn2/docs/d-machines-nntp.md section 4.3). Each fixture is one command line
; in a state, with the reply bytes written here from the spec text it cites
; (RFC 3977, 4643, 4644, 6048, 8054; specs/nntp.md; H's pins and rulings),
; never read from the grammar's table. The fixtures include every sub-form
; check D2b's fuzz oracle deferred to D3 (its DEFERRED list), each with a
; passing and a refused line. Teeth: the grammar's own test responder (a
; parsed line gets its command's first reply) must fail the deferred
; fixtures, so they constrain the decision table and not only the parser.
; Run: sh fn2/tools/certify.sh tests/conn-answer-unit.lisp
(in-package "ACL2")
(include-book "../books/conn-answer")

(defun fn2-cau-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-cau-octets (cdr cs)))))
(defun fn2-cau-crlf (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-cau-crlf (cdr lines)))))

(defun fn2-cau-feed (octets slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-gram-put (nfix (car octets)) slot gen 1 1 1 fn2-pool)
      (declare (ignore code))
      (fn2-cau-feed (cdr octets) slot gen fn2-pool))))
(defun fn2-cau-chars (k n slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  (if (>= (nfix k) (nfix n)) nil
    (mv-let (ok b) (fn2-gram-read slot gen (nfix k) 1 1 1 fn2-pool)
      (cons (code-char (if ok b 63)) (fn2-cau-chars (+ 1 (nfix k)) n slot gen fn2-pool)))))

; The answer to one line (given without its CRLF) in a state: (code after
; pending reply-text). RESPONDER :table is the decision table; :grammar is
; the grammar's test responder over the same parse (the teeth).
(defun fn2-cau-run (line mask pending seen flags real responder)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
        (mv-let (c1 slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
          (declare (ignore c1))
          (mv-let (c2 tslot tgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
            (declare (ignore c2))
            (let* ((octets (append (fn2-cau-octets (coerce line 'list)) (list 13 10)))
                   (fn2-pool (fn2-cau-feed octets slot gen fn2-pool)))
              (if (eq responder :grammar)
                  (mv-let (code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
                    (fn2-nntp-parse-line 0 (len octets) mask slot gen 1 1 1 fn2-pool)
                    (declare (ignore nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3))
                    (mv-let (cmd reply) (fn2-nntp-respond code tag)
                      (mv-let (rc fn2-pool) (fn2-answer-say cmd reply mask 0 tslot tgen 1 1 1 fn2-pool)
                        (mv (list rc (if (eq code :malformed) :closing :command) pending
                                  (coerce (fn2-cau-chars 0 (fn2-gram-fill tslot fn2-pool) tslot tgen fn2-pool) 'string))
                            fn2-pool))))
                (mv-let (code after pending fn2-pool)
                  (fn2-answer 0 (len octets) mask pending nil nil seen flags real slot gen tslot tgen 1 1 1 fn2-pool)
                  (mv (list code after pending
                            (coerce (fn2-cau-chars 0 (fn2-gram-fill tslot fn2-pool) tslot tgen fn2-pool) 'string))
                      fn2-pool)))))))
      result)))

(defconst *fn2-cau-reader* (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*))
(defconst *fn2-cau-peer* (logior *fn2-nntp-state-peer* *fn2-nntp-state-anonymous*))
(defconst *fn2-cau-authed* (logior *fn2-nntp-state-reader* *fn2-nntp-state-authenticated*))
(defconst *fn2-cau-s501* "501 syntax error")
(defconst *fn2-cau-noproj* "503 archive projection unavailable")
(defconst *fn2-cau-hex64* "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
; 2026-10-30T04:22:57Z, 2000-02-29T12:34:56Z, 2100-03-01T23:00:01Z in microseconds.
(defconst *fn2-cau-t1* (* 1793334177 1000000))
(defconst *fn2-cau-t2* (+ 999999 (* 951827696 1000000)))
(defconst *fn2-cau-t3* (* 4107625201 1000000))

; (name line mask pending (seen flags real) expected-after expected-pending
;  reply-lines deferred-p). Reply lines are joined with CRLF.
(defconst *fn2-cau-fixtures*
  `((capabilities "CAPABILITIES" ,*fn2-cau-reader* :none (nil 0 0) :command :none
     ("101 capability list follows" "VERSION 2" "READER" "IMPLEMENTATION fn2"
      "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT SUBSCRIPTIONS"
      "OVER MSGID" "HDR" "XPAT" "NEWNEWS" ".") nil)
    (capabilities-label "CAPABILITIES AUTOUPDATE" ,*fn2-cau-reader* :none (nil 0 0) :command :none
     ("101 capability list follows" "VERSION 2" "READER" "IMPLEMENTATION fn2"
      "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT SUBSCRIPTIONS"
      "OVER MSGID" "HDR" "XPAT" "NEWNEWS" ".") nil)
    ; specs/nntp.md:51-93: six rows; XFNCATCHUP and XFN-ZARTICLE have none.
    (help "HELP" ,*fn2-cau-reader* :none (nil 0 0) :command :none
     ("100 help text follows" "CAPABILITIES HELP QUIT MODE DATE POST" "AUTHINFO STARTTLS XREDEEM COMPRESS"
      "GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS" "ARTICLE HEAD BODY STAT" "OVER XOVER HDR XHDR XPAT"
      "IHAVE CHECK TAKETHIS" ".") nil)
    (help-arg "HELP me" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) nil)
    (quit "quit" ,*fn2-cau-reader* :none (nil 0 0) :closing :none ("205 closing connection") nil)
    (quit-arg "QUIT now" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) nil)
    (mode-reader "MODE READER" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("201 posting prohibited") nil)
    ; RFC 4644 section 2.3: MODE STREAM on a reader connection is 501.
    (mode-stream-reader "MODE STREAM" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (mode-stream-peer "mode stream" ,*fn2-cau-peer* :none (nil 0 0) :command :none ("203 streaming permitted") t)
    (mode-other "MODE WRITER" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) nil)
    ; RFC 3977 section 7.1: UTC, YYYYMMDDhhmmss.
    (date "DATE" ,*fn2-cau-reader* :none (t 1 ,*fn2-cau-t1*) :command :none ("111 20261030042257") nil)
    (date-leap "DATE" ,*fn2-cau-reader* :none (t 1 ,*fn2-cau-t2*) :command :none ("111 20000229123456") nil)
    (date-2100 "DATE" ,*fn2-cau-reader* :none (t 1 ,*fn2-cau-t3*) :command :none ("111 21000301230001") nil)
    (date-epoch "DATE" ,*fn2-cau-reader* :none (t 1 0) :command :none ("111 19700101000000") nil)
    (date-none "DATE" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("503 no clock observation supplied") nil)
    (date-no-wall "DATE" ,*fn2-cau-reader* :none (t 0 ,*fn2-cau-t1*) :command :none ("503 server holds no wall clock reading") nil)
    (date-negative "DATE" ,*fn2-cau-reader* :none (t 3 ,*fn2-cau-t1*) :command :none ("503 server holds no wall clock reading") nil)
    (date-range "DATE" ,*fn2-cau-reader* :none (t 1 ,(* 253402300800 1000000)) :command :none ("503 clock reading outside the representable range") nil)
    (date-arg "DATE 1" ,*fn2-cau-reader* :none (t 1 0) :command :none (,*fn2-cau-s501*) nil)
    ; RFC 4643 sections 2.3-2.4; H's shared pending slot; no credential store until E2.
    (authinfo-user "AUTHINFO USER alice" ,*fn2-cau-reader* :redeem (nil 0 0) :command :user ("381 password required") t)
    (authinfo-pass "AUTHINFO PASS secret" ,*fn2-cau-reader* :user (nil 0 0) :command :none ("481 authentication failed") t)
    (authinfo-pass-alone "AUTHINFO PASS secret" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("482 authentication commands issued out of sequence") t)
    ; H7-07: AUTHINFO PASS after a pending XREDEEM is out of sequence (RFC 4643; fn1's 481 is its bug).
    (authinfo-pass-after-redeem "AUTHINFO PASS secret" ,*fn2-cau-reader* :redeem (nil 0 0) :command :redeem ("482 authentication commands issued out of sequence") t)
    (authinfo-user-arity "AUTHINFO USER" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (authinfo-user-extra "AUTHINFO USER a b" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (authinfo-sasl "AUTHINFO SASL PLAIN" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("503 mechanism not recognized") t)
    (authinfo-sasl-ir "AUTHINFO SASL PLAIN AGFsaWNlAHNlY3JldA==" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("503 mechanism not recognized") t)
    (authinfo-sasl-arity "AUTHINFO SASL" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (authinfo-authed "AUTHINFO USER alice" ,*fn2-cau-authed* :none (nil 0 0) :command :none ("502 already authenticated") nil)
    ; specs/nntp.md:1784-1914.
    (xredeem "XREDEEM 0123 bob" ,*fn2-cau-reader* :user (nil 0 0) :command :redeem ("381 send the password with XREDEEM PASS") t)
    (xredeem-pass "XREDEEM PASS pw" ,*fn2-cau-reader* :redeem (nil 0 0) :command :none ("482 invitation code refused") t)
    (xredeem-pass-alone "XREDEEM pass pw" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("482 redemption commands issued out of sequence") t)
    (xredeem-arity "XREDEEM code" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (starttls "STARTTLS" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("580 can not initiate TLS negotiation") nil)
    ; NNT-054, H's ruling: COMPRESS only after authentication.
    (compress-anon "COMPRESS DEFLATE" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("480 authentication required") nil)
    ; RFC 3977 section 7.6, RFC 6048: LIST variants and their arguments.
    (list-overview "LIST OVERVIEW.FMT" ,*fn2-cau-reader* :none (nil 0 0) :command :none
     ("215 order of fields in overview database" "Subject:" "From:" "Date:" "Message-ID:" "References:"
      "Bytes:" "Lines:" "Xref:full" ".") nil)
    (list-overview-arg "LIST OVERVIEW.FMT x" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (list-headers "LIST HEADERS" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("215 field list follows" ":" ":bytes" ":lines" ".") nil)
    (list-headers-msgid "LIST HEADERS msgid" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("215 field list follows" ":" ":bytes" ":lines" ".") t)
    (list-headers-bad "LIST HEADERS ALL" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (list-motd "LIST MOTD" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("215 message of the day follows" ".") nil)
    (list-motd-arg "LIST MOTD x" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (list-distributions "LIST DISTRIBUTIONS" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("503 data item not stored") nil)
    (list-distrib-arg "LIST DISTRIB.PATS x" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (list-active "LIST ACTIVE comp.*,!comp.lang.*" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (list-active-bad "LIST ACTIVE comp.[a]" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (list-bare "LIST" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) nil)
    ; HDR/XHDR field names (RFC 3977 section 8.5; RFC 5322 section 3.6.8); XPAT patterns are wildmats.
    (hdr "HDR Subject 1-" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (hdr-meta "HDR :bytes" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (hdr-colon "HDR Sub:ject" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (hdr-bare-colon "HDR :" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (xhdr "XHDR From <a@b.example>" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (xhdr-colon "XHDR Fr:om" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (xpat "XPAT Subject 1-5 *fn2*" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (xpat-bad "XPAT Subject 1-5 [fn2]" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    ; specs/nntp.md:2484-2499: 64 lower-case hex octets per digest.
    (zarticle ,(concatenate 'string "XFN-ZARTICLE <a@b.example> " *fn2-cau-hex64*) ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) t)
    (zarticle-upper ,(concatenate 'string "XFN-ZARTICLE <a@b.example> " (string-upcase *fn2-cau-hex64*)) ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    (zarticle-short ,(concatenate 'string "XFN-ZARTICLE <a@b.example> " (subseq *fn2-cau-hex64* 0 63)) ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) t)
    ; Interim replies until the cursor (D6) and the transaction (D5).
    (group "GROUP misc.test" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) nil)
    (group-arity "GROUP" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) nil)
    (next "NEXT" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("412 no newsgroup selected") nil)
    (article "ARTICLE <a@b.example>" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-noproj*) nil)
    (post "POST" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("440 posting not permitted") nil)
    ; RFC 4644: transit commands on a reader connection.
    (ihave-reader "IHAVE <a@b.example>" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("502 transit is not permitted on this connection") nil)
    (takethis-reader "TAKETHIS <a@b.example>" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("502 transit is not permitted on this connection") nil)
    (unknown "FROB" ,*fn2-cau-reader* :none (nil 0 0) :command :none ("500 command not recognized") nil)
    ; H pin P-UTF8-WS: whitespace on valid UTF-8 is 501 and the connection stays.
    (whitespace " HELP" ,*fn2-cau-reader* :none (nil 0 0) :command :none (,*fn2-cau-s501*) nil)
    ; ... ill-formed UTF-8 or a NUL is malformed: 501, then close.
    (malformed-nul ,(coerce (list #\H #\E (code-char 0) #\L #\P) 'string) ,*fn2-cau-reader* :none (nil 0 0) :closing :none (,*fn2-cau-s501*) nil)
    (malformed-utf8 ,(coerce (list #\H #\E #\L #\P #\Space (code-char 255)) 'string) ,*fn2-cau-reader* :none (nil 0 0) :closing :none (,*fn2-cau-s501*) nil)))

(defun fn2-cau-check (fixtures responder)
  (declare (xargs :verify-guards nil))
  ; The names of the fixtures whose answer differs from the expectation.
  (if (atom fixtures) nil
    (let* ((f (car fixtures))
           (clock (nth 4 f))
           (got (fn2-cau-run (nth 1 f) (nth 2 f) (nth 3 f) (nth 0 clock) (nth 1 clock) (nth 2 clock) responder))
           (want (list :ok (nth 5 f) (nth 6 f) (fn2-cau-crlf (nth 7 f)))))
      (if (equal (if (eq responder :grammar) (list (nth 0 got) (nth 1 got) (nth 3 got))
                   got)
                 (if (eq responder :grammar) (list (nth 0 want) (nth 1 want) (nth 3 want)) want))
          (fn2-cau-check (cdr fixtures) responder)
        (cons (car f) (fn2-cau-check (cdr fixtures) responder))))))
(defun fn2-cau-deferred (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) nil
    (if (nth 8 (car fixtures)) (cons (car (car fixtures)) (fn2-cau-deferred (cdr fixtures)))
      (fn2-cau-deferred (cdr fixtures)))))

; Every fixture holds through the decision table.
(assert-event (equal (fn2-cau-check *fn2-cau-fixtures* :table) nil)
              :msg (msg "conn-answer fixtures failing: ~x0" (fn2-cau-check *fn2-cau-fixtures* :table)))

; Teeth: the grammar's test responder fails every deferred fixture whose
; answer is not the command's first declared reply (it cannot tell MODE
; STREAM's connection kind, a sub-form's arity, a pending slot, a field
; name or a digest), and fails at least one deferred fixture of each
; DEFERRED keyword.
(defconst *fn2-cau-grammar-misses*
  (fn2-cau-check *fn2-cau-fixtures* :grammar))
(assert-event
 (subsetp-eq '(mode-stream-reader authinfo-pass authinfo-user-arity authinfo-sasl xredeem-pass
               list-overview-arg list-headers-bad list-active-bad hdr-colon xhdr-colon xpat-bad
               zarticle-upper zarticle-short)
             *fn2-cau-grammar-misses*)
 :msg (msg "grammar responder unexpectedly passes: ~x0" *fn2-cau-grammar-misses*))

; The greeting and the overflow refusal.
(defun fn2-cau-greeting (refused)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
        (mv-let (c1 tslot tgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
          (declare (ignore c1))
          (mv-let (code after fn2-pool) (fn2-answer-greeting refused nil *fn2-cau-reader* tslot tgen 1 1 1 fn2-pool)
            (mv (list code after (coerce (fn2-cau-chars 0 (fn2-gram-fill tslot fn2-pool) tslot tgen fn2-pool) 'string))
                fn2-pool))))
      result)))
(assert-event (equal (fn2-cau-greeting nil) (list :ok :command (fn2-cau-crlf '("201 fn-nntp experimental reader ready")))))
; specs/nntp.md NNT-031: the capacity refusal, then close.
(assert-event (equal (fn2-cau-greeting t) (list :ok :closing (fn2-cau-crlf '("400 too many connections; try again later")))))

; Every DEFERRED keyword of tests/grammar-fuzz-oracle.py has fixtures here
; (XFNCATCHUP's fields are the grammar's own kinds, :digits and :number;
; on a reader connection it is the 502 state refusal until E4).
(assert-event
 (subsetp-eq '(mode-stream-reader authinfo-user-arity xredeem-arity zarticle-short list-motd-arg hdr-colon xhdr-colon xpat-bad)
             (fn2-cau-deferred *fn2-cau-fixtures*)))
