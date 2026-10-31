;; The connection machine's decision table (layer D, quest D3; the design is
;; fn2/docs/d-machines-nntp.md section 4.3). One complete command line in a
;; connection's RX slot is parsed by the declared grammar (nntp-grammar.lisp)
;; and answered into its TX slot: a typed status line, and for the few
;; commands with a fixed body (HELP, CAPABILITIES, LIST OVERVIEW.FMT, LIST
;; HEADERS, LIST MOTD) the body and its terminator. A library over the pool:
;; the machine (conn.lisp) calls it through one declared operation, and
;; tests/conn-answer-unit.lisp drives it on a local pool.
;;
;; The answer reads only the connection's own scalars (state mask, the
;; pending-authentication slot, the clock observation the run read) and
;; never a live configuration or access rule: the pinned rule of H's ruling
;; HZ3 (fn1 bug W01) is structural here.
(in-package "ACL2")
(include-book "nntp-grammar")
(fn2-book-layer :d)

;; At most this much fixed body follows a status line in one answer; the
;; machine's run budget counts it (section 4.2).
(defconst *fn2-answer-body-bytes* 1024)

(defun fn2-answer-crlf-lines (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-answer-crlf-lines (cdr lines)))))

;; CAPABILITIES' always-on labels (RFC 3977 section 5.2; specs/nntp.md:3-23).
;; The conditional labels (POST from D5; IHAVE and STREAMING with the peer
;; bit; STARTTLS from E1; AUTHINFO and SASL from E2; COMPRESS DEFLATE after
;; authentication, from E2) render nothing until their quest (section 11).
(defconst *fn2-answer-capabilities-text*
  (fn2-answer-crlf-lines
   '("VERSION 2" "READER" "IMPLEMENTATION fn2"
     "LIST ACTIVE ACTIVE.TIMES COUNTS HEADERS MOTD NEWSGROUPS OVERVIEW.FMT SUBSCRIPTIONS"
     "OVER MSGID" "HDR" "XPAT" "NEWNEWS")))
;; LIST OVERVIEW.FMT (RFC 3977 section 8.4; the overview fields C stores).
(defconst *fn2-answer-overview-fmt-text*
  (fn2-answer-crlf-lines '("Subject:" "From:" "Date:" "Message-ID:" "References:" "Bytes:" "Lines:" "Xref:full")))
;; LIST HEADERS (RFC 3977 section 8.6): any header by name, and the two
;; metadata items every article has.
(defconst *fn2-answer-headers-text* (fn2-answer-crlf-lines '(":" ":bytes" ":lines")))

(assert-event (and (<= (length *fn2-answer-capabilities-text*) *fn2-answer-body-bytes*)
                   (<= (length *fn2-nntp-help-text*) *fn2-answer-body-bytes*)
                   (<= (length *fn2-answer-overview-fmt-text*) *fn2-answer-body-bytes*)
                   (<= (length *fn2-answer-headers-text*) *fn2-answer-body-bytes*)))

;; A constant text appended to the TX slot, octet by octet, never as a list.
(defun fn2-answer-put-text (k text slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix (- (length text) (nfix k)))
                  :guard (and (fn2-pool-wfp fn2-pool) (natp k) (stringp text))))
  (if (or (not (stringp text)) (>= (nfix k) (length text))) (mv :ok fn2-pool)
    (mv-let (code fn2-pool)
      (fn2-gram-put (char-code (char text (nfix k))) slot gen okind oslot ogen fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-answer-put-text (+ 1 (nfix k)) text slot gen okind oslot ogen fn2-pool)))))
(fn2-pool-preserves fn2-answer-put-text (k text slot gen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-answer-put-text))

;; ------------------------------------------------------------------------
;; DATE (RFC 3977 section 7.1): the clock mailbox's realtime reading, in
;; microseconds since 1970-01-01T00:00:00Z (the unit is pinned in the layer
;; doc's section 8), as the UTC civil date YYYYMMDDhhmmss. Days to a civil
;; date by H. Hinnant's days_from_civil inverse, all in naturals (day 0 is
;; 1970-01-01, shifted to the era origin 0000-03-01); the result is YYYYMMDD.
(defun fn2-answer-civil (days)
  (declare (xargs :guard (natp days) :guard-hints (("Goal" :in-theory (disable floor)))))
  (let* ((z (+ (nfix days) 719468))
         (era (floor z 146097))
         (doe (- z (* era 146097)))
         (yoe (floor (- (+ doe (floor doe 36524)) (+ (floor doe 1460) (floor doe 146096))) 365))
         (doy (- doe (- (+ (* 365 yoe) (floor yoe 4)) (floor yoe 100))))
         (mp (floor (+ (* 5 doy) 2) 153))
         (d (+ 1 (- doy (floor (+ (* 153 mp) 2) 5))))
         (m (if (< mp 10) (+ mp 3) (- mp 9)))
         (y (+ (* era 400) yoe (if (<= m 2) 1 0))))
    (nfix (+ (* y 10000) (* m 100) d))))
(in-theory (disable fn2-answer-civil))

;; (mv code digits): :ok and the 14-digit number, or the DATE refusal's key.
(defconst *fn2-answer-date-max-us* 253402300799999999) ; 9999-12-31T23:59:59.999999Z
(defun fn2-answer-date-fields (real)
  (declare (xargs :guard (natp real)))
  (let* ((secs (nfix (floor (nfix real) 1000000)))
         (days (nfix (floor secs 86400)))
         (sod (nfix (- secs (* days 86400)))))
    (+ (* (fn2-answer-civil days) 1000000)
       (* (floor sod 3600) 10000) (* (mod (floor sod 60) 60) 100) (mod sod 60))))
(defun fn2-answer-date-digits (seen flags real)
  (declare (xargs :guard t))
  (cond ((not seen) (mv :no-observation 0))
        ((not (and (natp flags) (equal (logand flags 3) 1))) (mv :no-wall 0))
        ((not (and (natp real) (<= real *fn2-answer-date-max-us*))) (mv :out-of-range 0))
        (t (mv :ok (nfix (fn2-answer-date-fields real))))))
(in-theory (disable fn2-answer-date-fields))

;; ------------------------------------------------------------------------
;; Sub-form checks the grammar leaves to D3 (section 6, the fuzz oracle's
;; DEFERRED list). Each reads a span of the RX slot through the checked
;; reader, never a list.

;; A header field name for HDR, XHDR and XPAT: an optional leading colon,
;; then one or more printable octets other than the colon (RFC 5322 section
;; 3.6.8; RFC 3977 section 8.5's metadata items open with the colon).
(defun fn2-answer-field-loop (left i slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i))))
  (if (zp left) t
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (and ok (<= 33 b) (<= b 126) (not (= b 58))
           (fn2-answer-field-loop (- left 1) (+ 1 (nfix i)) slot gen okind oslot ogen fn2-pool)))))
(defun fn2-answer-field-p (ts tl slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp ts) (natp tl))))
  (mv-let (ok b) (fn2-gram-read slot gen ts okind oslot ogen fn2-pool)
    (if (and ok (= b 58))
        (and (< 1 tl) (fn2-answer-field-loop (- tl 1) (+ 1 ts) slot gen okind oslot ogen fn2-pool))
      (and (< 0 tl) (fn2-answer-field-loop tl ts slot gen okind oslot ogen fn2-pool)))))

;; XFN-ZARTICLE's digests: one or more words of exactly 64 lower-case hex
;; octets, separated by SP or TAB (specs/nntp.md:2484-2499).
(defun fn2-answer-digests-loop (left i run slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix left)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp i) (natp run))))
  (if (zp left) (equal run 64)
    (mv-let (ok b) (fn2-gram-read slot gen i okind oslot ogen fn2-pool)
      (cond ((not ok) nil)
            ((fn2-gram-wspp b)
             (and (or (equal run 64) (equal run 0))
                  (fn2-answer-digests-loop (- left 1) (+ 1 (nfix i)) 0 slot gen okind oslot ogen fn2-pool)))
            ((or (and (<= 48 b) (<= b 57)) (and (<= 97 b) (<= b 102)))
             (and (< (nfix run) 64)
                  (fn2-answer-digests-loop (- left 1) (+ 1 (nfix i)) (+ 1 (nfix run)) slot gen okind oslot ogen fn2-pool)))
            (t nil)))))

;; The sub-form verdict of a parsed line: T when the command's own checks
;; pass (or it has none). LIST's variant table: 0 ACTIVE, 1 ACTIVE.TIMES,
;; 2 COUNTS, 3 DISTRIB.PATS, 4 DISTRIBUTIONS, 5 HEADERS, 6 MOTD,
;; 7 NEWSGROUPS, 8 OVERVIEW.FMT, 9 SUBSCRIPTIONS (the declared keyword order).
(in-theory (disable fn2-answer-field-p fn2-answer-digests-loop))
(local (in-theory (disable fn2-gram-arg-wildmat fn2-gram-match)))
(defun fn2-answer-subform-p (tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 mask slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp nargs) (natp a0) (natp b0) (natp a1) (natp b1)
                              (natp a2) (natp b2))))
  (cond ((equal tag *fn2-nntp-command-authinfo*)
         ;; RFC 4643 sections 2.3, 2.4: USER and PASS take one argument, SASL a
         ;; mechanism and an optional initial response.
         (if (and (eq f0 :keyword) (equal a0 2)) (or (equal nargs 2) (equal nargs 3)) (equal nargs 2)))
        ((equal tag *fn2-nntp-command-mode*)
         ;; MODE STREAM is for peer connections only (RFC 4644 section 2.3).
         (or (not (and (eq f0 :keyword) (equal a0 1)))
             (and (integerp mask) (logtest mask *fn2-nntp-state-peer*))))
        ((equal tag *fn2-nntp-command-list*)
         (let ((variant (if (eq f0 :keyword) a0 0)) (rest (eq f1 :span)))
           (cond ((member variant '(3 4 6 8)) (not rest))
                 ((equal variant 5)
                  (or (not rest) (fn2-gram-match a1 b1 "MSGID" slot gen okind oslot ogen fn2-pool)
                      (fn2-gram-match a1 b1 "RANGE" slot gen okind oslot ogen fn2-pool)))
                 (t (or (not rest)
                        (mv-let (ok k x y) (fn2-gram-arg-wildmat a1 b1 slot gen okind oslot ogen fn2-pool)
                          (declare (ignore k x y)) ok))))))
        ((or (equal tag *fn2-nntp-command-hdr*) (equal tag *fn2-nntp-command-xhdr*))
         (and (eq f0 :span) (fn2-answer-field-p a0 b0 slot gen okind oslot ogen fn2-pool)))
        ((equal tag *fn2-nntp-command-xpat*)
         (and (eq f0 :span) (fn2-answer-field-p a0 b0 slot gen okind oslot ogen fn2-pool)
              (eq f2 :span)
              (mv-let (ok k x y) (fn2-gram-arg-wildmat a2 b2 slot gen okind oslot ogen fn2-pool)
                (declare (ignore k x y)) ok)))
        ((equal tag *fn2-nntp-command-xfn-zarticle*)
         (and (eq f1 :span) (fn2-answer-digests-loop b1 a1 0 slot gen okind oslot ogen fn2-pool)))
        (t t)))

;; ------------------------------------------------------------------------
;; Interim replies: commands whose machine is a later quest answer the reply
;; their own row declares for "not available here yet", after their
;; sub-form checks. Each row names the quest that replaces it; the table's
;; emptiness is a D9 acceptance check (section 4.3), so no interim outlives
;; its quest. NEXT and LAST answer 412: no D3 connection has a group.
(defconst *fn2-answer-interim*
  '((list :no-projection :d6)
    (newgroups :no-projection :d6) (newnews :no-projection :d6)
    (article :no-projection :d6) (head :no-projection :d6) (body :no-projection :d6)
    (stat :no-projection :d6) (over :no-projection :d6) (xover :no-projection :d6)
    (hdr :no-projection :d6) (xhdr :no-projection :d6) (xpat :no-projection :d6)
    (xfn-zarticle :no-projection :d6) (xfncatchup :no-projection :e4)
    (post :not-permitted :d5) (ihave :retry :d5) (check :later :d5)
    (starttls :cannot :d7) (compress :algorithm :e2)))

(defun fn2-answer-interim-arms (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (list (fn2-gram-const 'fn2-nntp "-command-" (car (car rows)))
                (fn2-gram-const 'fn2-nntp "-reply-" (car (car rows)) "-" (cadr (car rows))))
          (fn2-answer-interim-arms (cdr rows)))))
(defun fn2-answer-interim-conds (arms)
  (declare (xargs :verify-guards nil))
  (if (atom arms) (list (list t '*fn2-nntp-reply-none*))
    (cons (list (list 'equal 'tag (car (car arms))) (cadr (car arms)))
          (fn2-answer-interim-conds (cdr arms)))))
;; The reader commands the query cursor serves (D6 1/n, cursor.lisp): the
;; connection moves to :query and takes a cursor when the profile serves
;; reading (read rows, :reading); without reading, the reply each gives a
;; node that serves no archive (NEXT and LAST: no group can be selected).
(defconst *fn2-answer-unread*
  '((group :no-projection) (listgroup :no-projection) (next :no-group-selected) (last :no-group-selected)
    (stat :no-projection) (over :no-projection) (xover :no-projection)))
(make-event
 (value `(defun fn2-answer-unread-reply (tag)
           (declare (xargs :guard t))
           (cond ,@(fn2-answer-interim-conds (fn2-answer-interim-arms *fn2-answer-unread*))))))
(defun fn2-answer-query-p (tag)
  (declare (xargs :guard t))
  (not (equal (fn2-answer-unread-reply tag) *fn2-nntp-reply-none*)))
(make-event
 (value `(defun fn2-answer-interim-reply (tag)
           (declare (xargs :guard t))
           (cond ,@(fn2-answer-interim-conds (fn2-answer-interim-arms *fn2-answer-interim*))))))

;; Status line only, or status line, fixed body and terminator.
(defun fn2-answer-say (cmd reply mask n0 tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp n0))))
  (fn2-nntp-render cmd reply mask n0 0 0 tslot tgen 0 0 tslot tgen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-answer-say (cmd reply mask n0 tslot tgen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-answer-say))
(defun fn2-answer-say-body (cmd reply mask text tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (stringp text))))
  (mv-let (code fn2-pool) (fn2-answer-say cmd reply mask 0 tslot tgen okind oslot ogen fn2-pool)
    (if (not (eq code :ok)) (mv code fn2-pool)
      (mv-let (code fn2-pool) (fn2-answer-put-text 0 text tslot tgen okind oslot ogen fn2-pool)
        (if (not (eq code :ok)) (mv code fn2-pool)
          (fn2-gram-put-terminator tslot tgen okind oslot ogen fn2-pool))))))
(fn2-pool-preserves fn2-answer-say-body (cmd reply mask text tslot tgen okind oslot ogen fn2-pool) :position 1 :rows nil)
(in-theory (disable fn2-answer-say-body))

(in-theory (disable fn2-answer-subform-p fn2-answer-date-digits))
;; A parsed, sub-form-valid command. Returns (mv code after pending
;; fn2-pool): CODE is the renderer's, AFTER the phase the reply leads to
;; (:command or :closing), PENDING the shared pending-authentication slot
;; (:none :user :redeem; H's model: starting any exchange replaces the
;; others). With no credential store and no invitations until E2, every
;; completed exchange fails by its declared word.
(defun fn2-answer-ok (tag f0 a0 b0 mask pending posting reading seen flags real rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp a0) (natp b0))))
  (let ((c tag))
    (cond
     ((equal tag *fn2-nntp-command-capabilities*)
      (mv-let (code fn2-pool)
        (fn2-answer-say-body c *fn2-nntp-reply-capabilities-list* mask *fn2-answer-capabilities-text* tslot tgen okind oslot ogen fn2-pool)
        (mv code :command pending fn2-pool)))
     ((equal tag *fn2-nntp-command-help*)
      (mv-let (code fn2-pool)
        (fn2-answer-say-body c *fn2-nntp-reply-help-text* mask *fn2-nntp-help-text* tslot tgen okind oslot ogen fn2-pool)
        (mv code :command pending fn2-pool)))
     ((equal tag *fn2-nntp-command-quit*)
      (mv-let (code fn2-pool) (fn2-answer-say c *fn2-nntp-reply-quit-closing* mask 0 tslot tgen okind oslot ogen fn2-pool)
        (mv code :closing pending fn2-pool)))
     ((equal tag *fn2-nntp-command-mode*)
      ;; MODE READER says what the greeting said: 200 only where posting is
      ;; served (section 14.5); MODE STREAM reaches here only on a peer connection.
      (mv-let (code fn2-pool)
        (fn2-answer-say c (cond ((equal a0 1) *fn2-nntp-reply-mode-streaming*)
                                (posting *fn2-nntp-reply-mode-posting*)
                                (t *fn2-nntp-reply-mode-no-posting*))
                      mask 0 tslot tgen okind oslot ogen fn2-pool)
        (mv code :command pending fn2-pool)))
     ((equal tag *fn2-nntp-command-date*)
      (mv-let (verdict digits) (fn2-answer-date-digits seen flags real)
        (mv-let (code fn2-pool)
          (fn2-answer-say c (case verdict
                            (:ok *fn2-nntp-reply-date-date*)
                            (:no-observation *fn2-nntp-reply-date-no-observation*)
                            (:no-wall *fn2-nntp-reply-date-no-wall*)
                            (otherwise *fn2-nntp-reply-date-out-of-range*))
                        mask (nfix digits) tslot tgen okind oslot ogen fn2-pool)
          (mv code :command pending fn2-pool))))
     ((equal tag *fn2-nntp-command-authinfo*)
      (let ((form (if (eq f0 :keyword) a0 0)))
        (mv-let (reply next)
          (cond ((equal form 0) (mv *fn2-nntp-reply-authinfo-password* :user))
                ((equal form 1) (if (eq pending :user) (mv *fn2-nntp-reply-authinfo-failed* :none)
                                  (mv *fn2-nntp-reply-authinfo-sequence* pending)))
                (t (mv *fn2-nntp-reply-authinfo-no-mechanism* pending)))
          (mv-let (code fn2-pool) (fn2-answer-say c reply mask 0 tslot tgen okind oslot ogen fn2-pool)
            (mv code :command next fn2-pool)))))
     ((equal tag *fn2-nntp-command-xredeem*)
      (mv-let (reply next)
        (if (and (eq f0 :span) (fn2-gram-match a0 b0 "PASS" rslot rgen okind oslot ogen fn2-pool))
            (if (eq pending :redeem) (mv *fn2-nntp-reply-xredeem-refused* :none)
              (mv *fn2-nntp-reply-xredeem-sequence* pending))
          (mv *fn2-nntp-reply-xredeem-password* :redeem))
        (mv-let (code fn2-pool) (fn2-answer-say c reply mask 0 tslot tgen okind oslot ogen fn2-pool)
          (mv code :command next fn2-pool))))
     ((equal tag *fn2-nntp-command-list*)
      (let ((variant (if (eq f0 :keyword) a0 0)))
        (mv-let (code fn2-pool)
          (cond ((equal variant 8)
                 (fn2-answer-say-body c *fn2-nntp-reply-list-overview-fmt* mask *fn2-answer-overview-fmt-text* tslot tgen okind oslot ogen fn2-pool))
                ((equal variant 5)
                 (fn2-answer-say-body c *fn2-nntp-reply-list-headers* mask *fn2-answer-headers-text* tslot tgen okind oslot ogen fn2-pool))
                ((equal variant 6)
                 (fn2-answer-say-body c *fn2-nntp-reply-list-motd* mask "" tslot tgen okind oslot ogen fn2-pool))
                ((or (equal variant 3) (equal variant 4))
                 (fn2-answer-say c *fn2-nntp-reply-list-not-stored* mask 0 tslot tgen okind oslot ogen fn2-pool))
                (t (fn2-answer-say c (fn2-answer-interim-reply tag) mask 0 tslot tgen okind oslot ogen fn2-pool)))
          (mv code :command pending fn2-pool))))
     ;; POST where posting is served: no reply yet; the connection takes an
     ;; upload and renders 340, or waits for one (section 14.2).
     ;; a reader command: no reply here; the connection takes a query cursor
     ;; (section 15.3), or answers as a node with no archive
     ((fn2-answer-query-p tag)
      (if reading (mv :ok :query pending fn2-pool)
        (mv-let (code fn2-pool)
          (fn2-answer-say c (fn2-answer-unread-reply tag) mask 0 tslot tgen okind oslot ogen fn2-pool)
          (mv code :command pending fn2-pool))))
     ((and posting (equal tag *fn2-nntp-command-post*))
      (mv :ok :article-input pending fn2-pool))
     ((equal tag *fn2-nntp-command-takethis*)
      ;; Reached only on a peer connection, which D3 never admits: its block
      ;; follows at once and D4's article input discards it. Until then the
      ;; connection closes after the fault reply rather than read the
      ;; article as commands (NNT-003).
      (mv-let (code fn2-pool)
        (fn2-answer-say *fn2-nntp-command-none* *fn2-nntp-reply-fault* mask 0 tslot tgen okind oslot ogen fn2-pool)
        (mv code :closing pending fn2-pool)))
     ((not (equal (fn2-answer-interim-reply tag) *fn2-nntp-reply-none*))
      (mv-let (code fn2-pool)
        (fn2-answer-say c (fn2-answer-interim-reply tag) mask 0 tslot tgen okind oslot ogen fn2-pool)
        (mv code :command pending fn2-pool)))
     (t
      ;; A tag outside the table: the decision table missed a command.
      (mv :untabled :closing pending fn2-pool)))))
(fn2-pool-preserves fn2-answer-ok (tag f0 a0 b0 mask pending posting reading seen flags real rslot rgen tslot tgen okind oslot ogen fn2-pool) :position 3 :rows nil)
(in-theory (disable fn2-answer-ok))

(local (in-theory (disable fn2-nntp-parse-line)))
;; One complete command line [s, e) of the RX slot, answered into the TX
;; slot. Returns (mv code after pending fn2-pool); CODE :ok or the failing
;; renderer's code (the machine stops on any other).
(defun fn2-answer (s e mask pending posting reading seen flags real rslot rgen tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp s) (natp e))))
  (mv-let (code tag nargs f0 a0 b0 f1 a1 b1 f2 a2 b2 f3 a3 b3)
    (fn2-nntp-parse-line s e mask rslot rgen okind oslot ogen fn2-pool)
    (declare (ignore f3 a3 b3))
    (let ((none *fn2-nntp-command-none*))
      (case code
        (:ok (if (fn2-answer-subform-p tag (nfix nargs) f0 (nfix a0) (nfix b0) f1 (nfix a1) (nfix b1)
                                     f2 (nfix a2) (nfix b2) mask rslot rgen okind oslot ogen fn2-pool)
                 (fn2-answer-ok tag f0 (nfix a0) (nfix b0) mask pending posting reading seen flags real
                                     rslot rgen tslot tgen okind oslot ogen fn2-pool)
               (mv-let (rc fn2-pool) (fn2-answer-say none *fn2-nntp-reply-syntax* mask 0 tslot tgen okind oslot ogen fn2-pool)
                 (mv rc :command pending fn2-pool))))
        (:state (mv-let (rc fn2-pool) (fn2-answer-say tag (fn2-nntp-state-refusal tag) mask 0 tslot tgen okind oslot ogen fn2-pool)
                  (mv rc :command pending fn2-pool)))
        (:unknown (mv-let (rc fn2-pool) (fn2-answer-say none *fn2-nntp-reply-unknown* mask 0 tslot tgen okind oslot ogen fn2-pool)
                    (mv rc :command pending fn2-pool)))
        (:syntax (mv-let (rc fn2-pool) (fn2-answer-say none *fn2-nntp-reply-syntax* mask 0 tslot tgen okind oslot ogen fn2-pool)
                   (mv rc :command pending fn2-pool)))
        (:discard (mv-let (rc fn2-pool) (fn2-answer-say none *fn2-nntp-reply-fault* mask 0 tslot tgen okind oslot ogen fn2-pool)
                    (mv rc :closing pending fn2-pool)))
        ;; :malformed (H pin P-UTF8-WS): 501, then close.
        (otherwise (mv-let (rc fn2-pool) (fn2-answer-say none *fn2-nntp-reply-syntax* mask 0 tslot tgen okind oslot ogen fn2-pool)
                     (mv rc :closing pending fn2-pool)))))))
(fn2-pool-preserves fn2-answer (s e mask pending posting reading seen flags real rslot rgen tslot tgen okind oslot ogen fn2-pool) :position 3 :rows nil)
(in-theory (disable fn2-answer))

;; Every command tag is answered by the table: no tag reaches :untabled.
(defun fn2-answer-tabled-p (tag)
  (declare (xargs :guard t))
  (or (member-equal tag (list *fn2-nntp-command-capabilities* *fn2-nntp-command-help* *fn2-nntp-command-quit*
                              *fn2-nntp-command-mode* *fn2-nntp-command-date* *fn2-nntp-command-authinfo*
                              *fn2-nntp-command-xredeem* *fn2-nntp-command-list* *fn2-nntp-command-takethis*))
      (fn2-answer-query-p tag)
      (not (equal (fn2-answer-interim-reply tag) *fn2-nntp-reply-none*))))
(defun fn2-answer-all-tabled-p (n)
  (declare (xargs :guard (natp n)))
  (or (zp n) (and (fn2-answer-tabled-p (- n 1)) (fn2-answer-all-tabled-p (- n 1)))))
(assert-event (fn2-answer-all-tabled-p *fn2-nntp-command-none*))

;; The answer at a connection's greeting: 201 (posting is not served until
;; D5), or the capacity 400 when the row was admitted into the refusal
;; reserve, after which the connection closes.
(defun fn2-answer-greeting (refused posting mask tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (mv-let (code fn2-pool)
    (fn2-answer-say *fn2-nntp-command-none* (cond (refused *fn2-nntp-reply-busy*)
                                                  (posting *fn2-nntp-reply-greeting-posting*)
                                                  (t *fn2-nntp-reply-greeting*))
                  mask 0 tslot tgen okind oslot ogen fn2-pool)
    (mv code (if refused :closing :command) fn2-pool)))
(fn2-pool-preserves fn2-answer-greeting (refused posting mask tslot tgen okind oslot ogen fn2-pool) :position 2 :rows nil)

;; Article input (section 14.2, 14.5). The opening reply of a block: 340 for
;; POST (IHAVE's 335 with D5 3/n).
(defun fn2-answer-block-open (mask tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-answer-say *fn2-nntp-command-post* *fn2-nntp-reply-post-send* mask 0 tslot tgen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-answer-block-open (mask tslot tgen okind oslot ogen fn2-pool) :position 1 :rows nil)
;; A POST's outcome word as its reply row (the catalogue's texts are fn1's).
(defun fn2-answer-post-reply (word)
  (declare (xargs :guard t))
  (case word
    (:accepted *fn2-nntp-reply-post-received*)
    (:uncertain *fn2-nntp-reply-post-uncertain*)
    ((:malformed :framing) *fn2-nntp-reply-post-refused-unparsable*)
    (:too-large *fn2-nntp-reply-post-refused-oversize*)
    (:line-length *fn2-nntp-reply-post-refused-line-length*)
    (:header-fields *fn2-nntp-reply-post-refused-header-fields-limit*)
    (:header-lines *fn2-nntp-reply-post-refused-header-lines-limit*)
    (:header-octets *fn2-nntp-reply-post-refused-header-octets-limit*)
    (:from-missing *fn2-nntp-reply-post-refused-from-missing*)
    (:subject-missing *fn2-nntp-reply-post-refused-subject-missing*)
    (:newsgroups-missing *fn2-nntp-reply-post-refused-newsgroups-missing*)
    (:from-duplicate *fn2-nntp-reply-post-refused-from-duplicate*)
    (:subject-duplicate *fn2-nntp-reply-post-refused-subject-duplicate*)
    (:newsgroups-duplicate *fn2-nntp-reply-post-refused-newsgroups-duplicate*)
    (:message-id-duplicate *fn2-nntp-reply-post-refused-message-id-duplicate*)
    (:date-duplicate *fn2-nntp-reply-post-refused-date-duplicate*)
    (:path-duplicate *fn2-nntp-reply-post-refused-path-duplicate*)
    (:path *fn2-nntp-reply-post-refused-path-malformed*)
    (:message-id *fn2-nntp-reply-post-refused-message-id-invalid*)
    (:xref *fn2-nntp-reply-post-refused-xref*)
    (:injection-info *fn2-nntp-reply-post-refused-injection-info*)
    (:injection-date *fn2-nntp-reply-post-refused-injection-date-present*)
    (:no-clock *fn2-nntp-reply-post-refused-clock-unusable*)
    (:group *fn2-nntp-reply-post-refused-unknown-group*)
    ;; C's identity decision (section 14.4.3): a fifth content is answered
    ;; with the conflict line (the bound is C's, the word D's)
    (:duplicate *fn2-nntp-reply-post-refused-duplicate*)
    ((:conflict :identity-conflict-bound) *fn2-nntp-reply-post-refused-conflict*)
    (:unaffordable *fn2-nntp-reply-post-refused-unaffordable*)
    ;; :not-stored (the interim, D5 2/n) and every other refusal: the generic line
    (otherwise *fn2-nntp-reply-post-refused-unnamed*)))
;; The outcome reply: (mv code after fn2-pool); a framing refusal closes
;; after its reply (H's model; specs/nntp.md:513-518).
(defun fn2-answer-outcome (word mask tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (mv-let (code fn2-pool)
    (fn2-answer-say *fn2-nntp-command-post* (fn2-answer-post-reply word) mask 0 tslot tgen okind oslot ogen fn2-pool)
    (mv code (if (eq word :framing) :closing :command) fn2-pool)))
(fn2-pool-preserves fn2-answer-outcome (word mask tslot tgen okind oslot ogen fn2-pool) :position 2 :rows nil)
;; A command line over the 512-octet cap: 501, then close (RFC 3977 3.1).
(defun fn2-answer-overflow (mask tslot tgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-answer-say *fn2-nntp-command-none* *fn2-nntp-reply-syntax* mask 0 tslot tgen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-answer-overflow (mask tslot tgen okind oslot ogen fn2-pool) :position 1 :rows nil)

(assert-event
 (fn2-assert-compliant-p
  '(fn2-answer-put-text fn2-answer-civil fn2-answer-date-digits fn2-answer-field-p fn2-answer-digests-loop
    fn2-answer-subform-p fn2-answer-interim-reply fn2-answer-say fn2-answer-say-body fn2-answer-ok
    fn2-answer fn2-answer-greeting fn2-answer-overflow fn2-answer-block-open fn2-answer-post-reply fn2-answer-outcome)
  (w state)))
