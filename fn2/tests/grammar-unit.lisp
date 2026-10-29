; D2a evidence: the grammar's teeth and the every-split tests. Independently
; written transcripts (pipelined commands, every argument kind, the 512-octet
; boundary, bare LF/CR, NUL and 8-bit octets, an unterminated final line,
; dot-stuffed blocks with the terminator split, a refused block discarded to
; its terminator, the STARTTLS hand-off) parse to the same events and render
; the same reply bytes at every split point, and at every pair of split
; points for transcripts up to 64 octets.
; Run: sh fn2/tools/certify.sh tests/grammar-unit.lisp
(in-package "ACL2")
(include-book "../books/nntp-grammar")
(in-theory (disable fn2-nntp-run fn2-nntp-drive fn2-nntp-feed fn2-nntp-render fn2-nntp-parse-line fn2-nntp-parse-outcome-p fn2-gram-frame-outcome-p fn2-nntp-slot-bytes))

(defun fn2-gu-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-gu-octets (cdr cs)))))
(in-theory (disable fn2-gu-octets))
(defmacro fn2-gu-crlf () '(coerce (list (code-char 13) (code-char 10)) 'string))
(defun fn2-gu-lines (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (atom lines) ""
    (concatenate 'string (car lines) (coerce (list (code-char 13) (code-char 10)) 'string)
                 (fn2-gu-lines (cdr lines)))))
(in-theory (disable fn2-gu-lines))
(defun fn2-gu-text (s) (declare (xargs :guard (stringp s))) (fn2-gu-octets (coerce s 'list)))
(in-theory (disable fn2-gu-text))
(defun fn2-gu-repeat (n byte) (declare (xargs :guard (natp n))) (if (zp n) nil (cons byte (fn2-gu-repeat (- n 1) byte))))

; A command line of exactly N octets including CRLF: "GROUP " and a name.
(in-theory (disable fn2-gu-repeat))
(defun fn2-gu-group-line (n)
  (declare (xargs :guard (natp n)))
  (append (fn2-gu-text "GROUP ") (fn2-gu-repeat (nfix (- n 8)) 97) (list 13 10)))

(in-theory (disable fn2-gu-group-line))
(defconst *fn2-gu-transcripts*
  (list
   (fn2-gu-text (fn2-gu-lines '("CAPABILITIES" "HELP" "QUIT")))
   (fn2-gu-text (fn2-gu-lines '("group misc.test" "ARTICLE 42" "HEAD <a@b.example>" "STAT")))
   (fn2-gu-text (fn2-gu-lines '("LISTGROUP misc.test 3-" "LISTGROUP misc.test 3-9" "LISTGROUP")))
   (fn2-gu-text (fn2-gu-lines '("OVER 1-5" "XOVER <m@x>" "OVER" "HDR Subject 4-")))
   (fn2-gu-text (fn2-gu-lines '("XPAT Subject 1- *foo* *bar*" "XHDR From <q@r>")))
   (fn2-gu-text (fn2-gu-lines '("NEWGROUPS 20261029 120000 GMT" "NEWNEWS comp.*,!comp.sys 261029 000000")))
   (fn2-gu-text (fn2-gu-lines '("LIST" "LIST ACTIVE.TIMES" "LIST HEADERS MSGID" "LIST BOGUS")))
   (fn2-gu-text (fn2-gu-lines '("MODE READER" "MODE STREAM" "MODE" "DATE extra")))
   (fn2-gu-text (fn2-gu-lines '("FOO bar" "ARTICLE 0" "ARTICLE 1-2" "ARTICLE <bad" "NEWNEWS !x 20261029 000000")))
   (fn2-gu-text (fn2-gu-lines '("IHAVE <a@b>" "CHECK <c@d>" "TAKETHIS <e@f>" "XFNCATCHUP * 0 x 1")))
   (fn2-gu-text (fn2-gu-lines '("COMPRESS DEFLATE" "AUTHINFO USER alice" "AUTHINFO PASS secret")))
   (fn2-gu-text (fn2-gu-lines '("POST" "From: a@b" "Subject: x" "" "..leading dot" "." "DATE")))
   (fn2-gu-text (fn2-gu-lines '("POST" "Subject: y" ".unescaped" "body" "." "HELP")))
   (fn2-gu-text (fn2-gu-lines '("STARTTLS" "GROUP after.handshake")))
   (fn2-gu-text (fn2-gu-lines '(" GROUP leading" "GROUP trailing " "GROUP	tab")))
   (append (fn2-gu-text "GROUP a") (list 10) (fn2-gu-text (fn2-gu-lines '("HELP"))))
   (append (fn2-gu-text "GRO") (list 13) (fn2-gu-text (fn2-gu-lines '("UP x" "QUIT"))))
   (append (fn2-gu-text "GROUP a") (list 0) (fn2-gu-text (fn2-gu-lines '("b"))))
   (append (fn2-gu-text "GROUP caf") (list #xc3 #xa9) (fn2-gu-text (fn2-gu-lines '("" "HELP"))))
   (append (fn2-gu-text "GROUP caf") (list #xe9) (fn2-gu-text (fn2-gu-lines '("" "HELP"))))
   (append (fn2-gu-text "GROUP x") (list 1) (fn2-gu-text (fn2-gu-lines '("" "HELP"))))
   (fn2-gu-text (concatenate 'string (fn2-gu-lines '("HELP" "DATE")) "GROUP unterminated"))
   (append (fn2-gu-group-line 511) (fn2-gu-text (fn2-gu-lines '("HELP"))))
   (append (fn2-gu-group-line 512) (fn2-gu-text (fn2-gu-lines '("HELP"))))
   (append (fn2-gu-group-line 513) (fn2-gu-text (fn2-gu-lines '("HELP"))))
   (fn2-gu-text (fn2-gu-lines '("" "HELP")))
   (fn2-gu-text (fn2-gu-lines '("CAPABILITIES AUTOUPDATE" "CAPABILITIES x" "XFN-ZARTICLE <a@b> d1 d2")))
   ; RFC 3977 section 3.1's argument cap: 497 octets of arguments (505 in all) pass, 498 do not.
   (append (fn2-gu-group-line 505) (fn2-gu-text (fn2-gu-lines '("HELP"))))
   (append (fn2-gu-group-line 506) (fn2-gu-text (fn2-gu-lines '("HELP"))))))

(defconst *fn2-gu-masks*
  (list *fn2-nntp-state-reader* *fn2-nntp-state-peer*
        (logior *fn2-nntp-state-reader* *fn2-nntp-state-authenticated*)))

; ------------------------------------------------------------------------
; Every split point 1..n-1 gives the unsplit outcome; every pair of split
; points too when the transcript has at most 64 octets.
(defun fn2-gu-singles (left k octets mask whole)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (equal (fn2-nntp-run octets (list k) mask) whole)
         (fn2-gu-singles (- left 1) (+ 1 k) octets mask whole))))
(in-theory (disable fn2-gu-singles))
(defun fn2-gu-pairs-from (left k j octets mask whole)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (equal (fn2-nntp-run octets (list k (- j k)) mask) whole)
         (fn2-gu-pairs-from (- left 1) k (+ 1 j) octets mask whole))))
(in-theory (disable fn2-gu-pairs-from))
(defun fn2-gu-pairs (left k n octets mask whole)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (fn2-gu-pairs-from (nfix (- n (+ k 1))) k (+ 1 k) octets mask whole)
         (fn2-gu-pairs (- left 1) (+ 1 k) n octets mask whole))))
(in-theory (disable fn2-gu-pairs))
(defun fn2-gu-every-split (octets mask)
  (declare (xargs :verify-guards nil))
  (let ((whole (fn2-nntp-run octets nil mask)) (n (len octets)))
    (and (fn2-gu-singles (nfix (- n 1)) 1 octets mask whole)
         (or (> n 64) (fn2-gu-pairs (nfix (- n 1)) 1 n octets mask whole))
         ; Bytewise arrival is the extreme split.
         (equal (fn2-nntp-run octets (fn2-gu-repeat n 1) mask) whole))))
(in-theory (disable fn2-gu-every-split))
(defun fn2-gu-all-masks (octets masks)
  (declare (xargs :verify-guards nil))
  (if (atom masks) t (and (fn2-gu-every-split octets (car masks)) (fn2-gu-all-masks octets (cdr masks)))))

; Expected outcomes, independently of the parser: the event kinds and codes
; of a few transcripts, so that a split-invariant but wrong parser fails.
(in-theory (disable fn2-gu-all-masks))
(defun fn2-gu-all-splits (ts masks)
  (declare (xargs :verify-guards nil))
  (if (atom ts) t
    (and (fn2-gu-all-masks (car ts) masks) (fn2-gu-all-splits (cdr ts) masks))))
(in-theory (disable fn2-gu-all-splits))
(defun fn2-gu-codes (events)
  (declare (xargs :verify-guards nil))
  (if (atom events) nil
    (cons (if (eq (car (car events)) :command) (cadr (car events)) (car (car events)))
          (fn2-gu-codes (cdr events)))))
(in-theory (disable fn2-gu-codes))
(defun fn2-gu-outcome (i mask)
  (declare (xargs :verify-guards nil))
  (fn2-gu-codes (nth 3 (fn2-nntp-run (nth i *fn2-gu-transcripts*) nil mask))))
(in-theory (disable fn2-gu-outcome))
(defun fn2-gu-reply-text (i mask)
  (declare (xargs :verify-guards nil))
  (nth 4 (fn2-nntp-run (nth i *fn2-gu-transcripts*) nil mask)))

(in-theory (disable fn2-gu-reply-text))
(defmacro fn2-gu-expect (x y)
  `(assert-event (equal ,x ,y) :msg (msg "~x0 gives ~x1, expected ~x2" ',x ,x ,y)))
(fn2-gu-expect (fn2-gu-outcome 0 *fn2-nntp-state-reader*) '(:ok :ok :ok))
(fn2-gu-expect (fn2-gu-outcome 8 *fn2-nntp-state-reader*) '(:unknown :syntax :syntax :syntax :syntax))
(fn2-gu-expect (fn2-gu-outcome 9 *fn2-nntp-state-reader*) '(:state :state :state :state))
(fn2-gu-expect (fn2-gu-outcome 9 *fn2-nntp-state-peer*) '(:ok :data :data :data))
(fn2-gu-expect (fn2-gu-outcome 10 *fn2-nntp-state-reader*) '(:state :ok :ok))
(fn2-gu-expect (fn2-gu-outcome 11 *fn2-nntp-state-reader*) '(:ok :data :data :data :data :terminator :ok))
(fn2-gu-expect (fn2-gu-outcome 12 *fn2-nntp-state-reader*) '(:ok :data :bad-line :data :terminator :ok))
(fn2-gu-expect (fn2-gu-outcome 13 *fn2-nntp-state-reader*) '(:ok))
(fn2-gu-expect (fn2-gu-outcome 14 *fn2-nntp-state-reader*) '(:syntax :syntax :ok))
(fn2-gu-expect (fn2-gu-outcome 15 *fn2-nntp-state-reader*) '(:malformed))
(fn2-gu-expect (fn2-gu-outcome 16 *fn2-nntp-state-reader*) '(:malformed))
(fn2-gu-expect (fn2-gu-outcome 17 *fn2-nntp-state-reader*) '(:malformed))
(fn2-gu-expect (fn2-gu-outcome 18 *fn2-nntp-state-reader*) '(:ok :ok))
(fn2-gu-expect (fn2-gu-outcome 19 *fn2-nntp-state-reader*) '(:malformed))
(fn2-gu-expect (fn2-gu-outcome 20 *fn2-nntp-state-reader*) '(:syntax :ok))
(fn2-gu-expect (fn2-gu-outcome 21 *fn2-nntp-state-reader*) '(:ok :ok))
(fn2-gu-expect (fn2-gu-outcome 22 *fn2-nntp-state-reader*) '(:syntax :ok))
(fn2-gu-expect (fn2-gu-outcome 23 *fn2-nntp-state-reader*) '(:syntax :ok))
(fn2-gu-expect (fn2-gu-outcome 24 *fn2-nntp-state-reader*) '(:overflow))
(fn2-gu-expect (fn2-gu-outcome 25 *fn2-nntp-state-reader*) '(:malformed))
(fn2-gu-expect (fn2-gu-outcome 27 *fn2-nntp-state-reader*) '(:ok :ok))
(fn2-gu-expect (fn2-gu-outcome 28 *fn2-nntp-state-reader*) '(:syntax :ok))
(fn2-gu-expect (fn2-gu-outcome 26 *fn2-nntp-state-reader*) '(:ok :syntax :ok))
(assert-event (equal (fn2-gu-reply-text 0 *fn2-nntp-state-reader*)
                     (fn2-gu-text (fn2-gu-lines '("101 capability list follows" "100 help text follows"
                                                  "205 closing connection")))))
(assert-event (equal (fn2-gu-reply-text 8 *fn2-nntp-state-reader*)
                     (fn2-gu-text (fn2-gu-lines '("500 command not recognized" "501 syntax error" "501 syntax error"
                                                  "501 syntax error" "501 syntax error")))))

; ------------------------------------------------------------------------
; Teeth: fragmentation.
(defun fn2-nntp-test-fragmentation ()
  (declare (xargs :verify-guards nil))
  (fn2-gu-all-splits *fn2-gu-transcripts* *fn2-gu-masks*))
; A chunker that forgets a retained partial line at each chunk boundary
; (start := pos) is split-sensitive; the statement's equality rejects it.
(in-theory (disable fn2-nntp-test-fragmentation))
(defun fn2-gu-wrong-chunks (sizes octets mode pos mask events slot gen tslot tgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (len octets)))
  (if (atom octets) (mv events fn2-pool)
    (let ((k (if (and (consp sizes) (posp (car sizes))) (car sizes) (len octets))))
      (mv-let (rest fn2-pool) (fn2-nntp-feed k octets slot gen fn2-pool)
        (mv-let (mode start pos overflow events fn2-pool)
          (fn2-nntp-drive (+ 8 (* 4 (len octets))) mode pos pos 0 mask nil events slot gen tslot tgen fn2-pool)
          (declare (ignore start overflow))
          (if (>= (len rest) (len octets)) (mv events fn2-pool)
            (fn2-gu-wrong-chunks (if (consp sizes) (cdr sizes) nil) rest mode pos mask events slot gen tslot tgen fn2-pool)))))))
(in-theory (disable fn2-gu-wrong-chunks))
(defun fn2-gu-wrong-run (octets sizes mask)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
        (mv-let (c1 slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
          (declare (ignore c1))
          (mv-let (c2 tslot tgen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
            (declare (ignore c2))
            (mv-let (events fn2-pool)
              (fn2-gu-wrong-chunks sizes octets :command 0 mask nil slot gen tslot tgen fn2-pool)
              (mv events fn2-pool)))))
      result)))
(in-theory (disable fn2-gu-wrong-run))
(defun fn2-nntp-test-fragmentation-negative ()
  (declare (xargs :verify-guards nil))
  (let ((octets (nth 1 *fn2-gu-transcripts*)))
    (not (equal (fn2-gu-wrong-run octets '(3) *fn2-nntp-state-reader*)
                (fn2-gu-wrong-run octets nil *fn2-nntp-state-reader*)))))

; ------------------------------------------------------------------------
; A local pool with OCTETS in one slot, for direct framer and parser checks.
(in-theory (disable fn2-nntp-test-fragmentation-negative))
(defun fn2-gu-frame-at (start pos slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (fn2-gram-frame-outcome-p 1 start pos 0 *fn2-nntp-line-cap* slot gen 1 1 1 fn2-pool)
       (fn2-gram-frame-outcome-p 4096 start pos 0 *fn2-nntp-line-cap* slot gen 1 1 1 fn2-pool)
       (or (> (- pos start) 4) (fn2-gram-frame-outcome-p 4096 start pos 1 4 slot gen 1 1 1 fn2-pool))
       (fn2-nntp-parse-outcome-p start pos *fn2-nntp-state-reader* slot gen 1 1 1 fn2-pool)))
(in-theory (disable fn2-gu-frame-at))
(defun fn2-gu-frames-pos (left start pos slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (fn2-gu-frame-at start pos slot gen fn2-pool)
         (fn2-gu-frames-pos (- left 1) start (+ 1 pos) slot gen fn2-pool))))
(in-theory (disable fn2-gu-frames-pos))
(defun fn2-gu-frames-start (left start n slot gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (fn2-gu-frames-pos (min 20 (+ 1 (nfix (- n start)))) start start slot gen fn2-pool)
         (fn2-gu-frames-start (- left 1) (+ 1 start) n slot gen fn2-pool))))
(in-theory (disable fn2-gu-frames-start))
(defun fn2-gu-probe-frames (slot gen n fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (fn2-gu-frames-start (+ 1 (nfix n)) 0 n slot gen fn2-pool))
(in-theory (disable fn2-gu-probe-frames))
(defun fn2-gu-with-slot (octets)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (result fn2-pool)
      (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
        (mv-let (c slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
          (declare (ignore c))
          (mv-let (rest fn2-pool) (fn2-nntp-feed (len octets) octets slot gen fn2-pool)
            (declare (ignore rest))
            (mv (fn2-gu-probe-frames slot gen (len octets) fn2-pool) fn2-pool))))
      result)))
; The framer's shape at every (start, pos) with start <= pos <= n, start
; within cap of pos, for budgets 0, 1, 7 and the run quantum, both overflow
; states; and the parser's shape on every [s, e) with s < e <= n.
(in-theory (disable fn2-gu-with-slot))
(defun fn2-gu-probe-all (ts)
  (declare (xargs :verify-guards nil))
  (if (atom ts) t (and (fn2-gu-with-slot (car ts)) (fn2-gu-probe-all (cdr ts)))))
; Arbitrary octets beyond the transcripts: every byte value in a line.
(in-theory (disable fn2-gu-probe-all))
(defun fn2-gu-all-bytes (left b)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) nil (cons b (fn2-gu-all-bytes (- left 1) (+ 1 b)))))
(in-theory (disable fn2-gu-all-bytes))
(defconst *fn2-gu-short-transcripts*
  (list (nth 0 *fn2-gu-transcripts*) (nth 8 *fn2-gu-transcripts*) (nth 12 *fn2-gu-transcripts*)
        (nth 15 *fn2-gu-transcripts*) (nth 19 *fn2-gu-transcripts*)
        (append (fn2-gu-all-bytes 256 0) (list 13 10))))

(defun fn2-gram-test-frame-shapes ()
  (declare (xargs :verify-guards nil))
  (fn2-gu-probe-all *fn2-gu-short-transcripts*))
; A framer that keeps retaining an over-cap line breaks bounded retention:
; the shape predicate refuses its outcome.
(in-theory (disable fn2-gram-test-frame-shapes))
(defun fn2-gram-test-frame-shapes-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-gram-frame-shape-p 4096 0 0 4 :need-more 0 9 0 9))     ; retains 9 > cap 4
       (not (fn2-gram-frame-shape-p 4096 0 5 512 :line 0 3 0 9))        ; moved backwards
       (not (fn2-gram-frame-shape-p 2 0 0 512 :need-more 0 5 0 9))       ; over budget
       (not (fn2-gram-frame-shape-p 4096 0 0 512 :bogus 0 1 0 9))))     ; undeclared status

(in-theory (disable fn2-gram-test-frame-shapes-negative))
(defun fn2-nntp-test-parse-total ()
  (declare (xargs :verify-guards nil))
  (fn2-gu-probe-all *fn2-gu-short-transcripts*))
; A parser that answers :ok for an unknown keyword is refused by the shape.
(in-theory (disable fn2-nntp-test-parse-total))
(defun fn2-nntp-test-parse-total-negative ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-gram-parse-shape-p :ok *fn2-nntp-command-none* 0 *fn2-nntp-command-none*))
       (not (fn2-gram-parse-shape-p :unknown 3 0 *fn2-nntp-command-none*))
       (not (fn2-gram-parse-shape-p :ok 3 5 *fn2-nntp-command-none*))))

; ------------------------------------------------------------------------
; Reply typing: render every reply under every command tag and mask; a
; rendered status line always opens with the declared code and only a
; command's own admitted reply is written.
(in-theory (disable fn2-nntp-test-parse-total-negative))
(defun fn2-gu-render-check (cmd reply mask fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
    (mv-let (c slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
      (declare (ignore c))
      (mv-let (code fn2-pool) (fn2-nntp-render cmd reply mask 7 8 9 slot gen 0 0 slot gen 1 1 1 fn2-pool)
        (let* ((bytes (fn2-nntp-slot-bytes 0 3 slot gen fn2-pool))
               (digits (fn2-gu-text (coerce (explode-nonnegative-integer (fn2-nntp-reply-code reply) 10 nil) 'string))))
          (mv (if (eq code :ok)
                  (and (equal (fn2-nntp-reply-command reply) cmd) (fn2-nntp-reply-admitted reply mask)
                       (equal bytes digits))
                (not (and (equal (fn2-nntp-reply-command reply) cmd) (fn2-nntp-reply-admitted reply mask))))
              fn2-pool))))))
(in-theory (disable fn2-gu-render-check))
(defun fn2-gu-render-cmds (left cmd reply mask)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (with-local-stobj fn2-pool
           (mv-let (ok fn2-pool) (fn2-gu-render-check cmd reply mask fn2-pool) ok))
         (fn2-gu-render-cmds (- left 1) (+ 1 cmd) reply mask))))
(in-theory (disable fn2-gu-render-cmds))
(defun fn2-gu-render-masks (reply masks)
  (declare (xargs :verify-guards nil))
  (if (atom masks) t
    (and (fn2-gu-render-cmds (+ 1 *fn2-nntp-command-none*) 0 reply (car masks)) (fn2-gu-render-masks reply (cdr masks)))))
(in-theory (disable fn2-gu-render-masks))
(defun fn2-gu-render-replies (left reply masks)
  (declare (xargs :verify-guards nil :measure (nfix left)))
  (if (zp left) t
    (and (fn2-gu-render-masks reply masks)
         (fn2-gu-render-replies (- left 1) (+ 1 reply) masks))))
(in-theory (disable fn2-gu-render-replies))
(defun fn2-nntp-test-reply-typing ()
  (declare (xargs :verify-guards nil))
  (and (fn2-gu-render-replies *fn2-nntp-reply-count* 0 *fn2-gu-masks*)
       ; Peer-layer replies are refused on a reader connection and written on a peer one.
       (with-local-stobj fn2-pool
         (mv-let (ok fn2-pool) (fn2-gu-render-check *fn2-nntp-command-check* *fn2-nntp-reply-check-wanted*
                                                    *fn2-nntp-state-peer* fn2-pool) ok))))
; A renderer without the type check writes another command's reply: the
; typing condition refuses that outcome.
(in-theory (disable fn2-nntp-test-reply-typing))
(defun fn2-gu-untyped-render (reply fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (let ((fn2-pool (fn2-pool-init '((2 . 8192)) 1 1000 fn2-pool)))
    (mv-let (c slot gen fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool)
      (declare (ignore c))
      (fn2-gram-put-template 0 (fn2-nntp-reply-template reply) 0 0 0 0 slot gen 0 0 slot gen 1 1 1 fn2-pool))))
(in-theory (disable fn2-gu-untyped-render))
(defun fn2-nntp-test-reply-typing-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((reply *fn2-nntp-reply-article-sent*)
         (cmd *fn2-nntp-command-group*)
         (code (with-local-stobj fn2-pool (mv-let (code fn2-pool) (fn2-gu-untyped-render reply fn2-pool) code))))
    (and (eq code :ok)
         (not (and (equal (fn2-nntp-reply-command reply) cmd)
                   (fn2-nntp-reply-admitted reply *fn2-nntp-state-reader*))))))

(in-theory (disable fn2-nntp-test-reply-typing-negative))
(fn2-assert-owed-teeth fn2-gram-frame-total-linear fn2-nntp-parse-total fn2-nntp-fragmentation
                       fn2-nntp-reply-typing)

; The declared table, exported for tests/grammar-oracle.py.
(defun fn2-gu-codes-of (replies)
  (declare (xargs :verify-guards nil))
  (if (atom replies) nil
    (cons (fn2-decl-get :code (cdar replies)) (fn2-gu-codes-of (cdr replies)))))
(in-theory (disable fn2-gu-codes-of))
(defun fn2-gu-command-rows (rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (let ((p (cdar rows)))
      (cons (list (fn2-decl-get :keyword p) (fn2-decl-get :syntax p) (fn2-decl-get :protocol-states p)
                  (fn2-decl-get :block p) (fn2-decl-get :help p) (fn2-decl-get :spec p)
                  (fn2-gu-codes-of (fn2-decl-get :replies p)))
            (fn2-gu-command-rows (cdr rows))))))
(in-theory (disable fn2-gu-command-rows))
(make-event
 (value `(defconst *fn2-gu-table* ',(fn2-gu-command-rows (fn2-decl-rows :command (w state))))))
(assert-event (equal (len *fn2-gu-table*) *fn2-nntp-command-none*))
