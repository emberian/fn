; WIRE (ROUND2 section F.1): "replies have correct bytes, framing, ordering,
; and incomplete-stream behaviour". An independent checker over one
; connection: the octets the client sent, the octets the server sent, and
; whether the server closed. It reads neither the grammar nor the core: its
; reply-code table is written here from RFC 3977, 4643, 4644 and 8054 and
; specs/nntp.md, by command keyword, and its framing rules are the RFCs'.
; Lists are the checker's own (test-side) representation; it is never on a
; served path, so its functions are logic-only (no guards verified).
;
; Checked: (1) the stream is a greeting (200, 201, or 400 then close)
; followed by replies, each a status line `DDD[ text]CRLF` and, for the
; multi-line codes of its command, a dot-stuffed body ended by `.CRLF`;
; (2) replies answer the client's command lines one for one, in order,
; each with a code the command (or the generic set) admits; (3) a line the
; spec makes malformed (a NUL, or more than 512 octets with its CRLF) is
; answered 501 and is the last reply; a 205 or a greeting 400 is the last
; reply; nothing follows a closing reply, and a closing reply means the
; server closed; (4) an unfinished multi-line body is allowed only on a
; closed stream (incomplete-stream behaviour), and then no fresh status
; line follows inside it. Commands after the last reply are unanswered
; only after a closing reply, or after an article block's refusal that
; the server closed on; a close never excuses a complete command line. An
; unterminated tail of 511 octets or more is a (malformed) line already:
; its 501 and the close answer it.
(in-package "ACL2")

(defun fn2-wire-lines (octets cur acc)
  ; The client's complete lines (each without its CRLF), and the unfinished
  ; tail. Lists of octet lists. A line ended by a bare LF keeps the marker
  ; :bare-lf as its last element (a malformed line, RFC 3977 section 3.1).
  (declare (xargs :verify-guards nil))
  (cond ((atom octets) (mv (reverse acc) (reverse cur)))
        ((equal (car octets) 10)
         (let ((line (if (and (consp cur) (equal (car cur) 13)) (reverse (cdr cur))
                       (reverse (cons :bare-lf cur)))))
           (fn2-wire-lines (cdr octets) nil (cons line acc))))
        (t (fn2-wire-lines (cdr octets) (cons (car octets) cur) acc))))

(defun fn2-wire-upcase (b) (declare (xargs :verify-guards nil)) (if (and (natp b) (<= 97 b) (<= b 122)) (- b 32) b))
(defun fn2-wire-word (line)
  ; The first word, upper-cased, as a string.
  (declare (xargs :verify-guards nil))
  (if (or (atom line) (member (car line) '(32 9))) ""
    (concatenate 'string (coerce (list (code-char (min 255 (nfix (fn2-wire-upcase (car line)))))) 'string)
                 (fn2-wire-word (cdr line)))))
(defun fn2-wire-second-word (line)
  (declare (xargs :verify-guards nil))
  (cond ((atom line) "")
        ((member (car line) '(32 9))
         (let ((rest (if (and (consp (cdr line)) (member (cadr line) '(32 9))) (cddr line) (cdr line))))
           (fn2-wire-word rest)))
        (t (fn2-wire-second-word (cdr line)))))

; The codes each command admits (RFC 3977 sections 5-8; RFC 4643; RFC 4644;
; RFC 8054; specs/nntp.md), with the generic codes every command may get.
(defconst *fn2-wire-generic* '(400 403 480 483 500 501 502 503))
(defconst *fn2-wire-codes*
  '(("CAPABILITIES" 101) ("HELP" 100) ("QUIT" 205) ("MODE" 200 201 203) ("DATE" 111)
    ;; POST and IHAVE in two phases (RFC 3977 sections 6.3.1, 6.3.2): the
    ;; command's reply, and after 340 / 335 the reply to the article block
    ("POST" 340 440) ("POST-BLOCK" 240 441) ("IHAVE" 335 435 436) ("IHAVE-BLOCK" 235 436 437)
    ("CHECK" 238 431 438)
    ("TAKETHIS" 239 439) ("AUTHINFO" 281 381 481 482 283 383 504) ("STARTTLS" 382 580)
    ("XREDEEM" 281 381 482) ("COMPRESS" 206) ("GROUP" 211 411) ("LISTGROUP" 211 411 412)
    ("LIST" 215) ("NEXT" 223 412 420 421) ("LAST" 223 412 420 422) ("NEWGROUPS" 231) ("NEWNEWS" 230)
    ("ARTICLE" 220 412 420 423 430) ("HEAD" 221 412 420 423 430) ("BODY" 222 412 420 423 430)
    ("STAT" 223 412 420 423 430) ("OVER" 224 412 420 423 430) ("XOVER" 224 412 420 423)
    ("HDR" 225 412 420 423 430) ("XHDR" 221 412 420 423 430) ("XPAT" 221 412 430)
    ("XFNCATCHUP" 291 423) ("XFN-ZARTICLE" 229 220 423 430)))
; Multi-line codes by command (RFC 3977 section 3.4.1; 211 only for LISTGROUP).
(defun fn2-wire-multiline-p (keyword code)
  (declare (xargs :verify-guards nil))
  (or (member code '(100 101 215 220 221 222 224 225 230 231 229 291))
      (and (equal code 211) (equal keyword "LISTGROUP"))))
(defun fn2-wire-admits-p (keyword code)
  (declare (xargs :verify-guards nil))
  (let ((row (and (stringp keyword) (assoc-equal keyword *fn2-wire-codes*))))
    ; An unknown or empty keyword: 500, or 501 for a line refused before
    ; its keyword is read (leading whitespace, a control octet).
    (if row (or (member code (cdr row)) (member code *fn2-wire-generic*))
      (or (equal code 500) (equal code 501)))))

; One CRLF-ended line of the server stream: (mv found line rest), LINE
; without its CRLF; FOUND nil when no CRLF remains (an unfinished line).
(defun fn2-wire-take-line (octets acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom octets) (mv nil (reverse acc) nil))
        ((and (equal (car octets) 13) (consp (cdr octets)) (equal (cadr octets) 10))
         (mv t (reverse acc) (cddr octets)))
        (t (fn2-wire-take-line (cdr octets) (cons (car octets) acc)))))
(defun fn2-wire-digitp (b) (declare (xargs :verify-guards nil)) (and (natp b) (<= 48 b) (<= b 57)))
; A status line's code, or nil when it is not `DDD` or `DDD text`.
(defun fn2-wire-code (line)
  (declare (xargs :verify-guards nil))
  (and (true-listp line) (<= 3 (len line))
       (fn2-wire-digitp (nth 0 line)) (fn2-wire-digitp (nth 1 line)) (fn2-wire-digitp (nth 2 line))
       (or (equal (len line) 3) (equal (nth 3 line) 32))
       (+ (* 100 (- (nth 0 line) 48)) (* 10 (- (nth 1 line) 48)) (- (nth 2 line) 48))))
; A multi-line body: (mv status rest), STATUS :ok at its terminator,
; :unfinished when the stream ends inside it, :unstuffed for a body line
; opening with a single dot (RFC 3977 section 3.1.1).
(defun fn2-wire-body (octets fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :unfinished nil)
    (mv-let (found line rest) (fn2-wire-take-line octets nil)
      (cond ((not found) (mv :unfinished nil))
            ((equal line '(46)) (mv :ok rest))
            ((and (consp line) (equal (car line) 46) (not (and (consp (cdr line)) (equal (cadr line) 46))))
             (mv :unstuffed rest))
            (t (fn2-wire-body rest (- fuel 1)))))))

; Well-formed UTF-8 (RFC 3629 section 4: no overlong forms, no surrogates,
; nothing above U+10FFFF).
(defun fn2-wire-cont-p (b) (declare (xargs :verify-guards nil)) (and (natp b) (<= 128 b) (<= b 191)))
(defun fn2-wire-utf8-p (l)
  (declare (xargs :verify-guards nil :measure (len l)))
  (cond ((atom l) t)
        ((not (natp (car l))) nil)
        ((< (car l) 128) (fn2-wire-utf8-p (cdr l)))
        ((and (<= 194 (car l)) (<= (car l) 223))
         (and (consp (cdr l)) (fn2-wire-cont-p (cadr l)) (fn2-wire-utf8-p (cddr l))))
        ((and (<= 224 (car l)) (<= (car l) 239))
         (and (consp (cdr l)) (consp (cddr l))
              (natp (cadr l))
              (cond ((equal (car l) 224) (and (<= 160 (cadr l)) (<= (cadr l) 191)))
                    ((equal (car l) 237) (and (<= 128 (cadr l)) (<= (cadr l) 159)))
                    (t (fn2-wire-cont-p (cadr l))))
              (fn2-wire-cont-p (caddr l)) (fn2-wire-utf8-p (cdddr l))))
        ((and (<= 240 (car l)) (<= (car l) 244))
         (and (consp (cdr l)) (consp (cddr l)) (consp (cdddr l))
              (natp (cadr l))
              (cond ((equal (car l) 240) (and (<= 144 (cadr l)) (<= (cadr l) 191)))
                    ((equal (car l) 244) (and (<= 128 (cadr l)) (<= (cadr l) 143)))
                    (t (fn2-wire-cont-p (cadr l))))
              (fn2-wire-cont-p (caddr l)) (fn2-wire-cont-p (cadddr l)) (fn2-wire-utf8-p (cddddr l))))
        (t nil)))
(defun fn2-wire-malformed-p (line)
  ; The client line the spec makes malformed (RFC 3977 sections 3.1 and
  ; 12.5; specs/nntp.md:513-518): empty, ended by a bare LF, holding a bare
  ; CR or a NUL, over 512 octets with its CRLF, or not UTF-8 (H's first spec
  ; pin, 22de14c4d: 501 and close whatever else is wrong).
  (declare (xargs :verify-guards nil))
  (and (true-listp line)
       (or (null line) (member-eq :bare-lf line) (member 13 line) (member 0 line)
           (< 510 (len line)) (not (fn2-wire-utf8-p line)))))

; After 340 (POST) or 335 (IHAVE) the client's next lines are the article
; block up to its "." line; they stand as one entry, KEYWORD-BLOCK, which
; the next reply answers. A block the client never ended is cut input.
(defun fn2-wire-skip-block (lines)
  ; (mv found rest): the lines after the block's terminator line
  (declare (xargs :verify-guards nil))
  (cond ((atom lines) (mv nil nil))
        ((equal (car lines) '(46)) (mv t (cdr lines)))
        (t (fn2-wire-skip-block (cdr lines)))))
(defun fn2-wire-entry-keyword (line)
  (declare (xargs :verify-guards nil))
  (cond ((eq line :post-block) "POST-BLOCK") ((eq line :ihave-block) "IHAVE-BLOCK")
        (t (fn2-wire-word line))))
(defun fn2-wire-next-lines (keyword code lines)
  ; the client entries after the one CODE answered: (mv ok rest), OK nil
  ; when a block was opened and the client never ended it
  (declare (xargs :verify-guards nil))
  (let ((marker (cond ((and (equal keyword "POST") (equal code 340)) :post-block)
                      ((and (equal keyword "IHAVE") (equal code 335)) :ihave-block))))
    (if (not marker) (mv t (cdr lines))
      (mv-let (found rest) (fn2-wire-skip-block (cdr lines))
        (if found (mv t (cons marker rest)) (mv nil nil))))))

; Walk the replies against the client's lines. Returns :pass or
; (:fail reason index).
(defun fn2-wire-walk (wire lines cut closed index done fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (list :fail :fuel index))
   ;; DONE: t after a closing reply (205, a malformed line's 501): nothing
   ;; follows and the server closed; :may-close after an article block's
   ;; refusal (the server may close after it, H's model does for a framing
   ;; or bound refusal); nil otherwise. Every complete command line the
   ;; client sent before the close is answered: a close truncates only an
   ;; incomplete line, or the lines after a closing reply.
   ((atom wire)
    (cond ((and (eq done t) (not closed)) (list :fail :closing-reply-but-open index))
          ((or (eq done t) (atom lines)) :pass)
          ((and closed (eq done :may-close)) :pass)
          (t (list :fail (if closed :closed-before-reply :missing-reply) index))))
   ((eq done t) (list :fail :reply-after-close index))
   ((atom lines) (list :fail :unasked-reply index))
   (t (mv-let (found status rest) (fn2-wire-take-line wire nil)
        (let* ((code (and found (fn2-wire-code status)))
               (line (car lines)) (keyword (fn2-wire-entry-keyword line)))
          (cond
           ((not found) (if closed :pass (list :fail :unfinished-status index)))
           ((not code) (list :fail :bad-status-line index))
           ((fn2-wire-malformed-p line)
            (if (equal code 501) (fn2-wire-walk rest (cdr lines) cut closed (+ 1 index) t (- fuel 1))
              (list :fail :malformed-not-501 index)))
           ((not (fn2-wire-admits-p keyword code)) (list :fail :code-not-admitted index))
           ((fn2-wire-multiline-p keyword code)
            (mv-let (bstatus brest) (fn2-wire-body rest 100000)
              (case bstatus
                (:ok (fn2-wire-walk brest (cdr lines) cut closed (+ 1 index) (equal code 205) (- fuel 1)))
                (:unfinished (if closed :pass (list :fail :unfinished-body index)))
                (otherwise (list :fail :unstuffed-body index)))))
           (t (mv-let (ok next) (fn2-wire-next-lines keyword code lines)
                ;; an opened block the client never ended: its reply is unasked
                (if (not ok)
                    (if (and (atom rest) (or closed cut)) :pass (list :fail :unended-block index))
                  (fn2-wire-walk rest next cut closed (+ 1 index)
                                 (cond ((equal code 205) t)
                                       ((and (member-eq line '(:post-block :ihave-block))
                                             (not (member code '(240 235)))) :may-close)
                                       (t nil))
                                 (- fuel 1)))))))))))

; The whole connection: CLIENT octets sent, WIRE octets received, CLOSED.
(defun fn2-wire-check (client wire closed)
  (declare (xargs :verify-guards nil))
  (mv-let (found greeting rest) (fn2-wire-take-line wire nil)
    (let ((code (and found (fn2-wire-code greeting))))
      (cond ((not found) (if (and closed (atom wire)) :pass (list :fail :no-greeting 0)))
            ((member code '(200 201))
             (mv-let (lines tail) (fn2-wire-lines client nil nil)
               ;; an unterminated tail over the cap (511 octets or more
               ;; before any CRLF) is already a malformed line: the server
               ;; may answer it 501 and close before its end arrives (the
               ;; line-limit pin; seen under 1- and 7-octet delivery)
               (let ((lines (if (< 510 (len tail)) (append lines (list tail)) lines)))
                 (fn2-wire-walk rest lines (consp tail) closed 0 nil (+ 1 (len lines))))))
            ((equal code 400) (if (and (atom rest) closed) :pass (list :fail :refusal-not-final 0)))
            (t (list :fail :bad-greeting 0))))))

(defun fn2-wire-pass-p (client wire closed)
  (declare (xargs :verify-guards nil))
  (eq (fn2-wire-check client wire closed) :pass))
