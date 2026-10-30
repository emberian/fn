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
; only if the server closed or the client's last line was cut.
(in-package "ACL2")

(defun fn2-wire-lines (octets cur acc)
  ; The client's complete lines (each without its CRLF or LF), and the
  ; unfinished tail. Lists of octet lists.
  (declare (xargs :verify-guards nil))
  (cond ((atom octets) (mv (reverse acc) (reverse cur)))
        ((equal (car octets) 10)
         (let ((line (reverse (if (and (consp cur) (equal (car cur) 13)) (cdr cur) cur))))
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
    ("POST" 340 440 441 240) ("IHAVE" 335 435 436 437 235) ("CHECK" 238 431 438)
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

(defun fn2-wire-malformed-p (line)
  ; The client line the spec makes malformed: a NUL, or over 512 octets
  ; with its CRLF (RFC 3977 section 3.1; specs/nntp.md:513-518).
  (declare (xargs :verify-guards nil))
  (or (and (true-listp line) (member 0 line)) (and (true-listp line) (< 510 (len line)))))

; Walk the replies against the client's lines. Returns :pass or
; (:fail reason index).
(defun fn2-wire-walk (wire lines cut closed index done fuel)
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (list :fail :fuel index))
   ((atom wire)
    (cond ((and done (not closed)) (list :fail :closing-reply-but-open index))
          ((or closed (atom lines) cut) :pass)
          (t (list :fail :missing-reply index))))
   (done (list :fail :reply-after-close index))
   ((atom lines) (list :fail :unasked-reply index))
   (t (mv-let (found status rest) (fn2-wire-take-line wire nil)
        (let* ((code (and found (fn2-wire-code status)))
               (line (car lines)) (keyword (fn2-wire-word line)))
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
           (t (fn2-wire-walk rest (cdr lines) cut closed (+ 1 index) (equal code 205) (- fuel 1)))))))))

; The whole connection: CLIENT octets sent, WIRE octets received, CLOSED.
(defun fn2-wire-check (client wire closed)
  (declare (xargs :verify-guards nil))
  (mv-let (found greeting rest) (fn2-wire-take-line wire nil)
    (let ((code (and found (fn2-wire-code greeting))))
      (cond ((not found) (if (and closed (atom wire)) :pass (list :fail :no-greeting 0)))
            ((member code '(200 201))
             (mv-let (lines tail) (fn2-wire-lines client nil nil)
               (fn2-wire-walk rest lines (consp tail) closed 0 nil (+ 1 (len lines)))))
            ((equal code 400) (if (and (atom rest) closed) :pass (list :fail :refusal-not-final 0)))
            (t (list :fail :bad-greeting 0))))))

(defun fn2-wire-pass-p (client wire closed)
  (declare (xargs :verify-guards nil))
  (eq (fn2-wire-check client wire closed) :pass))
