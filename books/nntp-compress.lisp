; fn: the COMPRESS command's decisions (RFC 8054; lane compress, PRF-911).
; Prefix `fn-zc-'.
;
; books/nntp-auth.lisp answers COMPRESS (fn-auth-compress) and keeps the
; connection's compression state in its session; this book is what those
; answers are made of, so that the wide book carries only the arms:
;
;   the algorithms fn offers        `fn-zc-algorithms' ("DEFLATE"; a shared
;                                   preset dictionary is negotiated by digest,
;                                   docs/extensions/nntp-compress-dict.md)
;   the algorithm's grammar         `fn-zc-algorithm-syntaxp' (section 5.3:
;                                   1*20 of UPPER / DIGIT / "-" / "_",
;                                   case-sensitive)
;   the state                    nil (no layer), (:owed ALG) (206 was
;                                   answered; the host installs the layer
;                                   before the next octet it reads is NNTP),
;                                   (:active ALG)
;   the capability block            `fn-zc-capability-lines': COMPRESS and the
;                                   algorithm list only while a layer may be
;                                   started; once one is active, neither
;                                   COMPRESS, nor STARTTLS, nor any AUTHINFO
;                                   label (section 2.2.2)
;   the effect the host acts on     (:compress ALG)
;   the outbound stream's shape     `fn-zc-deflate-params' (level, window
;                                   bits, memory level: zlib's, host/native/
;                                   fn-deflate.c) and `fn-zc-layer-octets',
;                                   what a layer costs (books/connection-
;                                   budget.lisp charges every connection it)
;
; WHO MAY COMPRESS (local policy, stronger than RFC 8054 section 2.2.2).  A
; connection that authenticated, or that speaks for a configured peer
; (`fn-zc-may-startp'): CRIME-style attacks (RFC 8054 section 7) read secrets
; out of compressed lengths, and the one secret a reader sends is its
; password, which AUTHINFO after COMPRESS may no longer carry (502) and
; which an authenticated connection has already sent.

(in-package "ACL2")
(include-book "nntp-syntax")
(include-book "nntp-effects")

(defconst *fn-zc-algorithms* '("DEFLATE"))

(defun fn-zc-algorithms ()
  (declare (xargs :guard t))
  *fn-zc-algorithms*)

; Section 5.3: alg-char = UPPER / DIGIT / "-" / "_".
(defun fn-zc-alg-charp (o)
  (declare (xargs :guard t))
  (and (integerp o)
       (or (and (<= 65 o) (<= o 90))
           (and (<= 48 o) (<= o 57))
           (eql o 45) (eql o 95))))

(defun fn-zc-alg-charsp (token)
  (declare (xargs :guard t))
  (if (consp token)
      (and (fn-zc-alg-charp (car token)) (fn-zc-alg-charsp (cdr token)))
    (null token)))

(defun fn-zc-algorithm-syntaxp (token)
  (declare (xargs :guard t))
  (and (consp token)
       (true-listp token)
       (<= (len token) 20)
       (fn-zc-alg-charsp token)))

; The algorithm a token names, as the session records it, or nil.
(defun fn-zc-algorithm (token)
  (declare (xargs :guard t))
  (if (equal token (fn-nntp-string-octets "DEFLATE")) :deflate nil))

; The answer to COMPRESS ARGS on a connection in compression state ZS,
; that may start a layer (MAYP): :active (502, a layer is active or owed),
; :syntax (501), :unsupported (503), :auth-required (480), or (:start ALG).
(defun fn-zc-decide (zs mayp args)
  (declare (xargs :guard t))
  (cond (zs :active)
        ((not (and (consp args) (null (cdr args))
                   (fn-zc-algorithm-syntaxp (car args))))
         :syntax)
        ((not (fn-zc-algorithm (car args))) :unsupported)
        ((not mayp) :auth-required)
        (t (list :start (fn-zc-algorithm (car args))))))

; -----------------------------------------------------------------------------
; The state.

(defun fn-zc-statep (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (true-listp x) (equal (len x) 2)
           (member-equal (car x) '(:owed :active))
           (equal (cadr x) :deflate))))

(defun fn-zc-owed (alg)
  (declare (xargs :guard t))
  (list :owed alg))

(defun fn-zc-owedp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :owed)))

(defun fn-zc-activep (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) :active)))

; The host installed the owed layer: it is active.
(defun fn-zc-established (x)
  (declare (xargs :guard t))
  (if (fn-zc-owedp x)
      (list :active (if (consp (cdr x)) (cadr x) nil))
    x))

(defthm fn-zc-statep-of-owed
  (implies (equal alg :deflate) (fn-zc-statep (fn-zc-owed alg))))

(defthm fn-zc-statep-of-established
  (implies (fn-zc-statep x) (fn-zc-statep (fn-zc-established x))))

(defthm fn-zc-established-is-active
  (implies (fn-zc-owedp x) (fn-zc-activep (fn-zc-established x))))

(defthm fn-zc-decide-starts-only-deflate
  (implies (equal (car (fn-zc-decide zs mayp args)) :start)
           (and (equal (cadr (fn-zc-decide zs mayp args)) :deflate)
                (null zs)
                mayp))
  :rule-classes nil)

; The effect the host installs the layer on, after the 206's CRLF.
(defun fn-zc-effect (alg)
  (declare (xargs :guard t))
  (list :compress alg))

(defun fn-zc-effectp (e)
  (declare (xargs :guard t))
  (and (true-listp e) (equal (len e) 2) (equal (car e) :compress)
       (equal (cadr e) :deflate)))

; -----------------------------------------------------------------------------
; The capability block (section 2.1 and 2.2.2).

(defun fn-zc-label-line ()
  (declare (xargs :guard t))
  (fn-nntp-string-octets "COMPRESS DEFLATE"))

(defun fn-zc-prefixp (p x)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp x) (equal (car p) (car x)) (fn-zc-prefixp (cdr p) (cdr x)))
    t))

; A label an active layer withdraws: STARTTLS, and AUTHINFO with or without
; arguments.
(defun fn-zc-withdrawn-linep (line)
  (declare (xargs :guard t))
  (or (equal line (fn-nntp-string-octets "STARTTLS"))
      (equal line (fn-nntp-string-octets "AUTHINFO"))
      (fn-zc-prefixp (fn-nntp-string-octets "AUTHINFO ") line)))

(defun fn-zc-drop-withdrawn (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (if (fn-zc-withdrawn-linep (car lines))
          (fn-zc-drop-withdrawn (cdr lines))
        (cons (car lines) (fn-zc-drop-withdrawn (cdr lines))))
    nil))

(defun fn-zc-capability-lines (lines zs mayp)
  ; LINES, the block without compression.  Active: without the withdrawn
  ; labels.  Owed: unchanged (no command is read while the layer is owed).
  ; None: with the COMPRESS label when this connection may start a layer.
  (declare (xargs :guard t))
  (cond ((fn-zc-activep zs) (fn-zc-drop-withdrawn lines))
        ((and (null zs) mayp) (append (true-list-fix lines) (list (fn-zc-label-line))))
        (t lines)))

(defthm fn-zc-drop-withdrawn-drops
  (implies (fn-zc-withdrawn-linep line)
           (not (member-equal line (fn-zc-drop-withdrawn lines)))))

(defthm fn-zc-drop-withdrawn-keeps-true-list
  (true-listp (fn-zc-drop-withdrawn lines)))

; The block stays response text (RFC 3977 section 3.1.1): what a filter
; drops is only fewer lines, and the label is one line of it.
(defthm fn-zc-drop-withdrawn-keeps-block-text
  (implies (fn-nntp-block-textp lines)
           (fn-nntp-block-textp (fn-zc-drop-withdrawn lines))))

(defthm fn-zc-label-line-is-text
  (fn-nntp-response-textp (fn-zc-label-line)))

(local
 (defthm fn-zc-block-text-of-append-one
   (implies (and (fn-nntp-block-textp lines) (fn-nntp-response-textp line))
            (fn-nntp-block-textp (append lines (list line))))))

(local
 (defthm fn-zc-block-text-true-list-fix
   (implies (fn-nntp-block-textp lines)
            (equal (true-list-fix lines) lines))))

(defthm fn-zc-capability-lines-are-block-text
  (implies (fn-nntp-block-textp lines)
           (fn-nntp-block-textp (fn-zc-capability-lines lines zs mayp)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-zc-label-line (fn-zc-label-line) fn-zc-drop-withdrawn))))

(defthm fn-zc-capability-lines-withdraw
  ; Section 2.2.2: once a layer is active, neither STARTTLS nor an AUTHINFO
  ; label, and no COMPRESS label is added.
  (implies (fn-zc-activep zs)
           (and (not (member-equal (fn-nntp-string-octets "STARTTLS")
                                   (fn-zc-capability-lines lines zs mayp)))
                (not (member-equal (fn-nntp-string-octets "AUTHINFO USER")
                                   (fn-zc-capability-lines lines zs mayp)))
                (equal (fn-zc-capability-lines lines zs mayp)
                       (fn-zc-drop-withdrawn lines)))))

; -----------------------------------------------------------------------------
; The outbound stream and what a layer costs.  zlib's deflate zs is
; (1 << (window-bits + 2)) + (1 << (mem-level + 9)) octets (zlib.h,
; deflateInit2), 48 KiB here, and a z_stream with its internal zs about
; 6 KiB; the inflater's buffers are the window, the table and one read of
; input and output (books/deflate-inflate.lisp fn-zin-buffer-sizes).

(defun fn-zc-deflate-params ()
  ; (LEVEL WINDOW-BITS MEM-LEVEL): level 5 (RFC 8054 section 4: "1-5 the
  ; rest of the time"), a 4 KiB window, memory level 6.
  (declare (xargs :guard t))
  (list 5 12 6))

(defun fn-zc-deflate-state-octets ()
  (declare (xargs :guard t))
  (let ((p (fn-zc-deflate-params)))
    (+ (expt 2 (+ (nfix (cadr p)) 2)) (expt 2 (+ (nfix (caddr p)) 9)) 8192)))

(defthm fn-zc-deflate-state-octets-value
  (equal (fn-zc-deflate-state-octets) 57344))

; -----------------------------------------------------------------------------
; The flush schedule and the output it may make (GPT-6's compression review,
; 2026-09-29 section 6: zlib's deflateBound bounds a stream ended by Z_FINISH
; or Z_NO_FLUSH, not interactive flushes; the schedule and the buffered
; output belong in the reservation).
;
; SCHEDULE.  Under a layer the host renders the reply plan in windows of at
; most `fn-zc-window-octets' plaintext octets (`fn-zc-render-window-size' of
; the plan's own window) and compresses each with exactly one Z_SYNC_FLUSH
; (host/native/mux.lisp fnn-mux-z-out, host/native/deflate.lisp
; fnn-zout-sync).  A sync flush empties zlib's input and leaves the stream
; byte aligned, so every call starts from no pending input and no pending
; bits: a call's output is one segment of the stream.
;
; OUTPUT.  For these parameters (window bits 12 at most hash bits 13) zlib's
; own bound on a segment of N octets is its "fixed" bound N + N/8 + N/256 +
; N/512 + 4 (deflate.c deflateBound); the sync flush adds an empty stored
; block (at most 7 pad bits and 4 octets) after the last block's end code,
; which the 16 octets here cover.  That is a statement about foreign code:
; the host gives zlib exactly this capacity and a segment that does not fit
; is a fault that closes the connection (fn_deflate_sync's -2), never a
; truncated stream.  books/connection-budget.lisp charges the buffer.

(defun fn-zc-window-octets ()
  (declare (xargs :guard t))
  4096)

(defun fn-zc-render-window-size (size)
  ; The plaintext window the host renders under a layer: the plan's own
  ; window (books/served-plan.lisp fn-splan-window-size), at most
  ; `fn-zc-window-octets'.
  (declare (xargs :guard t))
  (min (nfix size) (fn-zc-window-octets)))

(defun fn-zc-sync-output-octets (n)
  ; The compressed octets one sync-flushed window of N plaintext octets is
  ; given room for.
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (+ n (floor n 8) (floor n 256) (floor n 512) 4 16)))

(defthm fn-zc-render-window-size-bounds
  (and (<= (fn-zc-render-window-size size) (fn-zc-window-octets))
       (<= (fn-zc-render-window-size size) (nfix size))
       (implies (posp size) (posp (fn-zc-render-window-size size))))
  :rule-classes nil)

(defthm fn-zc-sync-output-octets-of-a-window
  (equal (fn-zc-sync-output-octets (fn-zc-window-octets)) 4652))
