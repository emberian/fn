; fn: the node's own web face, part 3 -- sessions and what each route does
; (lane web-native, PRF-339, WEB-005; 2026-09-28).
;
; THE DESIGN.  The web face is an NNTP client INSIDE the node whose every
; step is ACL2.  A browser session is bound to a LOGICAL READER CONNECTION
; of the owner: host/native/web-host.lisp opens it through the owner's own
; exposure admission (books/public-exposure.lisp fn-exp-open, with the
; browser's address decided by books/web-request.lisp
; fn-web-client-address), and every page feeds NNTP commands this book
; builds through the owner's served step on that connection (host/native/
; owner.lisp fnn-owner-handle-chunk, class :reader, no socket).  So:
;
;   * sign-in IS the node's AUTHINFO (RFC 4643): the reply decides; a wrong
;     password is a 481 the owner's exposure counts for this browser's
;     address, so login pacing is the node's `exposure-auth-failures'
;     policy, the same one NNTP readers meet, not a second one;
;   * an account is made by the node's own XREDEEM (PRF-164);
;   * every page a session reads is the reply the node gave that
;     connection -- authenticated as that login, with that login's
;     `account access' narrowing (books/group-access.lisp) -- and the
;     render functions (books/web-render.lisp) take only those reply
;     octets;
;   * a post is the authored article (D25) built here and fed through the
;     same served POST path an NNTP reader uses; a removal is the same
;     cancel control article, which the node authorizes (SEC-006).
;
; What this book keeps, NODE-LOCAL and never in the log: the session table
; (the token the host drew from the OS CSPRNG, the connection it is bound
; to, the login, the CSRF token, the last use).  No password is ever kept:
; it is decoded from the form into the command octets of the one request
; that sends it.
;
; THE HOST PROTOCOL.  One HTTP request is a short conversation:
;
;   (fn-web-step CONFIG WSTATE FLOW EVENT fn-web-in fn-web-out)
;       -> (mv ACTION WSTATE' fn-web-out)
;
; EVENT is (:begin REQUEST BODY-START BODY-END NOW NONCE1 NONCE2 TLS
; FAMILY ADDRESS) for the parsed request, then the outcome of the host's
; last action: (:opened CID), (:reply), (:closed) or (:gone).  ACTION is
;
;   (:respond CODE FIELDS)       the page is fn-web-out; write
;                                fn-web-response-head and the page, close
;   (:open FAMILY ADDRESS PROTECTED FLOW)
;                                open a logical reader connection for this
;                                address (fn-owner-exposure-open); when
;                                PROTECTED, mark it (fn-owner-tls-
;                                established); answer (:opened CID-or-nil)
;   (:send CID START FLOW)       feed fn-web-out [START, len) to CID; the
;                                whole reply into fn-web-in; answer (:reply),
;                                or (:gone) when the owner forgot CID
;   (:close CID FLOW)            close CID (fn-owner-close, the exposure
;                                release); answer (:closed)
;
; The host keeps FLOW and WSTATE opaque.
;
; KEYSTONES (PRF-339):
;   fn-web-session-route-needs-its-session: a route whose capability is
;     :session or :csrf, begun without a live session for the request's
;     token, sends nothing to any connection and answers 303 to the
;     sign-in page;
;   fn-web-session-sends-only-to-its-connection: when it has one, every
;     connection it sends to is that session's own;
;   fn-web-sessions-bound-by-281: a session is added to the table only by
;     a reply to AUTHINFO whose code is 281, and bound to the connection
;     that reply came from, for the login that command named;
;   fn-wss-body-cannot-end-the-article: the posted body, however the
;     form's text is made, never contains the line "." that would end the
;     article (RFC 3977 3.1.1), so a body cannot smuggle commands.

(in-package "ACL2")
(include-book "web-render")
(include-book "web-health")
(include-book "def-loop")

; -----------------------------------------------------------------------------
; Base64 (RFC 4648 4 and 5): tokens use the URL alphabet unpadded; the
; RFC 2047 encoded-word the standard one.

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

(defun fn-wss-b64-char (v urlp)
  (declare (xargs :guard t))
  (let ((v (if (and (natp v) (< v 64)) v 0)))
    (cond ((< v 26) (+ 65 v))
          ((< v 52) (+ 97 (- v 26)))
          ((< v 62) (+ 48 (- v 52)))
          ((equal v 62) (if urlp 45 43))
          (t (if urlp 95 47)))))

(defun fn-wss-octet (x)
  (declare (xargs :guard t))
  (if (and (natp x) (< x 256)) x 0))

(defun fn-wss-b64 (xs urlp padp)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (let* ((a (fn-wss-octet (car xs)))
             (b (if (consp (cdr xs)) (fn-wss-octet (cadr xs)) 0))
             (c (if (and (consp (cdr xs)) (consp (cddr xs))) (fn-wss-octet (caddr xs)) 0))
             (n (+ (* a 65536) (* b 256) c))
             (c1 (fn-wss-b64-char (floor n 262144) urlp))
             (c2 (fn-wss-b64-char (mod (floor n 4096) 64) urlp))
             (c3 (fn-wss-b64-char (mod (floor n 64) 64) urlp))
             (c4 (fn-wss-b64-char (mod n 64) urlp)))
        (cond ((not (consp (cdr xs)))
               (append (list c1 c2) (if padp (list 61 61) nil)))
              ((not (consp (cddr xs)))
               (append (list c1 c2 c3) (if padp (list 61) nil)))
              (t (list* c1 c2 c3 c4 (fn-wss-b64 (cdddr xs) urlp padp)))))
    nil)))

; A token: the base64url of a host-drawn CSPRNG nonce.
(defun fn-wss-token (nonce)
  (declare (xargs :guard t))
  (fn-wss-b64 nonce t nil))

; -----------------------------------------------------------------------------
; Values a command may carry.  Every one is checked before it is written
; into a command line: no CR, LF, NUL or SP can reach the wire from a form.

(defun fn-wss-all-vchar (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-wrq-vcharp (car xs)) (fn-wss-all-vchar (cdr xs)))
    (null xs)))

(defun fn-wss-argp (xs max)
  ; 1..MAX printable ASCII octets, no SP (an NNTP argument, RFC 3977 3.1).
  (declare (xargs :guard (natp max)))
  (and (consp xs) (fn-wrq-shortp xs max) (fn-wss-all-vchar xs)))

; -----------------------------------------------------------------------------
; The posted body.  The form's text, decoded, becomes the article's body
; lines: CR LF, a lone CR and a lone LF each end a line (CR LF on the
; wire), a line that opens with "." gets a second (RFC 3977 3.1.1), and the
; last line is ended.  The model:

(defun fn-wss-stuff (xs bol pcr)
  ; BOL: the next octet begins a line.  PCR: a CR is pending.
  (declare (xargs :guard t
                  :measure (+ (* 2 (len xs)) (if pcr 1 0))))
  (if (consp xs)
      (let ((o (car xs)))
        (cond (pcr (if (equal o 10)
                       (list* 13 10 (fn-wss-stuff (cdr xs) t nil))
                     (list* 13 10 (fn-wss-stuff xs t nil))))
              ((equal o 13) (fn-wss-stuff (cdr xs) bol t))
              ((equal o 10) (list* 13 10 (fn-wss-stuff (cdr xs) t nil)))
              ((and bol (equal o 46)) (list* 46 46 (fn-wss-stuff (cdr xs) nil nil)))
              (t (cons o (fn-wss-stuff (cdr xs) nil nil)))))
    (if (or pcr (not bol)) (list 13 10) nil)))

; What the wire needs of a body: no line is "." (every line that opens with
; "." opens with ".."), and it is empty or ends with LF.
(defun fn-wss-no-dot-line (xs bol)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (and bol (equal (car xs) 46)
                     (not (and (consp (cdr xs)) (equal (cadr xs) 46)))))
           (fn-wss-no-dot-line (cdr xs) (equal (car xs) 10)))
    t))

(defun fn-wss-ends-lf (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs)) (fn-wss-ends-lf (cdr xs)) (equal (car xs) 10))
    t))

(defthm fn-wss-no-dot-line-of-stuff
  (fn-wss-no-dot-line (fn-wss-stuff xs bol pcr) bol))

(defthm fn-wss-stuff-consp
  (implies (or (consp xs) pcr (not bol))
           (consp (fn-wss-stuff xs bol pcr))))

(defthm fn-wss-ends-lf-cons
  (equal (fn-wss-ends-lf (cons a rest))
         (if (consp rest) (fn-wss-ends-lf rest) (equal a 10))))

(defthm fn-wss-ends-lf-of-stuff
  (fn-wss-ends-lf (fn-wss-stuff xs bol pcr)))

(defthm fn-wss-body-cannot-end-the-article
  ; KEYSTONE (PRF-339): whatever the form's text, the body lines the face
  ; writes contain no line "." and end at a line end, so the ".\r\n" that
  ; follows them is the article's one terminator.
  (let ((body (fn-wss-stuff (fn-wrq-urldecode text) t nil)))
    (and (fn-wss-no-dot-line body t)
         (fn-wss-ends-lf body)))
  :hints (("Goal" :in-theory (disable fn-wss-stuff fn-wrq-urldecode fn-wss-no-dot-line
                                      fn-wss-ends-lf))))

; The executable: the form's encoded text read in place from fn-web-in
; [I, E), decoded and stuffed into fn-web-out in one pass (D27: the body is
; never a list).  `fn-wss-emit-body-is-stuff' is its model.

(defun fn-wss-decode-at (i e fn-web-in)
  ; (OCTET . NEXT): the form octet at I, decoded ("+" is SP, "%" HEX HEX).
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp i) (natp e) (< i e) (<= e (fn-octets-len fn-web-in)))))
  (let ((o (fn-octets-get i fn-web-in)))
    (cond ((equal o 43) (cons 32 (1+ i)))
          ((and (equal o 37) (< (+ 2 i) e)
                (fn-ot-hex-value (fn-octets-get (+ 1 i) fn-web-in))
                (fn-ot-hex-value (fn-octets-get (+ 2 i) fn-web-in)))
           (cons (+ (* 16 (fn-ot-hex-value (fn-octets-get (+ 1 i) fn-web-in)))
                    (fn-ot-hex-value (fn-octets-get (+ 2 i) fn-web-in)))
                 (+ 3 i)))
          (t (cons o (1+ i))))))

(defthm fn-wss-decode-at-next
  (implies (and (natp i) (natp e) (< i e))
           (and (< i (cdr (fn-wss-decode-at i e fn-web-in)))
                (<= (cdr (fn-wss-decode-at i e fn-web-in)) e)))
  :rule-classes :linear)

(defthm fn-wss-decode-at-next-natp
  (implies (natp i) (natp (cdr (fn-wss-decode-at i e fn-web-in))))
  :rule-classes :type-prescription)

(defthm fn-wss-decode-at-octet
  (implies (and (fn-cbor-octet-listp fn-web-in) (natp i) (< i (len fn-web-in)))
           (fn-cbor-octetp (car (fn-wss-decode-at i e fn-web-in)))))

; One decoded octet with no CR pending: what it writes and the state after.
(defun fn-wss-step-octets (o bol)
  (declare (xargs :guard t))
  (cond ((equal o 13) nil)
        ((equal o 10) (list 13 10))
        ((and bol (equal o 46)) (list 46 46))
        (t (list o))))

(defun fn-wss-step-bol (o bol)
  (declare (xargs :guard t))
  (cond ((equal o 13) bol)
        ((equal o 10) t)
        (t nil)))

(defun fn-wss-step-pcr (o)
  (declare (xargs :guard t))
  (equal o 13))

(defthm fn-wss-stuff-cons-no-pcr
  (equal (fn-wss-stuff (cons o rest) bol nil)
         (append (fn-wss-step-octets o bol)
                 (fn-wss-stuff rest (fn-wss-step-bol o bol) (fn-wss-step-pcr o)))))

(defthm fn-wss-stuff-cons-pcr
  (implies pcr
   (equal (fn-wss-stuff (cons o rest) bol pcr)
         (if (equal o 10)
             (list* 13 10 (fn-wss-stuff rest t nil))
           (list* 13 10 (fn-wss-stuff (cons o rest) t nil))))))

(defthm fn-wss-stuff-atom
  (implies (not (consp xs))
           (equal (fn-wss-stuff xs bol pcr) (if (or pcr (not bol)) (list 13 10) nil))))

(defthm fn-wss-step-octets-octets
  (implies (fn-cbor-octetp o) (fn-cbor-octet-listp (fn-wss-step-octets o bol))))

(in-theory (disable fn-wss-step-octets fn-wss-step-bol fn-wss-step-pcr))

(defun fn-wss-emit-body (i e bol pcr fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (natp i) (natp e) (<= e (fn-octets-len fn-web-in)))
                  :measure (nfix (- e i))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-wss-decode-at)))))
  (if (or (not (natp i)) (not (natp e)) (<= e i))
      (if (or pcr (not bol)) (fn-octets-append-list '(13 10) fn-web-out) fn-web-out)
    (let* ((d (fn-wss-decode-at i e fn-web-in))
           (o (car d)))
      (if (and pcr (equal o 10))
          (let ((fn-web-out (fn-octets-append-list '(13 10) fn-web-out)))
            (fn-wss-emit-body (cdr d) e t nil fn-web-in fn-web-out))
        (let* ((fn-web-out (if pcr (fn-octets-append-list '(13 10) fn-web-out) fn-web-out))
               (b (if pcr t bol))
               (fn-web-out (fn-octets-append-list (fn-wss-step-octets o b) fn-web-out)))
          (fn-wss-emit-body (cdr d) e (fn-wss-step-bol o b) (fn-wss-step-pcr o)
                            fn-web-in fn-web-out))))))

(local
 (defthm fn-wss-slice-open
   (implies (and (natp s) (natp e) (< s e))
            (equal (fn-oct-slice-list s e fn-octets)
                   (cons (nth s fn-octets) (fn-oct-slice-list (1+ s) e fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-wss-slice-empty
   (implies (or (not (natp s)) (not (natp e)) (<= e s))
            (equal (fn-oct-slice-list s e fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(defthm fn-wss-urldecode-slice-step
  (implies (and (natp i) (natp e) (< i e))
           (equal (fn-wrq-urldecode (fn-oct-slice-list i e fn-web-in))
                  (cons (car (fn-wss-decode-at i e fn-web-in))
                        (fn-wrq-urldecode
                         (fn-oct-slice-list (cdr (fn-wss-decode-at i e fn-web-in)) e fn-web-in)))))
  :hints (("Goal" :expand ((:free (x y) (fn-wrq-urldecode (cons x y)))
                           (fn-oct-slice-list (+ 1 i) e fn-web-in)
                           (fn-oct-slice-list (+ 2 i) e fn-web-in))
           :in-theory (disable fn-oct-slice-list-is-take-nthcdr fn-ot-hex-value))))

(local
 (defthm fn-wss-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-wss-emit-body-is-stuff
  ; The in-place body writer is the model over the decoded form text.
  (implies (true-listp fn-web-out)
           (equal (fn-wss-emit-body i e bol pcr fn-web-in fn-web-out)
                  (append fn-web-out
                          (fn-wss-stuff (fn-wrq-urldecode (fn-oct-slice-list i e fn-web-in))
                                        bol pcr))))
  :hints (("Goal" :induct (fn-wss-emit-body i e bol pcr fn-web-in fn-web-out)
           :in-theory (disable fn-wss-decode-at fn-oct-slice-list-is-take-nthcdr
                               fn-wrq-urldecode fn-ot-hex-value fn-wss-stuff
                               fn-wss-slice-open))))

; -----------------------------------------------------------------------------
; The node's replies, read in place from fn-web-in (the host renders the
; served step's plan there).  RFC 3977 3.1: a status line, and after the
; codes that carry one, a multi-line block ended by a line ".".

(defun fn-wss-multi-line-code-p (code)
  (declare (xargs :guard t))
  (and (member code '(100 101 215 220 221 222 224 225 230 231)) t))

(defun fn-wss-code-at (i fn-web-in)
  ; The status code opening the line at I, or nil.
  (declare (xargs :stobjs fn-web-in :guard (natp i)))
  (let ((n (fn-octets-len fn-web-in)))
    (and (natp i) (< (+ 3 i) n)
         (fn-ot-digitp (fn-octets-get i fn-web-in))
         (fn-ot-digitp (fn-octets-get (+ 1 i) fn-web-in))
         (fn-ot-digitp (fn-octets-get (+ 2 i) fn-web-in))
         (member (fn-octets-get (+ 3 i) fn-web-in) '(32 13))
         (+ (* 100 (- (fn-octets-get i fn-web-in) 48))
            (* 10 (- (fn-octets-get (+ 1 i) fn-web-in) 48))
            (- (fn-octets-get (+ 2 i) fn-web-in) 48)))))

(defthm fn-wss-line-end-strict
  (implies (and (natp j) (< j (len fn-web-in)))
           (< j (fn-oct-line-end j fn-web-in)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-oct-line-end))))

(defun fn-wss-dot-line-at (j fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard (natp j)))
  (and (natp j) (< (+ 2 j) (fn-octets-len fn-web-in))
       (equal (fn-octets-get j fn-web-in) 46)
       (equal (fn-octets-get (+ 1 j) fn-web-in) 13)
       (equal (fn-octets-get (+ 2 j) fn-web-in) 10)))

(defun fn-wss-block-end (j fn-web-in)
  ; The start of the block's terminating line, or the buffer's end.
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (<= j (fn-octets-len fn-web-in)))
                  :measure (nfix (- (fn-octets-len fn-web-in) j))))
  (cond ((or (not (natp j)) (>= j (fn-octets-len fn-web-in))) (fn-octets-len fn-web-in))
        ((fn-wss-dot-line-at j fn-web-in) j)
        (t (fn-wss-block-end (fn-oct-line-end j fn-web-in) fn-web-in))))

(defthm fn-wss-block-end-bounds
  (implies (and (natp j) (<= j (len fn-web-in)))
           (and (<= j (fn-wss-block-end j fn-web-in))
                (<= (fn-wss-block-end j fn-web-in) (len fn-web-in))))
  :rule-classes ((:linear :trigger-terms ((fn-wss-block-end j fn-web-in)))))

(defthm fn-wss-block-end-natp
  (natp (fn-wss-block-end j fn-web-in))
  :rule-classes :type-prescription)

; One reply at I: (CODE START LINE-END BLOCK-START BLOCK-END NEXT).  CODE
; nil when the line is not a status line; no block unless the code carries
; one.  Every index is within the buffer (`fn-wss-reply-bounds').
(defun fn-wss-reply (i fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp i) (<= i (fn-octets-len fn-web-in)))))
  (let* ((n (fn-octets-len fn-web-in))
         (i (min (nfix i) n))
         (code (fn-wss-code-at i fn-web-in))
         (le (fn-oct-line-end i fn-web-in)))
    (if (fn-wss-multi-line-code-p code)
        (let ((be (fn-wss-block-end le fn-web-in)))
          (list code i le le be (min n (+ 3 be))))
      (list code i le le le le))))

(defun fn-wss-reply-code (r) (declare (xargs :guard t)) (fn-wrq-nth 0 r))
(defun fn-wss-reply-start (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 1 r)))
(defun fn-wss-reply-le (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 2 r)))
(defun fn-wss-reply-bs (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 3 r)))
(defun fn-wss-reply-be (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 4 r)))
(defun fn-wss-reply-next (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 5 r)))

(defthm fn-wss-reply-bounds
  (implies (natp i)
           (let ((r (fn-wss-reply i fn-web-in)))
             (and (<= (fn-wss-reply-start r) (fn-wss-reply-le r))
                  (<= (fn-wss-reply-le r) (len fn-web-in))
                  (<= (fn-wss-reply-bs r) (fn-wss-reply-be r))
                  (<= (fn-wss-reply-be r) (len fn-web-in))
                  (<= (fn-wss-reply-next r) (len fn-web-in)))))
  :rule-classes
  ((:linear :corollary (implies (natp i) (<= (fn-wss-reply-start (fn-wss-reply i fn-web-in))
                                            (fn-wss-reply-le (fn-wss-reply i fn-web-in)))))
   (:linear :corollary (implies (natp i) (<= (fn-wss-reply-le (fn-wss-reply i fn-web-in))
                                            (len fn-web-in))))
   (:linear :corollary (implies (natp i) (<= (fn-wss-reply-bs (fn-wss-reply i fn-web-in))
                                            (fn-wss-reply-be (fn-wss-reply i fn-web-in)))))
   (:linear :corollary (implies (natp i) (<= (fn-wss-reply-be (fn-wss-reply i fn-web-in))
                                            (len fn-web-in))))
   (:linear :corollary (implies (natp i) (<= (fn-wss-reply-next (fn-wss-reply i fn-web-in))
                                            (len fn-web-in)))))
  :hints (("Goal" :in-theory (disable fn-oct-line-end fn-wss-block-end))))

(in-theory (disable fn-wss-reply fn-wss-reply-start fn-wss-reply-le fn-wss-reply-bs
                    fn-wss-reply-be fn-wss-reply-next))

(defun fn-wss-slice (s e fn-web-in)
  ; A short field's octets (a group name, a number, a Message-ID).
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp s) (natp e) (<= e (fn-octets-len fn-web-in)))))
  (if (<= s e) (fn-oct-slice-list s e fn-web-in) nil))

; The status line's text without its CR LF: shown when the node refuses.
(defun fn-wss-status-text (i fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp i) (<= i (fn-octets-len fn-web-in)))))
  (let* ((r (fn-wss-reply i fn-web-in))
         (s (fn-wss-reply-start r))
         (le (fn-wss-reply-le r))
         (e (if (<= (+ 2 s) le) (- le 2) le)))
    (fn-wss-slice s e fn-web-in)))

; Fields of the line [A, B) separated by SEP: spans (S . E).
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-wss-split-loop (a b start sep fn-web-in acc)
  (declare (xargs :stobjs fn-web-in :measure (nfix (- b a)) :guard (and (and (natp a) (natp b) (natp start) (<= b (fn-octets-len fn-web-in))) (true-listp acc)) :verify-guards nil))
  (cond ((or (not (natp a)) (not (natp b)) (<= b a))
         (revappend acc (list (cons (nfix start) (nfix b)))))
        ((equal (fn-octets-get a fn-web-in) sep)
         (fn-wss-split-loop (1+ a)
                            b
                            (1+ a)
                            sep
                            fn-web-in
                            (cons (cons (nfix start) a) acc)))
        (t (fn-wss-split-loop (1+ a) b start sep fn-web-in acc))))

(defun fn-wss-split (a b start sep fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in
                  :guard (and (natp a) (natp b) (natp start) (<= b (fn-octets-len fn-web-in)))
                  :measure (nfix (- b a))))
  (mbe :logic
       (cond ((or (not (natp a)) (not (natp b)) (<= b a)) (list (cons (nfix start) (nfix b))))
             ((equal (fn-octets-get a fn-web-in) sep)
              (cons (cons (nfix start) a) (fn-wss-split (1+ a) b (1+ a) sep fn-web-in)))
             (t (fn-wss-split (1+ a) b start sep fn-web-in)))
       :exec (fn-wss-split-loop a b start sep fn-web-in nil)))

(local
 (defthm fn-wss-split-loop-is-revappend
   (equal (fn-wss-split-loop a b start sep fn-web-in acc)
          (revappend acc (fn-wss-split a b start sep fn-web-in)))
   :hints (("Goal" :induct (fn-wss-split-loop a b start sep fn-web-in acc)
                   :in-theory (union-theories '(fn-wss-split-loop fn-wss-split revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wss-split-loop)

(verify-guards fn-wss-split
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-wss-split)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-wss-split-loop-is-revappend (acc nil))))))


(defun fn-wss-spanp (x n)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (natp (cdr x)) (<= (car x) (cdr x)) (<= (cdr x) (nfix n))))

(defun fn-wss-spans-p (xs n)
  (declare (xargs :guard t))
  (if (consp xs) (and (fn-wss-spanp (car xs) n) (fn-wss-spans-p (cdr xs) n)) (null xs)))

(defthm fn-wss-split-spans
  (implies (and (natp a) (natp b) (natp start) (<= start a) (<= a b) (<= b n) (natp n))
           (fn-wss-spans-p (fn-wss-split a b start sep fn-web-in) n)))

(defun fn-wss-span-slice (span fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (if (and (fn-wss-spanp span (fn-octets-len fn-web-in)))
      (fn-oct-slice-list (car span) (cdr span) fn-web-in)
    nil))

(defun fn-wss-content-end (j le fn-web-in)
  ; A line [J, LE) without its CR LF.
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (natp le) (<= le (fn-octets-len fn-web-in)))))
  (if (and (<= (+ 2 j) le) (equal (fn-octets-get (- le 2) fn-web-in) 13)
           (equal (fn-octets-get (- le 1) fn-web-in) 10))
      (- le 2)
    le))

; LIST ACTIVE (RFC 3977 7.6.3): "group high low status" per line.  A row
; for the page: (NAME COUNT READ-ONLY-P).
(defun fn-wss-active-row (fields fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (let* ((name (fn-wss-span-slice (fn-wrq-nth 0 fields) fn-web-in))
         (high (fn-ot-decimal-parse (fn-wss-span-slice (fn-wrq-nth 1 fields) fn-web-in) nil))
         (low (fn-ot-decimal-parse (fn-wss-span-slice (fn-wrq-nth 2 fields) fn-web-in) nil))
         (status (fn-wss-span-slice (fn-wrq-nth 3 fields) fn-web-in))
         (count (if (and high low (<= low high) (< 0 high)) (+ 1 (- high low)) 0)))
    (list name (fn-ot-decimal-octets count) (equal status (list 110)))))

; Executes by a loop (lane depth-debt, PRF-919): one row per newsgroup of
; the reply, as many as the operator's group table holds (D27: data, not a
; bound).  The loop conses the rows reversed and rev-onto's them back.
(defun fn-wss-active-rows-loop (j be fn-web-in acc)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (natp be) (<= be (fn-octets-len fn-web-in)))
                  :measure (nfix (- be j))))
  (if (or (not (natp j)) (not (natp be)) (>= j be) (>= j (fn-octets-len fn-web-in)))
      (fn-ag-rev-onto acc nil)
    (let* ((le (min be (fn-oct-line-end j fn-web-in)))
           (ce (fn-wss-content-end j le fn-web-in)))
      (fn-wss-active-rows-loop
       le be fn-web-in
       (cons (fn-wss-active-row (fn-wss-split j ce j 32 fn-web-in) fn-web-in) acc)))))

(defun fn-wss-active-rows (j be fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (natp be) (<= be (fn-octets-len fn-web-in)))
                  :measure (nfix (- be j))
                  :verify-guards nil))
  (mbe :logic
       (if (or (not (natp j)) (not (natp be)) (>= j be) (>= j (fn-octets-len fn-web-in)))
           nil
         (let* ((le (min be (fn-oct-line-end j fn-web-in)))
                (ce (fn-wss-content-end j le fn-web-in)))
           (cons (fn-wss-active-row (fn-wss-split j ce j 32 fn-web-in) fn-web-in)
                 (fn-wss-active-rows le be fn-web-in))))
       :exec (fn-wss-active-rows-loop j be fn-web-in nil)))

(defthm fn-wss-active-rows-loop-is-rev-onto
  (equal (fn-wss-active-rows-loop j be fn-web-in acc)
         (fn-ag-rev-onto acc (fn-wss-active-rows j be fn-web-in)))
  :hints (("Goal" :induct (fn-wss-active-rows-loop j be fn-web-in acc)
                  :in-theory (e/d (fn-ag-rev-onto)
                                  (fn-wss-active-row fn-wss-split fn-wss-content-end
                                   fn-oct-line-end)))))

(verify-guards fn-wss-active-rows
  :hints (("Goal" :in-theory (e/d (fn-ag-rev-onto)
                                  (fn-wss-active-row fn-wss-split fn-wss-content-end
                                   fn-oct-line-end)))))

; OVER (RFC 3977 8.3): "number TAB subject TAB from TAB date TAB ..." per
; line.  A row for the page: (NUMBER SUBJECT FROM DATE), the last three
; spans.  Newest first (the order the page shows).
(defun fn-wss-over-rows (j be acc fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (natp be) (<= be (fn-octets-len fn-web-in)))
                  :measure (nfix (- be j))))
  (if (or (not (natp j)) (not (natp be)) (>= j be) (>= j (fn-octets-len fn-web-in)))
      acc
    (let* ((le (min be (fn-oct-line-end j fn-web-in)))
           (ce (fn-wss-content-end j le fn-web-in))
           (f (fn-wss-split j ce j 9 fn-web-in)))
      (fn-wss-over-rows le be
                        (cons (list (fn-wss-span-slice (fn-wrq-nth 0 f) fn-web-in)
                                    (fn-wrq-nth 1 f) (fn-wrq-nth 2 f) (fn-wrq-nth 3 f))
                              acc)
                        fn-web-in))))

; ARTICLE (RFC 3977 6.2.1; RFC 5536): the header lines until the empty
; line, then the body.  The page shows five fields; each is the span of the
; field's value, continuation lines included, found by its name
; case-insensitively (RFC 5322 1.2.2).
(defconst *fn-wss-shown-fields*
  (list (fn-wrq-oct "subject") (fn-wrq-oct "from") (fn-wrq-oct "date")
        (fn-wrq-oct "newsgroups") (fn-wrq-oct "message-id")))

(defun fn-wss-field-index (name fields k)
  (declare (xargs :guard (natp k)))
  (if (consp fields)
      (if (equal name (car fields)) k (fn-wss-field-index name (cdr fields) (1+ k)))
    nil))

(defun fn-wss-colon (a b fn-web-in)
  ; The first ":" in [A, B), or B.
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp a) (natp b) (<= b (fn-octets-len fn-web-in)))
                  :measure (nfix (- b a))))
  (cond ((or (not (natp a)) (not (natp b)) (<= b a)) (nfix b))
        ((equal (fn-octets-get a fn-web-in) 58) a)
        (t (fn-wss-colon (1+ a) b fn-web-in))))

(defthm fn-wss-colon-bounds
  (implies (and (natp a) (natp b) (<= a b))
           (and (<= a (fn-wss-colon a b fn-web-in)) (<= (fn-wss-colon a b fn-web-in) b)))
  :rule-classes ((:linear :trigger-terms ((fn-wss-colon a b fn-web-in)))))

(defun fn-wss-skip-ws (a b fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp a) (natp b) (<= b (fn-octets-len fn-web-in)))
                  :measure (nfix (- b a))))
  (cond ((or (not (natp a)) (not (natp b)) (<= b a)) (nfix b))
        ((member (fn-octets-get a fn-web-in) '(32 9)) (fn-wss-skip-ws (1+ a) b fn-web-in))
        (t a)))

(defthm fn-wss-skip-ws-bounds
  (implies (and (natp a) (natp b) (<= a b))
           (and (<= a (fn-wss-skip-ws a b fn-web-in)) (<= (fn-wss-skip-ws a b fn-web-in) b)))
  :rule-classes ((:linear :trigger-terms ((fn-wss-skip-ws a b fn-web-in)))))

(defun fn-wss-continued (k be fn-web-in)
  ; Past the continuation lines (opening with SP or HT) that start at K.
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp k) (natp be) (<= be (fn-octets-len fn-web-in)))
                  :measure (nfix (- be k))))
  (if (and (natp k) (natp be) (< k be) (< k (fn-octets-len fn-web-in))
           (member (fn-octets-get k fn-web-in) '(32 9)))
      (fn-wss-continued (min be (fn-oct-line-end k fn-web-in)) be fn-web-in)
    (nfix k)))

(defthm fn-wss-continued-bounds
  (implies (and (natp k) (natp be) (<= k be))
           (and (<= k (fn-wss-continued k be fn-web-in)) (<= (fn-wss-continued k be fn-web-in) be)))
  :rule-classes ((:linear :trigger-terms ((fn-wss-continued k be fn-web-in)))))

(defun fn-wss-put-span (k span found)
  ; FOUND with slot K set to SPAN unless already set.
  (declare (xargs :guard (natp k)))
  (if (consp found)
      (if (zp k)
          (cons (or (car found) span) (cdr found))
        (cons (car found) (fn-wss-put-span (1- k) span (cdr found))))
    nil))

; (FOUND . BODY-START): the five shown fields' spans (nil where absent)
; and where the body begins.
(defthm fn-wss-field-index-type
  (implies (natp k)
           (or (null (fn-wss-field-index name fields k))
               (natp (fn-wss-field-index name fields k))))
  :rule-classes :type-prescription)

(defthm fn-wss-content-end-bounds
  (implies (and (natp j) (natp le))
           (<= (fn-wss-content-end j le fn-web-in) le))
  :rule-classes :linear)

(defthm fn-wss-content-end-lower
  (implies (and (natp j) (natp le) (<= j le))
           (<= j (fn-wss-content-end j le fn-web-in)))
  :rule-classes :linear)

(defthm fn-wss-content-end-natp
  (implies (and (natp j) (natp le))
           (natp (fn-wss-content-end j le fn-web-in)))
  :rule-classes :type-prescription)

(defun fn-wss-headers (j be found fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp j) (natp be) (<= be (fn-octets-len fn-web-in)))
                  :measure (nfix (- be j))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-wss-content-end fn-wss-colon fn-wss-slice
                                                            fn-wrq-rev-down fn-wrq-rev fn-wss-field-index
                                                            fn-wss-put-span fn-wrq-shortp)))))
  (cond ((or (not (natp j)) (not (natp be)) (>= j be) (>= j (fn-octets-len fn-web-in)))
         (cons found (nfix be)))
        ((and (< (1+ j) be) (equal (fn-octets-get j fn-web-in) 13)
              (equal (fn-octets-get (1+ j) fn-web-in) 10))
         (cons found (+ 2 j)))
        (t (let* ((le (min be (fn-oct-line-end j fn-web-in)))
                  (k (fn-wss-continued le be fn-web-in))
                  (fe (fn-wss-content-end j k fn-web-in))
                  (colon (fn-wss-colon j fe fn-web-in))
                  (name (fn-wrq-rev-down (fn-wrq-rev (fn-wss-slice j colon fn-web-in) nil) nil))
                  (slot (and (fn-wrq-shortp name 16)
                             (fn-wss-field-index name *fn-wss-shown-fields* 0)))
                  (vs (fn-wss-skip-ws (min fe (1+ colon)) fe fn-web-in)))
             (fn-wss-headers k be
                             (if slot (fn-wss-put-span slot (cons vs fe) found) found)
                             fn-web-in)))))

; Whether the span holds "<LOGIN@" (the From this face writes).
(defun fn-wss-prefix-at (i pat fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard (natp i) :measure (len pat)))
  (if (consp pat)
      (and (natp i) (< i (fn-octets-len fn-web-in))
           (equal (fn-octets-get i fn-web-in) (car pat))
           (fn-wss-prefix-at (1+ i) (cdr pat) fn-web-in))
    t))

(defun fn-wss-span-has (i e pat fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp i) (natp e))
                  :measure (nfix (- e i))))
  (if (or (not (natp i)) (not (natp e)) (<= e i))
      nil
    (or (and (<= (+ i (len pat)) e) (fn-wss-prefix-at i pat fn-web-in))
        (fn-wss-span-has (1+ i) e pat fn-web-in))))

; -----------------------------------------------------------------------------
; The configuration (from the node's profile; host/web-host.lisp reads it
; through ACL2): the site's name, the mail domain of the From a post
; carries, whether a TLS proxy on this machine fronts the face, the idle
; seconds a session lives, and how many sessions the face keeps.

(defun fn-web-config (site domain proxied idle max-sessions)
  (declare (xargs :guard t))
  (list :web-config site domain proxied idle max-sessions))

(defun fn-wss-cfg-site (c) (declare (xargs :guard t)) (fn-wr-octets-only (fn-wrq-nth 1 c)))
(defun fn-wss-cfg-domain (c) (declare (xargs :guard t)) (fn-wr-octets-only (fn-wrq-nth 2 c)))
(defun fn-wss-cfg-proxied (c) (declare (xargs :guard t)) (and (fn-wrq-nth 3 c) t))
(defun fn-wss-cfg-idle (c)
  (declare (xargs :guard t))
  (let ((v (fn-wrq-nth 4 c))) (if (posp v) v 43200)))
(defun fn-wss-cfg-max (c)
  (declare (xargs :guard t))
  (let ((v (fn-wrq-nth 5 c))) (if (posp v) v 64)))

; -----------------------------------------------------------------------------
; THE SESSION TABLE (node-local; never logged).  A session is
; (TOKEN CID LOGIN CSRF USED): the token the browser holds, the owner
; connection AUTHINFO authenticated, the login it named, the CSRF token of
; its forms, and the time of its last request.

(defun fn-wss-session (token cid login csrf used)
  (declare (xargs :guard t))
  (list token cid login csrf used))

(defun fn-wss-s-token (s) (declare (xargs :guard t)) (fn-wrq-nth 0 s))
(defun fn-wss-s-cid (s) (declare (xargs :guard t)) (fn-wrq-nth 1 s))
(defun fn-wss-s-login (s) (declare (xargs :guard t)) (fn-wr-octets-only (fn-wrq-nth 2 s)))
(defun fn-wss-s-csrf (s) (declare (xargs :guard t)) (fn-wr-octets-only (fn-wrq-nth 3 s)))
(defun fn-wss-s-used (s) (declare (xargs :guard t)) (nfix (fn-wrq-nth 4 s)))

(defun fn-wss-livep (s now idle)
  (declare (xargs :guard t))
  (<= (nfix now) (+ (fn-wss-s-used s) (nfix idle))))

; The live session whose token is TOKEN (a token is never empty).
(defun fn-wss-find (token sessions now idle)
  (declare (xargs :guard t))
  (if (consp sessions)
      (if (and (consp token) (equal (fn-wss-s-token (car sessions)) token)
               (fn-wss-livep (car sessions) now idle))
          (car sessions)
        (fn-wss-find token (cdr sessions) now idle))
    nil))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-wss-drop (token sessions)
  :shape :map :over sessions :keep-order :skip-first
  :keep (equal (fn-wss-s-token (car sessions)) token)
  :body (car sessions))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-wss-touch-loop (token sessions now acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp sessions)
      (if (equal (fn-wss-s-token (car sessions)) token)
          (fn-wss-touch-loop token
                             (cdr sessions)
                             now
                             (cons (fn-wss-session token
                                                   (fn-wss-s-cid (car sessions))
                                                   (fn-wss-s-login (car sessions))
                                                   (fn-wss-s-csrf (car sessions))
                                                   now)
                                   acc))
        (fn-wss-touch-loop token (cdr sessions) now (cons (car sessions) acc)))
    (revappend acc nil)))

(defun fn-wss-touch (token sessions now)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp sessions)
           (if (equal (fn-wss-s-token (car sessions)) token)
               (cons (fn-wss-session token (fn-wss-s-cid (car sessions)) (fn-wss-s-login (car sessions))
                                     (fn-wss-s-csrf (car sessions)) now)
                     (fn-wss-touch token (cdr sessions) now))
             (cons (car sessions) (fn-wss-touch token (cdr sessions) now)))
         nil)
       :exec (fn-wss-touch-loop token sessions now nil)))

(local
 (defthm fn-wss-touch-loop-is-revappend
   (equal (fn-wss-touch-loop token sessions now acc)
          (revappend acc (fn-wss-touch token sessions now)))
   :hints (("Goal" :induct (fn-wss-touch-loop token sessions now acc)
                   :in-theory (union-theories '(fn-wss-touch-loop fn-wss-touch revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wss-touch-loop)

(verify-guards fn-wss-touch
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-wss-touch)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-wss-touch-loop-is-revappend (acc nil))))))


; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-wss-expired (sessions now idle)
  :shape :map :keep-order :skip-first
  :keep (fn-wss-livep (car sessions) now idle)
  :body (car sessions))


(defun fn-wss-live (sessions now idle)
  (declare (xargs :guard t))
  (if (consp sessions)
      (if (fn-wss-livep (car sessions) now idle)
          (cons (car sessions) (fn-wss-live (cdr sessions) now idle))
        (fn-wss-live (cdr sessions) now idle))
    nil))

; -----------------------------------------------------------------------------
; A request's context: what every route reads.

(defun fn-wss-ctx (request bs be now n1 n2 tls family address session theme config)
  (declare (xargs :guard t))
  (let* ((client (fn-web-client-address family address (fn-wss-cfg-proxied config) request))
         (loopback (fn-wrq-loopbackp family address)))
    (list request (nfix bs) (nfix be) (nfix now) n1 n2
          ; the browser's address the owner's exposure sees
          client
          ; PROTECTED: the channel the password crosses is TLS, or it does
          ; not leave this machine (a loopback peer: the proxy or a tunnel)
          (and (or tls loopback) t)
          ; SECURE: cookies are Secure and HSTS is sent (TLS here, or the
          ; profile's TLS proxy on this machine)
          (and (or tls (and (fn-wss-cfg-proxied config) loopback)) t)
          session theme)))

(defun fn-wss-c-request (c) (declare (xargs :guard t)) (fn-wrq-nth 0 c))
(defun fn-wss-c-bs (c) (declare (xargs :guard t)) (nfix (fn-wrq-nth 1 c)))
(defun fn-wss-c-be (c) (declare (xargs :guard t)) (nfix (fn-wrq-nth 2 c)))
(defun fn-wss-c-now (c) (declare (xargs :guard t)) (nfix (fn-wrq-nth 3 c)))
(defun fn-wss-c-n1 (c) (declare (xargs :guard t)) (fn-wrq-nth 4 c))
(defun fn-wss-c-n2 (c) (declare (xargs :guard t)) (fn-wrq-nth 5 c))
(defun fn-wss-c-client (c) (declare (xargs :guard t)) (fn-wrq-nth 6 c))
(defun fn-wss-c-protected (c) (declare (xargs :guard t)) (fn-wrq-nth 7 c))
(defun fn-wss-c-secure (c) (declare (xargs :guard t)) (fn-wrq-nth 8 c))
(defun fn-wss-c-session (c) (declare (xargs :guard t)) (fn-wrq-nth 9 c))
(defun fn-wss-c-theme (c) (declare (xargs :guard t)) (fn-wrq-nth 10 c))

(defun fn-wss-theme-of (request)
  (declare (xargs :guard t))
  (let ((v (fn-web-cookie-get (fn-wrq-oct "fnr_theme") (fn-web-req-cookie request))))
    (cond ((equal v (fn-wrq-oct "light")) :light)
          ((equal v (fn-wrq-oct "dark")) :dark)
          (t :auto))))

; -----------------------------------------------------------------------------
; Responses.

(defun fn-wss-cookie (name value max-age secure)
  ; "NAME=VALUE; Path=/; HttpOnly; SameSite=Lax[; Secure][; Max-Age=N]".
  (declare (xargs :guard t))
  (cons (fn-wrq-oct "Set-Cookie")
        (append (fn-wr-octets-only name) (list 61) (fn-wr-octets-only value)
                (fn-wrq-oct "; Path=/; HttpOnly; SameSite=Lax")
                (if secure (fn-wrq-oct "; Secure") nil)
                (if (natp max-age) (append (fn-wrq-oct "; Max-Age=") (fn-ot-decimal-octets max-age)) nil))))

(defconst *fn-wss-html-fields*
  (list (cons (fn-wrq-oct "Content-Type") (fn-wrq-oct "text/html; charset=utf-8"))
        (cons (fn-wrq-oct "Cache-Control") (fn-wrq-oct "no-store"))))

(defun fn-wss-bodyp (ctx)
  ; HEAD answers the head only (RFC 9110 9.3.2).
  (declare (xargs :guard t))
  (not (equal (fn-web-req-method (fn-wss-c-request ctx)) :head)))

; A page: MAIN framed, emitted into fn-web-out.  The segments are checked
; before they are written (the spans are the reply's, within fn-web-in); a
; list that is not is answered 500 with a fixed page.
(defun fn-wss-page (code fields title main ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard (true-listp main)))
  (let* ((session (fn-wss-c-session ctx))
         (segs (fn-wr-frame title (fn-wss-cfg-site config) (fn-wss-c-theme ctx)
                            (and session (fn-wss-s-login session))
                            (and session (fn-wss-s-csrf session))
                            main))
         (fn-web-out (fn-octets-clear fn-web-out)))
    (if (and (fn-wr-segsp segs) (fn-wr-segs-within segs (fn-octets-len fn-web-in)))
        (if (equal (fn-wrq-nth 6 config) :page-plan)
            (mv (list :respond code (append (fn-wrq-true fields) *fn-wss-html-fields*)
                      (fn-wss-bodyp ctx) :page-plan segs) fn-web-out)
          (let ((fn-web-out (fn-wr-emit segs fn-web-in fn-web-out)))
            (mv (list :respond code (append (fn-wrq-true fields) *fn-wss-html-fields*)
                      (fn-wss-bodyp ctx))
                fn-web-out)))
      (let ((fn-web-out (fn-octets-append-list (fn-wrq-oct "<!doctype html><title>error</title><p>The page could not be made.</p>") fn-web-out)))
        (mv (list :respond 500 *fn-wss-html-fields* (fn-wss-bodyp ctx)) fn-web-out)))))

(defun fn-wss-redirect (location fields ctx fn-web-out)
  (declare (xargs :stobjs fn-web-out :guard t))
  (let ((fn-web-out (fn-octets-clear fn-web-out)))
    (mv (list :respond 303
              (cons (cons (fn-wrq-oct "Location") (fn-wr-octets-only location))
                    (append (fn-wrq-true fields)
                            (list (cons (fn-wrq-oct "Cache-Control") (fn-wrq-oct "no-store")))))
              (fn-wss-bodyp ctx))
        fn-web-out)))

(defun fn-wss-outcome (code kind title message detail back ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (fn-wss-page code nil title (fn-wr-outcome-main kind title message detail back)
               ctx config fn-web-in fn-web-out))

; -----------------------------------------------------------------------------
; Reading the request's form and query.

(defun fn-wss-form (name ctx fn-web-in)
  ; The decoded body field NAME, or nil when absent.
  (declare (xargs :stobjs fn-web-in :guard t))
  (let ((bs (fn-wss-c-bs ctx)) (be (fn-wss-c-be ctx)))
    (if (and (<= bs be) (<= be (fn-octets-len fn-web-in)))
        (let ((v (fn-web-body-get name bs be fn-web-in)))
          (if (equal v :absent) nil v))
      nil)))

(defun fn-wss-query (name ctx)
  (declare (xargs :guard t))
  (let ((v (fn-wrq-form-get name (fn-web-req-query (fn-wss-c-request ctx)))))
    (if (equal v :absent) nil v)))

(defun fn-wss-cookie-val (name ctx)
  (declare (xargs :guard t))
  (let ((v (fn-web-cookie-get name (fn-web-req-cookie (fn-wss-c-request ctx)))))
    (if (equal v :absent) nil v)))

(defun fn-wss-b64url-octets-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (or (fn-ot-digitp (car x)) (fn-ot-alphap (car x)) (member (car x) '(45 95)))
           (fn-wss-b64url-octets-p (cdr x)))
    (null x)))

(defun fn-wss-tokenp (x)
  ; A token this face issued: base64url octets, 16..64 of them.
  (declare (xargs :guard t))
  (and (fn-wss-argp x 64) (not (fn-wrq-shortp x 15)) (fn-wss-b64url-octets-p x)))

(defun fn-wss-same-site (request)
  ; A POST from this site's own pages: Sec-Fetch-Site (when sent) is
  ; same-origin or none, and Origin (when sent and not "null") names the
  ; Host the request was sent to.
  (declare (xargs :guard t))
  (let ((fetch (fn-web-req-fetch-site request))
        (origin (fn-web-req-origin request))
        (host (fn-web-req-host request)))
    (and (or (not fetch) (equal fetch (fn-wrq-oct "same-origin")) (equal fetch (fn-wrq-oct "none")))
         (or (not origin) (equal origin (fn-wrq-oct "null"))
             (and (fn-wrq-prefix-ci (fn-wrq-oct "http://") origin)
                  (equal (fn-wrq-drop 7 origin) host))
             (and (fn-wrq-prefix-ci (fn-wrq-oct "https://") origin)
                  (equal (fn-wrq-drop 8 origin) host))))))

; -----------------------------------------------------------------------------
; Values a command carries, checked.

(defun fn-wss-loginp (x) (declare (xargs :guard t)) (fn-wss-argp x 64))
(defun fn-wss-passwordp (x) (declare (xargs :guard t)) (fn-wss-argp x 256))
(defun fn-wss-codep (x) (declare (xargs :guard t)) (fn-wss-argp x 128))
(defun fn-wss-groupp (x) (declare (xargs :guard t)) (fn-wss-argp x 497))
(defun fn-wss-numberp (x)
  (declare (xargs :guard t))
  (and (fn-wrq-shortp x 10) (fn-ot-decimal-parse x nil) (< 0 (fn-ot-decimal-parse x nil)) t))
(defun fn-wss-msgidp (x)
  (declare (xargs :guard t))
  (and (fn-wss-argp x 250) (equal (car x) 60) (equal (car (last x)) 62)))

(defun fn-wss-has (o xs)
  (declare (xargs :guard t))
  (if (consp xs) (or (equal (car xs) o) (fn-wss-has o (cdr xs))) nil))

(defun fn-wss-next-ok (x)
  ; Where to go after signing in: a path on this site, never another's.
  (declare (xargs :guard t))
  (if (and (fn-wss-argp x 1024) (equal (car x) 47)
           (not (and (consp (cdr x)) (equal (cadr x) 47)))
           (not (fn-wss-has 92 x)))
      x
    (list 47)))

(defun fn-wss-cmd (words)
  ; WORDS joined by SP, then CR LF.
  (declare (xargs :guard t))
  (append (fn-wrq-join words (list 32)) (list 13 10)))

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(def-loop fn-wss-one-line (xs)
  :shape :map
  :body (if (member (car xs) '(13 10 9 0)) 32 (fn-wss-octet (car xs))))


(defun fn-wss-asciip (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (integerp (car xs)) (<= 32 (car xs)) (<= (car xs) 126) (fn-wss-asciip (cdr xs)))
    t))

; RFC 2047 encoded-words for a non-ASCII Subject: at most 45 octets each
; (60 base64 characters), never splitting a UTF-8 sequence.
(defun fn-wss-utf8-back (acc xs)
  (declare (xargs :guard t))
  (if (and (consp acc) (consp (cdr acc)) (consp xs)
           (integerp (car xs)) (<= 128 (car xs)) (< (car xs) 192))
      (fn-wss-utf8-back (cdr acc) (cons (car acc) xs))
    (cons (fn-wrq-rev acc nil) xs)))

(defun fn-wss-utf8-take (xs n acc)
  ; (CHUNK . REST): up to N octets, ending before a continuation octet.
  (declare (xargs :guard (natp n)))
  (if (and (consp xs) (not (zp n)))
      (fn-wss-utf8-take (cdr xs) (1- n) (cons (car xs) acc))
    (if (and (consp xs) (integerp (car xs)) (<= 128 (car xs)) (< (car xs) 192)
             (consp acc) (consp (cdr acc)))
        ; back off to the sequence's start
        (fn-wss-utf8-back acc xs)
      (cons (fn-wrq-rev acc nil) xs))))

; fn-wss-ew executes by a loop (lane depth-debt, PRF-919): FUEL is the
; subject's length, one encoded word per 45 octets of it.  ACC holds the
; octets so far, reversed; the :logic is the recursion, unchanged.
(local
 (defthm fn-wss-ew-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto a acc) b)
          (fn-ag-rev-onto acc (append a b)))
   :hints (("Goal" :induct (fn-ag-rev-onto a acc)))))

(defun fn-wss-ew-loop (xs fuel acc)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (atom xs))
      (fn-ag-rev-onto acc nil)
    (let* ((cut (fn-wss-utf8-take xs 45 nil))
           (acc (fn-ag-rev-onto (fn-wrq-oct "?=")
                                (fn-ag-rev-onto (fn-wss-b64 (car cut) nil t)
                                                (fn-ag-rev-onto (fn-wrq-oct "=?UTF-8?B?") acc)))))
      (if (consp (cdr cut))
          (fn-wss-ew-loop (cdr cut) (1- fuel) (fn-ag-rev-onto (list 13 10 32) acc))
        (fn-ag-rev-onto acc nil)))))

(defun fn-wss-ew (xs fuel)
  ; The encoded-words of XS, one per line after the first.
  (declare (xargs :guard (natp fuel) :measure (nfix fuel) :verify-guards nil))
  (mbe :logic (if (or (zp fuel) (atom xs))
                  nil
                (let ((cut (fn-wss-utf8-take xs 45 nil)))
                  (append (fn-wrq-oct "=?UTF-8?B?") (fn-wss-b64 (car cut) nil t) (fn-wrq-oct "?=")
                          (if (consp (cdr cut))
                              (append (list 13 10 32) (fn-wss-ew (cdr cut) (1- fuel)))
                            nil))))
       :exec (fn-wss-ew-loop xs fuel nil)))

(defthm fn-wss-ew-loop-is-rev-onto
  (equal (fn-wss-ew-loop xs fuel acc)
         (fn-ag-rev-onto acc (fn-wss-ew xs fuel)))
  :hints (("Goal" :induct (fn-wss-ew-loop xs fuel acc)
                  :in-theory (union-theories
                              '(fn-wss-ew-loop fn-wss-ew fn-wss-ew-rev-onto-of-rev-onto atom)
                              (theory 'minimal-theory)))))

(defthm fn-wss-ew-loop-nil
  (equal (fn-wss-ew-loop xs fuel nil) (fn-wss-ew xs fuel))
  :hints (("Goal" :in-theory (union-theories '(fn-wss-ew-loop-is-rev-onto fn-ag-rev-onto)
                                             (theory 'minimal-theory)))))

(verify-guards fn-wss-ew
  :hints (("Goal" :expand ((fn-wss-ew xs fuel))
                  :in-theory (disable (:definition fn-wss-ew) (:definition fn-wss-ew-loop)
                                      fn-wss-ew-loop-is-rev-onto
                                      fn-wss-utf8-take fn-wss-b64))))

(defun fn-wss-subject-field (subject)
  (declare (xargs :guard t))
  (let ((s (fn-wss-one-line subject)))
    (append (fn-wrq-oct "Subject: ")
            (if (fn-wss-asciip s) s (fn-wss-ew s (len s)))
            (list 13 10))))

(defun fn-wss-from-field (login domain)
  (declare (xargs :guard t))
  (append (fn-wrq-oct "From: ") (fn-wr-octets-only login) (fn-wrq-oct " <")
          (fn-wr-octets-only login) (list 64)
          (if (consp domain) (fn-wr-octets-only domain) (fn-wrq-oct "invalid"))
          (fn-wrq-oct ">") (list 13 10)))

; The post: "POST" CR LF (six octets), then the authored article (D25),
; written straight into fn-web-out; the body decoded in place from the
; form's `body' field [BS, BE) (fn-wss-emit-body-is-stuff).
(defun fn-wss-post-head (login domain group subject)
  (declare (xargs :guard t))
  (fn-wr-octets-only
   (append (fn-wrq-oct "POST") (list 13 10)
           (fn-wss-from-field login domain)
           (fn-wrq-oct "Newsgroups: ") (fn-wr-octets-only group) (list 13 10)
           (fn-wss-subject-field subject)
           (fn-wrq-oct "MIME-Version: 1.0") (list 13 10)
           (fn-wrq-oct "Content-Type: text/plain; charset=utf-8") (list 13 10)
           (fn-wrq-oct "Content-Transfer-Encoding: 8bit") (list 13 10)
           (list 13 10))))

(defthm fn-wss-octets-only-octets
  (fn-cbor-octet-listp (fn-wr-octets-only x)))

(defthm fn-wss-post-head-octets
  (fn-cbor-octet-listp (fn-wss-post-head login domain group subject))
  :hints (("Goal" :in-theory (disable fn-wr-octets-only))))

(in-theory (disable fn-wss-post-head fn-wr-octets-only))

(defun fn-wss-write-post (login domain group subject bs be fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (natp bs) (natp be) (<= be (fn-octets-len fn-web-in)))))
  (let* ((fn-web-out (fn-octets-clear fn-web-out))
         (fn-web-out (fn-octets-append-list (fn-wss-post-head login domain group subject)
                                            fn-web-out))
         (fn-web-out (fn-wss-emit-body bs be t nil fn-web-in fn-web-out)))
    (fn-octets-append-list (list 46 13 10) fn-web-out)))

; The removal: the cancel control article (RFC 5537 5.3); the node decides
; whether this login may withdraw the target (SEC-006).
(defun fn-wss-cancel-octets (login domain group msgid)
  (declare (xargs :guard t))
  (fn-wr-octets-only
   (append (fn-wrq-oct "POST") (list 13 10)
           (fn-wss-from-field login domain)
           (fn-wrq-oct "Newsgroups: ") (fn-wr-octets-only group) (list 13 10)
           (fn-wrq-oct "Subject: cmsg cancel ") (fn-wr-octets-only msgid) (list 13 10)
           (fn-wrq-oct "Control: cancel ") (fn-wr-octets-only msgid) (list 13 10)
           (list 13 10)
           (fn-wrq-oct "cancel") (list 13 10)
           (list 46 13 10))))

(defun fn-wss-write (octets fn-web-out)
  (declare (xargs :stobjs fn-web-out :guard t))
  (let ((fn-web-out (fn-octets-clear fn-web-out)))
    (fn-octets-append-list (fn-wr-octets-only octets) fn-web-out)))

; -----------------------------------------------------------------------------
; THE FLOWS.  A flow is (ROUTE STAGE CTX DATA); every step answers
; (mv ACTION SESSIONS fn-web-out).

(defun fn-wss-flow (route stage ctx data)
  (declare (xargs :guard t))
  (list route stage ctx data))

(defun fn-wss-f-route (f) (declare (xargs :guard t)) (fn-wrq-nth 0 f))
(defun fn-wss-f-stage (f) (declare (xargs :guard t)) (fn-wrq-nth 1 f))
(defun fn-wss-f-ctx (f) (declare (xargs :guard t)) (fn-wrq-nth 2 f))
(defun fn-wss-f-data (f) (declare (xargs :guard t)) (fn-wrq-nth 3 f))

(defun fn-wss-pre (ctx)
  ; The sign-in forms' token: the browser's, or a new one.
  (declare (xargs :guard t))
  (let ((have (fn-wss-cookie-val (fn-wrq-oct "fnr_pre") ctx)))
    (if (fn-wss-tokenp have) have (fn-wss-token (fn-wss-c-n1 ctx)))))

(defun fn-wss-signin-page (code message user next ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((pre (fn-wss-pre ctx)))
    (fn-wss-page code (list (fn-wss-cookie (fn-wrq-oct "fnr_pre") pre 3600 (fn-wss-c-secure ctx)))
                 (fn-wrq-oct "Sign in")
                 (fn-wr-signin-main message pre (fn-wss-next-ok next) user)
                 ctx config fn-web-in fn-web-out)))

(defun fn-wss-redeem-page (code message user ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((pre (fn-wss-pre ctx)))
    (fn-wss-page code (list (fn-wss-cookie (fn-wrq-oct "fnr_pre") pre 3600 (fn-wss-c-secure ctx)))
                 (fn-wrq-oct "Make your account")
                 (fn-wr-redeem-main message pre nil user)
                 ctx config fn-web-in fn-web-out)))

(defconst *fn-wss-msg-mismatch* (fn-wrq-oct "That name and password don't match."))
(defconst *fn-wss-msg-busy*
  (fn-wrq-oct "Too many tries from here just now. Please wait a few minutes and try again."))
(defconst *fn-wss-msg-protect*
  (fn-wrq-oct "Signing in needs a protected connection: open this site with https://"))
(defconst *fn-wss-msg-unreachable*
  (fn-wrq-oct "We can't reach the server right now. Please try again in a minute."))

(defun fn-wss-reply-codes (fn-web-in)
  ; The codes of the first two replies in fn-web-in, and the second's text.
  (declare (xargs :stobjs fn-web-in :guard t))
  (let* ((r1 (fn-wss-reply 0 fn-web-in))
         (n1 (min (fn-wss-reply-next r1) (fn-octets-len fn-web-in)))
         (r2 (fn-wss-reply n1 fn-web-in)))
    (list (fn-wss-reply-code r1) (fn-wss-reply-code r2)
          (fn-wss-status-text n1 fn-web-in) (fn-wss-status-text 0 fn-web-in))))

(defun fn-wss-new-session (token cid login csrf now sessions)
  ; SESSIONS with the new one first.
  (declare (xargs :guard t))
  (cons (fn-wss-session token cid login csrf now) sessions))

; The AUTHINFO pair of a sign-in (RFC 4643 2.3): both lines in one feed.
(defun fn-wss-authinfo (login password)
  (declare (xargs :guard t))
  (append (fn-wss-cmd (list (fn-wrq-oct "AUTHINFO") (fn-wrq-oct "USER") login))
          (fn-wss-cmd (list (fn-wrq-oct "AUTHINFO") (fn-wrq-oct "PASS") password))))

; The end of an AUTHINFO exchange on CID, whose replies are in fn-web-in:
; the session, or the connection closed and the reason kept for the page.
(defun fn-wss-after-authinfo (route login next cid config sessions ctx fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((codes (fn-wss-reply-codes fn-web-in))
         (c2 (fn-wrq-nth 1 codes)))
    (cond ((and (equal c2 281) (< (len sessions) (fn-wss-cfg-max config)))
           (let* ((token (fn-wss-token (fn-wss-c-n1 ctx)))
                  (csrf (fn-wss-token (fn-wss-c-n2 ctx)))
                  (sessions (fn-wss-new-session token cid login csrf (fn-wss-c-now ctx) sessions)))
             (mv-let (action fn-web-out)
               (fn-wss-redirect (fn-wss-next-ok next)
                                (list (fn-wss-cookie (fn-wrq-oct "fnr_session") token nil
                                                     (fn-wss-c-secure ctx))
                                      (fn-wss-cookie (fn-wrq-oct "fnr_pre") nil 0
                                                     (fn-wss-c-secure ctx)))
                                ctx fn-web-out)
               (mv action sessions fn-web-out))))
          (t (mv (list :close cid
                       (fn-wss-flow route :closed ctx
                                    (list (cond ((equal c2 281) :full)
                                                ((or (equal (fn-wrq-nth 0 codes) 483) (equal c2 483)) :protect)
                                                ((equal c2 481) :mismatch)
                                                (t :other))
                                          login (fn-wrq-nth 2 codes))))
                 sessions fn-web-out)))))

(defun fn-wss-signin-refused (why user detail ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (case why
    (:mismatch (fn-wss-signin-page 401 *fn-wss-msg-mismatch* user nil ctx config fn-web-in fn-web-out))
    (:protect (fn-wss-signin-page 403 *fn-wss-msg-protect* user nil ctx config fn-web-in fn-web-out))
    (:busy (fn-wss-signin-page 429 *fn-wss-msg-busy* user nil ctx config fn-web-in fn-web-out))
    (:full (fn-wss-signin-page 503 (fn-wrq-oct "Too many people are signed in just now. Please try again later.")
                               user nil ctx config fn-web-in fn-web-out))
    (otherwise (fn-wss-signin-page 503 (append *fn-wss-msg-unreachable* (list 32)
                                               (fn-wr-octets-only detail))
                                   user nil ctx config fn-web-in fn-web-out))))

(defun fn-wss-car (x) (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-wss-cdr (x) (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(in-theory (disable fn-wss-page fn-wss-redirect fn-wss-outcome fn-wss-form fn-wss-write
                    fn-wss-authinfo fn-wss-cmd fn-wss-signin-page fn-wss-redeem-page
                    fn-wss-reply-codes fn-wss-after-authinfo fn-wss-signin-refused
                    fn-wss-query fn-wss-cookie-val fn-wss-cookie fn-wss-token fn-wss-pre
                    fn-wss-flow fn-wss-f-route fn-wss-f-stage fn-wss-f-ctx fn-wss-f-data
                    fn-wss-loginp fn-wss-passwordp fn-wss-codep fn-wss-groupp fn-wss-numberp
                    fn-wss-msgidp fn-wss-next-ok fn-wss-ctx fn-wss-reply fn-wss-status-text
                    fn-wss-cancel-octets fn-wss-write-post fn-wss-c-client fn-wss-c-protected
                    fn-wss-c-session fn-wss-c-secure fn-wss-c-now fn-wss-c-n1 fn-wss-c-n2
                    fn-wss-c-request fn-wss-c-bs fn-wss-c-be fn-wss-c-theme fn-wss-bodyp
                    fn-wss-s-cid fn-wss-s-login fn-wss-s-csrf fn-wss-s-token fn-wss-s-used
                    fn-wss-session fn-wss-new-session fn-wss-find fn-wss-drop fn-wss-touch
                    fn-wss-same-site fn-wss-tokenp))

(defthm fn-wss-page-shape
  (and (true-listp (mv-nth 0 (fn-wss-page code fields title main ctx config fn-web-in fn-web-out))))
  :hints (("Goal" :in-theory (enable fn-wss-page))))

; --- Sign in (POST /signin): the node's AUTHINFO decides.

(defun fn-wss-m-signin (sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((user (fn-wss-form (fn-wrq-oct "user") ctx fn-web-in))
        (password (fn-wss-form (fn-wrq-oct "password") ctx fn-web-in))
        (next (fn-wss-form (fn-wrq-oct "next") ctx fn-web-in))
        (client (fn-wss-c-client ctx)))
    (if (and (fn-wss-loginp user) (fn-wss-passwordp password))
        (mv (list :open (fn-wss-car client) (fn-wss-cdr client) (fn-wss-c-protected ctx)
                  (fn-wss-flow :signin :opened ctx (list user next)))
            sessions fn-web-out)
      (mv-let (a fn-web-out)
        (fn-wss-signin-page 401 *fn-wss-msg-mismatch* user next ctx config fn-web-in fn-web-out)
        (mv a sessions fn-web-out)))))

(defun fn-wss-k-signin (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((ctx (fn-wss-f-ctx flow)) (data (fn-wss-f-data flow))
         (user (fn-wrq-nth 0 data)) (next (fn-wrq-nth 1 data)))
    (case (fn-wss-f-stage flow)
      (:opened
       (let ((cid (fn-wss-car (fn-wss-cdr event))))
         (if (and (equal (fn-wss-car event) :opened) (natp cid))
             ; The password is read from the request once more (fn-web-in
             ; is untouched by an open) straight into the command octets.
             (let ((fn-web-out (fn-wss-write
                                (fn-wss-authinfo user (fn-wss-form (fn-wrq-oct "password") ctx fn-web-in))
                                fn-web-out)))
               (mv (list :send cid 0 (fn-octets-len fn-web-out)
                         (fn-wss-flow :signin :sent ctx (list user next cid)))
                   sessions fn-web-out))
           (mv-let (a fn-web-out)
             (fn-wss-signin-refused :busy user nil ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))))
      (:sent
       (if (equal (fn-wss-car event) :reply)
           (fn-wss-after-authinfo :signin user next (fn-wrq-nth 2 data) config sessions ctx
                                  fn-web-in fn-web-out)
         (mv-let (a fn-web-out)
           (fn-wss-signin-refused :other user nil ctx config fn-web-in fn-web-out)
           (mv a sessions fn-web-out))))
      (otherwise
       (mv-let (a fn-web-out)
         (fn-wss-signin-refused (fn-wrq-nth 0 data) (fn-wrq-nth 1 data) (fn-wrq-nth 2 data)
                                ctx config fn-web-in fn-web-out)
         (mv a sessions fn-web-out))))))

; --- Make an account (POST /redeem): the node's XREDEEM, then AUTHINFO on
; a new connection (its 281 says so).  The password is held in the flow,
; in memory, for this one request.

(defun fn-wss-m-redeem (sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((code (fn-wss-form (fn-wrq-oct "code") ctx fn-web-in))
        (user (fn-wss-form (fn-wrq-oct "user") ctx fn-web-in))
        (password (fn-wss-form (fn-wrq-oct "password") ctx fn-web-in))
        (again (fn-wss-form (fn-wrq-oct "again") ctx fn-web-in))
        (client (fn-wss-c-client ctx)))
    (cond ((not (and (fn-wss-codep code) (fn-wss-loginp user) (fn-wss-passwordp password)))
           (mv-let (a fn-web-out)
             (fn-wss-redeem-page 400 (fn-wrq-oct "Please check the code, your name and your password (no spaces).")
                                 user ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))
          ((not (equal password again))
           (mv-let (a fn-web-out)
             (fn-wss-redeem-page 400 (fn-wrq-oct "The two passwords are not the same.")
                                 user ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))
          (t (mv (list :open (fn-wss-car client) (fn-wss-cdr client) (fn-wss-c-protected ctx)
                       (fn-wss-flow :redeem :opened ctx (list code user password)))
                 sessions fn-web-out)))))

(defun fn-wss-redeem-refused (why user ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (case why
    (:code (fn-wss-redeem-page 403 (fn-wrq-oct "That invitation code didn't work: it may be used already, or mistyped, or the name may be taken.")
                               user ctx config fn-web-in fn-web-out))
    (:protect (fn-wss-redeem-page 403 *fn-wss-msg-protect* user ctx config fn-web-in fn-web-out))
    (:busy (fn-wss-redeem-page 429 *fn-wss-msg-busy* user ctx config fn-web-in fn-web-out))
    (otherwise (fn-wss-redeem-page 503 *fn-wss-msg-unreachable* user ctx config fn-web-in fn-web-out))))

(defun fn-wss-k-redeem (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((ctx (fn-wss-f-ctx flow)) (data (fn-wss-f-data flow))
         (code (fn-wrq-nth 0 data)) (user (fn-wrq-nth 1 data)) (password (fn-wrq-nth 2 data))
         (client (fn-wss-c-client ctx)))
    (case (fn-wss-f-stage flow)
      (:opened
       (let ((cid (fn-wss-car (fn-wss-cdr event))))
         (if (and (equal (fn-wss-car event) :opened) (natp cid))
             (let ((fn-web-out (fn-wss-write
                                (append (fn-wss-cmd (list (fn-wrq-oct "XREDEEM") code user))
                                        (fn-wss-cmd (list (fn-wrq-oct "XREDEEM") (fn-wrq-oct "PASS") password)))
                                fn-web-out)))
               (mv (list :send cid 0 (fn-octets-len fn-web-out)
                         (fn-wss-flow :redeem :redeeming ctx (list code user password cid)))
                   sessions fn-web-out))
           (mv-let (a fn-web-out) (fn-wss-redeem-refused :busy user ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))))
      (:redeeming
       (let* ((codes (fn-wss-reply-codes fn-web-in))
              (c1 (fn-wrq-nth 0 codes)) (c2 (fn-wrq-nth 1 codes))
              (cid (fn-wrq-nth 3 data)))
         (if (equal (fn-wss-car event) :reply)
             (mv (list :close cid
                       (fn-wss-flow :redeem :redeemed ctx
                                    (list code user password
                                          (cond ((equal c2 281) :bound)
                                                ((or (equal c1 483) (equal c2 483)) :protect)
                                                ((or (equal c1 482) (equal c2 482)) :code)
                                                (t :other)))))
                 sessions fn-web-out)
           (mv-let (a fn-web-out) (fn-wss-redeem-refused :other user ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))))
      (:redeemed
       (if (equal (fn-wrq-nth 3 data) :bound)
           (mv (list :open (fn-wss-car client) (fn-wss-cdr client) (fn-wss-c-protected ctx)
                     ; DATA keeps its layout (CODE LOGIN PASSWORD ...) through :signin.
                     (fn-wss-flow :redeem :signin ctx (list code user password)))
               sessions fn-web-out)
         (mv-let (a fn-web-out) (fn-wss-redeem-refused (fn-wrq-nth 3 data) user ctx config
                                                       fn-web-in fn-web-out)
           (mv a sessions fn-web-out))))
      (:signin
       (let ((cid (fn-wss-car (fn-wss-cdr event))))
         (if (and (equal (fn-wss-car event) :opened) (natp cid))
             (let ((fn-web-out (fn-wss-write (fn-wss-authinfo user password) fn-web-out)))
               (mv (list :send cid 0 (fn-octets-len fn-web-out)
                         (fn-wss-flow :redeem :sent ctx (list user cid)))
                   sessions fn-web-out))
           (mv-let (a fn-web-out) (fn-wss-signin-refused :busy user nil ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out)))))
      (:sent
       (if (equal (fn-wss-car event) :reply)
           ; At this stage DATA is (LOGIN CID).
           (fn-wss-after-authinfo :redeem (fn-wrq-nth 0 data) (list 47) (fn-wrq-nth 1 data)
                                  config sessions ctx
                                  fn-web-in fn-web-out)
         (mv-let (a fn-web-out) (fn-wss-signin-refused :other user nil ctx config fn-web-in fn-web-out)
           (mv a sessions fn-web-out))))
      (otherwise
       (mv-let (a fn-web-out)
         (fn-wss-signin-refused (fn-wrq-nth 0 data) (fn-wrq-nth 1 data) (fn-wrq-nth 2 data)
                                ctx config fn-web-in fn-web-out)
         (mv a sessions fn-web-out))))))

; --- The session's own connection.  Every page below that reads the node
; sends only to (fn-wss-s-cid SESSION), the connection AUTHINFO bound it to.

(defun fn-wss-send-session (route stage data octets session ctx sessions fn-web-out)
  (declare (xargs :stobjs fn-web-out :guard t))
  (let ((fn-web-out (fn-wss-write octets fn-web-out)))
    (mv (list :send (fn-wss-s-cid session) 0 (fn-octets-len fn-web-out)
              (fn-wss-flow route stage ctx data))
        sessions fn-web-out)))

(defun fn-wss-slices (spans fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard t))
  (if (consp spans)
      (cons (fn-wss-span-slice (car spans) fn-web-in) (fn-wss-slices (cdr spans) fn-web-in))
    nil))

(defun fn-wss-status-fields (fn-web-in)
  ; The first status line's space-separated fields, as octet lists.
  (declare (xargs :stobjs fn-web-in :guard t))
  (let* ((r (fn-wss-reply 0 fn-web-in))
         (s (fn-wss-reply-start r))
         (le (min (fn-wss-reply-le r) (fn-octets-len fn-web-in)))
         (ce (fn-wss-content-end (min s le) le fn-web-in)))
    (fn-wss-slices (fn-wss-split (min s ce) ce (min s ce) 32 fn-web-in) fn-web-in)))

(defconst *fn-wss-window* 100)

(defun fn-wss-trouble (code title message ctx config sessions fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (mv-let (a fn-web-out)
    ; The node's own line, when fn-web-in holds a reply; while it still
    ; holds the request (whose first line is never a status line: its
    ; method is GET, HEAD or POST) nothing of the request is echoed.
    (fn-wss-outcome code :no title message
                    (and (fn-wss-reply-code (fn-wss-reply 0 fn-web-in))
                         (fn-wss-status-text 0 fn-web-in))
                    nil ctx config fn-web-in fn-web-out)
    (mv a sessions fn-web-out)))

; --- The groups (GET /): LIST ACTIVE (RFC 3977 7.6.3).
(defun fn-wss-k-groups (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t) (ignore event))
  (let* ((ctx (fn-wss-f-ctx flow))
         (r (fn-wss-reply 0 fn-web-in)))
    (if (equal (fn-wss-reply-code r) 215)
        (mv-let (a fn-web-out)
          (fn-wss-page 200 nil (fn-wrq-oct "Groups")
                       (fn-wr-groups-main
                        (fn-wss-active-rows (min (fn-wss-reply-bs r) (fn-wss-reply-be r))
                                            (fn-wss-reply-be r) fn-web-in))
                       ctx config fn-web-in fn-web-out)
          (mv a sessions fn-web-out))
      (fn-wss-trouble 503 (fn-wrq-oct "The server said no") *fn-wss-msg-unreachable*
                      ctx config sessions fn-web-in fn-web-out))))

; --- A group (GET /g?name=G[&before=N]): GROUP, then OVER of a window.
(defun fn-wss-k-group (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t) (ignore event))
  (let* ((ctx (fn-wss-f-ctx flow)) (data (fn-wss-f-data flow))
         (group (fn-wrq-nth 0 data)) (session (fn-wss-c-session ctx))
         (r (fn-wss-reply 0 fn-web-in)) (code (fn-wss-reply-code r)))
    (case (fn-wss-f-stage flow)
      (:group
       (if (equal code 211)
           (let* ((f (fn-wss-status-fields fn-web-in))
                  (low (fn-ot-decimal-parse (fn-wrq-nth 2 f) nil))
                  (high (fn-ot-decimal-parse (fn-wrq-nth 3 f) nil))
                  (before (fn-ot-decimal-parse (fn-wrq-nth 1 data) nil))
                  (hi (if (and before high (< before high)) (- before 1) (nfix high)))
                  (lo (max (nfix low) (- hi (1- *fn-wss-window*)))))
             (if (and low high (<= 1 hi) (<= lo hi))
                 (fn-wss-send-session :group :over (list group lo (nfix low))
                                      (fn-wss-cmd (list (fn-wrq-oct "OVER")
                                                        (append (fn-ot-decimal-octets lo) (list 45)
                                                                (fn-ot-decimal-octets hi))))
                                      session ctx sessions fn-web-out)
               (mv-let (a fn-web-out)
                 (fn-wss-page 200 nil group (fn-wr-group-main group nil nil) ctx config
                              fn-web-in fn-web-out)
                 (mv a sessions fn-web-out))))
         (fn-wss-trouble 404 (fn-wrq-oct "No such group")
                         (fn-wrq-oct "There's no group by that name here, or you can't read it.")
                         ctx config sessions fn-web-in fn-web-out)))
      (otherwise
       (if (equal code 224)
           (let* ((lo (nfix (fn-wrq-nth 1 data))) (low (nfix (fn-wrq-nth 2 data))))
             (mv-let (a fn-web-out)
               (fn-wss-page 200 nil group
                            (fn-wr-group-main group
                                              (fn-wss-over-rows (min (fn-wss-reply-bs r) (fn-wss-reply-be r))
                                                                (fn-wss-reply-be r) nil fn-web-in)
                                              (if (< low lo) (fn-ot-decimal-octets lo) nil))
                            ctx config fn-web-in fn-web-out)
               (mv a sessions fn-web-out)))
         (fn-wss-trouble 503 (fn-wrq-oct "The server said no") *fn-wss-msg-unreachable*
                         ctx config sessions fn-web-in fn-web-out))))))

(defthm fn-wss-headers-cdr-natp
  (natp (cdr (fn-wss-headers j be found fn-web-in)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-wss-headers j be found fn-web-in)
           :in-theory (e/d (fn-wss-headers)
                           (fn-wss-continued fn-wss-content-end fn-wss-colon fn-wss-slice
                            fn-wrq-rev-down fn-wrq-rev fn-wss-field-index fn-wss-skip-ws
                            fn-wss-put-span fn-oct-line-end fn-wrq-shortp)))))

; The article page's view of an ARTICLE reply whose block is [BS, BE):
; (FOUND BODY OWN MSGID).
(defun fn-wss-article-view (bs be login fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp bs) (natp be) (<= be (fn-octets-len fn-web-in)))))
  (let* ((h (fn-wss-headers bs be (list nil nil nil nil nil) fn-web-in))
         (found (car h))
         (body (cons (min (nfix (cdr h)) (nfix be)) (nfix be)))
         (from (fn-wrq-nth 1 found))
         (own (and (consp from) (natp (car from)) (natp (cdr from))
                   (fn-wss-span-has (car from) (cdr from)
                                    (append (list 60) (fn-wr-octets-only login) (list 64))
                                    fn-web-in)))
         (msgid (fn-wss-span-slice (fn-wrq-nth 4 found) fn-web-in)))
    (list found body own msgid)))

(in-theory (disable fn-wss-article-view fn-wss-headers fn-wss-span-has fn-wss-span-slice fn-wr-article-main
                    fn-wr-group-main fn-wr-groups-main fn-wss-active-rows fn-wss-over-rows
                    fn-wss-status-fields fn-wss-trouble fn-wss-send-session))

; --- An article (GET /a?g=G&n=N): GROUP and ARTICLE in one feed.
(defun fn-wss-k-article (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t
                  :guard-hints (("Goal" :do-not-induct t)))
           (ignore event))
  (let* ((ctx (fn-wss-f-ctx flow)) (data (fn-wss-f-data flow))
         (group (fn-wrq-nth 0 data)) (session (fn-wss-c-session ctx))
         (r1 (fn-wss-reply 0 fn-web-in))
         (r2 (fn-wss-reply (min (fn-wss-reply-next r1) (fn-octets-len fn-web-in)) fn-web-in)))
    (if (and (equal (fn-wss-reply-code r1) 211) (equal (fn-wss-reply-code r2) 220))
        (let ((v (fn-wss-article-view (min (fn-wss-reply-bs r2) (fn-wss-reply-be r2))
                                      (min (fn-wss-reply-be r2) (fn-octets-len fn-web-in))
                                      (fn-wss-s-login session) fn-web-in)))
          (mv-let (a fn-web-out)
            (fn-wss-page 200 nil group
                         (fn-wr-article-main group (fn-wrq-nth 0 v) (fn-wrq-nth 1 v)
                                             (fn-wrq-nth 2 v) (fn-wrq-nth 3 v))
                         ctx config fn-web-in fn-web-out)
            (mv a sessions fn-web-out)))
      (fn-wss-trouble 404 (fn-wrq-oct "Not here")
                      (fn-wrq-oct "That post isn't here: it may have been removed.")
                      ctx config sessions fn-web-in fn-web-out))))

; --- Posting and removing: "POST" alone first (RFC 3977 6.3.1: the article
; only after 340), then the rest of what fn-web-out holds.
(defun fn-wss-k-submit (sessions flow event config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t) (ignore event))
  (let* ((route (fn-wss-f-route flow)) (ctx (fn-wss-f-ctx flow)) (data (fn-wss-f-data flow))
         (group (fn-wrq-nth 0 data)) (msgid (fn-wrq-nth 1 data))
         (session (fn-wss-c-session ctx))
         (r (fn-wss-reply 0 fn-web-in)) (code (fn-wss-reply-code r)))
    (case (fn-wss-f-stage flow)
      (:posting
       (if (equal code 340)
           (mv (list :send (fn-wss-s-cid session) 6 (fn-octets-len fn-web-out)
                     (fn-wss-flow route :article ctx data))
               sessions fn-web-out)
         (fn-wss-trouble 403 (fn-wrq-oct "Not posted")
                         (fn-wrq-oct "The server isn't taking posts from you just now.")
                         ctx config sessions fn-web-in fn-web-out)))
      (:article
       (cond ((and (equal code 240) (equal route :post))
              (mv-let (a fn-web-out)
                (fn-wss-outcome 200 :ok (fn-wrq-oct "Posted!")
                                (fn-wrq-oct "Posted! The server took your post.")
                                nil group ctx config fn-web-in fn-web-out)
                (mv a sessions fn-web-out)))
             ((equal code 240)
              (fn-wss-send-session :remove :check data
                                   (fn-wss-cmd (list (fn-wrq-oct "STAT") msgid))
                                   session ctx sessions fn-web-out))
             ((and (natp code) (<= 400 code) (< code 500))
              (fn-wss-trouble 403 (if (equal route :post) (fn-wrq-oct "Not posted")
                                    (fn-wrq-oct "Not removed"))
                              (fn-wrq-oct "The server said no.")
                              ctx config sessions fn-web-in fn-web-out))
             (t (fn-wss-trouble 503 (fn-wrq-oct "Not sure")
                                (fn-wrq-oct "We couldn't tell whether the server took it. Look at the group before sending it again.")
                                ctx config sessions fn-web-in fn-web-out))))
      (otherwise
       (if (equal code 430)
           (mv-let (a fn-web-out)
             (fn-wss-outcome 200 :ok (fn-wrq-oct "Removed")
                             (fn-wrq-oct "Your post has been removed from this server.")
                             nil group ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out))
         (fn-wss-trouble 200 (fn-wrq-oct "Still there")
                         (fn-wrq-oct "The server took the removal but still shows the post.")
                         ctx config sessions fn-web-in fn-web-out))))))

(in-theory (disable fn-wss-k-groups fn-wss-k-group fn-wss-k-article fn-wss-k-submit
                    fn-wss-k-signin fn-wss-k-redeem fn-wss-m-signin fn-wss-m-redeem))

; -----------------------------------------------------------------------------
; The routes' first steps.

(defconst *fn-wss-css-fields*
  (list (cons (fn-wrq-oct "Content-Type") (fn-wrq-oct "text/css; charset=utf-8"))
        (cons (fn-wrq-oct "Cache-Control") (fn-wrq-oct "max-age=3600"))))

(defun fn-wss-referer-path (request)
  ; The path of a Referer on this site, else "/".
  (declare (xargs :guard t))
  (let* ((ref (fn-wr-octets-only (fn-web-req-referer request)))
         (host (fn-web-req-host request))
         (rest (cond ((fn-wrq-prefix-ci (fn-wrq-oct "http://") ref) (fn-wrq-drop 7 ref))
                     ((fn-wrq-prefix-ci (fn-wrq-oct "https://") ref) (fn-wrq-drop 8 ref))
                     (t nil))))
    (if (and (consp host) (fn-oct-list-prefixp host rest))
        (fn-wss-next-ok (fn-wrq-drop (len host) rest))
      (list 47))))

(defun fn-wss-m-theme (sessions ctx fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((v (fn-wss-form (fn-wrq-oct "theme") ctx fn-web-in))
         (v (if (member-equal v (list (fn-wrq-oct "light") (fn-wrq-oct "dark"))) v
              (fn-wrq-oct "auto"))))
    (mv-let (a fn-web-out)
      (fn-wss-redirect (fn-wss-referer-path (fn-wss-c-request ctx))
                       (list (fn-wss-cookie (fn-wrq-oct "fnr_theme") v 34560000 (fn-wss-c-secure ctx)))
                       ctx fn-web-out)
      (mv a sessions fn-web-out))))

(defun fn-wss-m-post (session sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((group (fn-wss-form (fn-wrq-oct "g") ctx fn-web-in))
         (subject (fn-wss-form (fn-wrq-oct "subject") ctx fn-web-in))
         (bs (fn-wss-c-bs ctx)) (be (fn-wss-c-be ctx))
         (span (and (<= bs be) (<= be (fn-octets-len fn-web-in))
                    (fn-wrq-body-span (fn-wrq-oct "body") bs be fn-web-in))))
    (if (and (fn-wss-groupp group) (consp subject) (consp span)
             (natp (car span)) (natp (cdr span)) (< (car span) (cdr span))
             (<= (cdr span) (fn-octets-len fn-web-in)))
        (let ((fn-web-out (fn-wss-write-post (fn-wss-s-login session) (fn-wss-cfg-domain config)
                                             group subject (car span) (cdr span)
                                             fn-web-in fn-web-out)))
          (mv (list :send (fn-wss-s-cid session) 0 6
                    (fn-wss-flow :post :posting ctx (list group nil)))
              sessions fn-web-out))
      (mv-let (a fn-web-out)
        (fn-wss-page 400 nil (fn-wrq-oct "Post")
                     (fn-wr-compose-main group (fn-wss-s-csrf session)
                                         (fn-wrq-oct "Please write a subject and a message.")
                                         subject nil)
                     ctx config fn-web-in fn-web-out)
        (mv a sessions fn-web-out)))))

(defun fn-wss-m-remove (session sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((group (fn-wss-form (fn-wrq-oct "g") ctx fn-web-in))
        (msgid (fn-wss-form (fn-wrq-oct "id") ctx fn-web-in)))
    (if (and (fn-wss-groupp group) (fn-wss-msgidp msgid))
        (let ((fn-web-out (fn-wss-write (fn-wss-cancel-octets (fn-wss-s-login session)
                                                              (fn-wss-cfg-domain config)
                                                              group msgid)
                                        fn-web-out)))
          (mv (list :send (fn-wss-s-cid session) 0 6
                    (fn-wss-flow :remove :posting ctx (list group msgid)))
              sessions fn-web-out))
      (fn-wss-trouble 400 (fn-wrq-oct "Not removed") (fn-wrq-oct "That link is not one of this site's.")
                      ctx config sessions fn-web-in fn-web-out))))

; A route whose capability the gate checked: its first step.
(defun fn-wss-start (name session sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (case name
    (:health
     (mv (list :health (fn-wss-flow :health :observed ctx nil)) sessions fn-web-out))
    (:style
     (let ((fn-web-out (fn-wss-write *fn-web-css* fn-web-out)))
       (mv (list :respond 200 *fn-wss-css-fields* (fn-wss-bodyp ctx)) sessions fn-web-out)))
    (:signin-form
     (mv-let (a fn-web-out)
       (fn-wss-signin-page 200 nil nil (fn-wss-query (fn-wrq-oct "next") ctx) ctx config
                           fn-web-in fn-web-out)
       (mv a sessions fn-web-out)))
    (:redeem-form
     (mv-let (a fn-web-out) (fn-wss-redeem-page 200 nil nil ctx config fn-web-in fn-web-out)
       (mv a sessions fn-web-out)))
    (:signin (fn-wss-m-signin sessions ctx config fn-web-in fn-web-out))
    (:redeem (fn-wss-m-redeem sessions ctx config fn-web-in fn-web-out))
    (:theme (fn-wss-m-theme sessions ctx fn-web-in fn-web-out))
    (:groups
     (fn-wss-send-session :groups :list nil (fn-wss-cmd (list (fn-wrq-oct "LIST") (fn-wrq-oct "ACTIVE")))
                          session ctx sessions fn-web-out))
    (:group
     (let ((g (fn-wss-query (fn-wrq-oct "name") ctx))
           (before (fn-wss-query (fn-wrq-oct "before") ctx)))
       (if (fn-wss-groupp g)
           (fn-wss-send-session :group :group (list g (if (fn-wss-numberp before) before nil))
                                (fn-wss-cmd (list (fn-wrq-oct "GROUP") g))
                                session ctx sessions fn-web-out)
         (fn-wss-trouble 404 (fn-wrq-oct "No such group") (fn-wrq-oct "That link names no group.")
                         ctx config sessions fn-web-in fn-web-out))))
    (:article
     (let ((g (fn-wss-query (fn-wrq-oct "g") ctx))
           (n (fn-wss-query (fn-wrq-oct "n") ctx)))
       (if (and (fn-wss-groupp g) (fn-wss-numberp n))
           (fn-wss-send-session :article :article (list g n)
                                (append (fn-wss-cmd (list (fn-wrq-oct "GROUP") g))
                                        (fn-wss-cmd (list (fn-wrq-oct "ARTICLE") n)))
                                session ctx sessions fn-web-out)
         (fn-wss-trouble 404 (fn-wrq-oct "Not here") (fn-wrq-oct "That link names no post.")
                         ctx config sessions fn-web-in fn-web-out))))
    (:compose
     (let ((g (fn-wss-query (fn-wrq-oct "g") ctx)))
       (mv-let (a fn-web-out)
         (fn-wss-page (if (fn-wss-groupp g) 200 404) nil (fn-wrq-oct "Post")
                      (fn-wr-compose-main g (fn-wss-s-csrf session) nil nil nil)
                      ctx config fn-web-in fn-web-out)
         (mv a sessions fn-web-out))))
    (:post (fn-wss-m-post session sessions ctx config fn-web-in fn-web-out))
    (:remove-form
     (let ((g (fn-wss-query (fn-wrq-oct "g") ctx))
           (id (fn-wss-query (fn-wrq-oct "id") ctx)))
       (if (and (fn-wss-groupp g) (fn-wss-msgidp id))
           (mv-let (a fn-web-out)
             (fn-wss-page 200 nil (fn-wrq-oct "Remove my post")
                          (fn-wr-remove-main g (fn-wss-s-csrf session) id)
                          ctx config fn-web-in fn-web-out)
             (mv a sessions fn-web-out))
         (fn-wss-trouble 404 (fn-wrq-oct "Not here") (fn-wrq-oct "That link names no post.")
                         ctx config sessions fn-web-in fn-web-out))))
    (:remove (fn-wss-m-remove session sessions ctx config fn-web-in fn-web-out))
    (:signout (mv (list :close (fn-wss-s-cid session) (fn-wss-flow :signout :closing ctx nil))
                  sessions fn-web-out))
    (otherwise (fn-wss-trouble 404 (fn-wrq-oct "Not found") (fn-wrq-oct "There's nothing here.")
                               ctx config sessions fn-web-in fn-web-out))))

(in-theory (disable fn-wss-start))

; -----------------------------------------------------------------------------
; THE GATE: the row's capability, checked before its first step runs.

(defun fn-wss-signin-location (request)
  ; /signin?next=PATH[?QUERY] for a page that needs a session.
  (declare (xargs :guard t))
  (let ((path (fn-web-req-path request)) (query (fn-web-req-query request)))
    (if (and (equal (fn-web-req-method request) :get) (not (equal path (list 47))))
        (append (fn-wrq-oct "/signin?next=")
                (fn-wr-pct-encode (append path (if (consp query) (cons 63 query) nil))))
      (fn-wrq-oct "/signin"))))

(defun fn-wss-gate (row session sessions ctx config fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((cap (fn-web-row-capability row))
         (name (fn-web-row-name row))
         (request (fn-wss-c-request ctx)))
    (cond
     ((and (member cap '(:same-site :pre :csrf)) (not (fn-wss-same-site request)))
      (fn-wss-trouble 403 (fn-wrq-oct "Not allowed") (fn-wrq-oct "That didn't come from this site.")
                      ctx config sessions fn-web-in fn-web-out))
     ((and (equal cap :pre)
           (not (and (fn-wss-tokenp (fn-wss-cookie-val (fn-wrq-oct "fnr_pre") ctx))
                     (equal (fn-wss-cookie-val (fn-wrq-oct "fnr_pre") ctx)
                            (fn-wss-form (fn-wrq-oct "pre") ctx fn-web-in)))))
      (mv-let (a fn-web-out)
        (if (equal name :redeem)
            (fn-wss-redeem-page 400 (fn-wrq-oct "Something went wrong. Please try again.")
                                nil ctx config fn-web-in fn-web-out)
          (fn-wss-signin-page 400 (fn-wrq-oct "Something went wrong. Please try again.")
                              nil nil ctx config fn-web-in fn-web-out))
        (mv a sessions fn-web-out)))
     ((and (member cap '(:session :csrf)) (not session))
      (mv-let (a fn-web-out) (fn-wss-redirect (fn-wss-signin-location request) nil ctx fn-web-out)
        (mv a sessions fn-web-out)))
     ((and (equal cap :csrf)
           (not (equal (fn-wss-form (fn-wrq-oct "csrf") ctx fn-web-in) (fn-wss-s-csrf session))))
      (fn-wss-trouble 403 (fn-wrq-oct "Not allowed") (fn-wrq-oct "That form is out of date; please go back, reload and try again.")
                      ctx config sessions fn-web-in fn-web-out))
     (t (fn-wss-start name session sessions ctx config fn-web-in fn-web-out)))))

; :begin -- close one expired session's connection per step (the event is
; kept in the flow and begun again after), then route and gate.
; The route table admits GET (and HEAD) and POST. RFC 9110 15.5.6:
; a 405 response names the methods the target resource allows.
(defun fn-wss-allow-value (methods)
  (declare (xargs :guard t))
  (cond ((and (member :get (fn-wrq-true methods)) (member :post (fn-wrq-true methods)))
         (fn-wrq-oct "GET, HEAD, POST"))
        ((member :get (fn-wrq-true methods)) (fn-wrq-oct "GET, HEAD"))
        ((member :post (fn-wrq-true methods)) (fn-wrq-oct "POST"))
        (t nil)))

(defun fn-wss-route-refusal (route ctx config sessions fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (if (equal (fn-wrq-nth 1 route) 405)
      (mv-let (action fn-web-out)
        (fn-wss-page 405
                     (list (cons (fn-wrq-oct "Allow")
                                 (fn-wss-allow-value (fn-wrq-nth 2 route))))
                     (fn-wrq-oct "Method not allowed")
                     (fn-wr-outcome-main :no (fn-wrq-oct "Method not allowed")
                                         (fn-wrq-oct "This resource does not support that method.")
                                         nil nil)
                     ctx config fn-web-in fn-web-out)
        (mv action sessions fn-web-out))
    (fn-wss-trouble 404 (fn-wrq-oct "Not found")
                    (fn-wrq-oct "There's nothing here.")
                    ctx config sessions fn-web-in fn-web-out)))

(defun fn-web-private-begin-row-p (row)
  (declare (xargs :guard t))
  (and (member-equal row *fn-web-routes*)
       (member (fn-web-row-name row) '(:post :remove)) t))

(defun fn-wss-begin (config sessions event fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let* ((request (fn-wrq-nth 1 event))
         (now (nfix (fn-wrq-nth 4 event)))
         (idle (fn-wss-cfg-idle config))
         (expired (fn-wss-expired sessions now idle)))
    (if (consp expired)
        (mv (list :close (fn-wss-s-cid (car expired))
                  (fn-wss-flow :expire :closing nil event))
            (fn-wss-drop (fn-wss-s-token (car expired)) sessions)
            fn-web-out)
      (let* ((token (fn-web-cookie-get (fn-wrq-oct "fnr_session") (fn-web-req-cookie request)))
             (session (and (fn-wss-tokenp token) (fn-wss-find token sessions now idle)))
             (sessions (if session (fn-wss-touch token sessions now) sessions))
             (ctx (fn-wss-ctx request (fn-wrq-nth 2 event) (fn-wrq-nth 3 event) now
                              (fn-wrq-nth 5 event) (fn-wrq-nth 6 event) (fn-wrq-nth 7 event)
                              (fn-wrq-nth 8 event) (fn-wrq-nth 9 event)
                              session (fn-wss-theme-of request) config))
             (route (fn-web-route (fn-web-req-method request) (fn-web-req-path request))))
        (if (equal (car route) :route)
            (if (and (equal (fn-wrq-nth 7 config) :private-begin)
                     (fn-web-private-begin-row-p (cadr route)))
                (mv (list :private-begin (cadr route) session ctx) sessions fn-web-out)
              (fn-wss-gate (cadr route) session sessions ctx config fn-web-in fn-web-out))
          (fn-wss-route-refusal route ctx config sessions fn-web-in fn-web-out))))))

; THE HOST-CALLED STEP (host/web-host.lisp fn-web-host-step, called by
; host/native/web-host.lisp for every event of every request).
(defun fn-web-step (config sessions flow event fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (let ((ctx (fn-wss-f-ctx flow)))
    (cond
     ((equal (fn-wss-car event) :begin) (fn-wss-begin config sessions event fn-web-in fn-web-out))
     ((equal (fn-wss-f-route flow) :expire)
      (fn-wss-begin config sessions (fn-wss-f-data flow) fn-web-in fn-web-out))
     ((equal (fn-wss-f-route flow) :health)
      (let* ((observation (and (equal (fn-wss-car event) :health-observation)
                               (fn-wrq-nth 1 event)))
             (answer (fn-whl-answer observation))
             (fn-web-out (fn-wss-write (cadr answer) fn-web-out)))
        (mv (list :respond (car answer)
                  (list (cons (fn-wrq-oct "Content-Type")
                              (fn-wrq-oct "text/plain; charset=utf-8"))
                        (cons (fn-wrq-oct "Cache-Control") (fn-wrq-oct "no-store")))
                  (fn-wss-bodyp ctx)) sessions fn-web-out)))
     ((equal (fn-wss-f-route flow) :signin)
      (fn-wss-k-signin sessions flow event config fn-web-in fn-web-out))
     ((equal (fn-wss-f-route flow) :redeem)
      (fn-wss-k-redeem sessions flow event config fn-web-in fn-web-out))
     ; A session whose connection the owner no longer knows: gone.
     ((equal (fn-wss-car event) :gone)
      (let* ((session (fn-wss-c-session ctx))
             (sessions (fn-wss-drop (fn-wss-s-token session) sessions)))
        (mv-let (a fn-web-out)
          (fn-wss-redirect (fn-wrq-oct "/signin")
                           (list (fn-wss-cookie (fn-wrq-oct "fnr_session") nil 0 (fn-wss-c-secure ctx)))
                           ctx fn-web-out)
          (mv a sessions fn-web-out))))
     ((equal (fn-wss-f-route flow) :signout)
      (let* ((session (fn-wss-c-session ctx))
             (sessions (fn-wss-drop (fn-wss-s-token session) sessions)))
        (mv-let (a fn-web-out)
          (fn-wss-redirect (fn-wrq-oct "/signin")
                           (list (fn-wss-cookie (fn-wrq-oct "fnr_session") nil 0 (fn-wss-c-secure ctx)))
                           ctx fn-web-out)
          (mv a sessions fn-web-out))))
     ((equal (fn-wss-f-route flow) :groups)
      (fn-wss-k-groups sessions flow event config fn-web-in fn-web-out))
     ((equal (fn-wss-f-route flow) :group)
      (fn-wss-k-group sessions flow event config fn-web-in fn-web-out))
     ((equal (fn-wss-f-route flow) :article)
      (fn-wss-k-article sessions flow event config fn-web-in fn-web-out))
     ((member (fn-wss-f-route flow) '(:post :remove))
      (fn-wss-k-submit sessions flow event config fn-web-in fn-web-out))
     (t (fn-wss-trouble 500 (fn-wrq-oct "Error") (fn-wrq-oct "Something went wrong here.")
                        ctx config sessions fn-web-in fn-web-out)))))



; Reply handlers for the already captured read/post flow do not consult the
; live session table. The core selects this private worker boundary; BEGIN,
; authentication, expiry and disappearance remain the stateful boundary.
(defun fn-web-private-reply-p (flow event)
  (declare (xargs :guard t))
  (and (equal event '(:reply))
       (member (fn-wss-f-route flow) '(:groups :group :article :post :remove)) t))

(defun fn-web-private-reply-step (config flow event fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (if (fn-web-private-reply-p flow event)
      (mv-let (action sessions fn-web-out)
        (fn-web-step config nil flow event fn-web-in fn-web-out)
        (declare (ignore sessions))
        (mv action fn-web-out))
    (mv nil fn-web-out)))


; Only these captured gate/start handlers preserve the session table.
; Session lookup/touch/expiry happened in BEGIN under the owner section.
(defun fn-web-private-begin-p (action)
  (declare (xargs :guard t))
  (and (equal (fn-wss-car action) :private-begin)
       (fn-web-private-begin-row-p (fn-wrq-nth 1 action)) t))
(defun fn-web-private-begin-step (config action fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard t))
  (if (fn-web-private-begin-p action)
      (mv-let (next sessions fn-web-out)
        (fn-wss-gate (fn-wrq-nth 1 action) (fn-wrq-nth 2 action) nil
                     (fn-wrq-nth 3 action) config fn-web-in fn-web-out)
        (declare (ignore sessions))
        (mv next fn-web-out))
    (mv nil fn-web-out)))
