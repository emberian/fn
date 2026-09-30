; fn: the node's own web face, part 1 -- the HTTP/1.1 request, read in
; place (lane web-native, PRF-337, WEB-005; 2026-09-28).
;
; The friends' web reader was a Python process in front of the node (it
; was retired on 2026-09-28): a second implementation of the
; boundary -- request parsing, login pacing, cookies, rendering -- behind an
; NNTP client.  This book and its three siblings make the web face the
; node's own: the host (host/native/web-host.lisp) moves octets between a
; socket and the buffers below and calls these functions; every decision is
; here.
;
;   books/web-request.lisp  (this)  the request: framing, the head parser,
;                                   the form and cookie readers, the route
;                                   table and the response head codec
;   books/web-render.lisp           HTML pages (escaping proved)
;   books/web-session.lisp          sessions, CSRF, what each route does
;
; REPRESENTATION (D27).  The request is read IN PLACE from `fn-web-in', an
; abstract stobj congruent to `fn-octets' (books/octets-stobj.lisp): its
; logical value is the octet list and its executable a byte array the host
; fills from the socket.  Every reader below is written over the formal
; `fn-octets', so it is one definition for both views: logically `nth' of
; the list (fn-oct-get-is-nth), executed as one array read.  The page is
; written into `fn-web-out', the second congruent stobj.  Neither is the
; served path's `fn-octets': the web thread owns these two and nothing else
; touches them (host/native/web-host.lisp).
;
; THE HEAD PARSER is one pass: `fn-wrq-scan' folds `fn-wrq-next' over the
; octets [0, END) of the framed head, one octet per call, and
; `fn-wrq-finish' judges the result.  Its logical model is the same fold
; over the list (`fn-wrq-scan-is-fold').  The state carries a WORK counter:
; one unit per octet plus one per octet of any accumulated token it
; finalizes (a reverse, a trim, a case fold, a classification).  Keystone
; `fn-wrq-scan-work-bound': the work of parsing a head of N octets is at
; most 2N, and nothing is read at or past END (the guard; every read is
; `fn-octets-get' at an index below END).  Header names are classified only
; up to *fn-wrq-max-name* octets, so a classification is constant work.
;
; What the parser accepts (RFC 9112, cited by section):
;   request-line = method SP request-target SP HTTP-version CRLF  (3)
;   method: GET, HEAD, POST; any other token is 501 (RFC 9110 9.1)
;   request-target: origin-form, or absolute-form reduced to its path and
;     query (3.2.2: a server MUST accept absolute-form); anything else 400
;   HTTP-version: HTTP/1.1 or HTTP/1.0; another HTTP/x.y is 505
;   field-line = field-name ":" OWS field-value OWS CRLF  (5)
;     whitespace before the colon is 400 (5.1 MUST); obs-fold is 400 (5.2
;     permits rejecting); CR, LF or NUL in a value is 400 (RFC 9110 5.5)
;   HTTP/1.1 without exactly one Host is 400 (3.2 MUST)
;   Content-Length: one value, digits only (several equal ones are one;
;     unequal ones are 400, 6.3); POST without it is 411; over the
;     operator's body limit 413
;   Transfer-Encoding: 501.  LOCAL POLICY, a stated deviation from 6.1
;     ("MUST be able to parse the chunked transfer coding"): the only bodies
;     this face accepts are the HTML forms it serves, which every browser
;     sends with Content-Length; a proxy in front (Caddy) buffers them.
;   Only CRLF ends a line (2.2 permits a server to accept a bare LF; this
;   one does not: 400).
; The head is at most the profile's head limit (431 past it, RFC 6585 5).
;
; ROUTES.  `*fn-web-routes*' is the table: one row per (method, path), the
; function that serves it and the capability it needs.  The router
; (`fn-web-route') answers a row of the table or a refusal
; (`fn-web-route-is-a-row'); books/web-session.lisp dispatches on the row
; and checks the capability before the model function runs.
;
; RESPONSES.  `fn-web-response-head' writes the status line and the
; fields.  Every field value it writes is `fn-wrq-field-valuep' (no CR, LF
; or NUL), so the head's CRLFs are exactly its own line ends
; (`fn-web-response-head-crlf-count': response splitting is impossible by
; construction).

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "octet-text")

; -----------------------------------------------------------------------------
; The two buffers of the web thread.

(defabsstobj fn-web-in
  :foundation fn-octets$c
  :recognizer (fn-web-in-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-web-in :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-web-in-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-web-in-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-web-in-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-web-in-append-octet :logic fn-octets$a-append-octet
                                    :exec fn-octets$c-append-octet :protect t)
            (fn-web-in-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-web-in-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                               :protect t)
            (fn-web-in-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-web-in-from-list :logic fn-octets$a-from-list
                                 :exec fn-octets$c-from-list :protect t)
            (fn-web-in-append-list :logic fn-octets$a-append-list
                                   :exec fn-oct-write-list :protect t)
            (fn-web-in-append-back :logic fn-octets$a-append-back
                                   :exec fn-octets$c-append-back :protect t)
            (fn-web-in-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-web-in-append-word :logic fn-octets$a-append-word
                                   :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defabsstobj fn-web-out
  :foundation fn-octets$c
  :recognizer (fn-web-out-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-web-out :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-web-out-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-web-out-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-web-out-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-web-out-append-octet :logic fn-octets$a-append-octet
                                     :exec fn-octets$c-append-octet :protect t)
            (fn-web-out-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-web-out-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                :protect t)
            (fn-web-out-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-web-out-from-list :logic fn-octets$a-from-list
                                  :exec fn-octets$c-from-list :protect t)
            (fn-web-out-append-list :logic fn-octets$a-append-list
                                    :exec fn-oct-write-list :protect t)
            (fn-web-out-append-back :logic fn-octets$a-append-back
                                    :exec fn-octets$c-append-back :protect t)
            (fn-web-out-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-web-out-append-word :logic fn-octets$a-append-word
                                    :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

(defthm fn-web-in-p-is-octet-listp
  (equal (fn-web-in-p x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-web-in-p fn-octets$ap))))

(defthm fn-web-out-p-is-octet-listp
  (equal (fn-web-out-p x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-web-out-p fn-octets$ap))))

; -----------------------------------------------------------------------------
; Octet classes (RFC 9110 5.6.2 tchar; 5.5 field-vchar / obs-text).

(defun fn-wrq-tcharp (o)
  (declare (xargs :guard t))
  (or (fn-ot-digitp o)
      (fn-ot-alphap o)
      (and (member o '(33 35 36 37 38 39 42 43 45 46 94 95 96 124 126)) t)))

(defun fn-wrq-vcharp (o)
  (declare (xargs :guard t))
  (and (integerp o) (<= 33 o) (<= o 126)))

; A field-value octet: VCHAR, obs-text, SP or HT.  Never CR, LF or NUL.
(defun fn-wrq-field-octetp (o)
  (declare (xargs :guard t))
  (and (integerp o)
       (or (equal o 9) (and (<= 32 o) (<= o 126)) (and (<= 128 o) (<= o 255)))))

(defun fn-wrq-field-valuep (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-wrq-field-octetp (car xs)) (fn-wrq-field-valuep (cdr xs)))
    (null xs)))

; REV reversed onto ACC, each octet case-folded: the finalized name.
(defun fn-wrq-rev-down (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-wrq-rev-down (cdr rev) (cons (fn-ot-downcase-octet (car rev)) acc))
    acc))

(defun fn-wrq-rev (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-wrq-rev (cdr rev) (cons (car rev) acc))
    acc))

; Trailing OWS: dropped from the front of the reversed value.
(defun fn-wrq-drop-ows (rev)
  (declare (xargs :guard t))
  (if (and (consp rev) (or (equal (car rev) 32) (equal (car rev) 9)))
      (fn-wrq-drop-ows (cdr rev))
    rev))

;; A string's octets (ASCII constants of this book).
(defun fn-wrq-chars-octets (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs)
      (cons (char-code (car cs)) (fn-wrq-chars-octets (cdr cs)))
    nil))

(defthm fn-wrq-chars-octets-octet-listp
  (implies (character-listp cs) (fn-cbor-octet-listp (fn-wrq-chars-octets cs))))

(defmacro fn-wrq-oct (s) (list 'quote (fn-wrq-chars-octets (coerce s 'list))))

; -----------------------------------------------------------------------------
; The operator's limits: the head octets and the body octets one request may
; bring.  Admission limits (D27): the profile's, never a store ceiling.  The
; body limit a node derives from its article limit is `fn-wrq-body-limit':
; a form carries the article percent-encoded (at most three octets per
; octet) plus its other fields; the POST path bounds the article itself.

(defconst *fn-wrq-default-head-octets* 16384)

(defun fn-wrq-body-limit (article-limit)
  (declare (xargs :guard t))
  (+ (* 3 (nfix article-limit)) 8192))

(defun fn-wrq-limits (head body)
  (declare (xargs :guard t))
  (list :web-limits head body))

(defun fn-wrq-limits-head (l)
  (declare (xargs :guard t))
  (if (and (true-listp l) (posp (cadr l))) (cadr l) *fn-wrq-default-head-octets*))

(defun fn-wrq-limits-body (l)
  (declare (xargs :guard t))
  (if (and (true-listp l) (natp (caddr l))) (caddr l) 0))

(defthm fn-wrq-limits-head-posp
  (posp (fn-wrq-limits-head l))
  :rule-classes :type-prescription)

(defthm fn-wrq-limits-body-natp
  (natp (fn-wrq-limits-body l))
  :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; Framing: where the head ends.  The host appends each socket read to the
; buffer and asks again from where the last answer stopped, so every octet
; is looked at once over the whole head, however the reads split it.
;
;   (:head END)      the head is [0, END): END is just past CR LF CR LF
;   (:need FROM)     no end yet; ask again with FROM after the next read
;   (:refused 431)   no end within the head limit
;
; Only octets below min(len, limit) are examined; the answer's END is at
; most the limit.

(defun fn-wrq-crlf2-at (j fn-octets)
  ; Octets j-3 .. j are CR LF CR LF.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (< j (fn-octets-len fn-octets)))))
  (and (<= 3 j)
       (equal (fn-octets-get j fn-octets) 10)
       (equal (fn-octets-get (- j 1) fn-octets) 13)
       (equal (fn-octets-get (- j 2) fn-octets) 10)
       (equal (fn-octets-get (- j 3) fn-octets) 13)))

(defun fn-wrq-frame-scan (j stop fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (natp stop) (<= stop (fn-octets-len fn-octets)))
                  :measure (nfix (- stop j))))
  (cond ((or (not (natp j)) (not (natp stop)) (<= stop j)) (list :need (nfix j)))
        ((fn-wrq-crlf2-at j fn-octets) (list :head (1+ j)))
        (t (fn-wrq-frame-scan (1+ j) stop fn-octets))))

(defun fn-web-head-frame (from limits fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (natp from)))
  (let* ((n (fn-octets-len fn-octets))
         (limit (fn-wrq-limits-head limits))
         (stop (min n limit))
         (r (fn-wrq-frame-scan (min (nfix from) stop) stop fn-octets)))
    (if (and (equal (car r) :need) (<= limit n))
        (list :refused 431)
      r)))

(defthm fn-wrq-frame-scan-natp
  (natp (cadr (fn-wrq-frame-scan j stop fn-octets)))
  :rule-classes :type-prescription)

(defthm fn-wrq-frame-scan-tag
  (or (equal (car (fn-wrq-frame-scan j stop fn-octets)) :need)
      (equal (car (fn-wrq-frame-scan j stop fn-octets)) :head))
  :rule-classes nil)

(defthm fn-wrq-frame-scan-head-bound
  (implies (and (natp stop) (equal (car (fn-wrq-frame-scan j stop fn-octets)) :head))
           (and (< 0 (cadr (fn-wrq-frame-scan j stop fn-octets)))
                (<= (cadr (fn-wrq-frame-scan j stop fn-octets)) stop)))
  :rule-classes :linear)

(defthm fn-web-head-frame-bounded
  (let ((r (fn-web-head-frame from limits fn-octets)))
    (implies (equal (car r) :head)
             (and (posp (cadr r))
                  (<= (cadr r) (len fn-octets))
                  (<= (cadr r) (fn-wrq-limits-head limits))))))

; -----------------------------------------------------------------------------
; The head scanner's state: one list, positional.
;
;   0 phase    where in the grammar the next octet falls
;   1 acc      the current token or value, reversed
;   2 kind     the field being read: a recognized name's keyword, or :skip
;   3 work     the work counter (see the keystone)
;   4 method   :get :head :post :unknown, or nil before the first SP
;   5 target   the request-target's octets
;   6 version  :http11 :http10 :unsupported :bad
;   7 fields   ((KIND . VALUE) ...) of recognized fields, newest first
;   8 error    nil, or the status code of the first refusal

;; nth with guard t: the state is read positionally.
(defun fn-wrq-nth (k s)
  (declare (xargs :guard (natp k)))
  (if (consp s)
      (if (zp k) (car s) (fn-wrq-nth (1- k) (cdr s)))
    nil))

(defthm fn-wrq-nth-is-nth
  (implies (natp k) (equal (fn-wrq-nth k s) (nth k s))))

(defun fn-wrq-st (phase acc kind work method target version fields error)
  (declare (xargs :guard t))
  (list phase acc kind work method target version fields error))

(defun fn-wrq-phase (s) (declare (xargs :guard t)) (fn-wrq-nth 0 s))
(defun fn-wrq-acc (s) (declare (xargs :guard t)) (fn-wrq-nth 1 s))
(defun fn-wrq-kind (s) (declare (xargs :guard t)) (fn-wrq-nth 2 s))
(defun fn-wrq-work (s) (declare (xargs :guard t)) (nfix (fn-wrq-nth 3 s)))
(defun fn-wrq-method (s) (declare (xargs :guard t)) (fn-wrq-nth 4 s))
(defun fn-wrq-target (s) (declare (xargs :guard t)) (fn-wrq-nth 5 s))
(defun fn-wrq-version (s) (declare (xargs :guard t)) (fn-wrq-nth 6 s))
(defun fn-wrq-fields (s) (declare (xargs :guard t)) (fn-wrq-nth 7 s))
(defun fn-wrq-error (s) (declare (xargs :guard t)) (fn-wrq-nth 8 s))

; -----------------------------------------------------------------------------
; Classifications of a finalized token.  Each is over a token of at most a
; few octets (the caller checks `fn-wrq-shortp' first): constant work.

(defconst *fn-wrq-max-name* 24)

(defun fn-wrq-shortp (xs k)
  ; Whether XS has at most K elements, walking at most K+1 conses.
  (declare (xargs :guard (natp k)))
  (if (consp xs)
      (and (not (zp k)) (fn-wrq-shortp (cdr xs) (1- k)))
    t))

(defun fn-wrq-method-of (token)
  ; RFC 9110 9.1: method names are case-sensitive.
  (declare (xargs :guard t))
  (cond ((equal token (fn-wrq-oct "GET")) :get)
        ((equal token (fn-wrq-oct "HEAD")) :head)
        ((equal token (fn-wrq-oct "POST")) :post)
        (t :unknown)))

(defun fn-wrq-version-of (token)
  ; RFC 9112 2.3: HTTP-version = "HTTP" "/" DIGIT "." DIGIT, case-sensitive.
  (declare (xargs :guard t))
  (cond ((equal token (fn-wrq-oct "HTTP/1.1")) :http11)
        ((equal token (fn-wrq-oct "HTTP/1.0")) :http10)
        ((and (true-listp token)
              (equal (len token) 8)
              (equal (take 5 token) (fn-wrq-oct "HTTP/"))
              (fn-ot-digitp (nth 5 token))
              (equal (nth 6 token) 46)
              (fn-ot-digitp (nth 7 token)))
         :unsupported)
        (t :bad)))

; The fields this face reads (lower case; RFC 9110 5.1: names are
; case-insensitive).  Any other field is skipped: its value is never kept.
(defconst *fn-wrq-field-names*
  (list (cons (fn-wrq-oct "host") :host)
        (cons (fn-wrq-oct "cookie") :cookie)
        (cons (fn-wrq-oct "content-length") :content-length)
        (cons (fn-wrq-oct "content-type") :content-type)
        (cons (fn-wrq-oct "transfer-encoding") :transfer-encoding)
        (cons (fn-wrq-oct "origin") :origin)
        (cons (fn-wrq-oct "sec-fetch-site") :sec-fetch-site)
        (cons (fn-wrq-oct "referer") :referer)
        (cons (fn-wrq-oct "x-forwarded-for") :x-forwarded-for)))

(defun fn-wrq-field-kind (name)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal name *fn-wrq-field-names*)))
    (if hit (cdr hit) :skip)))

; -----------------------------------------------------------------------------
; One octet of the head.

(defun fn-wrq-fail (s code)
  ; The first refusal wins; the rest of the head is only counted.
  (declare (xargs :guard t))
  (fn-wrq-st :err nil :skip (1+ (fn-wrq-work s)) (fn-wrq-method s) (fn-wrq-target s)
             (fn-wrq-version s) (fn-wrq-fields s)
             (or (fn-wrq-error s) code)))

(defun fn-wrq-go (s phase acc kind extra)
  ; The common step: a new phase, accumulator and field kind; one unit of
  ; work plus EXTRA for a finalized token.
  (declare (xargs :guard t))
  (fn-wrq-st phase acc kind (+ 1 (nfix extra) (fn-wrq-work s)) (fn-wrq-method s)
             (fn-wrq-target s) (fn-wrq-version s) (fn-wrq-fields s) (fn-wrq-error s)))

(defun fn-wrq-next (s o)
  (declare (xargs :guard t))
  (let ((phase (fn-wrq-phase s))
        (acc (fn-wrq-acc s))
        (kind (fn-wrq-kind s)))
    (case phase
      ; method SP
      (:m (cond ((fn-wrq-tcharp o) (fn-wrq-go s :m (cons o acc) :skip 0))
                ((and (equal o 32) (consp acc))
                 (let ((s2 (fn-wrq-go s :t nil :skip (len acc))))
                   (update-nth 4 (if (fn-wrq-shortp acc 8)
                                     (fn-wrq-method-of (fn-wrq-rev acc nil))
                                   :unknown)
                               s2)))
                (t (fn-wrq-fail s 400))))
      ; request-target SP
      (:t (cond ((fn-wrq-vcharp o) (fn-wrq-go s :t (cons o acc) :skip 0))
                ((and (equal o 32) (consp acc))
                 (update-nth 5 (fn-wrq-rev acc nil)
                             (fn-wrq-go s :v nil :skip (len acc))))
                (t (fn-wrq-fail s 400))))
      ; HTTP-version CR
      (:v (cond ((fn-wrq-vcharp o) (fn-wrq-go s :v (cons o acc) :skip 0))
                ((equal o 13)
                 (update-nth 6 (if (fn-wrq-shortp acc 8)
                                   (fn-wrq-version-of (fn-wrq-rev acc nil))
                                 :bad)
                             (fn-wrq-go s :vl nil :skip (len acc))))
                (t (fn-wrq-fail s 400))))
      (:vl (if (equal o 10) (fn-wrq-go s :n nil :skip 0) (fn-wrq-fail s 400)))
      ; the start of a field line, or the empty line
      (:n (cond ((equal o 13) (fn-wrq-go s :el nil :skip 0))
                ((fn-wrq-tcharp o) (fn-wrq-go s :nn (list o) :skip 0))
                ; obs-fold (RFC 9112 5.2) or anything else
                (t (fn-wrq-fail s 400))))
      ; field-name ":"; whitespace before the colon is 400 (RFC 9112 5.1)
      (:nn (cond ((fn-wrq-tcharp o) (fn-wrq-go s :nn (cons o acc) :skip 0))
                 ((equal o 58)
                  (fn-wrq-go s :o nil
                             (if (fn-wrq-shortp acc *fn-wrq-max-name*)
                                 (fn-wrq-field-kind (fn-wrq-rev-down acc nil))
                               :skip)
                             (len acc)))
                 (t (fn-wrq-fail s 400))))
      ; OWS before the value
      (:o (cond ((or (equal o 32) (equal o 9)) (fn-wrq-go s :o nil kind 0))
                ((equal o 13)
                 (let ((s2 (fn-wrq-go s :hl nil :skip 0)))
                   (if (equal kind :skip)
                       s2
                     (update-nth 7 (cons (cons kind nil) (fn-wrq-fields s)) s2))))
                ((fn-wrq-field-octetp o)
                 (fn-wrq-go s :val (if (equal kind :skip) nil (list o)) kind 0))
                (t (fn-wrq-fail s 400))))
      ; field-value CR; a skipped field's octets are not kept
      (:val (cond ((equal o 13)
                   (let ((s2 (fn-wrq-go s :hl nil :skip (len acc))))
                     (if (equal kind :skip)
                         s2
                       (update-nth 7 (cons (cons kind (fn-wrq-rev (fn-wrq-drop-ows acc) nil))
                                           (fn-wrq-fields s))
                                   s2))))
                  ((fn-wrq-field-octetp o)
                   (fn-wrq-go s :val (if (equal kind :skip) nil (cons o acc)) kind 0))
                  (t (fn-wrq-fail s 400))))
      (:hl (if (equal o 10) (fn-wrq-go s :n nil :skip 0) (fn-wrq-fail s 400)))
      (:el (if (equal o 10) (fn-wrq-go s :done nil :skip 0) (fn-wrq-fail s 400)))
      (:err (fn-wrq-go s :err nil :skip 0))
      ; :done, or a state this function never makes
      (otherwise (fn-wrq-fail s 400)))))

(defun fn-wrq-initial ()
  (declare (xargs :guard t))
  (fn-wrq-st :m nil :skip 0 nil nil nil nil nil))

; The logical model: the fold over the list.
(defun fn-wrq-fold (octets s)
  (declare (xargs :guard t))
  (if (consp octets)
      (fn-wrq-fold (cdr octets) (fn-wrq-next s (car octets)))
    s))

; The executable: the same fold over the buffer [i, end), read in place.
(defun fn-wrq-scan (i end s fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))))
  (if (or (not (natp i)) (not (natp end)) (<= end i))
      s
    (fn-wrq-scan (1+ i) end (fn-wrq-next s (fn-octets-get i fn-octets)) fn-octets)))

; -----------------------------------------------------------------------------
; KEYSTONE: the work bound.  One step adds one unit and at most one octet to
; the accumulator, or finalizes the accumulator and adds its length; so
; work + |acc| grows by at most two per octet.

(local
 (defthm fn-wrq-len-rev
   (equal (len (fn-wrq-rev xs acc)) (+ (len xs) (len acc)))))

(local
 (defthm fn-wrq-len-drop-ows
   (<= (len (fn-wrq-drop-ows xs)) (len xs))
   :rule-classes :linear))

(defthm fn-wrq-next-work-step
  (<= (+ (fn-wrq-work (fn-wrq-next s o)) (len (fn-wrq-acc (fn-wrq-next s o))))
      (+ 2 (fn-wrq-work s) (len (fn-wrq-acc s))))
  :rule-classes :linear)

(in-theory (disable fn-wrq-next fn-wrq-work fn-wrq-acc))

(defthm fn-wrq-scan-is-fold
  (equal (fn-wrq-scan i end s fn-octets)
         (fn-wrq-fold (fn-oct-slice-list i end fn-octets) s))
  :hints (("Goal" :induct (fn-wrq-scan i end s fn-octets)
           :in-theory (enable fn-oct-slice-list))))


(defthm fn-wrq-fold-work
  (<= (+ (fn-wrq-work (fn-wrq-fold octets s)) (len (fn-wrq-acc (fn-wrq-fold octets s))))
      (+ (fn-wrq-work s) (len (fn-wrq-acc s)) (* 2 (len octets))))
  :rule-classes :linear)

(defthm fn-wrq-len-slice-list
  (implies (and (natp i) (natp n))
           (equal (len (fn-oct-slice-list i n fn-octets)) (nfix (- n i))))
  :hints (("Goal" :in-theory (enable fn-oct-slice-list))))

(defthm fn-wrq-scan-work-bound
  ; KEYSTONE (PRF-337).  Subject: the host-called head parse's scan
  ; (`fn-web-parse-head' below runs exactly this scan).  Parsing a head of
  ; END octets costs at most 2 * END units of work.
  ; (No hypothesis on END's place in the buffer: the guard keeps the host's
  ; END within it, and the bound holds either way.)
  (implies (natp end)
           (<= (fn-wrq-work (fn-wrq-scan 0 end (fn-wrq-initial) fn-octets))
               (* 2 end)))
  :hints (("Goal" :in-theory (disable fn-wrq-fold-work)
           :do-not-induct t
           :use ((:instance fn-wrq-fold-work
                  (octets (fn-oct-slice-list 0 end fn-octets))
                  (s (fn-wrq-initial)))))))

; -----------------------------------------------------------------------------
; The request-target (RFC 9112 3.2): origin-form, or absolute-form reduced
; to its path and query; then split at the first "?".

(defun fn-wrq-prefix-ci (pre xs)
  ; PRE (lower case) opens XS, compared case-insensitively.
  (declare (xargs :guard t))
  (if (consp pre)
      (and (consp xs)
           (equal (fn-ot-downcase-octet (car xs)) (car pre))
           (fn-wrq-prefix-ci (cdr pre) (cdr xs)))
    t))

(defun fn-wrq-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (and (consp xs) (not (zp n))) (fn-wrq-drop (1- n) (cdr xs)) xs))

(defun fn-wrq-skip-authority (xs)
  ; The rest from the first "/" or "?" after the authority.
  (declare (xargs :guard t))
  (if (consp xs)
      (if (or (equal (car xs) 47) (equal (car xs) 63))
          xs
        (fn-wrq-skip-authority (cdr xs)))
    nil))

(defun fn-wrq-origin-form (target)
  (declare (xargs :guard t))
  (cond ((and (consp target) (equal (car target) 47)) target)
        ((or (fn-wrq-prefix-ci (fn-wrq-oct "http://") target)
             (fn-wrq-prefix-ci (fn-wrq-oct "https://") target))
         (let ((rest (fn-wrq-skip-authority
                      (fn-wrq-drop (if (fn-wrq-prefix-ci (fn-wrq-oct "http://") target) 7 8)
                                   target))))
           (cond ((atom rest) (list 47))
                 ((equal (car rest) 63) (cons 47 rest))
                 (t rest))))
        (t :bad)))

(defun fn-wrq-split-query (xs path-rev)
  ; (PATH . QUERY): the octets before the first "?" and those after it.
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 63)
          (cons (fn-wrq-rev path-rev nil) (if (true-listp (cdr xs)) (cdr xs) nil))
        (fn-wrq-split-query (cdr xs) (cons (car xs) path-rev)))
    (cons (fn-wrq-rev path-rev nil) nil)))

; -----------------------------------------------------------------------------
; Field values: all of one kind, oldest first.

(defun fn-wrq-values (kind fields acc)
  ; FIELDS is newest first; ACC collects oldest first.
  (declare (xargs :guard t))
  (if (consp fields)
      (fn-wrq-values kind (cdr fields)
                     (if (and (consp (car fields)) (equal (car (car fields)) kind))
                         (cons (cdr (car fields)) acc)
                       acc))
    acc))

(defun fn-wrq-true (x)
  (declare (xargs :guard t))
  (if (true-listp x) x nil))

(defthm fn-wrq-true-true-listp
  (true-listp (fn-wrq-true x))
  :rule-classes :type-prescription)

; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap (D27).
(local
 (defthm fn-wrq-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto a acc) b)
          (fn-ag-rev-onto acc (append a b)))
   :hints (("Goal" :induct (fn-ag-rev-onto a acc)))))

; ACC holds the octets so far, reversed.
(defun fn-wrq-join-loop (vals sep acc)
  (declare (xargs :guard (true-listp sep)))
  (if (consp vals)
      (if (consp (cdr vals))
          (fn-wrq-join-loop (cdr vals) sep
                            (fn-ag-rev-onto sep (fn-ag-rev-onto (fn-wrq-true (car vals)) acc)))
        (fn-ag-rev-onto acc (fn-wrq-true (car vals))))
    (fn-ag-rev-onto acc nil)))

(defun fn-wrq-join (vals sep)
  (declare (xargs :guard (true-listp sep) :verify-guards nil))
  (mbe :logic (if (consp vals)
                  (if (consp (cdr vals))
                      (append (fn-wrq-true (car vals)) sep (fn-wrq-join (cdr vals) sep))
                    (fn-wrq-true (car vals)))
                nil)
       :exec (fn-wrq-join-loop vals sep nil)))

(defthm fn-wrq-join-loop-is-rev-onto
  (equal (fn-wrq-join-loop vals sep acc)
         (fn-ag-rev-onto acc (fn-wrq-join vals sep)))
  :hints (("Goal" :induct (fn-wrq-join-loop vals sep acc)
                  :in-theory (disable fn-wrq-true))))

(verify-guards fn-wrq-join
  :hints (("Goal" :in-theory (disable fn-wrq-true))))

(in-theory (disable fn-ot-decimal-parse))

(defun fn-wrq-all-equal (x vals)
  (declare (xargs :guard t))
  (if (consp vals)
      (and (equal x (car vals)) (fn-wrq-all-equal x (cdr vals)))
    t))

; -----------------------------------------------------------------------------
; The request: what the rest of the face reads.  Parsed fields, never raw
; buffer octets: the path and query are the target's octets, the field
; values the (trimmed) values of the fields this face reads.

(defun fn-web-request (method path query version clen host cookie origin fetch referer xff)
  (declare (xargs :guard t))
  (list :web-request method path query version clen host cookie origin fetch referer xff))

(defun fn-web-requestp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 12) (equal (car r) :web-request)))

(defun fn-web-req-method (r) (declare (xargs :guard t)) (fn-wrq-nth 1 r))
(defun fn-web-req-path (r) (declare (xargs :guard t)) (fn-wrq-true (fn-wrq-nth 2 r)))
(defun fn-web-req-query (r) (declare (xargs :guard t)) (fn-wrq-true (fn-wrq-nth 3 r)))
(defun fn-web-req-version (r) (declare (xargs :guard t)) (fn-wrq-nth 4 r))
(defun fn-web-req-clen (r) (declare (xargs :guard t)) (nfix (fn-wrq-nth 5 r)))
(defun fn-web-req-host (r) (declare (xargs :guard t)) (fn-wrq-true (fn-wrq-nth 6 r)))
(defun fn-web-req-cookie (r) (declare (xargs :guard t)) (fn-wrq-true (fn-wrq-nth 7 r)))
(defun fn-web-req-origin (r) (declare (xargs :guard t)) (fn-wrq-nth 8 r))
(defun fn-web-req-fetch-site (r) (declare (xargs :guard t)) (fn-wrq-nth 9 r))
(defun fn-web-req-referer (r) (declare (xargs :guard t)) (fn-wrq-nth 10 r))
(defun fn-web-req-xff (r) (declare (xargs :guard t)) (fn-wrq-true (fn-wrq-nth 11 r)))

(defun fn-wrq-first (vals)
  (declare (xargs :guard t))
  (if (consp vals) (fn-wrq-true (car vals)) nil))

; The judgement of a scanned head.  (:request R) or (:refused CODE).
(defun fn-web-finish-head (s limits)
  (declare (xargs :guard t))
  (let* ((fields (fn-wrq-fields s))
         (version (fn-wrq-version s))
         (method (fn-wrq-method s))
         (form (fn-wrq-origin-form (fn-wrq-target s)))
         (hosts (fn-wrq-values :host fields nil))
         (tes (fn-wrq-values :transfer-encoding fields nil))
         (cls (fn-wrq-values :content-length fields nil))
         (clen (and (consp cls) (fn-ot-decimal-parse (car cls) nil))))
    (cond ((fn-wrq-error s) (list :refused 400))
          ((not (equal (fn-wrq-phase s) :done)) (list :refused 400))
          ((equal version :unsupported) (list :refused 505))
          ((not (or (equal version :http11) (equal version :http10))) (list :refused 400))
          ((equal form :bad) (list :refused 400))
          ((and (equal version :http11) (not (and (consp hosts) (atom (cdr hosts)))))
           (list :refused 400))
          ((and (consp hosts) (consp (cdr hosts))) (list :refused 400))
          ((not (member method '(:get :head :post))) (list :refused 501))
          ((consp tes) (list :refused 501))
          ((and (consp cls) (not (and clen (fn-wrq-all-equal (car cls) (cdr cls)))))
           (list :refused 400))
          ((and clen (< (fn-wrq-limits-body limits) clen)) (list :refused 413))
          ((and (equal method :post) (not clen)) (list :refused 411))
          (t (let ((pq (fn-wrq-split-query form nil)))
               (list :request
                     (fn-web-request method (car pq) (cdr pq) version (nfix clen)
                                     (fn-wrq-first hosts)
                                     (fn-wrq-join (fn-wrq-values :cookie fields nil)
                                                  (fn-wrq-oct "; "))
                                     (fn-wrq-first (fn-wrq-values :origin fields nil))
                                     (fn-wrq-first (fn-wrq-values :sec-fetch-site fields nil))
                                     (fn-wrq-first (fn-wrq-values :referer fields nil))
                                     (fn-wrq-join (fn-wrq-values :x-forwarded-for fields nil)
                                                  (fn-wrq-oct ",")))))))))

(defthm fn-web-finish-head-answers
  (let ((r (fn-web-finish-head s limits)))
    (or (and (equal (car r) :request) (fn-web-requestp (cadr r)))
        (and (equal (car r) :refused)
             (member (cadr r) '(400 411 413 431 501 505)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-wrq-values fn-wrq-join fn-wrq-origin-form
                                      fn-wrq-split-query fn-wrq-all-equal fn-wrq-first))))

; THE HOST-CALLED PARSE (host/native/web-host.lisp fnn-web-read-request,
; after `fn-web-head-frame' answered (:head END)).
(defun fn-web-parse-head (end limits fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp end) (<= end (fn-octets-len fn-octets)))))
  (fn-web-finish-head (fn-wrq-scan 0 end (fn-wrq-initial) fn-octets) limits))

(defthm fn-web-parse-head-answers
  (let ((r (fn-web-parse-head end limits fn-octets)))
    (or (and (equal (car r) :request) (fn-web-requestp (cadr r)))
        (and (equal (car r) :refused)
             (member (cadr r) '(400 411 413 431 501 505)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-web-finish-head fn-wrq-scan-is-fold)
           :use ((:instance fn-web-finish-head-answers
                  (s (fn-wrq-scan 0 end (fn-wrq-initial) fn-octets)))))))

; -----------------------------------------------------------------------------
; Forms (application/x-www-form-urlencoded, the HTML form's encoding) and
; the query.  "+" is SP; "%" and two hex digits is that octet; any other
; "%" stands for itself (the WHATWG urlencoded parser's rule).  A field is
; found by its raw name: every name this face's forms use is a plain
; lower-case word.

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-wrq-urldecode-loop (xs acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp xs)
      (let ((o (car xs)))
        (cond ((equal o 43) (fn-wrq-urldecode-loop (cdr xs) (cons 32 acc)))
              ((and (equal o 37)
                    (consp (cdr xs))
                    (consp (cddr xs))
                    (fn-ot-hex-value (cadr xs))
                    (fn-ot-hex-value (caddr xs)))
               (fn-wrq-urldecode-loop (cdddr xs)
                                      (cons (+ (* 16 (fn-ot-hex-value (cadr xs)))
                                               (fn-ot-hex-value (caddr xs)))
                                            acc)))
              (t (fn-wrq-urldecode-loop (cdr xs) (cons o acc)))))
    (revappend acc nil)))

(defun fn-wrq-urldecode (xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs)
           (let ((o (car xs)))
             (cond ((equal o 43) (cons 32 (fn-wrq-urldecode (cdr xs))))
                   ((and (equal o 37) (consp (cdr xs)) (consp (cddr xs))
                         (fn-ot-hex-value (cadr xs)) (fn-ot-hex-value (caddr xs)))
                    (cons (+ (* 16 (fn-ot-hex-value (cadr xs))) (fn-ot-hex-value (caddr xs)))
                          (fn-wrq-urldecode (cdddr xs))))
                   (t (cons o (fn-wrq-urldecode (cdr xs))))))
         nil)
       :exec (fn-wrq-urldecode-loop xs nil)))

(local
 (defthm fn-wrq-urldecode-loop-is-revappend
   (equal (fn-wrq-urldecode-loop xs acc)
          (revappend acc (fn-wrq-urldecode xs)))
   :hints (("Goal" :induct (fn-wrq-urldecode-loop xs acc)
                   :in-theory (union-theories '(fn-wrq-urldecode-loop fn-wrq-urldecode revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wrq-urldecode-loop)

(verify-guards fn-wrq-urldecode
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-wrq-urldecode)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-wrq-urldecode-loop-is-revappend (acc nil))))))


(defun fn-wrq-field-match (name field)
  ; FIELD (octets of one name=value) has name NAME: its value's octets, else :no.
  (declare (xargs :guard t))
  (if (consp name)
      (if (and (consp field) (equal (car field) (car name)))
          (fn-wrq-field-match (cdr name) (cdr field))
        :no)
    (if (and (consp field) (equal (car field) 61))
        (fn-wrq-true (cdr field))
      :no)))

(defun fn-wrq-form-get-aux (name xs cur-rev)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 38)))
      (fn-wrq-form-get-aux name (cdr xs) (cons (car xs) cur-rev))
    (let ((hit (fn-wrq-field-match name (fn-wrq-rev cur-rev nil))))
      (cond ((not (equal hit :no)) (fn-wrq-urldecode hit))
            ((consp xs) (fn-wrq-form-get-aux name (cdr xs) nil))
            (t :absent)))))

; The decoded value of the first field NAME in the encoded XS, or :absent.
(defun fn-wrq-form-get (name xs)
  (declare (xargs :guard t))
  (fn-wrq-form-get-aux name xs nil))

; The same over the body, in place: the span [s, e) of the first field
; NAME's encoded value within [i, stop), or nil.  Nothing is copied.
(defun fn-wrq-body-name-at (i name stop fn-octets)
  ; Whether [i, stop) opens with NAME "=".
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp stop) (<= stop (fn-octets-len fn-octets)))
                  :measure (len name)))
  (if (consp name)
      (and (natp i) (< i stop)
           (equal (fn-octets-get i fn-octets) (car name))
           (fn-wrq-body-name-at (1+ i) (cdr name) stop fn-octets))
    (and (natp i) (< i stop) (equal (fn-octets-get i fn-octets) 61))))

(defun fn-wrq-body-amp (i stop fn-octets)
  ; The index of the first "&" at or after I, or STOP.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp stop) (<= stop (fn-octets-len fn-octets)))
                  :measure (nfix (- stop i))))
  (cond ((or (not (natp i)) (not (natp stop)) (<= stop i)) (nfix stop))
        ((equal (fn-octets-get i fn-octets) 38) i)
        (t (fn-wrq-body-amp (1+ i) stop fn-octets))))

(defthm fn-wrq-body-amp-bounds
  (implies (and (natp i) (natp stop) (<= i stop))
           (and (<= i (fn-wrq-body-amp i stop fn-octets))
                (<= (fn-wrq-body-amp i stop fn-octets) stop)))
  :rule-classes ((:linear :trigger-terms ((fn-wrq-body-amp i stop fn-octets)))))

(defthm fn-wrq-body-amp-natp
  (natp (fn-wrq-body-amp i stop fn-octets))
  :rule-classes :type-prescription)

(defun fn-wrq-body-span (name i stop fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp stop) (<= i stop)
                              (<= stop (fn-octets-len fn-octets)))
                  :measure (nfix (- stop i))))
  (if (or (not (natp i)) (not (natp stop)) (<= stop i))
      nil
    (let ((amp (fn-wrq-body-amp i stop fn-octets)))
      (if (fn-wrq-body-name-at i name stop fn-octets)
          (cons (min (+ i 1 (len name)) amp) amp)
        (fn-wrq-body-span name (min (1+ amp) stop) stop fn-octets)))))

(defthm fn-wrq-body-span-bounds
  (let ((r (fn-wrq-body-span name i stop fn-octets)))
    (implies (and r (natp i) (natp stop))
             (and (natp (car r)) (natp (cdr r))
                  (<= i (car r)) (<= (car r) (cdr r)) (<= (cdr r) stop)))))

; The decoded octets of the span [s, e): the logical model is
; `fn-wrq-urldecode' of the slice (`fn-wrq-span-decode-is-urldecode').
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-wrq-span-decode-loop (s e fn-octets acc)
  (declare (xargs :stobjs fn-octets :measure (nfix (- e s)) :guard (and (and (natp s) (natp e) (<= s e) (<= e (fn-octets-len fn-octets))) (true-listp acc)) :verify-guards nil))
  (if (or (not (natp s)) (not (natp e)) (<= e s))
      (revappend acc nil)
    (let ((o (fn-octets-get s fn-octets)))
      (cond ((equal o 43) (fn-wrq-span-decode-loop (1+ s) e fn-octets (cons 32 acc)))
            ((and (equal o 37)
                  (< (+ 2 s) e)
                  (fn-ot-hex-value (fn-octets-get (+ 1 s) fn-octets))
                  (fn-ot-hex-value (fn-octets-get (+ 2 s) fn-octets)))
             (fn-wrq-span-decode-loop (+ 3 s)
                                      e
                                      fn-octets
                                      (cons (+ (* 16
                                                  (fn-ot-hex-value (fn-octets-get (+ 1
                                                                                     s)
                                                                                  fn-octets)))
                                               (fn-ot-hex-value (fn-octets-get (+ 2 s)
                                                                               fn-octets)))
                                            acc)))
            (t (fn-wrq-span-decode-loop (1+ s) e fn-octets (cons o acc)))))))

(defun fn-wrq-span-decode (s e fn-octets)
  (declare (xargs :verify-guards nil :stobjs fn-octets
                  :guard (and (natp s) (natp e) (<= s e) (<= e (fn-octets-len fn-octets)))
                  :measure (nfix (- e s))))
  (mbe :logic
       (if (or (not (natp s)) (not (natp e)) (<= e s))
           nil
         (let ((o (fn-octets-get s fn-octets)))
           (cond ((equal o 43) (cons 32 (fn-wrq-span-decode (1+ s) e fn-octets)))
                 ((and (equal o 37) (< (+ 2 s) e)
                       (fn-ot-hex-value (fn-octets-get (+ 1 s) fn-octets))
                       (fn-ot-hex-value (fn-octets-get (+ 2 s) fn-octets)))
                  (cons (+ (* 16 (fn-ot-hex-value (fn-octets-get (+ 1 s) fn-octets)))
                           (fn-ot-hex-value (fn-octets-get (+ 2 s) fn-octets)))
                        (fn-wrq-span-decode (+ 3 s) e fn-octets)))
                 (t (cons o (fn-wrq-span-decode (1+ s) e fn-octets))))))
       :exec (fn-wrq-span-decode-loop s e fn-octets nil)))

(local
 (defthm fn-wrq-span-decode-loop-is-revappend
   (equal (fn-wrq-span-decode-loop s e fn-octets acc)
          (revappend acc (fn-wrq-span-decode s e fn-octets)))
   :hints (("Goal" :induct (fn-wrq-span-decode-loop s e fn-octets acc)
                   :in-theory (union-theories '(fn-wrq-span-decode-loop fn-wrq-span-decode revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-wrq-span-decode-loop)

(verify-guards fn-wrq-span-decode
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-wrq-span-decode)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-wrq-span-decode-loop-is-revappend (acc nil))))))


(local
 (defthm fn-wrq-slice-open
   (implies (and (natp s) (natp e) (< s e))
            (equal (fn-oct-slice-list s e fn-octets)
                   (cons (nth s fn-octets) (fn-oct-slice-list (1+ s) e fn-octets))))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-wrq-slice-empty
   (implies (or (not (natp s)) (not (natp e)) (<= e s))
            (equal (fn-oct-slice-list s e fn-octets) nil))
   :hints (("Goal" :in-theory (enable fn-oct-slice-list)))))

(defthm fn-wrq-span-decode-is-urldecode
  ; The in-place decoder is the list decoder over the slice.
  (equal (fn-wrq-span-decode s e fn-octets)
         (fn-wrq-urldecode (fn-oct-slice-list s e fn-octets)))
  :hints (("Goal" :induct (fn-wrq-span-decode s e fn-octets)
           :expand ((:free (x y) (fn-wrq-urldecode (cons x y)))
                    (fn-oct-slice-list (+ 1 s) e fn-octets)
                    (fn-oct-slice-list (+ 2 s) e fn-octets)))))

; A body field's decoded value, or :absent (the body is [start, stop)).
(defun fn-web-body-get (name start stop fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp start) (natp stop) (<= start stop)
                              (<= stop (fn-octets-len fn-octets)))))
  (let ((span (fn-wrq-body-span name start stop fn-octets)))
    (if span
        (fn-wrq-span-decode (car span) (cdr span) fn-octets)
      :absent)))

; -----------------------------------------------------------------------------
; Cookies (RFC 6265 5.4: "name=value" pairs separated by "; ").

(defun fn-wrq-drop-sp (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (equal (car xs) 32)) (fn-wrq-drop-sp (cdr xs)) xs))

(defun fn-wrq-cookie-aux (name xs cur-rev)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 59)))
      (fn-wrq-cookie-aux name (cdr xs) (cons (car xs) cur-rev))
    (let ((hit (fn-wrq-field-match name (fn-wrq-drop-sp (fn-wrq-rev cur-rev nil)))))
      (cond ((not (equal hit :no)) hit)
            ((consp xs) (fn-wrq-cookie-aux name (cdr xs) nil))
            (t :absent)))))

; The raw value of the cookie NAME, or :absent.
(defun fn-web-cookie-get (name cookie)
  (declare (xargs :guard t))
  (fn-wrq-cookie-aux name cookie nil))

; -----------------------------------------------------------------------------
; THE ROUTE TABLE.  One row per (method, path):
;
;   (NAME METHOD PATH CAPABILITY MODEL)
;
;   NAME        the route's keyword
;   METHOD      :get or :post (a :get row also answers HEAD, RFC 9110 9.3.2)
;   PATH        the path's octets, compared exactly (the query is separate)
;   CAPABILITY  what books/web-session.lisp checks before MODEL runs:
;                 :none       anyone
;                 :same-site  a POST from this site's own pages (Origin /
;                             Sec-Fetch-Site; the theme switch)
;                 :pre        :same-site, and the form's `pre' field equals
;                             the fnr_pre cookie (sign-in and invitation
;                             forms, before any session: login CSRF)
;                 :session    a live session (else the sign-in page)
;                 :csrf       :same-site, a live session, and the form's
;                             `csrf' field is that session's token
;   MODEL       the function in books/web-session.lisp that serves the row
;
; The same shape as the NNTP table on lane/defprotocol
; (books/protocol-table.lisp: NAME, the dispatcher layer, the model
; function); the codes each row can answer are in web-session's rows.

(defun fn-web-row (name method path capability model)
  (declare (xargs :guard (stringp path)))
  (list name method (fn-wrq-chars-octets (coerce path 'list)) capability model))

(defconst *fn-web-routes*
  (list (fn-web-row :health      :get  "/health"    :none      'fn-whl-answer)
        (fn-web-row :style       :get  "/style.css" :none      'fn-wss-style)
        (fn-web-row :signin-form :get  "/signin"    :none      'fn-wss-signin-form)
        (fn-web-row :signin      :post "/signin"    :pre       'fn-wss-signin)
        (fn-web-row :redeem-form :get  "/redeem"    :none      'fn-wss-redeem-form)
        (fn-web-row :redeem      :post "/redeem"    :pre       'fn-wss-redeem)
        (fn-web-row :theme       :post "/theme"     :same-site 'fn-wss-theme)
        (fn-web-row :groups      :get  "/"          :session   'fn-wss-groups)
        (fn-web-row :group       :get  "/g"         :session   'fn-wss-group)
        (fn-web-row :article     :get  "/a"         :session   'fn-wss-article)
        (fn-web-row :compose     :get  "/new"       :session   'fn-wss-compose)
        (fn-web-row :post        :post "/post"      :csrf      'fn-wss-post)
        (fn-web-row :remove-form :get  "/remove"    :session   'fn-wss-remove-form)
        (fn-web-row :remove      :post "/remove"    :csrf      'fn-wss-remove)
        (fn-web-row :signout     :post "/signout"   :csrf      'fn-wss-signout)))

(defun fn-web-row-name (row) (declare (xargs :guard t)) (fn-wrq-nth 0 row))
(defun fn-web-row-method (row) (declare (xargs :guard t)) (fn-wrq-nth 1 row))
(defun fn-web-row-path (row) (declare (xargs :guard t)) (fn-wrq-nth 2 row))
(defun fn-web-row-capability (row) (declare (xargs :guard t)) (fn-wrq-nth 3 row))
(defun fn-web-row-model (row) (declare (xargs :guard t)) (fn-wrq-nth 4 row))

(defun fn-web-method-matches (method row-method)
  (declare (xargs :guard t))
  (or (equal method row-method)
      (and (equal method :head) (equal row-method :get))))

(defun fn-web-route-aux (method path rows allow)
  ; ALLOW collects the methods of rows with this path (for a 405's Allow).
  (declare (xargs :guard t))
  (if (consp rows)
      (let ((row (car rows)))
        (if (equal (fn-web-row-path row) path)
            (if (fn-web-method-matches method (fn-web-row-method row))
                (list :route row)
              (fn-web-route-aux method path (cdr rows)
                                (cons (fn-web-row-method row) allow)))
          (fn-web-route-aux method path (cdr rows) allow)))
    (if (consp allow)
        (list :refused 405 allow)
      (list :refused 404))))

; (:route ROW), (:refused 405 METHODS) or (:refused 404).
(defun fn-web-route (method path)
  (declare (xargs :guard t))
  (fn-web-route-aux method path *fn-web-routes* nil))

(defthm fn-web-route-aux-is-a-row
  (let ((r (fn-web-route-aux method path rows allow)))
    (implies (equal (car r) :route)
             (and (member-equal (cadr r) rows)
                  (equal (fn-web-row-path (cadr r)) path)
                  (fn-web-method-matches method (fn-web-row-method (cadr r)))))))

(defthm fn-web-route-is-a-row
  ; KEYSTONE (PRF-337): a route is a row of the table, for this path and
  ; this method (HEAD on a GET row).
  (let ((r (fn-web-route method path)))
    (implies (equal (car r) :route)
             (and (member-equal (cadr r) *fn-web-routes*)
                  (equal (fn-web-row-path (cadr r)) path)
                  (fn-web-method-matches method (fn-web-row-method (cadr r))))))
  :hints (("Goal" :in-theory (disable fn-web-route-aux (fn-web-route-aux)
                                      fn-web-route-aux-is-a-row fn-web-method-matches)
           :use ((:instance fn-web-route-aux-is-a-row
                  (rows *fn-web-routes*) (allow nil))))))

(defthm fn-web-route-answers
  (let ((r (fn-web-route method path)))
    (or (equal (car r) :route)
        (and (equal (car r) :refused) (member (cadr r) '(404 405)))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; THE RESPONSE HEAD (RFC 9112 4 and 5).  FIELDS are (NAME . VALUE) pairs of
; octets.  A pair whose name is not a token or whose value is not a field
; value is not written: nothing a caller passes can add a line.  The face's
; own fields follow: the policy that forbids every script and every
; resource from elsewhere, and one request per connection (9.6: the face
; closes after each response).

(defun fn-wrq-tokenp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-wrq-tcharp (car xs))
           (if (consp (cdr xs)) (fn-wrq-tokenp (cdr xs)) (null (cdr xs))))
    nil))

(defun fn-web-field-goodp (f)
  (declare (xargs :guard t))
  (and (consp f) (fn-wrq-tokenp (car f)) (fn-wrq-field-valuep (cdr f))))

(defun fn-web-good-fields (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (fn-web-field-goodp (car fields))
          (cons (car fields) (fn-web-good-fields (cdr fields)))
        (fn-web-good-fields (cdr fields)))
    nil))

(defun fn-web-fields-octets (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (let ((f (if (consp (car fields)) (car fields) (cons nil nil))))
        (append (fn-wrq-true (car f)) (list 58 32) (fn-wrq-true (cdr f)) (list 13 10)
                (fn-web-fields-octets (cdr fields))))
    nil))

(defun fn-web-reason (code)
  (declare (xargs :guard t))
  (case code
    (200 "OK") (303 "See Other") (400 "Bad Request") (401 "Unauthorized")
    (403 "Forbidden") (404 "Not Found") (405 "Method Not Allowed")
    (411 "Length Required") (413 "Content Too Large") (429 "Too Many Requests")
    (431 "Request Header Fields Too Large") (500 "Internal Server Error")
    (501 "Not Implemented") (502 "Bad Gateway") (503 "Service Unavailable")
    (505 "HTTP Version Not Supported")
    (otherwise "Error")))

(defconst *fn-web-csp*
  "default-src 'none'; style-src 'self'; img-src 'self'; form-action 'self'; frame-ancestors 'none'; base-uri 'none'")

(defun fn-web-own-fields (secure)
  (declare (xargs :guard t))
  (append (list (cons (fn-wrq-oct "Content-Security-Policy")
                      (fn-wrq-chars-octets (coerce *fn-web-csp* 'list)))
                (cons (fn-wrq-oct "X-Content-Type-Options") (fn-wrq-oct "nosniff"))
                (cons (fn-wrq-oct "Referrer-Policy") (fn-wrq-oct "same-origin"))
                (cons (fn-wrq-oct "Connection") (fn-wrq-oct "close")))
          (if secure
              (list (cons (fn-wrq-oct "Strict-Transport-Security")
                          (fn-wrq-oct "max-age=31536000")))
            nil)))

; The fields a head carries: the caller's good ones, then the face's own,
; then Content-Length.
(defun fn-web-head-fields (fields clen secure)
  (declare (xargs :guard t))
  (fn-web-good-fields
   (append (fn-wrq-true fields)
           (fn-web-own-fields secure)
           (list (cons (fn-wrq-oct "Content-Length") (fn-ot-decimal-octets clen))))))

; THE HOST-CALLED HEAD (host/native/web-host.lisp fnn-web-respond): the
; status line, the fields, CRLF.
(defun fn-web-response-head (code fields clen secure)
  (declare (xargs :guard t))
  (append (fn-wrq-oct "HTTP/1.1 ")
          (fn-ot-decimal-octets code)
          (list 32)
          (fn-wrq-chars-octets (coerce (fn-web-reason code) 'list))
          (list 13 10)
          (fn-web-fields-octets (fn-web-head-fields fields clen secure))
          (list 13 10)))

(defun fn-wrq-count (o xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (if (equal (car xs) o) 1 0) (fn-wrq-count o (cdr xs)))
    0))

(defthm fn-wrq-count-append
  (equal (fn-wrq-count o (append xs ys))
         (+ (fn-wrq-count o xs) (fn-wrq-count o ys))))

(defthm fn-wrq-count-crlf-of-field-value
  (implies (fn-wrq-field-valuep xs)
           (and (equal (fn-wrq-count 13 xs) 0)
                (equal (fn-wrq-count 10 xs) 0))))

(defthm fn-wrq-count-crlf-of-token
  (implies (fn-wrq-tokenp xs)
           (and (equal (fn-wrq-count 13 xs) 0)
                (equal (fn-wrq-count 10 xs) 0))))

(defthm fn-wrq-field-valuep-true-listp
  (implies (fn-wrq-field-valuep xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-wrq-tokenp-true-listp
  (implies (fn-wrq-tokenp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defun fn-web-all-good (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (fn-web-field-goodp (car fields)) (fn-web-all-good (cdr fields)))
    t))

(defthm fn-web-all-good-of-good-fields
  (fn-web-all-good (fn-web-good-fields fields)))

(defthm fn-web-fields-octets-crlf-count
  (implies (fn-web-all-good fields)
           (and (equal (fn-wrq-count 13 (fn-web-fields-octets fields)) (len fields))
                (equal (fn-wrq-count 10 (fn-web-fields-octets fields)) (len fields)))))

; The decimal renderer (books/octet-text.lisp) emits digits only.
(defthm fn-wrq-count-crlf-of-nat-digits
  (and (equal (fn-wrq-count 13 (fn-ot-nat-digits n r acc)) (fn-wrq-count 13 acc))
       (equal (fn-wrq-count 10 (fn-ot-nat-digits n r acc)) (fn-wrq-count 10 acc)))
  :hints (("Goal" :induct (fn-ot-nat-digits n r acc)
           :in-theory (e/d (fn-ot-nat-digits fn-ot-hex-digit) (floor mod)))))

(defthm fn-web-all-good-of-head-fields
  (fn-web-all-good (fn-web-head-fields fields clen secure)))

(defthm fn-web-response-head-crlf-count
  ; KEYSTONE (PRF-337), response splitting: the head's CR and LF octets are
  ; exactly its own line ends -- the status line's, one per field it
  ; carries, and the empty line -- whatever FIELDS the caller passed.
  (and (equal (fn-wrq-count 13 (fn-web-response-head code fields clen secure))
              (+ 2 (len (fn-web-head-fields fields clen secure))))
       (equal (fn-wrq-count 10 (fn-web-response-head code fields clen secure))
              (+ 2 (len (fn-web-head-fields fields clen secure)))))
  :hints (("Goal" :in-theory (disable fn-web-head-fields fn-web-fields-octets))))

; -----------------------------------------------------------------------------
; The browser's address: what the owner's exposure rules (login pacing,
; per-address connections; books/public-exposure.lisp) see as this
; client.  The socket's peer, unless the operator's profile says a proxy on
; this machine fronts the face (PROXIED) and the peer is loopback: then the
; LAST X-Forwarded-For entry, the one that proxy itself appended (any a
; browser sent is to its left).  An entry that is not an IPv4 or IPv6
; literal leaves the peer.  (FAMILY . OCTETS) as the owner takes it.

(defun fn-wrq-split-on (sep xs cur-rev)
  ; XS split at each SEP, as a list of octet lists.
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) sep)
          (cons (fn-wrq-rev cur-rev nil) (fn-wrq-split-on sep (cdr xs) nil))
        (fn-wrq-split-on sep (cdr xs) (cons (car xs) cur-rev)))
    (list (fn-wrq-rev cur-rev nil))))

(defun fn-wrq-ipv4-part (xs)
  (declare (xargs :guard t))
  (and (consp xs) (fn-wrq-shortp xs 3)
       (let ((v (fn-ot-decimal-parse xs nil))) (and v (<= v 255) v))))

(defun fn-wrq-ipv4-parts (parts)
  (declare (xargs :guard t))
  (if (consp parts)
      (let ((v (fn-wrq-ipv4-part (car parts)))
            (rest (fn-wrq-ipv4-parts (cdr parts))))
        (and v (not (equal rest :bad)) (cons v rest)))
    (if (null parts) nil :bad)))

(defun fn-wrq-ipv4 (xs)
  (declare (xargs :guard t))
  (let ((v (fn-wrq-ipv4-parts (fn-wrq-split-on 46 xs nil))))
    (and (consp v) (equal (len v) 4) v)))

(defun fn-wrq-hex16 (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (consp xs)
      (let ((h (fn-ot-hex-value (car xs))))
        (and h (fn-wrq-hex16 (cdr xs) (+ (* 16 acc) h))))
    acc))

(defun fn-wrq-ipv6-groups (parts)
  ; Each part 1-4 hex digits: its two octets, concatenated; :bad otherwise.
  (declare (xargs :guard t))
  (if (consp parts)
      (let ((v (and (consp (car parts)) (fn-wrq-shortp (car parts) 4)
                    (fn-wrq-hex16 (car parts) 0)))
            (rest (fn-wrq-ipv6-groups (cdr parts))))
        (if (and (natp v) (< v 65536) (not (equal rest :bad)))
            (list* (floor v 256) (mod v 256) rest)
          :bad))
    nil))

(defthm fn-wrq-ipv6-groups-type
  (implies (not (equal (fn-wrq-ipv6-groups parts) :bad))
           (true-listp (fn-wrq-ipv6-groups parts))))

(defun fn-wrq-find-colons (xs before-rev)
  ; (BEFORE . AFTER) around the first "::", or nil.
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (if (and (equal (car xs) 58) (equal (cadr xs) 58))
          (cons (fn-wrq-rev before-rev nil) (cddr xs))
        (fn-wrq-find-colons (cdr xs) (cons (car xs) before-rev)))
    nil))

(defun fn-wrq-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (fn-wrq-zeros (1- n)))))

(defun fn-wrq-ipv6-side (xs)
  (declare (xargs :guard t))
  (if (consp xs) (fn-wrq-ipv6-groups (fn-wrq-split-on 58 xs nil)) nil))

(defthm fn-wrq-ipv6-side-type
  (implies (not (equal (fn-wrq-ipv6-side xs) :bad))
           (true-listp (fn-wrq-ipv6-side xs))))

(in-theory (disable fn-wrq-ipv6-side fn-wrq-find-colons))

(defun fn-wrq-ipv6 (xs)
  (declare (xargs :guard t))
  (let ((cc (fn-wrq-find-colons xs nil)))
    (if (consp cc)
        (let ((l (fn-wrq-ipv6-side (car cc)))
              (r (fn-wrq-ipv6-side (cdr cc))))
          (and (not (equal l :bad)) (not (equal r :bad))
               (not (fn-wrq-find-colons (cdr cc) nil))
               (<= (+ (len l) (len r)) 14)
               (append l (fn-wrq-zeros (- 16 (+ (len l) (len r)))) r)))
      (let ((v (fn-wrq-ipv6-groups (fn-wrq-split-on 58 xs nil))))
        (and (consp v) (equal (len v) 16) v)))))

(defun fn-wrq-trim (xs)
  (declare (xargs :guard t))
  (fn-wrq-rev (fn-wrq-drop-ows (fn-wrq-rev (fn-wrq-drop-ows xs) nil)) nil))

(defun fn-wrq-last (parts)
  (declare (xargs :guard t))
  (if (consp parts)
      (if (consp (cdr parts)) (fn-wrq-last (cdr parts)) (car parts))
    nil))

(defun fn-wrq-loopbackp (family address)
  (declare (xargs :guard t))
  (or (and (equal family :inet) (consp address) (equal (car address) 127))
      (and (equal family :inet6)
           (equal address '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)))))

; THE HOST-CALLED ADDRESS DECISION (host/native/web-host.lisp): the
; (FAMILY . OCTETS) the owner's exposure is opened with for this browser.
(defun fn-web-client-address (family address proxied request)
  (declare (xargs :guard t))
  (let ((peer (cons family address)))
    (if (and proxied (fn-wrq-loopbackp family address))
        (let* ((entry (fn-wrq-trim (fn-wrq-last (fn-wrq-split-on 44 (fn-web-req-xff request) nil))))
               (short (fn-wrq-shortp entry 64))
               (v4 (and short (fn-wrq-ipv4 entry)))
               (v6 (and short (not v4) (fn-wrq-ipv6 entry))))
          (cond (v4 (cons :inet v4))
                (v6 (cons :inet6 v6))
                (t peer)))
      peer)))

(defthm fn-web-client-address-without-proxy-unfolds
  ; Without PROXIED, the address is the socket's peer: no field a browser
  ; sends can choose it.
  (implies (not proxied)
           (equal (fn-web-client-address family address proxied request)
                  (cons family address))))
