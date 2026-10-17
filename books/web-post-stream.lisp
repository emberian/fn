; Authored POST body windows over the retained HTTP request, PRF-1293.
; Logic-mode definitions; guards are not verified and the byte agreement with
; fn-wss-post-head/fn-wss-write-post is established by the tests
; (tests/acl2/web-post-stream-tests.lisp), not by a refinement theorem --
; both are proof-owed.  The keystones at the end state what IS proved: a
; POST is accepted only with its session's CSRF token, a valid group, a
; non-empty subject and body, and to that session's own connection, and
; every other request takes exactly the existing gate's refusal.
(in-package "ACL2")
(include-book "web-session-keystones")

; HEAD REST, encoded offset/end, BOL, pending CR, pending fragment, phase.
(defun fn-wps-cursor (head bs be)
  (declare (xargs :verify-guards nil))
  (list head bs be t nil nil :head))

(defun fn-wps-subject-prefix (fuel xs)
  (declare (xargs :verify-guards nil))
  (if (or (zp fuel) (atom xs)) nil
    (cons (if (member (car xs) '(13 10 9 0)) 32 (car xs))
          (fn-wps-subject-prefix (1- fuel) (cdr xs)))))
(defun fn-wps-header-cursor (login domain group subject ascii bs be)
  (declare (xargs :verify-guards nil))
  (list (append (fn-wss-from-field login domain) (fn-wrq-oct "Newsgroups: ") group
                '(13 10) (fn-wrq-oct "Subject: "))
        bs be t nil nil :head subject ascii
        (append '(13 10) (fn-wrq-oct "MIME-Version: 1.0") '(13 10)
                (fn-wrq-oct "Content-Type: text/plain; charset=utf-8") '(13 10)
                (fn-wrq-oct "Content-Transfer-Encoding: 8bit") '(13 10 13 10))))

(defun fn-wps-next (cursor fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in))
  (let ((head (nth 0 cursor)) (i (nth 1 cursor)) (e (nth 2 cursor))
        (bol (nth 3 cursor)) (pcr (nth 4 cursor)) (pending (nth 5 cursor))
        (phase (nth 6 cursor)))
    (cond
     ((consp pending)
      (mv (car pending) (update-nth 5 (cdr pending) cursor) nil))
     ((equal phase :head)
      (if (consp head)
          (mv (car head) (update-nth 0 (cdr head) cursor) nil)
        (mv nil (update-nth 6 (if (consp (nth 7 cursor)) :subject :body) cursor) nil)))
     ((equal phase :subject)
      (let ((subject (nth 7 cursor)))
        (if (atom subject)
            (mv nil (update-nth 0 (nth 9 cursor) (update-nth 9 nil
                      (update-nth 6 :head cursor))) nil)
          (if (nth 8 cursor)
              (mv (if (member (car subject) '(13 10 9 0)) 32 (car subject))
                  (update-nth 7 (cdr subject) cursor) nil)
            (let* ((cut (fn-wss-utf8-take (fn-wps-subject-prefix 46 subject) 45 nil))
                   (rest (nthcdr (len (car cut)) subject))
                   (word (append (fn-wrq-oct "=?UTF-8?B?")
                                 (fn-wss-b64 (car cut) nil t) (fn-wrq-oct "?=")
                                 (if (consp rest) '(13 10 32) nil))))
              (mv nil (update-nth 5 word (update-nth 7 rest cursor)) nil))))))
     ((equal phase :body)
      (if (>= i e)
          (mv nil (update-nth 5 (append (if (or pcr (not bol)) '(13 10) nil) '(46 13 10))
                   (update-nth 6 :tail cursor)) nil)
        (let* ((d (fn-wss-decode-at i e fn-web-in)) (o (car d)))
          (if (and pcr (not (equal o 10)))
              ; Flush the pending CR without consuming this decoded octet.
              (mv nil (update-nth 5 '(13 10)
                       (update-nth 3 t (update-nth 4 nil cursor))) nil)
            (let* ((b (if pcr t bol))
                   (bytes (if pcr '(13 10) (fn-wss-step-octets o b))))
              (mv nil (list head (cdr d) e (fn-wss-step-bol o b)
                            (fn-wss-step-pcr o) bytes phase) nil))))))
     (t (mv nil cursor t)))))

(defun fn-wps-window (fuel cursor acc fn-web-in)
  ; One transition per work unit; zero-output CR/phase transitions also pay.
  ; At most FUEL octets and one <=75-byte RFC2047 fragment, including quantum one.
  (declare (xargs :verify-guards nil :stobjs fn-web-in))
  (if (zp fuel) (mv (reverse acc) cursor nil)
    (mv-let (o next done) (fn-wps-next cursor fn-web-in)
      (if done (mv (reverse acc) next t)
        (fn-wps-window (1- fuel) next (if o (cons o acc) acc) fn-web-in)))))

(local (defthm fn-wps-len-revappend
  (equal (len (revappend a b)) (+ (len a) (len b)))))

(defthm fn-wps-window-emits-at-most-fuel
  ; One host call (fuel 4096) emits at most FUEL octets; the at most one
  ; pending RFC 2047 fragment rides in the cursor, not the window.
  (<= (len (mv-nth 0 (fn-wps-window fuel cursor acc fn-web-in)))
      (+ (len acc) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-wps-next))))

(defun fn-wps-private-reply (config flow event cursor fn-web-in fn-web-out)
  (declare (xargs :verify-guards nil :stobjs (fn-web-in fn-web-out)))
  (if (and cursor (equal (fn-wss-f-route flow) :post)
           (equal (fn-wss-f-stage flow) :posting)
           (equal (fn-wss-reply-code (fn-wss-reply 0 fn-web-in)) 340))
      (mv (list :post-stream (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                (fn-wss-flow :post :article (fn-wss-f-ctx flow) (fn-wss-f-data flow))) fn-web-out)
    (fn-web-private-reply-step config flow event fn-web-in fn-web-out)))

; One form traversal. Raw names are at most seven octets; values remain spans.
(defun fn-wpf-start (action)
  (declare (xargs :verify-guards nil))
  (let ((ctx (nth 3 action)))
    (list action (fn-wss-c-bs ctx) (fn-wss-c-be ctx) nil nil
          (list nil nil nil nil) :scan 0 nil nil nil)))
(defun fn-wpf-store (name start end spans)
  (declare (xargs :verify-guards nil))
  (let ((index (cond ((equal name (fn-wrq-oct "csrf")) 0)
                     ((equal name (fn-wrq-oct "g")) 1)
                     ((equal name (fn-wrq-oct "subject")) 2)
                     ((equal name (fn-wrq-oct "body")) 3)
                     (t nil))))
    (if (and index start (not (nth index spans)))
        (update-nth index (cons start end) spans) spans)))
(defun fn-wpf-step (p fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in))
  (let* ((at (nth 1 p)) (end (nth 2 p)) (name (nth 3 p)) (start (nth 4 p))
         (spans (nth 5 p)) (phase (nth 6 p)) (index (nth 7 p))
         (pos (nth 8 p)) (rev (nth 9 p)) (vals (nth 10 p)))
    (cond
     ((equal phase :scan)
      (if (>= at end)
          (let ((spans (fn-wpf-store (reverse name) start at spans)))
            (mv (list (nth 0 p) at end nil nil spans :decode 0 nil nil nil) nil))
        (let ((o (fn-octets-get at fn-web-in)))
          (cond ((equal o 38)
                 (mv (list (nth 0 p) (1+ at) end nil nil
                           (fn-wpf-store (reverse name) start at spans) phase index pos rev vals) nil))
                ((and (not start) (equal o 61))
                 (mv (update-nth 4 (1+ at) (update-nth 1 (1+ at) p)) nil))
                (t (mv (update-nth 3 (if start name
                                        (if (< (len name) 8) (cons o name) name))
                                  (update-nth 1 (1+ at) p)) nil))))))
     ((equal phase :decode)
      (if (>= index 3)
          (mv (update-nth 6 :subject-check
                (update-nth 8 (nth 2 vals) (update-nth 11 t p))) nil)
        (let* ((span (nth index spans)) (i (if pos pos (car span))) (e (cdr span)))
          (if (or (not span) (>= i e))
              (mv (update-nth 6 :reverse (update-nth 11 nil p)) nil)
            (let ((d (fn-wss-decode-at i e fn-web-in)))
              (mv (update-nth 8 (cdr d) (update-nth 9 (cons (car d) rev) p)) nil))))))
     ((equal phase :reverse)
      (if (consp rev)
          (mv (update-nth 9 (cdr rev)
                (update-nth 11 (cons (car rev) (nth 11 p)) p)) nil)
        (mv (update-nth 6 :decode (update-nth 7 (1+ index)
              (update-nth 8 nil (update-nth 10 (append vals (list (nth 11 p))) p)))) nil)))
     ((equal phase :subject-check)
      (if (atom pos) (mv p t)
        (let ((o (if (member (car pos) '(13 10 9 0)) 32 (car pos))))
          (mv (update-nth 8 (cdr pos) (update-nth 11
                (and (nth 11 p) (<= 32 o) (<= o 126)) p)) nil))))
     (t (mv p t)))))
(defun fn-wpf-drive (fuel p fn-web-in)
  (declare (xargs :verify-guards nil :stobjs fn-web-in))
  (if (zp fuel) (mv p nil)
    (mv-let (next done) (fn-wpf-step p fn-web-in)
      (if done (mv next t) (fn-wpf-drive (1- fuel) next fn-web-in)))))
(defun fn-wpf-finish (config p fn-web-in fn-web-out)
  (declare (xargs :verify-guards nil :stobjs (fn-web-in fn-web-out)))
  (let* ((action (nth 0 p)) (session (nth 2 action)) (ctx (nth 3 action))
         (vals (nth 10 p)) (csrf (nth 0 vals)) (group (nth 1 vals))
         (subject (nth 2 vals)) (span (nth 3 (nth 5 p))))
    (if (and (equal csrf (fn-wss-s-csrf session)) (fn-wss-groupp group)
             (consp subject) (consp span) (< (car span) (cdr span)))
        (let* ((cursor (fn-wps-header-cursor (fn-wss-s-login session)
                                             (fn-wss-cfg-domain config) group subject
                                             (nth 11 p) (car span) (cdr span)))
               (fn-web-out (fn-octets-clear fn-web-out))
               (fn-web-out (fn-octets-append-list '(80 79 83 84 13 10) fn-web-out)))
          (mv (list :post-command (fn-wss-s-cid session)
                    cursor
                    (fn-wss-flow :post :posting ctx (list group nil))) fn-web-out))
      ; Preserve the exact existing refusal/page behavior, currently full.
      (fn-web-private-begin-step config action fn-web-in fn-web-out))))
(defun fn-wpf-private-begin (config action fn-web-in fn-web-out)
  (declare (xargs :verify-guards nil :stobjs (fn-web-in fn-web-out)))
  (let* ((row (nth 1 action)) (session (nth 2 action)) (ctx (nth 3 action)))
    (if (and (fn-web-private-begin-p action) (equal (fn-web-row-name row) :post)
             session (fn-wss-same-site (fn-wss-c-request ctx))
             (<= (fn-wss-c-bs ctx) (fn-wss-c-be ctx))
             (<= (fn-wss-c-be ctx) (fn-octets-len fn-web-in)))
        (mv (list :post-form (fn-wpf-start action)) fn-web-out)
      (fn-web-private-begin-step config action fn-web-in fn-web-out))))

; ---------------------------------------------------------------------------
; Accepted and refused stay distinct.

(defthm fn-wpf-finish-refusal-is-the-existing-gate
  ; A form whose CSRF token is not its session's, or whose group, subject or
  ; body is unusable, is answered exactly as the full gate answers it.
  (implies (not (and (equal (nth 0 (nth 10 p)) (fn-wss-s-csrf (nth 2 (nth 0 p))))
                     (fn-wss-groupp (nth 1 (nth 10 p)))
                     (consp (nth 2 (nth 10 p)))
                     (consp (nth 3 (nth 5 p)))
                     (< (car (nth 3 (nth 5 p))) (cdr (nth 3 (nth 5 p))))))
           (equal (fn-wpf-finish config p fn-web-in fn-web-out)
                  (fn-web-private-begin-step config (nth 0 p) fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wpf-finish) (theory 'minimal-theory)))))


(defthm fn-wpf-finish-accepts-to-its-session
  ; Accepted: the POST command goes to the session's own connection, with
  ; the posting flow, and the outgoing buffer holds exactly "POST" CR LF.
  (implies (and (equal (nth 0 (nth 10 p)) (fn-wss-s-csrf (nth 2 (nth 0 p))))
                (fn-wss-groupp (nth 1 (nth 10 p)))
                (consp (nth 2 (nth 10 p)))
                (consp (nth 3 (nth 5 p)))
                (< (car (nth 3 (nth 5 p))) (cdr (nth 3 (nth 5 p)))))
           (let ((action (mv-nth 0 (fn-wpf-finish config p fn-web-in fn-web-out))))
             (and (equal (car action) :post-command)
                  (equal (cadr action) (fn-wss-s-cid (nth 2 (nth 0 p))))
                  (equal (fn-octets-list (mv-nth 1 (fn-wpf-finish config p fn-web-in fn-web-out)))
                         '(80 79 83 84 13 10)))))
  :hints (("Goal" :in-theory (e/d (fn-wpf-finish)
                                  (fn-web-private-begin-step fn-wps-header-cursor fn-wss-groupp
                                   fn-wss-s-csrf fn-wss-s-cid fn-wss-flow)))))


(defthm fn-wpf-private-begin-refusal-is-the-existing-gate
  ; Not a captured POST gate, no session, cross-site, or a body span outside
  ; the request: the full gate's answer, unchanged.
  (implies (not (and (fn-web-private-begin-p action)
                     (equal (fn-web-row-name (nth 1 action)) :post)
                     (nth 2 action)
                     (fn-wss-same-site (fn-wss-c-request (nth 3 action)))
                     (<= (fn-wss-c-bs (nth 3 action)) (fn-wss-c-be (nth 3 action)))
                     (<= (fn-wss-c-be (nth 3 action)) (fn-octets-len fn-web-in))))
           (equal (fn-wpf-private-begin config action fn-web-in fn-web-out)
                  (fn-web-private-begin-step config action fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wpf-private-begin) (theory 'minimal-theory)))))


(defthm fn-wps-private-reply-streams-only-after-340
  ; The body is streamed only after the server's 340 to this flow's POST;
  ; any other reply is the existing private reply step's.
  (implies (not (and cursor (equal (fn-wss-f-route flow) :post)
                     (equal (fn-wss-f-stage flow) :posting)
                     (equal (fn-wss-reply-code (fn-wss-reply 0 fn-web-in)) 340)))
           (equal (fn-wps-private-reply config flow event cursor fn-web-in fn-web-out)
                  (fn-web-private-reply-step config flow event fn-web-in fn-web-out)))
  :hints (("Goal" :in-theory (union-theories '(fn-wps-private-reply) (theory 'minimal-theory)))))
