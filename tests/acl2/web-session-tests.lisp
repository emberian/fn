; Witnesses and teeth for books/web-session.lisp and
; books/web-session-keystones.lisp (lane web-native, PRF-339).  Every
; request is driven as host/native/web-host.lisp drives it: framed and
; parsed by books/web-request.lisp, then fn-web-step event by event, with
; a scripted node answering each :open and :send (the replies are what the
; owner's served step renders for those commands).
(in-package "ACL2")
(include-book "../../books/web-session-keystones")
(include-book "must-fail-checked")

(defun wsst-octs (s) (declare (xargs :guard (stringp s))) (fn-wrq-chars-octets (coerce s 'list)))
(defun wsst-crlf (lines) (declare (xargs :guard (string-listp lines)))
  (if (consp lines) (append (wsst-octs (car lines)) (list 13 10) (wsst-crlf (cdr lines))) nil))

; Drive one request: the host's loop, with a scripted node.  OPENS: the
; cids :open answers, in order; REPLIES: the reply octets each :send gets.
; Answers (ACTIONS SESSIONS PAGE SENT), SENT the octets each send carried.
(defun wsst-loop (fuel config sessions flow event opens replies actions sent fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :mode :program))
  (if (zp fuel)
      (mv (list :out-of-fuel (reverse actions) sessions nil (reverse sent)) fn-web-in fn-web-out)
    (mv-let (action sessions fn-web-out)
      (fn-web-step config sessions flow event fn-web-in fn-web-out)
      (let ((actions (cons action actions)))
        (case (car action)
          (:respond (mv (list (reverse actions) sessions (fn-octets-list fn-web-out) (reverse sent))
                        fn-web-in fn-web-out))
          (:open (wsst-loop (1- fuel) config sessions (car (last action)) (list :opened (car opens))
                            (cdr opens) replies actions sent fn-web-in fn-web-out))
          (:close (wsst-loop (1- fuel) config sessions (car (last action)) (list :closed)
                             opens replies actions sent fn-web-in fn-web-out))
          (:send (let* ((whole (fn-octets-list fn-web-out))
                        (piece (take (- (fourth action) (third action)) (nthcdr (third action) whole)))
                        (fn-web-in (fn-octets-from-list (car replies) fn-web-in)))
                   (wsst-loop (1- fuel) config sessions (car (last action)) (list :reply)
                              opens (cdr replies) actions (cons piece sent) fn-web-in fn-web-out)))
          (otherwise (mv (list :bad action) fn-web-in fn-web-out)))))))

(defun wsst-request (req-octets config sessions now tls opens replies)
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let* ((fn-web-in (fn-octets-from-list req-octets fn-web-in))
                 (limits (fn-wrq-limits 16384 100000))
                 (f (fn-web-head-frame 0 limits fn-web-in))
                 (p (fn-web-parse-head (cadr f) limits fn-web-in)))
            (if (not (equal (car p) :request))
                (mv p fn-web-in fn-web-out)
              (wsst-loop 20 config sessions nil
                         (list :begin (cadr p) (cadr f) (+ (cadr f) (fn-web-req-clen (cadr p)))
                               now (wsst-octs "nonce-one-nonce-one-nonce-one-12")
                               (wsst-octs "nonce-two-nonce-two-nonce-two-12") tls :inet '(127 0 0 1))
                         opens replies nil nil fn-web-in fn-web-out)))
          (mv r fn-web-in)))
      r)))

(defun wsst-chars (xs) (declare (xargs :mode :program))
  (if (consp xs) (cons (code-char (car xs)) (wsst-chars (cdr xs))) nil))
(defun wsst-str (xs) (declare (xargs :mode :program)) (coerce (wsst-chars xs) 'string))

(defconst *cfg* (fn-web-config (wsst-octs "Friends news") (wsst-octs "news.example") t 43200 64))

; --- A new visitor is sent to the sign-in page (no :send, no :open).
(defconst *r1* (wsst-request (wsst-crlf (list "GET /g?name=x HTTP/1.1" "Host: a" "")) *cfg* nil 100 nil nil nil))
(assert-event (equal (car (car *r1*)) (list :respond 303
  (list (cons (wsst-octs "Location") (wsst-octs "/signin?next=%2Fg%3Fname%3Dx"))
        (cons (wsst-octs "Cache-Control") (wsst-octs "no-store")))
  t)))

; --- Sign in: the node's AUTHINFO pair, one feed; 281 makes the session.
(defconst *body* "pre=abcdefghijklmnopqrstuvwxyz&next=%2Fg%3Fname%3Dx&user=carol&password=s3cret")
(defun wsst-post-req (path cookie body) (declare (xargs :mode :program))
  (append (wsst-crlf (list (concatenate 'string "POST " path " HTTP/1.1") "Host: a" "Origin: http://a"
                           (concatenate 'string "Cookie: " cookie)
                           (concatenate 'string "Content-Length: " (coerce (explode-atom (length body) 10) 'string))
                           ""))
          (wsst-octs body)))
(defconst *r2* (wsst-request (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*)
                             *cfg* nil 100 nil '(7) (list (wsst-crlf (list "381 more" "281 ok")))))
(assert-event (equal (car (nth 0 (car *r2*))) :open))
(assert-event (equal (nth 3 *r2*) (list (wsst-crlf (list "AUTHINFO USER carol" "AUTHINFO PASS s3cret")))))
(assert-event (equal (nth 1 *r2*)
                     (list (list (fn-wss-token (wsst-octs "nonce-one-nonce-one-nonce-one-12")) 7
                                 (wsst-octs "carol")
                                 (fn-wss-token (wsst-octs "nonce-two-nonce-two-nonce-two-12")) 100))))
(assert-event (equal (car (car (last (car *r2*)))) :respond))
; the password is on no page and in no session
(assert-event (not (member-equal (wsst-octs "s3cret") (nth 1 *r2*))))

; A wrong password: the node's 481; the connection is closed; 401 in plain words.
(defconst *r2b* (wsst-request (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*)
                              *cfg* nil 100 nil '(8) (list (wsst-crlf (list "381 more" "481 no")))))
(assert-event (and (equal (nth 1 *r2b*) nil)
                   (equal (car (nth 2 (car *r2b*))) :close)
                   (equal (cadr (car (last (car *r2b*)))) 401)))
; The owner refused the connection (the exposure's per-address limit): 429.
(defconst *r2c* (wsst-request (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*)
                              *cfg* nil 100 nil '(nil) nil))
(assert-event (equal (cadr (car (last (car *r2c*)))) 429))
; No fnr_pre cookie: 400, nothing opened.
(defconst *r2d* (wsst-request (wsst-post-req "/signin" "x=y" *body*) *cfg* nil 100 nil nil nil))
(assert-event (and (equal (len (car *r2d*)) 1) (equal (cadr (car (car *r2d*))) 400)))

(defconst *ss* (nth 1 *r2*))
(defconst *tok* (car (car *ss*)))
(defconst *csrf* (nth 3 (car *ss*)))
(defun wsst-get (path) (declare (xargs :mode :program))
  (wsst-crlf (list (concatenate 'string "GET " path " HTTP/1.1") "Host: a"
                   (concatenate 'string "Cookie: fnr_session=" (wsst-str *tok*)) "")))

; --- The group: GROUP then OVER of the window, on the session's cid 7.
(defconst *g* (wsst-request (wsst-get "/g?name=local.general") *cfg* *ss* 200 nil nil
  (list (wsst-crlf (list "211 2 1 2 local.general"))
        (append (wsst-crlf (list "224 overview follows"))
                (wsst-octs "1	Welcome <b>here</b>	op <op@x>	27 Sep 2026	<a@x>		10	1") '(13 10)
                (wsst-octs "2	Hello from carol	carol <carol@news.example>	28 Sep 2026	<b@x>		10	1") '(13 10)
                (wsst-crlf (list "."))))))
(assert-event (and (equal (nth 3 *g*) (list (wsst-crlf (list "GROUP local.general")) (wsst-crlf (list "OVER 1-2"))))
                   (equal (cadr (nth 0 (car *g*))) 7)
                   (equal (cadr (nth 1 (car *g*))) 7)))
(assert-event (search "Welcome &lt;b&gt;here&lt;/b&gt;" (wsst-str (nth 2 *g*))))
(assert-event (search "<a class='title' href='/a?g=local.general&amp;n=2'>Hello from carol</a>"
                      (wsst-str (nth 2 *g*))))
; The From column is the display name (fn-wss-name-span), never the whole
; mailbox: "op <op@x>" shows "op", "carol <carol@news.example>" "carol".
(assert-event (and (search "<td class='from'>op</td>" (wsst-str (nth 2 *g*)))
                   (search "<td class='from'>carol</td>" (wsst-str (nth 2 *g*)))
                   (not (search "op@x" (wsst-str (nth 2 *g*))))
                   (not (search "carol@news.example" (wsst-str (nth 2 *g*))))))

; --- Every shape of From (RFC 5322 3.4): a quoted phrase loses its quotes, a
; bare angle-addr shows the address inside, a bare addr-spec shows whole,
; blanks before "<" are dropped, an encoded-word phrase is decoded, and an
; empty "<>" shows nothing; the subject and date columns are untouched.
(defconst *g2* (wsst-request (wsst-get "/g?name=local.general") *cfg* *ss* 200 nil nil
  (list (wsst-crlf (list "211 6 1 6 local.general"))
        (append (wsst-crlf (list "224 overview follows"))
                (wsst-octs "1	one	\"Ada L.\" <ada@x>	27 Sep 2026	<a1@x>		10	1") '(13 10)
                (wsst-octs "2	two	<bare@x>	27 Sep 2026	<a2@x>		10	1") '(13 10)
                (wsst-octs "3	three	plain@x	27 Sep 2026	<a3@x>		10	1") '(13 10)
                (wsst-octs "4	four	Bob   <bob@x>	27 Sep 2026	<a4@x>		10	1") '(13 10)
                (wsst-octs "5	five	=?UTF-8?Q?Gr=C3=BC=C3=9Fe?= <g@x>	27 Sep 2026	<a5@x>		10	1") '(13 10)
                (wsst-octs "6	six	<>	27 Sep 2026	<a6@x>		10	1") '(13 10)
                (wsst-crlf (list "."))))))
(assert-event (let ((page (wsst-str (nth 2 *g2*))))
                (and (search "<td class='from'>Ada L.</td>" page)
                     (search "<td class='from'>bare@x</td>" page)
                     (search "<td class='from'>plain@x</td>" page)
                     (search "<td class='from'>Bob</td>" page)
                     ; the decoded phrase, its UTF-8 octets written as they are
                     (search (concatenate 'string "<td class='from'>"
                                          (wsst-str (list 71 114 195 188 195 159 101)) "</td>")
                             page)
                     (search "<td class='from'></td>" page)
                     (search "'>four</a></td>" page)
                     (search "<td class='date'>27 Sep 2026</td>" page)
                     (not (search "ada@x" page))
                     (not (search "bob@x" page)))))

; The narrowing is a span of the field's span (fn-wss-name-span-is-a-span):
; the executable check on the six fields above, and its teeth: a span past
; the buffer is answered as it came, never widened.  (with-local-stobj lives
; in a function, never at the top level.)
(defun wsst-name-spans-ok ()
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (ok fn-web-in)
      (let* ((in (append (wsst-octs "\"Ada L.\" <ada@x>") (wsst-octs "|<bare@x>|plain@x|Bob   <bob@x>|<>")))
             (fn-web-in (fn-octets-from-list in fn-web-in))
             (n (len in)))
        (mv (and (equal (fn-wss-name-span (cons 0 16) fn-web-in) (cons 1 7))
                 (equal (fn-wss-name-span (cons 17 25) fn-web-in) (cons 18 24))
                 (equal (fn-wss-name-span (cons 26 33) fn-web-in) (cons 26 33))
                 (equal (fn-wss-name-span (cons 34 47) fn-web-in) (cons 34 37))
                 (equal (fn-wss-name-span (cons 48 50) fn-web-in) (cons 49 49))
                 (fn-wss-spanp (fn-wss-name-span (cons 0 16) fn-web-in) n)
                 (equal (fn-wss-name-span (cons 0 (+ n 5)) fn-web-in) (cons 0 (+ n 5)))
                 (equal (fn-wss-name-span :not-a-span fn-web-in) :not-a-span))
            fn-web-in))
      ok)))
(assert-event (wsst-name-spans-ok))

; --- The article, un-stuffed and escaped; carol's own: "Remove my post".
(defconst *a* (wsst-request (wsst-get "/a?g=local.general&n=2") *cfg* *ss* 200 nil nil
  (list (wsst-crlf (list "211 2 1 2 local.general" "220 2 <b@x> article"
                         "Path: x" "From: carol <carol@news.example>" "Subject: Hello from carol"
                         "Message-ID: <b@x>" "" "..dot line" "My first post, <from> the browser." ".")))))
(assert-event (and (search "<pre class='body'>.dot line" (wsst-str (nth 2 *a*)))
                   (search "My first post, &lt;from&gt; the browser." (wsst-str (nth 2 *a*)))))
(assert-event (search "Remove my post" (wsst-str (nth 2 *a*))))
; The article page keeps the whole From line (the narrowing is the index's).
(assert-event (search "carol &lt;carol@news.example&gt;" (wsst-str (nth 2 *a*))))

; --- An article the node does not have: the page's line is ARTICLE's own
; refusal (423), never GROUP's 211 that preceded it (fn-wss-trouble-at).
(defconst *a423* (wsst-request (wsst-get "/a?g=local.general&n=9") *cfg* *ss* 200 nil nil
  (list (wsst-crlf (list "211 2 1 2 local.general" "423 no such article number in this group")))))
(assert-event (and (equal (car (car (last (car *a423*)))) :respond)
                   (equal (cadr (car (last (car *a423*)))) 404)
                   (search "That post isn&#39;t here" (wsst-str (nth 2 *a423*)))
                   (search "423 no such article number in this group" (wsst-str (nth 2 *a423*)))
                   (not (search "211 2 1 2" (wsst-str (nth 2 *a423*))))))
; And when GROUP itself refused (411), that line is the one shown.
(defconst *a411* (wsst-request (wsst-get "/a?g=local.general&n=9") *cfg* *ss* 200 nil nil
  (list (wsst-crlf (list "411 no such newsgroup")))))
(assert-event (and (equal (cadr (car (last (car *a411*)))) 404)
                   (search "411 no such newsgroup" (wsst-str (nth 2 *a411*)))))

; --- A post: "POST" alone, then (after 340) the authored article; the
; body's "." line and ".QUIT" line are stuffed.
(defconst *p* (wsst-request (wsst-post-req "/post" (concatenate 'string "fnr_session=" (wsst-str *tok*))
  (concatenate 'string "csrf=" (wsst-str *csrf*)
               "&g=local.general&subject=Gr%C3%BC%C3%9Fe+%E2%9C%93&body=line+one%0D%0A.%0D%0A.QUIT%0D%0Alast"))
  *cfg* *ss* 300 nil nil (list (wsst-crlf (list "340 send it")) (wsst-crlf (list "240 article received")))))
(assert-event (equal (nth 3 *p*)
  (list (wsst-crlf (list "POST"))
        (wsst-crlf (list "From: carol <carol@news.example>" "Newsgroups: local.general"
                         "Subject: =?UTF-8?B?R3LDvMOfZSDinJM=?=" "MIME-Version: 1.0"
                         "Content-Type: text/plain; charset=utf-8" "Content-Transfer-Encoding: 8bit" ""
                         "line one" ".." "..QUIT" "last" ".")))))
(assert-event (search "Posted!" (wsst-str (nth 2 *p*))))
; A form without the session's CSRF token: 403, nothing sent.
(defconst *pbad* (wsst-request (wsst-post-req "/post" (concatenate 'string "fnr_session=" (wsst-str *tok*))
                                              "csrf=wrong&g=local.general&subject=x&body=y")
                               *cfg* *ss* 300 nil nil nil))
(assert-event (and (equal (len (car *pbad*)) 1) (equal (cadr (car (car *pbad*))) 403)))
; From another site: 403.
(defconst *pforeign*
  (wsst-request (append (wsst-crlf (list "POST /post HTTP/1.1" "Host: a" "Origin: http://evil.example"
                                         (concatenate 'string "Cookie: fnr_session=" (wsst-str *tok*))
                                         "Content-Length: 4" "")) (wsst-octs "a=bc"))
                *cfg* *ss* 300 nil nil nil))
(assert-event (equal (cadr (car (car *pforeign*))) 403))

; --- A removal: the cancel, then STAT: 430 means removed.
(defconst *rm* (wsst-request (wsst-post-req "/remove" (concatenate 'string "fnr_session=" (wsst-str *tok*))
  (concatenate 'string "csrf=" (wsst-str *csrf*) "&g=local.general&id=%3Cb%40x%3E"))
  *cfg* *ss* 300 nil nil (list (wsst-crlf (list "340 send it")) (wsst-crlf (list "240 ok"))
                               (wsst-crlf (list "430 no such article")))))
(assert-event (equal (nth 2 (nth 3 *rm*)) (wsst-crlf (list "STAT <b@x>"))))
(assert-event (search "Your post has been removed" (wsst-str (nth 2 *rm*))))

; --- Idle expiry: the next request after the idle time closes the
; session's connection and is sent to sign in.
(defconst *late* (wsst-request (wsst-get "/") *cfg* *ss* (+ 101 43200) nil nil nil))
(assert-event (and (equal (car (nth 0 (car *late*))) :close)
                   (equal (cadr (nth 0 (car *late*))) 7)
                   (equal (nth 1 *late*) nil)
                   (equal (cadr (car (last (car *late*)))) 303)))

; --- Make an account: XREDEEM, close, AUTHINFO on a new connection.
(defconst *rd* (wsst-request (wsst-post-req "/redeem" "fnr_pre=abcdefghijklmnopqrstuvwxyz"
                   "pre=abcdefghijklmnopqrstuvwxyz&code=c0ffee&user=dave&password=pw1&again=pw1") ; FAKE-SECRET
                 *cfg* nil 100 nil '(3 4)
                 (list (wsst-crlf (list "381 send the password with XREDEEM PASS"
                                        "281 account bound; authenticate with AUTHINFO on a new connection"))
                       (wsst-crlf (list "381 more" "281 ok")))))
(assert-event (equal (nth 3 *rd*) (list (wsst-crlf (list "XREDEEM c0ffee dave" "XREDEEM PASS pw1"))
                                        (wsst-crlf (list "AUTHINFO USER dave" "AUTHINFO PASS pw1")))))
; the session is dave's, on the second connection (the defect the keystone
; fn-web-sessions-bound-by-281 found bound LOGIN to the connection id)
(assert-event (and (equal (nth 1 (car (nth 1 *rd*))) 4)
                   (equal (nth 2 (car (nth 1 *rd*))) (wsst-octs "dave"))))

; =============================================================================
; The keystones' teeth.  One step, as the host calls it.
(defun wsst-step (config sessions flow event in)
  (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (with-local-stobj fn-web-out
        (mv-let (r fn-web-in fn-web-out)
          (let ((fn-web-in (fn-octets-from-list in fn-web-in)))
            (mv-let (action sessions fn-web-out)
              (fn-web-step config sessions flow event fn-web-in fn-web-out)
              (mv (list action sessions) fn-web-in fn-web-out)))
          (mv r fn-web-in)))
      r)))

; A parsed request and its :begin event (the request's octets are the buffer).
(defun wsst-begin (req now) (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let* ((fn-web-in (fn-octets-from-list req fn-web-in))
             (limits (fn-wrq-limits 16384 100000))
             (f (fn-web-head-frame 0 limits fn-web-in))
             (p (fn-web-parse-head (cadr f) limits fn-web-in)))
        (mv (list :begin (cadr p) (cadr f) (+ (cadr f) (fn-web-req-clen (cadr p))) now
                  (wsst-octs "nonce-one-nonce-one-nonce-one-12")
                  (wsst-octs "nonce-two-nonce-two-nonce-two-12") nil :inet '(127 0 0 1))
            fn-web-in))
      r)))

(defconst *ev-g* (wsst-begin (wsst-get "/g?name=local.general") 200))
(defconst *ev-g-anon* (wsst-begin (wsst-crlf (list "GET /g?name=local.general HTTP/1.1" "Host: a" "")) 200))
(defconst *st-g* (wsst-step *cfg* *ss* nil *ev-g* (wsst-get "/g?name=local.general")))
(defconst *st-g-anon* (wsst-step *cfg* *ss* nil *ev-g-anon*
                                 (wsst-crlf (list "GET /g?name=local.general HTTP/1.1" "Host: a" ""))))

; --- KEYSTONE fn-web-session-route-needs-its-session.  Reached witness:
; the anonymous GET /g (every hypothesis holds; the action is a response).
(assert-event (and (equal (fn-wss-car *ev-g-anon*) :begin)
                   (member (fn-web-row-capability (fn-web-begin-row *ev-g-anon*)) '(:session :csrf))
                   (not (fn-web-begin-session *cfg* *ss* *ev-g-anon*))
                   (not (member (car (car *st-g-anon*)) '(:send :open)))))
; Without "no session": carol's GET /g sends GROUP.
(assert-event (and (fn-web-begin-session *cfg* *ss* *ev-g*)
                   (equal (car (car *st-g*)) :send)))
(must-fail-checked
 (defthm wsst-tooth-needs-no-session
   (implies (and (equal (fn-wss-car event) :begin)
                 (member (fn-web-row-capability (fn-web-begin-row event)) '(:session :csrf)))
            (not (member (car (car (fn-web-step config sessions flow event fn-web-in fn-web-out)))
                         '(:send :open))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step)))))
; Without the capability: the anonymous sign-in POST opens a connection.
(defconst *ev-si* (wsst-begin (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*) 100))
(defconst *st-si* (wsst-step *cfg* nil nil *ev-si*
                             (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*)))
(assert-event (and (not (member (fn-web-row-capability (fn-web-begin-row *ev-si*)) '(:session :csrf)))
                   (not (fn-web-begin-session *cfg* nil *ev-si*))
                   (equal (car (car *st-si*)) :open)))
(must-fail-checked
 (defthm wsst-tooth-needs-capability
   (implies (and (equal (fn-wss-car event) :begin)
                 (not (fn-web-begin-session config sessions event)))
            (not (member (car (car (fn-web-step config sessions flow event fn-web-in fn-web-out)))
                         '(:send :open))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step)))))
; Without :begin: a group flow's continuation (a GROUP reply) sends OVER.
(defconst *flow-g* (fn-wss-flow :group :group (nth 2 (nth 4 (car *st-g*))) (list (wsst-octs "local.general") nil)))
(defconst *st-g2* (wsst-step *cfg* *ss* *flow-g* '(:reply) (wsst-crlf (list "211 2 1 2 local.general"))))
(assert-event (and (not (equal (fn-wss-car '(:reply)) :begin))
                   (equal (car (car *st-g2*)) :send)))
(must-fail-checked
 (defthm wsst-tooth-needs-begin
   (implies (and (member (fn-web-row-capability (fn-web-begin-row event)) '(:session :csrf))
                 (not (fn-web-begin-session config sessions event)))
            (not (member (car (car (fn-web-step config sessions flow event fn-web-in fn-web-out)))
                         '(:send :open))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step)))))

; --- KEYSTONE fn-web-session-sends-only-to-its-connection.  Reached
; witnesses: carol's GET /g (first conjunct) and its continuation (second).
(assert-event (fn-web-sends-to (car *st-g*)
                               (fn-wss-s-cid (fn-web-begin-session *cfg* *ss* *ev-g*))
                               (fn-web-begin-session *cfg* *ss* *ev-g*)))
(assert-event (and (equal (nth 1 (car *st-g*)) 7) (equal (car (car *st-g*)) :send)))
(assert-event (and (member (fn-wss-f-route *flow-g*) '(:groups :group :article :post :remove))
                   (fn-web-sends-to (car *st-g2*) (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx *flow-g*)))
                                    (fn-wss-c-session (fn-wss-f-ctx *flow-g*)))
                   (equal (nth 1 (car *st-g2*)) 7)))
; Tooth for both conjuncts: a sign-in flow's continuation sends to the
; connection just opened (9), neither the event's session's nor its ctx's.
(defconst *flow-si* (nth 4 (car *st-si*)))
(defconst *st-si2* (wsst-step *cfg* nil *flow-si* '(:opened 9)
                              (wsst-post-req "/signin" "fnr_pre=abcdefghijklmnopqrstuvwxyz" *body*)))
(assert-event (and (equal (car (car *st-si2*)) :send) (equal (nth 1 (car *st-si2*)) 9)
                   (not (fn-web-sends-to (car *st-si2*) (fn-wss-s-cid (fn-web-begin-session *cfg* nil '(:opened 9)))
                                         (fn-web-begin-session *cfg* nil '(:opened 9))))
                   (not (member (fn-wss-f-route *flow-si*) '(:groups :group :article :post :remove)))
                   (not (fn-web-sends-to (car *st-si2*) (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx *flow-si*)))
                                         (fn-wss-c-session (fn-wss-f-ctx *flow-si*))))))
(must-fail-checked
 (defthm wsst-tooth-first-needs-begin
   (fn-web-sends-to (car (fn-web-step config sessions flow event fn-web-in fn-web-out))
                    (fn-wss-s-cid (fn-web-begin-session config sessions event))
                    (fn-web-begin-session config sessions event))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step fn-web-sends-to)))))
(must-fail-checked
 (defthm wsst-tooth-second-needs-route
   (implies (not (equal (fn-wss-car event) :begin))
            (fn-web-sends-to (car (fn-web-step config sessions flow event fn-web-in fn-web-out))
                             (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                             (fn-wss-c-session (fn-wss-f-ctx flow))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step fn-web-sends-to)))))
; Without "not :begin": a :begin event carrying a flow whose ctx names
; nobody -- the send goes to the request's session (7), not the flow's.
(defconst *st-g3* (wsst-step *cfg* *ss* *flow-si* *ev-g* (wsst-get "/g?name=local.general")))
(assert-event (and (equal (car (car *st-g3*)) :send)
                   (not (fn-web-sends-to (car *st-g3*) (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx *flow-si*)))
                                         (fn-wss-c-session (fn-wss-f-ctx *flow-si*))))))
(must-fail-checked
 (defthm wsst-tooth-second-needs-not-begin
   (implies (member (fn-wss-f-route flow) '(:groups :group :article :post :remove))
            (fn-web-sends-to (car (fn-web-step config sessions flow event fn-web-in fn-web-out))
                             (fn-wss-s-cid (fn-wss-c-session (fn-wss-f-ctx flow)))
                             (fn-wss-c-session (fn-wss-f-ctx flow))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step fn-web-sends-to)))))

; --- KEYSTONE fn-web-sessions-bound-by-281.  Reached witness: the AUTHINFO
; reply step of carol's sign-in (the session is new, and bound).
(defconst *flow-si3* (nth 4 (car *st-si2*)))
(defconst *reply-281* (wsst-crlf (list "381 more" "281 ok")))
(defconst *st-si3* (wsst-step *cfg* nil *flow-si3* '(:reply) *reply-281*))
(defconst *new-s* (car (nth 1 *st-si3*)))
(assert-event (and (member-equal *new-s* (nth 1 *st-si3*))
                   (not (member-equal (fn-wss-s-token *new-s*) (fn-wss-tokens nil)))
                   (equal (fn-wss-s-cid *new-s*) 9)
                   (equal (fn-wss-s-login *new-s*) (wsst-octs "carol"))))
(defun wsst-bound (s flow event in) (declare (xargs :mode :program))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let ((fn-web-in (fn-octets-from-list in fn-web-in)))
        (mv (fn-wss-bound-by-281 s flow event fn-web-in) fn-web-in))
      r)))
(assert-event (wsst-bound *new-s* *flow-si3* '(:reply) *reply-281*))
; Tooth: without "the token is new", carol's existing session after a GET
; is in the table, and no 281 made it in that step.
(assert-event (and (member-equal (car (nth 1 *st-g*)) (nth 1 *st-g*))
                   (member-equal (fn-wss-s-token (car (nth 1 *st-g*))) (fn-wss-tokens *ss*))
                   (not (wsst-bound (car (nth 1 *st-g*)) nil *ev-g* (wsst-get "/g?name=local.general")))))
(must-fail-checked
 (defthm wsst-tooth-281-needs-new-token
   (implies (member-equal s (car (cdr (fn-web-step config sessions flow event fn-web-in fn-web-out))))
            (fn-wss-bound-by-281 s flow event fn-web-in))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step fn-wss-bound-by-281)))))
; Without membership: a session no step made is not bound by any 281.
(assert-event (and (not (member-equal '(tok 1 nil nil 0) (nth 1 *st-g*)))
                   (not (member-equal 'tok (fn-wss-tokens *ss*)))
                   (not (wsst-bound '(tok 1 nil nil 0) nil *ev-g* (wsst-get "/")))))
(must-fail-checked
 (defthm wsst-tooth-281-needs-member
   (implies (not (member-equal (fn-wss-s-token s) (fn-wss-tokens sessions)))
            (fn-wss-bound-by-281 s flow event fn-web-in))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-step fn-wss-bound-by-281)))))
; A 481 in the same step makes no session (the table is unchanged).
(defconst *st-si4* (wsst-step *cfg* nil *flow-si3* '(:reply) (wsst-crlf (list "381 more" "481 no"))))
(assert-event (and (equal (nth 1 *st-si4*) nil) (equal (car (car *st-si4*)) :close)))

; --- KEYSTONE fn-wss-body-cannot-end-the-article (no hypotheses): the
; witness is the posted body above; MUTATION witness (labelled): the
; decoded text un-stuffed has the line "." that would end the article.
(defconst *evil* (wsst-octs "a%0D%0A.%0D%0AQUIT"))
(assert-event (and (fn-wss-no-dot-line (fn-wss-stuff (fn-wrq-urldecode *evil*) t nil) t)
                   (fn-wss-ends-lf (fn-wss-stuff (fn-wrq-urldecode *evil*) t nil))
                   (not (fn-wss-no-dot-line (fn-wrq-urldecode *evil*) t))))

; A refused form never echoes the request: the trouble page's detail is
; the node's status line only (the native run found the request line
; "POST /remove HTTP/1.1" shown as a detail; fixed).
(defconst *rm-bad* (wsst-request (wsst-post-req "/remove" (concatenate 'string "fnr_session=" (wsst-str *tok*))
  (concatenate 'string "csrf=" (wsst-str *csrf*) "&g=local.general&id=nope"))
  *cfg* *ss* 300 nil nil nil))
(assert-event (and (equal (cadr (car (car *rm-bad*))) 400)
                   (not (search "HTTP/1.1" (wsst-str (nth 2 *rm-bad*))))))
