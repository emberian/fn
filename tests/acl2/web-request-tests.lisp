; Witnesses and teeth for books/web-request.lisp (lane web-native, PRF-337).
; Every buffer below is filled the way the host fills it
; (host/native/web-host.lisp: the socket's octets appended to fn-web-in) and
; every answer is the host-called function's.
(in-package "ACL2")
(include-book "../../books/web-request")
(include-book "must-fail-checked")

(defun wrqt-octs (s)
  (declare (xargs :guard (stringp s)))
  (fn-wrq-chars-octets (coerce s 'list)))

(defun wrqt-crlf (lines)
  (declare (xargs :guard (string-listp lines)))
  (if (consp lines)
      (append (wrqt-octs (car lines)) (list 13 10) (wrqt-crlf (cdr lines)))
    nil))

(defthm wrqt-crlf-octets
  (implies (string-listp lines) (fn-cbor-octet-listp (wrqt-crlf lines))))

(defconst *wrqt-limits* (fn-wrq-limits 16384 4096))

; The host's two calls on a whole request: frame from 0, then parse.
(defun wrqt-parse (xs limits)
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let ((fn-web-in (fn-octets-from-list xs fn-web-in)))
        (mv (let ((f (fn-web-head-frame 0 limits fn-web-in)))
              (if (equal (car f) :head)
                  (fn-web-parse-head (cadr f) limits fn-web-in)
                f))
            fn-web-in))
      r)))

(defun wrqt-frame (xs from limits)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs) (natp from))))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let ((fn-web-in (fn-octets-from-list xs fn-web-in)))
        (mv (fn-web-head-frame from limits fn-web-in) fn-web-in))
      r)))

(defun wrqt-work (xs end)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs) (natp end) (<= end (len xs)))))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let ((fn-web-in (fn-octets-from-list xs fn-web-in)))
        (mv (fn-wrq-work (fn-wrq-scan 0 end (fn-wrq-initial) fn-web-in)) fn-web-in))
      r)))

(defun wrqt-body-get (name xs start stop)
  (declare (xargs :guard (and (fn-cbor-octet-listp xs) (natp start) (natp stop)
                              (<= start stop) (<= stop (len xs)))))
  (with-local-stobj fn-web-in
    (mv-let (r fn-web-in)
      (let ((fn-web-in (fn-octets-from-list xs fn-web-in)))
        (mv (fn-web-body-get name start stop fn-web-in) fn-web-in))
      r)))

; -----------------------------------------------------------------------------
; A browser's GET, parsed.

(defconst *wrqt-get*
  (wrqt-crlf (list "GET /g?name=local.general&from=3 HTTP/1.1"
                   "Host: news.example"
                   "Cookie: fnr_session=abc; fnr_theme=dark"
                   "User-Agent: Mozilla/5.0 (X11)"
                   "Sec-Fetch-Site: same-origin"
                   "")))

(defconst *wrqt-get-r* (cadr (wrqt-parse *wrqt-get* *wrqt-limits*)))

(assert-event (equal (car (wrqt-parse *wrqt-get* *wrqt-limits*)) :request))
(assert-event (equal (fn-web-req-method *wrqt-get-r*) :get))
(assert-event (equal (fn-web-req-path *wrqt-get-r*) (wrqt-octs "/g")))
(assert-event (equal (fn-web-req-query *wrqt-get-r*) (wrqt-octs "name=local.general&from=3")))
(assert-event (equal (fn-web-req-host *wrqt-get-r*) (wrqt-octs "news.example")))
(assert-event (equal (fn-web-cookie-get (wrqt-octs "fnr_theme") (fn-web-req-cookie *wrqt-get-r*))
                     (wrqt-octs "dark")))
(assert-event (equal (fn-web-cookie-get (wrqt-octs "fnr_session") (fn-web-req-cookie *wrqt-get-r*))
                     (wrqt-octs "abc")))
(assert-event (equal (fn-web-cookie-get (wrqt-octs "nope") (fn-web-req-cookie *wrqt-get-r*))
                     :absent))
(assert-event (equal (fn-wrq-form-get (wrqt-octs "name") (fn-web-req-query *wrqt-get-r*))
                     (wrqt-octs "local.general")))
(assert-event (equal (fn-wrq-form-get (wrqt-octs "from") (fn-web-req-query *wrqt-get-r*))
                     (wrqt-octs "3")))
(assert-event (equal (fn-web-req-fetch-site *wrqt-get-r*) (wrqt-octs "same-origin")))
; The unrecognized User-Agent's value is nowhere in the request.
(assert-event (not (member-equal (wrqt-octs "Mozilla/5.0 (X11)") *wrqt-get-r*)))

; Absolute-form (RFC 9112 3.2.2) reduces to the same path and query.
(assert-event
 (equal (fn-web-req-path
         (cadr (wrqt-parse (wrqt-crlf (list "GET HTTP://news.example:8119/g?x=1 HTTP/1.1"
                                            "Host: news.example" ""))
                           *wrqt-limits*)))
        (wrqt-octs "/g")))

; The refusals, each for its reason.
(defun wrqt-code (lines)
  (declare (xargs :guard (string-listp lines)))
  (let ((r (wrqt-parse (wrqt-crlf lines) *wrqt-limits*)))
    (if (equal (car r) :refused) (cadr r) :request)))

(assert-event (equal (wrqt-code (list "GET / HTTP/1.1" "")) 400))              ; no Host
(assert-event (equal (wrqt-code (list "GET / HTTP/1.0" "")) :request))         ; 1.0 may omit it
(assert-event (equal (wrqt-code (list "GET / HTTP/1.1" "Host: a" "Host: b" "")) 400))
(assert-event (equal (wrqt-code (list "GET / HTTP/2.0" "Host: a" "")) 505))
(assert-event (equal (wrqt-code (list "GET / HTTQ/1.1" "Host: a" "")) 400))
(assert-event (equal (wrqt-code (list "DELETE / HTTP/1.1" "Host: a" "")) 501))
(assert-event (equal (wrqt-code (list "GET / HTTP/1.1" "Host : a" "")) 400))   ; SP before colon
(assert-event (equal (wrqt-code (list "GET / HTTP/1.1" "Host: a" " folded" "")) 400))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "")) 411))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "Content-Length: 4097" "")) 413))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "Content-Length: 4096" "")) :request))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "Content-Length: 3"
                                      "Content-Length: 4" "")) 400))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "Content-Length: 3"
                                      "Content-Length: 3" "")) :request))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a" "Content-Length: -3" "")) 400))
(assert-event (equal (wrqt-code (list "POST /post HTTP/1.1" "Host: a"
                                      "Transfer-Encoding: chunked" "")) 501))
(assert-event (equal (wrqt-code (list "GET * HTTP/1.1" "Host: a" "")) 400))
; A bare LF, a NUL in a value, a control octet in the target.
(assert-event (equal (car (wrqt-parse (append (wrqt-octs "GET / HTTP/1.1") (list 10)
                                              (wrqt-octs "Host: a") (list 13 10 13 10))
                                      *wrqt-limits*))
                     :refused))
(assert-event (equal (wrqt-parse (append (wrqt-octs "GET / HTTP/1.1") (list 13 10)
                                         (wrqt-octs "Host: a") (list 0 13 10 13 10))
                                 *wrqt-limits*)
                     '(:refused 400)))

; Framing: incremental, and 431 past the head limit.
(assert-event (equal (wrqt-frame (wrqt-octs "GET / HTTP/1.1") 0 *wrqt-limits*) '(:need 14)))
(assert-event (equal (car (wrqt-frame *wrqt-get* 7 *wrqt-limits*)) :head))
(assert-event (equal (wrqt-frame *wrqt-get* 0 (fn-wrq-limits 20 0)) '(:refused 431)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-wrq-scan-work-bound.  Reached positive witness: the browser's
; GET above; its complete antecedent (END a natural) and conclusion.
(assert-event (let ((end (len *wrqt-get*)))
                (and (natp end)
                     (<= (wrqt-work *wrqt-get* end) (* 2 end))
                     ; not degenerate: the work is more than one unit per octet
                     (< end (wrqt-work *wrqt-get* end)))))
; Hypothesis-removal tooth: END a negative integer -- the retained hypothesis
; fails, and so does the conclusion (work 0 is not at most -2).
(assert-event (and (not (natp -1))
                   (not (<= (wrqt-work *wrqt-get* 0) (* 2 -1)))))
(must-fail-checked
 (defthm wrqt-tooth-work-bound-needs-natp
   (<= (fn-wrq-work (fn-wrq-scan 0 end (fn-wrq-initial) fn-octets)) (* 2 end))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wrq-scan)))))

; KEYSTONE fn-web-head-frame-bounded.  Witness: the GET's head.
(assert-event (let ((r (wrqt-frame *wrqt-get* 0 *wrqt-limits*)))
                (and (equal (car r) :head)
                     (posp (cadr r))
                     (<= (cadr r) (len *wrqt-get*))
                     (<= (cadr r) (fn-wrq-limits-head *wrqt-limits*)))))
; Tooth: without "the answer is :head" the conclusion fails on the
; refusal, whose second element (431) exceeds a 20-octet head limit.
(assert-event (let ((r (wrqt-frame *wrqt-get* 0 (fn-wrq-limits 20 0))))
                (and (not (equal (car r) :head))
                     (not (<= (cadr r) (fn-wrq-limits-head (fn-wrq-limits 20 0)))))))
(must-fail-checked
 (defthm wrqt-tooth-frame-needs-head
   (let ((r (fn-web-head-frame from limits fn-octets)))
     (<= (cadr r) (fn-wrq-limits-head limits)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-wrq-frame-scan)))))

; KEYSTONE fn-web-route-is-a-row.  Witnesses: GET /g, HEAD /g (a GET row),
; POST /post.  Refusals: 405 with the path's methods, 404.
(assert-event (let ((r (fn-web-route :get (wrqt-octs "/g"))))
                (and (equal (car r) :route)
                     (member-equal (cadr r) *fn-web-routes*)
                     (equal (fn-web-row-name (cadr r)) :group)
                     (equal (fn-web-row-capability (cadr r)) :session)
                     (equal (fn-web-row-path (cadr r)) (wrqt-octs "/g")))))
(assert-event (equal (fn-web-row-name (cadr (fn-web-route :head (wrqt-octs "/g")))) :group))
(assert-event (equal (fn-web-row-capability (cadr (fn-web-route :post (wrqt-octs "/post")))) :csrf))
(assert-event (equal (fn-web-route :post (wrqt-octs "/g")) '(:refused 405 (:get))))
(assert-event (equal (fn-web-route :get (wrqt-octs "/nothing")) '(:refused 404)))
; Tooth: drop the hypothesis and the 404's second element is no row.
(must-fail-checked
 (defthm wrqt-tooth-route-needs-route
   (member-equal (cadr (fn-web-route method path)) *fn-web-routes*)
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-route)))))

; KEYSTONE fn-web-response-head-crlf-count.  Witness: a head whose caller
; passed a value carrying CR LF and a second field ("response splitting").
(defconst *wrqt-evil*
  (list (cons (wrqt-octs "Location") (append (wrqt-octs "/x") (list 13 10) (wrqt-octs "Set-Cookie: evil=1")))
        (cons (wrqt-octs "Content-Type") (wrqt-octs "text/html; charset=utf-8"))))
(defconst *wrqt-head* (fn-web-response-head 303 *wrqt-evil* 0 t))
(assert-event (and (equal (fn-wrq-count 13 *wrqt-head*)
                          (+ 2 (len (fn-web-head-fields *wrqt-evil* 0 t))))
                   (equal (fn-wrq-count 10 *wrqt-head*)
                          (+ 2 (len (fn-web-head-fields *wrqt-evil* 0 t))))
                   ; the evil field was not written; the good one was
                   (not (member-equal (car *wrqt-evil*) (fn-web-head-fields *wrqt-evil* 0 t)))
                   (member-equal (cadr *wrqt-evil*) (fn-web-head-fields *wrqt-evil* 0 t))))
; MUTATION witness (labelled): the fields' encoder WITHOUT the filter writes
; one more CR than it has fields -- the line the filter keeps out.
(assert-event (equal (fn-wrq-count 13 (fn-web-fields-octets *wrqt-evil*))
                     (+ 1 (len *wrqt-evil*))))
(assert-event (equal (take 17 *wrqt-head*) (wrqt-octs "HTTP/1.1 303 See ")))

; KEYSTONE fn-web-client-address-without-proxy.  Witness: a loopback peer
; with an X-Forwarded-For entry, not proxied: the peer.
(defconst *wrqt-xff*
  (cadr (wrqt-parse (wrqt-crlf (list "GET / HTTP/1.1" "Host: a"
                                     "X-Forwarded-For: 10.9.9.9, 203.0.113.7 " ""))
                    *wrqt-limits*)))
(assert-event (equal (fn-web-client-address :inet '(127 0 0 1) nil *wrqt-xff*)
                     (cons :inet '(127 0 0 1))))
; Tooth: PROXIED, and the last entry (the proxy's) decides.
(assert-event (equal (fn-web-client-address :inet '(127 0 0 1) t *wrqt-xff*)
                     (cons :inet '(203 0 113 7))))
; ...and a non-loopback peer is never overridden.
(assert-event (equal (fn-web-client-address :inet '(192 0 2 1) t *wrqt-xff*)
                     (cons :inet '(192 0 2 1))))
(must-fail-checked
 (defthm wrqt-tooth-address-needs-no-proxy
   (equal (fn-web-client-address family address proxied request) (cons family address))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-client-address)))))
; IPv6 literals.
(assert-event (equal (fn-wrq-ipv6 (wrqt-octs "2001:db8::1"))
                     '(32 1 13 184 0 0 0 0 0 0 0 0 0 0 0 1)))
(assert-event (equal (fn-wrq-ipv6 (wrqt-octs "::1")) '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)))
(assert-event (not (fn-wrq-ipv6 (wrqt-octs "1::2::3"))))
(assert-event (not (fn-wrq-ipv4 (wrqt-octs "256.1.1.1"))))

; fn-wrq-span-decode-is-urldecode and the body reader: a form body.
(defconst *wrqt-body* (wrqt-octs "csrf=t0k&subject=Hi+there&body=Gr%C3%BC%C3%9Fe%0D%0A100%+sure"))
(assert-event (equal (wrqt-body-get (wrqt-octs "subject") *wrqt-body* 0 (len *wrqt-body*))
                     (wrqt-octs "Hi there")))
(assert-event (equal (wrqt-body-get (wrqt-octs "body") *wrqt-body* 0 (len *wrqt-body*))
                     (append (wrqt-octs "Gr") '(195 188 195 159) (wrqt-octs "e") '(13 10)
                             (wrqt-octs "100% sure"))))
(assert-event (equal (wrqt-body-get (wrqt-octs "csr") *wrqt-body* 0 (len *wrqt-body*)) :absent))
(assert-event (equal (wrqt-body-get (wrqt-octs "body") *wrqt-body* 0 (len *wrqt-body*))
                     (fn-wrq-form-get (wrqt-octs "body") *wrqt-body*)))
