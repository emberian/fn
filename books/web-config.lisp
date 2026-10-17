; fn: the node's own web face -- its `[web]' table (lane web-native,
; PRF-340, WEB-005; 2026-09-28).
;
; The operator turns the face on in fn.toml:
;
;   [web]
;   port = 8119            ; required: no port, no face
;   host = "127.0.0.1"     ; one listener address (the [listener] grammar);
;                          ; loopback unless the operator names another
;   site = "Friends news"  ; the name in every page's bar and title
;   domain = "news.example.net"  ; the From of a post: LOGIN <LOGIN@DOMAIN>
;   proxied = true         ; a TLS proxy on this machine fronts the face
;                          ; (Caddy): the browser's address is its last
;                          ; X-Forwarded-For entry, cookies are Secure
;   tls = true             ; serve HTTPS itself with [listener]'s certificate
;   idle_seconds = 43200   ; a session's idle life (default 12 hours)
;   max_sessions = 64      ; sessions kept at once (each holds one owner
;                          ; connection)
;
; `fn-web-config-plan' reads the same octets the operator's profile was
; loaded from (books/native-config.lisp parses the table and admits its
; keys) and answers the face's plan, or (:none), or (:refused REASON).
; The host binds exactly the plan's address and port, loads TLS exactly
; when the plan says so, and hands `fn-web-plan-config' to fn-web-step.

(in-package "ACL2")
(include-book "native-config")
(include-book "web-session")

(defconst *fn-web-default-host* "127.0.0.1")
(defconst *fn-web-default-site* "fn news")
(defconst *fn-web-default-domain* "localhost")
(defconst *fn-web-max-idle* 2592000)      ; 30 days
(defconst *fn-web-max-sessions* 4096)

(defun fn-web-config-pairs (octets)
  ; The profile's key/value rows, as books/native-config.lisp parses them.
  (declare (xargs :guard t))
  (if (and (fn-ncfg-ascii-octetsp octets) (<= (len octets) *fn-ncfg-max-octets*))
      (let ((lines (fn-ncfg-lines octets)))
        (if (< *fn-ncfg-max-lines* (len lines)) :bad (fn-ncfg-parse-lines lines nil nil nil)))
    :bad))

(defun fn-web-config-string (pairs key default)
  (declare (xargs :guard t))
  (fn-ncfg-string-value (fn-ncfg-value pairs "web" key) default *fn-ncfg-max-text* nil))

; The face's plan:
;   (:web PORT FAMILY ADDRESS SITE DOMAIN PROXIED TLS IDLE MAX)
; LISTENER-PORT and TLS-PORT are the owner's (the face takes neither);
; CERTP whether the host holds [listener]'s certificate and key.
(defun fn-web-config-plan (octets listener-port tls-port certp)
  (declare (xargs :guard t))
  (let ((pairs (fn-web-config-pairs octets)))
    (if (equal pairs :bad)
        (list :refused :syntax)
      (let* ((port (fn-ncfg-nat-value (fn-ncfg-value pairs "web" "port") nil 65535))
             (host (fn-web-config-string pairs "host" *fn-web-default-host*))
             (site (fn-web-config-string pairs "site" *fn-web-default-site*))
             ; No domain named: nil here; fn-web-plan-config takes the node's own
             ; name for it at the start (lane operability-review, 2026-09-29).
             (domain (fn-web-config-string pairs "domain" nil))
             (proxied (fn-ncfg-bool-value (fn-ncfg-value pairs "web" "proxied") nil))
             (tls (fn-ncfg-bool-value (fn-ncfg-value pairs "web" "tls") nil))
             (idle (fn-ncfg-nat-value (fn-ncfg-value pairs "web" "idle_seconds") 43200 *fn-web-max-idle*))
             (max (fn-ncfg-nat-value (fn-ncfg-value pairs "web" "max_sessions") 64 *fn-web-max-sessions*))
             (address (and (stringp host)
                           (fn-native-config-listener-address (fn-record-string-octets host)))))
        (cond ((null port) (list :none))
              ((or (equal port :bad) (equal port 0)) (list :refused :port))
              ((or (equal port listener-port) (equal port tls-port)) (list :refused :port-taken))
              ((or (equal address :bad) (not (consp address))
                   (not (member (fn-ncfg-first address) '(:inet :inet6))))
               (list :refused :host))
              ((or (equal site :bad) (equal domain :bad)) (list :refused :text))
              ((or (equal proxied :bad) (equal tls :bad)) (list :refused :flag))
              ((and tls (not certp)) (list :refused :tls-needs-certificate))
              ((or (equal idle :bad) (equal idle 0) (equal max :bad) (equal max 0))
               (list :refused :bounds))
              (t (list :web port (fn-ncfg-first address) (fn-ncfg-second address)
                       (fn-record-string-octets site)
                       (and (stringp domain) (fn-record-string-octets domain))
                       (and proxied t) (and tls t) idle max)))))))

(defun fn-web-plan-port (plan) (declare (xargs :guard t)) (fn-wrq-nth 1 plan))
(defun fn-web-plan-family (plan) (declare (xargs :guard t)) (fn-wrq-nth 2 plan))
(defun fn-web-plan-address (plan) (declare (xargs :guard t)) (fn-wrq-nth 3 plan))
(defun fn-web-plan-tls (plan) (declare (xargs :guard t)) (fn-wrq-nth 7 plan))

; What fn-web-step reads.  IDENTITY is the node's own name (the
; `path-identity' policy, the name its Path and Injection-Info carry; octets,
; or nil while none is set): the domain of a post's From, `LOGIN <LOGIN@DOMAIN>',
; when the [web] table names no domain, so a friend's post says where it
; was made rather than the machine's host name; "localhost" when neither.
; The order is the decision: a named domain, else the node's name; its
; witness and teeth are in tests/acl2/web-config-tests.lisp.
(defun fn-web-plan-domain (plan identity)
  (declare (xargs :guard t))
  (let ((named (fn-wrq-nth 5 plan)))
    (cond ((consp named) named)
          ((consp identity) identity)
          (t (fn-record-string-octets *fn-web-default-domain*)))))

(defun fn-web-plan-config (plan identity)
  (declare (xargs :guard t))
  (fn-web-config (fn-wrq-nth 4 plan) (fn-web-plan-domain plan identity) (fn-wrq-nth 6 plan)
                 (fn-wrq-nth 8 plan) (fn-wrq-nth 9 plan)))



; The request limits: the profile's head default and the body a form
; carrying the owner's article limit needs (books/web-request.lisp).
(defun fn-web-plan-limits (article-limit)
  (declare (xargs :guard t))
  (fn-wrq-limits *fn-wrq-default-head-octets* (fn-wrq-body-limit article-limit)))

(defthm fn-web-nat-value-range
  (let ((v (fn-ncfg-nat-value value default ceiling)))
    (or (equal v :bad) (equal v default) (and (natp v) (<= v ceiling))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ncfg-nat-value))))

(defthm fn-web-config-plan-answers
  ; KEYSTONE (PRF-340): the face is planned only on a port of its own, at
  ; an admitted address, and with TLS only beside the certificate.
  (let ((plan (fn-web-config-plan octets listener-port tls-port certp)))
    (implies (equal (car plan) :web)
             (and (natp (fn-web-plan-port plan)) (< 0 (fn-web-plan-port plan))
                  (<= (fn-web-plan-port plan) 65535)
                  (not (equal (fn-web-plan-port plan) listener-port))
                  (not (equal (fn-web-plan-port plan) tls-port))
                  (member (fn-web-plan-family plan) '(:inet :inet6))
                  (implies (fn-web-plan-tls plan) certp))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-web-config-pairs fn-ncfg-parse-lines
                                      fn-native-config-listener-address fn-ncfg-value
                                      fn-ncfg-string-value fn-ncfg-nat-value fn-ncfg-bool-value
                                      fn-record-string-octets fn-web-config-string)
           :use ((:instance fn-web-nat-value-range
                  (value (fn-ncfg-value (fn-web-config-pairs octets) "web" "port"))
                  (default nil) (ceiling 65535))))))
