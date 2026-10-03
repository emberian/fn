; ACL2-facing boundary of the node's own web face (lane web-native, PRF-340;
; books/web-request.lisp, web-render.lisp, web-session.lisp, web-config.lisp).
; Every decision is the books'; these wrappers name them for the image
; (host/native/web-host.lisp) and keep the session table, node-local, in the
; state global `fn-web-sessions' (never in the log, never on disk).
(in-package "ACL2")
(include-book "../books/web-session-keystones")
(include-book "../books/web-config")
(include-book "../books/web-page-cursor")

(defun fn-web-host-plan (config-octets listener-port tls-port certp)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp config-octets)))
  (fn-web-config-plan config-octets listener-port tls-port certp))

(defun fn-web-host-plan-web-p (plan)
  (declare (xargs :mode :program))
  (equal (car plan) :web))

(defun fn-web-host-plan-refusal (plan)
  ; The reason word of a refused plan, else nil.
  (declare (xargs :mode :program))
  (and (equal (car plan) :refused) (cadr plan)))

(defun fn-web-host-plan-port (plan) (declare (xargs :mode :program)) (fn-web-plan-port plan))
(defun fn-web-host-plan-family (plan) (declare (xargs :mode :program)) (fn-web-plan-family plan))
(defun fn-web-host-plan-address (plan) (declare (xargs :mode :program)) (fn-web-plan-address plan))
(defun fn-web-host-plan-tls (plan) (declare (xargs :mode :program)) (fn-web-plan-tls plan))
(defun fn-web-host-plan-config (plan) (declare (xargs :mode :program)) (fn-web-plan-config plan))

(defun fn-web-host-limits (article-limit)
  (declare (xargs :mode :program))
  (fn-web-plan-limits article-limit))

; A new run starts with no sessions (they are this process's; a restart
; signs everyone out).
(defun fn-web-host-reset (state)
  (declare (xargs :mode :program :stobjs state))
  (let ((state (f-put-global 'fn-web-sessions nil state)))
    (value :reset)))

(defun fn-web-host-frame (from limits fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-web-head-frame from limits fn-web-in))

(defun fn-web-host-parse (end limits fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-web-parse-head end limits fn-web-in))

; One event of one request (books/web-session.lisp fn-web-step).
(defun fn-web-host-step (config flow event fn-web-in fn-web-out state)
  (declare (xargs :mode :program :stobjs (fn-web-in fn-web-out state)))
  (let ((sessions (if (boundp-global 'fn-web-sessions state)
                      (f-get-global 'fn-web-sessions state)
                    nil)))
    (mv-let (action sessions fn-web-out)
      (fn-web-step (append (take 6 config) (list :page-plan)) sessions flow event fn-web-in fn-web-out)
      (let ((state (f-put-global 'fn-web-sessions sessions state)))
        (mv action fn-web-out state)))))

; The response head (books/web-request.lisp fn-web-response-head).  SECURE
; (HSTS) when the face serves TLS itself or the profile's proxy does.
(defun fn-web-host-head (code fields length config tls)
  (declare (xargs :mode :program))
  (fn-web-response-head code fields length (or tls (fn-wss-cfg-proxied config))))

; A request the parser refused: its status and a one-line page.
(defun fn-web-host-refusal-body (code)
  (declare (xargs :mode :program))
  (append (fn-wrq-oct "<!doctype html><title>")
          (fn-ot-decimal-octets code)
          (fn-wrq-oct "</title><p>")
          (fn-wrq-chars-octets (coerce (fn-web-reason code) 'list))
          (fn-wrq-oct "</p>")))

(defun fn-web-host-refusal-fields ()
  (declare (xargs :mode :program))
  *fn-wss-html-fields*)

; The work a request may take: events one request's flow may need (the
; longest is make-your-account: open, send, close, open, send, respond).
(defun fn-web-host-max-events ()
  (declare (xargs :mode :program))
  16)

; The seconds a connection may take to bring its whole request (a slow
; client is closed, not waited for).
(defun fn-web-host-request-seconds ()
  (declare (xargs :mode :program))
  15)

; The owner's article limit, for the request body bound.
(defun fn-web-host-article-limit (state)
  (declare (xargs :mode :program :stobjs state))
  (fn-own-body-limit (fn-owner-core state)))

; Host observations whose meaning ACL2 decides.
(defun fn-web-host-action-kind (action)
  (declare (xargs :mode :program))
  (and (consp action) (member (car action) '(:respond :open :send :close :health)) (car action)))

; Q10d: observe only the fixed scheduler/disk and checkpoint values, no
; whole-state walk. Called under the existing owner mutex by the web face.
(defun fn-web-host-health-observe (sched state)
  (declare (xargs :mode :program :stobjs state))
  (fn-whl-observe sched (fn-owner-sco-deferred state)))

; Scheduling ceilings are the configured supported profile and a work window,
; never a truncation of a stored article. The HTTP actor consumes these exact
; core decisions before allocating/reading or slicing a continuation.
(defun fn-web-host-connection-limit (config)
  (declare (xargs :mode :program))
  (fn-wss-cfg-max config))

(defun fn-web-host-request-end (end request)
  (declare (xargs :mode :program))
  (+ (nfix end) (fn-web-req-clen request)))

(defun fn-web-host-window-end (start end)
  (declare (xargs :mode :program))
  (min (nfix end) (+ (nfix start) 4096)))

(defun fn-web-host-read-size (used limits end request)
  (declare (xargs :mode :program))
  (min 4096 (nfix (- (if request (fn-web-host-request-end end request)
                       (fn-wrq-limits-head limits)) (nfix used)))))

(defun fn-web-host-event-cid (config flow event state)
  (declare (xargs :mode :program :stobjs state))
  (if (or (equal (fn-wss-car event) :begin) (equal (fn-wss-f-route flow) :expire))
      (let* ((begin (if (equal (fn-wss-car event) :begin) event (fn-wss-f-data flow)))
             (request (fn-wrq-nth 1 begin)) (now (nfix (fn-wrq-nth 4 begin)))
             (sessions (if (boundp-global 'fn-web-sessions state) (f-get-global 'fn-web-sessions state) nil))
             (expired (fn-wss-expired sessions now (fn-wss-cfg-idle config)))
             (token (fn-web-cookie-get (fn-wrq-oct "fnr_session") (fn-web-req-cookie request)))
             (session (if (consp expired) (car expired)
                        (and (fn-wss-tokenp token) (fn-wss-find token sessions now (fn-wss-cfg-idle config))))))
        (and session (fn-wss-s-cid session)))
    nil))

(defun fn-web-host-reserve-size (need capacity)
  (declare (xargs :mode :program))
  (if (<= (nfix need) (nfix capacity)) (nfix capacity)
    (max 1024 (* 2 (nfix need)))))

; Count and emit use the same immutable segment cursor outside the owner
; section. IN remains the exact retained NNTP reply through the HTTP body.
(defun fn-web-host-page-cursor (segs)
  (declare (xargs :mode :program))
  (fn-wpc-cursor segs))

(defun fn-web-host-page-step (cursor count emitp fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-wpc-step cursor count emitp fn-web-in))
