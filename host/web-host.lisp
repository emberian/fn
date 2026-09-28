; ACL2-facing boundary of the node's own web face (lane web-native, PRF-340;
; books/web-request.lisp, web-render.lisp, web-session.lisp, web-config.lisp).
; Every decision is the books'; these wrappers name them for the image
; (host/native/web-host.lisp) and keep the session table, node-local, in the
; state global `fn-web-sessions' (never in the log, never on disk).
(in-package "ACL2")
(include-book "../books/web-session-keystones")
(include-book "../books/web-config")

(defun fn-web-host-plan (config-octets listener-port tls-port certp)
  (declare (xargs :mode :program))
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
      (fn-web-step config sessions flow event fn-web-in fn-web-out)
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
          (fn-web-decimal code)
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
  (and (consp action) (member (car action) '(:respond :open :send :close)) (car action)))
