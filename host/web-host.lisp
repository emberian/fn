; ACL2-facing boundary of the node's own web face (lane web-native, PRF-340;
; books/web-request.lisp, web-render.lisp, web-session.lisp, web-config.lisp).
; Every decision is the books'; these wrappers name them for the image
; (host/native/web-host.lisp) and keep the session table, node-local, in the
; state global `fn-web-sessions' (never in the log, never on disk).
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/history-paged-attach")
(include-book "../books/web-session-keystones")
(include-book "../books/web-config")
(include-book "../books/web-page-cursor")
(include-book "../books/web-reply-stream")
(include-book "../books/web-post-stream")
; fn-web-host-article-limit reads the owner (fn-owner-core, fn-own-body-limit).
(include-book "../books/owner-state-accessors")
; fn-web-host-identity reads the live configuration (fn-owner-config, fn-cfg-policy).
(include-book "../books/owner-config-state")
(include-book "../books/definterface")

(defun fn-web-host-plan (config-octets listener-port tls-port certp)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp config-octets)))
  (fn-web-config-plan config-octets listener-port tls-port certp))

(definterface fn-web-host-plan
  :class ::program
  :kinds ((config-octets fn-cbor-octet-listp)))

(defun fn-web-host-plan-web-p (plan)
  (declare (xargs :mode :program))
  (equal (car plan) :web))

(definterface fn-web-host-plan-web-p
  :class ::program)

(defun fn-web-host-plan-refusal (plan)
  ; The reason word of a refused plan, else nil.
  (declare (xargs :mode :program))
  (and (equal (car plan) :refused) (cadr plan)))

(definterface fn-web-host-plan-refusal
  :class ::program)

(defun fn-web-host-plan-port (plan) (declare (xargs :mode :program)) (fn-web-plan-port plan))

(definterface fn-web-host-plan-port
  :class ::program)
(defun fn-web-host-plan-family (plan) (declare (xargs :mode :program)) (fn-web-plan-family plan))

(definterface fn-web-host-plan-family
  :class ::program)
(defun fn-web-host-plan-address (plan) (declare (xargs :mode :program)) (fn-web-plan-address plan))

(definterface fn-web-host-plan-address
  :class ::program)
(defun fn-web-host-plan-tls (plan) (declare (xargs :mode :program)) (fn-web-plan-tls plan))

(definterface fn-web-host-plan-tls
  :class ::program)
(defun fn-web-host-plan-config (plan identity)
  (declare (xargs :mode :program))
  (fn-web-plan-config plan identity))

(definterface fn-web-host-plan-config
  :class ::program)

; The node's own name, the `path-identity' policy of the owner's live
; configuration (the one Path and Injection-Info carry): the domain of a
; post's From when [web] names none (books/web-config.lisp fn-web-plan-domain).
; Octets, or nil while the policy is unset.
(defun fn-web-host-identity (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (let ((identity (fn-cfg-policy (fn-cfg-value (fn-owner-config state)) "path-identity")))
    (if (and (stringp identity) (not (equal identity "")))
        (fn-record-string-octets identity)
      nil)))

(definterface fn-web-host-identity
  :class :common-lisp-compliant)

(defun fn-web-host-limits (article-limit)
  (declare (xargs :mode :program))
  (fn-web-plan-limits article-limit))

(definterface fn-web-host-limits
  :class ::program)

; A new run starts with no sessions (they are this process's; a restart
; signs everyone out).
(defun fn-web-host-reset (state)
  (declare (xargs :mode :program :stobjs state))
  (let ((state (f-put-global 'fn-web-sessions nil state)))
    (value :reset)))

(definterface fn-web-host-reset
  :class ::program)

(defun fn-web-host-frame (from limits fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-web-head-frame from limits fn-web-in))

(definterface fn-web-host-frame
  :class ::program)

(defun fn-web-host-parse (end limits fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-web-parse-head end limits fn-web-in))

(definterface fn-web-host-parse
  :class ::program)

; One event of one request (books/web-session.lisp fn-web-step).
(defun fn-web-host-step (config flow event fn-web-in fn-web-out state)
  (declare (xargs :mode :program :stobjs (fn-web-in fn-web-out state)))
  (let ((sessions (if (boundp-global 'fn-web-sessions state)
                      (f-get-global 'fn-web-sessions state)
                    nil)))
    (mv-let (action sessions fn-web-out)
      (fn-web-step (append (take 6 config) (list :page-plan :private-begin)) sessions flow event fn-web-in fn-web-out)
      (let ((state (f-put-global 'fn-web-sessions sessions state)))
        (mv action fn-web-out state)))))

(definterface fn-web-host-step
  :class ::program
  :keystones ((fn-web-health-step-preserves-sessions-and-bounds-body :via fn-web-step)))

; The response head (books/web-request.lisp fn-web-response-head).  SECURE
; (HSTS) when the face serves TLS itself or the profile's proxy does.
(defun fn-web-host-head (code fields length config tls)
  (declare (xargs :mode :program))
  (fn-web-response-head code fields length (or tls (fn-wss-cfg-proxied config))))

(definterface fn-web-host-head
  :class ::program)

; A request the parser refused: its status and a one-line page.
(defun fn-web-host-refusal-body (code)
  (declare (xargs :mode :program))
  (append (fn-wrq-oct "<!doctype html><title>")
          (fn-ot-decimal-octets code)
          (fn-wrq-oct "</title><p>")
          (fn-wrq-chars-octets (coerce (fn-web-reason code) 'list))
          (fn-wrq-oct "</p>")))

(definterface fn-web-host-refusal-body
  :class ::program)

(defun fn-web-host-refusal-fields ()
  (declare (xargs :mode :program))
  *fn-wss-html-fields*)

(definterface fn-web-host-refusal-fields
  :class ::program)

; The work a request may take: events one request's flow may need (the
; longest is make-your-account: open, send, close, open, send, respond).
(defun fn-web-host-max-events ()
  (declare (xargs :mode :program))
  16)

(definterface fn-web-host-max-events
  :class ::program)

; The seconds a connection may take to bring its whole request (a slow
; client is closed, not waited for).
(defun fn-web-host-request-seconds ()
  (declare (xargs :mode :program))
  15)

(definterface fn-web-host-request-seconds
  :class ::program)

; The owner's article limit, for the request body bound.
(defun fn-web-host-article-limit (state)
  (declare (xargs :mode :program :stobjs state))
  (fn-own-body-limit (fn-owner-core state)))

(definterface fn-web-host-article-limit
  :class ::program)

; Host observations whose meaning ACL2 decides.
(defun fn-web-host-action-kind (action)
  (declare (xargs :mode :program))
  (and (consp action)
       (member (car action) '(:respond :open :send :close :health :private-begin
                             :post-form :post-command :post-stream))
       (car action)))

(definterface fn-web-host-action-kind
  :class ::program)

; Q10d: observe only the fixed scheduler/disk and checkpoint values, no
; whole-state walk. Called under the existing owner mutex by the web face.
(defun fn-web-host-health-observe (sched state)
  (declare (xargs :stobjs state :guard t))
  (fn-whl-observe sched (fn-owner-sco-deferred state)))

; Q10d bounded observation for the owner's web readiness route.
(definterface fn-web-host-health-observe
  :class :common-lisp-compliant
  :keystones ((fn-whl-success-requires-observed-clear-owner :via fn-whl-observe)))

; Scheduling ceilings are the configured supported profile and a work window,
; never a truncation of a stored article. The HTTP actor consumes these exact
; core decisions before allocating/reading or slicing a continuation.
(defun fn-web-host-connection-limit (config)
  (declare (xargs :guard t))
  (fn-wss-cfg-max config))

; HTTP reactor uses these actual ACL2 scheduling and lease projections.
(definterface fn-web-host-connection-limit :class :common-lisp-compliant)

(defun fn-web-host-request-end (end request)
  (declare (xargs :guard t))
  (+ (nfix end) (fn-web-req-clen request)))

(definterface fn-web-host-request-end :class :common-lisp-compliant)

(defun fn-web-host-window-end (start end)
  (declare (xargs :guard t))
  (min (nfix end) (+ (nfix start) 4096)))

(definterface fn-web-host-window-end :class :common-lisp-compliant)

(defun fn-web-host-read-size (used limits end request)
  (declare (xargs :guard t))
  (min 4096 (nfix (- (if request (fn-web-host-request-end end request)
                       (fn-wrq-limits-head limits)) (nfix used)))))

(definterface fn-web-host-read-size :class :common-lisp-compliant)

(defun fn-web-host-event-cid (config flow event state)
  (declare (xargs :stobjs state :guard t))
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

(definterface fn-web-host-event-cid :class :common-lisp-compliant)

(defun fn-web-host-reserve-size (need capacity)
  (declare (xargs :guard t))
  (if (<= (nfix need) (nfix capacity)) (nfix capacity)
    (max 1024 (* 2 (nfix need)))))

(definterface fn-web-host-reserve-size :class :common-lisp-compliant)

; Count and emit use the same immutable segment cursor outside the owner
; section. IN remains the exact retained NNTP reply through the HTTP body.
(defun fn-web-host-page-cursor (segs)
  (declare (xargs :guard t))
  (fn-wpc-cursor segs))

(definterface fn-web-host-page-cursor :class :common-lisp-compliant)

; The cursor is one fn-web-host-page-cursor made and fn-wpc-step returned: its
; spans end inside the retained reply (fn-wpc-cursorp).
(defun fn-web-host-page-step (cursor count emitp fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (fn-wpc-cursorp cursor (fn-octets-len fn-web-in))))
  (fn-wpc-step cursor count emitp fn-web-in))

(definterface fn-web-host-page-step :class :common-lisp-compliant)

(defun fn-web-host-private-reply-p (flow event)
  (declare (xargs :guard t))
  (fn-web-private-reply-p flow event))

(definterface fn-web-host-private-reply-p :class :common-lisp-compliant)

(defun fn-web-host-private-reply-step (config flow event fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard (true-listp config)))
  (fn-web-private-reply-step (append (take 6 config) (list :page-plan :private-begin))
                            flow event fn-web-in fn-web-out))

(definterface fn-web-host-private-reply-step :class :common-lisp-compliant
  :kinds ((config true-listp)))

; Virtual ARTICLE source: scan only one rendered window, then replay the
; retained logical plans for the exact spans requested by the page cursor.
(defun fn-web-host-article-p (flow)
  (declare (xargs :mode :program))
  (equal (fn-wss-f-route flow) :article))
(defun fn-web-host-article-start (flow)
  (declare (xargs :mode :program))
  (fn-was-start (fn-wss-s-login (fn-wss-c-session (fn-wss-f-ctx flow)))))
(defun fn-web-host-article-scan (scan fn-web-in)
  (declare (xargs :mode :program :stobjs fn-web-in))
  (fn-was-scan 0 (fn-octets-len fn-web-in) scan fn-web-in))
(defun fn-web-host-article-page (config flow scan)
  (declare (xargs :mode :program))
  (fn-was-page config flow scan))
(defun fn-web-host-window-page-step (cursor base count emitp fn-web-in)
  (declare (xargs :stobjs fn-web-in
                  :guard (and (natp base) (natp count) (fn-wpc-wcursorp cursor))))
  (fn-wpc-window-drive 4096 cursor base count emitp nil fn-web-in))

(definterface fn-web-host-window-page-step :class :common-lisp-compliant
  :kinds ((base natp) (count natp)))
(defun fn-web-host-replay-slice (at length need)
  (declare (xargs :guard (consp need)))
  (let ((s (max (nfix at) (nfix (car need))))
        (e (min (+ (nfix at) (nfix length)) (nfix (cdr need)))))
    (list (max 0 (- s (nfix at))) (max 0 (- e (nfix at)))
          (+ (nfix at) (nfix length)) (>= (+ (nfix at) (nfix length)) (nfix (cdr need))))))

(definterface fn-web-host-replay-slice :class :common-lisp-compliant)

(defun fn-web-host-replay-forward-p (need base end)
  (declare (xargs :guard (consp need)))
  (and (<= (nfix base) (nfix (car need))) (<= (nfix (car need)) (nfix end))))

(definterface fn-web-host-replay-forward-p :class :common-lisp-compliant)

(defun fn-web-host-stream-p (flow) (declare (xargs :guard t)) (fn-wrs-p flow))

(definterface fn-web-host-stream-p :class :common-lisp-compliant)
(defun fn-web-host-stream-start (flow) (declare (xargs :guard t)) (fn-wrs-start flow))

(definterface fn-web-host-stream-start :class :common-lisp-compliant)

; The scan is one fn-web-host-stream-start made and fn-web-host-stream-scan
; returned (fn-wrs-statep).
(defun fn-web-host-stream-scan (scan fn-web-in)
  (declare (xargs :stobjs fn-web-in :guard (fn-wrs-statep scan)))
  (fn-wrs-scan scan fn-web-in))

(definterface fn-web-host-stream-scan :class :common-lisp-compliant)
(defun fn-web-host-stream-page (config flow scan)
  (declare (xargs :guard (fn-wrs-statep scan)))
  (fn-wrs-page config flow scan))

(definterface fn-web-host-stream-page :class :common-lisp-compliant)

(defun fn-web-host-private-begin-step (config action fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (true-listp config) (true-listp action))))
  (fn-wpf-private-begin (append (take 6 config) (list :page-plan :private-begin))
                             action fn-web-in fn-web-out))

(definterface fn-web-host-private-begin-step :class :common-lisp-compliant
  :kinds ((config true-listp) (action true-listp)))

; The cursor is one fn-wps-header-cursor made (the form's finish) and this
; function returned; its encoded body [I, E) lies in the source (fn-wps-cursorp).
(defun fn-web-host-post-window (cursor fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (fn-wps-cursorp cursor (fn-octets-len fn-web-in))))
  (mv-let (bytes next done) (fn-wps-window 4096 cursor nil fn-web-in)
    (let* ((fn-web-out (fn-octets-clear fn-web-out))
           (fn-web-out (fn-octets-append-list bytes fn-web-out)))
      (mv next done fn-web-out))))

(definterface fn-web-host-post-window :class :common-lisp-compliant)
(defun fn-web-host-post-reply-step (config flow event cursor fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out) :guard (true-listp config)))
  (fn-wps-private-reply (append (take 6 config) (list :page-plan :private-begin))
                        flow event cursor fn-web-in fn-web-out))

(definterface fn-web-host-post-reply-step :class :common-lisp-compliant
  :kinds ((config true-listp)))

; The traversal is one fn-wpf-start made (fn-web-host-private-begin-step) and
; this function returned; it reads fn-web-in only inside the form span
; (fn-wpf-statep).
(defun fn-web-host-post-form-step (config prep fn-web-in fn-web-out)
  (declare (xargs :stobjs (fn-web-in fn-web-out)
                  :guard (and (true-listp config)
                              (fn-wpf-statep prep (fn-octets-len fn-web-in)))))
  (mv-let (next done) (fn-wpf-drive 4096 prep fn-web-in)
    (if done (fn-wpf-finish (append (take 6 config) (list :page-plan :private-begin))
                           next fn-web-in fn-web-out)
      (mv (list :post-form next) fn-web-out))))

(definterface fn-web-host-post-form-step :class :common-lisp-compliant
  :kinds ((config true-listp)))
