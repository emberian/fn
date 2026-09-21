;;; Native acquisition seam for the external freshness anchor.
;;;
;;; Raw Lisp owns only OS entropy, DNS/UDP and cryptographic primitive
;;; observations.  ACL2 produces the request datagram, parses the response,
;;; reconstructs both signature subjects and later decides window, pinning,
;;; freshness, acceptance and persistence.  Endpoint/key selection is an
;;; injected result of the future pinned-server manifest; this file has no
;;; default server and no key table.  `fn-anchor-server-host-select' supplies
;;; the complete bounded acquisition profile, including all wire sizes.

(in-package "ACL2")

(defun fnn-anchor-csprng-nonce (nonce-octets)
  "Read one nonce from the OS CSPRNG.  A short/failed device read is a fault."
  (let ((fd (fnn-open "/dev/urandom" sb-posix:o-rdonly))
        (answer (fnn-make-octets nonce-octets))
        (offset 0))
    (unwind-protect
         (progn
           (loop while (< offset nonce-octets) do
             (let* ((remaining (- nonce-octets offset))
                    (chunk (fnn-make-octets remaining))
                    (count (fnn-read-fd fd chunk)))
               (when (zerop count)
                 (fnn-fault "OS CSPRNG ended before one nonce"))
               (replace answer chunk :start1 offset :end2 count)
               (incf offset count)))
           answer)
      (fnn-close fd))))

(defun fnn-anchor-request (nonce request-octets)
  "Ask ACL2 for the exact deployed NONC/PAD request and copy its octets."
  (let ((result (fnn-core 'fn-anchor-wire-host-request
                          (fnn-octet-list nonce))))
    (unless (and (listp result) (= (length result) 2)
                 (eq (first result) :request)
                 (fnn-octet-list-p (second result))
                 (= (length (second result)) request-octets))
      (fnn-fault "ACL2 returned an invalid anchor request"))
    (fnn-octets (second result))))

(defun fnn-anchor-resolve-v4 (host)
  "The bounded first IPv4 result.  The pinned manifest remains endpoint owner."
  (if (typep host '(simple-array (unsigned-byte 8) (4)))
      host
    (sb-bsd-sockets:host-ent-address
     (sb-bsd-sockets:get-host-by-name host))))

(defun fnn-anchor-udp-exchange (host port request request-octets
                                response-octets timeout)
  "Send exactly one connected UDP datagram; return response octets or :TIMEOUT."
  (unless (and (stringp host) (< 0 (length host))
               (integerp port) (<= 1 port 65535)
               (realp timeout) (< 0 timeout)
               (typep request 'fnn-octets)
               (= (length request) request-octets)
               (integerp response-octets) (< 0 response-octets))
    (fnn-fault "invalid bounded anchor UDP request"))
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket
                               :type :datagram :protocol :udp)))
    (unwind-protect
         (progn
           (sb-bsd-sockets:socket-connect socket (fnn-anchor-resolve-v4 host) port)
           (let ((fd (fnn-socket-fd socket)))
             (unless (sb-sys:wait-until-fd-usable fd :output timeout)
               (return-from fnn-anchor-udp-exchange :timeout))
             (unless (= (sb-bsd-sockets:socket-send socket request nil)
                        (length request))
               (fnn-fault "short anchor UDP datagram send"))
             (unless (sb-sys:wait-until-fd-usable fd :input timeout)
               (return-from fnn-anchor-udp-exchange :timeout))
             ; One extra octet distinguishes an exact-bound packet from a
             ; longer datagram even on receive APIs that truncate to buffer.
             (let ((buffer (fnn-make-octets (1+ response-octets))))
               (multiple-value-bind (received count peer)
                   (sb-bsd-sockets:socket-receive
                    socket buffer (1+ response-octets))
                 (declare (ignore peer))
                 (when (> count response-octets)
                   (return-from fnn-anchor-udp-exchange :overbound))
                 (subseq received 0 count)))))
      (fnn-socket-shut socket))))

(defun fnn-anchor-parse (packet nonce pinned-key)
  "Call the ACL2 parser; :REFUSED is a grammar/binding verdict, not I/O."
  (let ((result (fnn-core 'fn-anchor-wire-host-parse
                          (fnn-octet-list packet)
                          (fnn-octet-list nonce)
                          (fnn-octet-list pinned-key))))
    (unless (and (listp result) (consp result)
                 (member (first result) '(:parsed :refused)))
      (fnn-fault "ACL2 returned an invalid anchor parse result"))
    result))

(defun fnn-anchor-observe (parsed nonce)
  "Run only the Ed25519/SHA-512 observations over ACL2's parsed projection."
  (unless (and (listp parsed) (= (length parsed) 7)
               (eq (first parsed) :parsed))
    (fnn-fault "invalid ACL2 anchor projection"))
  (let* ((fields (second parsed))
         (delegation-subject (fifth parsed))
         (response-subject (sixth parsed))
         (single-leaf-shape (seventh parsed)))
    (unless (and (listp fields) (= (length fields) 10)
                 (member single-leaf-shape '(0 1)))
      (fnn-fault "invalid ACL2 anchor fields"))
    (let ((delegation
            (fnn-crypto-ed25519-observe
             (first fields) delegation-subject (fifth fields)))
          (response
            (fnn-crypto-ed25519-observe
             (second fields) response-subject (ninth fields))))
      (when (or (eq delegation :unavailable) (eq response :unavailable))
        (return-from fnn-anchor-observe '(:uncertain :crypto-unavailable)))
      (when (or (eq delegation :fault) (eq response :fault))
        (return-from fnn-anchor-observe '(:fault :crypto)))
      (handler-case
          (let ((one-nonce
                  (and (= single-leaf-shape 1)
                       (equalp (fnn-crypto-anchor-leaf nonce)
                               (fnn-crypto-octets (tenth fields) 64
                                                  "anchor root")))))
            (list :observed fields
                  (and (eq delegation :verified) (eq response :verified))
                  one-nonce))
        (fnn-crypto-unavailable () '(:uncertain :crypto-unavailable))
        (fnn-crypto-fault () '(:fault :crypto))
        (error () '(:fault :crypto))))))

(defun fnn-anchor-profile (name timeout)
  "Resolve NAME and every acquisition bound through the ACL2 manifest."
  (let ((result (fnn-core 'fn-anchor-server-host-select
                          (fnn-octet-list (fnn-string-octets name)) timeout)))
    (unless (and (listp result) (consp result)
                 (member (first result) '(:server :refused)))
      (fnn-fault "ACL2 returned an invalid anchor server profile"))
    result))

(defun fnn-anchor-profile-host (octets)
  (unless (and (fnn-octet-list-p octets)
               (< 0 (length octets)) (<= (length octets) 255)
               (every (lambda (x) (<= 33 x 126)) octets))
    (fnn-fault "ACL2 returned an invalid anchor host"))
  (map 'string #'code-char octets))

(defun fnn-anchor-acquire (profile)
  "One bounded acquisition through ACL2 request/parser and native primitives."
  (handler-case
      (progn
        (unless (and (listp profile) (= (length profile) 9)
                     (eq (first profile) :server))
          (return-from fnn-anchor-acquire '(:fault :profile)))
        (let* ((host (fnn-anchor-profile-host (second profile)))
               (port (third profile))
               (pinned-key (fourth profile))
               (nonce-octets (sixth profile))
               (request-octets (seventh profile))
               (response-octets (eighth profile))
               (timeout (ninth profile)))
          (unless (and (integerp port) (<= 1 port 65535)
                       (integerp nonce-octets) (< 0 nonce-octets)
                       (integerp request-octets) (< 0 request-octets)
                       (integerp response-octets) (< 0 response-octets)
                       (realp timeout) (< 0 timeout))
            (return-from fnn-anchor-acquire '(:fault :profile)))
          (let ((key (fnn-crypto-octets pinned-key nonce-octets
                                         "pinned anchor key")))
            (when (/= (length key) nonce-octets)
              (return-from fnn-anchor-acquire '(:fault :pinned-key)))
            (let* ((nonce (fnn-anchor-csprng-nonce nonce-octets))
                 (request (fnn-anchor-request nonce request-octets))
                 (packet
                   (handler-case
                       (fnn-anchor-udp-exchange host port request request-octets
                                                response-octets timeout)
                     (sb-bsd-sockets:name-service-error () :network)
                     (sb-bsd-sockets:socket-error () :network)
                     (fnn-os-error () :network))))
            (cond ((eq packet :timeout) '(:uncertain :timeout))
                  ((eq packet :network) '(:uncertain :network))
                  ((eq packet :overbound) '(:refused :response-too-large))
                  (t
                   (let ((parsed (fnn-anchor-parse packet nonce key)))
                     (if (eq (first parsed) :refused)
                         parsed
                       (fnn-anchor-observe parsed nonce)))))))))
    (fnn-crypto-unavailable () '(:uncertain :crypto-unavailable))
    (fnn-crypto-fault () '(:fault :crypto))
    (fnn-store-indeterminate () '(:uncertain :core))
    (fnn-store-fault () '(:fault :host))
    (fnn-store-error () '(:fault :core))
    (error () '(:fault :host))))

;;; --------------------------------------------------------------------------
;;; ACL2 decision and mutable FNAN publication.
;;;
;;; This is deliberately separate from the shared immutable publisher.  FNAN
;;; has one authoritative final name and advances by atomic replacement after
;;; `fn-anchor-host-accept' says the candidate is monotone.  The store writer
;;; lock is held for load, acquisition, decision and publication.

(defun fnn-anchor-path (store)
  (fnn-join (fnn-store-root store) "anchor.fnan"))

(defun fnn-anchor-rp-start ()
  (fnn-core 'fn-anchor-rp-start))

(defun fnn-anchor-rp-recover-start (presentp)
  (fnn-core 'fn-anchor-rp-recover-start presentp))

(defun fnn-anchor-rp-action (phase)
  (fnn-core 'fn-anchor-rp-action phase))

(defun fnn-anchor-rp-step (phase event)
  (let ((next (fnn-core 'fn-anchor-rp-step phase event)))
    (when (equal next phase)
      (fnn-fault "ACL2 rejected anchor replacement event ~s in ~s"
                 event phase))
    next))

(defun fnn-anchor-rp-outcome (phase)
  (let ((outcome (fnn-core 'fn-anchor-rp-outcome phase)))
    (unless (member outcome '(:pending :durable :recovered :fault :uncertain))
      (fnn-fault "ACL2 returned invalid anchor replacement outcome"))
    outcome))

(defun fnn-anchor-recovery-barriers (store path presentp)
  "Make the observed final-name state durable before it becomes held state."
  (let ((phase (fnn-anchor-rp-recover-start presentp)))
    (when presentp
      (unless (eq (fnn-anchor-rp-action phase) :recovery-file-barrier)
        (fnn-fault "ACL2 rejected anchor file recovery barrier"))
      (handler-case
          (progn
            (fnn-fsync-regular path)
            (fnn-at store :anchor-recovery-file-durable)
            (setq phase (fnn-anchor-rp-step
                         phase '(:recovery-file-result :ok))))
        ((or fnn-os-error serious-condition) ()
          (setq phase (fnn-anchor-rp-step
                       phase '(:recovery-file-result :uncertain))))))
    (when (eq (fnn-anchor-rp-outcome phase) :uncertain)
      (fnn-indeterminate "anchor final-file recovery barrier is uncertain"))
    (unless (eq (fnn-anchor-rp-action phase) :recovery-directory-barrier)
      (fnn-fault "ACL2 rejected anchor directory recovery barrier"))
    (handler-case
        (progn
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-at store :anchor-recovery-directory-durable)
          (setq phase (fnn-anchor-rp-step
                       phase '(:recovery-directory-result :ok))))
      ((or fnn-os-error serious-condition) ()
        (setq phase (fnn-anchor-rp-step
                     phase '(:recovery-directory-result :uncertain)))))
    (unless (eq (fnn-anchor-rp-outcome phase) :recovered)
      (fnn-indeterminate "anchor directory recovery barrier is uncertain"))
    :recovered))

(defun fnn-anchor-load-held (store)
  "Return (values incarnation fields), faulting on a present invalid FNAN."
  (let* ((path (fnn-anchor-path store))
         (stat (fnn-lstat path)))
    (when (and stat (or (fnn-symlink-p stat) (not (fnn-regular-p stat))))
      (fnn-fault "refusing non-regular anchor record"))
    (fnn-anchor-recovery-barriers store path (not (null stat)))
    (when (null stat)
      (return-from fnn-anchor-load-held (values 0 nil)))
    (let* ((limit (fnn-core 'fn-anchor-host-frame-limit))
           (trailer (fnn-constant :trailer))
           (raw (progn
                  (unless (and (integerp limit) (< trailer limit))
                    (fnn-fault "ACL2 returned an invalid FNAN frame limit"))
                  (fnn-read-regular-bounded path limit))))
      (when (<= (length raw) trailer)
        (fnn-fault "truncated durable anchor record"))
      (let* ((values (fnn-core 'fn-anchor-host-decode
                               (fnn-octet-list raw)
                               (fnn-digest-of raw))))
        (unless (and (listp values) (= (length values) 11)
                     (integerp (first values)) (<= 0 (first values)))
          (fnn-fault "invalid durable anchor record"))
        (values (first values) (rest values))))))

(defun fnn-anchor-contents (incarnation fields)
  "The exact ACL2 FNAN protected bytes sealed by ACL2's frame trailer."
  (let ((protected (fnn-core 'fn-anchor-host-protected incarnation fields)))
    (unless (fnn-octet-list-p protected)
      (fnn-fault "ACL2 refused FNAN encoding after anchor acceptance"))
    (fnn-seal protected)))

(defun fnn-anchor-publish (store contents)
  "Replace anchor.fnan and return :DURABLE, :UNCERTAIN, or :FAULT.

Once final-name replacement is attempted, any failure is uncertain and the
caller must end this process ownership.  A later invocation recovers only by
decoding the final name while holding the same writer lock."
  (unless (and (fnn-store-writable store) (fnn-store-lock-fd store))
    (fnn-fault "anchor publication requires the exclusive store lock"))
  (let* ((stage (fnn-join (fnn-staging store)
                          (format nil ".anchor-~d-~a"
                                  (sb-posix:getpid) (fnn-random-hex 12))))
         (final (fnn-anchor-path store))
         (phase (fnn-anchor-rp-start)))
    (unless (eq (fnn-anchor-rp-action phase) :stage-and-file-barrier)
      (fnn-fault "ACL2 rejected anchor staging action"))
    (handler-case
        (progn
          (fnn-write-staged stage contents)
          (fnn-at store :anchor-staged-durable)
          (setq phase (fnn-anchor-rp-step phase '(:stage-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (ignore-errors (fnn-unlink stage))
        (setq phase (fnn-anchor-rp-step
                     phase '(:stage-result :known-fail)))))
    (when (eq (fnn-anchor-rp-outcome phase) :fault)
      (return-from fnn-anchor-publish :fault))
    (unless (eq (fnn-anchor-rp-action phase) :issue-replace)
      (fnn-fault "ACL2 rejected anchor replace action"))
    ; Record issue before entering rename(2).  Death after the syscall but
    ; before its result is therefore a reachable :replace-issued cut.
    (setq phase (fnn-anchor-rp-step phase :replace-issued))
    (unless (eq (fnn-anchor-rp-action phase) :observe-replace)
      (fnn-fault "ACL2 rejected issued anchor replace"))
    (handler-case
        (progn
          (fnn-replace stage final)
          (fnn-at store :anchor-replaced)
          (setq phase (fnn-anchor-rp-step
                       phase '(:replace-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (setq phase (fnn-anchor-rp-step
                     phase '(:replace-result :uncertain)))))
    (when (eq (fnn-anchor-rp-outcome phase) :uncertain)
      (return-from fnn-anchor-publish :uncertain))
    (unless (eq (fnn-anchor-rp-action phase) :directory-barrier)
      (fnn-fault "ACL2 rejected anchor directory action"))
    (handler-case
        (progn
          (fnn-fsync-dir (fnn-store-root store))
          (fnn-at store :anchor-directory-durable)
          (setq phase (fnn-anchor-rp-step
                       phase '(:directory-result :ok))))
      ((or fnn-os-error fnn-store-error serious-condition) ()
        (setq phase (fnn-anchor-rp-step
                     phase '(:directory-result :uncertain)))))
    (fnn-anchor-rp-outcome phase)))

(defun fnn-anchor-decision (profile held-fields incarnation observation)
  "Call the actual ACL2 acceptance entry over one primitive observation."
  (unless (and (listp profile) (= (length profile) 9)
               (eq (first profile) :server)
               (listp observation) (= (length observation) 4)
               (eq (first observation) :observed))
    (fnn-fault "invalid anchor decision inputs"))
  (let ((result
          (fnn-core 'fn-anchor-host-accept
                    (fifth profile) held-fields incarnation
                    (second observation) (third observation)
                    (fourth observation))))
    (unless (and (listp result) (= (length result) 2)
                 (member (first result) '(:accepted :refused :uncertain)))
      (fnn-fault "ACL2 returned an invalid anchor acceptance result"))
    result))

(defun fnn-anchor-reason-text (reason)
  (if reason (string-downcase (symbol-name reason)) "none"))

(defun fnn-command-anchor (command args)
  "Native CLI: anchor acquire STORE SERVER TIMEOUT-SECONDS."
  (unless (string= command "acquire")
    (error 'fnn-usage-error :message
           (format nil "unknown anchor command ~a" command)))
  (unless (= (length args) 3)
    (error 'fnn-usage-error :message
           "anchor acquire needs STORE SERVER TIMEOUT-SECONDS"))
  (let* ((root (first args))
         (name (second args))
         (timeout (handler-case (parse-integer (third args))
                    (error ()
                      (error 'fnn-usage-error :message
                             "anchor timeout must be an integer"))))
         (profile (fnn-anchor-profile name timeout)))
    (when (eq (first profile) :refused)
      (fnn-out "anchor refused: ~a" (fnn-anchor-reason-text (second profile)))
      (return-from fnn-command-anchor +fnn-exit-refused+))
    ; A saved image must never trust a serialized :READY FFI state.  This
    ; command resets, reloads and checks libsodium in the serving process.
    (handler-case (fnn-crypto-startup)
      (fnn-crypto-unavailable ()
        (fnn-out "anchor uncertain: crypto-unavailable")
        (return-from fnn-command-anchor +fnn-exit-uncertain+))
      (fnn-crypto-fault ()
        (fnn-err "anchor fault: crypto")
        (return-from fnn-command-anchor +fnn-exit-fault+)))
    (let ((store (make-fnn-store root :writable t)))
      (unwind-protect
           (progn
             (fnn-acquire store)
             (multiple-value-bind (incarnation held-fields)
                 (fnn-anchor-load-held store)
               (let ((observation (fnn-anchor-acquire profile)))
                 (case (first observation)
                   (:uncertain
                    (fnn-out "anchor uncertain: ~a"
                             (fnn-anchor-reason-text (second observation)))
                    +fnn-exit-uncertain+)
                   (:refused
                    (fnn-out "anchor refused: ~a"
                             (fnn-anchor-reason-text (second observation)))
                    +fnn-exit-refused+)
                   (:fault
                    (fnn-err "anchor fault: ~a"
                             (fnn-anchor-reason-text (second observation)))
                    +fnn-exit-fault+)
                   (:observed
                    (let* ((decision (fnn-anchor-decision
                                      profile held-fields incarnation observation))
                           (status (first decision))
                           (reason (second decision)))
                      (case status
                        (:accepted
                         (case (fnn-anchor-publish
                                store
                                (fnn-anchor-contents
                                 incarnation (second observation)))
                           (:durable
                            (fnn-out "anchor accepted incarnation=~d" incarnation)
                            +fnn-exit-ok+)
                           (:uncertain
                            (fnn-out "anchor uncertain: persistence")
                            +fnn-exit-uncertain+)
                           (t
                            (fnn-err "anchor fault: persistence")
                            +fnn-exit-fault+)))
                        (:uncertain
                         (fnn-out "anchor uncertain: ~a"
                                  (fnn-anchor-reason-text reason))
                         +fnn-exit-uncertain+)
                        (t
                         (fnn-out "anchor refused: ~a"
                                  (fnn-anchor-reason-text reason))
                         +fnn-exit-refused+))))
                   (t
                    (fnn-err "anchor fault: invalid observation")
                    +fnn-exit-fault+)))))
        (fnn-store-close store)))))

(fnn-register-verb "anchor" #'fnn-command-anchor)
