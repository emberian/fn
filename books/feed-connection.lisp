; fn: ACL2-owned outbound NNTP connection phase.
;
; A TCP descriptor is not a feed connection.  Before the owner may expose it
; to fn-own-feed-port-tick-peer, this machine consumes RFC 3977's greeting and
; (only for a configured streaming peer) RFC 4644's MODE STREAM response.
; It is layered over feed-wire-input's one-event pull interface, so a socket
; chunk that coalesces a greeting, MODE reply, and article reply remains
; bounded and is still applied one event at a time by the host.
(in-package "ACL2")
(include-book "feed-wire-input")
(include-book "owner-feed")
(include-book "feed-auth-profile")

(defconst *fn-fc-mode-stream-command*
  '(77 79 68 69 32 83 84 82 69 65 77 13 10))
(defconst *fn-fc-starttls-command* '(83 84 65 82 84 84 76 83 13 10))
(defconst *fn-fc-auth-user-prefix* '(65 85 84 72 73 78 70 79 32 85 83 69 82 32))
(defconst *fn-fc-auth-pass-prefix* '(65 85 84 72 73 78 70 79 32 80 65 83 83 32))

(defun fn-fc-make-state (input streamingp phase conn security)
  (list input streamingp phase conn security))
(defun fn-fc-input (x) (if (consp x) (car x) nil))
(defun fn-fc-streamingp (x)
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))
(defun fn-fc-phase (x)
  (if (and (consp x) (consp (cdr x)) (consp (cddr x))) (caddr x) nil))
(defun fn-fc-conn (x)
  (if (and (consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x)))
      (cadddr x)
    nil))
(defun fn-fc-security (x) (if (and (true-listp x) (member-equal (len x) '(5 8))) (nth 4 x) :clear))
(defun fn-fc-user (x) (if (and (true-listp x) (equal (len x) 8)) (nth 5 x) nil))
(defun fn-fc-pass (x) (if (and (true-listp x) (equal (len x) 8)) (nth 6 x) nil))
(defun fn-fc-allow-clear (x) (if (and (true-listp x) (equal (len x) 8)) (nth 7 x) nil))

(defun fn-fc-phasep (x)
  (member-equal x '(:greeting :starttls :tls :auth-user :auth-pass :mode :ready :closed)))

(defun fn-fc-statep (x)
  (and (true-listp x) (member-equal (len x) '(5 8))
       (fn-fwi-statep (fn-fc-input x))
       (booleanp (fn-fc-streamingp x))
       (fn-fc-phasep (fn-fc-phase x))
       (natp (fn-fc-conn x))
       (member-equal (fn-fc-security x) '(:clear :implicit :starttls))
       (or (equal (len x) 5)
           (and (fn-fap-tokenp (fn-fc-user x))
                (fn-fap-tokenp (fn-fc-pass x))
                (booleanp (fn-fc-allow-clear x))))))

(defun fn-fc-initial-state (streamingp conn security)
  (fn-fc-make-state (fn-fwi-initial-state) streamingp
                    (if (equal security :implicit) :tls :greeting) conn security))

(defun fn-fc-initial-auth-state (streamingp conn security user pass allow-clear)
  (list (fn-fwi-initial-state) streamingp
        (if (equal security :implicit) :tls :greeting) conn security
        user pass allow-clear))

(defun fn-fc-result (kind st line)
  (list kind st line))
(defun fn-fc-kind (x) (if (consp x) (car x) nil))
(defun fn-fc-next-state (x)
  (if (and (consp x) (consp (cdr x))) (cadr x) nil))
(defun fn-fc-line (x)
  (if (and (consp x) (consp (cdr x)) (consp (cddr x))) (caddr x) nil))

(defun fn-fc-with-input-phase (st input phase)
  (if (equal (len st) 8)
      (list input (fn-fc-streamingp st) phase (fn-fc-conn st)
            (fn-fc-security st) (fn-fc-user st) (fn-fc-pass st)
            (fn-fc-allow-clear st))
    (fn-fc-make-state input (fn-fc-streamingp st) phase (fn-fc-conn st)
                      (fn-fc-security st))))

(defun fn-fc-greetingp (line)
  "RFC 3977 section 5.1.1's two server greeting codes, exactly."
  (member-equal (fn-own-feed-response-code line) '(200 201)))

(defun fn-fc-mode-okp (line)
  "RFC 4644 section 2.3: MODE STREAM succeeds only with 203."
  (equal (fn-own-feed-response-code line) 203))

(defun fn-fc-mode-command ()
  "The ACL2-rendered bounded MODE STREAM line, or NIL on an internal defect."
  (let ((rendered (fn-wire-outbound-command-line
                   *fn-fc-mode-stream-command*
                   *fn-nntp-max-initial-line-octets*)))
    (if (fn-wire-outbound-okp rendered)
        (fn-wire-ag-car (fn-wire-outbound-octets rendered))
      nil)))

(defun fn-fc-starttls-command ()
  (let ((rendered (fn-wire-outbound-command-line
                   *fn-fc-starttls-command* *fn-nntp-max-initial-line-octets*)))
    (if (fn-wire-outbound-okp rendered)
        (fn-wire-ag-car (fn-wire-outbound-octets rendered)) nil)))

; Total under the book's implicit `:guard t' (its callers are too, and
; `fn-fc-user' returns whatever the state holds): a prefix or token that is
; not a true list renders no command, which is also what a state that fails
; `fn-fc-statep' (both fields `fn-fap-tokenp') would deserve.  Before
; 2026-09-22 this called `append' on them unguarded and `verify-guards'
; below could not discharge it.
(defun fn-fc-auth-command (prefix token)
  (if (and (true-listp prefix) (true-listp token))
      (let ((rendered (fn-wire-outbound-command-line
                       (append prefix token '(13 10))
                       *fn-nntp-max-initial-line-octets*)))
        (if (fn-wire-outbound-okp rendered)
            (fn-wire-ag-car (fn-wire-outbound-octets rendered)) nil))
    nil))
(defun fn-fc-auth-user-command (st)
  (fn-fc-auth-command *fn-fc-auth-user-prefix* (fn-fc-user st)))
(defun fn-fc-auth-pass-command (st)
  (fn-fc-auth-command *fn-fc-auth-pass-prefix* (fn-fc-pass st)))
(defun fn-fc-after-auth (st input)
  (if (fn-fc-streamingp st)
      (fn-fc-result :mode (fn-fc-with-input-phase st input :mode) nil)
    (fn-fc-result :ready (fn-fc-with-input-phase st input :ready) nil)))
(defun fn-fc-begin-auth-or-mode (st input)
  (if (fn-fc-user st)
      (if (and (equal (fn-fc-security st) :clear)
               (not (fn-fc-allow-clear st)))
          (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil)
        (fn-fc-result :auth-user (fn-fc-with-input-phase st input :auth-user) nil))
    (fn-fc-after-auth st input)))

(defun fn-fc-after-tls (st)
  "A host may report this event only after authenticated TLS succeeds."
  (if (and (fn-fc-statep st) (equal (fn-fc-phase st) :tls))
      (if (equal (fn-fc-security st) :implicit)
          (fn-fc-result :need-input (fn-fc-with-input-phase st (fn-fwi-initial-state)
                                                            :greeting) nil)
        (fn-fc-begin-auth-or-mode st (fn-fwi-initial-state)))
    (fn-fc-result :invalid st nil)))

(defun fn-fc-from-line (st input line)
  (case (fn-fc-phase st)
    (:greeting
     (if (fn-fc-greetingp line)
         (if (equal (fn-fc-security st) :starttls)
             (fn-fc-result :starttls (fn-fc-with-input-phase st input :starttls) nil)
           (fn-fc-begin-auth-or-mode st input))
       (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil)))
    (:starttls
     (if (equal (fn-own-feed-response-code line) 382)
         (fn-fc-result :tls (fn-fc-with-input-phase st input :tls) nil)
       (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil)))
    (:auth-user
     (case (fn-own-feed-response-code line)
       (381 (fn-fc-result :auth-pass (fn-fc-with-input-phase st input :auth-pass) nil))
       (281 (fn-fc-after-auth st input))
       (otherwise (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil))))
    (:auth-pass
     (if (equal (fn-own-feed-response-code line) 281)
         (fn-fc-after-auth st input)
       (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil)))
    (:mode
     (if (fn-fc-mode-okp line)
         (fn-fc-result :ready (fn-fc-with-input-phase st input :ready) nil)
       (fn-fc-result :refused (fn-fc-with-input-phase st input :closed) nil)))
    (:ready (fn-fc-result :reply (fn-fc-with-input-phase st input :ready) line))
    (otherwise (fn-fc-result :closed (fn-fc-with-input-phase st input :closed) nil))))

(defun fn-fc-step (st octets)
  "Consume at most one complete peer line, preserving the fwi suffix."
  (if (not (and (fn-fc-statep st) (fn-fwi-chunkp octets)))
      (fn-fc-result :invalid st nil)
    (let* ((fwi (fn-fwi-step (fn-fc-input st) octets))
           (kind (fn-fwi-kind fwi))
           (input (fn-fwi-next-state fwi)))
      (case kind
        (:line (fn-fc-from-line st input (fn-fwi-line fwi)))
        (:need-input (fn-fc-result :need-input (fn-fc-with-input-phase st input
                                                                   (fn-fc-phase st)) nil))
        (:closed (fn-fc-result :closed (fn-fc-with-input-phase st input :closed) nil))
        (otherwise (fn-fc-result :invalid st nil))))))

(defun fn-fc-lost (st)
  "Transport loss closes only this connection incarnation; no offer is made."
  (if (fn-fc-statep st)
      (fn-fc-with-input-phase st (fn-fc-input st) :closed)
    st))

; The owner host maintains one phase state per peer until loss.  This table is
; intentionally separate from the durable feed table: transport handshakes do
; not create an offer, a record, or a reusable connection incarnation.
(defun fn-fc-table-entryp (entry)
  (and (consp entry) (stringp (car entry)) (fn-fc-statep (cdr entry))))
(defun fn-fc-table-memberp (x xs)
  (if (consp xs) (or (equal x (car xs)) (fn-fc-table-memberp x (cdr xs))) nil))
(defun fn-fc-table-names (table)
  (if (consp table)
      (cons (if (consp (car table)) (car (car table)) nil)
            (fn-fc-table-names (cdr table)))
    nil))
(defun fn-fc-table-unique-namesp (xs)
  (if (consp xs)
      (and (not (fn-fc-table-memberp (car xs) (cdr xs)))
           (fn-fc-table-unique-namesp (cdr xs)))
    t))
(defun fn-fc-tablep (table)
  (if (consp table)
      (and (fn-fc-table-entryp (car table))
           (fn-fc-tablep (cdr table))
           (fn-fc-table-unique-namesp (fn-fc-table-names table)))
    (null table)))
(defun fn-fc-table-lookup (peer table)
  (if (consp table)
      (if (consp (car table))
          (if (equal peer (car (car table))) (cdr (car table))
            (fn-fc-table-lookup peer (cdr table)))
        (fn-fc-table-lookup peer (cdr table)))
    nil))
(defun fn-fc-table-remove (peer table)
  (if (consp table)
      (if (and (consp (car table)) (equal peer (car (car table))))
          (fn-fc-table-remove peer (cdr table))
        (cons (car table) (fn-fc-table-remove peer (cdr table))))
    nil))
(defun fn-fc-table-put (peer st table)
  (cons (cons peer st) (fn-fc-table-remove peer table)))

(defthm fn-fc-initial-state-is-state
  (implies (and (booleanp streamingp) (natp conn)
                (member-equal security '(:clear :implicit :starttls)))
           (fn-fc-statep (fn-fc-initial-state streamingp conn security)))
  :hints (("Goal" :in-theory (enable fn-fc-initial-state fn-fc-statep
                                     fn-fc-make-state fn-fc-phasep))))

(defthm fn-fc-step-is-one-fwi-step
  (implies (and (fn-fc-statep st) (fn-fwi-chunkp octets))
           (equal (fn-fc-step st octets)
                  (let* ((fwi (fn-fwi-step (fn-fc-input st) octets))
                         (kind (fn-fwi-kind fwi))
                         (input (fn-fwi-next-state fwi)))
                    (case kind
                      (:line (fn-fc-from-line st input (fn-fwi-line fwi)))
                      (:need-input
                       (fn-fc-result :need-input
                                     (fn-fc-with-input-phase st input (fn-fc-phase st))
                                     nil))
                      (:closed
                       (fn-fc-result :closed (fn-fc-with-input-phase st input :closed)
                                     nil))
                      (otherwise (fn-fc-result :invalid st nil))))))
  :hints (("Goal" :in-theory (enable fn-fc-step))))

(verify-guards fn-fc-make-state)
(verify-guards fn-fc-input)
(verify-guards fn-fc-streamingp)
(verify-guards fn-fc-phase)
(verify-guards fn-fc-conn)
(verify-guards fn-fc-security)
(verify-guards fn-fc-user)
(verify-guards fn-fc-pass)
(verify-guards fn-fc-allow-clear)
(verify-guards fn-fc-phasep)
(verify-guards fn-fc-statep)
(verify-guards fn-fc-initial-state)
(verify-guards fn-fc-initial-auth-state)
(verify-guards fn-fc-result)
(verify-guards fn-fc-kind)
(verify-guards fn-fc-next-state)
(verify-guards fn-fc-line)
(verify-guards fn-fc-with-input-phase)
(verify-guards fn-fc-greetingp)
(verify-guards fn-fc-mode-okp)
(verify-guards fn-fc-mode-command)
(verify-guards fn-fc-starttls-command)
(verify-guards fn-fc-auth-command)
(verify-guards fn-fc-auth-user-command)
(verify-guards fn-fc-auth-pass-command)
(verify-guards fn-fc-after-auth)
(verify-guards fn-fc-begin-auth-or-mode)
(verify-guards fn-fc-after-tls)
(verify-guards fn-fc-from-line)
(verify-guards fn-fc-step)
(verify-guards fn-fc-lost)
(verify-guards fn-fc-table-entryp)
(verify-guards fn-fc-table-memberp)
(verify-guards fn-fc-table-names)
(verify-guards fn-fc-table-unique-namesp)
(verify-guards fn-fc-tablep)
(verify-guards fn-fc-table-lookup)
(verify-guards fn-fc-table-remove)
(verify-guards fn-fc-table-put)
