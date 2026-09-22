; fn: what a node says about itself -- the injecting agent a served POST
; names, and the service-log line the native owner writes for a submission
; and for an accepted connection.
;
; The injecting agent.  RFC 5536 section 3.2.8 opens Injection-Info with the
; <path-identity> of the injecting agent, and RFC 5537 section 3.2.1 has the
; same agent prepend that identity to Path.  fn has ONE slot for a node's
; <path-identity>: the replayed configuration policy `path-identity`
; (`fn operator CONFIG policy set path-identity IDENTITY`, admitted by
; fn-path-identityp in books/native-admin.lisp), which peer loop suppression
; reads too (fn-peer-local-identity).  `fn-oag-agent' reads that slot and
; nothing else.  fn.toml's `[posting] agent' is not a second slot: a value
; there could only disagree with Path, and the native operator refuses it by
; name (books/native-config.lisp, fn-native-config-unsupported-key).
;
; This was host code (host/owner-host.lisp `fn-owner-agent-of', program
; mode), so no theorem could name the function the host called; the host
; now calls `fn-oag-post-config' and holds no identity of its own.
;
; The service log.  One line per submission the owner takes (served POST
; and local-control post) and one per accepted connection, outcome word
; first, rendered here from ACL2's own classification so the log says what
; the reply says.  The host writes the octets and a newline and decides
; nothing.  Every rendered field is bounded and printable, so a line is one
; line whatever a client sent.

(in-package "ACL2")
(include-book "injection")
(include-book "injection-invariants")
(include-book "config")
(include-book "node-config")
(include-book "owner")

; -----------------------------------------------------------------------------
; The injecting agent

; A store whose `path-identity' slot is unset injects as this RFC 2606
; `.invalid' name: it names no real host, and it says the node was not told
; who it is.  It was host/owner-host.lisp's `*fn-owner-agent*'.
(defconst *fn-oag-unset-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))

(defun fn-oag-identity (cfg)
  "The configured path-identity policy text, or the empty string."
  (declare (xargs :guard t))
  (fn-cfg-policy (fn-cfg-value cfg) "path-identity"))

(defun fn-oag-identity-setp (cfg)
  (declare (xargs :guard t))
  (and (stringp (fn-oag-identity cfg))
       (not (equal (fn-oag-identity cfg) ""))))

(defun fn-oag-agent (cfg)
  (declare (xargs :guard t))
  (if (fn-oag-identity-setp cfg)
      (fn-record-string-octets (fn-oag-identity cfg))
    *fn-oag-unset-agent*))

(defun fn-oag-group-octets (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-nntp-string-octets (car names))
            (fn-oag-group-octets (cdr names)))
    nil))

(defun fn-oag-post-config (cfg max-octets)
  "The posting configuration the owner installs for configuration CFG.

The host calls this at host/owner-host.lisp `fn-owner-post-config', which
`fn-owner-open-store' and `fn-owner-config-complete' install with
fn-own-configure; a connection pins the installed value at open and its
served POST reaches fn-inj-decide with it (fn-nntp-post-step).  MAX-OCTETS is
the store's payload bound, which the host still supplies
(`*fn-store-max-payload*', host/store-host.lisp)."
  (declare (xargs :guard t))
  (fn-inj-make-config t (fn-oag-agent cfg)
                      (fn-oag-group-octets (fn-cnode-served-of cfg))
                      max-octets))

(defthm fn-oag-post-config-agent-is-the-path-identity
  (implies (fn-oag-identity-setp cfg)
           (equal (fn-inj-config-agent (fn-oag-post-config cfg max-octets))
                  (fn-record-string-octets (fn-oag-identity cfg))))
  :hints (("Goal" :in-theory (disable fn-oag-identity))))

(defthm fn-oag-injected-article-names-the-path-identity
  (implies (and (fn-oag-identity-setp cfg)
                (fn-inj-injectedp
                 (fn-inj-decide source (fn-oag-post-config cfg max-octets)
                                observation)))
           (fn-inj-infixp
            (fn-inj-injection-info-line
             (fn-record-string-octets (fn-oag-identity cfg)))
            (fn-inj-decision-octets
             (fn-inj-decide source (fn-oag-post-config cfg max-octets)
                            observation))))
  :hints (("Goal"
           :use ((:instance fn-inj-injected-article-names-the-configured-agent
                            (config (fn-oag-post-config cfg max-octets))))
           :in-theory (disable fn-inj-injected-article-names-the-configured-agent
                               fn-oag-post-config fn-oag-identity
                               fn-oag-identity-setp fn-inj-decide
                               fn-inj-injectedp fn-inj-injection-info-line
                               fn-inj-infixp))))

; The served step: whatever submission fn-nntp-post-step hands the owner
; carries the Injection-Info line of the configuration the connection
; pinned.  With the theorem above, a connection opened under
; `fn-oag-post-config' of a configuration whose path-identity is set submits
; only articles whose Injection-Info names that identity.
(defthm fn-oag-post-step-submission-names-the-configured-agent
  (implies (fn-post-result-submission
            (fn-nntp-post-step ps archive config observation injection
                               wire-event))
           (fn-inj-infixp
            (fn-inj-injection-info-line (fn-inj-config-agent config))
            (fn-inj-decision-octets
             (fn-post-result-submission
              (fn-nntp-post-step ps archive config observation injection
                                 wire-event)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-post-step)
                                  (fn-inj-decide fn-inj-injectedp
                                      fn-inj-injection-info-line
                                      fn-inj-infixp fn-nntp-step
                                      fn-post-offeredp
                                      fn-post-refusal-line)))))

; -----------------------------------------------------------------------------
; Rendering helpers

(defconst *fn-oag-max-field-octets* 256)

(defun fn-oag-text (s)
  (declare (xargs :guard t))
  (fn-record-string-octets s))

(defun fn-oag-visible-aux (xs n)
  ; Each octet outside 33..126 becomes `?', and at most N are kept, so a
  ; field is one bounded token whatever it held.
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (and (consp xs) (not (zp n)))
        (cons (if (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126))
                  (car xs)
                63)
              (fn-oag-visible-aux (cdr xs) (1- n)))
      nil)))

(defun fn-oag-visible (xs)
  (declare (xargs :guard t))
  (fn-oag-visible-aux xs *fn-oag-max-field-octets*))

(defun fn-oag-strip-zeros (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)) (equal (car xs) 48))
      (fn-oag-strip-zeros (cdr xs))
    xs))

(defun fn-oag-decimal (n)
  (declare (xargs :guard t))
  (fn-oag-strip-zeros (fn-inj-digits n 20)))

(defun fn-oag-time (obs)
  "YYYY-MM-DDTHH:MM:SSZ of the owner's wall reading, or `none'."
  (declare (xargs :guard t))
  (if (and (fn-clock-observationp obs) (fn-clock-has-wall obs))
      (let ((i (fn-inj-instant-of (fn-clock-wall obs))))
        (fn-inj-append
         (fn-inj-digits (fn-inj-instant-year i) 4)
         (cons 45
         (fn-inj-append
          (fn-inj-digits (fn-inj-instant-month i) 2)
          (cons 45
          (fn-inj-append
           (fn-inj-digits (fn-inj-instant-day i) 2)
           (cons 84
           (fn-inj-append
            (fn-inj-digits (fn-inj-instant-hour i) 2)
            (cons 58
            (fn-inj-append
             (fn-inj-digits (fn-inj-instant-minute i) 2)
             (cons 58
             (fn-inj-append
              (fn-inj-digits (fn-inj-instant-second i) 2)
              (list 90)))))))))))))
    (fn-oag-text "none")))

(defun fn-oag-join (parts)
  ; PARTS joined by one space.
  (declare (xargs :guard t))
  (if (consp parts)
      (if (consp (cdr parts))
          (fn-inj-append (car parts) (cons 32 (fn-oag-join (cdr parts))))
        (fn-inj-append (car parts) nil))
    nil))

(defun fn-oag-field (name value)
  (declare (xargs :guard t))
  (fn-inj-append (fn-oag-text name) (cons 61 (fn-oag-visible value))))

(defun fn-oag-class-word (class)
  (declare (xargs :guard t))
  (cond ((equal class :accepted) (fn-oag-text "accepted"))
        ((equal class :duplicate) (fn-oag-text "duplicate"))
        ((equal class :refused) (fn-oag-text "refused"))
        (t (fn-oag-text "uncertain"))))

; -----------------------------------------------------------------------------
; The lines

; A served submission's outcome, in the words the control reply uses
; (fn-own-control-outcome-result): the host's :duplicate is a duplicate, and
; otherwise it is what fn-own-outcome-completion made of the host's word --
; :durable only for a completion consumed after the take.
(defun fn-oag-served-class (o word)
  (declare (xargs :guard t))
  (if (equal word :duplicate)
      :duplicate
    (let ((completion (fn-own-outcome-completion o word)))
      (cond ((equal completion :durable) :accepted)
            ((equal completion :refused) :refused)
            (t :uncertain)))))

(defun fn-oag-served-post-line (o id word)
  "The line for served submission ID completing with host word WORD.

Read from the owner before fn-own-outcome consumes the in-flight
submission.  The agent is the one the connection pinned, which is the one
its article's Injection-Info names."
  (declare (xargs :guard t))
  (let* ((sub (fn-own-inflight o))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (agent (if conn
                    (fn-inj-config-agent (fn-own-conn-config conn))
                  (fn-inj-config-agent (fn-own-config o)))))
    (fn-oag-join
     (list (fn-oag-class-word (fn-oag-served-class o word))
           (fn-oag-text "post")
           (fn-oag-field "path" (fn-oag-text "served"))
           (fn-oag-field "connection" (fn-oag-decimal id))
           (fn-oag-field "message-id" (fn-own-sub-msgid sub))
           (fn-oag-field "agent" agent)
           (fn-oag-field "time" (fn-oag-time (fn-own-clock o)))))))

(defun fn-oag-control-post-line (o word)
  "The line for the local-control submission in flight completing with WORD.

A control post stores an already-authored article exactly
(fn-own-control-decision): no injecting agent writes a field into it, so the
line names none."
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o))
        (class (fn-own-control-outcome-result o word)))
    (fn-oag-join
     (list (fn-oag-class-word class)
           (fn-oag-text "post")
           (fn-oag-field "path" (fn-oag-text "control"))
           (fn-oag-field "message-id" (fn-own-sub-msgid sub))
           (fn-oag-field "time" (fn-oag-time (fn-own-clock o)))))))

(defun fn-oag-connection-line (o id peer)
  "The line for connection ID the owner just opened; PEER is the record name
the owner resolved the source address to, or nil for a reader."
  (declare (xargs :guard t))
  (fn-oag-join
   (if peer
       (list (fn-oag-text "accepted") (fn-oag-text "peer")
             (fn-oag-field "connection" (fn-oag-decimal id))
             (fn-oag-field "peer" peer)
             (fn-oag-field "time" (fn-oag-time (fn-own-clock o))))
     (list (fn-oag-text "accepted") (fn-oag-text "reader")
           (fn-oag-field "connection" (fn-oag-decimal id))
           (fn-oag-field "time" (fn-oag-time (fn-own-clock o)))))))

; A line is one line: no octet of it is CR or LF, whatever the owner held.
(defthm fn-oag-visible-has-no-line-break
  (and (not (member-equal 10 (fn-oag-visible-aux xs n)))
       (not (member-equal 13 (fn-oag-visible-aux xs n)))))
