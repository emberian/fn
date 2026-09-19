; Trusted experimental adapter helpers.  ACL2 owns wire/session/archive state.
(in-package "ACL2")
(include-book "../books/store-node")
(include-book "../books/nntp-post")

(defconst *fn-reader-groups* '("fn.letters"))
(defconst *fn-reader-id* "<reader@example.invalid>")
(defconst *fn-reader-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 72 101 108 108 111 13 10))
; The injecting-agent identity this experimental reader uses.  It is
; configuration, not a decision: books/injection.lisp reads it and builds
; Path, Injection-Info and any generated Message-ID from it.
(defconst *fn-reader-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *fn-reader-greeting*
  '(50 48 49 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109 101 110 116 97 108 32 114 101 97 100 101 114 32 114 101 97 100 121 13 10))
(defconst *fn-reader-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-reader-groups*) 1 *fn-reader-id*
                      *fn-reader-payload* *fn-reader-groups*)
   0 1 :durable))

(defun fn-reader-group-octets (names)
  (declare (xargs :mode :program))
  (if (consp names)
      (cons (fn-nntp-string-octets (car names))
            (fn-reader-group-octets (cdr names)))
    nil))

; The posting configuration is derived from the selected archive by ACL2, so
; the groups fn will accept a local post into are exactly the groups the store
; carries.  `allow` is the only part the operator supplies.
(defun fn-reader-post-config (archive allow)
  (declare (xargs :mode :program))
  (fn-inj-make-config (if allow t nil) *fn-reader-agent*
                      (fn-reader-group-octets (fn-state-groups archive))
                      *fn-article-max-octets*))

; The one effect the adapter acts on rather than writes out: POST asked for
; article framing.  The host's whole response is to call fn-wire-begin-article.
(defun fn-reader-begin-article-effectp (effects)
  (declare (xargs :mode :program))
  (if (consp effects)
      (or (equal (car effects) (fn-nntp-begin-article-effect))
          (fn-reader-begin-article-effectp (cdr effects)))
    nil))

; The adapter only consumes these fixed, trusted effect shapes.  Socket code
; obtains the resulting octets through @ globals; it does not decode NNTP
; commands or construct NNTP responses itself.
(defun fn-reader-effect-octets (effects)
  (if (consp effects)
      (let ((effect (car effects)))
        (append (if (and (consp effect)
                         (equal (car effect) :reply)
                         (consp (cdr effect)))
                    (car (cdr effect))
                  nil)
                (fn-reader-effect-octets (cdr effects))))
    nil))

(defun fn-reader-close-effectsp (effects)
  (if (consp effects)
      (or (equal (car effects) (fn-nntp-close-effect))
          (fn-reader-close-effectsp (cdr effects)))
    nil))

(defun fn-reader-wire-closedp (wire)
  (and (fn-wire-statep wire)
       (equal (fn-wire-state-mode wire) :closed)))

(defun fn-reader-install-effects (effects state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-reader-effects effects state))
         (state (f-put-global 'fn-reader-output
                              (fn-reader-effect-octets effects) state))
         (state (f-put-global 'fn-reader-closep
                              (fn-reader-close-effectsp effects) state)))
    state))

; Archive selection happens once before a listener accepts clients.  A reset
; starts a fresh wire/session pair but keeps the selected immutable snapshot.
; The store variant reads only the actual-node projection of the composed
; file/node state reconstructed by the store adapter.
(defun fn-reader-use-seed (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-reader-archive *fn-reader-archive* state))
         (state (f-put-global 'fn-reader-action :ready state)))
    (value :ready)))

; The operator's posting permission and the host's clock reading.  A clock
; reading is an observation, not a computed value: books/clock.lisp says what
; the host is asserting, and books/injection.lisp is the only thing that
; interprets it.
(defun fn-reader-set-posting (allow state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-reader-allow-post (if allow t nil) state)))
    (value :ok)))

(defun fn-reader-observe-clock (monotonic wall error state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-reader-clock
                             (fn-clock-observation monotonic wall error t)
                             state)))
    (value :ok)))

; A single committed article whose stored bytes cannot be projected used to
; refuse the whole store here.  It no longer does: fn-nntp-projectionp is now a
; configuration recognizer over the group names, the watermarks, and the
; article capacity, and an unprojectable article degrades only itself through
; fn-nntp-article-response.  Refusal is reserved for a store whose recognizer
; fails and for a configuration whose group names cannot be rendered inside RFC
; 3977 section 3.1's 512-octet initial line.
(defun fn-reader-use-store (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((store (f-get-global 'fn-store-sn state)))
    (if (fn-sn-statep store)
        (let ((node (fn-sn-node store)))
        (let ((archive (fn-node-acceptance node)))
          (if (fn-nntp-projectionp archive)
              (let* ((state (f-put-global 'fn-reader-archive archive state))
                     (state (f-put-global 'fn-reader-action :ready state)))
                (value :ready))
            (let ((state (f-put-global 'fn-reader-action :refused state)))
              (value :refused)))))
      (let ((state (f-put-global 'fn-reader-action :refused state)))
        (value :refused)))))

; Opening a connection is the one place the whole-archive projection recognizer
; runs.  fn-nntp-open-session records its verdict in the session; no command
; recomputes it: fn-nntp-step, called at line 112 below, reads the carried
; verdict instead of rerunning fn-nntp-projectionp.
(defun fn-reader-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (if (boundp-global 'fn-reader-archive state)
                      (f-get-global 'fn-reader-archive state)
                    nil))
         (state (f-put-global 'fn-reader-wire
                               ; RFC 3977's 512 includes CRLF; wire state holds
                               ; only content before that delimiter.
                               (fn-wire-initial-state 510 8192) state))
         (state (f-put-global 'fn-reader-session
                              (fn-post-open-session archive) state))
         (state (f-put-global 'fn-reader-config
                              (fn-reader-post-config
                               archive
                               (and (boundp-global 'fn-reader-allow-post state)
                                    (f-get-global 'fn-reader-allow-post state)))
                              state))
         (state (f-put-global 'fn-reader-submission nil state))
         (state (f-put-global 'fn-reader-suffix nil state))
         (state (fn-reader-install-effects
                 (list (fn-nntp-reply-effect *fn-reader-greeting*)) state)))
    (value :ready)))

; One call consumes at most one wire event.  The Python boundary preserves any
; returned suffix as transport bytes; protocol state is never reconstructed in
; Python.
(defun fn-reader-chunk (octets state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((next (fn-wire-next (f-get-global 'fn-reader-wire state) octets))
         (wire (fn-wire-next-state next))
         (event (fn-wire-next-event next))
         (suffix (fn-wire-next-unconsumed next))
         (session (f-get-global 'fn-reader-session state))
         (archive (f-get-global 'fn-reader-archive state))
         (config (f-get-global 'fn-reader-config state))
         (clock (if (boundp-global 'fn-reader-clock state)
                    (f-get-global 'fn-reader-clock state)
                  nil))
         (result (if event
                     (fn-nntp-post-step session archive config clock event)
                   (fn-post-make-result session nil nil)))
         (effects (fn-post-result-effects result))
         ; The one effect the adapter acts on.  Article framing is ACL2's
         ; decision; fn-wire-begin-article is the host carrying it out.
         (wire (if (fn-reader-begin-article-effectp effects)
                   (fn-wire-result-state (fn-wire-begin-article wire))
                 wire))
         ; A framing rejection closes the wire state.  It receives the core's
         ; syntax response, then the adapter closes the socket without taking
         ; any more bytes from that connection.
         (effects (if (fn-reader-wire-closedp wire)
                      (append effects (list (fn-nntp-close-effect)))
                    effects))
         (submission (fn-post-result-submission result))
         (state (f-put-global 'fn-reader-wire wire state))
         (state (f-put-global 'fn-reader-session
                              (fn-post-result-session result) state))
         (state (f-put-global 'fn-reader-submission submission state))
         (state (f-put-global 'fn-reader-submit-octets
                              (if submission
                                  (fn-inj-decision-octets submission) nil)
                              state))
         (state (f-put-global 'fn-reader-submit-msgid
                              (if submission
                                  (fn-inj-decision-msgid submission) nil)
                              state))
         (state (f-put-global 'fn-reader-submit-groups
                              (if submission
                                  (fn-inj-decision-groups submission) nil)
                              state))
         (state (fn-reader-install-effects effects state))
         (state (f-put-global 'fn-reader-suffix suffix state)))
    (value :ok)))

; The durable observation comes back from the host after it has carried the
; submitted octets through the same acceptance path tools/run_store.py `post`
; uses.  ACL2 turns it into the reply; the host never writes 240 itself.
(defun fn-reader-outcome (completion state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((session (f-get-global 'fn-reader-session state))
         (result (fn-nntp-post-outcome session completion))
         (state (f-put-global 'fn-reader-submission nil state))
         (state (fn-reader-install-effects
                 (fn-post-result-effects result) state)))
    (value :ok)))
