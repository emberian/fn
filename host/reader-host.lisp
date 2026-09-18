; Trusted experimental adapter helpers.  ACL2 owns wire/session/archive state.
(in-package "ACL2")

(defconst *fn-reader-groups* '("fn.letters"))
(defconst *fn-reader-id* "<reader@example.invalid>")
(defconst *fn-reader-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 72 101 108 108 111 13 10))
(defconst *fn-reader-greeting*
  '(50 48 49 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109 101 110 116 97 108 32 114 101 97 100 101 114 32 114 101 97 100 121 13 10))
(defconst *fn-reader-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-reader-groups*) 1 *fn-reader-id*
                      *fn-reader-payload* *fn-reader-groups*)
   0 1 :durable))

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
; The store variant reads only the ACL2 node reconstructed by store-host.
(defun fn-reader-use-seed (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-reader-archive *fn-reader-archive* state))
         (state (f-put-global 'fn-reader-action :ready state)))
    (value :ready)))

(defun fn-reader-use-store (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((node (f-get-global 'fn-store-node state)))
    (if (fn-node-statep node)
        (let ((archive (fn-node-acceptance node)))
          (if (fn-nntp-projectionp archive)
              (let* ((state (f-put-global 'fn-reader-archive archive state))
                     (state (f-put-global 'fn-reader-action :ready state)))
                (value :ready))
            (let ((state (f-put-global 'fn-reader-action :refused state)))
              (value :refused))))
      (let ((state (f-put-global 'fn-reader-action :refused state)))
        (value :refused)))))

(defun fn-reader-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-reader-wire
                               ; RFC 3977's 512 includes CRLF; wire state holds
                               ; only content before that delimiter.
                               (fn-wire-initial-state 510 8192) state))
         (state (f-put-global 'fn-reader-session (fn-nntp-initial-session) state))
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
         (result (if event (fn-nntp-step session archive event)
                   (fn-nntp-make-result session nil)))
         ; A framing rejection closes the wire state.  It receives the core's
         ; syntax response, then the adapter closes the socket without taking
         ; any more bytes from that connection.
         (effects (if (fn-reader-wire-closedp wire)
                      (append (fn-nntp-result-effects result)
                              (list (fn-nntp-close-effect)))
                    (fn-nntp-result-effects result)))
         (state (f-put-global 'fn-reader-wire wire state))
         (state (f-put-global 'fn-reader-session (fn-nntp-result-session result) state))
         (state (fn-reader-install-effects effects state))
         (state (f-put-global 'fn-reader-suffix suffix state)))
    (value :ok)))
