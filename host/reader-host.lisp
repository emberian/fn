; Trusted experimental adapter helpers.  ACL2 owns wire/session/archive state.
(in-package "ACL2")
(include-book "../books/store-node")
(include-book "../books/served")

(defconst *fn-reader-groups* '("fn.letters"))
(defconst *fn-reader-id* "<reader@example.invalid>")
(defconst *fn-reader-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 72 101 108 108 111 13 10))
(defconst *fn-reader-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-reader-groups*) 1 *fn-reader-id*
                      *fn-reader-payload* *fn-reader-groups*)
   0 1 :durable))

; The adapter consumes one typed result per call and takes no decision of its
; own.  Concatenating the reply stream and recognising the close effect are
; fn-served-reply-octets and fn-served-closingp (books/served.lisp): they used
; to be fn-reader-effect-octets and fn-reader-close-effectsp here, in :program
; mode, which made the host a second owner of the reply framing.  The carried
; connection is opaque to this file: it is stored and handed back, never read.
(defun fn-reader-install-result (result state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((effects (fn-served-result-effects result))
         (state (f-put-global 'fn-reader-conn (fn-served-result-conn result) state))
         (state (f-put-global 'fn-reader-output
                              (fn-served-reply-octets effects) state))
         (state (f-put-global 'fn-reader-closep
                              (fn-served-closingp effects) state)))
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
; recomputes it: fn-nntp-step, reached through fn-served-step below, reads the
; carried verdict instead of rerunning fn-nntp-projectionp.
(defun fn-reader-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (if (boundp-global 'fn-reader-archive state)
                      (f-get-global 'fn-reader-archive state)
                    nil))
         ; RFC 3977's 512 includes CRLF; wire state holds only content before
         ; that delimiter.
         (state (fn-reader-install-result (fn-served-open archive 510 8192) state)))
    (value :ready)))

; One socket read.  The whole chunk is consumed: fn-served-step is
; fn-wire-drive followed by fn-nntp-step per framed event, with the reply
; concatenation, proved partition independent in books/served.lisp.  There is
; no suffix to hand back and no loop in Python.
(defun fn-reader-chunk (octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-reader-install-result
                (fn-served-step (f-get-global 'fn-reader-conn state) octets)
                state)))
    (value :ok)))
