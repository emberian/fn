; Trusted experimental adapter helpers.  ACL2 owns wire/session/archive state.
(in-package "ACL2")
(include-book "../books/store-node")
(include-book "../books/served")
(include-book "../books/reader-open-carried")
(include-book "../books/state-globals")

(defconst *fn-reader-groups* '("fn.letters"))
(defconst *fn-reader-id* "<reader@example.invalid>")
(defconst *fn-reader-payload* '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 72 101 108 108 111 13 10))
; The injecting-agent identity this experimental reader uses.  It is
; configuration, not a decision: books/injection.lisp reads it and builds
; Path, Injection-Info and any generated Message-ID from it.
(defconst *fn-reader-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
;; The records flip: the seed article's payload is handle 0 of the payload
;; arena, which fn-reader-use-seed fills with *fn-reader-payload* (the served
;; readers read an article's bytes through the arena: books/nntp-session.lisp
;; fn-nntp-article-bytes).
(defconst *fn-reader-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-reader-groups*) 1 *fn-reader-id*
                      0 *fn-reader-groups* :legacy)
   0 1 :durable))

; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-reader-group-octets-loop (names acc)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-reader-group-octets-loop (cdr names)
                                   (cons (fn-nntp-string-octets (car names)) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-reader-group-octets (names)
  (declare (xargs :guard t))
  (fn-reader-group-octets-loop names nil))

; The posting configuration is derived from the selected archive by ACL2, so
; the groups fn will accept a local post into are exactly the groups the store
; carries.  `allow` is the only part the operator supplies.
(defun fn-reader-post-config (archive allow)
  (declare (xargs :guard t))
  (fn-inj-make-config (if allow t nil) *fn-reader-agent*
                      (fn-reader-group-octets (fn-state-groups archive))
                      *fn-article-max-octets*))

; The adapter consumes one typed result per call and takes no decision of its
; own.  Concatenating the reply stream, recognising the close effect and
; finding the submission are fn-served-reply-octets, fn-served-closingp and
; fn-served-submission (books/served.lisp); the first two used to be
; fn-reader-effect-octets and fn-reader-close-effectsp here, in :program mode,
; which made the host a second owner of the reply framing.  The carried
; connection is opaque to this file: it is stored and handed back, never read.
; Article-mode framing is inside it: the :begin-article effect is acted on by
; fn-served-dispatch, not here.
(defun fn-reader-install-result (result state)
  (declare (xargs :stobjs state :guard t))
  (let* ((effects (fn-served-result-effects result))
         (submission (fn-served-submission effects))
         (state (f-put-global 'fn-reader-conn (fn-served-result-conn result) state))
         (state (f-put-global 'fn-reader-output
                              (fn-served-reply-octets effects) state))
         (state (f-put-global 'fn-reader-closep
                              (fn-served-closingp effects) state))
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
                              state)))
    state))

; Archive selection happens once before a listener accepts clients.  A reset
; starts a fresh wire/session pair but keeps the selected immutable snapshot.
; The store variant reads only the actual-node projection of the composed
; file/node state reconstructed by the store adapter.
;; The selection (books/reader-open-carried.lisp fn-rdc-selection): the
;; archive recognised once, with its verdicts and its Message-ID trie built
;; once.  The reader's archive is immutable under its shared lock, so every
;; connection opens over this one value (fn-rdc-reset-is-served-open).
(defun fn-reader-install-selection (sel state)
  (declare (xargs :stobjs state :guard t))
  (if (fn-rdc-readyp sel)
      (let* ((state (f-put-global 'fn-reader-selection sel state))
             (state (f-put-global 'fn-reader-archive (fn-rdc-archive sel) state))
             (state (f-put-global 'fn-reader-verdicts (fn-rdc-verdicts sel) state))
             (state (f-put-global 'fn-reader-action :ready state)))
        (value :ready))
    (let ((state (f-put-global 'fn-reader-action :refused state)))
      (value :refused))))

(defun fn-reader-use-seed (fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :guard t))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list *fn-reader-payload* fn-arena)))
    (mv-let (erp val state)
      (fn-reader-install-selection (fn-rdc-selection *fn-reader-archive* nil) state)
      (mv erp val fn-arena state))))

; The operator's posting permission and the host's clock reading.  A clock
; reading is an observation, not a computed value: books/clock.lisp says what
; the host is asserting, and books/injection.lisp is the only thing that
; interprets it.
(defun fn-reader-set-posting (allow state)
  (declare (xargs :stobjs state :guard t))
  (let ((state (f-put-global 'fn-reader-allow-post (if allow t nil) state)))
    (value :ok)))

(defun fn-reader-observe-clock (monotonic wall error state)
  (declare (xargs :stobjs state :guard t))
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
  (declare (xargs :stobjs state :guard (boundp-global 'fn-store-sn state)))
  (fn-reader-install-selection
   (fn-rdc-store-selection (f-get-global 'fn-store-sn state)) state))

; Opening a connection is the one place the whole-archive projection recognizer
; runs.  fn-nntp-open-session records its verdict in the session; no command
; recomputes it: fn-nntp-step, reached through fn-served-step below, reads the
; carried verdict instead of rerunning fn-nntp-projectionp.  The posting
; configuration and the clock observation are pinned into the connection here;
; a served step reads them from the connection and never from a global.
(defun fn-reader-reset (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((archive (if (boundp-global 'fn-reader-archive state)
                      (f-get-global 'fn-reader-archive state)
                    nil))
         (config (fn-reader-post-config
                  archive
                  (and (boundp-global 'fn-reader-allow-post state)
                       (f-get-global 'fn-reader-allow-post state))))
         (clock (if (boundp-global 'fn-reader-clock state)
                    (f-get-global 'fn-reader-clock state)
                  nil))
         ; RFC 3977's 512 includes CRLF; wire state holds only content before
         ; that delimiter.
         (sel (if (boundp-global 'fn-reader-selection state)
                  (f-get-global 'fn-reader-selection state)
                nil))
         ; fn-rdc-reset-is-served-open (books/reader-open-carried.lisp): the
         ; reference open of the selected archive, pinned with its verdicts,
         ; with the trie and the recognisers taken from the selection.
         (state (fn-reader-install-result
                 (fn-rdc-reset sel 510 8192 config clock clock
                               (fn-auth-open-config))
                 state)))
    (value :ready)))

; One socket read.  The whole chunk is consumed: fn-served-step is a fold of
; fn-wire-feed-byte with fn-nntp-post-step run on each framed event before the
; next byte, with the reply concatenation, proved partition independent in
; books/served.lisp.  There is no suffix to hand back and no loop in Python.
(defun fn-reader-chunk (octets fn-arena state)
  (declare (xargs :stobjs (state fn-arena)
                  :guard (and (fn-cbor-octet-listp octets)
                              (boundp-global 'fn-reader-conn state))))
  (let ((state (fn-reader-install-result
                (fn-served-step (f-get-global 'fn-reader-conn state) octets fn-arena)
                state)))
    (value :ok)))

; The durable observation comes back from the host after it has carried the
; submitted octets through the same acceptance path tools/run_store.py `post`
; uses.  It is one more served input: ACL2 turns it into the reply, and the
; host never writes 240 itself.
(defun fn-reader-outcome (completion state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-reader-conn state)))
  (let ((state (fn-reader-install-result
                (fn-served-post-outcome (f-get-global 'fn-reader-conn state)
                                        completion)
                state)))
    (value :ok)))
