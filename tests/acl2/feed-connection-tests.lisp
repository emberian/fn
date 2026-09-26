; Teeth for the ACL2-owned outbound connection phase.
(in-package "ACL2")
(include-book "../../books/feed-connection")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fc-stream* (fn-fc-initial-state t 7 :clear))
(assert-event (fn-fc-statep *fc-stream*))

; Greeting split at CR/LF: no feed connection or command before the line.
(defconst *fc-greeting-cr* (fn-fc-step *fc-stream* '(50 48 48 32 111 107 13)))
(assert-event (equal (fn-fc-kind *fc-greeting-cr*) :need-input))
(defconst *fc-mode* (fn-fc-step (fn-fc-next-state *fc-greeting-cr*) '(10)))
(assert-event (equal (fn-fc-kind *fc-mode*) :mode))
(assert-event (equal (fn-fc-mode-command) '(77 79 68 69 32 83 84 82 69 65 77 13 10)))

; A MODE response coalesced with a later reply stays retained: first ready,
; then the ready state's NIL drain exposes exactly that later reply.
(defconst *fc-coalesced*
  (fn-fc-step (fn-fc-next-state *fc-mode*)
              '(50 48 51 32 115 116 114 101 97 109 13 10 50 51 56 13 10)))
(assert-event (equal (fn-fc-kind *fc-coalesced*) :ready))
(defconst *fc-reply* (fn-fc-step (fn-fc-next-state *fc-coalesced*) nil))
(assert-event (equal (fn-fc-kind *fc-reply*) :reply))
(assert-event (equal (fn-fc-line *fc-reply*) '(50 51 56)))

; The configured non-streaming profile becomes ready immediately after either
; RFC 3977 greeting.  It never emits the MODE action.
(defconst *fc-legacy* (fn-fc-initial-state nil 8 :clear))

(defconst *fc-starttls* (fn-fc-initial-state t 9 :starttls))
(defconst *fc-starttls-offer* (fn-fc-step *fc-starttls* '(50 48 48 13 10)))
(assert-event (equal (fn-fc-kind *fc-starttls-offer*) :starttls))
(assert-event (equal (fn-fc-starttls-command) '(83 84 65 82 84 84 76 83 13 10)))
(defconst *fc-starttls-382*
  (fn-fc-step (fn-fc-next-state *fc-starttls-offer*) '(51 56 50 13 10)))
(assert-event (equal (fn-fc-kind *fc-starttls-382*) :tls))
(assert-event (equal (fn-fc-kind (fn-fc-after-tls (fn-fc-next-state *fc-starttls-382*)))
                     :mode))
(assert-event (equal (fn-fc-kind
                      (fn-fc-step (fn-fc-next-state *fc-starttls-offer*)
                                  '(53 56 48 13 10))) :refused))
(defconst *fc-legacy-ready* (fn-fc-step *fc-legacy* '(50 48 49 13 10)))
(assert-event (equal (fn-fc-kind *fc-legacy-ready*) :ready))

; Teeth: a non-greeting 20x, a non-203 MODE response, and a lost connection
; cannot become a ready/reply state and thus cannot authorize an offer.
(assert-event (equal (fn-fc-kind (fn-fc-step *fc-stream* '(50 48 50 13 10)))
                     :refused))
; (PRF-207: 500 and 501 to MODE STREAM are the IHAVE fallback, below; the
; tooth is a 400, which still refuses.)
(assert-event (equal (fn-fc-kind
                      (fn-fc-step (fn-fc-next-state *fc-mode*) '(52 48 48 13 10)))
                     :refused))
(defconst *fc-lost* (fn-fc-lost (fn-fc-next-state *fc-coalesced*)))
(assert-event (equal (fn-fc-phase *fc-lost*) :closed))
(assert-event (equal (fn-fc-kind (fn-fc-step *fc-lost* nil))
                     :closed))

; AUTHINFO is ordered after authenticated TLS and before MODE STREAM.
(defconst *fc-auth0*
  (fn-fc-initial-auth-state t 10 :starttls '(110 111 100 101)
                            '(115 101 99 114 101 116) nil))
(defconst *fc-auth-starttls* (fn-fc-step *fc-auth0* '(50 48 48 13 10)))
(defconst *fc-auth-tls*
  (fn-fc-step (fn-fc-next-state *fc-auth-starttls*) '(51 56 50 13 10)))
(defconst *fc-auth-user* (fn-fc-after-tls (fn-fc-next-state *fc-auth-tls*)))
(assert-event (equal (fn-fc-kind *fc-auth-user*) :auth-user))
(assert-event
 (equal (fn-fc-auth-user-command (fn-fc-next-state *fc-auth-user*))
        '(65 85 84 72 73 78 70 79 32 85 83 69 82 32 110 111 100 101 13 10)))
(defconst *fc-auth-pass*
  (fn-fc-step (fn-fc-next-state *fc-auth-user*) '(51 56 49 13 10)))
(assert-event (equal (fn-fc-kind *fc-auth-pass*) :auth-pass))
(assert-event
 (equal (fn-fc-auth-pass-command (fn-fc-next-state *fc-auth-pass*))
        '(65 85 84 72 73 78 70 79 32 80 65 83 83 32
          115 101 99 114 101 116 13 10)))
(defconst *fc-auth-mode*
  (fn-fc-step (fn-fc-next-state *fc-auth-pass*) '(50 56 49 13 10)))
(assert-event (equal (fn-fc-kind *fc-auth-mode*) :mode))
; A failed password and an interrupted exchange never reach ready.
(assert-event
 (equal (fn-fc-kind
         (fn-fc-step (fn-fc-next-state *fc-auth-pass*) '(52 56 49 13 10)))
        :refused))
(assert-event
 (equal (fn-fc-phase (fn-fc-lost (fn-fc-next-state *fc-auth-pass*))) :closed))
; Cleartext credentials require the explicit local policy bit.
(assert-event
 (equal (fn-fc-kind
         (fn-fc-step
          (fn-fc-initial-auth-state nil 11 :clear '(117) '(112) nil)
          '(50 48 48 13 10)))
        :refused))
(assert-event
 (equal (fn-fc-kind
         (fn-fc-step
          (fn-fc-initial-auth-state nil 12 :clear '(117) '(112) t)
          '(50 48 48 13 10)))
        :auth-user))

; PRF-130 (the walk, finding c), restated by PRF-207: a peer answering MODE
; STREAM with a code other than 203, 500 or 501 (here 502) is a streaming
; refusal; recorded, the peer is not dialled again.
(defconst *fc-mode-state* (fn-fc-next-state *fc-mode*))
(assert-event (equal (fn-fc-phase *fc-mode-state*) :mode))
(defconst *fc-502* (fn-fc-step *fc-mode-state* '(53 48 50 32 110 111 13 10)))
(assert-event (not (fn-fc-mode-unsupportedp '(53 48 50 32 110 111))))
(assert-event (equal (fn-fc-kind *fc-502*) :refused))
(assert-event (equal (fn-fc-phase (fn-fc-next-state *fc-502*)) :closed))
(assert-event (fn-fc-streaming-refusal-p *fc-mode-state* *fc-502*))
(assert-event (fn-fc-dial-allowedp t "hub" nil))
(assert-event (not (fn-fc-dial-allowedp t "hub" (fn-fc-stopped-put "hub" :mode-stream-refused nil))))
(assert-event (fn-fc-dial-allowedp t "far" (fn-fc-stopped-put "hub" :mode-stream-refused nil)))
(assert-event (fn-fc-stopped-reason "hub" (fn-fc-stopped-put "hub" :mode-stream-refused nil)))
; Tooth for PRF-207's added hypothesis (not 500/501): 501 is no longer a
; refusal, so the old statement is false, and its counterexample is below.
(must-fail
 (defthm fc-old-prf-130-mode-stream-refusal-stops-the-dial
   (implies (and (fn-fc-statep st)
                 (equal (fn-fc-phase st) :mode)
                 (fn-fwi-chunkp octets)
                 (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
                 (not (equal (fn-own-feed-response-code
                              (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))
                             203)))
            (equal (fn-fc-kind (fn-fc-step st octets)) :refused))
   :hints (("Goal" :in-theory (disable fn-fc-step fn-fwi-step fn-fwi-kind
                                       fn-fwi-line fn-fc-statep
                                       fn-own-feed-response-code)))))

; PRF-207: 500 and 501 (RFC 3977 section 3.2.1) make the SAME connection
; ready with streaming off; the owner then offers with IHAVE on it.  The
; keystone fn-fc-mode-stream-unsupported-falls-back-to-ihave, positive
; witnesses with the full antecedent and conclusion, for 501 and 500.
(defun fc-fallback-antecedent (st octets)
  (and (fn-fc-statep st)
       (equal (fn-fc-phase st) :mode)
       (fn-fwi-chunkp octets)
       (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
       (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))))
(defun fc-fallback-conclusion (st octets)
  (let* ((step (fn-fc-step st octets))
         (n (fn-fc-next-state step)))
    (and (equal (fn-fc-kind step) :ready)
         (equal (fn-fc-phase n) :ready)
         (not (fn-fc-streamingp n))
         (equal (fn-fc-conn n) (fn-fc-conn st))
         (equal (fn-fc-security n) (fn-fc-security st))
         (equal (fn-fc-user n) (fn-fc-user st))
         (equal (fn-fc-pass n) (fn-fc-pass st))
         (not (fn-fc-streaming-refusal-p st step)))))
(defconst *fc-501-line* '(53 48 49 32 110 111 13 10))
(defconst *fc-500-line* '(53 48 48 32 119 104 97 116 63 13 10))
(assert-event (fc-fallback-antecedent *fc-mode-state* *fc-501-line*))
(assert-event (fc-fallback-conclusion *fc-mode-state* *fc-501-line*))
(assert-event (fc-fallback-antecedent *fc-mode-state* *fc-500-line*))
(assert-event (fc-fallback-conclusion *fc-mode-state* *fc-500-line*))
(assert-event (fn-fc-statep (fn-fc-next-state (fn-fc-step *fc-mode-state* *fc-501-line*))))
; The streaming state it started from asked for streaming: non-degenerate.
(assert-event (fn-fc-streamingp *fc-mode-state*))
; With a credential, the credential is kept.
(defconst *fc-cred-mode*
  (list (fn-fwi-initial-state) t :mode 9 :clear '(117) '(112) t))
(assert-event (fc-fallback-antecedent *fc-cred-mode* *fc-501-line*))
(assert-event (fc-fallback-conclusion *fc-cred-mode* *fc-501-line*))
(assert-event (equal (fn-fc-user (fn-fc-next-state (fn-fc-step *fc-cred-mode* *fc-501-line*))) '(117)))

(defmacro fc-fallback-tooth (name hyps)
  `(must-fail
    (defthm ,name
      (implies (and ,@hyps) (fc-fallback-conclusion st octets))
      :hints (("Goal" :in-theory (disable fn-fc-step fn-fwi-step fn-fwi-kind
                                          fn-fwi-line fn-fc-statep
                                          fn-fc-mode-unsupportedp))))))
; Tooth, (fn-fc-statep st): a state whose connection is not a number is
; invalid, not ready.
(defconst *fc-bad-state* (list (fn-fwi-initial-state) t :mode 'x :clear))
(assert-event (and (not (fn-fc-statep *fc-bad-state*))
                   (equal (fn-fc-phase *fc-bad-state*) :mode)
                   (fn-fwi-chunkp *fc-501-line*)
                   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input *fc-bad-state*) *fc-501-line*)) :line)
                   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input *fc-bad-state*) *fc-501-line*)))
                   (not (fc-fallback-conclusion *fc-bad-state* *fc-501-line*))))
(fc-fallback-tooth fc-fallback-without-statep
  ((equal (fn-fc-phase st) :mode) (fn-fwi-chunkp octets)
   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))))
; Tooth, (equal (fn-fc-phase st) :mode): after 203 the connection is ready
; and a 501 is an ordinary reply for the feed.
(defconst *fc-ready-state* (fn-fc-next-state (fn-fc-step *fc-mode-state* '(50 48 51 32 111 107 13 10))))
(assert-event (and (fn-fc-statep *fc-ready-state*)
                   (not (equal (fn-fc-phase *fc-ready-state*) :mode))
                   (fn-fwi-chunkp *fc-501-line*)
                   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input *fc-ready-state*) *fc-501-line*)) :line)
                   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input *fc-ready-state*) *fc-501-line*)))
                   (equal (fn-fc-kind (fn-fc-step *fc-ready-state* *fc-501-line*)) :reply)
                   (not (fc-fallback-conclusion *fc-ready-state* *fc-501-line*))))
(fc-fallback-tooth fc-fallback-without-mode-phase
  ((fn-fc-statep st) (fn-fwi-chunkp octets)
   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))))
; Tooth, (fn-fwi-chunkp octets): a non-octet chunk is invalid.
(assert-event (and (fn-fc-statep *fc-mode-state*)
                   (not (fn-fwi-chunkp '(53 48 49 -1 13 10)))
                   (not (fc-fallback-conclusion *fc-mode-state* '(53 48 49 -1 13 10)))))
(fc-fallback-tooth fc-fallback-without-chunk
  ((fn-fc-statep st) (equal (fn-fc-phase st) :mode)
   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)
   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))))
; Tooth, a complete line: "50" alone is no answer yet.
(assert-event (and (fn-fc-statep *fc-mode-state*)
                   (fn-fwi-chunkp '(53 48))
                   (not (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input *fc-mode-state*) '(53 48))) :line))
                   (not (fc-fallback-conclusion *fc-mode-state* '(53 48)))))
(fc-fallback-tooth fc-fallback-without-line
  ((fn-fc-statep st) (equal (fn-fc-phase st) :mode) (fn-fwi-chunkp octets)
   (fn-fc-mode-unsupportedp (fn-fwi-line (fn-fwi-step (fn-fc-input st) octets)))))
; Tooth, (fn-fc-mode-unsupportedp line): 203 streams (streaming stays on),
; 502 refuses.
(assert-event (and (fn-fc-statep *fc-mode-state*)
                   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input *fc-mode-state*) '(50 48 51 32 111 107 13 10))) :line)
                   (not (fn-fc-mode-unsupportedp '(50 48 51 32 111 107)))
                   (not (fc-fallback-conclusion *fc-mode-state* '(50 48 51 32 111 107 13 10)))
                   (not (fc-fallback-conclusion *fc-mode-state* '(53 48 50 32 110 111 13 10)))))
(fc-fallback-tooth fc-fallback-without-unsupported
  ((fn-fc-statep st) (equal (fn-fc-phase st) :mode) (fn-fwi-chunkp octets)
   (equal (fn-fwi-kind (fn-fwi-step (fn-fc-input st) octets)) :line)))

; Without the :mode phase: a greeting refusal is a refusal, not a streaming one.
(defconst *fc-greet-state* (fn-fc-initial-state t 1 :clear))
(defconst *fc-greet-502* (fn-fc-step *fc-greet-state* '(53 48 50 13 10)))
(assert-event (equal (fn-fc-kind *fc-greet-502*) :refused))
(assert-event (not (fn-fc-streaming-refusal-p *fc-greet-state* *fc-greet-502*)))
; Without the non-203 hypothesis: 203 makes the connection ready.
(defconst *fc-203* (fn-fc-step *fc-mode-state* '(50 48 51 32 111 107 13 10)))
(assert-event (equal (fn-fc-kind *fc-203*) :ready))
(assert-event (not (fn-fc-streaming-refusal-p *fc-mode-state* *fc-203*)))
; Without a complete line: no reply yet, no refusal.
(defconst *fc-partial* (fn-fc-step *fc-mode-state* '(53 48)))
(assert-event (equal (fn-fc-kind *fc-partial*) :need-input))
(assert-event (not (fn-fc-streaming-refusal-p *fc-mode-state* *fc-partial*)))
; Nothing queued: no dial even without a stop.
(assert-event (not (fn-fc-dial-allowedp nil "hub" nil)))
