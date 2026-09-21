; Teeth for the ACL2-owned outbound connection phase.
(in-package "ACL2")
(include-book "../../books/feed-connection")

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
(assert-event (equal (fn-fc-kind
                      (fn-fc-step (fn-fc-next-state *fc-mode*) '(53 48 48 13 10)))
                     :refused))
(defconst *fc-lost* (fn-fc-lost (fn-fc-next-state *fc-coalesced*)))
(assert-event (equal (fn-fc-phase *fc-lost*) :closed))
(assert-event (equal (fn-fc-kind (fn-fc-step *fc-lost* nil))
                     :closed))
