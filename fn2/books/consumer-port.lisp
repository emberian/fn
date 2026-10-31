; The consumer port (layer E3; fn2/docs/e-surface.md sections 1-6). Ten verbs
; over the one engine, and the three carriers that speak them: L, the owner's
; control socket (FNCT kind 4; the port's codes, and fn1's codes 0-10 with
; fn1's payloads, translated: consumer-codec.lisp section 5); R, the
; authenticated NNTP connection (XFNC and one framed FNCT body; the port's
; codes only, scoped to the login by the grant step); N, the NNTP convention
; (append is POST, fetch is ARTICLE), with its losses declared.
(in-package "ACL2")
(include-book "port")
(include-book "nntp-grammar")
(fn2-book-layer :e)

(defport fn2-consumer
  :fields ((consumer (:octets 64)) (query :edges) (cursor (:octets 366)) (limits :limits)
           (timeout :u32) (stream :stream) (article :handle) (op (:octets 64))
           (position :position) (frontier :position) (counters :counters) (reference :reference)
           (items :items) (more :u8) (next (:octets 366))
           (message-id (:octets 250)) (numbers :numbers) (receipt :receipt))
  :reasons (scope behind beyond-frontier rebase-required unknown-consumer query
            waiters cursor-version operation-reused operation-expired frame addressees
            unavailable withdrawn
            ; D5's typed POST refusals (d-machines-nntp.md 14.5), the same words
            duplicate conflict unaffordable unknown-group malformed-article)
  :verbs
  ((register :request (consumer query) :result (cursor)
             :effect :durable :retry :idempotent :grant (:consume consumer) :meter (:requests :durable-octets)
             :reasons (query rebase-required)
             :spec "e-surface.md 3, 7; consumer-progress.md L67-80; INBOX 4.3")
   (rebase :request (cursor (:opt query)) :result (cursor)
           :effect :durable :retry :idempotent :grant (:consume cursor) :meter (:requests :durable-octets)
           :reasons (scope unknown-consumer query)
           :spec "e-surface.md 3, 7; consumer-progress.md L108-112; INBOX 4.3")
   (unregister :request (cursor) :result ()
               :effect :durable :retry :idempotent :grant (:consume cursor) :meter (:requests :durable-octets)
               :reasons (scope unknown-consumer)
               :spec "e-surface.md 3; consumer-progress.md L112-116")
   (read :request (cursor (:opt limits)) :result (items more next)
         :effect :read :retry :repeat :grant (:read cursor) :meter (:requests :tx-octets)
         :reasons (scope rebase-required unknown-consumer cursor-version)
         :spec "e-surface.md 3, 4.1, 7; consumer-progress.md L67-100; INBOX 4.4, 4.8")
   (wait :request (cursor (:opt limits) timeout) :result (items more next)
         :effect :park :retry :repeat :grant (:read cursor) :meter (:requests :tx-octets :waiter :subscription-edges)
         :reasons (scope rebase-required unknown-consumer cursor-version waiters)
         :spec "e-surface.md 3, 5, 7; consumer-progress.md L376-412 (CNS-007); INBOX 4.4; ROUND2 F scenario 7")
   (ack :request (cursor) :result (position)
        :effect :durable :retry :position :grant (:consume cursor) :meter (:requests :durable-octets)
        :reasons (scope rebase-required unknown-consumer behind beyond-frontier cursor-version)
        :spec "e-surface.md 3.2; consumer-progress.md L101-121")
   (position :request (consumer) :result (cursor)
             :effect :read :retry :repeat :grant (:consume consumer) :meter (:requests)
             :reasons (unknown-consumer)
             :spec "e-surface.md 3.2; consumer-progress.md L104-106")
   (status :request (consumer) :result (position frontier counters)
           :effect :read :retry :repeat :grant (:consume consumer) :meter (:requests)
           :reasons (unknown-consumer)
           :spec "e-surface.md 3, 8; consumer-progress.md L630-642; INBOX 4.7")
   ; An item too large for the page arrives as a reference; FETCH answers its
   ; octets under the current grant, or names why it cannot (Astra 1, item 2).
   (fetch :request (reference) :result (article)
          :effect :read :retry :repeat :grant (:read reference) :meter (:requests :tx-octets)
          :reasons (unavailable withdrawn)
          :spec "e-surface.md 3.4")
   (append :request (stream article (:opt op)) :result (message-id position numbers receipt)
           :effect :durable :retry :op :grant (:append stream) :meter (:requests :durable-octets)
           :reasons (operation-reused operation-expired addressees duplicate conflict unaffordable unknown-group
                     malformed-article)
           :spec "e-surface.md 3.3; d-machines-nntp.md 14.4-14.5; IDENTITY ruling 6; INBOX 4.2")))

; L: the owner's 0600 socket, FNCT kind 4. A verb's code is the port's own
; payload (consumer-codec.lisp section 3); ack (1) and position (2) keep fn1's
; codes because their payloads already are the port's. fn1's other codes are
; carrier forms translated to these verbs (consumer-codec.lisp section 5).
(defcarrier fn2-consumer-local :port fn2-consumer :frame :fnct
  :binds ((register 4 14) (ack 4 1) (position 4 2) (unregister 4 17) (read 4 15) (status 4 18)
          (wait 4 16) (append 4 11) (rebase 4 12) (fetch 4 13)))

; R: XFNC on the authenticated connection; the same frames and codes; every
; verb of the remote whitelist (e-surface.md 3), scoped to the login's own
; consumers by the grant step. fn1's legacy codes are not carried.
(defcarrier fn2-consumer-remote :port fn2-consumer :frame :fnct
  :binds ((register 4 14) (ack 4 1) (position 4 2) (unregister 4 17) (read 4 15) (status 4 18)
          (wait 4 16) (append 4 11) (rebase 4 12) (fetch 4 13)))

; N: the NNTP convention. An NNTP reader sees the same articles; what the
; translation loses is declared, so a bridge's loss is computed.
(defcarrier fn2-consumer-nntp :port fn2-consumer :grammar fn2-nntp
  :binds ((append post :terminal (:received :refused-duplicate :refused-conflict :refused-unaffordable :uncertain))
          (fetch article :terminal (:sent :reclaimed-msgid :withdrawn-msgid :no-msgid)))
  :loses ((append op :retry-by-message-id) (append receipt :reply-code-only) (append position :reply-code-only)
          (append numbers :reply-code-only)
          (read * :not-carried) (register * :not-carried) (rebase * :not-carried) (unregister * :not-carried)
          (wait * :not-carried) (ack * :not-carried) (position * :not-carried) (status * :not-carried)))
