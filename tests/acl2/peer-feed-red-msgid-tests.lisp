; Red-before/green-after witness for rp-feed-reply-msgid (lane peer-feed, 2026-10-04).
; The assertion is the fixed behaviour, in vocabulary the base and the fix
; share: RED at lane/read-peer@9ab11e8ee (certify-20261004T171953Z-23799),
; green on lane/peer-feed.
(in-package "ACL2")
(include-book "../../books/owner-feed")

(defconst *pfr-peer* '(105 110 110))
(defconst *pfr-a* '(60 97 64 102 110 62))
(defconst *pfr-b* '(60 98 64 102 110 62))
(defconst *pfr-contact* (fn-sched-contact "inn" 0 1000000))
(defconst *pfr-obs* (fn-clock-observation 10 0 0 nil))

; rp-feed-reply-msgid: a TAKETHIS reply `239 <b@fn>' read while <a@fn> is in
; flight names <b@fn>, not the entry in flight.
(assert-event
 (equal (fn-feed-response-msgid
         (fn-own-feed-parse-response
          (append '(50 51 57 32) *pfr-b* '(13 10)) *pfr-a*))
        *pfr-b*))
