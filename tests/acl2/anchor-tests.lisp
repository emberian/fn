;; Witnesses and teeth for the external freshness anchor.
;;
;; The genuine witness is a real Roughtime response captured from
;; roughtime.int08h.com:2002 on 2026-09-19, saved as
;; tests/vectors/roughtime-int08h-2026-09-19.json.  Its fields are transcribed
;; below, and the first two assertions are that ACL2's reconstruction of the
;; two messages the server signed -- the delegation DELE and the response SREP
;; -- is octet-for-octet what the server sent.  That is what makes this book,
;; and not the host, the owner of what a signature covers.

(in-package "ACL2")

(include-book "../../books/anchor-invariants")
(include-book "std/testing/must-fail" :dir :system)

;; -----------------------------------------------------------------------------
;; The captured response

(defconst *anchor-key* '(1 110 110 2 132 210 76 55 198 228 215 216 213 180 225 211 193 148
    156 234 165 69 191 135 86 22 201 220 224 201 190 193))
(defconst *anchor-delegate* '(112 225 147 18 154 229 157 97 162 171 106 245 153 162 69 214 84
    231 236 149 66 50 74 243 234 59 223 111 207 214 35 185))
(defconst *anchor-dele-sig* '(87 225 33 224 241 80 220 225 1 150 133 87 82 115 28 33 135 244 117
    247 106 201 154 207 152 226 221 225 39 169 161 114 23 19 115 137
    134 116 246 138 52 156 54 11 61 7 92 144 175 88 216 182 45 47 9
    144 97 138 145 112 8 93 207 15))
(defconst *anchor-nonce* '(149 179 179 248 80 223 100 39 92 132 72 216 112 168 89 251 30 78
    105 10 198 180 78 22 216 60 18 215 138 163 162 193))
(defconst *anchor-signature* '(167 176 13 248 220 115 89 127 133 217 185 95 250 61 214 214 111 99
    179 138 247 227 191 171 231 159 119 111 19 222 210 42 155 123 234
    58 32 17 33 7 21 40 82 150 147 224 224 224 134 229 216 172 42 96
    11 145 67 174 202 140 193 102 5 3))
(defconst *anchor-root* '(254 82 135 71 189 187 83 171 13 4 181 230 42 123 242 229 198 219
    113 137 206 39 198 24 190 15 16 30 59 254 239 50 233 1 28 45 176
    61 76 83 102 108 2 83 35 251 121 82 28 28 160 248 150 151 44 149
    212 120 181 252 16 170 228 126))
(defconst *anchor-srep* '(3 0 0 0 4 0 0 0 12 0 0 0 82 65 68 73 77 73 68 80 82 79 79 84 64 75
    76 0 225 226 191 57 215 91 6 0 254 82 135 71 189 187 83 171 13 4
    181 230 42 123 242 229 198 219 113 137 206 39 198 24 190 15 16 30
    59 254 239 50 233 1 28 45 176 61 76 83 102 108 2 83 35 251 121 82
    28 28 160 248 150 151 44 149 212 120 181 252 16 170 228 126))
(defconst *anchor-dele* '(3 0 0 0 32 0 0 0 40 0 0 0 80 85 66 75 77 73 78 84 77 65 88 84 112
    225 147 18 154 229 157 97 162 171 106 245 153 162 69 214 84 231
    236 149 66 50 74 243 234 59 223 111 207 214 35 185 0 0 0 0 0 0 0 0
    255 255 255 255 255 255 255 255))
(defconst *anchor-midpoint* 1789829805236961)
(defconst *anchor-radius* 5000000)
(defconst *anchor-mint* 0)
(defconst *anchor-maxt* 18446744073709551615)

(defconst *anchor-live*
  (fn-anchor *anchor-key* *anchor-delegate* *anchor-mint* *anchor-maxt*
             *anchor-dele-sig* *anchor-midpoint* *anchor-radius*
             *anchor-nonce* *anchor-signature*))

(assert-event (fn-anchor-p *anchor-live*))

;; ACL2 rebuilds the server's SREP exactly.  A different nonce is a different
;; Merkle root is a different signed message, so the nonce is load-bearing.
(assert-event
 (equal (fn-anchor-srep-from-root *anchor-radius* *anchor-midpoint* *anchor-root*)
        *anchor-srep*))
(assert-event (equal (len *anchor-srep*) 100))

;; And it rebuilds the delegation the pinned long-term key signed.
(assert-event (equal (fn-anchor-dele-octets *anchor-live*) *anchor-dele*))
(assert-event (equal (len *anchor-dele*) 72))

(assert-event
 (equal (fn-anchor-signed-from-root *anchor-radius* *anchor-midpoint* *anchor-root*)
        (append *fn-anchor-response-context* *anchor-srep*)))
(assert-event
 (equal (fn-anchor-delegation-signed-octets *anchor-live*)
        (append *fn-anchor-delegation-context* *anchor-dele*)))

;; The captured midpoint really is inside the window it was delegated for.
(assert-event (<= *anchor-mint* *anchor-midpoint*))
(assert-event (<= *anchor-midpoint* *anchor-maxt*))

;; A key one octet short is not a key and a signature one octet short is not a
;; signature: the field widths are part of the statement.
(assert-event
 (not (fn-anchor-p (fn-anchor (cdr *anchor-key*) *anchor-delegate* *anchor-mint*
                              *anchor-maxt* *anchor-dele-sig* *anchor-midpoint*
                              *anchor-radius* *anchor-nonce* *anchor-signature*))))
(assert-event
 (not (fn-anchor-p (fn-anchor *anchor-key* *anchor-delegate* *anchor-mint*
                              *anchor-maxt* *anchor-dele-sig* *anchor-midpoint*
                              *anchor-radius* *anchor-nonce*
                              (cdr *anchor-signature*)))))

;; -----------------------------------------------------------------------------
;; The interval order, on real numbers from the captured response
;;
;; The radius is five seconds.  An earlier reading is strictly older only when
;; its whole interval clears the later one: ten seconds apart is not enough,
;; thirty is.

(defun anchor-at (midpoint)
  (declare (xargs :guard (fn-anchor-timep midpoint)))
  (fn-anchor *anchor-key* *anchor-delegate* *anchor-mint* *anchor-maxt*
             *anchor-dele-sig* midpoint *anchor-radius* *anchor-nonce*
             *anchor-signature*))

(defconst *anchor-older* (anchor-at (- *anchor-midpoint* 30000000)))
(defconst *anchor-overlapping* (anchor-at (- *anchor-midpoint* 5000000)))
(defconst *anchor-newer* (anchor-at (+ *anchor-midpoint* 30000000)))

(assert-event (fn-anchor-newerp *anchor-live* *anchor-older*))
(assert-event (not (fn-anchor-newerp *anchor-older* *anchor-live*)))
(assert-event (not (fn-anchor-newerp *anchor-live* *anchor-overlapping*)))
(assert-event (not (fn-anchor-newerp *anchor-overlapping* *anchor-live*)))
(assert-event (not (fn-anchor-newerp *anchor-live* *anchor-live*)))

;; -----------------------------------------------------------------------------
;; Acceptance, through the entry the host actually calls
;;
;; `t' below is the host's Ed25519 verdict over the octets ACL2 produced; the
;; live Python check of that verdict is tests/test_anchor.py.

(defconst *anchor-pinned* (list *anchor-key*))
(defconst *anchor-node-fresh* (fn-anchor-node *anchor-pinned* nil 7))
(defconst *anchor-node-held* (fn-anchor-node *anchor-pinned* *anchor-older* 7))
(defconst *anchor-node-current* (fn-anchor-node *anchor-pinned* *anchor-live* 7))

(assert-event (fn-anchor-nodep *anchor-node-held*))

(assert-event
 (equal (fn-anchor-status
         (fn-anchor-node-accept-observed *anchor-node-held* *anchor-live* t))
        :accepted))
(assert-event
 (equal (fn-anchor-node-latest
         (fn-anchor-payload
          (fn-anchor-node-accept-observed *anchor-node-held* *anchor-live* t)))
        *anchor-live*))

;; Replaying the older response at a node that holds the live one is stale.
(assert-event
 (equal (fn-anchor-reason
         (fn-anchor-node-accept-observed *anchor-node-current* *anchor-older* t))
        :stale))
;; An overlapping reading is refused too: not knowing which came first is not
;; permission to advance.
(assert-event
 (equal (fn-anchor-reason
         (fn-anchor-node-accept-observed *anchor-node-current*
                                         *anchor-overlapping* t))
        :stale))
;; A failed Ed25519 check is a refusal with its own reason, never an accept.
(assert-event
 (equal (fn-anchor-reason
         (fn-anchor-node-accept-observed *anchor-node-held* *anchor-live* nil))
        :unverified))
;; A server this node does not pin is refused, verdict or no verdict.
(assert-event
 (equal (fn-anchor-reason
         (fn-anchor-node-accept-observed
          (fn-anchor-node (list (cons 200 (cdr *anchor-key*))) *anchor-older* 7)
          *anchor-live* t))
        :unpinned))
;; No anchor at all is uncertain, which is neither of the other two.
(assert-event
 (equal (fn-anchor-status
         (fn-anchor-node-accept-observed *anchor-node-held* nil t))
        :uncertain))

;; -----------------------------------------------------------------------------
;; Restore: the FLR-003 case, an intact old snapshot

(defconst *anchor-image-old* (fn-anchor-image 7 *anchor-live*))
(defconst *anchor-image-unanchored* (fn-anchor-image 7 nil))

(assert-event
 (equal (fn-anchor-reason
         (fn-anchor-restore-observed *anchor-node-fresh* *anchor-image-old*
                                     *anchor-older* t))
        :possibly-stale))
(assert-event
 (equal (fn-anchor-status
         (fn-anchor-restore-observed *anchor-node-fresh* *anchor-image-old*
                                     *anchor-older* t))
        :refused))

;; The same image under a genuinely newer anchor is accepted, and it opens the
;; next incarnation rather than continuing the one in the snapshot.
(assert-event
 (equal (fn-anchor-status
         (fn-anchor-restore-observed *anchor-node-fresh* *anchor-image-old*
                                     *anchor-newer* t))
        :accepted))
(assert-event
 (equal (fn-anchor-node-incarnation
         (fn-anchor-payload
          (fn-anchor-restore-observed *anchor-node-fresh* *anchor-image-old*
                                      *anchor-newer* t)))
        8))

;; An image that refers to no anchor has nothing to be stale against.
(assert-event
 (equal (fn-anchor-status
         (fn-anchor-restore-observed *anchor-node-fresh*
                                     *anchor-image-unanchored* *anchor-older* t))
        :accepted))
;; With no anchor obtainable the restore is uncertain, not refused.
(assert-event
 (equal (fn-anchor-status
         (fn-anchor-restore-observed *anchor-node-fresh* *anchor-image-old* nil t))
        :uncertain))

;; -----------------------------------------------------------------------------
;; Fork evidence

(defconst *anchor-image-fork* (fn-anchor-image 7 *anchor-newer*))

(assert-event
 (equal (fn-anchor-reason (fn-anchor-pair-admit *anchor-image-old*
                                                *anchor-image-fork*))
        :fork))
(assert-event
 (equal (fn-anchor-payload (fn-anchor-pair-admit *anchor-image-old*
                                                 *anchor-image-fork*))
        (list *anchor-image-old* *anchor-image-fork*)))
(assert-event
 (not (fn-anchor-pair-admittedp (fn-anchor-pair-admit *anchor-image-old*
                                                      *anchor-image-fork*))))
(assert-event
 (fn-anchor-pair-admittedp (fn-anchor-pair-admit *anchor-image-old*
                                                 *anchor-image-old*)))
(assert-event
 (equal (fn-anchor-status (fn-anchor-pair-admit *anchor-image-old*
                                                (fn-anchor-image 8 *anchor-newer*)))
        :distinct))

;; -----------------------------------------------------------------------------
;; The durable FNAN record round-trips the captured anchor

(defconst *anchor-values*
  (list *anchor-key* *anchor-delegate* *anchor-mint* *anchor-maxt*
        *anchor-dele-sig* *anchor-midpoint* *anchor-radius* *anchor-nonce*
        *anchor-signature*))
(defconst *anchor-digest*
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
    16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31))

(assert-event (fn-anchor-record-okp :observed *anchor-values*))
(assert-event
 (equal (fn-anchor-record-anchor :observed *anchor-values*) *anchor-live*))
(assert-event
 (equal (fn-anchor-decode (fn-anchor-encode :observed *anchor-values*
                                            *anchor-digest*)
                          *anchor-digest*)
        (fn-frame-ok *fn-anchor-magic* *fn-frame-version* :observed
                     *anchor-values*)))
;; The incarnation record carries the same anchor under a number.
(assert-event
 (equal (fn-anchor-record-anchor :incarnation (cons 7 *anchor-values*))
        *anchor-live*))
;; A truncated key is refused by the record grammar, not silently padded.
(assert-event
 (not (fn-anchor-record-okp :observed (cons (cdr *anchor-key*)
                                            (cdr *anchor-values*)))))
