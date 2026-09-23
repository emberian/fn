; RFC 3977 HDR :fn-verified against a pinned, historical verdict list.
(in-package "ACL2")
(include-book "../../books/nntp-verdict-effects")

(defconst *nv-id* "<verdict@fn.invalid>")
(defconst *nv-article*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 118 101 114 100 105 99
    116 64 102 110 46 105 110 118 97 108 105 100 62 13 10 13 10 120 13 10))
(defconst *nv-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state '("fn.letters")) 1 *nv-id*
                      *nv-article* '("fn.letters") :legacy)
   0 1 :durable))
(defconst *nv-session* (fn-nntp-open-session *nv-archive*))
(defconst *nv-principal*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(defconst *nv-pin*
  (list (cons *nv-id* (fn-stx-make-verdict :verified *nv-principal* 7))))

(assert-event
 (fn-nntp-effectsp
  (fn-nntp-result-effects
   (fn-nntp-verdict-hdr-response
    *nv-session* *nv-archive* *nv-pin*
    (list (fn-nntp-string-octets ":fn-verified")
          (fn-nntp-string-octets *nv-id*))))))

(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-verdict-hdr-response
          *nv-session* *nv-archive* *nv-pin*
          (list (fn-nntp-string-octets ":fn-verified")
                (fn-nntp-string-octets *nv-id*))))
        (list (list :reply
                    (append (fn-nntp-string-octets "225 headers follow")
                            '(13 10 48 32 118 101 114 105 102 105 101 100 32)
                            (append (fn-stx-hex-octets *nv-principal*)
                                    (append (fn-nntp-string-octets " keyring 7")
                                            '(13 10 46 13 10))))))))

; Querying the same accepted archive with a different later verdict list
; would produce a different answer.  The connection therefore has to keep
; its own verdict pin across both posting and keyring changes.
(assert-event
 (let ((later (cons (cons *nv-id*
                          (fn-stx-make-verdict :unverified :signature 8))
                    *nv-pin*)))
   (not (equal (fn-nntp-result-effects
                (fn-nntp-verdict-hdr-response
                 *nv-session* *nv-archive* *nv-pin*
                 (list (fn-nntp-string-octets ":fn-verified")
                       (fn-nntp-string-octets *nv-id*))))
               (fn-nntp-result-effects
                (fn-nntp-verdict-hdr-response
                 *nv-session* *nv-archive* later
                 (list (fn-nntp-string-octets ":fn-verified")
                       (fn-nntp-string-octets *nv-id*))))))))
