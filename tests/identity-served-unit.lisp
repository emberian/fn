; Exact external-name binding through upload, identity decision, persisted
; successor/article address, and block read. No identity rows or digests
; are seeded: every candidate is submitted on the actual POST wire.
; This finite regression is not a proof of hash collision resistance or
; source-profile extraction, and does not exercise reboot recovery.
(in-package "ACL2")
(include-book "../books/owed-txn")

(defconst *fn2-is-profile*
  (put-assoc-equal :reading t
    (put-assoc-equal :x 2 *fn2-txn-posting-profile*)))
(defconst *fn2-is-source*
  '("From: a@example.invalid" "Subject: binding" "Newsgroups: local.test"
    "Message-ID: <Exact@example.invalid>" "" "original" "..dot"))
(defconst *fn2-is-conflict*
  '("From: a@example.invalid" "Subject: binding" "Newsgroups: local.test"
    "Message-ID: <Exact@example.invalid>" "" "changed" "..dot"))
(defconst *fn2-is-case-distinct*
  '("From: a@example.invalid" "Subject: binding" "Newsgroups: local.test"
    "Message-ID: <exact@example.invalid>" "" "lowercase"))
(defconst *fn2-is-input*
  (append '("POST") *fn2-is-source* '(".")
          '("POST") *fn2-is-source* '(".")
          '("POST") *fn2-is-conflict* '(".")
          '("POST") *fn2-is-case-distinct* '(".")
          '("GROUP local.test"
            "BODY 1" "BODY <Exact@example.invalid>"
            "BODY 2" "BODY <exact@example.invalid>"
            "BODY <Exac@example.invalid>" "BODY <Exactx@example.invalid>"
            "QUIT")))
; Literal independent expected replies and bytes. The conflict must not
; overwrite the earlier body's numeric address OR exact-name binding;
; ASCII case and a proper prefix/suffix are distinct external names.
(defconst *fn2-is-expected*
  '("200 fn-nntp experimental server ready"
    "340 send article to be posted" "240 article received OK"
    "340 send article to be posted"
    "441 posting failed; this article is already stored here"
    "340 send article to be posted"
    "441 posting failed; a different article with this Message-ID is stored here"
    "340 send article to be posted" "240 article received OK"
    "211 2 1 2 local.test"
    "222 1 <Exact@example.invalid> body follows" "original" "..dot" "."
    "222 0 <Exact@example.invalid> body follows" "original" "..dot" "."
    "222 2 <exact@example.invalid> body follows" "lowercase" "."
    "222 0 <exact@example.invalid> body follows" "lowercase" "."
    "430 no article with that message-id"
    "430 no article with that message-id"
    "205 closing connection"))

(defun fn2-is-run (chunk)
  (declare (xargs :verify-guards nil))
  (let* ((bytes (fn2-cw-crlf-octets *fn2-is-input*))
         (sizes (make-list (+ 1 (floor (len bytes) chunk))
                           :initial-element chunk))
         (r (fn2-conn-wire-run-in *fn2-is-profile*
                                 (list (list bytes sizes)))))
    (list (car r) (nth 2 r) (nth 1 r))))
(defun fn2-is-binding-positive (chunk)
  (declare (xargs :verify-guards nil))
  (equal (fn2-is-run chunk)
         (list :quiet 0
               (list (list (fn2-cw-crlf-octets *fn2-is-expected*) t)))))
(assert-event (fn2-is-binding-positive 4096))
(assert-event (fn2-is-binding-positive 7))
