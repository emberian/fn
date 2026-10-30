; The interims of D5 1/n (fn2/docs/d-machines-nntp.md section 14.4, 14.7),
; each an owed row with its fixture so that it is lifted, not forgotten.
; Their subject is the served core under a profile that serves posting, at
; its adapter boundary (fn2-conn-wire-run-in, owed-conn.lisp): a client's
; wire for a POST transcript arriving in given chunk sizes. Each row's teeth
; are in tests/txn-unit.lisp. T6 and T9 (section 14.6) are written with the
; durable POST (D5 2/n), whose subject the batch member gives them.
(in-package "ACL2")
(include-book "owed-conn")
(fn2-book-layer :d)

; Posting served with two upload windows of 4 KiB chunks and room for C's
; engine (4 KiB arenas, the bind scratch).
;; One group carried at genesis (S-GROUP): local.test is group 1.
(defconst *fn2-txn-posting-profile*
 (put-assoc-equal :groups '(("local.test" . 1))
  (put-assoc-equal :identity-arena-bytes 4096
    (put-assoc-equal :posting-interim t
      (put-assoc-equal :format-slots 5
        (put-assoc-equal :pool-classes '((8 . 1024) (16 . 4096)) *fn2-conn-wire-profile*))))))
(defun fn2-txn-wire-solo (octets sizes)
  (declare (xargs :verify-guards nil))
  (car (nth 1 (fn2-conn-wire-run-in *fn2-txn-posting-profile* (list (list octets sizes))))))
(defun fn2-txn-post-octets (lines)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets (append '("POST") lines '("." "QUIT"))))
(defconst *fn2-txn-article*
  '("From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
    "Message-ID: <one@example.invalid>" "" "body"))
(defun fn2-txn-interim-wire (reply)
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets (list "200 fn-nntp experimental server ready" "340 send article to be posted" reply
                                  "205 closing connection"))
        t))

(defthm-owed fn2-txn-admission-interim (sizes)
  (implies (nat-listp sizes)
           (equal (fn2-txn-wire-solo (fn2-txn-post-octets *fn2-txn-article*) sizes)
                  (fn2-txn-interim-wire "441 posting failed")))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-txn-test-admission-interim fn2-txn-test-admission-interim-negative)
  :doc "Interim until B-S2 (B's transaction member, fn2-commit-admit-txn): the transaction stages its slots at :ready and the interim admission answers :not-served, so a valid POST whose Message-ID is unrecorded is refused :not-stored (the generic 441), however it is chunked. The slots it stages are the identity fact, the article row, the operation outcome and one group-count accept per carried group; the overview row (its line) and the addr entries come with D5 2/n. Lifting it replaces this row with T6 (accepted only on durable and published evidence, uncertain from log-write, refused otherwise) and T9.")

(defthm-owed fn2-txn-generated-message-id-interim (sizes)
  (implies (nat-listp sizes)
           (equal (fn2-txn-wire-solo (fn2-txn-post-octets (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*))
                                     sizes)
                  (fn2-txn-interim-wire "441 posting failed")))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-txn-test-generated-interim fn2-txn-test-generated-interim-negative)
  :doc "Interim until injection (D5 2/n: the clock reading, the agent, RFC 5537's injected block): a POST that supplies no Message-ID takes no claim and no identity decision; after the upload's verdict it is refused :not-stored. Lifting it generates the Message-ID from the injection reading (specs/nntp.md 824-856), claims it and decides it like a supplied one.")
