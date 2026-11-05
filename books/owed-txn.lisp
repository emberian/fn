; The interims of D5 1/n (docs/d-machines-nntp.md section 14.4, 14.7),
; each an owed row with its fixture so that it is lifted, not forgotten.
; Their subject is the served core under a profile that serves posting, at
; its adapter boundary (fn2-conn-wire-run-in, owed-conn.lisp): a client's
; wire for a POST transcript arriving in given chunk sizes. Each row's teeth
; are in tests/txn-unit.lisp. T6 and T9 (section 14.6) are written with the
; durable POST (D5 2/n), whose subject the batch member gives them.
(in-package "ACL2")
(include-book "owed-conn")
(include-book "assembly-attach")
(fn2-book-layer :d)

; Posting served with two upload windows of 4 KiB chunks and room for C's
; engine (4 KiB arenas, the bind scratch), and twelve 64 KiB slots: the two
; windows, the sealer's page workspace and the resident pages of the runs a
; seeded POST seals (one per schema it writes, C §4a's five among them).
;; One group carried at genesis (S-GROUP): local.test is group 1.
(defconst *fn2-txn-posting-profile*
 (put-assoc-equal :groups '(("local.test" . 1))
  (put-assoc-equal :identity-overlays 64
   (put-assoc-equal :identity-arena-bytes 4096
     (put-assoc-equal :posting-interim t
       (put-assoc-equal :large-upload-windows 2
         (put-assoc-equal :pool-classes '((8 . 1024) (128 . 4096) (64 . 65536)) *fn2-conn-wire-profile*)))))))
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
                  (fn2-txn-interim-wire "240 article received OK")))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-txn-test-admission-interim fn2-txn-test-admission-interim-negative)
  :doc "D5 2/n: a valid POST whose Message-ID is unrecorded stages its slots at :ready, emits the transaction member's record stream into chunk 1, admits the member to B's commit batch, binds the successor, and after the commit batch publishes and settles, answers 240 article received OK, however it is chunked.")

(defthm-owed fn2-txn-generated-message-id (sizes)
  (implies (nat-listp sizes)
           (equal (fn2-txn-wire-solo (fn2-txn-post-octets (remove-equal (nth 3 *fn2-txn-article*) *fn2-txn-article*))
                                     sizes)
                  (fn2-txn-interim-wire "240 article received OK")))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-txn-test-generated fn2-txn-test-generated-negative)
  :doc "Injection (D5 2/n, RFC 5537 3.5): a POST that supplies no Message-ID is given one by the node, <fn2.E.A@P> (RFC 5536 3.1.3; E.A its payload extent's writer epoch and allocation, P the path identity), stored as the article's first field before the source; it is claimed and decided like a supplied one and answers 240, however it is chunked. Owed with injection: Date, Path, Injection-Info and Injection-Date, and P from the profile.")
