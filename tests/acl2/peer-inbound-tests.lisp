; Transcripts and teeth for the inbound transit machine (specs/peering.md
; section 2 and section 4 K1, K2, K4-offer/transfer), through the functions
; the served path and the owner call: fn-peer-step, fn-peer-transfer,
; fn-peer-transit-outcome.  Every form is a computation on a specific node,
; configuration, session and wire event.  Guard-world audit first, then the
; configuration record, then the transcripts, then the teeth.
(in-package "ACL2")
(include-book "../../books/peer-inbound-invariants")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The peer record and the configuration (books/peer-config.lisp)

(defconst *pt-peer*
  (fn-cfg-peer-make "innA" "inn.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(defconst *pt-peer-bp*
  (fn-cfg-peer-make "dtnB" "dtnb.example" '(:bp "dtn://b/") '("fn.dtn" 4096 1)
                    nil '(:principal "b0")))
(assert-event (fn-cfg-peerp *pt-peer*))
(assert-event (fn-cfg-peerp *pt-peer-bp*))
; Each hypothesis of fn-cfg-peerp on a concrete violating value.
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "" "inn.hbox.test" '(:nntp "h" 1) nil nil '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" ".inn" '(:nntp "h" 1) nil nil '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" "inn" '(:tcp "h" 1) nil nil '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" "inn" '(:nntp "h" 1) '("fn.*" 0 1) nil '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" "inn" '(:nntp "h" 1) '("fn.*" 32769 1) nil '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" "inn" '(:nntp "h" 1) nil '("fn.*" 2 1 0) '(:principal "p")))))
(assert-event (not (fn-cfg-peerp (fn-cfg-peer-make "x" "inn" '(:nntp "h" 1) nil nil '(:password "p")))))
(assert-event
 (not (fn-cfg-peerp
       (fn-cfg-peer-make "x" "inn"
                         (list :nntp 1 "h" 119
                               (list :tls :starttls "" "/tmp/ca.pem"))
                         nil nil '(:principal "p")))))
(assert-event
 (not (fn-cfg-peerp
       (fn-cfg-peer-make "x" "inn"
                         (list :nntp 1 "h" 119
                               (list :tls :implicit
                                     (coerce (list #\n #\e #\w #\s (code-char 0)
                                                   #\x) 'string)
                                     "/tmp/ca.pem"))
                         nil nil '(:principal "p")))))
(assert-event
 (not (fn-cfg-peerp
       (fn-cfg-peer-make "x" "inn"
                         (list :nntp 1 "h" 119
                               (list :tls :implicit "news.example"
                                     (coerce (list #\/ #\t #\m #\p (code-char 0)
                                                   #\/ #\c #\a) 'string)))
                         nil nil '(:principal "p")))))
; Round trip through the rows, and the injectivity it gives.
; The rows-to-record round trip on two ground records (the general theorem
; is open, books/peer-config.lisp).
(assert-event (equal (fn-cfg-peer-of-rows "innA" (fn-cfg-peer-rows *pt-peer*)) *pt-peer*))
(assert-event (equal (fn-cfg-peer-of-rows "dtnB" (fn-cfg-peer-rows *pt-peer-bp*)) *pt-peer-bp*))
(assert-event (equal (fn-cfg-peer-of-rows "innA" nil) nil))
(assert-event (equal (len (fn-cfg-peer-rows *pt-peer*)) 8))
(assert-event (equal (len (fn-cfg-peer-rows *pt-peer-bp*)) 5))

; The configuration: the default record's change plus the node's own path
; identity and the peer, replayed to generation 1.
(defconst *pt-change*
  (append *fn-cfg-default-change*
          (list (fn-cfg-set-policy "path-identity" "fnA.hbox.test")
                (fn-cfg-set-peer-delta *pt-peer*)
                (fn-cfg-set-peer-delta *pt-peer-bp*))))
(defconst *pt-record* (fn-cfg-record-make 0 0 1 *pt-change* *fn-cfg-default-stamp*))
(assert-event (fn-cfg-recordp *pt-record*))
; The configuration codec carries both peer deltas: decode of encode is the
; record, and the encoding is one octet list (canonical by construction).
(assert-event (equal (fn-cfg-decode-exact (fn-cfg-encode *pt-record*))
                     (fn-record-parse-ok *pt-record* nil)))
(defconst *pt-cfg* (fn-config-replay 0 510 (list *pt-record*)))
(assert-event (fn-cfgp *pt-cfg*))
(assert-event (equal (fn-cfg-generation *pt-cfg*) 1))
(assert-event (equal (fn-cfg-peer-find "innA" (fn-cfg-peers (fn-cfg-value *pt-cfg*))) *pt-peer*))
(assert-event (equal (fn-cfg-peer-find "dtnB" (fn-cfg-peers (fn-cfg-value *pt-cfg*))) *pt-peer-bp*))
(assert-event (equal (fn-cfg-peer-find "ghost" (fn-cfg-peers (fn-cfg-value *pt-cfg*))) nil))
(assert-event (equal (fn-peer-local-identity *pt-cfg*) (fn-nntp-string-octets "fnA.hbox.test")))
; :remove-peer: admissible only for a configured peer; afterwards the peer is
; gone and every other slot of the value is what it was.
(defconst *pt-remove* (fn-cfg-record-make 1 1 2 (list (fn-cfg-remove-peer-delta "innA")) *fn-cfg-default-stamp*))
(assert-event (equal (fn-cfg-decode-exact (fn-cfg-encode *pt-remove*))
                     (fn-record-parse-ok *pt-remove* nil)))
(defconst *pt-cfg2* (fn-config-replay 0 510 (list *pt-record* *pt-remove*)))
(assert-event (fn-cfgp *pt-cfg2*))
(assert-event (equal (fn-cfg-generation *pt-cfg2*) 2))
(assert-event (equal (fn-cfg-peer-find "innA" (fn-cfg-peers (fn-cfg-value *pt-cfg2*))) nil))
(assert-event (equal (fn-cfg-peer-find "dtnB" (fn-cfg-peers (fn-cfg-value *pt-cfg2*))) *pt-peer-bp*))
(assert-event (equal (fn-cfg-groups (fn-cfg-value *pt-cfg2*)) (fn-cfg-groups (fn-cfg-value *pt-cfg*))))
(assert-event (equal (fn-cfg-admissible-reason (fn-cfg-value *pt-cfg2*) 3 *fn-cfg-default-stamp* 0 510
                                               (list (fn-cfg-remove-peer-delta "innA")))
                     :no-such-peer))
(assert-event (equal (fn-cfg-admissible-reason (fn-cfg-value *pt-cfg*) 2 *fn-cfg-default-stamp* 0 510
                                               (list (fn-cfg-set-peer "innA" (list (fn-cfg-row-make "other" "path-identity" "x" 0)))))
                     :peer-rows-unkeyed))
(assert-event (equal (fn-cfg-admissible-reason (fn-cfg-value *pt-cfg*) 2 *fn-cfg-default-stamp* 0 510
                                               (list (fn-cfg-set-peer "innA" nil)))
                     :peer-rows-empty))
; A re-set narrows accept-groups: the same name finds the new record.
(defconst *pt-peer-narrow*
  (fn-cfg-peer-make "innA" "inn.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.test" 32768 16) nil '(:source-address "127.0.0.1")))
(defconst *pt-cfg3* (fn-config-replay 0 510 (list *pt-record* (fn-cfg-record-make 1 1 2 (list (fn-cfg-set-peer-delta *pt-peer-narrow*)) *fn-cfg-default-stamp*))))
(assert-event (equal (fn-cfg-peer-find "innA" (fn-cfg-peers (fn-cfg-value *pt-cfg3*))) *pt-peer-narrow*))

; -----------------------------------------------------------------------------
; Path (books/path.lisp)

(defun pt-o (s) (fn-nntp-string-octets s))
(assert-event (fn-path-identityp (pt-o "fnA.hbox.test")))
(assert-event (not (fn-path-identityp (pt-o ".fnA"))))
(assert-event (not (fn-path-identityp (pt-o "fnA."))))
(assert-event (not (fn-path-identityp (pt-o "fn A"))))
(assert-event (not (fn-path-identityp nil)))
(assert-event (equal (fn-path-entries (pt-o "inn.hbox.test!fnA.hbox.test!not-for-mail"))
                     (list (pt-o "inn.hbox.test") (pt-o "fnA.hbox.test") (pt-o "not-for-mail"))))
(assert-event (equal (fn-path-entries (pt-o "a!!b")) (list (pt-o "a") nil (pt-o "b"))))
; Our identity second of three: named.
(assert-event (fn-path-names-p (pt-o "inn.hbox.test!fnA.hbox.test!not-for-mail") (pt-o "fnA.hbox.test")))
; In the tail-entry only: not named (RFC 5537 section 3.6 exclusion).
(assert-event (not (fn-path-names-p (pt-o "inn.hbox.test!origin!fnA.hbox.test") (pt-o "fnA.hbox.test"))))
; After a POSTED diagnostic: not named.
(assert-event (not (fn-path-names-p (pt-o "inn.hbox.test!.POSTED!fnA.hbox.test!origin") (pt-o "fnA.hbox.test"))))
(assert-event (not (fn-path-names-p (pt-o "inn.hbox.test!.POSTED.1.2.3.4!fnA.hbox.test!origin") (pt-o "fnA.hbox.test"))))
; Before a POSTED diagnostic: named.
(assert-event (fn-path-names-p (pt-o "fnA.hbox.test!.POSTED!origin!tail") (pt-o "fnA.hbox.test")))
; Not substring search: fnA.hbox.test.old is another identity.
(assert-event (not (fn-path-names-p (pt-o "inn!fnA.hbox.test.old!tail") (pt-o "fnA.hbox.test"))))
; An unset local identity names nothing.
(assert-event (not (fn-path-names-p (pt-o "a!!b") nil)))
(assert-event (equal (fn-path-diagnostic (pt-o "inn.hbox.test") (pt-o "inn.hbox.test!x")) '(:match)))
(assert-event (equal (fn-path-diagnostic (pt-o "inn.hbox.test") (pt-o "other!x")) (list :mismatch (pt-o "inn.hbox.test"))))

; -----------------------------------------------------------------------------
; Articles, node, session

(defun pt-lines (strings)
  (if (consp strings) (cons (pt-o (car strings)) (pt-lines (cdr strings))) nil))
(defconst *pt-a1-lines*
  (pt-lines '("Path: inn.hbox.test!not-for-mail" "From: poster@example.invalid"
              "Newsgroups: fn.letters,alt.test" "Subject: hello"
              "Date: Sat, 19 Sep 2026 12:00:00 +0000"
              "Message-ID: <a1@example.invalid>" "" "Hello, news.")))
(defconst *pt-a1* (fn-post-body-octets *pt-a1-lines*))
; What the node stores for it: Path updated with fnA.hbox.test and the
; diag-match "!" (the peer record innA expects inn.hbox.test, which IS the
; leftmost entry, RFC 5537 section 3.2.1 step 3), every other octet as sent.
(defconst *pt-a1-stored*
  (fn-post-body-octets
   (pt-lines '("Path: fnA.hbox.test!!inn.hbox.test!not-for-mail"
               "From: poster@example.invalid"
               "Newsgroups: fn.letters,alt.test" "Subject: hello"
               "Date: Sat, 19 Sep 2026 12:00:00 +0000"
               "Message-ID: <a1@example.invalid>" "" "Hello, news."))))
(defconst *pt-id1* (pt-o "<a1@example.invalid>"))
(defconst *pt-loop-lines*
  (pt-lines '("Path: inn.hbox.test!fnA.hbox.test!not-for-mail" "From: poster@example.invalid"
              "Newsgroups: fn.letters" "Subject: loop" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
              "Message-ID: <loop@example.invalid>" "" "Round and round.")))
(defconst *pt-loop* (fn-post-body-octets *pt-loop-lines*))
(defconst *pt-idloop* (pt-o "<loop@example.invalid>"))
(defconst *pt-tail*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!origin!fnA.hbox.test" "From: poster@example.invalid"
               "Newsgroups: fn.letters" "Subject: loop" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
               "Message-ID: <loop@example.invalid>" "" "Round and round."))))
(defconst *pt-posted*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!.POSTED!fnA.hbox.test!origin" "From: poster@example.invalid"
               "Newsgroups: fn.letters" "Subject: loop" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
               "Message-ID: <loop@example.invalid>" "" "Round and round."))))
(defconst *pt-noloop*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!origin!not-for-mail" "From: poster@example.invalid"
               "Newsgroups: fn.letters" "Subject: loop" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
               "Message-ID: <loop@example.invalid>" "" "Round and round."))))
(defconst *pt-alt-lines*
  (pt-lines '("Path: inn.hbox.test!not-for-mail" "From: poster@example.invalid"
              "Newsgroups: alt.test" "Subject: elsewhere" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
              "Message-ID: <alt@example.invalid>" "" "Not for us.")))
(defconst *pt-alt* (fn-post-body-octets *pt-alt-lines*))
(defconst *pt-idalt* (pt-o "<alt@example.invalid>"))
(defconst *pt-nodate*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!not-for-mail" "From: poster@example.invalid"
               "Newsgroups: fn.letters" "Subject: undated"
               "Message-ID: <nodate@example.invalid>" "" "When?"))))
(defconst *pt-idnodate* (pt-o "<nodate@example.invalid>"))
(defconst *pt-mismatch*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!not-for-mail" "From: poster@example.invalid"
               "Newsgroups: fn.letters" "Subject: other" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
               "Message-ID: <other@example.invalid>" "" "Offered as a1."))))

(defconst *pt-node0* (fn-node-initial-state '("fn.letters" "fn.test") 1048576))
(assert-event (fn-node-statep *pt-node0*))
(defconst *pt-archive* (fn-node-acceptance *pt-node0*))
(defconst *pt-inj* (fn-inj-make-config t (pt-o "fn.example.invalid") (list (pt-o "fn.letters")) 32768))
(defconst *pt-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *pt-ps0* (fn-peer-open-session *pt-archive* "innA" *pt-node0* *pt-cfg*))
(assert-event (fn-peer-sessionp *pt-ps0*))
(assert-event (fn-peer-session-consistentp *pt-ps0* *pt-archive*))
(assert-event (equal (fn-peer-session-peer *pt-ps0*) "innA"))
(defconst *pt-reader* (fn-peer-open-session *pt-archive* nil nil nil))
(assert-event (fn-peer-sessionp *pt-reader*))
(assert-event (null (fn-peer-session-peer *pt-reader*)))
; A peer session pins the node under its recognizer, once: a non-state opens
; as a reader.
(assert-event (null (fn-peer-session-peer (fn-peer-open-session *pt-archive* "innA" '(not a node) *pt-cfg*))))

(defun pt-cmd (s) (list :command (pt-o s)))
(defun pt-reply (s) (fn-nntp-reply-effect (fn-nntp-crlf (pt-o s))))
(defun pt-echo (code msgid) (fn-nntp-reply-effect (fn-nntp-crlf (append (pt-o code) msgid))))

; -----------------------------------------------------------------------------
; Transcript: IHAVE accepted (RFC 3977 section 6.3.2.3, first example)

(defconst *pt-r1* (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <a1@example.invalid>")))
(assert-event (equal (fn-post-result-effects *pt-r1*)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>") (fn-nntp-begin-article-effect))))
(assert-event (fn-nntp-effectsp (fn-post-result-effects *pt-r1*)))
(assert-event (equal (fn-peer-session-transfer (fn-post-result-session *pt-r1*)) (list :ihave *pt-id1*)))
(assert-event (null (fn-post-result-submission *pt-r1*)))
(defconst *pt-r2* (fn-peer-step (fn-post-result-session *pt-r1*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (list :article *pt-a1-lines*)))
(assert-event (null (fn-post-result-effects *pt-r2*)))
(assert-event (equal (fn-post-result-submission *pt-r2*) (fn-peer-make-submission "innA" :ihave *pt-id1* *pt-a1*)))
(assert-event (fn-peer-submissionp (fn-post-result-submission *pt-r2*)))
(assert-event (not (fn-inj-injectedp (fn-post-result-submission *pt-r2*))))
(assert-event (null (fn-peer-session-transfer (fn-post-result-session *pt-r2*))))
(assert-event (fn-peer-session-consistentp (fn-post-result-session *pt-r2*) *pt-archive*))
; The owner's transit port: the transfer is one fn-node-prepare on the
; arguments computed from the octets.  Two Newsgroups, one membership
; (non-degenerate: alt.test is not carried here).
(defconst *pt-t1* (mv-list 2 (fn-peer-transfer *pt-node0* *pt-cfg* "innA" *pt-id1* *pt-a1* nil 1 "ob-a1" "subject-a1")))
(assert-event (equal (nth 1 *pt-t1*) (fn-peer-decision :want nil)))
(assert-event (not (equal (nth 0 *pt-t1*) *pt-node0*)))
(assert-event (fn-node-statep (nth 0 *pt-t1*)))
(assert-event (equal (nth 3 (fn-peer-injection-arguments *pt-node0* *pt-cfg* "innA" *pt-id1* *pt-a1* 1 "ob-a1" "subject-a1")) '("fn.letters")))
(assert-event (equal (fn-pending-groups (fn-state-pending (fn-node-acceptance (nth 0 *pt-t1*)))) '("fn.letters")))
(assert-event (equal (fn-node-stage-msgid (fn-node-stage (nth 0 *pt-t1*))) "<a1@example.invalid>"))
(assert-event (equal (fn-node-stage-evidence (fn-node-stage (nth 0 *pt-t1*))) "peer-transit:innA"))
(assert-event (equal (nth 0 *pt-t1*)
                     (fn-node-prepare *pt-node0* 1 "<a1@example.invalid>" *pt-a1-stored* '("fn.letters")
                                      "ob-a1" "subject-a1" "peer-transit:innA" (fn-charge-for-payload (len *pt-a1-stored*)) 841000000)))
; Nothing is published by the prepare: the archive is unchanged until the
; store's :durable completion.
(assert-event (equal (fn-state-articles (fn-node-acceptance (nth 0 *pt-t1*))) nil))
(defconst *pt-node1* (fn-node-complete (nth 0 *pt-t1*) 0 1 :durable))
(assert-event (fn-node-statep *pt-node1*))
(assert-event (fn-peer-history-hasp "<a1@example.invalid>" *pt-node1*))
(assert-event (equal (fn-article-payload (car (fn-state-articles (fn-node-acceptance *pt-node1*)))) *pt-a1-stored*))
; 235 only on the durable completion.
(assert-event (equal (fn-post-result-effects (fn-peer-transit-outcome (fn-post-result-session *pt-r2*) (fn-post-result-submission *pt-r2*) (nth 1 *pt-t1*) :durable))
                     (list (pt-reply "235 article transferred OK"))))

; -----------------------------------------------------------------------------
; Transcript: the loop is refused at transfer (K2), and the two acceptances

(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-loop* nil "ob" "s") (fn-peer-decision :refuse :loop)))
(assert-event (equal (nth 0 (mv-list 2 (fn-peer-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-loop* nil 1 "ob" "s"))) *pt-node0*))
; Separating witness: the same article with a Path that does not name us.
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-noloop* nil "ob" "s") (fn-peer-decision :want nil)))
; Tail-entry and POSTED variants are accepted: the test is not substring search.
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-tail* nil "ob" "s") (fn-peer-decision :want nil)))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-posted* nil "ob" "s") (fn-peer-decision :want nil)))
; Unparsable octets are :proto-article, not :loop: the reasons separate.
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* (pt-o "garbage") nil "ob" "s") (fn-peer-decision :refuse :proto-article)))
; The IHAVE transcript of a loop: 335, the article, 437 with the reason.
(defconst *pt-l1* (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <loop@example.invalid>")))
(defconst *pt-l2* (fn-peer-step (fn-post-result-session *pt-l1*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (list :article *pt-loop-lines*)))
(defconst *pt-lt* (mv-list 2 (fn-peer-transfer *pt-node0* *pt-cfg* "innA" *pt-idloop* *pt-loop* nil 1 "ob" "s")))
(assert-event (equal (fn-post-result-effects (fn-peer-transit-outcome (fn-post-result-session *pt-l2*) (fn-post-result-submission *pt-l2*) (nth 1 *pt-lt*) nil))
                     (list (pt-reply "437 transfer rejected; path loop"))))

; -----------------------------------------------------------------------------
; Transcript: the duplicate is refused at offer and at transfer (K3)

(defconst *pt-ps1* (fn-peer-open-session (fn-node-acceptance *pt-node1*) "innA" *pt-node1* *pt-cfg*))
(assert-event (equal (fn-peer-decide-offer *pt-node1* *pt-cfg* "innA" *pt-ps1* *pt-id1* nil 0) (fn-peer-decision :have :history)))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps1* (fn-node-acceptance *pt-node1*) *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "435 duplicate"))))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps1* (fn-node-acceptance *pt-node1*) *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CHECK <a1@example.invalid>")))
                     (list (pt-echo "438 " *pt-id1*))))
(assert-event (equal (fn-peer-decide-transfer *pt-node1* *pt-cfg* "innA" *pt-id1* *pt-a1* nil "ob-a1" "subject-a1") (fn-peer-decision :have :history)))
(assert-event (equal (nth 0 (mv-list 2 (fn-peer-transfer *pt-node1* *pt-cfg* "innA" *pt-id1* *pt-a1* nil 2 "ob-a1" "subject-a1"))) *pt-node1*))
; The separating witness: a fresh Message-ID on the same node is wanted.
(assert-event (equal (fn-peer-decide-offer *pt-node1* *pt-cfg* "innA" *pt-ps1* *pt-idloop* nil 0) (fn-peer-decision :want nil)))
; A binding is a tombstone: released of its pin, the article is still :have.
(assert-event (consp (fn-node-find-binding "<a1@example.invalid>" (fn-node-bindings *pt-node1*))))

; -----------------------------------------------------------------------------
; The defect w11/transit-correct closes: ONE connection, before and after the
; article it delivered became durable (fn-peer-with-node, applied per socket
; read by books/owner.lisp fn-own-conn-live-session).
;
; *pt-ps0* is the session exactly as fn-peer-open-session pinned it, over
; *pt-node0*, which holds nothing.  The first offer on it is 335 and that is
; right.  The second offer -- after the SAME connection transferred the
; article and the store made it durable -- was 335 again, because nothing
; ever replaced the node in the session.  Observed on the wire:
; V0-TRANSIT-DUPLICATE-AB/BA 335 and V0-TRANSIT-CHECK-DUP-AB/BA 238 at
; 6fb30ca (planning/evidence/v0-matrix-2026-09-21.md).

(defconst *pt-ps0-stale*
  (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                (pt-cmd "IHAVE <a1@example.invalid>")))
(assert-event (equal (fn-post-result-effects *pt-ps0-stale*)
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))

(defconst *pt-ps0-live* (fn-peer-with-node *pt-ps0* *pt-node1*))
(assert-event (fn-peer-sessionp *pt-ps0-live*))
(assert-event (fn-peer-session-consistentp *pt-ps0-live* *pt-archive*))
; Everything but the node is the session it was.
(assert-event (equal (fn-peer-session-peer *pt-ps0-live*) "innA"))
(assert-event (equal (fn-peer-session-cfg *pt-ps0-live*) (fn-peer-session-cfg *pt-ps0*)))
(assert-event (equal (fn-peer-session-base *pt-ps0-live*) (fn-peer-session-base *pt-ps0*)))
(assert-event (equal (fn-peer-session-transfer *pt-ps0-live*) (fn-peer-session-transfer *pt-ps0*)))
(assert-event (equal (fn-peer-session-inflight *pt-ps0-live*) (fn-peer-session-inflight *pt-ps0*)))
(assert-event (equal (fn-peer-session-node *pt-ps0-live*) *pt-node1*))

; The reply, and no article mode: the peer pays no bytes for what we hold.
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "435 duplicate"))))
(assert-event (null (fn-peer-session-transfer
                     (fn-post-result-session
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <a1@example.invalid>"))))))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "CHECK <a1@example.invalid>")))
                     (list (pt-echo "438 " *pt-id1*))))

; Teeth for fn-peer-ihave-of-a-held-message-id-is-435-and-no-article and
; fn-peer-check-of-a-held-message-id-is-438-and-no-offer-outstanding: one
; concrete violating value per hypothesis, each answering something the
; theorem's conclusion is not.
;
; (a) the history hypothesis: a Message-ID the live node does not hold.
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <loop@example.invalid>")))
                     (list (pt-reply "335 send it; end with <CR-LF>.<CR-LF>")
                           (fn-nntp-begin-article-effect))))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "CHECK <loop@example.invalid>")))
                     (list (pt-echo "238 " *pt-idloop*))))
; (b) the peer hypothesis: a reader connection carries no node and gets the
; reader's answer to a transit keyword, not a duplicate refusal.
(assert-event (null (fn-peer-session-peer (fn-peer-with-node *pt-reader* *pt-node1*))))
; The must-fail for `fn-peer-sessionp-of-fn-peer-with-node's configuration
; hypothesis: this object is what `fn-peer-with-node' makes of a reader that
; carries no configuration, and it is not a session.  It is stepped above only
; to read the reader's 502; the machine never stores it, because
; `fn-own-conn-live-session' refreshes a session's node only when the session
; has a configuration.  `*pt-ps0-live*' above is the witness with it.
(assert-event (not (fn-peer-sessionp (fn-peer-with-node *pt-reader* *pt-node1*))))
; And what the step does with that object is nothing at all.
; `fn-peer-step's first branch is `(not (fn-peer-sessionp ps))' and it returns
; the object it was given with no effects and no submission, so a reader
; refreshed without a configuration is not served rather than served a 502.
; This assertion said 502 until 2026-09-22 and had never run: this book last
; certified before `64a80197' (2026-09-21 13:02) made a null peer beside a
; checked node and a null configuration fail `fn-peer-sessionp'.  The 502 is
; the answer a REAL reader session gets and it is asserted of `*pt-reader*'
; further down, where it belongs.
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step (fn-peer-with-node *pt-reader* *pt-node1*)
                                    (fn-node-acceptance *pt-node1*) *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <a1@example.invalid>")))
                     nil))
(assert-event (null (fn-post-result-submission
                     (fn-peer-step (fn-peer-with-node *pt-reader* *pt-node1*)
                                   (fn-node-acceptance *pt-node1*) *pt-inj* *pt-obs* *pt-obs*
                                   (pt-cmd "IHAVE <a1@example.invalid>")))))
; (c) the peer-record hypothesis: a connection whose name is in no peer
; table answers :not-a-peer, which is a 435 with a different text and a 438
; with the same code for a different reason.
(defconst *pt-ghost* (fn-peer-with-node
                      (fn-peer-open-session *pt-archive* "ghost" *pt-node1* *pt-cfg*)
                      *pt-node1*))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ghost* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "435 not wanted; not a peer"))))
; (d) the inbound-half hypothesis: a feed-only peer record.
(defconst *pt-feedonly*
  (fn-cfg-peer-make "outC" "outc.example" '(:nntp "127.0.0.1" 1120)
                    nil '("fn.*" t 256 1000) '(:source-address "127.0.0.1")))
(assert-event (fn-cfg-peerp *pt-feedonly*))
(defconst *pt-cfg-feedonly*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "fnA.hbox.test")
                                         (fn-cfg-set-peer-delta *pt-feedonly*)))
                           *fn-cfg-default-stamp*))))
(assert-event (fn-cfgp *pt-cfg-feedonly*))
(defconst *pt-ps-feedonly*
  (fn-peer-with-node
   (fn-peer-open-session *pt-archive* "outC" *pt-node1* *pt-cfg-feedonly*)
   *pt-node1*))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps-feedonly* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "435 not wanted; no inbound feed configured"))))
; (e) the Message-ID hypothesis: a token that is not one is a syntax error,
; never a duplicate refusal.
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "IHAVE not-a-message-id")))
                     (list (pt-reply "501 syntax error"))))
(assert-event (equal (fn-post-result-effects
                      (fn-peer-step *pt-ps0-live* *pt-archive* *pt-inj* *pt-obs* *pt-obs*
                                    (pt-cmd "CHECK not-a-message-id")))
                     (list (pt-reply "501 syntax error"))))

; -----------------------------------------------------------------------------
; Transcript: CHECK/TAKETHIS refused by groups (RFC 4644 section 2.4.3 shape)

(defconst *pt-c1* (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CHECK <alt@example.invalid>")))
(assert-event (equal (fn-post-result-effects *pt-c1*) (list (pt-echo "238 " *pt-idalt*))))
(assert-event (equal (fn-peer-session-inflight (fn-post-result-session *pt-c1*)) 1))
(defconst *pt-c2* (fn-peer-step (fn-post-result-session *pt-c1*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "TAKETHIS <alt@example.invalid>")))
(assert-event (equal (fn-post-result-effects *pt-c2*) (list (fn-nntp-begin-article-effect))))
(assert-event (equal (fn-peer-session-transfer (fn-post-result-session *pt-c2*)) (list :takethis *pt-idalt*)))
(assert-event (equal (fn-peer-session-inflight (fn-post-result-session *pt-c2*)) 0))
(defconst *pt-c3* (fn-peer-step (fn-post-result-session *pt-c2*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (list :article *pt-alt-lines*)))
(assert-event (equal (fn-post-result-submission *pt-c3*) (fn-peer-make-submission "innA" :takethis *pt-idalt* *pt-alt*)))
(defconst *pt-ct* (mv-list 2 (fn-peer-transfer *pt-node0* *pt-cfg* "innA" *pt-idalt* *pt-alt* nil 1 "ob" "s")))
(assert-event (equal (nth 1 *pt-ct*) (fn-peer-decision :refuse :out-of-scope)))
(assert-event (equal (nth 0 *pt-ct*) *pt-node0*))
(assert-event (equal (fn-post-result-effects (fn-peer-transit-outcome (fn-post-result-session *pt-c3*) (fn-post-result-submission *pt-c3*) (nth 1 *pt-ct*) nil))
                     (list (pt-echo "439 " *pt-idalt*))))
; The narrowed peer record flips the two-group article to :out-of-scope
; while the node is untouched (peering.md section 1.2.1).
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg3* "innA" *pt-id1* *pt-a1* nil "ob" "s") (fn-peer-decision :refuse :out-of-scope)))

; -----------------------------------------------------------------------------
; Uncertain and deferred after the bytes: 400 and close (TAKETHIS), 436 and
; close (IHAVE); three outcomes distinct out to the wire.

(defconst *pt-sub-t* (fn-peer-make-submission "innA" :takethis *pt-id1* *pt-a1*))
(defconst *pt-sub-i* (fn-peer-make-submission "innA" :ihave *pt-id1* *pt-a1*))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :want nil) :uncertain)
                     (list (pt-echo "436 " *pt-id1*) (fn-nntp-close-effect))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :want nil) :durable)
                     (list (pt-echo "239 " *pt-id1*))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :want nil) :refused)
                     (list (pt-echo "439 " *pt-id1*))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :defer :busy) nil)
                     (list (pt-echo "436 " *pt-id1*))))
; The code classes innfeed acts on (retry: 431/436; drop: 437/439), on every
; decision kind and completion, for both commands.
(assert-event (equal (fn-peer-transit-code :takethis (fn-peer-decision :defer :busy) nil) 436))
(assert-event (equal (fn-peer-transit-code :ihave (fn-peer-decision :defer :capacity) nil) 436))
(assert-event (equal (fn-peer-transit-code :takethis (fn-peer-decision :want nil) :uncertain) 436))
(assert-event (equal (fn-peer-transit-code :takethis (fn-peer-decision :refuse :loop) nil) 439))
(assert-event (equal (fn-peer-transit-code :ihave (fn-peer-decision :have :history) nil) 437))
(assert-event (equal (fn-peer-transit-code :takethis (fn-peer-decision :want nil) :refused) 439))
(assert-event (equal (fn-peer-transit-code :ihave (fn-peer-decision :want nil) :durable) 235))
(assert-event (equal (fn-peer-offer-code :ihave (fn-peer-decision :defer :capacity)) 436))
(assert-event (equal (fn-peer-offer-code :check (fn-peer-decision :defer :inflight-limit)) 431))
(assert-event (equal (fn-peer-offer-code :check (fn-peer-decision :have :history)) 438))
(assert-event (equal (fn-peer-offer-code :ihave (fn-peer-decision :refuse :not-a-peer)) 435))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-i* (fn-peer-decision :want nil) :uncertain)
                     (list (pt-reply "436 transfer failed; the outcome is uncertain") (fn-nntp-close-effect))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-i* (fn-peer-decision :defer :fenced) nil)
                     (list (pt-reply "436 retry later; recovery pending"))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-i* (fn-peer-decision :want nil) :refused)
                     (list (pt-reply "437 transfer rejected; refused by acceptance"))))
(assert-event (equal (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-i* (fn-peer-decision :have :history) nil)
                     (list (pt-reply "437 transfer rejected; duplicate"))))
; The remaining offer cells: 436 (defer at offer: the inflight limit) and
; 431, 435 not wanted / 438 for a refusal (not a peer).
(defconst *pt-ps-full* (fn-peer-make-session (fn-peer-session-base *pt-ps0*) "innA" nil 16 *pt-node0* *pt-cfg*))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps-full* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "436 retry later; too many offers outstanding"))))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps-full* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CHECK <a1@example.invalid>")))
                     (list (pt-echo "431 " *pt-id1*))))
(defconst *pt-ps-ghost* (fn-peer-open-session *pt-archive* "ghost" *pt-node0* *pt-cfg*))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps-ghost* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "435 not wanted; not a peer"))))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps-ghost* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CHECK <a1@example.invalid>")))
                     (list (pt-echo "438 " *pt-id1*))))
; A feed-only peer cannot inject.
(defconst *pt-ps-dtn* (fn-peer-open-session *pt-archive* "dtnB" *pt-node0* *pt-cfg*))
(assert-event (equal (fn-post-result-effects (fn-peer-step (fn-peer-make-session (fn-peer-session-base *pt-ps-dtn*) "dtnB" nil 0 *pt-node0* *pt-cfg3*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CHECK <a1@example.invalid>")))
                     (list (pt-echo "238 " *pt-id1*))))
; Transfer refusals by article: no date, and an offered id that is not the article's.
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-idnodate* *pt-nodate* nil "ob" "s") (fn-peer-decision :refuse :no-date)))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-id1* *pt-mismatch* nil "ob" "s") (fn-peer-decision :refuse :message-id-syntax)))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" (pt-o "a1@example.invalid") *pt-a1* nil "ob" "s") (fn-peer-decision :refuse :message-id-syntax)))

; -----------------------------------------------------------------------------
; MODE STREAM, CAPABILITIES, the reader connection, the not-received article

(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "MODE STREAM")))
                     (list (pt-reply "203 streaming permitted"))))
; The second argument is the pinned configuration's posting bit, which
; fn-nntp-capability-lines gates the POST label on.  fn-peer-command passes
; nil on a transit connection: it reads only the session and carries no
; injection configuration, so it does not promise POST.  Witnessed both
; ways, so the label follows the bit and not the peer record.
(assert-event (member-equal (pt-o "IHAVE") (fn-peer-capability-lines *pt-peer* nil)))
(assert-event (member-equal (pt-o "STREAMING") (fn-peer-capability-lines *pt-peer* nil)))
(assert-event (not (member-equal (pt-o "IHAVE") (fn-peer-capability-lines nil nil))))
(assert-event (not (member-equal (pt-o "POST") (fn-peer-capability-lines *pt-peer* nil))))
(assert-event (member-equal (pt-o "POST") (fn-peer-capability-lines *pt-peer* t)))
(assert-event (fn-nntp-effectsp (fn-post-result-effects (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "CAPABILITIES")))))
; A reader connection: the dispatcher's 502, and MODE STREAM is 501 as before.
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-reader* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE <a1@example.invalid>")))
                     (list (pt-reply "502 transit is not permitted on this connection"))))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-reader* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "MODE STREAM")))
                     (list (pt-reply "501 syntax error"))))
; A reader's POST still goes through the POST-composed step.
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-reader* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "POST")))
                     (list (pt-reply "340 send article to be posted") (fn-nntp-begin-article-effect))))
; Malformed transit lines: 501, no article mode.
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "TAKETHIS")))
                     (list (pt-reply "501 syntax error"))))
(assert-event (equal (fn-post-result-effects (fn-peer-step *pt-ps0* *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "IHAVE a1")))
                     (list (pt-reply "501 syntax error"))))
; Awaiting the article and something else arrives: retry code and close.
(assert-event (equal (fn-post-result-effects (fn-peer-step (fn-post-result-session *pt-r1*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "QUIT")))
                     (list (pt-reply "436 transfer failed; the article was not received") (fn-nntp-close-effect))))
(assert-event (equal (fn-post-result-effects (fn-peer-step (fn-post-result-session *pt-c2*) *pt-archive* *pt-inj* *pt-obs* *pt-obs* (pt-cmd "QUIT")))
                     (list (pt-reply "436 the article was not received; closing") (fn-nntp-close-effect))))
; Every transit reply above is a typed effect list.
(assert-event (fn-nntp-effectsp (fn-post-result-effects *pt-c1*)))
(assert-event (fn-nntp-effectsp (fn-post-result-effects *pt-c2*)))
(assert-event (fn-nntp-effectsp (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :want nil) :durable)))
(assert-event (fn-nntp-effectsp (fn-peer-transit-outcome-effects *pt-ps0* *pt-sub-t* (fn-peer-decision :want nil) :uncertain)))

; -----------------------------------------------------------------------------
; What a relaying and serving agent changes: Path and Xref (RFC 5537 3.6,
; 3.7; books/path-update.lisp, the keystones
;   fn-peer-relayed-octets-change-only-path-and-xref
;   fn-peer-relayed-octets-are-idempotent
;   fn-peer-relayed-octets-carry-no-xref
;   fn-peer-relayed-octets-name-this-node-in-every-path
; in books/peer-inbound-invariants.lisp).  The subject is
; fn-peer-relayed-octets, which host/owner-host.lisp fn-owner-take calls to
; fill the octets the native drain stores.
;
; THE WITNESS IS INN'S OWN ARTICLE: planning/evidence/inn-lab-dabebb84-
; 2026-09-22.md, "innfeed -> fn", the octets innfeed sent in TAKETHIS, which
; fn stored and served unchanged -- INN's Path without fnA.hbox.test and INN's
; Xref -- until this change (the lab's findings 2 and 3).  The peer record
; innA expects inn.hbox.test, the leftmost entry, so the diagnostic is "!".
; The expected octets are written out here, not computed by the function.

(defconst *pt-inn-fed*
  (fn-post-body-octets
   (pt-lines '("Path: inn.hbox.test!lab.example.invalid!not-for-mail"
               "From: lab@example.invalid"
               "Newsgroups: fn.letters"
               "Subject: handed to INN, fed on to fn"
               "Date: Tue, 22 Sep 2026 21:26:21 -0000"
               "Message-ID: <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>"
               "Xref: inn.hbox.test fn.letters:15"
               "" "From the fn INN interop lab."))))
(defconst *pt-inn-stored*
  (fn-post-body-octets
   (pt-lines '("Path: fnA.hbox.test!!inn.hbox.test!lab.example.invalid!not-for-mail"
               "From: lab@example.invalid"
               "Newsgroups: fn.letters"
               "Subject: handed to INN, fed on to fn"
               "Date: Tue, 22 Sep 2026 21:26:21 -0000"
               "Message-ID: <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>"
               "" "From the fn INN interop lab."))))
(defconst *pt-inn-id*
  (pt-o "<inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>"))

; The octets the transfer stages and the host stores.
(assert-event (equal (fn-peer-relayed-octets *pt-cfg* "innA" *pt-inn-fed*)
                     *pt-inn-stored*))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA" *pt-inn-id*
                                              *pt-inn-fed* nil "ob-inn" "subject-inn")
                     (fn-peer-decision :want nil)))
(assert-event (equal (nth 2 (fn-peer-injection-arguments *pt-node0* *pt-cfg* "innA"
                                                         *pt-inn-id* *pt-inn-fed*
                                                         1 "ob-inn" "subject-inn"))
                     *pt-inn-stored*))
(assert-event (equal (nth 7 (fn-peer-injection-arguments *pt-node0* *pt-cfg* "innA"
                                                         *pt-inn-id* *pt-inn-fed*
                                                         1 "ob-inn" "subject-inn"))
                     (fn-charge-for-payload (len *pt-inn-stored*))))
; Through the transfer to the durable article a reader is served.
(defconst *pt-inn-node*
  (fn-node-complete
   (nth 0 (mv-list 2 (fn-peer-transfer *pt-node0* *pt-cfg* "innA" *pt-inn-id*
                                       *pt-inn-fed* nil 1 "ob-inn" "subject-inn")))
   0 1 :durable))
(assert-event (equal (fn-article-payload
                      (car (fn-state-articles (fn-node-acceptance *pt-inn-node*))))
                     *pt-inn-stored*))
; The stored article parses and names fnA.hbox.test in its Path, and has no
; Xref, as the reader's parser sees it.
(assert-event
 (let ((a (fn-article-result-article (fn-article-parse *pt-inn-stored*))))
   (and (equal (fn-af-path-field-value a)
               (pt-o "fnA.hbox.test!!inn.hbox.test!lab.example.invalid!not-for-mail"))
        (null (fn-article-get-headers a *fn-af-xref-name*)))))
; A peer whose record expects another identity: the diagnostic is .MISMATCH.
(defconst *pt-inn-other-peer*
  (fn-cfg-peer-make "innA" "other.hbox.test" '(:nntp "127.0.0.1" 1119)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.1")))
(defconst *pt-cfg-other-peer*
  (fn-config-replay 0 510
                    (list *pt-record*
                          (fn-cfg-record-make 1 1 2
                                              (list (fn-cfg-set-peer-delta
                                                     *pt-inn-other-peer*))
                                              *fn-cfg-default-stamp*))))
(assert-event
 (equal (fn-peer-relayed-octets *pt-cfg-other-peer* "innA" *pt-inn-fed*)
        (fn-post-body-octets
         (pt-lines '("Path: fnA.hbox.test!.MISMATCH.other.hbox.test!inn.hbox.test!lab.example.invalid!not-for-mail"
                     "From: lab@example.invalid"
                     "Newsgroups: fn.letters"
                     "Subject: handed to INN, fed on to fn"
                     "Date: Tue, 22 Sep 2026 21:26:21 -0000"
                     "Message-ID: <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>"
                     "" "From the fn INN interop lab.")))))

; Keystone: nothing but Path and Xref changes.  Witness, non-degenerate: the
; stored octets differ from what arrived, and agree once Path and Xref are
; removed from both.
(assert-event (not (equal *pt-inn-stored* *pt-inn-fed*)))
(assert-event (equal (fn-pu-strip *pt-inn-stored* nil) (fn-pu-strip *pt-inn-fed* nil)))
(assert-event (equal (fn-pu-strip *pt-inn-fed* nil)
                     (fn-post-body-octets
                      (pt-lines '("From: lab@example.invalid"
                                  "Newsgroups: fn.letters"
                                  "Subject: handed to INN, fed on to fn"
                                  "Date: Tue, 22 Sep 2026 21:26:21 -0000"
                                  "Message-ID: <inn-lab-fed-8a5f502-20260922T212621Z@example.invalid>"
                                  "" "From the fn INN interop lab.")))))
; The statement has no hypothesis.  Tooth: the stronger claim that the relay
; changes nothing is false, and INN's article is the value that says so.
(must-fail
 (defthm pt-relay-changes-nothing
   (equal (fn-peer-relayed-octets cfg peer octets) octets)
   :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                   (fn-pu-relay-article))))))

; Keystone: a second pass changes nothing.
(assert-event (equal (fn-peer-relayed-octets *pt-cfg* "innA" *pt-inn-stored*)
                     *pt-inn-stored*))
; No hypothesis.  Tooth: a pass by ANOTHER node (another identity) does
; change the article -- idempotence is this node's, not a relay's.
(defconst *pt-cfg-fnb*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-policy "path-identity" "fnB.hbox.test")
                                         (fn-cfg-set-peer-delta *pt-peer*)))
                           *fn-cfg-default-stamp*))))
(must-fail
 (defthm pt-relay-by-another-node-changes-nothing
   (equal (fn-peer-relayed-octets cfg2 peer (fn-peer-relayed-octets cfg peer octets))
          (fn-peer-relayed-octets cfg peer octets))
   :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                   (fn-pu-relay-article))))))
(assert-event (not (equal (fn-peer-relayed-octets *pt-cfg-fnb* "innA" *pt-inn-stored*)
                          *pt-inn-stored*)))

; Keystone: no Xref is stored.
(assert-event (fn-pu-xref-freep *pt-inn-stored*))
; No hypothesis.  Tooth: what arrived had one.
(must-fail
 (defthm pt-every-article-is-xref-free
   (fn-pu-xref-freep octets)))
(assert-event (not (fn-pu-xref-freep *pt-inn-fed*)))

; Keystone: every Path names this node, when it has an identity.
(assert-event (fn-pu-path-markedp *pt-inn-stored* (fn-peer-local-identity *pt-cfg*)))
(assert-event (not (fn-pu-path-markedp *pt-inn-fed* (fn-peer-local-identity *pt-cfg*))))
; Tooth for the one hypothesis: a node with no path identity updates no Path
; (the policy slot is unset), so what it stores names nothing.
(must-fail
 (defthm pt-relay-names-a-node-without-an-identity
   (fn-pu-path-markedp (fn-peer-relayed-octets cfg peer octets)
                       (fn-peer-local-identity cfg))
   :hints (("Goal" :in-theory (e/d (fn-peer-relayed-octets)
                                   (fn-pu-relay-article fn-pu-path-markedp
                                    fn-peer-expected-identity
                                    fn-peer-local-identity fn-path-identityp))))))
(defconst *pt-cfg-anon*
  (fn-config-replay 0 510
                    (list (fn-cfg-record-make
                           0 0 1
                           (append *fn-cfg-default-change*
                                   (list (fn-cfg-set-peer-delta *pt-peer*)))
                           *fn-cfg-default-stamp*))))
(assert-event (not (fn-path-identityp (fn-peer-local-identity *pt-cfg-anon*))))
(assert-event (not (fn-pu-path-markedp (fn-peer-relayed-octets *pt-cfg-anon* "innA" *pt-inn-fed*)
                                       (fn-peer-local-identity *pt-cfg-anon*))))
; ... and it still removes the sender's Xref.
(assert-event (fn-pu-xref-freep (fn-peer-relayed-octets *pt-cfg-anon* "innA" *pt-inn-fed*)))

; The update is refused rather than stored without it: an article whose Path
; line is already at the 998-octet line bound grows past it, and the transfer
; is refused :oversize (RFC 5537 3.6, last paragraph).
(defun pt-long-path (n)
  (if (zp n) nil (append (pt-o "a.b!") (pt-long-path (- n 1)))))
(defconst *pt-long*
  (fn-post-body-octets
   (list (append (pt-o "Path: inn.hbox.test!") (pt-long-path 244) (pt-o "x"))
         (pt-o "From: lab@example.invalid") (pt-o "Newsgroups: fn.letters")
         (pt-o "Subject: long") (pt-o "Date: Tue, 22 Sep 2026 21:26:21 -0000")
         (pt-o "Message-ID: <long@example.invalid>") nil (pt-o "x"))))
(assert-event (fn-article-result-okp (fn-article-parse *pt-long*)))
(assert-event (not (fn-article-result-okp
                    (fn-article-parse (fn-peer-relayed-octets *pt-cfg* "innA" *pt-long*)))))
(assert-event (equal (fn-peer-decide-transfer *pt-node0* *pt-cfg* "innA"
                                              (pt-o "<long@example.invalid>") *pt-long*
                                              nil "ob-long" "subject-long")
                     (fn-peer-decision :refuse :oversize)))
