; Witnesses and teeth for catching up from a peer (PRF-325, NNT-053;
; books/peer-catchup-serve.lisp, books/peer-catchup-effects.lisp,
; books/peer-catchup.lisp).
;
; The witness is one whole exchange as the two hosts drive it.  The serving
; view holds three articles, oldest first A1 and A2 in fn.test (A2 has a
; line that begins with ".", so the block's dot-stuffing is exercised) and
; A3 in fn.other; a fourth, W, is in the view but not in its Message-ID trie
; (a withdrawn article).  XFNCATCHUP fn.test from position 0 answers one
; batch with A1 and A2; the requesting round (the spool controller) spools
; and verifies its chain, opens the local transit connection, offers A1 (335,
; then its body, 235) and A2 (435), journals the cursor at the batch's end
; and closes.  A copy of the reply with one octet of A2's body changed is
; refused :digest-mismatch.
(in-package "ACL2")
(include-book "../../books/peer-catchup")
(include-book "../../books/peer-catchup-spool")
(include-book "../../books/peer-catchup-effects")
(include-book "must-fail-checked")
(include-book "arena-lift")

(defun cut-octets (s) (fn-record-string-octets s))
(defun cut-line (s) (append (fn-record-string-octets s) '(13 10)))

(defconst *cut-a1-bytes*
  (append (cut-line "From: one@example.invalid")
          (cut-line "Newsgroups: fn.test")
          (cut-line "Subject: first")
          (cut-line "Message-ID: <a1@example.invalid>")
          (cut-line "")
          (cut-line "first body")))
(defconst *cut-a2-bytes*
  (append (cut-line "From: two@example.invalid")
          (cut-line "Newsgroups: fn.test")
          (cut-line "Subject: second")
          (cut-line "Message-ID: <a2@example.invalid>")
          (cut-line "")
          (cut-line ".a line that begins with a dot")
          (cut-line "second body")))
(defconst *cut-a3-bytes*
  (append (cut-line "From: three@example.invalid")
          (cut-line "Newsgroups: fn.other")
          (cut-line "Subject: third")
          (cut-line "Message-ID: <a3@example.invalid>")
          (cut-line "")
          (cut-line "third body")))
(defconst *cut-w-bytes*
  (append (cut-line "From: w@example.invalid")
          (cut-line "Newsgroups: fn.test")
          (cut-line "Subject: withdrawn")
          (cut-line "Message-ID: <w@example.invalid>")
          (cut-line "")
          (cut-line "withdrawn body")))

;; The arena: handles 0..3 hold A1, A2, A3, W.
(defconst *sr-arena* (list *cut-a1-bytes* *cut-a2-bytes* *cut-a3-bytes* *cut-w-bytes*))

(defconst *cut-a1* (fn-make-article "<a1@example.invalid>" 0 '("fn.test")
                                    (list (cons "fn.test" 1)) t 841000000))
(defconst *cut-a2* (fn-make-article "<a2@example.invalid>" 1 '("fn.test")
                                    (list (cons "fn.test" 2)) t 841000001))
(defconst *cut-a3* (fn-make-article "<a3@example.invalid>" 2 '("fn.other")
                                    (list (cons "fn.other" 1)) t 841000002))
(defconst *cut-w* (fn-make-article "<w@example.invalid>" 3 '("fn.test")
                                   (list (cons "fn.test" 3)) t 841000003))
;; Newest first, as the view holds them.
(defconst *cut-articles* (list *cut-w* *cut-a3* *cut-a2* *cut-a1*))
(defconst *cut-state*
  (fn-make-state '("fn.test" "fn.other")
                 (list (cons "fn.test" 4) (cons "fn.other" 2))
                 *cut-articles* 4 nil nil))
;; W is not in the trie: a withdrawn article (books/nntp.lisp
;; `fn-nntp-msgid-withdrawn-p' answers it "430 withdrawn").
(defconst *cut-trie* (fn-midx-build (list *cut-a3* *cut-a2* *cut-a1*)))

(defconst *cut-wildmat* (cut-octets "fn.test"))
(defun cut-args (from chain quantum)
  (list *cut-wildmat* (fn-cu-u64-hex from) (fn-cu-hex chain)
        (fn-nntp-string-octets quantum)))

(bpr-lift fn-cu-serve-reply 4)
(defun cut-reply (from chain quantum)
  (cadr (car (cdr (in-arena-fn-cu-serve-reply *sr-arena* nil *cut-state* *cut-trie*
                                              (cut-args from chain quantum))))))

;; The digest chain over A1 then A2, computed here from the definition.
(defconst *cut-chain-1*
  (fn-cu-chain-step *fn-cu-zero-chain* (cut-octets "<a1@example.invalid>") *cut-a1-bytes*))
(defconst *cut-chain-2*
  (fn-cu-chain-step *cut-chain-1* (cut-octets "<a2@example.invalid>") *cut-a2-bytes*))

(defun cut-a2-stuffed ()
  (append (cut-line "From: two@example.invalid")
          (cut-line "Newsgroups: fn.test")
          (cut-line "Subject: second")
          (cut-line "Message-ID: <a2@example.invalid>")
          (cut-line "")
          (cut-line "..a line that begins with a dot")
          (cut-line "second body")))

; -----------------------------------------------------------------------------
; The serving half: the exact reply

(defconst *cut-reply* (cut-reply 0 *fn-cu-zero-chain* "1000"))
(assert-event
 (equal *cut-reply*
        (append (cut-line (concatenate 'string
                                       "291 0000000000000004 0000000000000004 done "
                                       (coerce (fn-nntp-octets-chars (fn-cu-hex *cut-chain-2*))
                                               'string)))
                (cut-line "R <a1@example.invalid> 0000000000000006")
                *cut-a1-bytes*
                (cut-line "R <a2@example.invalid> 0000000000000007")
                (cut-a2-stuffed)
                (cut-line "."))))

; A quantum smaller than A1 still serves A1 (whole, alone) and moves on.
(assert-event
 (equal (take 55 (cut-reply 0 *fn-cu-zero-chain* "1"))
        (take 55 (cut-line (concatenate 'string
                                        "291 0000000000000001 0000000000000004 more "
                                        (coerce (fn-nntp-octets-chars
                                                 (fn-cu-hex *cut-chain-1*))
                                                'string))))))

; Past the end: refused by name.
(assert-event
 (equal (cut-reply 5 *fn-cu-zero-chain* "1000")
        (cut-line "423 catch-up position past the end of the log")))
; A malformed chain is a syntax error.
(assert-event
 (equal (cadr (car (cdr (in-arena-fn-cu-serve-reply
                         *sr-arena* nil *cut-state* *cut-trie*
                         (list *cut-wildmat* (fn-cu-u64-hex 0) (cut-octets "00")
                               (cut-octets "1000"))))))
        (cut-line "501 syntax error")))

; KEYSTONE fn-cu-select-serves-only-retrievable.  The reachable witness: A1
; and A2 are served; A3 (outside the wildmat) and W (not in the trie) are
; entries of the view the batch passes over, and neither is servedp -- the
; conclusion's servedp half is not vacuous.
(defun cut-select (articles from groups trie quantum fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (next served) (fn-cu-select articles from groups trie quantum fn-arena)
    (list next served)))
(bpr-lift cut-select 5)
(bpr-lift fn-cu-servedp 3)
(defconst *cut-groups* '("fn.test"))
(defconst *cut-selected*
  (in-arena-cut-select *sr-arena* *cut-articles* 0 *cut-groups* *cut-trie* 1000))
(assert-event (equal *cut-selected* (list 4 (list *cut-a1* *cut-a2*))))
(assert-event (in-arena-fn-cu-servedp *sr-arena* *cut-a1* *cut-groups* *cut-trie*))
(assert-event (member-equal *cut-a3* *cut-articles*))
(assert-event (member-equal *cut-w* *cut-articles*))
(must-fail-checked
 (assert-event (in-arena-fn-cu-servedp *sr-arena* *cut-a3* *cut-groups* *cut-trie*)))
(must-fail-checked
 (assert-event (in-arena-fn-cu-servedp *sr-arena* *cut-w* *cut-groups* *cut-trie*)))

; KEYSTONE fn-cu-select-makes-progress.  Witness: from 0 below the end 4, NEXT
; is 4.  Tooth (FROM below the end): at the end, NEXT does not move past FROM.
(assert-event (< 0 (car *cut-selected*)))
(must-fail-checked
 (assert-event (< 4 (car (in-arena-cut-select *sr-arena* *cut-articles* 4
                                              *cut-groups* *cut-trie* 1000)))))

; KEYSTONE fn-cu-select-stays-within-the-quantum.  Witness: quantum 1 serves
; A1 alone (larger than the quantum, never cut).  Tooth (natp quantum): with
; no entries and quantum -1 the batch is empty and 0 octets exceed -1.
(bpr-lift fn-cu-octets-of 1)
(defconst *cut-selected-q1*
  (in-arena-cut-select *sr-arena* *cut-articles* 0 *cut-groups* *cut-trie* 1))
(assert-event (equal *cut-selected-q1* (list 1 (list *cut-a1*))))
(assert-event (< 1 (in-arena-fn-cu-octets-of *sr-arena* (cadr *cut-selected-q1*))))
(must-fail-checked
 (assert-event
  (let ((served (cadr (in-arena-cut-select *sr-arena* nil 0 *cut-groups* *cut-trie* -1))))
    (or (<= (in-arena-fn-cu-octets-of *sr-arena* served) -1)
        (equal (len served) 1)))))

; KEYSTONE fn-cu-serve-reply-effects-well-formed: the reply is one
; well-formed response.
(assert-event (fn-nntp-effectsp (list (list :reply *cut-reply*))))

; -----------------------------------------------------------------------------
; The requesting half: one round, through the spool controller
;
; The round is books/peer-catchup-spool.lisp's `fn-csp-step', driven here as
; the host drives it: the peer's reply in 512-octet windows (or smaller), a
; materialized spool, and scripted local answers.  The driver is test-only;
; the controller itself retains no record, line list or article.

(defconst *cut-peer* (cut-octets "A"))
(defconst *cut-r0* (fn-cu-begin (fn-cu-fresh-cursor *cut-peer*) *cut-wildmat*))

; The request the session sends when its preamble is ready.
(assert-event
 (equal (fn-cu-request *cut-r0*)
        (cut-line (concatenate 'string "XFNCATCHUP fn.test 0000000000000000 "
                               (coerce (fn-nntp-octets-chars (fn-cu-hex *fn-cu-zero-chain*))
                                       'string)
                               " 262144"))))

(defun cut-csp-state (cursor limit)
  ; A ready session at CURSOR, the request already sent.
  (let ((session (fn-cu-session (fn-fc-make-state (fn-fwi-initial-state) nil :ready 0 :clear)
                                (fn-cu-begin cursor *cut-wildmat*) nil :clear)))
    (list :status session nil nil nil 0 0 nil (fn-cu-cursor-chain cursor)
          nil nil 0 limit 0 nil nil nil)))

(defun cut-drive (s effects wire chunk disk replies local journals fuel)
  ; (word state local-octets journals). REPLIES answers each local offer,
  ; terminator and greeting in turn; a body window is taken without reply.
  (declare (xargs :mode :program))
  (cond
   ((zp fuel) (list :exhausted s local journals))
   ((consp effects)
    (let* ((effect (car effects)) (kind (car effect))
           (disk (if (eq kind :spool-write)
                     (append (take (cadr effect) disk) (caddr effect)) disk))
           (local (if (eq kind :local) (append local (cdr effect)) local))
           (journals (if (eq kind :journal) (append journals (list (cdr effect))) journals))
           (answer (and (member-eq kind '(:open-local :local))
                        (not (eq (fn-csp-mode s) :local-write))))
           (event
            (case kind
              (:spool-write (list :spool-written :ok (len (caddr effect))))
              (:spool-hash (list :digest (fn-blake3-stobj
                                          (take (caddr effect) (nthcdr (cadr effect) disk)))))
              (:spool-read (list :spool-read :ok (caddr effect)
                                 (take (caddr effect) (nthcdr (cadr effect) disk))))
              ((:open-local :local)
               (if answer (cons :local (cut-line (car replies))) '(:local-window)))
              (otherwise nil)))
           (replies (if answer (cdr replies) replies)))
      (if event
          (let ((pair (fn-csp-step s event)))
            (cut-drive (car pair) (append (cdr effects) (cadr pair)) wire chunk disk replies
                       local journals (1- fuel)))
        (cut-drive s (cdr effects) wire chunk disk replies local journals (1- fuel)))))
   ((fn-csp-done-p s) (list (fn-csp-mode s) s local journals))
   ((fn-csp-tick-p s)
    (let ((pair (fn-csp-step s '(:tick))))
      (cut-drive (car pair) (cadr pair) wire chunk disk replies local journals (1- fuel))))
   ((consp wire)
    (let* ((n (min chunk (len wire)))
           (pair (fn-csp-step s (cons :remote (take n wire)))))
      (cut-drive (car pair) (cadr pair) (nthcdr n wire) chunk disk replies local journals
                 (1- fuel))))
   (t (list :stuck s local journals))))

(defun cut-round (cursor reply chunk replies)
  (declare (xargs :mode :program))
  (cut-drive (cut-csp-state cursor 1000000) nil reply chunk nil replies nil nil 100000))

(defconst *cut-replies* '("200 local ready" "335 send it" "235 stored" "435 duplicate"))
(defconst *cut-round* (cut-round (fn-cu-fresh-cursor *cut-peer*) *cut-reply* 512 *cut-replies*))
(defconst *cut-final-cursor* (fn-cu-cursor *cut-peer* 4 *cut-chain-2*))
(defun cut-round-session (r) (declare (xargs :mode :program)) (fn-csp-session (cadr r)))

; The verified batch is offered oldest first: A1 by IHAVE, its body on the
; 335 (dot-stuffed again for the local node), then A2, answered 435.  The
; cursor is journaled once, at the batch's end, and the round ends done.
(assert-event (eq (car *cut-round*) :done))
(assert-event
 (equal (nth 2 *cut-round*)
        (append (cut-line "IHAVE <a1@example.invalid>")
                *cut-a1-bytes* (cut-line ".")
                (cut-line "IHAVE <a2@example.invalid>"))))
(assert-event (equal (nth 3 *cut-round*) (list *cut-final-cursor*)))
(assert-event (equal (fn-csp-close (cadr *cut-round*)) *cut-final-cursor*))
(assert-event (equal (fn-cu-r-counts (fn-cu-s-round (cut-round-session *cut-round*))) '(1 1 0)))
; The same reply in 7-octet windows drives the same round.
(assert-event
 (equal (cdr (cut-round (fn-cu-fresh-cursor *cut-peer*) *cut-reply* 7 *cut-replies*))
        (cdr *cut-round*)))

; Teeth for the proof-owed verdict keystone over fn-csp-step (the analog of
; the deleted fn-cu-step-installs-only-through-the-verdict): a body follows
; only the local 335; answered 435, A1's body is never sent.
(defconst *cut-round-435*
  (cut-round (fn-cu-fresh-cursor *cut-peer*) *cut-reply* 512
             '("200 local ready" "435 have it" "435 duplicate")))
(assert-event (eq (car *cut-round-435*) :done))
(assert-event
 (equal (nth 2 *cut-round-435*)
        (append (cut-line "IHAVE <a1@example.invalid>")
                (cut-line "IHAVE <a2@example.invalid>"))))

; Teeth for the proof-owed digest keystone over fn-csp-step (the analog of
; the deleted fn-cu-on-end-refuses-a-digest-mismatch): one octet of A2's
; body changed in transit fails the round :digest-mismatch; nothing reaches
; the local node, nothing is journaled, the cursor stays fresh.
(defconst *cut-bad-reply*
  (let ((i (- (len *cut-reply*) 10)))
    (append (take i *cut-reply*) (list 122) (nthcdr (+ i 1) *cut-reply*))))
(assert-event (not (equal *cut-bad-reply* *cut-reply*)))
(defconst *cut-bad* (cut-round (fn-cu-fresh-cursor *cut-peer*) *cut-bad-reply* 512 *cut-replies*))
(assert-event (eq (car *cut-bad*) :failed))
(assert-event (equal (fn-cu-r-refusal (fn-cu-s-round (cut-round-session *cut-bad*)))
                     :digest-mismatch))
(assert-event (and (null (nth 2 *cut-bad*)) (null (nth 3 *cut-bad*))))
(assert-event (equal (fn-csp-close (cadr *cut-bad*)) (fn-cu-fresh-cursor *cut-peer*)))

; A peer that does not know the verb (a 500) or refuses the position (423)
; is refused by name.
(assert-event
 (equal (fn-cu-r-refusal (fn-cu-s-round (cut-round-session
                                        (cut-round (fn-cu-fresh-cursor *cut-peer*)
                                                   (cut-line "500 what") 512 nil))))
        :peer-lacks-catch-up))
(assert-event
 (equal (fn-cu-r-refusal (fn-cu-s-round (cut-round-session
                                        (cut-round (fn-cu-fresh-cursor *cut-peer*)
                                                   (cut-reply 5 *fn-cu-zero-chain* "1000")
                                                   512 nil))))
        :position-past-end))

; -----------------------------------------------------------------------------
; The journal: FNCU append, scan and replay

;; The frame trailer's digest is an attached function (books/frame-trailer),
;; which a defconst does not evaluate; make-event does.
(make-event
 `(defconst *cut-envelope* ',(fn-cu-cursor-envelope *cut-final-cursor*)))
(assert-event (fn-cbor-octet-listp *cut-envelope*))
; What the host reads at OFFSET: the four-octet prefix, then at most the
; frame length it names (a torn append yields fewer octets).
(defun cut-scan (bytes offset)
  (let* ((prefix (take 4 bytes))
         (plan (fn-feed-journal-prefix prefix))
         (rest (nthcdr 4 bytes)))
    (fn-cu-journal-scan *cut-peer* prefix
                        (if (and (natp plan) (<= plan (len rest))) (take plan rest) rest)
                        offset)))
(assert-event
 (equal (cut-scan *cut-envelope* 0)
        (list :next (len *cut-envelope*) *cut-final-cursor*)))
; A torn append: the frame is short, the open repairs to the offset.
(assert-event
 (equal (car (cut-scan (butlast *cut-envelope* 1) 0)) :repair))

; KEYSTONE fn-cu-records-replay-is-the-last-cursor.  Witness: two appends
; of this peer replay to the second.  Tooth (same peer): a record of
; another peer is not this peer's cursor, and the replay keeps this one.
(defconst *cut-mid-cursor* (fn-cu-cursor *cut-peer* 1 *cut-chain-1*))
(assert-event
 (equal (fn-cu-records-replay (fn-cu-fresh-cursor *cut-peer*)
                              (list *cut-mid-cursor* *cut-final-cursor*))
        *cut-final-cursor*))
(defconst *cut-other* (fn-cu-cursor (cut-octets "B") 9 *cut-chain-1*))
(must-fail-checked
 (assert-event
  (equal (fn-cu-records-replay (fn-cu-fresh-cursor *cut-peer*)
                               (list *cut-mid-cursor* *cut-other*))
         (fn-cu-last-cursor (fn-cu-fresh-cursor *cut-peer*)
                            (list *cut-mid-cursor* *cut-other*)))))

; KEYSTONE fn-cu-resume-asks-from-the-journaled-cursor.  A round begun from
; the replayed journal asks from position 1 with A1's chain; the next batch
; it receives is A2 alone.
(defconst *cut-resumed*
  (fn-cu-begin (fn-cu-records-replay (fn-cu-fresh-cursor *cut-peer*)
                                     (list *cut-mid-cursor*))
               *cut-wildmat*))
(assert-event
 (equal (fn-cu-request *cut-resumed*)
        (fn-cu-command-line *cut-wildmat* 1 *cut-chain-1*)))
(defconst *cut-resumed-round*
  (cut-round (fn-cu-records-replay (fn-cu-fresh-cursor *cut-peer*) (list *cut-mid-cursor*))
             (cut-reply 1 *cut-chain-1* "1000") 512 '("200 local ready" "335 send it" "235 stored")))
(assert-event (eq (car *cut-resumed-round*) :done))
(assert-event (equal (nth 3 *cut-resumed-round*) (list *cut-final-cursor*)))

; KEYSTONE fn-cu-decode-of-encode (PRF-325).  Positive: the final cursor's
; record under the pull chain's zero digest encodes and decodes back to
; the record.  (make-event: the trailer digest is attached.)
(defconst *cut-cu-values*
  (list (fn-cu-cursor-peer *cut-final-cursor*)
        (fn-cu-cursor-position *cut-final-cursor*)
        (fn-cu-cursor-chain *cut-final-cursor*)))
(make-event
 `(defconst *cut-cu-frame* ',(fn-cu-encode :cu-cursor *cut-cu-values* *fn-pull-zero-digest*)))
(assert-event
 (and (fn-cu-record-okp :cu-cursor *cut-cu-values*)
      (fn-frame-digestp *fn-pull-zero-digest*)
      (not (equal *cut-cu-frame* :bad))
      (equal (fn-cu-decode *cut-cu-frame* *fn-pull-zero-digest*)
             (fn-frame-ok *fn-cu-magic* *fn-frame-version* :cu-cursor *cut-cu-values*))))
; The third hypothesis removed: a position that is no natural is no record,
; the encoder answers :bad, and :bad decodes to no record.
(defconst *cut-cu-bad-values*
  (list (fn-cu-cursor-peer *cut-final-cursor*) -1 (fn-cu-cursor-chain *cut-final-cursor*)))
(assert-event
 (and (equal (fn-cu-encode :cu-cursor *cut-cu-bad-values* *fn-pull-zero-digest*) :bad)
      (not (equal (fn-cu-decode :bad *fn-pull-zero-digest*)
                  (fn-frame-ok *fn-cu-magic* *fn-frame-version* :cu-cursor
                               *cut-cu-bad-values*)))))
; The first two hypotheses (a record, a digest) have NO counter-witness:
; fn-cu-encode answers :bad unless both hold, so the third implies them.
; The keystone without them is proved here.
(defthm cut-cu-decode-of-encode-third-hypothesis-alone
  (implies (not (equal (fn-cu-encode kind values digest) :bad))
           (equal (fn-cu-decode (fn-cu-encode kind values digest) digest)
                  (fn-frame-ok *fn-cu-magic* *fn-frame-version* kind values)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cu-decode-of-encode))
           :in-theory (e/d (fn-cu-encode) (fn-cu-decode))))
  :rule-classes nil)
