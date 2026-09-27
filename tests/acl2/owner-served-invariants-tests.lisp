; Teeth for books/owner-served-invariants.lisp (v0 P2, P3, P5).
;
; For each keystone: a reachable witness at which every hypothesis and the
; conclusion hold, then per hypothesis one concrete value at which the other
; hypotheses hold, that hypothesis fails and the conclusion is false, each
; asserted positively and then closed with a must-fail on the conclusion.
; The fixtures are tests/acl2/owner-tests.lisp's served POST scenario.

(in-package "ACL2")
(include-book "owner-tests")
(include-book "../../books/owner-served-invariants")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (equal (symbol-class 'fn-own-finish (w state)) :common-lisp-compliant))
(assert-event (equal (stobjs-in 'fn-own-finish (w state)) '(nil nil fn-arena)))

; -----------------------------------------------------------------------------
; P2: fn-own-240-follows-consumed-completion.

; The live configuration fn-own-finish is given: owner-tests' peer
; configuration, with peer "p" and path-identity own.example.  A local
; submission's staged octets do not depend on it.
(defconst *osi-cfg* *own-peer-cfg*)

; The 240 line fn-own-outcome would render for connection `id' of `o'.
(defun osi-240-reply (o id)
  (let ((conn (fn-own-find-conn id (fn-own-conns o))))
    (fn-served-result-effects
     (fn-served-post-outcome
      (fn-served-make-conn (fn-own-conn-wire conn) (fn-own-conn-session conn)
                           (fn-own-conn-archive conn) (fn-own-conn-config conn)
                           (fn-own-conn-observation conn) (fn-own-clock o))
      :durable))))

; The finish over the arena of the entry that interned the journal PRIOR (the
; wire records, in order; handle i = the i-th record's bytes), as the host's
; arena holds it: fn-own-finish reads the completed row through it.
(defun osi-finish-in (o cfg prior fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (mv (fn-own-finish o cfg fn-arena) fn-arena)))

(defun osi-finish (o cfg prior)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (osi-finish-in o cfg prior fn-arena)
      result)))

(defun osi-p2-240p (o id prior)
  (equal (car (fn-own-outcome (cdr (osi-finish o *osi-cfg* prior)) id
                              (car (osi-finish o *osi-cfg* prior))))
         (osi-240-reply (cdr (osi-finish o *osi-cfg* prior)) id)))

(defun osi-p2-conclusion (o id prior)
  (let* ((o2 (cdr (osi-finish o *osi-cfg* prior)))
         (word (car (osi-finish o *osi-cfg* prior)))
         (pair (fn-sf-completion (fn-sn-files (fn-own-store o))))
         (record (fn-sn-completion-record (fn-own-store o)))
         (w (car (fn-hrt-wire-of prior (list record))))
         (sub (fn-own-inflight o)))
    (and (equal word :durable)
         sub
         (equal (fn-own-sub-id sub) id)
         (fn-sn-completion-enabledp (fn-own-store o))
         (equal (fn-own-store o2) (fn-sn-finish (fn-own-store o)))
         (equal (fn-sf-successes (fn-sn-files (fn-own-store o2)))
                (append (fn-sf-successes (fn-sn-files (fn-own-store o)))
                        (list pair)))
         (equal (fn-own-ledger o2) (append (fn-own-ledger o) (list pair)))
         (equal (fn-own-inflight o2) sub)
         (fn-held-p record)
         (equal (fn-record-msgid w)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload w) (fn-own-sub-stored-octets *osi-cfg* sub (fn-own-node-secret o)))
         (fn-sf-record-has-pairp pair (fn-sf-records (fn-sn-files (fn-own-store o2))))
         t)))

; The record the host should stage for the submission in flight: its
; Message-ID and octets, with the metadata own-record derives.
(defun osi-record-of-wire (sequence txid sub payload)
  (let ((msgid (fn-record-octets-string (fn-own-sub-msgid sub))))
    (fn-record-make sequence txid txid msgid payload
                    '("fn.letters")
                    (concatenate 'string "own-pin:" msgid)
                    (concatenate 'string "own-content:" msgid)
                    (concatenate 'string "own-release:" msgid)
                    2 841000000)))
; The store retains held rows (records-flip): the owner stages the row the
; entry interns (owner-tests' convention: handle = journal sequence).
(defun osi-record-of (sequence txid sub payload)
  (fn-hrt-row-at (osi-record-of-wire sequence txid sub payload) sequence))
; ALPHA of a completion row staged on *own-taken* (whose history is
; owner-tests' "<one@example>" and "<two@example>" at handles 0 and 1): the
; bytes under its handle in the arena that interned the journal in order,
; the staged record WIRE last.
(defun osi-completion-bytes (o wire)
  (fn-hrt-bytes (list (own-record-wire 0 0 "<one@example>")
                      (own-record-wire 1 1 "<two@example>")
                      wire)
                (fn-record-payload (fn-sn-completion-record (fn-own-store o)))))
; The journal the entry interned for a completion staged on *own-taken*:
; owner-tests' two records at handles 0 and 1, the staged record WIRE last.
(defun osi-prior (wire)
  (if wire
      (list (own-record-wire 0 0 "<one@example>") (own-record-wire 1 1 "<two@example>") wire)
    (list (own-record-wire 0 0 "<one@example>") (own-record-wire 1 1 "<two@example>"))))
(defun osi-sub-record (sequence txid sub)
  (osi-record-of sequence txid sub (fn-own-sub-octets sub)))

(defun osi-drop-last (xs)
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (osi-drop-last (cdr xs)))
    nil))

; Witness: connection 4's injected article, staged as itself, at :completing.
(defconst *osi-sub* (fn-own-inflight *own-taken*))
(defconst *osi-completing*
  (fn-own-run *own-taken*
              (osi-drop-last (own-post-events (osi-sub-record 2 2 *osi-sub*)))))
(defconst *osi-completing-prior*
  (osi-prior (osi-record-of-wire 2 2 *osi-sub* (fn-own-sub-octets *osi-sub*))))
(assert-event (fn-own-relation *osi-completing*))
(assert-event (fn-sn-completion-enabledp (fn-own-store *osi-completing*)))
(assert-event (equal (car (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*)) :durable))
(assert-event (osi-p2-240p *osi-completing* 4 *osi-completing-prior*))
(assert-event (equal (fn-served-reply-octets
                      (car (fn-own-outcome (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*)) 4
                                           (car (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*)))))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (osi-p2-conclusion *osi-completing* 4 *osi-completing-prior*))
; The flip regression (L5's finding): the completed row's payload is a
; handle, so the comparison fn-own-completion-names-submission-p made before
; it read through the arena is false on this durable completion, and every
; served POST finish answered :fault (436/441 uncertain).
(assert-event (natp (fn-record-payload (fn-sn-completion-record (fn-own-store *osi-completing*)))))
(assert-event (not (equal (fn-record-payload (fn-sn-completion-record (fn-own-store *osi-completing*)))
                          (fn-own-sub-stored-octets *osi-cfg* *osi-sub*
                                                    (fn-own-node-secret *osi-completing*)))))
; The finish is the (:complete) event on the owner.
(assert-event (equal (cdr (osi-finish *osi-completing* *osi-cfg* *osi-completing-prior*))
                     (fn-own-step *osi-completing* '(:complete))))

; FINDING (P2).  With the host's word, 240 is rendered over a completion of
; another record.  owner-tests' *own-p-done* completed <three@example> for
; the injected "Hello, news." submission of connection 4, and *own-240* is
; the 240.  fn-own-finish over the same state answers :fault, so the outcome
; is the uncertain 441.
(defconst *osi-mismatch-completing*
  (fn-own-run *own-taken*
              (osi-drop-last (own-post-events (own-record 2 2 "<three@example>")))))
(defconst *osi-mismatch-prior* (osi-prior (own-record-wire 2 2 "<three@example>")))
(assert-event (equal (fn-own-step *osi-mismatch-completing* '(:complete)) *own-p-done*))
(assert-event (equal (fn-served-reply-octets (car *own-240*))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (equal (fn-record-msgid (fn-sn-completion-record
                                       (fn-own-store *osi-mismatch-completing*)))
                     "<three@example>"))
(assert-event (not (equal (fn-record-octets-string (fn-own-sub-msgid *osi-sub*))
                          "<three@example>")))
; by specification: the flip: the payload is a handle; the completed row's
; bytes (alpha) are <three@example>'s, not the submission's octets.
(assert-event (not (equal (osi-completion-bytes *osi-mismatch-completing*
                                                (own-record-wire 2 2 "<three@example>"))
                          (fn-own-sub-octets *osi-sub*))))
(assert-event (equal (car (osi-finish *osi-mismatch-completing* *osi-cfg* *osi-mismatch-prior*)) :fault))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (cdr (osi-finish *osi-mismatch-completing* *osi-cfg* *osi-mismatch-prior*)) 4
                                           (car (osi-finish *osi-mismatch-completing* *osi-cfg* *osi-mismatch-prior*))))))
                     (fn-nntp-string-octets "441 ")))

; Hypothesis 2 (the reply is 240).  *own-taken*: related, nothing staged,
; the finish is :fault and the reply the uncertain 441.
(assert-event (fn-own-relation *own-taken*))
(assert-event (not (osi-p2-240p *own-taken* 4 (osi-prior nil))))
(assert-event (not (osi-p2-conclusion *own-taken* 4 (osi-prior nil))))
(must-fail (assert-event (osi-p2-conclusion *own-taken* 4 (osi-prior nil))))

; Hypothesis 1 (the relation).  Connection 4's session replaced by a
; malformed one: every completion renders the same 403, so the reply equals
; the reference 240 expression while the finish word is :fault.
(defconst *osi-bad-conn*
  (let ((conn (fn-own-find-conn 4 (fn-own-conns *own-taken*))))
    (fn-own-conn-make-group-indexed 4 (fn-own-conn-version conn)
                                    (fn-own-conn-frontier conn)
                                    (fn-own-conn-wire conn) nil
                                    (fn-own-conn-archive conn)
                                    (fn-own-conn-config conn)
                                    (fn-own-conn-observation conn)
                                    (fn-own-conn-verdicts conn)
                                    (fn-own-conn-index conn)
                                    (fn-own-conn-group-index conn) (fn-own-conn-control conn))))
(defconst *osi-unrelated*
  (fn-own-set-conns *own-taken*
                    (fn-own-replace-conn *osi-bad-conn* (fn-own-conns *own-taken*))))
(assert-event (not (fn-own-relation *osi-unrelated*)))
(assert-event (osi-p2-240p *osi-unrelated* 4 (osi-prior nil)))
(assert-event (not (osi-p2-conclusion *osi-unrelated* 4 (osi-prior nil))))
(must-fail (assert-event (osi-p2-conclusion *osi-unrelated* 4 (osi-prior nil))))

; Transit (transit-436, the 6c0626c5 regression).  A transit submission from
; peer "p" in flight on connection 4 of the reachable *own-taken*, installed
; with owner-tests' own-with-inflight (the idiom of its feed-subject teeth;
; it is not reached by an IHAVE through fn-own-read).  *osi-cfg* sets
; path-identity own.example, so the octets fn-owner-take stages for the
; Store are the received octets with own.example prepended to Path.
(defconst *osi-transit-sub*
  (let ((sub (fn-own-inflight *own-taken*)))
    (fn-own-sub-make 4 (fn-own-sub-version sub) (fn-own-sub-mark sub)
                     (fn-peer-make-submission
                      "p" :ihave *own-transit-msgid*
                      (own-transit-octets "peer.example!x")))))
(defconst *osi-transit-stored*
  (fn-own-sub-stored-octets *osi-cfg* *osi-transit-sub* nil))
(defconst *osi-transit-received* (fn-own-sub-octets *osi-transit-sub*))
(assert-event (fn-own-transit-subp *osi-transit-sub*))
; Non-degenerate: the staged octets are not the received ones; they begin
; with this node's identity.
(assert-event (not (equal *osi-transit-stored* *osi-transit-received*)))
(assert-event (equal (take 18 *osi-transit-stored*)
                     (fn-nntp-string-octets "Path: own.example!")))

(defun osi-transit-completing (payload)
  (fn-own-run (own-with-inflight *own-taken* *osi-transit-sub*)
              (osi-drop-last
               (own-post-events
                (osi-record-of 2 2 *osi-transit-sub* payload)))))

; Witness: the Store completes the record carrying the staged octets.  The
; finish is :durable, the reply is the 240 expression, and the keystone's
; conclusion holds.
(defconst *osi-transit-completing* (osi-transit-completing *osi-transit-stored*))
(defconst *osi-transit-prior*
  (osi-prior (osi-record-of-wire 2 2 *osi-transit-sub* *osi-transit-stored*)))
(assert-event (fn-own-relation *osi-transit-completing*))
(assert-event (fn-sn-completion-enabledp (fn-own-store *osi-transit-completing*)))
(assert-event (equal (car (osi-finish *osi-transit-completing* *osi-cfg* *osi-transit-prior*))
                     :durable))
(assert-event (osi-p2-240p *osi-transit-completing* 4 *osi-transit-prior*))
(assert-event (osi-p2-conclusion *osi-transit-completing* 4 *osi-transit-prior*))
; The regression: 6c0626c5's fn-own-finish compared the completed record
; with the received octets (fn-own-sub-octets).  On this durable completion
; that comparison is false, so it answered :fault, which the host reported
; as `436 ... uncertain' and a recovery stop.
; by specification: the flip: the completed row's payload is a handle; its
; bytes (alpha over the journal's arena) are the staged octets, not the
; received ones.
(defconst *osi-transit-wire* (osi-record-of-wire 2 2 *osi-transit-sub* *osi-transit-stored*))
(assert-event (equal (osi-completion-bytes *osi-transit-completing* *osi-transit-wire*)
                     *osi-transit-stored*))
(assert-event (not (equal (osi-completion-bytes *osi-transit-completing* *osi-transit-wire*)
                          *osi-transit-received*)))
(must-fail
 (assert-event (equal (osi-completion-bytes *osi-transit-completing* *osi-transit-wire*)
                      *osi-transit-received*)))

; Negative: the Store completes a record carrying the received octets, which
; is not what the owner staged.  The finish is :fault (uncertain), no 240 is
; rendered, and the conclusion fails.
(defconst *osi-transit-unstaged* (osi-transit-completing *osi-transit-received*))
(defconst *osi-unstaged-prior*
  (osi-prior (osi-record-of-wire 2 2 *osi-transit-sub* *osi-transit-received*)))
(assert-event (fn-own-relation *osi-transit-unstaged*))
(assert-event (fn-sn-completion-enabledp (fn-own-store *osi-transit-unstaged*)))
(assert-event (equal (car (osi-finish *osi-transit-unstaged* *osi-cfg* *osi-unstaged-prior*))
                     :fault))
(assert-event (not (osi-p2-240p *osi-transit-unstaged* 4 *osi-unstaged-prior*)))
(must-fail (assert-event (osi-p2-conclusion *osi-transit-unstaged* 4 *osi-unstaged-prior*)))

; Negative: a completion for a different article.  The record carries the
; staged octets but another Message-ID; the finish still faults.
(defconst *osi-transit-other*
  (fn-own-run (own-with-inflight *own-taken* *osi-transit-sub*)
              (osi-drop-last
               (own-post-events
                (fn-hrt-row-at
                 (fn-record-make 2 2 2 "<other@example.invalid>"
                                 *osi-transit-stored* '("fn.letters")
                                 "own-pin:<other@example.invalid>"
                                 "own-content:<other@example.invalid>"
                                 "own-release:<other@example.invalid>"
                                 2 841000000)
                 2)))))
(defconst *osi-other-prior*
  (osi-prior (fn-record-make 2 2 2 "<other@example.invalid>"
                             *osi-transit-stored* '("fn.letters")
                             "own-pin:<other@example.invalid>"
                             "own-content:<other@example.invalid>"
                             "own-release:<other@example.invalid>"
                             2 841000000)))
(assert-event (fn-own-relation *osi-transit-other*))
(assert-event (fn-sn-completion-enabledp (fn-own-store *osi-transit-other*)))
(assert-event (equal (car (osi-finish *osi-transit-other* *osi-cfg* *osi-other-prior*)) :fault))
(assert-event (not (osi-p2-240p *osi-transit-other* 4 *osi-other-prior*)))
(must-fail (assert-event (osi-p2-conclusion *osi-transit-other* 4 *osi-other-prior*)))

; The transit arm's Path shape on the witness (P7's
; fn-peer-relayed-octets-keep-the-received-path-tail, concretely): the staged
; octets are the received ones with "own.example!<diagnostic>!" inserted
; before the received Path contents, and nothing else changed.
(defconst *osi-received-path-line*
  (fn-nntp-string-octets "Path: peer.example!x"))
(assert-event (equal (take (len *osi-received-path-line*) *osi-transit-received*)
                     *osi-received-path-line*))
(assert-event (equal (nthcdr 6 *osi-transit-received*)
                     (let ((tail (nthcdr 6 *osi-transit-stored*)))
                       (nthcdr (- (len tail) (len (nthcdr 6 *osi-transit-received*)))
                               tail))))

; -----------------------------------------------------------------------------
; P3: fn-own-pinned-view-survives-other-post (restated under NNT-042 on
; 2026-09-27: the reader's PIN survives another post; its served chunk answers
; as before unless it selects a group, when it acquires the fresh view BY
; SPECIFICATION) and fn-own-other-post-keeps-a-non-selecting-read-step.

(defun osi-oc (o) (fn-ocfg-make o *own-config* nil nil))

(defun osi-after-post (oc events sub-id word)
  (let ((oc1 (fn-ocfg-run oc events)))
    (fn-ocfg-with-owner oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))

; The chunk read answers as before (the pre-NNT-042 conclusion; now the
; not-yet-proved chunk form for chunks framing no selection).
(defun osi-p3-read-conclusion (oc events sub-id word id octets)
  (let ((oc2 (osi-after-post oc events sub-id word)))
    (and (equal (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc2 id octets))
                (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets)))
         (equal (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc2 id octets))
                (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc id octets))))))

; The theorem's conclusion: the connection record and the clock survive.
(defun osi-p3-pin-conclusion (oc events sub-id word id)
  (let ((oc2 (osi-after-post oc events sub-id word)))
    (and (equal (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
         (equal (fn-own-clock (fn-ocfg-owner oc2)) (fn-own-clock (fn-ocfg-owner oc))))))

; The corollary's conclusion: one framed event answers as before.
(defun osi-p3-step-conclusion (oc events sub-id word id event)
  (let ((oc2 (osi-after-post oc events sub-id word)))
    (equal (car (fn-ocfg-read-step oc2 id event))
           (car (fn-ocfg-read-step oc id event)))))

(defun osi-reader-p (oc id)
  (not (fn-peer-session-cfg
        (fn-auth-session-base
         (fn-own-conn-session (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))))

(defconst *osi-q* (osi-oc *own-q*))
(defconst *osi-post-events*
  (cons '(:take) (own-post-events (osi-sub-record 2 2 *osi-sub*))))
(defconst *osi-group* *own-group-octets*)
(defconst *osi-group-event* (list :command (butlast *own-group-octets* 2)))
(defconst *osi-stat-event* (list :command (butlast *own-stat-octets* 2)))
(defconst *osi-after* (osi-after-post *osi-q* *osi-post-events* 4 :durable))

; Witness: reader 3 pinned at version 2; connection 4's POST is taken,
; staged, completed and answered 240; the view the store publishes moves to
; version 3.  Reader 3's record, its pin included, and the clock are what
; they were.
(assert-event (fn-ocfg-writer-eventsp *osi-post-events*))
(assert-event (osi-reader-p *osi-q* 3))
(assert-event (fn-own-find-conn 3 (fn-own-conns *own-q*)))
(assert-event (equal (fn-own-conn-version (fn-own-find-conn 3 (fn-own-conns *own-q*))) 2))
(assert-event (equal (fn-own-view-version (fn-own-view (fn-ocfg-owner *osi-after*))) 3))
(assert-event (equal (fn-own-take 4 (fn-served-reply-octets
                                     (car (fn-own-outcome
                                           (fn-ocfg-owner (fn-ocfg-run *osi-q* *osi-post-events*))
                                           4 :durable))))
                     (fn-nntp-string-octets "240 ")))
(assert-event (osi-p3-pin-conclusion *osi-q* *osi-post-events* 4 :durable 3))
(assert-event (equal (fn-own-conn-version
                      (fn-own-find-conn 3 (fn-own-conns (fn-ocfg-owner *osi-after*))))
                     2))
; BY SPECIFICATION (NNT-042): reader 3's GROUP after the post acquires the
; fresh view (version 3) and counts connection 4's article, so the GROUP
; chunk no longer answers as before.  A STAT does: it is answered from the
; pin (the corollary, per framed event; and the chunk form as executable
; evidence).
(assert-event (fn-served-advance-eventp *osi-group-event*))
(assert-event (not (fn-served-advance-eventp *osi-stat-event*)))
(assert-event (not (osi-p3-read-conclusion *osi-q* *osi-post-events* 4 :durable 3 *osi-group*)))
(assert-event (consp (fn-served-reply-octets
                      (fn-own-tls-result-effects
                       (fn-ocfg-read-tls-prefix *osi-after* 3 *osi-group*)))))
(assert-event (osi-p3-step-conclusion *osi-q* *osi-post-events* 4 :durable 3 *osi-stat-event*))
(assert-event (consp (fn-served-reply-octets (car (fn-ocfg-read-step *osi-q* 3 *osi-stat-event*)))))
(assert-event (osi-p3-read-conclusion *osi-q* *osi-post-events* 4 :durable 3 *own-stat-octets*))

; Hypothesis (not (fn-served-advance-eventp event)) of the corollary: the
; GROUP event is answered from the fresh view.
(assert-event (not (osi-p3-step-conclusion *osi-q* *osi-post-events* 4 :durable 3 *osi-group-event*)))
(must-fail (assert-event (osi-p3-step-conclusion *osi-q* *osi-post-events* 4 :durable 3 *osi-group-event*)))

; Hypothesis (not (equal id sub-id)).  The poster itself is re-pinned by
; the 240: its record changes.
(assert-event (osi-reader-p *osi-q* 4))
(assert-event (not (osi-p3-pin-conclusion *osi-q* *osi-post-events* 4 :durable 4)))
(must-fail (assert-event (osi-p3-pin-conclusion *osi-q* *osi-post-events* 4 :durable 4)))

; Hypothesis (fn-ocfg-writer-eventsp events).  An (:advance 3) among the
; events re-pins reader 3 itself.
(defconst *osi-advance-events* (append *osi-post-events* '((:advance 3))))
(assert-event (not (fn-ocfg-writer-eventsp *osi-advance-events*)))
(assert-event (not (osi-p3-pin-conclusion *osi-q* *osi-advance-events* 4 :durable 3)))
(must-fail (assert-event (osi-p3-pin-conclusion *osi-q* *osi-advance-events* 4 :durable 3)))

; A peer connection's record survives another post too (P3 no longer needs
; the reader hypothesis), but its chunk read is not pin-stable: IHAVE answers
; from the live node (fn-own-conn-live-session), 335 before and 435 after.
; This is the reader hypothesis of the chunk read statements.  The post here
; is owner-tests' CLI post by connection 1.
(defconst *osi-peered* (osi-oc *own-peered-begun*))
(defconst *osi-peer-events* (own-post-events (own-record 0 0 "<one@example>")))
(assert-event (fn-ocfg-writer-eventsp *osi-peer-events*))
(assert-event (not (osi-reader-p *osi-peered* *own-peer-id*)))
(assert-event (not (equal *own-peer-id* 1)))
(assert-event (osi-p3-pin-conclusion *osi-peered* *osi-peer-events* 1 :durable *own-peer-id*))
(assert-event (not (osi-p3-read-conclusion *osi-peered* *osi-peer-events* 1 :durable
                                           *own-peer-id* *own-ihave-octets*)))
(must-fail (assert-event (osi-p3-read-conclusion *osi-peered* *osi-peer-events* 1 :durable
                                                 *own-peer-id* *own-ihave-octets*)))

; -----------------------------------------------------------------------------
; P5: the bound, and the fault wrapper.

(defconst *osi-open0*
  (fn-ocfg-make (fn-own-start (fn-sn-initial *own-groups* 10) 2) *own-peer-cfg* nil nil))
(defconst *osi-full* (cdr (fn-ocfg-open (cdr (fn-ocfg-open *osi-open0* nil)) nil)))
(assert-event (fn-ocfg-statep *osi-full*))
(assert-event (equal (len (fn-own-conns (fn-ocfg-owner *osi-full*))) 2))
(assert-event (equal (fn-own-max-conns (fn-ocfg-owner *osi-full*)) 2))
(assert-event (equal (fn-ocfg-open *osi-full* nil) (cons nil *osi-full*)))

; Hypothesis (the bound is reached).  Below it the open succeeds: a greeting
; and a new connection.
(assert-event (fn-ocfg-statep *osi-open0*))
(assert-event (< (len (fn-own-conns (fn-ocfg-owner *osi-open0*)))
                 (fn-own-max-conns (fn-ocfg-owner *osi-open0*))))
(assert-event (consp (car (fn-ocfg-open *osi-open0* nil))))
(must-fail (assert-event (equal (fn-ocfg-open *osi-open0* nil) (cons nil *osi-open0*))))

; Hypothesis (fn-ocfg-statep).  The same full owner with its identifier
; counter wound back onto an open connection: the refused open still writes
; that connection's reader context and pin.
(defconst *osi-wound*
  (let ((o (fn-ocfg-owner *osi-full*)))
    (fn-ocfg-make (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                               0 (fn-own-max-conns o) (fn-own-pending o)
                               (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                               (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                               (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))
                  (fn-ocfg-config *osi-full*) nil nil)))
(assert-event (not (fn-ocfg-statep *osi-wound*)))
(assert-event (<= (fn-own-max-conns (fn-ocfg-owner *osi-wound*))
                  (len (fn-own-conns (fn-ocfg-owner *osi-wound*)))))
(assert-event (not (equal (fn-ocfg-open *osi-wound* nil) (cons nil *osi-wound*))))
(must-fail (assert-event (equal (fn-ocfg-open *osi-wound* nil) (cons nil *osi-wound*))))

; The fault wrapper: its equation at a reachable connection, and K-FAULT-2
; over it.  The one hypothesis, other /= id: the faulted connection itself
; is gone.
(defconst *osi-faulted* (fn-ocfg-fault *osi-full* 0))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))
(assert-event (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *osi-full*))))
(assert-event (consp (car *osi-faulted*)))
(assert-event (equal (car *osi-faulted*) (car (fn-own-fault (fn-ocfg-owner *osi-full*) 0))))
(assert-event (equal (fn-ocfg-owner (cdr *osi-faulted*))
                     (cdr (fn-own-fault (fn-ocfg-owner *osi-full*) 0))))
(assert-event (equal (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                     (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *osi-full*)))))
(assert-event (fn-ocfg-pin-find 1 (fn-ocfg-pins (cdr *osi-faulted*))))
(assert-event (equal (fn-ocfg-pin-find 1 (fn-ocfg-pins (cdr *osi-faulted*)))
                     (fn-ocfg-pin-find 1 (fn-ocfg-pins *osi-full*))))
(assert-event (not (equal (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                          (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))))
(must-fail (assert-event
            (equal (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner (cdr *osi-faulted*))))
                   (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *osi-full*))))))
