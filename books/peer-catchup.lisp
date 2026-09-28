; fn: catching up from a peer -- the requesting half (PRF-325, NNT-053;
; specs/peering.md "Catching up from a peer").
;
; A node that is new, or has been away, fetches a peer's articles as the
; batches of XFNCATCHUP (books/peer-catchup-serve.lisp) instead of one
; NEWNEWS listing and one ARTICLE per Message-ID.  Each batch is received
; whole, its digest chain recomputed and compared with the peer's claim, and
; only then are its records offered, one at a time and oldest first, to THIS
; node by IHAVE on the logical transit connection of that peer: the node's
; own prepare and verdict path decides each one, exactly as for a push from
; that peer.  Catch-up imports articles and their provenance (the Path the
; local acceptance extends); it never carries the peer's article numbers,
; never installs anything itself, and a peer's cancel arrives as an offered
; article that the local verdict decides like any other.
;
; The session is the pull's (books/peer-pull-session.lisp): the feed's
; protected preamble (STARTTLS, the verified handshake, AUTHINFO from the
; outbound credential profile) decided by `fn-pull-plan-verdict', then this
; round in place of the NEWNEWS round.  The host drives both with the same
; effect vocabulary (host/native/pull-service.lisp `fnn-pull-round'):
; (:journal . cursor), (:dial), (:tls NAME ANCHOR), (:remote . octets),
; (:open-local), (:local . octets), (:close).
;
; THE CURSOR is (peer position chain): the peer's log position the last
; verified batch ended at and the digest chain over every record before it.
; It is journaled (FNCU, <store>/catch-up/) only after every record of the
; batch drew 235, 435 or 437 from the local node, so a cut anywhere resumes
; at the last journaled batch boundary; a record of the interrupted batch
; the node committed before the cut is offered again and answered 435
; (duplicate suppression, specs/peering.md K4): nothing is skipped and
; nothing is installed twice.
;
; What is proved (the host calls `fn-cu-session-step-pair',
; `fn-cu-session-begin-pair', `fn-cu-session-close', `fn-cu-cursor-envelope',
; `fn-cu-journal-scan' and `fn-cu-records-replay'):
;   fn-cu-step-keeps-offers-verified   while a round offers a batch, the batch
;       chains from the committed chain to the peer's claim (the invariant
;       `fn-cu-verifiedp', established by `fn-cu-begin'): no record reaches
;       the local node from a batch whose recomputed chain differs
;   fn-cu-on-end-refuses-a-digest-mismatch   a mismatch ends the round
;       :failed with the refusal :digest-mismatch, only (:close) sent, the
;       cursor unmoved
;   fn-cu-step-installs-only-through-the-verdict   every octet sent to the
;       local node is the IHAVE of the record the round then waits on, or
;       that record's body right after the local node answered 335; every
;       journal record is the round's committed cursor with nothing of its
;       batch left to offer
;   fn-cu-records-replay-is-the-last-cursor   the open recovers the last
;       journaled cursor (a torn tail is truncated to it)
;   fn-cu-resume-asks-from-the-journaled-cursor   a round begun from the
;       recovered cursor asks the peer from exactly that position and chain
;   fn-cu-decode-of-encode   an FNCU record round-trips
(in-package "ACL2")
(include-book "peer-pull-session")
(include-book "peer-catchup-serve")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:linear fn-frame-at-mostp-bounds-len))))

; -----------------------------------------------------------------------------
; Policy

; The quantum a requester asks for (octets of article per batch beyond the
; first record): local policy, a bound on one batch's buffering.
(defconst *fn-cu-request-quantum* 262144)

; The longest line a batch may carry (an article line; RFC 5536 section 3.1
; bounds a line at 998 octets, a stored article's framing does not): a line
; longer than this fails the round by name rather than growing the buffer.
(defconst *fn-cu-max-line* 1048576)

; -----------------------------------------------------------------------------
; The cursor

(defun fn-cu-cursor (peer position chain)
  (declare (xargs :guard t))
  (list peer position chain))
(defun fn-cu-cursor-peer (c) (declare (xargs :guard t)) (fn-pull-at 0 c))
(defun fn-cu-cursor-position (c) (declare (xargs :guard t)) (fn-pull-at 1 c))
(defun fn-cu-cursor-chain (c) (declare (xargs :guard t)) (fn-pull-at 2 c))

(defthm fn-cu-cursor-fields
  (and (equal (fn-cu-cursor-peer (fn-cu-cursor peer position chain)) peer)
       (equal (fn-cu-cursor-position (fn-cu-cursor peer position chain)) position)
       (equal (fn-cu-cursor-chain (fn-cu-cursor peer position chain)) chain)))

(defun fn-cu-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 3)
       (fn-feed-namep (fn-cu-cursor-peer c))
       (natp (fn-cu-cursor-position c))
       (< (fn-cu-cursor-position c) *fn-cu-u64-limit*)
       (fn-cu-chainp (fn-cu-cursor-chain c))))

(defun fn-cu-fresh-cursor (peer)
  (declare (xargs :guard t))
  (fn-cu-cursor peer 0 *fn-cu-zero-chain*))

(in-theory (disable fn-cu-cursor fn-cu-cursor-peer fn-cu-cursor-position
                    fn-cu-cursor-chain))

; -----------------------------------------------------------------------------
; The round
;
; (phase peer wildmat position chain buf batch records cur todo counts
;  refusal localp end)
;   phase    :reply :local-greeting :offer :forward :done :failed
;   position chain   the committed cursor's fields
;   buf      remote octets not yet framed into lines
;   batch    nil before the batch's status line, else (next end morep claim)
;   records  while reading: the batch's complete records, newest first;
;            once verified: the batch's records, oldest first (msgid . lines)
;   cur      the record being read: (msgid remaining lines-rev), or nil
;   running  the chain over the batch's complete records so far
;   todo     the verified batch's records still to offer, oldest first
;   counts   (imported duplicate refused)
;   refusal  why the round failed, or nil
;   localp   the local transit connection is open
;   end      the peer's log position its last batch named

(defun fn-cu-round (phase peer wildmat position chain buf batch records cur
                          running todo counts refusal localp end)
  (declare (xargs :guard t))
  (list phase peer wildmat position chain buf batch records cur running todo
        counts refusal localp end))

(defun fn-cu-r-phase (r) (declare (xargs :guard t)) (fn-pull-at 0 r))
(defun fn-cu-r-peer (r) (declare (xargs :guard t)) (fn-pull-at 1 r))
(defun fn-cu-r-wildmat (r) (declare (xargs :guard t)) (fn-pull-at 2 r))
(defun fn-cu-r-position (r) (declare (xargs :guard t)) (fn-pull-at 3 r))
(defun fn-cu-r-chain (r) (declare (xargs :guard t)) (fn-pull-at 4 r))
(defun fn-cu-r-buf (r) (declare (xargs :guard t)) (fn-pull-at 5 r))
(defun fn-cu-r-batch (r) (declare (xargs :guard t)) (fn-pull-at 6 r))
(defun fn-cu-r-records (r) (declare (xargs :guard t)) (fn-pull-at 7 r))
(defun fn-cu-r-cur (r) (declare (xargs :guard t)) (fn-pull-at 8 r))
(defun fn-cu-r-running (r) (declare (xargs :guard t)) (fn-pull-at 9 r))
(defun fn-cu-r-todo (r) (declare (xargs :guard t)) (fn-pull-at 10 r))
(defun fn-cu-r-counts (r) (declare (xargs :guard t)) (fn-pull-at 11 r))
(defun fn-cu-r-refusal (r) (declare (xargs :guard t)) (fn-pull-at 12 r))
(defun fn-cu-r-localp (r) (declare (xargs :guard t)) (fn-pull-at 13 r))
(defun fn-cu-r-end (r) (declare (xargs :guard t)) (fn-pull-at 14 r))

(defthm fn-cu-r-of-round
  (let ((r (fn-cu-round phase peer wildmat position chain buf batch records cur
                        running todo counts refusal localp end)))
    (and (equal (fn-cu-r-phase r) phase)
         (equal (fn-cu-r-peer r) peer)
         (equal (fn-cu-r-wildmat r) wildmat)
         (equal (fn-cu-r-position r) position)
         (equal (fn-cu-r-chain r) chain)
         (equal (fn-cu-r-buf r) buf)
         (equal (fn-cu-r-batch r) batch)
         (equal (fn-cu-r-records r) records)
         (equal (fn-cu-r-cur r) cur)
         (equal (fn-cu-r-running r) running)
         (equal (fn-cu-r-todo r) todo)
         (equal (fn-cu-r-counts r) counts)
         (equal (fn-cu-r-refusal r) refusal)
         (equal (fn-cu-r-localp r) localp)
         (equal (fn-cu-r-end r) end))))

(in-theory (disable fn-cu-round fn-cu-r-phase fn-cu-r-peer fn-cu-r-wildmat
                    fn-cu-r-position fn-cu-r-chain fn-cu-r-buf fn-cu-r-batch
                    fn-cu-r-records fn-cu-r-cur fn-cu-r-running fn-cu-r-todo
                    fn-cu-r-counts fn-cu-r-refusal fn-cu-r-localp fn-cu-r-end))

; Functional update, one field at a time.
(defmacro fn-cu-with (r &key (phase 'nil phase-p) (position 'nil position-p)
                          (chain 'nil chain-p) (buf 'nil buf-p)
                          (batch 'nil batch-p) (records 'nil records-p)
                          (cur 'nil cur-p) (running 'nil running-p)
                          (todo 'nil todo-p) (counts 'nil counts-p)
                          (refusal 'nil refusal-p) (localp 'nil localp-p)
                          (end 'nil end-p))
  `(fn-cu-round ,(if phase-p phase `(fn-cu-r-phase ,r))
                (fn-cu-r-peer ,r)
                (fn-cu-r-wildmat ,r)
                ,(if position-p position `(fn-cu-r-position ,r))
                ,(if chain-p chain `(fn-cu-r-chain ,r))
                ,(if buf-p buf `(fn-cu-r-buf ,r))
                ,(if batch-p batch `(fn-cu-r-batch ,r))
                ,(if records-p records `(fn-cu-r-records ,r))
                ,(if cur-p cur `(fn-cu-r-cur ,r))
                ,(if running-p running `(fn-cu-r-running ,r))
                ,(if todo-p todo `(fn-cu-r-todo ,r))
                ,(if counts-p counts `(fn-cu-r-counts ,r))
                ,(if refusal-p refusal `(fn-cu-r-refusal ,r))
                ,(if localp-p localp `(fn-cu-r-localp ,r))
                ,(if end-p end `(fn-cu-r-end ,r))))

(defun fn-cu-round-cursor (r)
  (declare (xargs :guard t))
  (fn-cu-cursor (fn-cu-r-peer r) (fn-cu-r-position r) (fn-cu-r-chain r)))

(defun fn-cu-done-p (r)
  (declare (xargs :guard t))
  (and (member-equal (fn-cu-r-phase r) '(:done :failed)) t))

; -----------------------------------------------------------------------------
; Wire helpers

(defun fn-cu-command-line (wildmat position chain)
  ; XFNCATCHUP WILDMAT FROM CHAIN QUANTUM, CRLF.
  (declare (xargs :guard t))
  (fn-pull-command (list (fn-record-string-octets "XFNCATCHUP")
                         (fn-cu-list wildmat)
                         (fn-cu-u64-hex position)
                         (fn-cu-hex chain)
                         (fn-nntp-decimal-field *fn-cu-request-quantum*))))

(defun fn-cu-request (r)
  (declare (xargs :guard t))
  (fn-cu-command-line (fn-cu-r-wildmat r) (fn-cu-r-position r) (fn-cu-r-chain r)))

(defun fn-cu-quit () (declare (xargs :guard t)) (fn-pull-quit))

(defun fn-cu-split-aux (buf acc budget)
  (declare (xargs :guard (and (true-listp acc) (natp budget))
                  :measure (nfix budget)))
  (cond ((zp budget) (mv :long nil nil))
        ((atom buf) (mv :need nil nil))
        ((and (equal (car buf) 13) (consp (cdr buf)) (equal (cadr buf) 10))
         (mv :line (revappend acc nil) (cddr buf)))
        (t (fn-cu-split-aux (cdr buf) (cons (car buf) acc) (1- budget)))))

(defun fn-cu-split (buf)
  (declare (xargs :guard t))
  (fn-cu-split-aux buf nil *fn-cu-max-line*))

(defthm fn-cu-split-aux-rest-shorter
  (implies (equal (mv-nth 0 (fn-cu-split-aux buf acc budget)) :line)
           (< (len (mv-nth 2 (fn-cu-split-aux buf acc budget))) (len buf)))
  :rule-classes :linear)

(defthm fn-cu-split-aux-line-true-listp
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (fn-cu-split-aux buf acc budget)))))

; The words of a line split at single spaces.
(defun fn-cu-words-aux (line word acc)
  (declare (xargs :guard (and (true-listp word) (true-listp acc))))
  (cond ((atom line) (revappend (cons (revappend word nil) acc) nil))
        ((equal (car line) 32)
         (fn-cu-words-aux (cdr line) nil (cons (revappend word nil) acc)))
        (t (fn-cu-words-aux (cdr line) (cons (car line) word) acc))))

(defun fn-cu-words (line)
  (declare (xargs :guard t))
  (fn-cu-words-aux line nil nil))

; The status line of a batch: (next end morep claim), or nil.
(defun fn-cu-parse-status (line)
  (declare (xargs :guard t))
  (let ((words (fn-cu-words line)))
    (if (and (equal (len words) 5)
             (equal (car words) (fn-record-string-octets "291")))
        (let ((next (fn-cu-u64-value (nth 1 words)))
              (end (fn-cu-u64-value (nth 2 words)))
              (mode (nth 3 words))
              (claim (fn-cu-unhex (nth 4 words))))
          (if (and (natp next) (natp end)
                   (member-equal mode (list (fn-record-string-octets "more")
                                            (fn-record-string-octets "done")))
                   (fn-cu-chainp claim))
              (list next end (equal mode (fn-record-string-octets "more")) claim)
            nil))
      nil)))

(defun fn-cu-batch-next (b) (declare (xargs :guard t)) (fn-pull-at 0 b))
(defun fn-cu-batch-end (b) (declare (xargs :guard t)) (fn-pull-at 1 b))
(defun fn-cu-batch-morep (b) (declare (xargs :guard t)) (fn-pull-at 2 b))
(defun fn-cu-batch-claim (b) (declare (xargs :guard t)) (fn-pull-at 3 b))

; A record header "R <msgid> <count>": (msgid . count), or nil.
(defun fn-cu-parse-header (line)
  (declare (xargs :guard t))
  (let ((words (fn-cu-words line)))
    (if (and (equal (len words) 3)
             (equal (car words) (list 82))
             (fn-pull-msgidp (nth 1 words))
             (natp (fn-cu-u64-value (nth 2 words))))
        (cons (nth 1 words) (fn-cu-u64-value (nth 2 words)))
      nil)))

; RFC 3977 section 3.1.1: a line of the block that begins with "." had one
; prepended; remove it.
(defun fn-cu-unstuff (line)
  (declare (xargs :guard t))
  (if (and (consp line) (equal (car line) 46)) (cdr line) line))

; The article a record's lines denote: each line then CRLF.
(defun fn-cu-join (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (fn-cu-list (car lines)) (list 13 10) (fn-cu-join (cdr lines)))
    nil))

; The IHAVE body of a record: its lines dot-stuffed, then ".".
(defun fn-cu-body (lines)
  (declare (xargs :guard t))
  (append (fn-nntp-stuff-lines (fn-cu-list lines)) (list 46 13 10)))

(defun fn-cu-record-msgid (rec) (declare (xargs :guard t)) (if (consp rec) (car rec) nil))
(defun fn-cu-record-lines (rec) (declare (xargs :guard t)) (if (consp rec) (cdr rec) nil))

; The chain over RECORDS (oldest first) from CHAIN: the requester's
; recomputation of the peer's `fn-cu-chain-over'.
(defun fn-cu-records-chain (chain records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-cu-records-chain
       (fn-cu-chain-step chain (fn-cu-record-msgid (car records))
                         (fn-cu-join (fn-cu-record-lines (car records))))
       (cdr records))
    (fn-cu-list chain)))

; -----------------------------------------------------------------------------
; Transitions

(defun fn-cu-fail (r reason)
  (declare (xargs :guard t))
  (mv (fn-cu-with r :phase :failed :buf nil :refusal reason)
      (list (list :close))))

(defun fn-cu-count (counts k)
  ; COUNTS with its K-th entry incremented.
  (declare (xargs :guard (natp k)))
  (let ((c (if (and (true-listp counts) (equal (len counts) 3)) counts '(0 0 0))))
    (update-nth k (+ 1 (nfix (nth k c))) c)))

; The IHAVE line offering record REC to the local node.
(defun fn-cu-ihave (rec)
  (declare (xargs :guard t))
  (fn-pull-command (list (fn-record-string-octets "IHAVE")
                         (fn-cu-list (fn-cu-record-msgid rec)))))

; Offer the next verified record, or close the batch: journal the cursor it
; ends at, then ask for the next batch or end the round.
(defun fn-cu-next (r)
  (declare (xargs :guard t))
  (let ((todo (fn-cu-r-todo r)))
    (if (consp todo)
        (mv (fn-cu-with r :phase :offer)
            (list (cons :local (fn-cu-ihave (car todo)))))
      (let* ((b (fn-cu-r-batch r))
             (r2 (fn-cu-with r :position (fn-cu-batch-next b)
                             :chain (fn-cu-batch-claim b)
                             :batch nil :records nil :cur nil :running nil))
             (journal (list (cons :journal (fn-cu-round-cursor r2)))))
        (if (fn-cu-batch-morep b)
            (mv (fn-cu-with r2 :phase :reply)
                (append journal (list (cons :remote (fn-cu-request r2)))))
          (mv (fn-cu-with r2 :phase :done)
              (append journal (list (cons :remote (fn-cu-quit)) (list :close)))))))))

; The batch's block ended: verify it, then offer its records.
(defun fn-cu-on-end (r)
  (declare (xargs :guard t))
  (let* ((b (fn-cu-r-batch r))
         (next (fn-cu-batch-next b))
         (end (fn-cu-batch-end b))
         (position (nfix (fn-cu-r-position r)))
         (records (revappend (fn-cu-list (fn-cu-r-records r)) nil)))
    (cond ((consp (fn-cu-r-buf r)) (fn-cu-fail r :malformed))
          ((consp (fn-cu-r-cur r)) (fn-cu-fail r :malformed))
          ((not (and (natp next) (natp end) (<= next end)
                     (equal (fn-cu-batch-morep b) (< next end))))
           (fn-cu-fail r :malformed))
          ; A batch below the peer's end moves forward, or the round would
          ; ask the same batch forever.
          ((not (or (< position next) (and (equal position next) (equal next end))))
           (fn-cu-fail r :no-progress))
          ((not (equal (fn-cu-records-chain (fn-cu-r-chain r) records)
                       (fn-cu-batch-claim b)))
           (fn-cu-fail r :digest-mismatch))
          ; Verified: RECORDS (oldest first) is the batch the round now
          ; offers, and it stays in the round until the batch closes.
          ((and (consp records) (not (fn-cu-r-localp r)))
           (mv (fn-cu-with r :phase :local-greeting :records records
                           :todo records :end end :localp t)
               (list (list :open-local))))
          (t (fn-cu-next (fn-cu-with r :phase :offer :records records
                                     :todo records :end end))))))

; One framed line of the batch: (mv round effects continuep).
(defun fn-cu-on-line (r line)
  (declare (xargs :guard (true-listp line)))
  (let ((b (fn-cu-r-batch r))
        (cur (fn-cu-r-cur r)))
    (cond
     ((not (consp b))
      (let ((status (fn-cu-parse-status line)))
        (if status
            (mv (fn-cu-with r :batch status :records nil :cur nil) nil t)
          (mv-let (f e)
            (fn-cu-fail r (let ((code (fn-pull-code line)))
                            (cond ((equal code 423) :position-past-end)
                                  ((equal code 480) :authentication-required)
                                  ((equal code 501) :peer-refused-syntax)
                                  ((equal code 500) :peer-lacks-catch-up)
                                  (t :peer-refused))))
            (mv f e nil)))))
     ((consp cur)
      ; Inside a record: CUR is (msgid remaining lines-rev).
      (if (equal line '(46))
          (mv-let (f e) (fn-cu-fail r :malformed) (mv f e nil))
        (let* ((remaining (nfix (fn-pull-at 1 cur)))
               (lines (cons (fn-cu-unstuff line) (fn-cu-list (fn-pull-at 2 cur)))))
          (if (<= remaining 1)
              (let ((rec (cons (car cur) (revappend lines nil))))
                (mv (fn-cu-with r :cur nil
                                :records (cons rec (fn-cu-list (fn-cu-r-records r))))
                    nil t))
            (mv (fn-cu-with r :cur (list (car cur) (- remaining 1) lines)) nil t)))))
     ((equal line '(46))
      (mv-let (r2 e) (fn-cu-on-end r) (mv r2 e nil)))
     (t
      (let ((header (fn-cu-parse-header line)))
        (cond ((not header) (mv-let (f e) (fn-cu-fail r :malformed) (mv f e nil)))
              ((zp (cdr header))
               (mv (fn-cu-with r :records (cons (cons (car header) nil)
                                                (fn-cu-list (fn-cu-r-records r))))
                   nil t))
              (t (mv (fn-cu-with r :cur (list (car header) (cdr header) nil))
                     nil t))))))))

(defthm fn-cu-split-line-true-listp
  (true-listp (mv-nth 1 (fn-cu-split buf))))

(in-theory (disable fn-cu-split))

(defthm fn-cu-on-end-effects-true-listp
  (true-listp (mv-nth 1 (fn-cu-on-end r)))
  :hints (("Goal" :in-theory (disable fn-cu-records-chain fn-cu-request
                                      fn-cu-ihave fn-cu-quit))))

(defthm fn-cu-on-line-effects-true-listp
  (true-listp (mv-nth 1 (fn-cu-on-line r line)))
  :hints (("Goal" :in-theory (disable fn-cu-on-end fn-cu-parse-status
                                      fn-cu-parse-header fn-pull-code fn-cu-unstuff
                                      fn-cu-list fn-pull-at revappend-removal))))

; Frame and handle every complete line in the buffer, at most FUEL of them.
(defun fn-cu-drain (r fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)
                  :guard-hints (("Goal" :in-theory (disable fn-cu-on-line)))))
  (if (or (zp fuel) (not (equal (fn-cu-r-phase r) :reply)))
      (mv r nil)
    (mv-let (status line rest) (fn-cu-split (fn-cu-r-buf r))
      (cond ((equal status :need) (mv r nil))
            ((equal status :long) (fn-cu-fail r :line-too-long))
            (t (mv-let (r2 effects continuep)
                 (fn-cu-on-line (fn-cu-with r :buf rest) line)
                 (if continuep
                     (mv-let (r3 more) (fn-cu-drain r2 (1- fuel))
                       (mv r3 (append effects more)))
                   (mv r2 effects))))))))

(defun fn-cu-event-octets (event)
  (declare (xargs :guard t))
  (fn-pull-event-octets event))

; KEYSTONE SUBJECT.  One event of the round (host/native/pull-service.lisp
; `fnn-pull-round' through `fn-cu-session-step-pair'):
;   (:remote . octets)   octets read from the peer
;   (:local . octets)    the local node's reply on the transit connection
;   (:lost)              either connection failed or closed
(defun fn-cu-step (r event)
  (declare (xargs :guard t))
  (let ((kind (if (consp event) (car event) nil))
        (octets (fn-cu-event-octets event))
        (phase (fn-cu-r-phase r)))
    (cond
     ((member-equal phase '(:done :failed)) (mv r nil))
     ((equal kind :lost) (fn-cu-fail r :lost))
     ((equal kind :remote)
      (if (equal phase :reply)
          (let ((buf (append (fn-cu-list (fn-cu-r-buf r)) octets)))
            (fn-cu-drain (fn-cu-with r :buf buf) (+ 1 (len buf))))
        ; Octets from the peer while no command is outstanding there.
        (fn-cu-fail r :malformed)))
     ((equal kind :local)
      (let ((code (fn-pull-local-code octets))
            (todo (fn-cu-r-todo r)))
        (cond
         ((equal phase :local-greeting)
          (if (member-equal code '(200 201))
              (fn-cu-next r)
            (fn-cu-fail r :local-refused)))
         ((and (equal phase :offer) (consp todo))
          (cond ((equal code 335)
                 (mv (fn-cu-with r :phase :forward)
                     (list (cons :local (fn-cu-body (fn-cu-record-lines (car todo)))))))
                ((equal code 435)
                 (fn-cu-next (fn-cu-with r :todo (cdr todo)
                                         :counts (fn-cu-count (fn-cu-r-counts r) 1))))
                ((equal code 436) (fn-cu-fail r :local-deferred))
                (t (fn-cu-fail r :local-refused))))
         ((and (equal phase :forward) (consp todo))
          (cond ((equal code 235)
                 (fn-cu-next (fn-cu-with r :todo (cdr todo)
                                         :counts (fn-cu-count (fn-cu-r-counts r) 0))))
                ((equal code 437)
                 (fn-cu-next (fn-cu-with r :todo (cdr todo)
                                         :counts (fn-cu-count (fn-cu-r-counts r) 2))))
                ((equal code 436) (fn-cu-fail r :local-deferred))
                (t (fn-cu-fail r :local-refused))))
         (t (fn-cu-fail r :local-refused)))))
     (t (mv r nil)))))

(defun fn-cu-run (r events)
  (declare (xargs :guard t))
  (if (consp events)
      (mv-let (r2 effects) (fn-cu-step r (car events))
        (mv-let (r3 more) (fn-cu-run r2 (cdr events))
          (mv r3 (append (fn-pull-list effects) more))))
    (mv r nil)))

; A round at CURSOR: waiting for the reply to the request the session sends
; when its preamble is ready.
(defun fn-cu-begin (cursor wildmat)
  (declare (xargs :guard t))
  (fn-cu-round :reply (fn-cu-cursor-peer cursor) wildmat
               (fn-cu-cursor-position cursor) (fn-cu-cursor-chain cursor)
               nil nil nil nil nil nil '(0 0 0) nil nil nil))

; The cursor a closed round leaves: always the committed one.
(defun fn-cu-close (r)
  (declare (xargs :guard t))
  (fn-cu-round-cursor r))

; -----------------------------------------------------------------------------
; The session: the pull's preamble, then this round

(defun fn-cu-session (fc round refusal security)
  (declare (xargs :guard t))
  (list fc round refusal security))
(defun fn-cu-s-fc (s) (declare (xargs :guard t)) (fn-pull-at 0 s))
(defun fn-cu-s-round (s) (declare (xargs :guard t)) (fn-pull-at 1 s))
(defun fn-cu-s-refusal (s) (declare (xargs :guard t)) (fn-pull-at 2 s))
(defun fn-cu-s-security (s) (declare (xargs :guard t)) (fn-pull-at 3 s))

(defthm fn-cu-s-of-session
  (and (equal (fn-cu-s-fc (fn-cu-session fc round refusal security)) fc)
       (equal (fn-cu-s-round (fn-cu-session fc round refusal security)) round)
       (equal (fn-cu-s-refusal (fn-cu-session fc round refusal security)) refusal)
       (equal (fn-cu-s-security (fn-cu-session fc round refusal security)) security)))

(in-theory (disable fn-cu-session fn-cu-s-fc fn-cu-s-round fn-cu-s-refusal
                    fn-cu-s-security))

; KEYSTONE SUBJECT.  Beginning a catch-up round (host/native/pull-service.lisp
; `fnn-pull-round' through `fn-cu-session-begin-pair').  PLAN is a pull plan
; (`fn-cu-plans'); whether it may be dialled with its transport and
; credential is the pull's verdict, decided before any connection.
(defun fn-cu-session-begin (plan cursor credential)
  (declare (xargs :guard t))
  (let* ((security (fn-pull-plan-security plan))
         (round (fn-cu-begin cursor (fn-pull-plan-wildmat plan)))
         (refusal (fn-pull-session-refusal plan credential))
         (fc (fn-pull-session-fc0 plan credential)))
    (if refusal
        (mv-let (r2 fail) (fn-cu-fail round refusal)
          (mv (fn-cu-session fc r2 refusal security) fail))
      (mv (fn-cu-session fc round nil security)
          (append (list (list :dial))
                  (if (equal (fn-fc-phase fc) :tls)
                      (list (fn-pull-tls-effect security))
                    nil))))))

(defun fn-cu-obs-effect (kind fc security round)
  (declare (xargs :guard t))
  (cond ((equal kind :starttls) (list (cons :remote (fn-fc-starttls-command))))
        ((equal kind :tls) (list (fn-pull-tls-effect security)))
        ((equal kind :auth-user) (list (cons :remote (fn-fc-auth-user-command fc))))
        ((equal kind :auth-pass) (list (cons :remote (fn-fc-auth-pass-command fc))))
        ((equal kind :ready) (list (cons :remote (fn-cu-request round))))
        (t nil)))

(defun fn-cu-obs-effects (obs fc security round)
  (declare (xargs :guard t))
  (if (consp obs)
      (append (fn-cu-obs-effect (fn-fc-obs-kind (car obs)) fc security round)
              (fn-cu-obs-effects (cdr obs) fc security round))
    nil))

(defun fn-cu-session-readyp (s)
  (declare (xargs :guard t))
  (equal (fn-fc-phase (fn-cu-s-fc s)) :ready))

(defun fn-cu-session-fc-events (s event)
  (declare (xargs :guard t))
  (let ((fc (fn-cu-s-fc s)))
    (cond ((or (fn-cu-done-p (fn-cu-s-round s)) (fn-cu-session-readyp s)) nil)
          ((equal event '(:tls-up)) (fn-pull-pre-events fc :tls-up 1))
          ((and (consp event) (equal (car event) :remote))
           (let ((octets (fn-pull-event-octets event)))
             (fn-pull-pre-events fc octets (+ 1 (len octets)))))
          (t nil))))

; KEYSTONE SUBJECT.  One event of a catch-up session.
(defun fn-cu-session-step (s event)
  (declare (xargs :guard t))
  (let ((fc (fn-cu-s-fc s))
        (round (fn-cu-s-round s))
        (security (fn-cu-s-security s)))
    (cond ((fn-cu-done-p round) (mv s nil))
          ((fn-cu-session-readyp s)
           (mv-let (r2 effects) (fn-cu-step round event)
             (mv (fn-cu-session fc r2 (fn-cu-s-refusal s) security) effects)))
          ((or (equal event '(:tls-up))
               (and (consp event) (equal (car event) :remote)))
           (let* ((evs (fn-cu-session-fc-events s event))
                  (obs (fn-fc-drive fc evs))
                  (fc2 (fn-fc-drive-state fc evs))
                  (effects (fn-cu-obs-effects obs fc security round)))
             (if (fn-pull-pre-okp obs)
                 (mv (fn-cu-session fc2 round (fn-cu-s-refusal s) security) effects)
               (mv-let (r2 fail) (fn-cu-fail round :preamble)
                 (mv (fn-cu-session fc2 r2 (fn-cu-s-refusal s) security)
                     (append effects fail))))))
          (t (mv-let (r2 fail) (fn-cu-fail round :lost)
               (mv (fn-cu-session fc r2 (fn-cu-s-refusal s) security) fail))))))

; -----------------------------------------------------------------------------
; The host's entry points (one value each)

(defun fn-cu-session-begin-pair (plan cursor credential)
  (declare (xargs :guard t))
  (mv-let (s effects) (fn-cu-session-begin plan cursor credential) (list s effects)))

(defun fn-cu-session-step-pair (s event)
  (declare (xargs :guard t))
  (mv-let (s2 effects) (fn-cu-session-step s event) (list s2 effects)))

(defun fn-cu-session-done-p (s)
  (declare (xargs :guard t))
  (fn-cu-done-p (fn-cu-s-round s)))

(defun fn-cu-session-close (s)
  (declare (xargs :guard t))
  (fn-cu-close (fn-cu-s-round s)))

(defun fn-cu-session-close-effects (s)
  (declare (ignore s) (xargs :guard t))
  nil)

; A read bounded like the pull's during the preamble; a batch's lines are
; bounded by `fn-cu-split''s line budget and the peer's quantum.
(defun fn-cu-session-read-limit (s)
  (declare (xargs :guard t))
  (if (fn-cu-session-readyp s) nil *fn-feed-wire-input-max-chunk-octets*))

(defun fn-cu-refusal-name (refusal)
  (declare (xargs :guard t))
  (cond ((symbolp refusal) (string-downcase (symbol-name refusal)))
        (t "other")))

(defun fn-cu-count-words (counts)
  (declare (xargs :guard t))
  (let ((c (if (and (true-listp counts) (equal (len counts) 3)) counts '(0 0 0))))
    (append (fn-record-string-octets " imported=") (fn-nntp-decimal-field (nfix (nth 0 c)))
            (fn-record-string-octets " duplicate=") (fn-nntp-decimal-field (nfix (nth 1 c)))
            (fn-record-string-octets " refused=") (fn-nntp-decimal-field (nfix (nth 2 c))))))

; The owner log line of a closed round: the peer, how it ended, the cursor's
; position and the peer's end, the local answers of this round, the digest
; chain of every record up to the position, and why a failed round failed.
(defun fn-cu-session-log-line (s)
  (declare (xargs :guard t))
  (let ((r (fn-cu-s-round s)))
    (append (fn-record-string-octets "catch-up peer=")
            (fn-pull-list (fn-cu-r-peer r))
            (fn-record-string-octets
             (if (equal (fn-cu-r-phase r) :done) " round=done" " round=failed"))
            (fn-record-string-octets " position=")
            (fn-nntp-decimal-field (nfix (fn-cu-r-position r)))
            (fn-record-string-octets " end=")
            (fn-nntp-decimal-field (nfix (fn-cu-r-end r)))
            (fn-cu-count-words (fn-cu-r-counts r))
            (fn-record-string-octets " digest=")
            (fn-cu-hex (fn-cu-r-chain r))
            (if (fn-cu-r-refusal r)
                (append (fn-record-string-octets " reason=")
                        (fn-record-string-octets (fn-cu-refusal-name (fn-cu-r-refusal r))))
              nil)
            (fn-record-string-octets
             (cond ((not (fn-cu-session-readyp s)) " at=preamble")
                   ((fn-pull-tls-securityp (fn-cu-s-security s)) " transport=tls")
                   (t " transport=clear"))))))

; -----------------------------------------------------------------------------
; Which peers catch up, from the live configuration
;
; A peer catches up when its group has a positive `catch-up-interval' row
; (seconds; `peer catch-up NAME SECONDS', books/native-admin-peer.lisp) and
; everything a pull needs: the plan IS the pull plan of the same rows with
; that interval, so the transport, the credential policy and the wildmat
; (the peer's inbound accept-groups) are the pull's, decided by the same
; functions.

(defconst *fn-cu-interval-slot* *fn-pcb-catch-up-interval-slot*)

(defun fn-cu-plan-of-rows (name rows)
  (declare (xargs :guard t))
  (let ((seconds (fn-pcb-slot-natural *fn-cu-interval-slot* rows)))
    (if (posp seconds)
        (fn-pull-plan-of-rows
         name
         (cons (fn-cfg-row-make name *fn-pcb-pull-interval-slot* "" seconds)
               (fn-cu-list rows)))
      nil)))

(defun fn-cu-plans-of (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((plan (fn-cu-plan-of-rows (car names)
                                      (fn-cfg-rows-with-key peers (car names)))))
        (if plan
            (cons plan (fn-cu-plans-of (cdr names) peers))
          (fn-cu-plans-of (cdr names) peers)))
    nil))

; KEYSTONE SUBJECT.  The peers this node catches up from
; (host/owner-host.lisp `fn-owner-catchup-plans').
(defun fn-cu-plans (peers)
  (declare (xargs :guard t))
  (fn-cu-plans-of (fn-cfg-peer-names peers) peers))

; -----------------------------------------------------------------------------
; FNCU: the cursor's journal
;
; One record kind in the generic frame grammar of books/frame, `(:cu-cursor
; peer position chain)', framed on disk by the FNFD envelope (a four-octet
; length before each frame).  A journal is the cursors appended in order;
; the open keeps the last complete one and truncates a torn tail.  The file
; is <store>/catch-up/ plus the FNFD filename codec's components for the peer.

(local (in-theory (enable fn-frame-fields-vocabulary
                          fn-frame-octet-vocabulary
                          (:d fn-frame-magicp) (:d fn-frame-spec-for)
                          (:d fn-frame-specp) (:d fn-frame-spec-listp)
                          (:d fn-frame-digestp))))

(defconst *fn-cu-magic* '(70 78 67 85))   ; FNCU
(defconst *fn-cu-max-payload* 1024)
(defconst *fn-cu-kinds* '(:cu-cursor))
(defconst *fn-cu-specs* (list (cons :cu-cursor '(:text :nat :blob))))

(defthm fn-cu-spec-for-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-cu-specs*) :none))
           (fn-frame-spec-listp (fn-frame-spec-for kind *fn-cu-specs*))))

(defun fn-cu-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-cu-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-cu-record-okp)

(defun fn-cu-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cu-record-okp kind values) (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-cu-kinds*)))
      (if (equal code 0)
          :bad
        (let ((payload (fn-frame-fields-octets
                        (fn-frame-spec-for kind *fn-cu-specs*) values)))
          (if (not (fn-cbor-at-mostp payload *fn-cu-max-payload*))
              :bad
            (fn-frame-encode *fn-cu-magic* *fn-frame-version* code
                             payload digest)))))))

(defun fn-cu-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-cu-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-cu-magic*)
                    (equal (fn-frame-result-version frame)
                           *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-cu-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1) *fn-cu-kinds*))
                   (spec (fn-frame-spec-for kind *fn-cu-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (if (not (fn-cu-record-okp
                              kind (fn-frame-parse-value parsed)))
                        (fn-frame-error :fields)
                      (fn-frame-ok *fn-cu-magic* *fn-frame-version*
                                   kind
                                   (fn-frame-parse-value parsed)))))))))))))

(defthm fn-cu-encode-frame-guard
  (implies (fn-cu-record-okp kind values)
           (and (fn-frame-spec-listp (fn-frame-spec-for kind *fn-cu-specs*))
                (fn-frame-values-okp (fn-frame-spec-for kind *fn-cu-specs*)
                                     values)
                (fn-cbor-octet-listp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-cu-specs*) values))
                (fn-frame-magicp *fn-cu-magic*)
                (fn-cbor-octetp *fn-frame-version*)
                (fn-cbor-octetp (fn-frame-enum-index kind *fn-cu-kinds*))))
  :rule-classes nil)

(verify-guards fn-cu-encode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cu-encode-frame-guard)))))

(defthm fn-cu-decode-frame-guard
  (implies (fn-frame-result-okp
            (fn-frame-decode octets digest *fn-cu-max-payload*))
           (fn-cbor-octet-listp
            (fn-frame-result-payload
             (fn-frame-decode octets digest *fn-cu-max-payload*))))
  :rule-classes nil)

(verify-guards fn-cu-decode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-cu-decode-frame-guard)))))

; KEYSTONE (the value direction for FNCU).  Every cursor record the host
; writes decodes back to the kind and values it started from.
(defthm fn-cu-decode-of-encode
  (implies (and (fn-cu-record-okp kind values)
                (fn-frame-digestp digest)
                (not (equal (fn-cu-encode kind values digest) :bad)))
           (equal (fn-cu-decode (fn-cu-encode kind values digest) digest)
                  (fn-frame-ok *fn-cu-magic* *fn-frame-version* kind values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cu-encode fn-cu-decode
                            fn-frame-fields-parse-of-octets
                            fn-frame-item-of-enum-index
                            fn-frame-enum-index-of-item
                            fn-frame-inputp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

(defun fn-cu-cursor-frame (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cu-cursorp c))
      nil
    (let ((unsealed (fn-cu-encode :cu-cursor
                                  (list (fn-cu-cursor-peer c)
                                        (fn-cu-cursor-position c)
                                        (fn-cu-cursor-chain c))
                                  *fn-pull-zero-digest*)))
      (if (not (fn-cbor-octet-listp unsealed))
          nil
        (let ((prefix (fn-frame-protected-prefix unsealed)))
          (append (fn-pull-list prefix) (fn-frame-trailer prefix)))))))

(verify-guards fn-cu-cursor-frame)

(defun fn-cu-journal-open-frame (frame)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp frame))
      (fn-frame-error :octets)
    (fn-cu-decode frame (fn-frame-trailer (fn-frame-protected-prefix frame)))))

(verify-guards fn-cu-journal-open-frame)

; KEYSTONE SUBJECT.  The octets one cursor append writes
; (host/native/pull-service.lisp, the catch-up journal's append): the wrapped
; frame, or :bad (never written).
(defun fn-cu-cursor-envelope (c)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-cu-cursor-frame c)))
    (if (not (and (fn-cbor-octet-listp frame)
                  (consp frame)
                  (<= (len frame) *fn-feed-journal-frame-max*)
                  (fn-frame-result-okp (fn-cu-journal-open-frame frame))))
        :bad
      (append (fn-cbor-u32-bytes (len frame)) frame))))

(verify-guards fn-cu-cursor-envelope)

(defun fn-cu-journal-prefix-size ()
  (declare (xargs :guard t))
  *fn-feed-journal-prefix-size*)

; KEYSTONE SUBJECT.  One bounded read of an FNCU file at open: (status
; safe-offset record).  The prefix plan is FNFD's; the safe offset advances
; only over a complete verified cursor frame of this peer, and is the
; truncate authority, so a torn final append is repaired to the previous
; cursor.  RECORD is `(peer position chain)'.
(defun fn-cu-journal-scan (peer prefix frame offset)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plan (fn-feed-journal-prefix prefix))
        (offset (nfix offset)))
    (cond ((equal plan :end) (list :end offset nil))
          ((equal plan :repair) (list :repair offset nil))
          ((not (natp plan)) (list :invalid offset nil))
          ((< (len frame) plan) (list :repair offset nil))
          ((not (equal (len frame) plan)) (list :invalid offset nil))
          (t (let* ((decoded (fn-cu-journal-open-frame frame))
                    (v (fn-frame-result-payload decoded)))
               (if (and (fn-frame-result-okp decoded)
                        (equal (fn-frame-result-kind decoded) :cu-cursor)
                        (true-listp v) (equal (len v) 3)
                        (equal (car v) peer)
                        (fn-cu-cursorp v))
                   (list :next (+ offset *fn-feed-journal-prefix-size* plan) v)
                 (list :invalid offset nil)))))))

(verify-guards fn-cu-journal-scan)

; KEYSTONE SUBJECT.  The cursor the open recovers from the scanned records,
; oldest first: the last one of this peer, else C.
(defun fn-cu-records-replay (c records)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-cu-records-replay (if (and (fn-cu-cursorp (car records))
                                     (equal (fn-cu-cursor-peer (car records))
                                            (fn-cu-cursor-peer c)))
                                (car records)
                              c)
                            (cdr records))
    c))

; -----------------------------------------------------------------------------
; Keystones

(defthm fn-cu-fail-facts
  (and (equal (fn-cu-r-phase (mv-nth 0 (fn-cu-fail r reason))) :failed)
       (equal (fn-cu-r-refusal (mv-nth 0 (fn-cu-fail r reason))) reason)
       (equal (fn-cu-r-position (mv-nth 0 (fn-cu-fail r reason))) (fn-cu-r-position r))
       (equal (fn-cu-r-chain (mv-nth 0 (fn-cu-fail r reason))) (fn-cu-r-chain r))
       (equal (mv-nth 1 (fn-cu-fail r reason)) (list (list :close)))))

; The replay of an append-only journal of cursors is the last one.
(defun fn-cu-last-cursor (c cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (fn-cu-last-cursor (car cursors) (cdr cursors))
    c))

(defun fn-cu-same-peer-cursorsp (peer cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (and (fn-cu-cursorp (car cursors))
           (equal (fn-cu-cursor-peer (car cursors)) peer)
           (fn-cu-same-peer-cursorsp peer (cdr cursors)))
    t))

; KEYSTONE (the FNCU replay).  The records the open scans back from a
; journal of this peer's cursor appends fold to the last one appended.
(defthm fn-cu-records-replay-is-the-last-cursor
  (implies (fn-cu-same-peer-cursorsp (fn-cu-cursor-peer c) cursors)
           (equal (fn-cu-records-replay c cursors)
                  (fn-cu-last-cursor c cursors))))

(local
 (defthm fn-cu-cursor-peer-of-begin
   (equal (fn-cu-r-peer (fn-cu-begin cursor wildmat)) (fn-cu-cursor-peer cursor))))

; KEYSTONE (resumable).  A round begun from the recovered cursor asks the
; peer, as soon as its preamble is ready, from exactly that cursor's
; position and chain: a cut mid catch-up resumes at the last journaled
; batch boundary.
(defthm fn-cu-resume-asks-from-the-journaled-cursor
  (implies (fn-cu-same-peer-cursorsp (fn-cu-cursor-peer c) cursors)
           (let ((cursor (fn-cu-records-replay c cursors)))
             (equal (fn-cu-request (fn-cu-begin cursor wildmat))
                    (fn-cu-command-line wildmat
                                        (fn-cu-cursor-position
                                         (fn-cu-last-cursor c cursors))
                                        (fn-cu-cursor-chain
                                         (fn-cu-last-cursor c cursors))))))
  :hints (("Goal" :in-theory (e/d (fn-cu-begin fn-cu-request) (fn-cu-command-line)))))

; -----------------------------------------------------------------------------
; The round's invariant: an offered batch is a verified batch

(defun fn-cu-offeringp (phase)
  (declare (xargs :guard t))
  (and (member-equal phase '(:local-greeting :offer :forward)) t))

(defun fn-cu-suffixp (x y)
  (declare (xargs :guard t))
  (if (equal x y)
      t
    (if (consp y) (fn-cu-suffixp x (cdr y)) nil)))

; While the round offers a batch, the batch it holds chains from the
; committed chain to the peer's claim, and what remains to offer is a suffix
; of it; while it waits for a batch, nothing remains to offer.
(defun fn-cu-verifiedp (r)
  (declare (xargs :guard t))
  (cond ((fn-cu-offeringp (fn-cu-r-phase r))
         (and (equal (fn-cu-records-chain (fn-cu-r-chain r) (fn-cu-r-records r))
                     (fn-cu-batch-claim (fn-cu-r-batch r)))
              (fn-cu-suffixp (fn-cu-r-todo r) (fn-cu-r-records r))))
        ((equal (fn-cu-r-phase r) :reply) (not (consp (fn-cu-r-todo r))))
        (t t)))

(defthm fn-cu-verifiedp-of-begin
  (fn-cu-verifiedp (fn-cu-begin cursor wildmat))
  :hints (("Goal" :in-theory (enable fn-cu-begin))))

(local
 (defthm fn-cu-suffixp-cdr
   (implies (and (fn-cu-suffixp x y) (consp x))
            (fn-cu-suffixp (cdr x) y))))

(local
 (defthm fn-cu-verifiedp-of-fail
   (fn-cu-verifiedp (car (fn-cu-fail r reason)))))

(local
 (defthm fn-cu-verifiedp-of-next
   (implies (and (equal (fn-cu-records-chain (fn-cu-r-chain r) (fn-cu-r-records r))
                        (fn-cu-batch-claim (fn-cu-r-batch r)))
                 (fn-cu-suffixp (fn-cu-r-todo r) (fn-cu-r-records r)))
            (fn-cu-verifiedp (car (fn-cu-next r))))
   :hints (("Goal" :in-theory (disable fn-cu-records-chain fn-cu-request
                                       fn-cu-ihave fn-cu-round-cursor)))))

(local
 (defthm fn-cu-verifiedp-of-on-end
   (fn-cu-verifiedp (car (fn-cu-on-end r)))
   :hints (("Goal" :in-theory (disable fn-cu-records-chain fn-cu-next fn-cu-fail)))))

(local
 (defthm fn-cu-on-line-continues-in-reply
   (implies (and (equal (fn-cu-r-phase r) :reply)
                 (mv-nth 2 (fn-cu-on-line r line)))
            (and (equal (fn-cu-r-phase (car (fn-cu-on-line r line))) :reply)
                 (equal (fn-cu-r-todo (car (fn-cu-on-line r line)))
                        (fn-cu-r-todo r))
                 (equal (mv-nth 1 (fn-cu-on-line r line)) nil)))
   :hints (("Goal" :in-theory (disable fn-cu-on-end fn-cu-fail fn-cu-parse-status
                                       fn-cu-parse-header fn-pull-code fn-cu-unstuff
                                       fn-cu-list fn-pull-at revappend-removal
                                       fn-cu-records-chain fn-cu-suffixp)))))

(local
 (defthm fn-cu-verifiedp-of-on-line
   (implies (and (equal (fn-cu-r-phase r) :reply)
                 (not (consp (fn-cu-r-todo r))))
            (fn-cu-verifiedp (car (fn-cu-on-line r line))))
   :hints (("Goal" :in-theory (disable fn-cu-on-end fn-cu-fail fn-cu-parse-status
                                       fn-cu-parse-header fn-pull-code fn-cu-unstuff
                                       fn-cu-list fn-pull-at revappend-removal
                                       fn-cu-records-chain fn-cu-suffixp)))))

(local
 (defthm fn-cu-verifiedp-of-drain
   (implies (and (equal (fn-cu-r-phase r) :reply)
                 (not (consp (fn-cu-r-todo r))))
            (fn-cu-verifiedp (car (fn-cu-drain r fuel))))
   :hints (("Goal" :in-theory (disable fn-cu-on-line fn-cu-fail fn-cu-split
                                       fn-cu-verifiedp)
            :induct (fn-cu-drain r fuel)
            :expand ((fn-cu-drain r fuel)
                     (:free (x) (fn-cu-verifiedp x)))))))

; KEYSTONE (an offered batch is a verified batch).  The host's step keeps the
; invariant: no record reaches the local node from a batch whose digest
; chain, recomputed over what arrived, differs from the peer's claim.
(defthm fn-cu-step-keeps-offers-verified
  (implies (fn-cu-verifiedp r)
           (fn-cu-verifiedp (car (fn-cu-step r event))))
  :hints (("Goal" :in-theory (disable fn-cu-drain fn-cu-next fn-cu-fail
                                      fn-pull-local-code fn-cu-records-chain
                                      fn-cu-body fn-cu-verifiedp)
           :expand ((fn-cu-verifiedp r)
                    (:free (phase peer wildmat position chain buf batch records
                                  cur running todo counts refusal localp end)
                           (fn-cu-verifiedp
                            (fn-cu-round phase peer wildmat position chain buf
                                         batch records cur running todo counts
                                         refusal localp end)))))))

; KEYSTONE (a digest mismatch is refused by name).  A batch whose records do
; not chain to the peer's claim ends the round :failed with the refusal
; :digest-mismatch; nothing is offered, nothing journaled, the cursor stays.
(defthm fn-cu-on-end-refuses-a-digest-mismatch
  (implies (not (equal (fn-cu-records-chain
                        (fn-cu-r-chain r)
                        (revappend (fn-cu-list (fn-cu-r-records r)) nil))
                       (fn-cu-batch-claim (fn-cu-r-batch r))))
           (let ((out (fn-cu-on-end r)))
             (and (equal (fn-cu-r-phase (mv-nth 0 out)) :failed)
                  (equal (mv-nth 1 out) (list (list :close)))
                  (equal (fn-cu-round-cursor (mv-nth 0 out)) (fn-cu-round-cursor r)))))
  :hints (("Goal" :in-theory (disable fn-cu-records-chain fn-cu-next fn-cu-list
                                      revappend-removal fn-pull-at))))

; -----------------------------------------------------------------------------
; What a step sends: offers only through the local verdict, journals only a
; closed batch

; Every effect in EFFECTS that reaches the local node is the IHAVE of the
; record the round R2 then waits on, and every journal record is R2's cursor
; with nothing of its batch left to offer.
(defun fn-cu-out-okp (effects r2)
  (declare (xargs :guard t))
  (if (consp effects)
      (and (let ((e (car effects)))
             (cond ((and (consp e) (equal (car e) :local))
                    (and (equal (fn-cu-r-phase r2) :offer)
                         (consp (fn-cu-r-todo r2))
                         (equal (cdr e) (fn-cu-ihave (car (fn-cu-r-todo r2))))))
                   ((and (consp e) (equal (car e) :journal))
                    (and (equal (cdr e) (fn-cu-round-cursor r2))
                         (not (consp (fn-cu-r-todo r2)))))
                   (t t)))
           (fn-cu-out-okp (cdr effects) r2))
    t))

(local
 (defthm fn-cu-out-okp-of-plain
   (and (fn-cu-out-okp nil r2)
        (fn-cu-out-okp '((:close)) r2)
        (fn-cu-out-okp '((:open-local)) r2))))

(local
 (defthm fn-cu-out-okp-of-fail
   (fn-cu-out-okp (mv-nth 1 (fn-cu-fail r reason)) (car (fn-cu-fail r reason)))))

(local
 (defthm fn-cu-out-okp-of-next
   (fn-cu-out-okp (mv-nth 1 (fn-cu-next r)) (car (fn-cu-next r)))
   :hints (("Goal" :in-theory (disable fn-cu-ihave fn-cu-request fn-cu-quit)))))

(local
 (defthm fn-cu-out-okp-of-on-end
   (fn-cu-out-okp (mv-nth 1 (fn-cu-on-end r)) (car (fn-cu-on-end r)))
   :hints (("Goal" :in-theory (disable fn-cu-next fn-cu-fail fn-cu-records-chain
                                       fn-cu-out-okp)))))

(local
 (defthm fn-cu-out-okp-of-on-line
   (fn-cu-out-okp (mv-nth 1 (fn-cu-on-line r line)) (car (fn-cu-on-line r line)))
   :hints (("Goal" :in-theory (disable fn-cu-on-end fn-cu-fail fn-cu-parse-status
                                       fn-cu-parse-header fn-pull-code fn-cu-out-okp
                                       fn-cu-unstuff fn-cu-list fn-pull-at
                                       revappend-removal)))))

(local
 (defthm fn-cu-on-line-continuing-sends-nothing
   (implies (mv-nth 2 (fn-cu-on-line r line))
            (equal (mv-nth 1 (fn-cu-on-line r line)) nil))
   :hints (("Goal" :in-theory (disable fn-cu-on-end fn-cu-fail fn-cu-parse-status
                                       fn-cu-parse-header fn-pull-code fn-cu-unstuff
                                       fn-cu-list fn-pull-at revappend-removal
                                       fn-cu-records-chain fn-cu-suffixp)))))

(local
 (defthm fn-cu-out-okp-of-drain
   (fn-cu-out-okp (mv-nth 1 (fn-cu-drain r fuel)) (car (fn-cu-drain r fuel)))
   :hints (("Goal" :in-theory (disable fn-cu-on-line fn-cu-fail fn-cu-split
                                       fn-cu-out-okp)
            :induct (fn-cu-drain r fuel)
            :expand ((fn-cu-drain r fuel))))))

; KEYSTONE (catch-up installs only through the local verdict).  Every effect
; of the host's step that reaches the local node is either the IHAVE of the
; record the round then waits on, or -- only on the local node's 335 to that
; IHAVE, in phase :offer -- that record's body; and every journal record is
; the round's committed cursor with nothing of its batch left to offer.
; Catch-up never installs a record itself: an article is stored only by the
; local node's acceptance of an IHAVE, under its own verdict.
(defthm fn-cu-step-installs-only-through-the-verdict
  (let* ((out (fn-cu-step r event)))
    (or (fn-cu-out-okp (mv-nth 1 out) (car out))
        (and (equal (fn-cu-r-phase r) :offer)
             (consp (fn-cu-r-todo r))
             (consp event)
             (equal (car event) :local)
             (equal (fn-pull-local-code (fn-cu-event-octets event)) 335)
             (equal (mv-nth 1 out)
                    (list (cons :local (fn-cu-body (fn-cu-record-lines
                                                    (car (fn-cu-r-todo r)))))))
             (equal (fn-cu-r-phase (car out)) :forward))))
  :hints (("Goal" :in-theory (disable fn-cu-drain fn-cu-next fn-cu-fail
                                      fn-pull-local-code fn-cu-body fn-cu-out-okp))))
