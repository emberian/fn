; fn: the NEWNEWS pull feed as owner work (PRF-100; RFC 3977 section 7.4).
;
; A node that cannot be dialled (behind NAT) and a server that only answers
; readers (INN's nnrpd) are fed by PULLING: this node dials the peer, asks
; DATE, lists the Message-IDs the peer received since a cursor with NEWNEWS,
; and offers each one to ITSELF on a logical connection of that peer's
; transit role, so each article meets the node's own served IHAVE decision
; exactly as if the peer had pushed it.  Only an article the local node
; wants (335) is fetched with ARTICLE, and its octets are forwarded as the
; IHAVE body.
;
; Everything the round decides is here: which command goes to which side,
; what a reply code means, when the round ends, and whether the cursor moves.
; The host (host/native/pull-service.lisp) moves octets between two sockets
; and the owner and appends the journal records this book hands it.
;
; The cursor.  `(peer since advances pending)': PEER the peer's label
; octets, SINCE the DTN millisecond instant the next NEWNEWS names (nil
; before the first round asked anything), ADVANCES how many rounds moved it,
; PENDING the ids unavailable at the peer with their consecutive counts.  It is persisted
; as an FNPL frame (the generic journal grammar of books/frame, magic "FNPL")
; in <store>/pull/, one file per peer named by the FNFD filename codec, and
; recovered by `fn-pull-replay' over the scanned entries.
;
; The ack-bounded advance.  A round moves the cursor past itself only when
; every Message-ID its NEWNEWS listed drew 235, 435 or 437 from the local
; node: an ack means what it names (review 2026-09-24).  A 436 or a lost
; connection leaves the cursor where the round found it, so the next round
; asks NEWNEWS from the same instant and the peer lists the article again.
;
; Unavailable (PRF-165, PKT-213).  A peer that lists a Message-ID and then
; answers its ARTICLE with 430 (RFC 3977 section 6.2.1.3: no article with
; that message-id) has ANSWERED: the id is recorded in the round's
; `unavailable' list, the local transit connection (inside an IHAVE it cannot
; finish) is reopened, and the round goes on with the ids that remain.  A
; round that ran to its end with every listed id answered or unavailable is
; COMPLETE.  A complete round with an id unavailable fewer than BOUND
; consecutive complete rounds holds the instant (the peer lists the id
; again) and journals the per-id counts in the cursor's PENDING field; once
; every unavailable id has reached BOUND the cursor advances, and each id
; whose count reached BOUND in this round is named in the owner log
; (`dropped=').  BOUND is the peer's `pull-unavailable-rounds' row, else
; `*fn-pull-default-unavailable-rounds*'.  A failed round changes no count.
;
; Durable before the wire.  The only instant a NEWNEWS names is the round's
; cursor, fixed by `fn-pull-begin' for the round's whole life; a fresh cursor
; takes its first instant there and `fn-pull-begin-effects' journals it
; before the round touches the wire.  No step journals or changes the
; cursor, and a close journals exactly the cursor it moves to.  So at every
; crash point the replayed cursor is the in-flight round's
; (`fn-pull-journal-is-the-cursor-at-every-cut'), and recovery asks the same
; NEWNEWS again (`fn-pull-recovery-asks-the-dead-rounds-newnews').
(in-package "ACL2")
(include-book "feed-journal")
(include-book "scheduler-peers")
(include-book "nntp-responses")
(include-book "peer-carriage-rows")
(include-book "peer-config")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Constants.  Each bounds WORK per step (D27), not data.

; RFC 3977 section 3.1: an initial response line is at most 512 octets
; including CRLF.  A NEWNEWS line is one Message-ID (section 3.6: at most 250
; octets).  A remote line longer than this is a protocol error for the round.
(defconst *fn-pull-max-line* 512)

; Local policy for a fresh cursor: the first NEWNEWS asks one day back from
; the peer's own DATE (the epoch is a date some servers read as "no date").
(defconst *fn-pull-first-window-ms* 86400000)

; One second of overlap: an article that arrived in the second of the DATE
; the round read is listed again next round and answered 435, never missed.
(defconst *fn-pull-overlap-ms* 1000)

(defconst *fn-pull-terminal-codes* '(235 435 437))

; RFC 3977 section 6.2.1.3: the peer has no article with that message-id.
(defconst *fn-pull-unavailable-code* 430)

; Local policy (PRF-165), not a data cap: how many consecutive complete
; rounds an id the peer lists but cannot produce holds the cursor when the
; peer record has no `pull-unavailable-rounds' row.  It bounds WORK (the
; re-listing a held instant costs, one interval per round), never what is
; stored; `peer pull NAME SECONDS ROUNDS' sets the peer's own figure.
(defconst *fn-pull-default-unavailable-rounds* 5)

; -----------------------------------------------------------------------------
; Small total helpers

(defun fn-pull-at (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (if (consp x) (car x) nil)
    (fn-pull-at (1- n) (if (consp x) (cdr x) nil))))

(defun fn-pull-octetsp (x)
  (declare (xargs :guard t))
  (fn-cbor-octet-listp x))

(defun fn-pull-digitp (o)
  (declare (xargs :guard t))
  (and (natp o) (<= 48 o) (<= o 57)))

(defun fn-pull-digits-value (xs acc)
  (declare (xargs :guard (natp acc)))
  (if (consp xs)
      (if (fn-pull-digitp (car xs))
          (fn-pull-digits-value (cdr xs) (+ (* 10 acc) (- (car xs) 48)))
        nil)
    acc))

; The reply code of a response line: three digits, then the end of the line
; or a space.  Anything else is no code at all.
(defun fn-pull-code (line)
  (declare (xargs :guard t))
  (if (and (true-listp line)
           (<= 3 (len line))
           (fn-pull-digitp (car line))
           (fn-pull-digitp (cadr line))
           (fn-pull-digitp (caddr line))
           (or (equal (len line) 3) (equal (cadddr line) 32)))
      (+ (* 100 (- (car line) 48)) (* 10 (- (cadr line) 48))
         (- (caddr line) 48))
    nil))

(defthm fn-pull-code-type
  (or (null (fn-pull-code line)) (natp (fn-pull-code line)))
  :rule-classes :type-prescription)

(defun fn-pull-terminal-codep (code)
  (declare (xargs :guard t))
  (and (member-equal code *fn-pull-terminal-codes*) t))

; A NEWNEWS line names one Message-ID: "<", printable US-ASCII, ">", at most
; 250 octets (RFC 3977 section 3.6).
(defun fn-pull-msgid-bodyp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (natp (car xs)) (<= 33 (car xs)) (<= (car xs) 126)
           (fn-pull-msgid-bodyp (cdr xs)))
    (null xs)))

(defun fn-pull-msgidp (xs)
  (declare (xargs :guard t))
  (and (true-listp xs)
       (<= 3 (len xs)) (<= (len xs) 250)
       (equal (car xs) 60)
       (equal (car (last xs)) 62)
       (fn-pull-msgid-bodyp xs)))

(defthm fn-pull-msgidp-octets
  (implies (fn-pull-msgidp xs) (fn-pull-octetsp xs))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)
           :induct (fn-pull-msgid-bodyp xs))))

(defun fn-pull-list (x)
  (declare (xargs :guard t))
  (if (true-listp x) x nil))

(defun fn-pull-crlf () (declare (xargs :guard t)) '(13 10))

(defun fn-pull-command (words)
  ; The octets of WORDS joined by single spaces, then CRLF.
  (declare (xargs :guard (true-listp words)))
  (if (consp words)
      (append (if (true-listp (car words)) (car words) nil)
              (if (consp (cdr words))
                  (cons 32 (fn-pull-command (cdr words)))
                (fn-pull-crlf)))
    (fn-pull-crlf)))

; -----------------------------------------------------------------------------
; Line framing of the remote side.  At most *fn-pull-max-line* octets are
; examined per line; the scan is tail-recursive with an accumulator.

(defun fn-pull-split-aux (buf acc budget)
  (declare (xargs :guard (and (true-listp acc) (natp budget))
                  :measure (nfix budget)))
  (cond ((zp budget) (mv :long nil nil))
        ((atom buf) (mv :need nil nil))
        ((and (equal (car buf) 13) (consp (cdr buf)) (equal (cadr buf) 10))
         (mv :line (revappend acc nil) (cddr buf)))
        (t (fn-pull-split-aux (cdr buf) (cons (car buf) acc) (1- budget)))))

(defun fn-pull-split (buf)
  (declare (xargs :guard t))
  (fn-pull-split-aux buf nil *fn-pull-max-line*))

(defthm fn-pull-split-aux-rest-shorter
  (implies (equal (mv-nth 0 (fn-pull-split-aux buf acc budget)) :line)
           (< (len (mv-nth 2 (fn-pull-split-aux buf acc budget))) (len buf)))
  :rule-classes :linear)

(defthm fn-pull-split-aux-line-true-listp
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (fn-pull-split-aux buf acc budget)))))

; -----------------------------------------------------------------------------
; DATE and the NEWNEWS instant

; "111 yyyymmddhhmmss" (RFC 3977 section 7.1) as DTN milliseconds, or nil.
(defun fn-pull-date-ms (line)
  (declare (xargs :guard t))
  (if (and (true-listp line)
           (equal (len line) 18)
           (equal (fn-pull-code line) 111))
      (let* ((d (nthcdr 4 line))
             (year (fn-pull-digits-value (take 4 d) 0))
             (month (fn-pull-digits-value (take 2 (nthcdr 4 d)) 0))
             (day (fn-pull-digits-value (take 2 (nthcdr 6 d)) 0))
             (hour (fn-pull-digits-value (take 2 (nthcdr 8 d)) 0))
             (minute (fn-pull-digits-value (take 2 (nthcdr 10 d)) 0))
             (second (fn-pull-digits-value (take 2 (nthcdr 12 d)) 0)))
        (if (and (natp year) (natp month) (natp day) (natp hour)
                 (natp minute) (natp second)
                 (<= 2000 year) (<= 1 month) (<= month 12)
                 (<= 1 day) (<= day 31) (< hour 24) (< minute 60)
                 (< second 61))
            (fn-nntp-civil-dtn-ms year month day hour minute second)
          nil))
    nil))

; "yyyymmdd" and "hhmmss" of a DTN millisecond instant (section 7.3.2).
(defun fn-pull-date-words (ms)
  (declare (xargs :guard t))
  (let ((civil (fn-nntp-dtn-civil ms)))
    (list (append (fn-nntp-pad4 (fn-nntp-civil-year civil))
                  (fn-nntp-pad2 (fn-nntp-civil-month civil))
                  (fn-nntp-pad2 (fn-nntp-civil-day civil)))
          (append (fn-nntp-pad2 (fn-nntp-civil-hour civil))
                  (fn-nntp-pad2 (fn-nntp-civil-minute civil))
                  (fn-nntp-pad2 (fn-nntp-civil-second civil))))))

; The one NEWNEWS a round sends, a function of the wildmat and the cursor's
; instant and nothing else.
(defun fn-pull-newnews-octets (wildmat since)
  (declare (xargs :guard t))
  (let ((words (fn-pull-date-words since)))
    (fn-pull-command
     (list (fn-record-string-octets "NEWNEWS")
           (if (true-listp wildmat) wildmat nil)
           (car words) (cadr words)
           (fn-record-string-octets "GMT")))))

(defun fn-pull-back (ms by)
  (declare (xargs :guard t))
  (nfix (- (nfix ms) (nfix by))))

; -----------------------------------------------------------------------------
; The cursor

(defun fn-pull-cursor (peer since advances pending)
  (declare (xargs :guard t))
  (list peer since advances pending))

(defun fn-pull-cursor-peer (c) (declare (xargs :guard t)) (fn-pull-at 0 c))
(defun fn-pull-cursor-since (c) (declare (xargs :guard t)) (fn-pull-at 1 c))
(defun fn-pull-cursor-advances (c) (declare (xargs :guard t)) (fn-pull-at 2 c))
(defun fn-pull-cursor-pending (c) (declare (xargs :guard t)) (fn-pull-at 3 c))

(defun fn-pull-fresh-cursor (peer)
  (declare (xargs :guard t))
  (fn-pull-cursor peer nil 0 nil))

; PENDING: (id . count) pairs, each id a Message-ID, each count positive.
(defun fn-pull-pendingp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (fn-pull-msgidp (car (car x)))
           (posp (cdr (car x)))
           (fn-pull-pendingp (cdr x)))
    (null x)))

; A journaled cursor: every field present, SINCE an instant.
(defun fn-pull-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 4)
       (fn-feed-namep (fn-pull-cursor-peer c))
       (natp (fn-pull-cursor-since c))
       (natp (fn-pull-cursor-advances c))
       (fn-pull-pendingp (fn-pull-cursor-pending c))))


; A cursor the owner may begin a round with: journaled, or fresh (no instant).
(defun fn-pull-startable-cursorp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 4)
       (fn-feed-namep (fn-pull-cursor-peer c))
       (or (null (fn-pull-cursor-since c)) (natp (fn-pull-cursor-since c)))
       (natp (fn-pull-cursor-advances c))
       (fn-pull-pendingp (fn-pull-cursor-pending c))))

; -----------------------------------------------------------------------------
; The round
;
; (phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)
; PEER, WILDMAT, SINCE, ADVANCES, PENDING and BOUND are fixed at
; `fn-pull-begin' and no step changes them: the round asks with one cursor
; for its whole life.  UNAVAILABLE collects the listed ids the peer answered
; 430 (PRF-165).

(defun fn-pull-round (phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)
  (declare (xargs :guard t))
  (list phase peer wildmat since advances pending bound started listed todo answers unavailable buf current))

(defun fn-pull-r-phase (r) (declare (xargs :guard t)) (fn-pull-at 0 r))
(defun fn-pull-r-peer (r) (declare (xargs :guard t)) (fn-pull-at 1 r))
(defun fn-pull-r-wildmat (r) (declare (xargs :guard t)) (fn-pull-at 2 r))
(defun fn-pull-r-since (r) (declare (xargs :guard t)) (fn-pull-at 3 r))
(defun fn-pull-r-advances (r) (declare (xargs :guard t)) (fn-pull-at 4 r))
(defun fn-pull-r-pending (r) (declare (xargs :guard t)) (fn-pull-at 5 r))
(defun fn-pull-r-bound (r) (declare (xargs :guard t)) (fn-pull-at 6 r))
(defun fn-pull-r-started (r) (declare (xargs :guard t)) (fn-pull-at 7 r))
(defun fn-pull-r-listed (r) (declare (xargs :guard t)) (fn-pull-at 8 r))
(defun fn-pull-r-todo (r) (declare (xargs :guard t)) (fn-pull-at 9 r))
(defun fn-pull-r-answers (r) (declare (xargs :guard t)) (fn-pull-at 10 r))
(defun fn-pull-r-unavailable (r) (declare (xargs :guard t)) (fn-pull-at 11 r))
(defun fn-pull-r-buf (r) (declare (xargs :guard t)) (fn-pull-at 12 r))
(defun fn-pull-r-current (r) (declare (xargs :guard t)) (fn-pull-at 13 r))

(defthm fn-pull-r-of-round
  (and
       (equal (fn-pull-r-phase (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) phase)
       (equal (fn-pull-r-peer (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) peer)
       (equal (fn-pull-r-wildmat (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) wildmat)
       (equal (fn-pull-r-since (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) since)
       (equal (fn-pull-r-advances (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) advances)
       (equal (fn-pull-r-pending (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) pending)
       (equal (fn-pull-r-bound (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) bound)
       (equal (fn-pull-r-started (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) started)
       (equal (fn-pull-r-listed (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) listed)
       (equal (fn-pull-r-todo (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) todo)
       (equal (fn-pull-r-answers (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) answers)
       (equal (fn-pull-r-unavailable (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) unavailable)
       (equal (fn-pull-r-buf (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) buf)
       (equal (fn-pull-r-current (fn-pull-round phase peer wildmat since advances pending bound started listed todo answers unavailable buf current)) current)))

; A round is read through its accessors and built by `fn-pull-round'; the
; list underneath stays closed in every proof below.
(in-theory (disable fn-pull-round fn-pull-r-phase fn-pull-r-peer fn-pull-r-wildmat fn-pull-r-since fn-pull-r-advances fn-pull-r-pending fn-pull-r-bound fn-pull-r-started fn-pull-r-listed fn-pull-r-todo fn-pull-r-answers fn-pull-r-unavailable fn-pull-r-buf fn-pull-r-current))

; The cursor a round asks with: what the journal holds while it runs.
(defun fn-pull-round-cursor (r)
  (declare (xargs :guard t))
  (fn-pull-cursor (fn-pull-r-peer r) (fn-pull-r-since r) (fn-pull-r-advances r)
                  (fn-pull-r-pending r)))

; Field updates.  Each names the fields it changes; the cursor's four, the
; bound and the wildmat are not among the keywords.
(defmacro fn-pull-with (r &key (phase 'nil phase-p)
                          (started 'nil started-p) (listed 'nil listed-p)
                          (todo 'nil todo-p) (answers 'nil answers-p)
                          (unavailable 'nil unavailable-p)
                          (buf 'nil buf-p) (current 'nil current-p))
  `(fn-pull-round ,(if phase-p phase `(fn-pull-r-phase ,r))
                  (fn-pull-r-peer ,r) (fn-pull-r-wildmat ,r)
                  (fn-pull-r-since ,r) (fn-pull-r-advances ,r)
                  (fn-pull-r-pending ,r) (fn-pull-r-bound ,r)
                  ,(if started-p started `(fn-pull-r-started ,r))
                  ,(if listed-p listed `(fn-pull-r-listed ,r))
                  ,(if todo-p todo `(fn-pull-r-todo ,r))
                  ,(if answers-p answers `(fn-pull-r-answers ,r))
                  ,(if unavailable-p unavailable `(fn-pull-r-unavailable ,r))
                  ,(if buf-p buf `(fn-pull-r-buf ,r))
                  ,(if current-p current `(fn-pull-r-current ,r))))

; KEYSTONE SUBJECT.  Beginning a round (host/native/pull-service.lisp
; `fnn-pull-begin').  NOW is the owner's wall reading in DTN milliseconds.
; A fresh cursor takes its first instant here, one window before NOW, and
; `fn-pull-begin-effects' journals it before the round touches the wire.
; BOUND is the plan's (`fn-pull-plan-bound').
(defun fn-pull-begin-since (cursor now)
  (declare (xargs :guard t))
  (if (natp (fn-pull-cursor-since cursor))
      (fn-pull-cursor-since cursor)
    (fn-pull-back now *fn-pull-first-window-ms*)))

(defun fn-pull-begin (cursor wildmat now bound)
  (declare (xargs :guard t))
  (fn-pull-round :greeting (fn-pull-cursor-peer cursor) wildmat
                 (fn-pull-begin-since cursor now)
                 (nfix (fn-pull-cursor-advances cursor))
                 (fn-pull-cursor-pending cursor) bound
                 nil nil nil nil nil nil nil))

; The round a session enters once its preamble (the feed-connection
; machine's greeting, STARTTLS, TLS and AUTHINFO) has reached :ready
; (books/peer-pull-session.lisp `fn-pull-session-begin').  It differs from
; `fn-pull-begin' in the phase alone: the DATE is outstanding.  Its cursor
; fields are `fn-pull-begin''s (`fn-pull-begin-ready-cursor-fields'), so
; the cut theorem below transfers to it unchanged.
(defun fn-pull-begin-ready (cursor wildmat now bound)
  (declare (xargs :guard t))
  (fn-pull-with (fn-pull-begin cursor wildmat now bound) :phase :date))

(defthm fn-pull-begin-ready-cursor-fields
  (and (equal (fn-pull-r-phase (fn-pull-begin-ready cursor wildmat now bound)) :date)
       (equal (fn-pull-r-peer (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-r-peer (fn-pull-begin cursor wildmat now bound)))
       (equal (fn-pull-r-wildmat (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-r-wildmat (fn-pull-begin cursor wildmat now bound)))
       (equal (fn-pull-r-since (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-r-since (fn-pull-begin cursor wildmat now bound)))
       (equal (fn-pull-r-advances (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-r-advances (fn-pull-begin cursor wildmat now bound)))
       (equal (fn-pull-r-bound (fn-pull-begin-ready cursor wildmat now bound))
              bound)
       (equal (fn-pull-r-pending (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-r-pending (fn-pull-begin cursor wildmat now bound)))
       (equal (fn-pull-round-cursor (fn-pull-begin-ready cursor wildmat now bound))
              (fn-pull-round-cursor (fn-pull-begin cursor wildmat now bound)))))

; Effects, in the order the host performs them:
;   (:journal . cursor)   append the FNPL record, durably, before anything after it
;   (:remote . octets)    write to the peer
;   (:open-local)         open the logical transit connection of this peer
;   (:local . octets)     hand to that connection (fnn-owner-handle-chunk)
;   (:reopen-local)       close that connection and open a fresh one (PRF-165)
;   (:close)              the round is over: close both sides
(defun fn-pull-begin-effects (cursor now)
  (declare (xargs :guard t))
  (if (natp (fn-pull-cursor-since cursor))
      nil
    (list (cons :journal
                (fn-pull-cursor (fn-pull-cursor-peer cursor)
                                (fn-pull-begin-since cursor now)
                                (nfix (fn-pull-cursor-advances cursor))
                                (fn-pull-cursor-pending cursor))))))

(defun fn-pull-fail (r)
  (declare (xargs :guard t))
  (mv (fn-pull-with r :phase :failed :buf nil) (list (list :close))))

; The one DATE command a round sends (RFC 3977 section 7.1): after the
; peer's greeting, or, for a session whose preamble ran first, when the
; feed-connection machine reports :ready (books/peer-pull-session.lisp).
(defun fn-pull-date-command ()
  (declare (xargs :guard t))
  (fn-pull-command (list (fn-record-string-octets "DATE"))))

(defun fn-pull-quit ()
  (declare (xargs :guard t))
  (fn-pull-command (list (fn-record-string-octets "QUIT"))))

; The next listed article, or the end of the round.
(defun fn-pull-next (r)
  (declare (xargs :guard t))
  (let ((todo (fn-pull-r-todo r)))
    (if (consp todo)
        (mv (fn-pull-with r :phase :offer :todo (cdr todo) :current (car todo))
            (list (cons :local
                        (fn-pull-command
                         (list (fn-record-string-octets "IHAVE")
                               (if (true-listp (car todo)) (car todo) nil))))))
      (mv (fn-pull-with r :phase :done :current nil)
          (list (cons :remote (fn-pull-quit)) (list :close))))))

(defun fn-pull-record-answer (r code)
  (declare (xargs :guard t))
  (fn-pull-with r :answers (cons (cons (fn-pull-r-current r) code)
                                 (fn-pull-r-answers r))))

; One remote line in a line phase: (mv round effects continuep).
(defun fn-pull-on-line (r line)
  (declare (xargs :guard (true-listp line)))
  (let ((phase (fn-pull-r-phase r))
        (code (fn-pull-code line)))
    (cond
     ((equal phase :greeting)
      (if (member-equal code '(200 201))
          (mv (fn-pull-with r :phase :date)
              (list (cons :remote (fn-pull-date-command)))
              t)
        (mv-let (f e) (fn-pull-fail r) (mv f e nil))))
     ((equal phase :date)
      (let ((started (fn-pull-date-ms line)))
        (if (not (natp started))
            (mv-let (f e) (fn-pull-fail r) (mv f e nil))
          (mv (fn-pull-with r :phase :newnews :started started)
              (list (cons :remote (fn-pull-newnews-octets
                                   (fn-pull-r-wildmat r) (fn-pull-r-since r))))
              t))))
     ((equal phase :newnews)
      (if (equal code 230)
          (mv (fn-pull-with r :phase :list) nil t)
        (mv-let (f e) (fn-pull-fail r) (mv f e nil))))
     ((equal phase :list)
      (cond ((equal line '(46))
             (cond ((consp (fn-pull-r-buf r))
                    ; Nothing may follow the list: one command is outstanding.
                    (mv-let (f e) (fn-pull-fail r) (mv f e nil)))
                   ((consp (fn-pull-r-listed r))
                    (mv (fn-pull-with r :phase :local-greeting
                                      :todo (fn-pull-r-listed r))
                        (list (list :open-local))
                        nil))
                   (t (mv (fn-pull-with r :phase :done)
                          (list (cons :remote (fn-pull-quit)) (list :close))
                          nil))))
            ((fn-pull-msgidp line)
             (let ((listed (fn-pull-list (fn-pull-r-listed r))))
               (mv (fn-pull-with r :listed
                                 (if (member-equal line listed)
                                     listed
                                   (append listed (list line))))
                   nil t)))
            (t (mv-let (f e) (fn-pull-fail r) (mv f e nil)))))
     ((equal phase :article)
      (if (equal code 220)
          ; The rest of the buffer is the article's first octets, already in
          ; IHAVE's wire form (dot-stuffed, ending in CRLF.CRLF).
          (mv (fn-pull-with r :phase :forward :buf nil)
              (if (consp (fn-pull-r-buf r))
                  (list (cons :local (fn-pull-r-buf r)))
                nil)
              nil)
        (if (and (equal code *fn-pull-unavailable-code*)
                 (not (consp (fn-pull-r-buf r))))
            ; PRF-165: the peer has no such article.  That is its answer for
            ; the id; the local node is inside an IHAVE it cannot finish, so
            ; its transit connection is reopened and the round goes on from
            ; the fresh greeting with the ids that remain.
            (mv (fn-pull-with r :phase :local-greeting :buf nil
                              :unavailable
                              (cons (fn-pull-r-current r)
                                    (fn-pull-list (fn-pull-r-unavailable r))))
                (list (list :reopen-local))
                nil)
          ; Any other reply: the round ends with this article unanswered.
          (mv-let (f e) (fn-pull-fail r) (mv f e nil)))))
     (t (mv-let (f e) (fn-pull-fail r) (mv f e nil))))))

(defun fn-pull-line-phasep (phase)
  (declare (xargs :guard t))
  (and (member-equal phase '(:greeting :date :newnews :list :article)) t))

; Frame and handle every complete line the buffer holds, at most FUEL of them.
(defun fn-pull-drain (r fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (not (fn-pull-line-phasep (fn-pull-r-phase r))))
      (mv r nil)
    (mv-let (status line rest) (fn-pull-split (fn-pull-r-buf r))
      (cond ((equal status :need) (mv r nil))
            ((equal status :long) (fn-pull-fail r))
            (t (mv-let (r2 effects continuep)
                 (fn-pull-on-line (fn-pull-with r :buf rest) line)
                 (if continuep
                     (mv-let (r3 more) (fn-pull-drain r2 (1- fuel))
                       (mv r3 (append effects more)))
                   (mv r2 effects))))))))

; The code of the local node's reply: the first line's.
(defun fn-pull-local-code (octets)
  (declare (xargs :guard t))
  (mv-let (status line rest) (fn-pull-split octets)
    (declare (ignore rest))
    (fn-pull-code (if (equal status :line) line nil))))

(defun fn-pull-event-octets (event)
  (declare (xargs :guard t))
  (if (and (consp event) (fn-pull-octetsp (cdr event))) (cdr event) nil))

; KEYSTONE SUBJECT.  One event of the round: the function the host calls
; (host/native/pull-service.lisp `fnn-pull-event').
;   (:remote . octets)   octets read from the peer
;   (:local . octets)    the local node's non-empty reply on the transit connection
;   (:lost)              either connection failed or closed
(defun fn-pull-step (r event)
  (declare (xargs :guard t))
  (let ((kind (if (consp event) (car event) nil))
        (octets (fn-pull-event-octets event))
        (phase (fn-pull-r-phase r)))
    (cond
     ((member-equal phase '(:done :failed)) (mv r nil))
     ((equal kind :lost) (fn-pull-fail r))
     ((equal kind :remote)
      (cond ((fn-pull-line-phasep phase)
             (let ((buf (append (if (true-listp (fn-pull-r-buf r))
                                    (fn-pull-r-buf r) nil)
                                octets)))
               (fn-pull-drain (fn-pull-with r :buf buf) (+ 1 (len buf)))))
            ((equal phase :forward)
             (mv r (if (consp octets) (list (cons :local octets)) nil)))
            ; Octets from the peer while no command is outstanding there.
            (t (fn-pull-fail r))))
     ((equal kind :local)
      (let ((code (fn-pull-local-code octets)))
        (cond
         ((equal phase :local-greeting)
          (if (member-equal code '(200 201))
              (fn-pull-next r)
            (fn-pull-fail r)))
         ((equal phase :offer)
          (cond ((equal code 335)
                 (mv (fn-pull-with r :phase :article)
                     (list (cons :remote
                                 (fn-pull-command
                                  (list (fn-record-string-octets "ARTICLE")
                                        (let ((c (fn-pull-r-current r)))
                                          (if (true-listp c) c nil))))))))
                ((natp code) (fn-pull-next (fn-pull-record-answer r code)))
                (t (fn-pull-fail r))))
         ((equal phase :forward)
          (if (natp code)
              (fn-pull-next (fn-pull-record-answer r code))
            (fn-pull-fail r)))
         (t (fn-pull-fail r)))))
     (t (mv r nil)))))

; The round's transitions are opened by name in the proofs below.
(in-theory (disable fn-pull-step fn-pull-drain fn-pull-on-line fn-pull-next
                    fn-pull-command
                    fn-pull-newnews-octets fn-pull-date-ms fn-pull-msgidp
                    fn-pull-code fn-pull-local-code fn-pull-split))

; A whole round's events, for the trace statements and the tests.
(defun fn-pull-run (r events)
  (declare (xargs :guard t))
  (if (consp events)
      (mv-let (r2 effects) (fn-pull-step r (car events))
        (mv-let (r3 more) (fn-pull-run r2 (cdr events))
          (mv r3 (append (fn-pull-list effects) more))))
    (mv r nil)))

; -----------------------------------------------------------------------------
; Closing a round: the ack-bounded advance.

(defun fn-pull-answer-of (id answers)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal id (if (alistp answers) answers nil))))
    (if (consp hit) (cdr hit) nil)))

(defun fn-pull-all-answeredp (listed answers)
  (declare (xargs :guard t))
  (if (consp listed)
      (and (fn-pull-terminal-codep (fn-pull-answer-of (car listed) answers))
           (fn-pull-all-answeredp (cdr listed) answers))
    t))

;; PRF-165: the unavailable class.

; The round's bound as a positive count.
(defun fn-pull-bound-of (bound)
  (declare (xargs :guard t))
  (if (posp bound) bound 1))

; The consecutive count PENDING holds for ID (0 when absent).
(defun fn-pull-count-of (id pending)
  (declare (xargs :guard t))
  (let ((hit (assoc-equal id (if (alistp pending) pending nil))))
    (if (and (consp hit) (natp (cdr hit))) (cdr hit) 0)))

; Every listed id drew a terminal answer or the peer's 430.
(defun fn-pull-all-answered-or-unavailablep (listed answers unavailable)
  (declare (xargs :guard t))
  (if (consp listed)
      (and (or (fn-pull-terminal-codep (fn-pull-answer-of (car listed) answers))
               (and (member-equal (car listed) (fn-pull-list unavailable)) t))
           (fn-pull-all-answered-or-unavailablep (cdr listed) answers unavailable))
    t))

; The round ran to its end and every id it listed was answered.
(defun fn-pull-completep (r)
  (declare (xargs :guard t))
  (and (equal (fn-pull-r-phase r) :done)
       (consp (fn-pull-r-listed r))
       (natp (fn-pull-r-started r))
       (fn-pull-all-answered-or-unavailablep (fn-pull-r-listed r)
                                             (fn-pull-r-answers r)
                                             (fn-pull-r-unavailable r))))

; The counts after a complete round: each id unavailable in it, one more
; than the round's cursor held; an id the round did not find unavailable
; starts again from nothing.
(defun fn-pull-next-pending (ids pending)
  (declare (xargs :guard t))
  (if (consp ids)
      (if (fn-pull-msgidp (car ids))
          (cons (cons (car ids) (+ 1 (fn-pull-count-of (car ids) pending)))
                (fn-pull-next-pending (cdr ids) pending))
        (fn-pull-next-pending (cdr ids) pending))
    nil))

; Some unavailable id has not yet been unavailable BOUND consecutive rounds.
(defun fn-pull-holdingp (ids pending bound)
  (declare (xargs :guard t))
  (if (consp ids)
      (or (< (+ 1 (fn-pull-count-of (car ids) pending)) (fn-pull-bound-of bound))
          (fn-pull-holdingp (cdr ids) pending bound))
    nil))

(defun fn-pull-advancesp (r)
  (declare (xargs :guard t))
  (and (fn-pull-completep r)
       (not (fn-pull-holdingp (fn-pull-list (fn-pull-r-unavailable r))
                              (fn-pull-r-pending r) (fn-pull-r-bound r)))))

; KEYSTONE SUBJECT.  The cursor after a round (host/native/pull-service.lisp
; `fnn-pull-round' through `fn-pull-session-close').  An advancing round
; moves the instant and clears PENDING; a complete round an unavailable id
; still holds keeps the instant and journals the new counts; any other round
; leaves the cursor as it began.
(defun fn-pull-close (r)
  (declare (xargs :guard t))
  (cond ((fn-pull-advancesp r)
         (fn-pull-cursor (fn-pull-r-peer r)
                         (fn-pull-back (fn-pull-r-started r) *fn-pull-overlap-ms*)
                         (+ 1 (nfix (fn-pull-r-advances r)))
                         nil))
        ((fn-pull-completep r)
         (fn-pull-cursor (fn-pull-r-peer r) (fn-pull-r-since r)
                         (fn-pull-r-advances r)
                         (fn-pull-next-pending (fn-pull-list (fn-pull-r-unavailable r))
                                               (fn-pull-r-pending r))))
        (t (fn-pull-round-cursor r))))

; The journal effects of a close: one record exactly when the round was
; complete (the cursor moved, or its counts changed).
(defun fn-pull-close-effects (r)
  (declare (xargs :guard t))
  (if (fn-pull-completep r) (list (cons :journal (fn-pull-close r))) nil))

; The ids a complete round drops: unavailable in it, their count reaching
; BOUND exactly now.  The owner log names each (`fn-pull-log-line').
(defun fn-pull-dropped-of (ids pending bound)
  (declare (xargs :guard t))
  (if (consp ids)
      (if (equal (+ 1 (fn-pull-count-of (car ids) pending)) (fn-pull-bound-of bound))
          (cons (car ids) (fn-pull-dropped-of (cdr ids) pending bound))
        (fn-pull-dropped-of (cdr ids) pending bound))
    nil))

(defun fn-pull-dropped (r)
  (declare (xargs :guard t))
  (if (fn-pull-completep r)
      (fn-pull-dropped-of (fn-pull-list (fn-pull-r-unavailable r)) (fn-pull-r-pending r)
                          (fn-pull-r-bound r))
    nil))

; Each listed id drew a terminal answer, or was unavailable in this round
; with its consecutive count reaching the bound.
(defun fn-pull-all-answered-or-droppedp (listed answers unavailable pending bound)
  (declare (xargs :guard t))
  (if (consp listed)
      (and (or (fn-pull-terminal-codep (fn-pull-answer-of (car listed) answers))
               (and (member-equal (car listed) (fn-pull-list unavailable))
                    (<= (fn-pull-bound-of bound)
                        (+ 1 (fn-pull-count-of (car listed) pending)))))
           (fn-pull-all-answered-or-droppedp (cdr listed) answers unavailable
                                             pending bound))
    t))

(defthm fn-pull-holdingp-member
  (implies (and (not (fn-pull-holdingp ids pending bound))
                (member-equal id ids))
           (<= (fn-pull-bound-of bound) (+ 1 (fn-pull-count-of id pending))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-pull-bound-of fn-pull-count-of))))

(defthm fn-pull-answered-or-unavailable-and-not-holding
  (implies (and (fn-pull-all-answered-or-unavailablep listed answers unavailable)
                (not (fn-pull-holdingp (fn-pull-list unavailable) pending bound)))
           (fn-pull-all-answered-or-droppedp listed answers unavailable pending bound))
  :hints (("Goal" :in-theory (disable fn-pull-bound-of fn-pull-count-of
                                      fn-pull-terminal-codep fn-pull-answer-of))))

(defthm fn-pull-list-of-true-list
  (implies (true-listp x) (equal (fn-pull-list x) x)))

; KEYSTONE (the ack-bounded advance, PRF-100 restated for PRF-165).  If
; closing a round moves the cursor, the round ran to its end and EVERY
; Message-ID its NEWNEWS listed drew 235, 435 or 437 from the local node,
; or was answered 430 by the peer in this round with its consecutive count
; reaching the bound; the new instant is the peer's DATE at the round's
; start less the overlap, and no count survives it.
(defthm fn-pull-close-advances-only-past-a-fully-answered-round
  (implies (not (equal (fn-pull-cursor-advances (fn-pull-close r))
                       (fn-pull-r-advances r)))
           (and (equal (fn-pull-r-phase r) :done)
                (fn-pull-all-answered-or-droppedp
                 (fn-pull-r-listed r) (fn-pull-r-answers r)
                 (fn-pull-r-unavailable r) (fn-pull-r-pending r)
                 (fn-pull-r-bound r))
                (equal (fn-pull-cursor-since (fn-pull-close r))
                       (fn-pull-back (fn-pull-r-started r) *fn-pull-overlap-ms*))
                (equal (fn-pull-cursor-pending (fn-pull-close r)) nil)))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-pull-all-answered-or-droppedp
                                   fn-pull-all-answered-or-unavailablep
                                   fn-pull-holdingp fn-pull-next-pending
                                   fn-pull-list))
           :use ((:instance fn-pull-answered-or-unavailable-and-not-holding
                            (listed (fn-pull-r-listed r))
                            (answers (fn-pull-r-answers r))
                            (unavailable (fn-pull-r-unavailable r))
                            (pending (fn-pull-r-pending r))
                            (bound (fn-pull-r-bound r)))))))

(defthm fn-pull-all-answered-or-unavailablep-of-no-unavailable
  (implies (not (consp unavailable))
           (equal (fn-pull-all-answered-or-unavailablep listed answers unavailable)
                  (fn-pull-all-answeredp listed answers)))
  :hints (("Goal" :in-theory (e/d (fn-pull-list)
                                  (fn-pull-terminal-codep fn-pull-answer-of)))))

; KEYSTONE (PRF-100's conclusion, verbatim, for a round the peer served in
; full).  A round in which the peer produced every listed article moves the
; cursor only past a round every listed id of which drew 235, 435 or 437.
(defthm fn-pull-close-advances-past-all-answered-when-nothing-is-unavailable
  (implies (and (not (consp (fn-pull-r-unavailable r)))
                (not (equal (fn-pull-close r) (fn-pull-round-cursor r))))
           (and (equal (fn-pull-r-phase r) :done)
                (fn-pull-all-answeredp (fn-pull-r-listed r) (fn-pull-r-answers r))
                (equal (fn-pull-cursor-since (fn-pull-close r))
                       (fn-pull-back (fn-pull-r-started r) *fn-pull-overlap-ms*))))
  :hints (("Goal" :in-theory (disable fn-pull-all-answeredp
                                      fn-pull-all-answered-or-unavailablep))))

(defthm fn-pull-all-answeredp-member
  (implies (and (fn-pull-all-answeredp listed answers)
                (member-equal id listed))
           (fn-pull-terminal-codep (fn-pull-answer-of id answers)))
  :hints (("Goal" :in-theory (disable fn-pull-terminal-codep fn-pull-answer-of))))

(defthm fn-pull-all-answered-or-droppedp-member
  (implies (and (fn-pull-all-answered-or-droppedp listed answers unavailable
                                                  pending bound)
                (member-equal id listed))
           (or (fn-pull-terminal-codep (fn-pull-answer-of id answers))
               (and (member-equal id (fn-pull-list unavailable))
                    (<= (fn-pull-bound-of bound)
                        (+ 1 (fn-pull-count-of id pending))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pull-terminal-codep fn-pull-answer-of
                                      fn-pull-bound-of fn-pull-count-of))))

; The per-id reading: a listed id with no terminal answer that was not
; dropped in this round holds the cursor's instant and advance count.
(defthm fn-pull-unanswered-id-holds-the-cursor
  (implies (and (member-equal id (fn-pull-r-listed r))
                (not (fn-pull-terminal-codep
                      (fn-pull-answer-of id (fn-pull-r-answers r))))
                (not (and (member-equal id (fn-pull-list (fn-pull-r-unavailable r)))
                          (<= (fn-pull-bound-of (fn-pull-r-bound r))
                              (+ 1 (fn-pull-count-of id (fn-pull-r-pending r)))))))
           (and (equal (fn-pull-cursor-since (fn-pull-close r)) (fn-pull-r-since r))
                (equal (fn-pull-cursor-advances (fn-pull-close r))
                       (fn-pull-r-advances r))))
  :hints (("Goal" :in-theory (disable fn-pull-terminal-codep fn-pull-answer-of
                                      fn-pull-all-answered-or-droppedp
                                      fn-pull-bound-of fn-pull-count-of
                                      fn-pull-close)
           :use ((:instance fn-pull-close-advances-only-past-a-fully-answered-round)
                 (:instance fn-pull-all-answered-or-droppedp-member
                            (listed (fn-pull-r-listed r))
                            (answers (fn-pull-r-answers r))
                            (unavailable (fn-pull-r-unavailable r))
                            (pending (fn-pull-r-pending r))
                            (bound (fn-pull-r-bound r))))
           :expand ((fn-pull-close r)))))

(defthm fn-pull-count-of-next-pending
  (implies (and (member-equal id ids) (fn-pull-msgidp id))
           (equal (fn-pull-count-of id (fn-pull-next-pending ids pending))
                  (+ 1 (fn-pull-count-of id pending))))
  :hints (("Goal" :in-theory (e/d () (fn-pull-msgidp)))))

(defthm fn-pull-count-of-next-pending-absent
  (implies (not (member-equal id ids))
           (equal (fn-pull-count-of id (fn-pull-next-pending ids pending)) 0))
  :hints (("Goal" :in-theory (e/d () (fn-pull-msgidp)))))

(defthm fn-pull-holdingp-witness
  (implies (and (member-equal id ids)
                (< (+ 1 (fn-pull-count-of id pending)) (fn-pull-bound-of bound)))
           (fn-pull-holdingp ids pending bound))
  :hints (("Goal" :in-theory (disable fn-pull-bound-of fn-pull-count-of))))

; KEYSTONE (retried while listed).  An id the peer answered 430 in a round,
; unavailable fewer than BOUND consecutive complete rounds counting this
; one, does not let the instant pass it: the next NEWNEWS names the same
; instant, so the peer lists the id again; and if the round was complete
; its count is exactly one more than the round's cursor held.
(defthm fn-pull-unavailable-id-is-retried-below-the-bound
  (implies (and (member-equal id (fn-pull-list (fn-pull-r-unavailable r)))
                (fn-pull-msgidp id)
                (< (+ 1 (fn-pull-count-of id (fn-pull-r-pending r)))
                   (fn-pull-bound-of (fn-pull-r-bound r))))
           (and (equal (fn-pull-cursor-since (fn-pull-close r)) (fn-pull-r-since r))
                (equal (fn-pull-cursor-advances (fn-pull-close r))
                       (fn-pull-r-advances r))
                (implies (fn-pull-completep r)
                         (equal (fn-pull-count-of
                                 id (fn-pull-cursor-pending (fn-pull-close r)))
                                (+ 1 (fn-pull-count-of id (fn-pull-r-pending r)))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-pull-completep fn-pull-count-of fn-pull-list
                                   fn-pull-bound-of fn-pull-msgidp
                                   fn-pull-next-pending))
           :use ((:instance fn-pull-holdingp-witness
                            (ids (fn-pull-list (fn-pull-r-unavailable r)))
                            (pending (fn-pull-r-pending r))
                            (bound (fn-pull-r-bound r)))))))

; KEYSTONE (dropped exactly at the bound).  A complete round in which every
; unavailable id has reached BOUND consecutive rounds moves the cursor:
; the peer's unproducible ids no longer hold it.  Together with
; `fn-pull-unavailable-id-is-retried-below-the-bound' (the count is the
; number of consecutive complete rounds, and below BOUND the instant holds),
; an id is dropped at the round its count reaches BOUND and at no earlier one.
(defthm fn-pull-complete-round-past-the-bound-advances
  (implies (and (fn-pull-completep r)
                (not (fn-pull-holdingp (fn-pull-list (fn-pull-r-unavailable r))
                                       (fn-pull-r-pending r) (fn-pull-r-bound r))))
           (equal (fn-pull-close r)
                  (fn-pull-cursor (fn-pull-r-peer r)
                                  (fn-pull-back (fn-pull-r-started r)
                                                *fn-pull-overlap-ms*)
                                  (+ 1 (nfix (fn-pull-r-advances r)))
                                  nil)))
  :hints (("Goal" :in-theory (disable fn-pull-completep fn-pull-holdingp))))

; -----------------------------------------------------------------------------
; A step asks with one cursor and journals nothing.

(defun fn-pull-journal-effects (effects)
  ; The cursors of the (:journal . cursor) effects, in order.
  (declare (xargs :guard t))
  (if (consp effects)
      (if (and (consp (car effects)) (equal (car (car effects)) :journal))
          (cons (cdr (car effects)) (fn-pull-journal-effects (cdr effects)))
        (fn-pull-journal-effects (cdr effects)))
    nil))

(defthm fn-pull-journal-effects-of-append
  (equal (fn-pull-journal-effects (append a b))
         (append (fn-pull-journal-effects a) (fn-pull-journal-effects b))))

(defun fn-pull-remote-effects (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (if (and (consp (car effects)) (equal (car (car effects)) :remote))
          (cons (cdr (car effects)) (fn-pull-remote-effects (cdr effects)))
        (fn-pull-remote-effects (cdr effects)))
    nil))

(defthm fn-pull-remote-effects-of-append
  (equal (fn-pull-remote-effects (append a b))
         (append (fn-pull-remote-effects a) (fn-pull-remote-effects b))))

; "NEWNEWS " as octets.
(defconst *fn-pull-newnews-prefix* '(78 69 87 78 69 87 83 32))

(defun fn-pull-newnews-linep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (<= 8 (len x))
       (equal (take 8 x) *fn-pull-newnews-prefix*)))

; Every NEWNEWS in EFFECTS is the one for WILDMAT and SINCE.
(defun fn-pull-newnews-all (remotes wildmat since)
  (declare (xargs :guard t))
  (if (consp remotes)
      (and (or (not (fn-pull-newnews-linep (car remotes)))
               (equal (car remotes) (fn-pull-newnews-octets wildmat since)))
           (fn-pull-newnews-all (cdr remotes) wildmat since))
    t))

(defthm fn-pull-newnews-all-of-append
  (equal (fn-pull-newnews-all (append a b) w s)
         (and (fn-pull-newnews-all a w s) (fn-pull-newnews-all b w s))))

(defthm fn-pull-article-is-not-newnews
  (not (fn-pull-newnews-linep
        (fn-pull-command (list (quote (65 82 84 73 67 76 69)) x)))) ; "ARTICLE"
  :hints (("Goal" :in-theory (enable fn-pull-command))))

;; The pieces of a step, one lemma each, so that no proof below opens more
;; than one transition.
(defthm fn-pull-fail-facts
  (and (equal (fn-pull-round-cursor (car (fn-pull-fail r)))
              (fn-pull-round-cursor r))
       (equal (fn-pull-r-wildmat (car (fn-pull-fail r))) (fn-pull-r-wildmat r))
       (equal (fn-pull-r-answers (car (fn-pull-fail r))) (fn-pull-r-answers r))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-fail r))) nil)
       (equal (fn-pull-remote-effects (mv-nth 1 (fn-pull-fail r))) nil))
  :hints (("Goal" :in-theory (enable fn-pull-fail))))

(defthm fn-pull-next-facts
  (and (equal (fn-pull-r-peer (car (fn-pull-next r))) (fn-pull-r-peer r))
       (equal (fn-pull-r-since (car (fn-pull-next r))) (fn-pull-r-since r))
       (equal (fn-pull-r-advances (car (fn-pull-next r))) (fn-pull-r-advances r))
       (equal (fn-pull-r-pending (car (fn-pull-next r))) (fn-pull-r-pending r))
       (equal (fn-pull-r-bound (car (fn-pull-next r))) (fn-pull-r-bound r))
       (equal (fn-pull-r-wildmat (car (fn-pull-next r))) (fn-pull-r-wildmat r))
       (equal (fn-pull-r-answers (car (fn-pull-next r))) (fn-pull-r-answers r))
       (equal (fn-pull-r-current (car (fn-pull-next r)))
              (if (consp (fn-pull-r-todo r)) (car (fn-pull-r-todo r)) nil))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-next r))) nil)
       (equal (fn-pull-remote-effects (mv-nth 1 (fn-pull-next r)))
              (if (consp (fn-pull-r-todo r)) nil (list (fn-pull-quit)))))
  :hints (("Goal" :in-theory (enable fn-pull-next))))

(defthm fn-pull-record-answer-facts
  (and (equal (fn-pull-round-cursor (fn-pull-record-answer r code))
              (fn-pull-round-cursor r))
       (equal (fn-pull-r-wildmat (fn-pull-record-answer r code)) (fn-pull-r-wildmat r))
       (equal (fn-pull-r-todo (fn-pull-record-answer r code)) (fn-pull-r-todo r))
       (equal (fn-pull-r-current (fn-pull-record-answer r code)) (fn-pull-r-current r))
       (equal (fn-pull-r-answers (fn-pull-record-answer r code))
              (cons (cons (fn-pull-r-current r) code) (fn-pull-r-answers r))))
  :hints (("Goal" :in-theory (enable fn-pull-record-answer))))

(defthm fn-pull-on-line-facts
  (and (equal (fn-pull-r-peer (car (fn-pull-on-line r line))) (fn-pull-r-peer r))
       (equal (fn-pull-r-since (car (fn-pull-on-line r line))) (fn-pull-r-since r))
       (equal (fn-pull-r-advances (car (fn-pull-on-line r line))) (fn-pull-r-advances r))
       (equal (fn-pull-r-pending (car (fn-pull-on-line r line))) (fn-pull-r-pending r))
       (equal (fn-pull-r-bound (car (fn-pull-on-line r line))) (fn-pull-r-bound r))
       (equal (fn-pull-r-wildmat (car (fn-pull-on-line r line))) (fn-pull-r-wildmat r))
       (equal (fn-pull-r-answers (car (fn-pull-on-line r line)))
              (fn-pull-r-answers r))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-on-line r line))) nil))
  :hints (("Goal" :in-theory (enable fn-pull-on-line))))

(defthm fn-pull-on-line-newnews
  (implies (and (equal w (fn-pull-r-wildmat r)) (equal since (fn-pull-r-since r)))
           (fn-pull-newnews-all
            (fn-pull-remote-effects (mv-nth 1 (fn-pull-on-line r line))) w since))
  :hints (("Goal" :in-theory (enable fn-pull-on-line))))

(defthm fn-pull-drain-keeps-the-cursor
  (and (equal (fn-pull-r-peer (car (fn-pull-drain r fuel))) (fn-pull-r-peer r))
       (equal (fn-pull-r-since (car (fn-pull-drain r fuel))) (fn-pull-r-since r))
       (equal (fn-pull-r-advances (car (fn-pull-drain r fuel))) (fn-pull-r-advances r))
       (equal (fn-pull-r-pending (car (fn-pull-drain r fuel))) (fn-pull-r-pending r))
       (equal (fn-pull-r-bound (car (fn-pull-drain r fuel))) (fn-pull-r-bound r))
       (equal (fn-pull-r-wildmat (car (fn-pull-drain r fuel))) (fn-pull-r-wildmat r)))
  :hints (("Goal" :in-theory (enable fn-pull-drain))))

(defthm fn-pull-drain-journals-nothing
  (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-drain r fuel))) nil)
  :hints (("Goal" :in-theory (enable fn-pull-drain))))

(defthm fn-pull-step-keeps-the-cursor-fields
  (and (equal (fn-pull-r-peer (car (fn-pull-step r event))) (fn-pull-r-peer r))
       (equal (fn-pull-r-since (car (fn-pull-step r event))) (fn-pull-r-since r))
       (equal (fn-pull-r-advances (car (fn-pull-step r event))) (fn-pull-r-advances r))
       (equal (fn-pull-r-pending (car (fn-pull-step r event))) (fn-pull-r-pending r))
       (equal (fn-pull-r-bound (car (fn-pull-step r event))) (fn-pull-r-bound r))
       (equal (fn-pull-r-wildmat (car (fn-pull-step r event))) (fn-pull-r-wildmat r)))
  :hints (("Goal" :in-theory (enable fn-pull-step))))

; KEYSTONE.  No step changes the cursor a round asks with or journals
; anything: the round's durable state is fixed from `fn-pull-begin' to
; `fn-pull-close'.
(defthm fn-pull-step-keeps-the-cursor-and-journals-nothing
  (and (equal (fn-pull-round-cursor (car (fn-pull-step r event)))
              (fn-pull-round-cursor r))
       (equal (fn-pull-r-wildmat (car (fn-pull-step r event)))
              (fn-pull-r-wildmat r))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-step r event))) nil))
  :hints (("Goal" :in-theory (enable fn-pull-step))))

(defthm fn-pull-run-keeps-the-cursor-and-journals-nothing
  (and (equal (fn-pull-round-cursor (car (fn-pull-run r events)))
              (fn-pull-round-cursor r))
       (equal (fn-pull-r-wildmat (car (fn-pull-run r events)))
              (fn-pull-r-wildmat r))
       (equal (fn-pull-journal-effects (mv-nth 1 (fn-pull-run r events))) nil))
  :hints (("Goal" :in-theory (disable fn-pull-step fn-pull-round-cursor))))

; -----------------------------------------------------------------------------
; Answers come only from the local node.

(defthm fn-pull-drain-keeps-answers
  (equal (fn-pull-r-answers (car (fn-pull-drain r fuel)))
         (fn-pull-r-answers r))
  :hints (("Goal" :in-theory (enable fn-pull-drain))))

; KEYSTONE.  A step that changes the answers is a local reply, and it adds
; exactly one answer: that reply's own code, for the article in hand.
(defthm fn-pull-step-answers-only-from-the-local-node
  (implies (not (equal (fn-pull-r-answers (car (fn-pull-step r event)))
                       (fn-pull-r-answers r)))
           (and (consp event)
                (equal (car event) :local)
                (equal (fn-pull-r-answers (car (fn-pull-step r event)))
                       (cons (cons (fn-pull-r-current r)
                                   (fn-pull-local-code
                                    (fn-pull-event-octets event)))
                             (fn-pull-r-answers r)))))
  :hints (("Goal" :in-theory (enable fn-pull-step))))

; PRF-165: only the peer marks an id unavailable.

(defthm fn-pull-on-line-unavailable
  (and (equal (fn-pull-r-current (car (fn-pull-on-line r line))) (fn-pull-r-current r))
       (implies (not (equal (fn-pull-r-phase r) :article))
                (and (equal (fn-pull-r-unavailable (car (fn-pull-on-line r line)))
                            (fn-pull-r-unavailable r))
                     (not (equal (fn-pull-r-phase (car (fn-pull-on-line r line)))
                                 :article)))))
  :hints (("Goal" :in-theory (enable fn-pull-on-line fn-pull-fail))))

(defthm fn-pull-on-line-unavailable-in-article
  (implies (equal (fn-pull-r-phase r) :article)
           (and (not (mv-nth 2 (fn-pull-on-line r line)))
                (equal (fn-pull-r-unavailable (car (fn-pull-on-line r line)))
                       (if (and (equal (fn-pull-code line) 430)
                                (not (consp (fn-pull-r-buf r))))
                           (cons (fn-pull-r-current r)
                                 (fn-pull-list (fn-pull-r-unavailable r)))
                         (fn-pull-r-unavailable r)))))
  :hints (("Goal" :in-theory (enable fn-pull-on-line fn-pull-fail))))

(defthm fn-pull-drain-unavailable
  (implies (not (equal (fn-pull-r-unavailable (car (fn-pull-drain r fuel)))
                       (fn-pull-r-unavailable r)))
           (and (equal (fn-pull-r-phase r) :article)
                (equal (fn-pull-r-unavailable (car (fn-pull-drain r fuel)))
                       (cons (fn-pull-r-current r)
                             (fn-pull-list (fn-pull-r-unavailable r))))))
  :hints (("Goal" :in-theory (enable fn-pull-drain fn-pull-fail))))

(defthm fn-pull-next-and-record-keep-unavailable
  (and (equal (fn-pull-r-unavailable (car (fn-pull-next r))) (fn-pull-r-unavailable r))
       (equal (fn-pull-r-unavailable (fn-pull-record-answer r code))
              (fn-pull-r-unavailable r))
       (equal (fn-pull-r-unavailable (car (fn-pull-fail r))) (fn-pull-r-unavailable r)))
  :hints (("Goal" :in-theory (enable fn-pull-next fn-pull-record-answer fn-pull-fail))))

(defthm fn-pull-drain-keeps-unavailable-outside-article
  (implies (not (equal (fn-pull-r-phase r) :article))
           (equal (fn-pull-r-unavailable (car (fn-pull-drain r fuel)))
                  (fn-pull-r-unavailable r)))
  :hints (("Goal" :in-theory (disable fn-pull-drain-unavailable)
           :use ((:instance fn-pull-drain-unavailable)))))

; KEYSTONE (PRF-165).  A step that changes the unavailable ids is the PEER's
; reply to the round's ARTICLE (phase :article), and it adds exactly the
; article in hand: the local node's replies never mark an id unavailable,
; and the peer marks at most the one id it was asked for.
(defthm fn-pull-step-marks-unavailable-only-on-the-peers-reply
  (implies (not (equal (fn-pull-r-unavailable (car (fn-pull-step r event)))
                       (fn-pull-r-unavailable r)))
           (and (consp event)
                (equal (car event) :remote)
                (equal (fn-pull-r-phase r) :article)
                (equal (fn-pull-r-unavailable (car (fn-pull-step r event)))
                       (cons (fn-pull-r-current r)
                             (fn-pull-list (fn-pull-r-unavailable r))))))
  :hints (("Goal" :in-theory (e/d (fn-pull-step)
                                  (fn-pull-next fn-pull-record-answer fn-pull-fail
                                   fn-pull-drain fn-pull-list
                                   fn-pull-drain-unavailable))
           :use ((:instance fn-pull-drain-unavailable
                            (r (fn-pull-with r :buf (append (if (true-listp (fn-pull-r-buf r))
                                                                (fn-pull-r-buf r) nil)
                                                            (fn-pull-event-octets event))))
                            (fuel (+ 1 (len (append (if (true-listp (fn-pull-r-buf r))
                                                        (fn-pull-r-buf r) nil)
                                                    (fn-pull-event-octets event))))))))))

; -----------------------------------------------------------------------------
; The NEWNEWS names the cursor's instant.

(defthm fn-pull-drain-newnews
  (implies (and (equal w (fn-pull-r-wildmat r)) (equal since (fn-pull-r-since r)))
           (fn-pull-newnews-all
            (fn-pull-remote-effects (mv-nth 1 (fn-pull-drain r fuel))) w since))
  :hints (("Goal" :in-theory (e/d (fn-pull-drain) (fn-pull-newnews-linep)))))

; KEYSTONE.  Every NEWNEWS a step sends names the round's own cursor instant:
; the one `fn-pull-begin' fixed and the journal holds.
(defthm fn-pull-step-newnews-names-the-cursor
  (fn-pull-newnews-all (fn-pull-remote-effects (mv-nth 1 (fn-pull-step r event)))
                       (fn-pull-r-wildmat r) (fn-pull-r-since r))
  :hints (("Goal" :in-theory (e/d (fn-pull-step) (fn-pull-newnews-linep)))))

; -----------------------------------------------------------------------------
; The journal: replay and the correspondence at every crash point

; Replay: the last journaled cursor of this peer, else C.
(defun fn-pull-replay (c cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (fn-pull-replay (if (and (fn-pull-cursorp (car cursors))
                               (equal (fn-pull-cursor-peer (car cursors))
                                      (fn-pull-cursor-peer c)))
                          (car cursors)
                        c)
                      (cdr cursors))
    c))

(defthm fn-pull-replay-of-append
  (equal (fn-pull-replay c (append a b))
         (fn-pull-replay (fn-pull-replay c a) b)))

(defthm fn-pull-replay-of-nil
  (equal (fn-pull-replay c nil) c))

(defthm fn-pull-round-cursor-of-begin
  (implies (fn-pull-startable-cursorp c)
           (equal (fn-pull-round-cursor (fn-pull-begin c wildmat now bound))
                  (fn-pull-cursor (fn-pull-cursor-peer c)
                                  (fn-pull-begin-since c now)
                                  (fn-pull-cursor-advances c)
                                  (fn-pull-cursor-pending c)))))

(defthm fn-pull-replay-of-cons
  (equal (fn-pull-replay c (cons x rest))
         (fn-pull-replay (if (and (fn-pull-cursorp x)
                                  (equal (fn-pull-cursor-peer x)
                                         (fn-pull-cursor-peer c)))
                             x c)
                         rest)))

(defthm fn-pull-startable-cursor-is-its-fields
  (implies (fn-pull-startable-cursorp c)
           (equal (fn-pull-cursor (fn-pull-cursor-peer c) (fn-pull-cursor-since c)
                                  (fn-pull-cursor-advances c)
                                  (fn-pull-cursor-pending c))
                  c))
  :hints (("Goal" :in-theory (enable fn-pull-at)
           :expand ((fn-pull-at 1 c) (fn-pull-at 0 (cdr c)) (fn-pull-at 2 c)
                    (fn-pull-at 1 (cdr c)) (fn-pull-at 0 (cddr c))
                    (fn-pull-at 3 c) (fn-pull-at 2 (cdr c))
                    (fn-pull-at 1 (cddr c)) (fn-pull-at 0 (cdddr c))
                    (len c) (len (cdr c)) (len (cddr c)) (len (cdddr c))
                    (len (cddddr c))))))

(defthm fn-pull-cursorp-of-cursor
  ; (a cursor is a four-element list: `fn-pull-cursor' is open)
  (equal (fn-pull-cursorp (list peer since advances pending))
         (and (fn-feed-namep peer) (natp since) (natp advances)
              (fn-pull-pendingp pending))))

(defthm fn-pull-pendingp-of-next-pending
  (fn-pull-pendingp (fn-pull-next-pending ids pending))
  :hints (("Goal" :in-theory (disable fn-pull-msgidp fn-pull-count-of))))

(defthm fn-pull-back-natp
  (natp (fn-pull-back ms by))
  :rule-classes :type-prescription)

(defun fn-pull-roundp (r)
  ; What the owner carries of an in-flight round: its peer is a name, its
  ; instant and advance count naturals and its counts well formed.
  (declare (xargs :guard t))
  (and (fn-feed-namep (fn-pull-r-peer r))
       (natp (fn-pull-r-since r))
       (natp (fn-pull-r-advances r))
       (fn-pull-pendingp (fn-pull-r-pending r))))

(defthm fn-pull-begin-since-natp
  (natp (fn-pull-begin-since c now))
  :rule-classes :type-prescription)

(defthm fn-pull-roundp-of-begin
  (implies (fn-pull-startable-cursorp c)
           (fn-pull-roundp (fn-pull-begin c wildmat now bound)))
  :hints (("Goal" :in-theory (e/d (fn-pull-startable-cursorp)
                                  (fn-pull-begin-since)))))

(defthm fn-pull-run-keeps-the-cursor-fields
  (and (equal (fn-pull-r-peer (car (fn-pull-run r events))) (fn-pull-r-peer r))
       (equal (fn-pull-r-since (car (fn-pull-run r events))) (fn-pull-r-since r))
       (equal (fn-pull-r-advances (car (fn-pull-run r events))) (fn-pull-r-advances r))
       (equal (fn-pull-r-pending (car (fn-pull-run r events))) (fn-pull-r-pending r))
       (equal (fn-pull-r-bound (car (fn-pull-run r events))) (fn-pull-r-bound r))
       (equal (fn-pull-r-wildmat (car (fn-pull-run r events))) (fn-pull-r-wildmat r)))
  :hints (("Goal" :in-theory (disable fn-pull-step))))

(defthm fn-pull-roundp-of-run
  (implies (fn-pull-roundp r)
           (fn-pull-roundp (mv-nth 0 (fn-pull-run r events))))
  :hints (("Goal" :in-theory (disable fn-pull-run))))

(in-theory (disable fn-pull-replay fn-pull-cursorp fn-pull-back
                    fn-pull-begin-since fn-pull-startable-cursorp))

(defthm fn-pull-begin-since-of-a-journaled-instant
  (implies (natp since)
           (equal (fn-pull-begin-since (list peer since advances pending) now) since))
  :hints (("Goal" :in-theory (enable fn-pull-begin-since))))

(defthm fn-pull-begin-journal-replays-to-the-round
  (implies (and (fn-pull-startable-cursorp c)
                (equal (fn-pull-replay c0 j) c))
           (equal (fn-pull-replay c0 (append j (fn-pull-journal-effects
                                                (fn-pull-begin-effects c now))))
                  (fn-pull-round-cursor (fn-pull-begin c wildmat now bound))))
  :hints (("Goal" :in-theory (e/d (fn-pull-startable-cursorp fn-pull-begin-since)
                                  (fn-pull-startable-cursor-is-its-fields))
           :use ((:instance fn-pull-startable-cursor-is-its-fields))
           :do-not-induct t)))

(defthm fn-pull-advancesp-is-complete
  (implies (fn-pull-advancesp r) (fn-pull-completep r))
  :rule-classes :forward-chaining)

(defthm fn-pull-close-journal-replays-to-the-close
  (implies (and (fn-pull-roundp r)
                (equal (fn-pull-replay c0 j) (fn-pull-round-cursor r)))
           (equal (fn-pull-replay c0 (append j (fn-pull-journal-effects
                                                (fn-pull-close-effects r))))
                  (fn-pull-close r)))
  :hints (("Goal" :in-theory (disable fn-pull-advancesp fn-pull-completep)
           :do-not-induct t)))

; KEYSTONE (durable before the wire).  Suppose the journal replays to the
; cursor the owner holds for this peer.  Then after the begin's records the
; journal replays to the cursor the round asks with; after any events of the
; round (which journal nothing) still to it; and after the close's records
; to the closed cursor.  A process death at any cut of a round therefore
; recovers exactly the cursor that round asked with, or, once the close
; record is durable, the closed one.
(defthm fn-pull-journal-is-the-cursor-at-every-cut
  (implies (and (fn-pull-startable-cursorp c)
                (equal (fn-pull-replay c0 j) c))
           (let* ((r0 (fn-pull-begin c wildmat now bound))
                  (j0 (append j (fn-pull-journal-effects
                                 (fn-pull-begin-effects c now)))))
             (and (equal (fn-pull-replay c0 j0) (fn-pull-round-cursor r0))
                  (equal (fn-pull-replay
                          c0 (append j0 (fn-pull-journal-effects
                                         (mv-nth 1 (fn-pull-run r0 events)))))
                         (fn-pull-round-cursor (car (fn-pull-run r0 events))))
                  (equal (fn-pull-replay
                          c0 (append j0 (fn-pull-journal-effects
                                         (fn-pull-close-effects
                                          (car (fn-pull-run r0 events))))))
                         (fn-pull-close (car (fn-pull-run r0 events)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pull-run fn-pull-close fn-pull-advancesp
                               fn-pull-begin fn-pull-round-cursor
                               fn-pull-begin-effects)
           :use ((:instance fn-pull-begin-journal-replays-to-the-round)
                 (:instance fn-pull-close-journal-replays-to-the-close
                            (r (mv-nth 0 (fn-pull-run (fn-pull-begin c wildmat now bound)
                                                      events)))
                            (j (append j (fn-pull-journal-effects
                                          (fn-pull-begin-effects c now)))))
                 (:instance fn-pull-roundp-of-run
                            (r (fn-pull-begin c wildmat now bound)))
                 (:instance fn-pull-roundp-of-begin)))))

; KEYSTONE (recovery asks again).  The round begun from the recovered cursor
; after a crash anywhere in a round sends the same NEWNEWS as the round that
; died: its instant is the dead round's, so every Message-ID the peer listed
; to that round and the local node had not answered 235, 435 or 437 in a
; closed round is listed again by the peer's own NEWNEWS (RFC 3977 7.4).
(defthm fn-pull-recovery-asks-the-dead-rounds-newnews
  (implies (and (fn-pull-startable-cursorp c)
                (equal (fn-pull-replay c0 j) c))
           (let* ((r0 (fn-pull-begin c wildmat now bound))
                  (dead (car (fn-pull-run r0 events)))
                  (recovered
                   (fn-pull-replay
                    c0 (append j (fn-pull-journal-effects
                                  (fn-pull-begin-effects c now))
                               (fn-pull-journal-effects
                                (mv-nth 1 (fn-pull-run r0 events)))))))
             (equal (fn-pull-r-since (fn-pull-begin recovered wildmat later bound))
                    (fn-pull-r-since dead))))
  :hints (("Goal" :in-theory (disable fn-pull-run fn-pull-close
                                      fn-pull-advancesp)
           :use ((:instance fn-pull-journal-is-the-cursor-at-every-cut)))))

; -----------------------------------------------------------------------------
; FNPL: the cursor's journal frame
;
; Two record kinds in the generic frame grammar of books/frame:
; `(:pull-cursor peer since advances)' and (PRF-165) `(:pull-unavailable
; peer id count)'.  A cursor is journaled as one :pull-unavailable record per
; PENDING entry, in order, then its :pull-cursor record, which COMMITS them:
; replay stages unavailable records and a cursor record takes the staged
; ones as its PENDING (`fn-pull-records-fold'); records after the last
; cursor record are an uncommitted tail the open truncates
; (`fn-pull-journal-scan''s committed offset).  A journal written before
; PRF-165 is cursor records alone and replays to PENDING nil.  The grammar
; is (magic, version, kind, bounded length, payload,
; trailer), framed on disk by the FNFD envelope (`fn-feed-journal-prefix':
; a four-octet length before each frame).  The file is <store>/pull/ plus the
; FNFD filename codec's components for the peer.

; The small frame predicates and the spec machinery, as books/peer-feed
; opens them for FNFD; never the field grammar or the two codec entry points.
; Everything above this line is proved without them.
(local (in-theory (enable fn-frame-fields-vocabulary
                          fn-frame-octet-vocabulary
                          (:d fn-frame-magicp) (:d fn-frame-spec-for)
                          (:d fn-frame-specp) (:d fn-frame-spec-listp)
                          (:d fn-frame-digestp))))

(defconst *fn-pull-magic* '(70 78 80 76))   ; FNPL
(defconst *fn-pull-max-payload* 1024)
(defconst *fn-pull-kinds* '(:pull-cursor :pull-unavailable))
(defconst *fn-pull-specs* (list (cons :pull-cursor '(:text :nat :nat))
                                (cons :pull-unavailable '(:text :text :nat))))

; The placeholder a frame is encoded under before its trailer is computed
; over the protected prefix (books/frame-trailer `fn-frame-trailer').
(defconst *fn-pull-zero-digest*
  '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(defthm fn-pull-spec-for-is-spec-list
  (implies (not (equal (fn-frame-spec-for kind *fn-pull-specs*) :none))
           (fn-frame-spec-listp (fn-frame-spec-for kind *fn-pull-specs*))))

(defun fn-pull-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-pull-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values))))

(verify-guards fn-pull-record-okp)

(defun fn-pull-encode (kind values digest)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-pull-record-okp kind values) (fn-frame-digestp digest)))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-pull-kinds*)))
      (if (equal code 0)
          :bad
        (let ((payload (fn-frame-fields-octets
                        (fn-frame-spec-for kind *fn-pull-specs*) values)))
          (if (not (fn-cbor-at-mostp payload *fn-pull-max-payload*))
              :bad
            (fn-frame-encode *fn-pull-magic* *fn-frame-version* code
                             payload digest)))))))

(defun fn-pull-decode (octets digest)
  (declare (xargs :guard t :verify-guards nil))
  (let ((frame (fn-frame-decode octets digest *fn-pull-max-payload*)))
    (if (not (fn-frame-result-okp frame))
        frame
      (if (not (and (equal (fn-frame-result-magic frame) *fn-pull-magic*)
                    (equal (fn-frame-result-version frame)
                           *fn-frame-version*)))
          (fn-frame-error :magic)
        (let ((code (fn-frame-result-kind frame)))
          (if (or (not (posp code)) (< (len *fn-pull-kinds*) code))
              (fn-frame-error :kind)
            (let* ((kind (fn-frame-item (- code 1) *fn-pull-kinds*))
                   (spec (fn-frame-spec-for kind *fn-pull-specs*)))
              (if (equal spec :none)
                  (fn-frame-error :kind)
                (let ((parsed (fn-frame-fields-parse
                               spec (fn-frame-result-payload frame))))
                  (if (not (fn-frame-parse-okp parsed))
                      (fn-frame-error (fn-frame-parse-value parsed))
                    (if (not (fn-pull-record-okp
                              kind (fn-frame-parse-value parsed)))
                        (fn-frame-error :fields)
                      (fn-frame-ok *fn-pull-magic* *fn-frame-version*
                                   kind
                                   (fn-frame-parse-value parsed)))))))))))))

(defthm fn-pull-encode-frame-guard
  (implies (fn-pull-record-okp kind values)
           (and (fn-frame-spec-listp (fn-frame-spec-for kind *fn-pull-specs*))
                (fn-frame-values-okp (fn-frame-spec-for kind *fn-pull-specs*)
                                     values)
                (fn-cbor-octet-listp
                 (fn-frame-fields-octets
                  (fn-frame-spec-for kind *fn-pull-specs*) values))
                (fn-frame-magicp *fn-pull-magic*)
                (fn-cbor-octetp *fn-frame-version*)
                (fn-cbor-octetp (fn-frame-enum-index kind *fn-pull-kinds*))))
  :rule-classes nil)

(verify-guards fn-pull-encode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pull-encode-frame-guard)))))

(defthm fn-pull-decode-frame-guard
  (implies (fn-frame-result-okp
            (fn-frame-decode octets digest *fn-pull-max-payload*))
           (fn-cbor-octet-listp
            (fn-frame-result-payload
             (fn-frame-decode octets digest *fn-pull-max-payload*))))
  :rule-classes nil)

(verify-guards fn-pull-decode
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pull-decode-frame-guard)))))

; KEYSTONE (the value direction for FNPL).  Every cursor record the host
; writes decodes back to the kind and values it started from.
(defthm fn-pull-decode-of-encode
  (implies (and (fn-pull-record-okp kind values)
                (fn-frame-digestp digest)
                (not (equal (fn-pull-encode kind values digest) :bad)))
           (equal (fn-pull-decode (fn-pull-encode kind values digest) digest)
                  (fn-frame-ok *fn-pull-magic* *fn-frame-version* kind values)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pull-encode fn-pull-decode
                            fn-frame-fields-parse-of-octets
                            fn-frame-item-of-enum-index
                            fn-frame-enum-index-of-item
                            fn-frame-inputp fn-frame-item)
                           (fn-frame-decode fn-frame-encode
                            fn-frame-fields-parse fn-frame-fields-parse-aux
                            fn-frame-fields-octets)))))

; The sealed frame of a cursor, as the FNFD envelope carries it: protected
; prefix then trailer (books/frame-trailer), and nil for a cursor that is not
; a journaled one.
(defun fn-pull-sealed-frame (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unsealed (fn-pull-encode kind values *fn-pull-zero-digest*)))
    (if (not (fn-cbor-octet-listp unsealed))
        nil
      (let ((prefix (fn-frame-protected-prefix unsealed)))
        (append (fn-pull-list prefix) (fn-frame-trailer prefix))))))

(verify-guards fn-pull-sealed-frame)

; The :pull-cursor record's values: the cursor's first three fields.
(defun fn-pull-cursor-values (c)
  (declare (xargs :guard t))
  (list (fn-pull-cursor-peer c) (fn-pull-cursor-since c)
        (fn-pull-cursor-advances c)))

(defun fn-pull-cursor-frame (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-pull-cursorp c))
      nil
    (fn-pull-sealed-frame :pull-cursor (fn-pull-cursor-values c))))

(verify-guards fn-pull-cursor-frame)

(defun fn-pull-unavailable-frame (peer entry)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pull-sealed-frame :pull-unavailable
                        (list peer (if (consp entry) (car entry) nil)
                              (if (consp entry) (cdr entry) nil))))

(verify-guards fn-pull-unavailable-frame)

; -----------------------------------------------------------------------------
; The logical records of a journaled cursor, and their fold

(defun fn-pull-pending-records (peer pending)
  (declare (xargs :guard t))
  (if (consp pending)
      (cons (list :unavailable peer
                  (if (consp (car pending)) (car (car pending)) nil)
                  (if (consp (car pending)) (cdr (car pending)) nil))
            (fn-pull-pending-records peer (cdr pending)))
    nil))

(defun fn-pull-cursor-records (c)
  ; What `fn-pull-cursor-envelope' writes for C, as the scan reads it back.
  (declare (xargs :guard t))
  (if (fn-pull-cursorp c)
      (append (fn-pull-pending-records (fn-pull-cursor-peer c)
                                       (fn-pull-cursor-pending c))
              (list (list :cursor (fn-pull-cursor-peer c) (fn-pull-cursor-since c)
                          (fn-pull-cursor-advances c))))
    nil))

(defun fn-pull-journal-records (cursors)
  (declare (xargs :guard t))
  (if (consp cursors)
      (append (fn-pull-cursor-records (car cursors))
              (fn-pull-journal-records (cdr cursors)))
    nil))

; The fold the open performs: (committed . staged).  An unavailable record
; of the cursor's peer is staged; a cursor record of that peer commits the
; staged entries as its PENDING; any other record is ignored.
(defun fn-pull-records-fold (c staged records)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((x (car records)))
        (cond ((and (true-listp x) (equal (len x) 4) (equal (car x) :cursor)
                    (equal (cadr x) (fn-pull-cursor-peer c))
                    (fn-pull-cursorp (list (cadr x) (caddr x) (cadddr x)
                                           (revappend (fn-pull-list staged) nil))))
               (fn-pull-records-fold (list (cadr x) (caddr x) (cadddr x)
                                           (revappend (fn-pull-list staged) nil))
                                     nil (cdr records)))
              ((and (true-listp x) (equal (len x) 4) (equal (car x) :unavailable)
                    (equal (cadr x) (fn-pull-cursor-peer c)))
               (fn-pull-records-fold c (cons (cons (caddr x) (cadddr x)) staged)
                                     (cdr records)))
              (t (fn-pull-records-fold c staged (cdr records)))))
    (cons c staged)))

; KEYSTONE SUBJECT.  The cursor the open recovers from the scanned records
; (host/native/pull-service.lisp `fnn-pull-journal-open').
(defun fn-pull-records-replay (c records)
  (declare (xargs :guard t))
  (car (fn-pull-records-fold c nil records)))

(defthm fn-pull-records-fold-of-append
  (equal (fn-pull-records-fold c staged (append a b))
         (fn-pull-records-fold (car (fn-pull-records-fold c staged a))
                               (cdr (fn-pull-records-fold c staged a)) b)))

(defthm fn-pull-records-fold-of-pending-records
  (implies (and (fn-pull-pendingp pending)
                (equal peer (fn-pull-cursor-peer c)))
           (equal (fn-pull-records-fold c staged (fn-pull-pending-records peer pending))
                  (cons c (revappend pending staged))))
  :hints (("Goal" :in-theory (disable fn-pull-msgidp fn-pull-cursorp
                                      fn-pull-cursorp-of-cursor revappend-removal))))

(defthm fn-pull-records-fold-skips-another-peers-pending
  (implies (not (equal peer (fn-pull-cursor-peer c)))
           (equal (fn-pull-records-fold c staged (fn-pull-pending-records peer pending))
                  (cons c staged)))
  :hints (("Goal" :in-theory (disable fn-pull-cursorp fn-pull-cursorp-of-cursor))))

(defthm fn-pull-revappend-revappend
  (equal (revappend (revappend x y) z) (revappend y (append x z)))
  :hints (("Goal" :in-theory (disable revappend-removal))))

(defthm fn-pull-pendingp-true-listp
  (implies (fn-pull-pendingp p) (true-listp p))
  :rule-classes :forward-chaining)

(defthm fn-pull-cursorp-is-startable
  (implies (fn-pull-cursorp c) (fn-pull-startable-cursorp c))
  :hints (("Goal" :in-theory (enable fn-pull-cursorp fn-pull-startable-cursorp))))

(defthm fn-pull-records-fold-of-cursor-records
  (equal (fn-pull-records-fold c nil (fn-pull-cursor-records x))
         (if (and (fn-pull-cursorp x)
                  (equal (fn-pull-cursor-peer x) (fn-pull-cursor-peer c)))
             (cons x nil)
           (cons c nil)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pull-cursorp)
                           (fn-pull-pendingp fn-pull-pending-records revappend-removal
                            fn-pull-startable-cursor-is-its-fields
                            fn-pull-cursorp-is-startable))
           :use ((:instance fn-pull-startable-cursor-is-its-fields (c x))
                 (:instance fn-pull-cursorp-is-startable (c x))))))

(defthm fn-pull-records-fold-of-journal-records
  (equal (fn-pull-records-fold c nil (fn-pull-journal-records cursors))
         (cons (fn-pull-replay c cursors) nil))
  :hints (("Goal" :induct (fn-pull-replay c cursors)
           :in-theory (e/d (fn-pull-replay) (fn-pull-cursor-records fn-pull-cursorp)))))

; KEYSTONE (PRF-165, the FNPL refinement).  The records the open scans back
; from a journal of cursor appends fold to exactly the cursor the logical
; journal replays to: the per-id counts survive the reopen.
(defthm fn-pull-records-replay-is-the-replay
  (equal (fn-pull-records-replay c (fn-pull-journal-records cursors))
         (fn-pull-replay c cursors)))

(defun fn-pull-uncommittedp (records)
  ; No record in RECORDS is a cursor record: nothing in it commits.
  (declare (xargs :guard t))
  (if (consp records)
      (and (not (and (consp (car records)) (equal (car (car records)) :cursor)))
           (fn-pull-uncommittedp (cdr records)))
    t))

(defthm fn-pull-uncommittedp-of-pending-records
  (fn-pull-uncommittedp (fn-pull-pending-records peer pending)))

(defthm fn-pull-records-fold-of-uncommitted-keeps-the-cursor
  (implies (fn-pull-uncommittedp records)
           (equal (car (fn-pull-records-fold c staged records)) c))
  :hints (("Goal" :induct (fn-pull-records-fold c staged records)
           :in-theory (disable fn-pull-cursorp fn-pull-cursorp-of-cursor))))

; KEYSTONE (PRF-165, an uncommitted tail).  The unavailable records of a
; cursor whose own record never became durable change nothing: the open
; recovers the cursor before that append (and truncates them).
(defthm fn-pull-records-replay-ignores-an-uncommitted-tail
  (equal (fn-pull-records-replay
          c (append (fn-pull-journal-records cursors)
                    (fn-pull-pending-records peer pending)))
         (fn-pull-replay c cursors))
  :hints (("Goal" :in-theory (disable fn-pull-pending-records fn-pull-journal-records))))


(defun fn-pull-journal-open-frame (frame)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-cbor-octet-listp frame))
      (fn-frame-error :octets)
    (fn-pull-decode frame
      (fn-frame-trailer (fn-frame-protected-prefix frame)))))

(verify-guards fn-pull-journal-open-frame)

; KEYSTONE SUBJECT.  One bounded read of an FNPL file at open
; (host/native/pull-service.lisp `fnn-pull-journal-open'): (status
; safe-offset record committed).  The prefix plan is FNFD's; the safe offset
; advances only over a complete verified frame of this peer; COMMITTED
; advances only over a cursor record (PRF-165) and is the sole truncate
; authority, so a torn final append, or the unavailable records of a cursor
; whose own record never became durable, is repaired to the previous
; cursor.  RECORD is `(:cursor peer since advances)' or `(:unavailable peer
; id count)'.
(defun fn-pull-journal-scan (peer prefix frame offset committed)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plan (fn-feed-journal-prefix prefix))
        (committed (nfix committed)))
    (cond ((equal plan :end)
           (if (equal committed (nfix offset))
               (list :end committed nil committed)
             (list :repair committed nil committed)))
          ((equal plan :repair) (list :repair committed nil committed))
          ((not (natp plan)) (list :invalid (nfix offset) nil committed))
          ((< (len frame) plan) (list :repair committed nil committed))
          ((not (equal (len frame) plan))
           (list :invalid (nfix offset) nil committed))
          (t (let* ((decoded (fn-pull-journal-open-frame frame))
                    (kind (fn-frame-result-kind decoded))
                    (v (fn-frame-result-payload decoded))
                    (next (+ (nfix offset) *fn-feed-journal-prefix-size* plan)))
               (cond ((not (and (fn-frame-result-okp decoded)
                                (true-listp v) (equal (len v) 3)
                                (equal (car v) peer)
                                (fn-feed-namep peer)))
                      (list :invalid (nfix offset) nil committed))
                     ((and (equal kind :pull-cursor)
                           (natp (cadr v)) (natp (caddr v)))
                      (list :next next (cons :cursor v) next))
                     ((and (equal kind :pull-unavailable)
                           (fn-pull-msgidp (cadr v)) (posp (caddr v)))
                      (list :next next (cons :unavailable v) committed))
                     (t (list :invalid (nfix offset) nil committed))))))))

(verify-guards fn-pull-journal-scan)

; -----------------------------------------------------------------------------
; Which peers are pulled, from the live configuration
;
; A peer is pulled when its group has a positive `pull-interval' row
; (seconds; `peer pull NAME SECONDS', books/native-admin-peer.lisp), an NNTP
; transport, and an inbound record: the NEWNEWS wildmat is the peer's own
; inbound accept-groups, so a pull asks for exactly what this node would
; accept from that peer if it pushed.
;
; The plan carries the transport's security and the peer's outbound
; credential policy as the configuration states them; whether the round may
; use them is `fn-pull-plan-verdict' (books/peer-pull-session.lisp), decided
; before any connection.  A TLS transport whose server name or trust anchor
; row is missing denotes no security and is not planned.
;
; A plan: (peer-octets host-octets port wildmat-octets interval-ms
;          security auth bound), BOUND the peer's `pull-unavailable-rounds'
; row or `*fn-pull-default-unavailable-rounds*' (PRF-165), SECURITY `(:clear)' or `(:tls MODE SERVER-NAME
; TRUST-ANCHOR)' with MODE :starttls or :implicit, AUTH nil or
; `(:authinfo PROFILE-PATH ALLOW-CLEAR)'.

(defun fn-pull-security-of-rows (rows)
  (declare (xargs :guard t))
  (let ((ts (fn-cfg-peer-slot rows "transport-security"))
        (sn (fn-cfg-peer-slot rows "transport-server-name"))
        (ta (fn-cfg-peer-slot rows "transport-trust-anchor")))
    (cond ((or (null ts) (equal (fn-cfg-row-c ts) "clear")) (list :clear))
          ((and (member-equal (fn-cfg-row-c ts) '("starttls" "implicit"))
                sn ta (stringp (fn-cfg-row-c sn)) (stringp (fn-cfg-row-c ta)))
           (list :tls (if (equal (fn-cfg-row-c ts) "implicit") :implicit :starttls)
                 (fn-cfg-row-c sn) (fn-cfg-row-c ta)))
          (t nil))))

(defun fn-pull-auth-of-rows (rows)
  (declare (xargs :guard t))
  (let ((oa (fn-cfg-peer-slot rows "outbound-auth-profile")))
    (if (and oa (stringp (fn-cfg-row-c oa)))
        (list :authinfo (fn-cfg-row-c oa) (equal (fn-cfg-row-n oa) 1))
      nil)))

(defun fn-pull-plan-of-rows (name rows)
  (declare (xargs :guard t))
  (let ((tn (fn-cfg-peer-slot rows "transport-nntp"))
        (ig (fn-cfg-peer-slot rows "inbound-groups"))
        (seconds (fn-pcb-slot-natural *fn-pcb-pull-interval-slot* rows))
        (rounds (fn-pcb-slot-natural *fn-pcb-pull-unavailable-slot* rows))
        (security (fn-pull-security-of-rows rows)))
    (if (and (stringp name) tn ig (posp seconds)
             (stringp (fn-cfg-row-c tn)) (posp (fn-cfg-row-n tn))
             (stringp (fn-cfg-row-c ig))
             security)
        (list (fn-record-string-octets name)
              (fn-record-string-octets (fn-cfg-row-c tn))
              (fn-cfg-row-n tn)
              (fn-record-string-octets (fn-cfg-row-c ig))
              (* 1000 seconds)
              security
              (fn-pull-auth-of-rows rows)
              (if (posp rounds) rounds *fn-pull-default-unavailable-rounds*))
      nil)))

(defun fn-pull-plans-of (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((plan (fn-pull-plan-of-rows (car names)
                                        (fn-cfg-rows-with-key peers (car names)))))
        (if plan
            (cons plan (fn-pull-plans-of (cdr names) peers))
          (fn-pull-plans-of (cdr names) peers)))
    nil))

; KEYSTONE SUBJECT.  The pulled peers of a configuration's peer rows
; (host/owner-host.lisp `fn-owner-pull-plans').
(defun fn-pull-plans (peers)
  (declare (xargs :guard t))
  (fn-pull-plans-of (fn-cfg-peer-names peers) peers))

(defun fn-pull-plan-peer (p) (declare (xargs :guard t)) (fn-pull-at 0 p))
(defun fn-pull-plan-host (p) (declare (xargs :guard t)) (fn-pull-at 1 p))
(defun fn-pull-plan-port (p) (declare (xargs :guard t)) (fn-pull-at 2 p))
(defun fn-pull-plan-wildmat (p) (declare (xargs :guard t)) (fn-pull-at 3 p))
(defun fn-pull-plan-interval (p) (declare (xargs :guard t)) (fn-pull-at 4 p))
(defun fn-pull-plan-security (p) (declare (xargs :guard t)) (fn-pull-at 5 p))
(defun fn-pull-plan-auth (p) (declare (xargs :guard t)) (fn-pull-at 6 p))
(defun fn-pull-plan-bound (p) (declare (xargs :guard t)) (fn-pull-at 7 p))

; The schedule the owner holds, reconfigured from the live plans at NOW.
(defun fn-pull-schedule (plans now tbl)
  (declare (xargs :guard t))
  (if (consp plans)
      (fn-pull-schedule (cdr plans) now
                        (fn-sched-pull-configure
                         (fn-pull-plan-peer (car plans))
                         (fn-pull-plan-interval (car plans)) now tbl))
    tbl))

(defun fn-pull-plan-for (peer plans)
  (declare (xargs :guard t))
  (if (consp plans)
      (if (equal (fn-pull-plan-peer (car plans)) peer)
          (car plans)
        (fn-pull-plan-for peer (cdr plans)))
    nil))

; -----------------------------------------------------------------------------
; The host's entry points that return one value (the native bridge takes the
; first value of a call), and the envelope an FNPL frame is appended in.

(defun fn-pull-step-pair (r event)
  (declare (xargs :guard t))
  (mv-let (r2 effects) (fn-pull-step r event) (list r2 effects)))

(defun fn-pull-journal-prefix-size ()
  (declare (xargs :guard t))
  *fn-feed-journal-prefix-size*)

; A frame this node may append: a complete verified FNPL cursor frame, behind
; its four-octet length.  Anything else is :bad and is never written.
(defun fn-pull-journal-wrap (frame)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-cbor-octet-listp frame)
                (<= (len frame) *fn-feed-journal-frame-max*)
                (fn-frame-result-okp (fn-pull-journal-open-frame frame))))
      :bad
    (append (fn-cbor-u32-bytes (len frame)) frame)))

(verify-guards fn-pull-journal-wrap)

(defun fn-pull-pending-envelope (peer pending)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pending)
      (let ((w (fn-pull-journal-wrap (fn-pull-unavailable-frame peer (car pending))))
            (rest (fn-pull-pending-envelope peer (cdr pending))))
        (if (or (equal w :bad) (equal rest :bad))
            :bad
          (append w rest)))
    nil))

(verify-guards fn-pull-pending-envelope)

(defthm fn-pull-pending-envelope-true-listp
  (implies (not (equal (fn-pull-pending-envelope peer pending) :bad))
           (true-listp (fn-pull-pending-envelope peer pending)))
  :hints (("Goal" :in-theory (disable fn-pull-journal-wrap
                                      fn-pull-unavailable-frame))))

; KEYSTONE SUBJECT.  The octets one cursor append writes
; (host/native/pull-service.lisp `fnn-pull-journal-append'): one wrapped
; :pull-unavailable frame per PENDING entry, then the wrapped :pull-cursor
; frame that commits them, or :bad (never written).  The host writes them in
; one write and one fsync, so the crash cuts of an append are unchanged.
(defun fn-pull-cursor-envelope (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-pull-cursorp c))
      :bad
    (let ((p (fn-pull-pending-envelope (fn-pull-cursor-peer c)
                                       (fn-pull-cursor-pending c)))
          (w (fn-pull-journal-wrap (fn-pull-cursor-frame c))))
      (if (or (equal p :bad) (equal w :bad))
          :bad
        (append p w)))))

(verify-guards fn-pull-cursor-envelope
  :hints (("Goal" :in-theory (disable fn-pull-pending-envelope
                                      fn-pull-journal-wrap fn-pull-cursor-frame))))

(defun fn-pull-done-p (r)
  (declare (xargs :guard t))
  (and (member-equal (fn-pull-r-phase r) '(:done :failed)) t))

(defun fn-pull-dropped-words (ids)
  (declare (xargs :guard t))
  (if (consp ids)
      (append (fn-record-string-octets " dropped=")
              (fn-pull-list (car ids))
              (fn-pull-dropped-words (cdr ids)))
    nil))

; The owner log line of a closed round: the peer, how it ended, whether the
; cursor moved, how many listed ids the peer could not produce, and each id
; dropped in this round (its count reached the bound).
(defun fn-pull-log-line (r)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "pull peer=")
          (fn-pull-list (fn-pull-r-peer r))
          (fn-record-string-octets
           (if (equal (fn-pull-r-phase r) :done) " round=done" " round=failed"))
          (fn-record-string-octets
           (if (fn-pull-advancesp r) " cursor=advanced" " cursor=held"))
          (if (consp (fn-pull-r-unavailable r))
              (append (fn-record-string-octets " unavailable=")
                      (fn-nntp-decimal-field (len (fn-pull-r-unavailable r))))
            nil)
          (fn-pull-dropped-words (fn-pull-dropped r))))
