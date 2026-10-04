; fn: catching up from a peer -- the requesting half (PRF-325, NNT-053;
; specs/peering.md "Catching up from a peer").
;
; A node that is new, or has been away, fetches a peer's articles as the
; batches of XFNCATCHUP (books/peer-catchup-serve.lisp) instead of one
; NEWNEWS listing and one ARTICLE per Message-ID.  This book holds the
; session (the pull's preamble), the cursor and its FNCU journal; the round
; itself is the bounded spool controller (books/peer-catchup-spool.lisp):
; each batch is streamed through 512-octet windows into a private spool, its
; digest chain recomputed record by record and compared with the peer's
; claim, and only then are its records replayed from the spool and offered,
; one at a time and oldest first, to THIS node by IHAVE on the logical
; transit connection of that peer: the node's own prepare and verdict path
; decides each one, exactly as for a push from that peer.  Catch-up imports
; articles and their provenance (the Path the local acceptance extends); it
; never carries the peer's article numbers, never installs anything itself,
; and a peer's cancel arrives as an offered article that the local verdict
; decides like any other.
;
; The session is the pull's (books/peer-pull-session.lisp): the feed's
; protected preamble (STARTTLS, the verified handshake, AUTHINFO from the
; outbound credential profile) decided by `fn-pull-plan-verdict', then this
; round in place of the NEWNEWS round.  The host drives both with the same
; effect vocabulary (host/native/pull-service.lisp, through `fn-csp-step'):
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
; What is proved here (the host calls `fn-cu-cursor-envelope',
; `fn-cu-journal-scan' and `fn-cu-records-replay'; the round's keystones are
; in books/peer-catchup-spool.lisp and its framer):
;   fn-cu-records-replay-is-the-last-cursor   the open recovers the last
;       journaled cursor (a torn tail is truncated to it)
;   fn-cu-resume-asks-from-the-journaled-cursor   a round begun from the
;       recovered cursor asks the peer from exactly that position and chain
;   fn-cu-decode-of-encode   an FNCU record round-trips
(in-package "ACL2")
(include-book "peer-pull-session")
(include-book "peer-catchup-serve")

; -----------------------------------------------------------------------------
; Policy

; The quantum a requester asks for (octets of article per batch beyond the
; first record): local policy. A batch is spooled whole before any record is
; offered, so it bounds the spool one round needs (the peer flight allowance).
(defconst *fn-cu-request-quantum* 262144)

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

(defun fn-cu-record-msgid (rec) (declare (xargs :guard t)) (if (consp rec) (car rec) nil))

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

; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-cu-obs-effects-loop (obs fc security round acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp obs)
      (fn-cu-obs-effects-loop (cdr obs)
                              fc
                              security
                              round
                              (fn-ag-rev-onto (fn-cu-obs-effect (fn-fc-obs-kind (car obs))
                                                                fc
                                                                security
                                                                round)
                                              acc))
    (revappend acc nil)))

(defun fn-cu-obs-effects (obs fc security round)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp obs)
           (append (fn-cu-obs-effect (fn-fc-obs-kind (car obs)) fc security round)
                   (fn-cu-obs-effects (cdr obs) fc security round))
         nil)
       :exec (fn-cu-obs-effects-loop obs fc security round nil)))

(local
 (defthm fn-cu-obs-effects-loop-rev-onto-append
   (equal (revappend (fn-ag-rev-onto x acc) y)
          (revappend acc (append x y)))))

(local
 (defthm fn-cu-obs-effects-loop-is-revappend
   (equal (fn-cu-obs-effects-loop obs fc security round acc)
          (revappend acc (fn-cu-obs-effects obs fc security round)))
   :hints (("Goal" :induct (fn-cu-obs-effects-loop obs fc security round acc)
                   :in-theory (union-theories '(fn-cu-obs-effects-loop fn-cu-obs-effects revappend car-cons cdr-cons fn-cu-obs-effects-loop-rev-onto-append)
                                              (theory 'minimal-theory))))))

(verify-guards fn-cu-obs-effects-loop)

(verify-guards fn-cu-obs-effects
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-cu-obs-effects)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-cu-obs-effects-loop-is-revappend (acc nil))))))

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

; One event of a catch-up session's preamble (books/peer-catchup-spool.lisp
; `fn-csp-step' sends it only these, until the session is ready).  Once ready
; the round belongs to the spool controller: an event here changes nothing.
(defun fn-cu-session-step (s event)
  (declare (xargs :guard t))
  (let ((fc (fn-cu-s-fc s))
        (round (fn-cu-s-round s))
        (security (fn-cu-s-security s)))
    (cond ((fn-cu-done-p round) (mv s nil))
          ((fn-cu-session-readyp s) (mv s nil))
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

; Executes by a loop (lane depth-debt, PRF-919): NAMES are the configured
; peers, operator data with no fixed cap (D27).  (mbe :logic <the recursion,
; unchanged> :exec <a loop>), equal by fn-cu-plans-of-loop-is-rev-onto
; (books/rev-onto.lisp).
(defun fn-cu-plans-of-loop (names peers acc)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-cu-plans-of-loop
       (cdr names) peers
       (let ((plan (fn-cu-plan-of-rows (car names)
                    (fn-cfg-rows-with-key peers (car names)))))
         (if plan (cons plan acc) acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-cu-plans-of (names peers)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp names)
           (let ((plan (fn-cu-plan-of-rows (car names)
                        (fn-cfg-rows-with-key peers (car names)))))
             (if plan
                 (cons plan (fn-cu-plans-of (cdr names) peers))
               (fn-cu-plans-of (cdr names) peers)))
         nil)
       :exec (fn-cu-plans-of-loop names peers nil)))

(defthm fn-cu-plans-of-loop-is-rev-onto
  (equal (fn-cu-plans-of-loop names peers acc)
         (fn-ag-rev-onto acc (fn-cu-plans-of names peers)))
  :hints (("Goal" :induct (fn-cu-plans-of-loop names peers acc)
                  :in-theory (union-theories
                              '(fn-cu-plans-of-loop fn-cu-plans-of
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-cu-plans-of
  :hints (("Goal" :in-theory (union-theories
                              '(fn-cu-plans-of fn-ag-rev-onto
                                fn-cu-plans-of-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

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
