; fn: the articles a node holds in flight, admitted within the slots its
; dynamic space was sized for (lane zero-copy-commit, 2026-09-28; D27).
;
; A connection in the middle of an article retains the body until its
; terminator (books/wire.lisp body-rev), and a connection whose article has
; arrived holds its submission in the owner's queue or the batch in flight
; until the commit answers it.  Each is the per-connection heap term that
; grows with the profile's article limit A (at A = 11 MiB, 383 MB of octet
; lists a connection), and before this book nothing bounded how many there
; were: books/connection-budget.lisp charged them to the machine, not to the
; dynamic space, so enough concurrent posters of large articles exhausted
; the heap and the node faulted (exit 4).
;
; books/heap-store-figure.lisp now holds `fn-heap-article-slots' articles in
; flight in the figure the launcher reserves (fn-heap-articles-octets); this
; book keeps what the owner holds (`fn-oas-held': the connections in article
; mode, the queued submissions and the batch in flight) within that many
; across every read.  The host installs the slots once per run
; (host/owner-host.lisp fn-owner-connection-budget, from the store's
; profile) and every served read runs `fn-oas-read-span':
;
;   - the read as the host ran it before (books/owner-time-admission.lisp
;     fn-otm-read-span); it stands unless it is OVER (fn-oas-over-p): the
;     owner then holds more than the slots and more than before the read,
;     or connection ID entered article mode in it.  A read can raise what
;     the owner holds without leaving ID in article mode: a TAKETHIS (RFC
;     4644 section 2.5 streams the command and the article with no wait), a
;     pipelined IHAVE or POST, or any small article arriving within one
;     socket read enters article mode and completes the article in the one
;     read, leaving ID in command mode with one more submission queued;
;   - past the slots, the first of three tiers the slots hold (fn-oas-tiers):
;     (a) the read again from the same owner with ID's posting bit off: a
;     POST is answered 440 at the command (RFC 3977 section 6.3.1: the client
;     sends no article), with this book's reason line in place of the generic
;     text when the connection's own configuration permits posting; (b) that
;     read with ID's wire then closed, answered 400 and closed (RFC 3977
;     section 3.2.1: 400 may answer any command, and the client retries
;     later): the article it entered is dropped, what it completed before is
;     kept; (c) the whole read refused: nothing it carried is taken, ID's
;     wire is closed, 400 and close.  A connection already in article mode
;     skips (a): its read runs as it would.  The body past the slots is never
;     retained.
;
; `fn-oas-read-span-held-step' (no hypothesis): after the host's read the
; owner holds at most the slots or at most what it held before.
; KEYSTONE `fn-oas-read-span-admits-within-the-slots' (no hypothesis): after
; the host's read, if connection ID is in article mode and was not before,
; the owner holds at most SLOTS articles in flight.
; `fn-oas-read-span-when-held-unfolds': a read the slots hold is the read
; before this book exactly (every theorem about fn-otm-read-span is about the
; host's call there).
; books/owner-article-held.lisp carries the invariant across reads (held <=
; slots), the frame (a read of ID leaves every other connection's record)
; and the completion policy, RESERVE-TO-FINISH: a slot is the whole
; article's worst case (fn-heap-article-reserve-octets), taken at entry into
; article mode, so the reads of an admitted connection that continue or
; complete its article are never refused by the slots, and an admitted
; upload completes (or is refused by name past the body limit) without
; waiting for any other.  A stalled upload holds its slot until the
; connection's idle timeout closes it.
;
; The subject is fn-oas-read-span, which host/owner-host.lisp
; fn-owner-chunk-span-at calls with the slots it installed.
;
; Not claimed here: the queue's growth by the control channel and BP
; deliveries, which enter no connection's article mode (their heap is the
; figure's in-flight request).

(in-package "ACL2")
(include-book "owner-time-admission")

; -----------------------------------------------------------------------------
; What the owner holds in flight.

(defun fn-oas-conn-articlep (c)
  (declare (xargs :guard t))
  (equal (fn-wire-state-mode (fn-own-conn-wire c)) :article))

; A loop (tail recursive): one control-stack frame whatever the count.
(defun fn-oas-article-conns-onto (conns n)
  (declare (xargs :guard (natp n)))
  (if (consp conns)
      (fn-oas-article-conns-onto (cdr conns)
                                 (if (fn-oas-conn-articlep (car conns)) (+ 1 n) n))
    n))

(defun fn-oas-article-conns (conns)
  (declare (xargs :guard t))
  (fn-oas-article-conns-onto conns 0))

(defthm fn-oas-article-conns-onto-natp
  (implies (natp n) (natp (fn-oas-article-conns-onto conns n)))
  :rule-classes :type-prescription)

(defthm fn-oas-article-conns-natp
  (natp (fn-oas-article-conns conns))
  :rule-classes :type-prescription)

(defun fn-oas-held (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (+ (fn-oas-article-conns (fn-own-conns o))
       (len (fn-own-queue o))
       (len (fn-own-inflight o)))))

(defun fn-oas-articlep (oc id)
  (declare (xargs :guard t))
  (let ((c (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (and c (fn-oas-conn-articlep c) t)))

;; A read over OC that left OC1 is OVER when the owner then holds more than
;; SLOTS and either holds more than before the read or connection ID entered
;; article mode in it.  The first disjunct is the invariant's (a read that
;; raises what the owner holds may not raise it past the slots, whichever
;; way the article arrived: a TAKETHIS stream, a pipelined IHAVE or POST, a
;; small article within one socket read, each entering article mode and
;; completing the article in the one read); the second keeps the entry test
;; this book began with.
(defun fn-oas-over-p (oc oc1 id slots)
  (declare (xargs :guard t))
  (and (< (nfix slots) (fn-oas-held oc1))
       (or (< (fn-oas-held oc) (fn-oas-held oc1))
           (and (not (fn-oas-articlep oc id))
                (fn-oas-articlep oc1 id)))))

; -----------------------------------------------------------------------------
; The refusal.

(defconst *fn-oas-post-line*
  (fn-nntp-crlf (fn-nntp-string-octets
                 "440 posting not permitted now; the articles in flight fill the memory, try again later")))

(defconst *fn-oas-busy-line*
  (fn-nntp-crlf (fn-nntp-string-octets
                 "400 the articles in flight fill the memory; try again later")))

; Each generic 440 becomes this book's line; every other effect as it is.
; A loop onto an accumulator, reversed at the end (tail recursive).
(defun fn-oas-post-effects-onto (effects acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp effects)
      (fn-oas-post-effects-onto
       (cdr effects)
       (cons (if (equal (car effects) *fn-otm-generic-440*)
                 (fn-nntp-reply-effect *fn-oas-post-line*)
               (car effects))
             acc))
    (revappend acc nil)))

(defun fn-oas-post-effects (effects)
  (declare (xargs :guard t))
  (fn-oas-post-effects-onto effects nil))

; Connection ID's wire closed (its retained input dropped), every other
; field and connection as it is.
(defun fn-oas-conn-closed (c)
  (declare (xargs :guard t))
  (update-nth 3 (fn-wire-result-state
                 (fn-wire-make-result
                  (fn-wire-make-state :closed nil 0 nil nil 0
                                      (fn-wire-state-line-limit (fn-own-conn-wire c))
                                      (fn-wire-state-body-limit (fn-own-conn-wire c)))
                  nil))
              (true-list-fix c)))

(defun fn-oas-owner-closed (oc id)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (c (fn-own-find-conn id (fn-own-conns o))))
    (if c
        (fn-ocfg-with-owner
         oc (fn-own-set-conns o (fn-own-replace-conn (fn-oas-conn-closed c) (fn-own-conns o))))
      oc)))

;; Tier (a): the read from OC with ID's posting bit off and restored after;
;; a POST is refused 440 at the command, with this book's reason line when
;; the connection's own configuration permits posting.
(defun fn-oas-posting-off-read (oc views id i end cache s fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let* ((allow (fn-otm-conn-allow oc id))
         (r (fn-otm-read-span (fn-otm-owner-with-allow oc id nil) views id i end cache s
                              fn-octets fn-arena fn-cat)))
    (fn-own-tls-make-result
     (fn-own-tls-result-consumed r)
     (if allow
         (fn-oas-post-effects (fn-own-tls-result-effects r))
       (fn-own-tls-result-effects r))
     (fn-otm-owner-with-allow (fn-own-tls-result-owner r) id allow)
     (fn-own-tls-result-repinned r))))

;; Tier (b): the read R as it ran, connection ID's wire then closed (the
;; article it entered dropped, whatever the read completed before it kept)
;; and the read answered 400 and closed.
(defun fn-oas-close-result (r id)
  (declare (xargs :guard t))
  (fn-own-tls-make-result
   (fn-own-tls-result-consumed r)
   (append (true-list-fix (fn-own-tls-result-effects r))
           (list (fn-nntp-reply-effect *fn-oas-busy-line*)
                 (fn-nntp-close-effect)))
   (fn-oas-owner-closed (fn-own-tls-result-owner r) id)
   (fn-own-tls-result-repinned r)))

;; Tier (c): the whole read refused.  Nothing it carried is taken: the owner
;; is OC with ID's wire closed, the span is consumed, and the answer is 400
;; and close (RFC 3977 section 3.2.1).
(defun fn-oas-whole-refusal (oc id i end)
  (declare (xargs :guard t))
  (fn-own-tls-make-result (nfix (- (nfix end) (nfix i)))
                          (list (fn-nntp-reply-effect *fn-oas-busy-line*)
                                (fn-nntp-close-effect))
                          (fn-oas-owner-closed oc id)
                          nil))

;; The first of R1, R1 closed, the whole refusal that the slots hold.
(defun fn-oas-tiers (oc r1 id i end slots)
  (declare (xargs :guard t))
  (cond ((not (fn-oas-over-p oc (fn-own-tls-result-owner r1) id slots)) r1)
        ((and (fn-oas-articlep (fn-own-tls-result-owner r1) id)
              (not (fn-oas-over-p oc (fn-own-tls-result-owner (fn-oas-close-result r1 id))
                                  id slots)))
         (fn-oas-close-result r1 id))
        (t (fn-oas-whole-refusal oc id i end))))

; THE READ THE HOST CALLS (host/owner-host.lisp fn-owner-chunk-span-at).
; A connection already in article mode (admitted: its slot is its whole
; article's) never takes tier (a): its read runs as it would, and past the
; slots only the article it began after completing its own is closed
; (books/owner-article-held.lisp fn-oah-read-span-never-blocks-an-admitted-
; article shows tier (c) is unreachable for it).
(defun fn-oas-read-span (oc views id i end cache s slots fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((r (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))
    (cond ((not (fn-oas-over-p oc (fn-own-tls-result-owner r) id slots)) r)
          ((fn-oas-articlep oc id) (fn-oas-tiers oc r id i end slots))
          (t (fn-oas-tiers oc (fn-oas-posting-off-read oc views id i end cache s
                                                       fn-octets fn-arena fn-cat)
                           id i end slots)))))

; -----------------------------------------------------------------------------
; The theorems.

;; A read the slots hold is the read before this book.
(defthm fn-oas-read-span-when-held-unfolds
  (implies (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                   (fn-otm-read-span oc views id i end cache s fn-octets
                                                     fn-arena fn-cat))
                               id slots))
           (equal (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat)
                  (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (union-theories '(fn-oas-read-span) (theory 'minimal-theory)))))

(local
 (defthm fn-oas-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(local
 (defthm fn-oas-conns-of-set-conns
   (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
   :hints (("Goal" :in-theory (enable fn-own-conns fn-own-set-conns fn-own-make)))))

(local
 (defthm fn-oas-find-conn-of-replace-same
   (implies (and (fn-own-find-conn id conns) (equal (fn-own-conn-id c) id))
            (equal (fn-own-find-conn id (fn-own-replace-conn c conns)) c))
   :hints (("Goal" :in-theory (enable fn-own-find-conn fn-own-replace-conn)))))

(local
 (defthm fn-oas-find-conn-id
   (implies (fn-own-find-conn id conns)
            (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))
   :hints (("Goal" :in-theory (enable fn-own-find-conn)))))

; The fourth field of a record of the owner's shape, replaced.
(local
 (defthm fn-oas-update-nth-3-shape
   (and (equal (car (update-nth 3 v c)) (car c))
        (equal (car (cdr (cdr (cdr (update-nth 3 v c))))) v))
   :hints (("Goal" :expand ((update-nth 3 v c) (update-nth 2 v (cdr c))
                            (update-nth 1 v (cddr c)) (update-nth 0 v (cdddr c)))
            :in-theory (disable update-nth)))))

(local
 (defthm fn-oas-car-of-true-list-fix
   (equal (car (true-list-fix c)) (car c))))

(defthm fn-oas-conn-closed-id
  (equal (fn-own-conn-id (fn-oas-conn-closed c)) (fn-own-conn-id c))
  :hints (("Goal" :in-theory (union-theories '(fn-own-conn-id fn-oas-conn-closed
                                               fn-oas-car-of-true-list-fix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-oas-update-nth-3-shape
                            (c (true-list-fix c))
                            (v (fn-wire-result-state
                                (fn-wire-make-result
                                 (fn-wire-make-state :closed nil 0 nil nil 0
                                                     (fn-wire-state-line-limit (fn-own-conn-wire c))
                                                     (fn-wire-state-body-limit (fn-own-conn-wire c)))
                                 nil))))))))

(defthm fn-oas-conn-closed-is-not-article
  (not (fn-oas-conn-articlep (fn-oas-conn-closed c)))
  :hints (("Goal" :in-theory (e/d (fn-oas-conn-closed fn-oas-conn-articlep fn-own-conn-wire)
                                  (update-nth))
           :use ((:instance fn-oas-update-nth-3-shape
                            (c (true-list-fix c))
                            (v (fn-wire-result-state
                                (fn-wire-make-result
                                 (fn-wire-make-state :closed nil 0 nil nil 0
                                                     (fn-wire-state-line-limit (fn-own-conn-wire c))
                                                     (fn-wire-state-body-limit (fn-own-conn-wire c)))
                                 nil))))))))

(defthm fn-oas-owner-closed-is-not-article
  (not (fn-oas-articlep (fn-oas-owner-closed oc id) id))
  :hints (("Goal" :in-theory (e/d (fn-oas-owner-closed fn-oas-articlep)
                                  (fn-oas-conn-articlep fn-oas-conn-closed
                                   fn-own-replace-conn fn-own-find-conn)))))

;; Tiers (b) and (c) never leave ID in article mode.
(defthm fn-oas-refusals-are-not-article
  (and (not (fn-oas-articlep (fn-own-tls-result-owner (fn-oas-close-result r id)) id))
       (not (fn-oas-articlep (fn-own-tls-result-owner (fn-oas-whole-refusal oc id i end)) id)))
  :hints (("Goal" :in-theory (e/d (fn-oas-close-result fn-oas-whole-refusal)
                                  (fn-oas-articlep fn-oas-owner-closed)))))

; -----------------------------------------------------------------------------
; What closing a connection does to what the owner holds.

(local
 (defun fn-oas-count (conns)
   (if (consp conns)
       (+ (if (fn-oas-conn-articlep (car conns)) 1 0) (fn-oas-count (cdr conns)))
     0)))

(local
 (defthm fn-oas-article-conns-onto-is-count
   (implies (acl2-numberp n)
            (equal (fn-oas-article-conns-onto conns n) (+ n (fn-oas-count conns))))
   :hints (("Goal" :in-theory (disable fn-oas-conn-articlep)))))

(local
 (defthm fn-oas-count-of-replace-not-article
   (implies (not (fn-oas-conn-articlep c))
            (<= (fn-oas-count (fn-own-replace-conn c conns)) (fn-oas-count conns)))
   :hints (("Goal" :in-theory (disable fn-oas-conn-articlep)))
   :rule-classes :linear))

(local
 (defthm fn-oas-queue-of-set-conns
   (and (equal (fn-own-queue (fn-own-set-conns o conns)) (fn-own-queue o))
        (equal (fn-own-inflight (fn-own-set-conns o conns)) (fn-own-inflight o)))
   :hints (("Goal" :in-theory (enable fn-own-queue fn-own-inflight fn-own-set-conns fn-own-make)))))

;; Closing connection ID never raises what the owner holds.
(defthm fn-oas-owner-closed-held
  (<= (fn-oas-held (fn-oas-owner-closed oc id)) (fn-oas-held oc))
  :hints (("Goal" :in-theory (e/d (fn-oas-owner-closed fn-oas-held fn-oas-article-conns)
                                  (fn-oas-conn-articlep fn-oas-conn-closed
                                   fn-own-replace-conn fn-own-find-conn fn-own-set-conns))))
  :rule-classes :linear)

(defthm fn-oas-whole-refusal-held
  (<= (fn-oas-held (fn-own-tls-result-owner (fn-oas-whole-refusal oc id i end)))
      (fn-oas-held oc))
  :hints (("Goal" :in-theory (e/d (fn-oas-whole-refusal) (fn-oas-held fn-oas-owner-closed))))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The per-read step.

;; A result of the tiers is one the slots hold, or the whole refusal.
(defthm fn-oas-tiers-cases
  (let ((r (fn-oas-tiers oc r1 id i end slots)))
    (or (not (fn-oas-over-p oc (fn-own-tls-result-owner r) id slots))
        (equal r (fn-oas-whole-refusal oc id i end))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oas-tiers) (fn-oas-over-p fn-oas-close-result
                                                  fn-oas-whole-refusal)))))

(defthm fn-oas-read-span-cases
  (let ((r (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat)))
    (or (not (fn-oas-over-p oc (fn-own-tls-result-owner r) id slots))
        (equal r (fn-oas-whole-refusal oc id i end))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oas-read-span)
                                  (fn-oas-over-p fn-oas-tiers fn-otm-read-span
                                   fn-oas-posting-off-read fn-oas-whole-refusal))
           :use ((:instance fn-oas-tiers-cases
                            (r1 (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)))
                 (:instance fn-oas-tiers-cases
                            (r1 (fn-oas-posting-off-read oc views id i end cache s
                                                         fn-octets fn-arena fn-cat)))))))

;; THE STEP.  The host's read leaves the owner holding at most the slots, or
;; at most what it held before the read: no read -- whatever it carried, one
;; command or a stream of them, an article entered, completed or both --
;; raises what the owner holds past the slots.
(defthm fn-oas-read-span-held-step
  (let ((held1 (fn-oas-held (fn-own-tls-result-owner
                             (fn-oas-read-span oc views id i end cache s slots
                                               fn-octets fn-arena fn-cat)))))
    (or (<= held1 (nfix slots))
        (<= held1 (fn-oas-held oc))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-oas-over-p)
                                  (fn-oas-read-span fn-oas-held fn-oas-articlep
                                   fn-oas-whole-refusal))
           :use (fn-oas-read-span-cases
                 (:instance fn-oas-whole-refusal-held)))))

;; KEYSTONE.  After the host's read, a connection that entered article mode
;; did so with the owner holding at most the slots.
(defthm fn-oas-read-span-admits-within-the-slots
  (let ((oc1 (fn-own-tls-result-owner
              (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat))))
    (implies (and (not (fn-oas-articlep oc id))
                  (fn-oas-articlep oc1 id))
             (<= (fn-oas-held oc1) (nfix slots))))
  :hints (("Goal" :in-theory (e/d (fn-oas-over-p)
                                  (fn-oas-read-span fn-oas-held fn-oas-articlep
                                   fn-oas-whole-refusal))
           :use (fn-oas-read-span-cases))))

(in-theory (disable fn-oas-read-span fn-oas-posting-off-read fn-oas-close-result
                    fn-oas-whole-refusal fn-oas-tiers fn-oas-over-p fn-oas-held
                    fn-oas-articlep))
