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
; book admits a connection into article mode only while the owner then holds
; at most that many (`fn-oas-held': the connections in article mode, the
; queued submissions and the batch in flight).  The host installs the slots
; once per run (host/owner-host.lisp fn-owner-connection-budget, from the
; store's profile) and every served read runs `fn-oas-read-span':
;
;   - the read as the host ran it before (books/owner-time-admission.lisp
;     fn-otm-read-span); when it leaves connection ID newly in article mode
;     and the owner then holds more than the slots,
;   - the read again from the same owner with ID's posting bit off: a POST
;     is answered 440 at the command (RFC 3977 section 6.3.1: the client
;     sends no article), with this book's reason line in place of the
;     generic text when the connection's own configuration permits posting;
;   - and when ID still enters article mode (IHAVE's 335, a TAKETHIS: RFC
;     4644 offers no refusal before a streamed article), its wire is closed
;     and the read answers 400 and closes (RFC 3977 section 3.2.1: 400 may
;     answer any command, and the client retries later).  The body is never
;     retained.
;
; KEYSTONE `fn-oas-read-span-admits-within-the-slots' (no hypothesis): after
; the host's read, if connection ID is in article mode and was not before,
; the owner holds at most SLOTS articles in flight.
; `fn-oas-read-span-when-held-unfolds': a read the slots hold is the read
; before this book exactly (every theorem about fn-otm-read-span is about the
; host's call there).
; KEYSTONE `fn-oas-read-span-never-blocks-an-admitted-article': the policy
; against completion deadlock is RESERVE-TO-FINISH -- a slot is the whole
; article's worst case (fn-heap-article-reserve-octets), taken at entry into
; article mode, so the reads of an admitted connection are never refused by
; the slots and an admitted upload completes (or is refused by name past the
; body limit) without waiting for any other.  A stalled upload holds its
; slot until the connection's idle timeout closes it.
;
; The subject is fn-oas-read-span, which host/owner-host.lisp
; fn-owner-chunk-span-at calls with the slots it installed.
;
; Not claimed here: that a read of connection ID leaves every OTHER
; connection's wire mode as it was (no frame theorem over the served chain
; exists yet), which the invariant "held <= slots between reads" needs
; beside this keystone; the queue's growth by the control channel and BP
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

; A read over OC that left OC1: ID entered article mode and the owner holds
; more than SLOTS.
(defun fn-oas-over-p (oc oc1 id slots)
  (declare (xargs :guard t))
  (and (not (fn-oas-articlep oc id))
       (fn-oas-articlep oc1 id)
       (< (nfix slots) (fn-oas-held oc1))))

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

; The read from OC with ID's posting bit off; a POST is refused 440 at the
; command, and a connection that still enters article mode is closed with
; 400.
(defun fn-oas-refused-read (oc views id i end s fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let* ((allow (fn-otm-conn-allow oc id))
         (r (fn-otm-read-span (fn-otm-owner-with-allow oc id nil) views id i end s
                              fn-octets fn-arena fn-cat))
         (oc1 (fn-otm-owner-with-allow (fn-own-tls-result-owner r) id allow))
         (effects (if allow
                      (fn-oas-post-effects (fn-own-tls-result-effects r))
                    (fn-own-tls-result-effects r))))
    (if (fn-oas-articlep oc1 id)
        (fn-own-tls-make-result
         (fn-own-tls-result-consumed r)
         (append (true-list-fix effects)
                 (list (fn-nntp-reply-effect *fn-oas-busy-line*)
                       (fn-nntp-close-effect)))
         (fn-oas-owner-closed oc1 id)
         (fn-own-tls-result-repinned r))
      (fn-own-tls-make-result (fn-own-tls-result-consumed r) effects oc1
                              (fn-own-tls-result-repinned r)))))

; THE READ THE HOST CALLS (host/owner-host.lisp fn-owner-chunk-span-at).
(defun fn-oas-read-span (oc views id i end s slots fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((r (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
    (if (fn-oas-over-p oc (fn-own-tls-result-owner r) id slots)
        (fn-oas-refused-read oc views id i end s fn-octets fn-arena fn-cat)
      r)))

; -----------------------------------------------------------------------------
; The theorems.

;; A read the slots hold is the read before this book.
(defthm fn-oas-read-span-when-held-unfolds
  (implies (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                   (fn-otm-read-span oc views id i end s fn-octets
                                                     fn-arena fn-cat))
                               id slots))
           (equal (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)
                  (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
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

(local
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
                                  nil)))))))))

(local
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
                                  nil)))))))))

(defthm fn-oas-owner-closed-is-not-article
  (not (fn-oas-articlep (fn-oas-owner-closed oc id) id))
  :hints (("Goal" :in-theory (e/d (fn-oas-owner-closed fn-oas-articlep)
                                  (fn-oas-conn-articlep fn-oas-conn-closed
                                   fn-own-replace-conn fn-own-find-conn)))))

;; The refused read never leaves ID in article mode.
(defthm fn-oas-refused-read-is-not-article
  (not (fn-oas-articlep
        (fn-own-tls-result-owner
         (fn-oas-refused-read oc views id i end s fn-octets fn-arena fn-cat))
        id))
  :hints (("Goal" :in-theory (e/d (fn-oas-refused-read)
                                  (fn-otm-read-span fn-oas-articlep fn-oas-owner-closed
                                   fn-otm-owner-with-allow fn-otm-conn-allow
                                   fn-oas-post-effects)))))

;; KEYSTONE.  After the host's read, a connection that entered article mode
;; did so with the owner holding at most the slots.
(defthm fn-oas-read-span-admits-within-the-slots
  (let ((oc1 (fn-own-tls-result-owner
              (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat))))
    (implies (and (not (fn-oas-articlep oc id))
                  (fn-oas-articlep oc1 id))
             (<= (fn-oas-held oc1) (nfix slots))))
  :hints (("Goal" :in-theory (e/d (fn-oas-read-span fn-oas-over-p)
                                  (fn-otm-read-span fn-oas-refused-read fn-oas-articlep
                                   fn-oas-held)))))

;; KEYSTONE (no completion deadlock: the policy is reserve-to-finish).  A
;; connection already in article mode was admitted with a whole article's
;; credit, and the slots never stop it: its read is the read before this
;; book exactly, whatever the slots and whatever else is held, so an
;; admitted upload completes (or is refused by name past the body limit,
;; books/wire.lisp's :body-overlimit, 441) without waiting for any other.
;; Many partial uploads therefore cannot hold the pool in a state where each
;; needs more of it to finish.
(defthm fn-oas-read-span-never-blocks-an-admitted-article
  (implies (fn-oas-articlep oc id)
           (equal (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)
                  (fn-otm-read-span oc views id i end s fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-oas-read-span fn-oas-over-p)
                                  (fn-otm-read-span fn-oas-refused-read fn-oas-articlep
                                   fn-oas-held)))))

(in-theory (disable fn-oas-read-span fn-oas-refused-read fn-oas-over-p fn-oas-held
                    fn-oas-articlep))
