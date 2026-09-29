; fn: memory credits on the served path (lane credits, B5 of
; COMPLETE-BEFORE-6.6.0, 2026-09-28; D35 F8; PRF-380;
; planning/review-2026-09-28-gpt6.md "Memory and zero-copy calls").
;
; books/memory-credits.lisp is the ledger
;
;     M_base + M_cache + sum_i credit_i + E_completion + E_runtime <= B
;
; and this book is where the served path calls it.  The host keeps ONE
; ledger for the run (host/owner-host.lisp, global fn-owner-credits):
;
;   THE BUDGET is the reservation the launcher sized the dynamic space
;   from, fn-heap-figure-octets (`fn-mca-initial'): its base less the
;   open's terms and the articles' pool is M_base (the image, the state at
;   the profile's bounds, the request in flight, the octet buffers), the
;   open's terms are E_completion (the open and the recovery re-run them:
;   funded separately and never admitted against), the collector's room is
;   E_runtime, and what is left, exactly fn-heap-articles-octets, is the
;   pool the operations draw on (KEYSTONE fn-mca-initial-funds-exactly-the-
;   articles).  No cache is charged: a committed article's octets live in
;   the store state, which M_base holds at the profile's bounds
;   (fn-heap-store-history-holds-payload-and-memberships); M_cache and its
;   eviction get a host subject when the state leaves the base (P1/P2 of
;   planning/evidence/f8-reservation-2026-09-28.md).
;
;   THE OPERATIONS are keyed by where the buffer is:
;     (:conn . ID)  connection ID's article buffers: one reserve R (the
;                   article's worst case packed, fn-heap-article-reserve-octets)
;                   while it is mid-article and one per submission of it
;                   still queued (`fn-mca-need');
;     :open         the submissions the committer took and has not sealed
;                   into a batch (taken, attempted, in the log's open
;                   batch);
;     :sealed       the batch in flight: appended, its barrier (the
;                   syncer thread's fdatasync, the owner released) not yet
;                   returned.
;
; The credit follows the buffer:
;   a read of ID      `fn-mca-read-span': the read the host ran before
;                     (fn-oas-read-span) and ID's credit resized to what
;                     the read left it holding.  Shrinking and holding
;                     steady are never refused (RESERVE TO FINISH: an
;                     admitted article reads on and completes into a queued
;                     submission at the same credit); growth is admitted
;                     only within the budget, and past it the read is
;                     refused by name -- a POST 440 at the command
;                     (fn-mca-refused-read), else the read is not run at
;                     all and the connection is answered 400 and closed
;                     (`fn-mca-shut-read': RFC 3977 section 3.2.1) -- so
;                     the ledger is never over-committed;
;   the take          `fn-mca-take': one reserve moves from (:conn . ID)
;                     to :open;
;   the seal          `fn-mca-seal': :open becomes :sealed;
;   COMPLETE          `fn-mca-batch-done': :sealed is released after the
;                     barrier returned;
;   the stop          `fn-mca-stop': both released (the service exits);
;   a close, a fault  `fn-mca-close': ID's own credit only.  A client that
;   or a stall        went away, timed out or was told uncertain at a
;                     stall frees its body and its queued submissions, but
;                     never what the committer or a submitted fdatasync
;                     still owns (KEYSTONE fn-mca-close-keeps-what-the-
;                     commit-owns).
;
; KEYSTONES: fn-mca-read-span-keeps-funded (no hypothesis beyond a funded
; ledger: the host's read never over-commits), fn-mca-read-span-covers-the-
; connection (after the read ID's credit is exactly what its buffers need,
; whenever it covered them before), fn-mca-read-span-within-the-credit-
; unfolds (a read the credit holds is fn-oas-read-span exactly),
; fn-mca-close-keeps-what-the-commit-owns, fn-mca-commit-steps-keep-funded,
; fn-mca-initial-funds-exactly-the-articles.
;
; Not claimed here: that a read of ID leaves every OTHER connection's
; buffers as they were (the frame theorem lane admission-gap is proving);
; with it, "every connection's credit covers its buffers" is an invariant of
; the served machine, and without it this book's coverage is per read of
; the connection read.  That the packed store and the packed submission
; take the reserve's figures (544 octets a 512-octet block; an octet and 48
; a natural) is a measurement: measure at convergence (VmRSS with 30 posters
; mid-article at the default preset with A = 1 MiB).

(in-package "ACL2")
(include-book "owner-article-slots")
(include-book "memory-credits")
(include-book "heap-figure")

; -----------------------------------------------------------------------------
; Keys and needs.

(defun fn-mca-conn-key (id)
  (declare (xargs :guard t))
  (cons :conn id))

(defconst *fn-mca-open* :open)
(defconst *fn-mca-sealed* :sealed)

; The queued submissions of connection ID.  A loop (tail recursive).
(defun fn-mca-queued-onto (id subs n)
  (declare (xargs :guard (natp n)))
  (if (consp subs)
      (fn-mca-queued-onto id (cdr subs)
                          (if (and (consp (car subs)) (equal (fn-own-sub-id (car subs)) id))
                              (+ 1 n)
                            n))
    n))

(defun fn-mca-queued (id subs)
  (declare (xargs :guard t))
  (fn-mca-queued-onto id subs 0))

(defthm fn-mca-queued-onto-natp
  (implies (natp n) (natp (fn-mca-queued-onto id subs n)))
  :rule-classes :type-prescription)

(defthm fn-mca-queued-natp
  (natp (fn-mca-queued id subs))
  :rule-classes :type-prescription)

; What a queued submission holds (lane credits-stall; PKT-887): the queue
; holds it packed (lane chunked-body-2, B6b: fn-own-enqueue,
; books/packed-submission.lisp fn-psub-sub-heap -- the article's octets one
; natural, the groups another, the Message-ID and the records' cells), twice
; for the collector's copy -- never more than the reserve it was admitted
; with.  The worst case (the reserve) is what an article NOT YET COMPLETE
; may still need; once complete its size is known and the rest comes back.
; SUB is the submission as QUEUED (the host reads the queue's head before
; the take, host/owner-host.lisp fn-owner-take).
(defun fn-mca-sub-charge (sub reserve)
  (declare (xargs :guard t))
  (min (nfix reserve) (* 2 (fn-psub-sub-heap sub))))

(defthm fn-mca-sub-charge-natp
  (natp (fn-mca-sub-charge sub reserve))
  :rule-classes :type-prescription)

; The charges of connection ID's queued submissions.  A loop.
(defun fn-mca-queued-charge-onto (id subs reserve acc)
  (declare (xargs :guard (natp acc)))
  (if (consp subs)
      (fn-mca-queued-charge-onto id (cdr subs) reserve
                                 (if (and (consp (car subs)) (equal (fn-own-sub-id (car subs)) id))
                                     (+ acc (fn-mca-sub-charge (car subs) reserve))
                                   acc))
    acc))

(defthm fn-mca-queued-charge-onto-natp
  (implies (natp acc) (natp (fn-mca-queued-charge-onto id subs reserve acc)))
  :rule-classes :type-prescription)

; What connection ID's buffers need in OC: a whole reserve while it is
; mid-article (reserve to finish), and each queued submission's charge.
(defun fn-mca-need (oc id reserve)
  (declare (xargs :guard t))
  (+ (if (fn-oas-articlep oc id) (nfix reserve) 0)
     (fn-mca-queued-charge-onto id (fn-own-queue (fn-ocfg-owner oc)) reserve 0)))

(defthm fn-mca-need-natp
  (natp (fn-mca-need oc id reserve))
  :rule-classes :type-prescription)

(defun fn-mca-held (credits id)
  (declare (xargs :guard t))
  (fn-mcr-credit-of (fn-mca-conn-key id) (fn-mcr-ops credits)))

; -----------------------------------------------------------------------------
; The read.

; The read not run: connection ID answered 400 and closed, its wire dropped
; (its retained input with it), nothing else of OC changed.  Every octet
; offered is consumed (the connection closes).
(defun fn-mca-shut-read (oc id i end)
  (declare (xargs :guard (and (natp i) (natp end) (<= i end))))
  (fn-own-tls-make-result (- end i)
                          (list (fn-nntp-reply-effect *fn-oas-busy-line*)
                                (fn-nntp-close-effect))
                          (fn-oas-owner-closed oc id)
                          nil))

;; The read refused at the command: posting switched off for it (a POST
;; answered 440), and, when it still leaves ID in article mode, ID's wire
;; closed and answered 400 (books/owner-article-slots.lisp
;; fn-oas-posting-off-read, fn-oas-close-result; lane admission-gap split the
;; former fn-oas-refused-read into those two, batch BB 2026-09-28).
(defun fn-mca-refused-read (oc views id i end s fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let ((r (fn-oas-posting-off-read oc views id i end s fn-octets fn-arena fn-cat)))
    (if (fn-oas-articlep (fn-own-tls-result-owner r) id)
        (fn-oas-close-result r id)
      r)))

; THE READ THE HOST CALLS (host/owner-host.lisp fn-owner-chunk-span-at):
; (RESULT . CREDITS').
(defun fn-mca-read-span (credits oc views id i end s slots reserve fn-octets fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (let* ((key (fn-mca-conn-key id))
         (r0 (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat))
         (d0 (fn-mcr-resize credits key
                            (fn-mca-need (fn-own-tls-result-owner r0) id reserve))))
    (if (equal (car d0) :ok)
        (cons r0 (cadr d0))
      (let* ((r1 (fn-mca-refused-read oc views id i end s fn-octets fn-arena fn-cat))
             (d1 (fn-mcr-resize credits key
                                (fn-mca-need (fn-own-tls-result-owner r1) id reserve))))
        (if (equal (car d1) :ok)
            (cons r1 (cadr d1))
          (let* ((r2 (fn-mca-shut-read oc id i end))
                 (d2 (fn-mcr-resize credits key
                                    (fn-mca-need (fn-own-tls-result-owner r2) id reserve))))
            (cons r2 (if (equal (car d2) :ok) (cadr d2) credits))))))))

; -----------------------------------------------------------------------------
; The commit's steps and the close.  Each is a transition of the ledger
; that is never refused; a refusal could only come from an inconsistent
; key, and then the ledger is kept as it was (never released early).

(defun fn-mca-ok-or (d credits)
  (declare (xargs :guard t))
  (if (and (consp d) (equal (car d) :ok) (consp (cdr d))) (cadr d) credits))

; A connection closed, faulted or was told uncertain: its own buffers are
; freed.  Nothing the commit holds (:open, :sealed) is touched.
(defun fn-mca-close (credits id)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-resize credits (fn-mca-conn-key id) 0) credits))

; The committer took connection ID's oldest queued submission: its charge
; RESERVE (fn-mca-sub-charge; what the connection holds, if less) moves to
; :open.  The control
; channel's and a BP delivery's submissions are not keyed by a connection
; (the figure's request in flight holds them): nothing moves.
(defun fn-mca-take (credits id reserve)
  (declare (xargs :guard t))
  (let ((x (min (nfix reserve) (fn-mca-held credits id))))
    (fn-mca-ok-or (fn-mcr-move credits (fn-mca-conn-key id) *fn-mca-open* x) credits)))

; A submission taken and answered without joining a batch (a shed POST,
; nothing stored): its reserve comes back from :open.
(defun fn-mca-untake (credits reserve)
  (declare (xargs :guard t))
  (let ((have (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits))))
    (fn-mca-ok-or (fn-mcr-resize credits *fn-mca-open* (- have (min have (nfix reserve))))
                  credits)))

; The open batch was appended: it is the batch in flight.
(defun fn-mca-seal (credits)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-move credits *fn-mca-open* *fn-mca-sealed*
                             (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits)))
                credits))

; The batch in flight's barrier returned and COMPLETE answered it.
(defun fn-mca-batch-done (credits)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-resize credits *fn-mca-sealed* 0) credits))

; The taken submissions were written synchronously (the path without a
; commit pipeline) or the START sealed nothing: :open is free.
(defun fn-mca-settle (credits)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-resize credits *fn-mca-open* 0) credits))

; The service stops (an uncertain batch: exit 3).
(defun fn-mca-stop (credits)
  (declare (xargs :guard t))
  (fn-mca-settle (fn-mca-batch-done credits)))

; -----------------------------------------------------------------------------
; The budget.  The reservation the launcher sized the dynamic space from
; (host/owner-host.lisp fn-owner-connection-budget's figure).

(defun fn-mca-open-octets (profile)
  (declare (xargs :guard t))
  (fn-heap-store-open-octets profile
                             (fn-heap-open-octets-bound profile nil)
                             (fn-heap-open-records-bound profile nil)))

(defun fn-mca-initial (profile core nursery)
  (declare (xargs :guard t))
  (let* ((fig (fn-heap-figure-octets profile core nursery))
         (base (fn-heap-store-base-octets profile core nil))
         (open (fn-mca-open-octets profile)))
    (fn-mcr-make fig (- base (+ (fn-heap-articles-octets profile) open)) 0 open
                 (- fig base) 0 nil)))

; Before a run installs its budget: a ledger that admits one article at
; RESERVE (as fn-owner-article-slots admits one slot).
(defun fn-mca-default (reserve)
  (declare (xargs :guard t))
  (fn-mcr-make reserve 0 0 0 0 0 nil))

; -----------------------------------------------------------------------------
; The theorems.

(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-mca-ok-or-keeps-funded
  (implies (and (fn-mcr-fundedp credits)
                (implies (equal (car d) :ok) (fn-mcr-fundedp (cadr d))))
           (fn-mcr-fundedp (fn-mca-ok-or d credits))))

(defthm fn-mca-ok-or-of-resize
  (implies (equal (car (fn-mcr-resize l id n)) :ok)
           (equal (fn-mca-ok-or (fn-mcr-resize l id n) c) (cadr (fn-mcr-resize l id n))))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-with)))))

(defthm fn-mca-ok-or-of-move
  (implies (equal (car (fn-mcr-move l from to x)) :ok)
           (equal (fn-mca-ok-or (fn-mcr-move l from to x) c) (cadr (fn-mcr-move l from to x))))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-with)))))

(defthm fn-mca-resize-to-nothing-is-admitted
  (equal (car (fn-mcr-resize l id 0)) :ok))

(defthm fn-mca-ok-or-of-resize-keeps-funded
  (implies (fn-mcr-fundedp l) (fn-mcr-fundedp (fn-mca-ok-or (fn-mcr-resize l id n) l)))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-resize fn-mcr-fundedp)))))

(defthm fn-mca-ok-or-of-move-keeps-funded
  (implies (fn-mcr-fundedp l) (fn-mcr-fundedp (fn-mca-ok-or (fn-mcr-move l a b x) l)))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-move fn-mcr-fundedp)))))

(in-theory (disable fn-mca-ok-or))

;; KEYSTONE.  The host's read never over-commits the ledger: from a funded
;; ledger the credits it leaves are funded, whatever the read.
(defthm fn-mca-read-span-keeps-funded
  (implies (fn-mcr-fundedp credits)
           (fn-mcr-fundedp
            (cdr (fn-mca-read-span credits oc views id i end s slots reserve
                                   fn-octets fn-arena fn-cat))))
  :hints (("Goal" :in-theory (union-theories '(fn-mca-read-span fn-mcr-resize-and-move-keep-funded
                                               car-cons cdr-cons)
                                             (theory 'minimal-theory)))))

;; A read the credit holds is the read before this book exactly.
(defthm fn-mca-read-span-within-the-credit-unfolds
  (implies (equal (car (fn-mcr-resize credits (fn-mca-conn-key id)
                                      (fn-mca-need (fn-own-tls-result-owner
                                                    (fn-oas-read-span oc views id i end s slots
                                                                      fn-octets fn-arena fn-cat))
                                                   id reserve)))
                  :ok)
           (equal (car (fn-mca-read-span credits oc views id i end s slots reserve
                                         fn-octets fn-arena fn-cat))
                  (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d () (fn-oas-read-span fn-mca-refused-read fn-mca-need
                                      fn-mcr-resize fn-mca-shut-read)))))

;; RESERVE TO FINISH.  A read that leaves connection ID needing no more
;; than it holds -- an admitted article read on, completed into its queued
;; submission, or answered -- is never refused by the credit.
(defthm fn-mca-read-span-never-blocks-what-is-held
  (implies (<= (fn-mca-need (fn-own-tls-result-owner
                             (fn-oas-read-span oc views id i end s slots
                                               fn-octets fn-arena fn-cat))
                            id reserve)
               (fn-mca-held credits id))
           (equal (car (fn-mca-read-span credits oc views id i end s slots reserve
                                         fn-octets fn-arena fn-cat))
                  (fn-oas-read-span oc views id i end s slots fn-octets fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-mca-held)
                                  (fn-oas-read-span fn-mca-refused-read fn-mca-need
                                   fn-mcr-resize fn-mca-shut-read fn-mca-read-span
                                   fn-mcr-total))
           :use (fn-mca-read-span-within-the-credit-unfolds
                 (:instance fn-mcr-resize-refuses-exactly-past-the-budget
                            (l credits) (id (fn-mca-conn-key id))
                            (n (fn-mca-need (fn-own-tls-result-owner
                                             (fn-oas-read-span oc views id i end s slots
                                                               fn-octets fn-arena fn-cat))
                                            id reserve)))))))

;; The shut read needs no more than the connection needed before it.
(local
 (defthm fn-mca-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (enable fn-ocfg-owner fn-ocfg-with-owner fn-ocfg-make)))))

(local
 (defthm fn-mca-queue-of-set-conns
   (equal (fn-own-queue (fn-own-set-conns o conns)) (fn-own-queue o))
   :hints (("Goal" :in-theory (enable fn-own-set-conns)))))

(defthm fn-mca-queue-of-owner-closed
  (equal (fn-own-queue (fn-ocfg-owner (fn-oas-owner-closed oc id)))
         (fn-own-queue (fn-ocfg-owner oc)))
  :hints (("Goal" :in-theory (e/d (fn-oas-owner-closed) (fn-own-set-conns fn-ocfg-with-owner)))))

(defthm fn-mca-need-of-shut-read
  (<= (fn-mca-need (fn-own-tls-result-owner (fn-mca-shut-read oc id i end)) id reserve)
      (fn-mca-need oc id reserve))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-mca-shut-read)
                                  (fn-oas-articlep fn-oas-owner-closed)))))

;; KEYSTONE.  Coverage per read: when connection ID's credit covered what
;; its buffers needed before the read, after it the credit is exactly what
;; they need -- the admitted read's, the refused read's or the shut read's.
(defthm fn-mca-read-span-covers-the-connection
  (implies (<= (fn-mca-need oc id reserve) (fn-mca-held credits id))
           (let ((rc (fn-mca-read-span credits oc views id i end s slots reserve
                                       fn-octets fn-arena fn-cat)))
             (equal (fn-mca-held (cdr rc) id)
                    (fn-mca-need (fn-own-tls-result-owner (car rc)) id reserve))))
  :hints (("Goal" :in-theory (e/d (fn-mca-held)
                                  (fn-oas-read-span fn-mca-refused-read fn-mca-need
                                   fn-mcr-resize fn-mca-shut-read fn-mcr-total))
           :use ((:instance fn-mcr-resize-sets-the-credit (l credits) (a nil)
                            (id (fn-mca-conn-key id))
                            (n (fn-mca-need (fn-own-tls-result-owner
                                             (fn-oas-read-span oc views id i end s slots
                                                               fn-octets fn-arena fn-cat))
                                            id reserve)))
                 (:instance fn-mcr-resize-sets-the-credit (l credits) (a nil)
                            (id (fn-mca-conn-key id))
                            (n (fn-mca-need (fn-own-tls-result-owner
                                             (fn-mca-refused-read oc views id i end s
                                                                  fn-octets fn-arena fn-cat))
                                            id reserve)))
                 (:instance fn-mcr-resize-sets-the-credit (l credits) (a nil)
                            (id (fn-mca-conn-key id))
                            (n (fn-mca-need (fn-own-tls-result-owner
                                             (fn-mca-shut-read oc id i end))
                                            id reserve)))
                 (:instance fn-mcr-resize-refuses-exactly-past-the-budget
                            (l credits) (id (fn-mca-conn-key id))
                            (n (fn-mca-need (fn-own-tls-result-owner
                                             (fn-mca-shut-read oc id i end))
                                            id reserve)))))))

;; KEYSTONE.  A close (a client gone, a timeout, a stall's uncertain
;; answer, a fault) releases only the connection's own credit: what the
;; committer took and the batch in flight still own keep theirs, and the
;; ledger stays funded.
(defthm fn-mca-close-keeps-what-the-commit-owns
  (and (implies (not (equal a (fn-mca-conn-key id)))
                (equal (fn-mcr-credit-of a (fn-mcr-ops (fn-mca-close credits id)))
                       (fn-mcr-credit-of a (fn-mcr-ops credits))))
       (equal (fn-mca-held (fn-mca-close credits id) id) 0)
       (implies (fn-mcr-fundedp credits)
                (fn-mcr-fundedp (fn-mca-close credits id))))
  :hints (("Goal" :in-theory (e/d (fn-mca-held fn-mca-close)
                                  (fn-mcr-resize fn-mcr-fundedp fn-mca-conn-key))
           :use ((:instance fn-mcr-resize-sets-the-credit (l credits)
                            (id (fn-mca-conn-key id)) (n 0))
                 (:instance fn-mcr-resize-and-move-keep-funded (l credits)
                            (id (fn-mca-conn-key id)) (n 0))))))

;; KEYSTONE.  Every commit step keeps a funded ledger funded, and the take
;; and the seal move credit without changing the funded total (the same
;; credit follows the buffer from the connection to the batch in flight).
(defthm fn-mca-commit-steps-keep-funded
  (implies (fn-mcr-fundedp credits)
           (and (fn-mcr-fundedp (fn-mca-take credits id reserve))
                (fn-mcr-fundedp (fn-mca-untake credits reserve))
                (fn-mcr-fundedp (fn-mca-seal credits))
                (fn-mcr-fundedp (fn-mca-batch-done credits))
                (fn-mcr-fundedp (fn-mca-settle credits))
                (fn-mcr-fundedp (fn-mca-stop credits))))
  :hints (("Goal" :in-theory (union-theories '(fn-mca-take fn-mca-untake fn-mca-seal fn-mca-batch-done
                                               fn-mca-settle fn-mca-stop
                                               fn-mca-ok-or-of-resize-keeps-funded
                                               fn-mca-ok-or-of-move-keeps-funded)
                                             (theory 'minimal-theory)))))

(defthm fn-mca-take-and-seal-keep-the-total
  (implies (fn-mcr-opsp (fn-mcr-ops credits))
           (and (equal (fn-mcr-total (fn-mca-take credits id reserve)) (fn-mcr-total credits))
                (equal (fn-mcr-total (fn-mca-seal credits)) (fn-mcr-total credits))))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-move fn-mcr-total))
           :use ((:instance fn-mcr-total-of-move (l credits)
                            (from (fn-mca-conn-key id)) (to *fn-mca-open*)
                            (x (min (nfix reserve) (fn-mca-held credits id))))
                 (:instance fn-mcr-total-of-move (l credits)
                            (from *fn-mca-open*) (to *fn-mca-sealed*)
                            (x (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits))))))))

;; The seal takes all of :open into :sealed; the batch's COMPLETE releases
;; :sealed and nothing else.
(defthm fn-mca-seal-and-batch-done-move-the-batch
  (and (equal (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops (fn-mca-seal credits)))
              (+ (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops credits))
                 (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits))))
       (equal (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops (fn-mca-seal credits))) 0)
       (equal (fn-mcr-credit-of *fn-mca-sealed* (fn-mcr-ops (fn-mca-batch-done credits))) 0)
       (implies (not (equal a *fn-mca-sealed*))
                (equal (fn-mcr-credit-of a (fn-mcr-ops (fn-mca-batch-done credits)))
                       (fn-mcr-credit-of a (fn-mcr-ops credits)))))
  :hints (("Goal" :in-theory (e/d (fn-mca-ok-or) (fn-mcr-move fn-mcr-resize))
           :use ((:instance fn-mcr-move-moves-the-credit (l credits)
                            (from *fn-mca-open*) (to *fn-mca-sealed*)
                            (x (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits))))
                 (:instance fn-mcr-move-within-what-it-holds-is-admitted (l credits)
                            (from *fn-mca-open*) (to *fn-mca-sealed*)
                            (x (fn-mcr-credit-of *fn-mca-open* (fn-mcr-ops credits))))
                 (:instance fn-mcr-resize-sets-the-credit (l credits)
                            (id *fn-mca-sealed*) (n 0))
                 (:instance fn-mcr-resize-refuses-exactly-past-the-budget (l credits)
                            (id *fn-mca-sealed*) (n 0))))))

;; The base the launcher's figure is computed from, split as the ledger
;; splits it.
(local
 (defthm fn-mca-accessors-of-make
   (and (equal (fn-mcr-budget (fn-mcr-make b ba c co r d o)) (nfix b))
        (equal (fn-mcr-base (fn-mcr-make b ba c co r d o)) (nfix ba))
        (equal (fn-mcr-cache (fn-mcr-make b ba c co r d o)) (nfix c))
        (equal (fn-mcr-completion (fn-mcr-make b ba c co r d o)) (nfix co))
        (equal (fn-mcr-runtime (fn-mcr-make b ba c co r d o)) (nfix r))
        (equal (fn-mcr-drawn (fn-mcr-make b ba c co r d o)) (nfix d))
        (equal (fn-mcr-ops (fn-mcr-make b ba c co r d o)) o))
   :hints (("Goal" :in-theory (enable fn-mcr-make fn-mcr-budget fn-mcr-base fn-mcr-cache
                                      fn-mcr-completion fn-mcr-runtime fn-mcr-drawn
                                      fn-mcr-ops)))))

(local
 (defthm fn-mca-base-splits
   (equal (fn-heap-store-base-octets profile core nil)
          (+ (fn-heap-core-dynamic core) (fn-heap-store-state-bound profile)
             (fn-mca-open-octets profile) (fn-heap-store-inflight-octets profile)
             (fn-heap-articles-octets profile)))
   :hints (("Goal" :in-theory (union-theories '(fn-heap-store-base-octets fn-mca-open-octets)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-mca-parts-natp
   (and (natp (fn-heap-core-dynamic core))
        (natp (fn-heap-store-state-bound profile))
        (natp (fn-mca-open-octets profile))
        (natp (fn-heap-store-inflight-octets profile))
        (natp (fn-heap-articles-octets profile)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-mca-open-octets)))))

(local
 (defthm fn-heap-articles-octets-natp
   (natp (fn-heap-articles-octets profile))
   :rule-classes :type-prescription))

;; The ledger's arithmetic, over opaque parts.
(local
 (defthm fn-mca-initial-shape
   (implies (and (natp d) (natp st) (natp o) (natp i) (natp a) (natp fig)
                 (<= (+ d st o i a) fig))
            (let ((l (fn-mcr-make fig (- (+ d st o i a) (+ a o)) 0 o (- fig (+ d st o i a)) 0 nil)))
              (and (fn-mcr-fundedp l) (equal (- (fn-mcr-budget l) (fn-mcr-total l)) a)
                   (equal (fn-mcr-budget l) fig) (equal (fn-mcr-completion l) o))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-mcr-fundedp fn-mcr-total) (fn-mcr-make))))))

;; KEYSTONE.  The launcher's reservation is the budget: the ledger a run
;; starts from is funded, and what it leaves free for operations is exactly
;; the articles' pool the figure holds (so it admits fn-heap-article-slots
;; whole reserves, as the slots did).  The open's terms are the completion
;; reserve, funded and never admitted against.
(defthm fn-mca-initial-funds-exactly-the-articles
  (let ((l (fn-mca-initial profile core nursery)))
    (and (fn-mcr-fundedp l)
         (equal (- (fn-mcr-budget l) (fn-mcr-total l)) (fn-heap-articles-octets profile))
         (equal (fn-mcr-budget l) (fn-heap-figure-octets profile core nursery))
         (equal (fn-mcr-completion l) (fn-mca-open-octets profile))))
  :hints (("Goal" :in-theory (union-theories '(fn-mca-initial fn-heap-figure-octets
                                               fn-heap-store-figure-octets fn-mca-base-splits
                                               nfix natp-compound-recognizer)
                                             (theory 'minimal-theory))
           :use ((:instance fn-mca-initial-shape
                            (d (fn-heap-core-dynamic core)) (st (fn-heap-store-state-bound profile))
                            (o (fn-mca-open-octets profile)) (i (fn-heap-store-inflight-octets profile))
                            (a (fn-heap-articles-octets profile))
                            (fig (fn-heap-with-nursery (fn-heap-store-base-octets profile core nil)
                                                       nursery)))
                 (:instance fn-mca-parts-natp)
                 (:instance fn-heap-with-nursery-covers-base
                            (base (fn-heap-store-base-octets profile core nil)))
                 (:instance fn-heap-with-nursery-natp
                            (base (fn-heap-store-base-octets profile core nil)))))))

(in-theory (disable fn-mca-read-span fn-mca-shut-read fn-mca-need fn-mca-held fn-mca-close
                    fn-mca-take fn-mca-untake fn-mca-seal fn-mca-batch-done fn-mca-settle
                    fn-mca-stop fn-mca-initial fn-mca-default))
