; fn: the owner admits an article by the memory equation (K-ADMIT; Builder M,
; memory landing 3+4, 2026-10-09).
;
; An article is admitted exactly when three resources admit it, and the
; refusal word names the first that refuses:
;   transactions T  (books/store-capacity-vector.lisp, :unaffordable)
;   history H       (payload octets since landing 3+4, :history-exhausted)
;   memory          the memory gate at the launch's LIMIT over the carried
;                   totals plus the held row the article becomes
;                   (books/memory-model.lisp fn-mm-gate-p; :memory)
; The owner (host/owner-host.lisp fn-owner-prepare-buffer) carries TOT
; (books/history-totals-carried.lisp, K-TOTALS) and builds ROW with
; fn-apc-intern-row-at before the prepare, so the memory term charges the
; row exactly, not a worst case.  The prepare is handed budget 0 when the
; memory gate refuses, so it answers :unaffordable and the word names the
; memory.  A store the gate admitted reopens within LIMIT (K3,
; fn-mm-gate-p's reopen conjunct).
;
; KEYSTONES (K-ADMIT)
;   fn-adm-article-budget-admits-exactly-the-three
;   fn-adm-article-word-under-the-budget-names-the-resource
;   fn-adm-admitted-row-keeps-the-gate
; KEYSTONES (the run's capacity, ruling (b) 2026-10-10)
;   fn-adm-capacity-fits, fn-adm-capacity-is-the-most,
;   fn-adm-capacity-monotone-in-the-limit, fn-adm-capacity-antitone-in-the-store,
;   fn-adm-capacity-binding-configured-exactly-at-c

(in-package "ACL2")
(include-book "store-capacity-vector")
(include-book "memory-model")
(include-book "history-totals-carried")

(local (in-theory (disable (tau-system))))

(defun fn-adm-residency (tot)
  (declare (xargs :guard t))
  (if (fn-mm-tot-p tot) (if (fn-mm-tot-paged-p tot) :paged :resident) :resident))

; The totals after ROW commits.
(defun fn-adm-after (tot row)
  (declare (xargs :guard t :verify-guards nil))
  (fn-mm-tot-plus tot (fn-ct-row-tot row (fn-adm-residency tot))))

(defun fn-adm-memory-admitp (profile img cfg limit tot row)
  (declare (xargs :guard t :verify-guards nil))
  (fn-mm-gate-p profile img cfg limit (fn-adm-after tot row)))

; The budget the served prepare is handed.
(defun fn-adm-article-budget (profile img cfg limit used bytes-used record debt tot row)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-adm-memory-admitp profile img cfg limit tot row)
      (fn-cvec-article-budget-for profile used bytes-used record debt)
    0))

; The word the host reports: T, then H, then the memory.
(defun fn-adm-article-word (word profile img cfg limit used bytes-used record debt tot row)
  (declare (xargs :guard t :verify-guards nil))
  (let ((w (fn-cvec-article-refusal-word word profile used bytes-used record debt)))
    (if (and (equal w :unaffordable)
             (fn-cvec-article-transactions-admitp profile used debt)
             (fn-cvec-article-history-admitp
              profile bytes-used
              (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                           (len (fn-record-groups record)))
              debt)
             (not (fn-adm-memory-admitp profile img cfg limit tot row)))
        :memory
      w)))

; KEYSTONE K-ADMIT (1): the budget admits one more record exactly when the
; transactions, the history and the memory admit it.
(defthm fn-adm-article-budget-admits-exactly-the-three
  (iff (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used bytes-used
                                              record debt tot row)
                       used)
       (and (fn-cvec-article-transactions-admitp profile used debt)
            (fn-cvec-article-history-admitp
             profile bytes-used
             (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                          (len (fn-record-groups record)))
             debt)
            (fn-adm-memory-admitp profile img cfg limit tot row)))
  :hints (("Goal" :use ((:instance fn-cvec-article-budget-for-admits-exactly-both-sides))
           :in-theory (e/d (fn-adm-article-budget fn-sbud-admitp)
                           (fn-adm-memory-admitp fn-cvec-article-budget-for
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-cvec-article-budget-for-admits-exactly-both-sides)))))

; KEYSTONE K-ADMIT (2): under the budget the host handed, a refusal names
; the first resource that refused.
(defthm fn-adm-article-word-under-the-budget-names-the-resource
  (let* ((tx (fn-cvec-article-transactions-admitp profile used debt))
         (hx (fn-cvec-article-history-admitp
              profile bytes-used
              (fn-sbud-article-gate-figure (len (fn-record-payload record))
                                           (len (fn-record-groups record)))
              debt))
         (mx (fn-adm-memory-admitp profile img cfg limit tot row))
         (w (fn-adm-article-word :unaffordable profile img cfg limit used bytes-used
                                 record debt tot row)))
    (implies (not (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used
                                                         bytes-used record debt tot row)
                                  used))
             (and (member-equal w '(:unaffordable :history-exhausted :memory))
                  (iff (equal w :unaffordable) (not tx))
                  (iff (equal w :history-exhausted) (and tx (not hx)))
                  (iff (equal w :memory) (and tx hx (not mx))))))
  :hints (("Goal" :use ((:instance fn-adm-article-budget-admits-exactly-the-three)
                        (:instance fn-cvec-article-budget-for-admits-exactly-both-sides)
                        (:instance fn-cvec-article-refusal-word-under-the-budget-names-the-resource))
           :in-theory (e/d (fn-adm-article-word fn-cvec-article-refusal-word)
                           (fn-adm-article-budget fn-adm-memory-admitp fn-cvec-article-budget-for
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-sbud-admitp
                            fn-adm-article-budget-admits-exactly-the-three
                            fn-cvec-article-budget-for-admits-exactly-both-sides
                            fn-cvec-article-refusal-word-under-the-budget-names-the-resource)))))

; A word other than :unaffordable passes through.
(defthm fn-adm-article-word-passes-other-words
  (implies (not (equal word :unaffordable))
           (equal (fn-adm-article-word word profile img cfg limit used bytes-used
                                       record debt tot row)
                  word))
  :hints (("Goal" :in-theory (enable fn-adm-article-word fn-cvec-article-refusal-word))))

; KEYSTONE K-ADMIT (3): a row the budget admitted leaves the totals within
; the gate: the store it commits serves within LIMIT (K1) and reopens
; within it (K3).
(defthm fn-adm-admitted-row-keeps-the-gate
  (implies (fn-sbud-admitp (fn-adm-article-budget profile img cfg limit used bytes-used
                                                  record debt tot row)
                           used)
           (and (<= (fn-mm-sum profile img cfg (fn-adm-after tot row)) limit)
                (<= (fn-mm-reopen-need profile img cfg (fn-adm-after tot row)) limit)))
  :hints (("Goal" :use ((:instance fn-adm-article-budget-admits-exactly-the-three))
           :in-theory (e/d (fn-adm-memory-admitp fn-mm-gate-p)
                           (fn-adm-article-budget fn-adm-article-budget-admits-exactly-the-three fn-mm-sum fn-mm-reopen-need fn-adm-after fn-mm-tot-plus
                            fn-cvec-article-transactions-admitp fn-cvec-article-history-admitp
                            fn-sbud-article-gate-figure fn-sbud-admitp)))))

; -----------------------------------------------------------------------------
; THE RUN'S CAPACITY (ruling (b), 2026-10-10).  The run states at configure
; C' of C: the most connections, at most the configured C, at which the
; memory gate holds at LIMIT over the carried store TOT.  C' is derived at
; every run, never pinned (D27); the run accepts at most C' readers and its
; gate prices C' connections.  NIL: the gate fails with no connection at all.
(defun fn-adm-cfg-at (cfg k)
  (declare (xargs :guard t))
  (update-nth 0 (nfix k) (true-list-fix cfg)))

(defun fn-adm-capacity-down (profile img cfg limit tot k)
  (declare (xargs :guard t :verify-guards nil :measure (nfix k)
                  :hints (("Goal" :in-theory '(zp nfix o-p o< o-finp natp)))))
  (cond ((fn-mm-gate-p profile img (fn-adm-cfg-at cfg k) limit tot) (nfix k))
        ((zp k) nil)
        (t (fn-adm-capacity-down profile img cfg limit tot (1- k)))))

(defun fn-adm-capacity (profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (fn-adm-capacity-down profile img cfg limit tot (fn-mm-cfg-connections cfg)))

; The term that bound C', named on the run's line: :configured when C' is C;
; when C' < C the term one more connection adds, the large reply (the OVER
; window or the article reply, whichever is larger) when a holder is added,
; else the connection's fixed part; with no C', :no-limit, :store when the
; sum with no connection does not fit, else :reopen.
(defun fn-adm-capacity-binding (profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-adm-capacity profile img cfg limit tot)))
    (cond ((null c)
           (cond ((not (natp limit)) :no-limit)
                 ((< limit (fn-mm-sum profile img (fn-adm-cfg-at cfg 0) tot)) :store)
                 (t :reopen)))
          ((equal c (fn-mm-cfg-connections cfg)) :configured)
          ((< (fn-mm-cfg-holders (fn-adm-cfg-at cfg c))
              (fn-mm-cfg-holders (fn-adm-cfg-at cfg (1+ c))))
           (if (< (+ (* 2 (nfix (fn-bs-profile-max-article-octets profile)))
                     *fn-cbud-reply-status-octets*)
                  (fn-mm-over-window-octets profile cfg))
               :over-window
             :article-reply))
          (t :connection-fixed))))

; The run's line (logged by the host at configure, the permanent admission
; statement): "memory capacity=C' of C bound-by=WORD sum=S MB limit=L MB", S
; the model's sum at C' over the carried store; with no C',
; "refused memory-cannot-hold-the-store capacity=0 of C bound-by=WORD
; sum=S MB limit=L MB", S the sum with no connection.
; MB, the sum rounded up and the limit down (never a figure that flatters).
(defun fn-adm-mb-up (octets)
  (declare (xargs :guard t))
  (fn-heap-decimal (floor (+ (nfix octets) 1048575) 1048576)))
(defun fn-adm-mb-down (octets)
  (declare (xargs :guard t))
  (fn-heap-decimal (floor (nfix octets) 1048576)))

(defun fn-adm-capacity-line (profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((c (fn-adm-capacity profile img cfg limit tot))
         (word (fn-adm-capacity-binding profile img cfg limit tot))
         (tail (concatenate 'string
                            " of " (fn-heap-decimal (fn-mm-cfg-connections cfg))
                            " bound-by=" (string-downcase (symbol-name word))
                            " sum=" (fn-adm-mb-up (fn-mm-sum profile img (fn-adm-cfg-at cfg (nfix c)) tot))
                            " MB limit=" (fn-adm-mb-down limit) " MB")))
    (if c
        (concatenate 'string "memory capacity=" (fn-heap-decimal c) tail)
      (concatenate 'string "refused memory-cannot-hold-the-store capacity=0" tail))))

(local (defthm fn-adm-cfg-at-of-zp
  (implies (and (zp k) (syntaxp (not (equal k ''0))))
           (equal (fn-adm-cfg-at cfg k) (fn-adm-cfg-at cfg 0)))
  :hints (("Goal" :in-theory (enable fn-adm-cfg-at)))))

(local (defthm fn-adm-cfg-at-of-nfix
  (equal (fn-adm-cfg-at cfg (nfix k)) (fn-adm-cfg-at cfg k))
  :hints (("Goal" :in-theory (enable fn-adm-cfg-at)))))

(local (defthm fn-adm-capacity-down-fits
  (let ((c (fn-adm-capacity-down profile img cfg limit tot k)))
    (implies c
             (and (natp c)
                  (<= c (nfix k))
                  (fn-mm-gate-p profile img (fn-adm-cfg-at cfg c) limit tot))))
  :hints (("Goal" :induct (fn-adm-capacity-down profile img cfg limit tot k)
           :in-theory (disable fn-mm-gate-p fn-adm-cfg-at)))))

(local (defthm fn-adm-capacity-down-is-the-most
  (implies (and (natp j) (<= j (nfix k))
                (fn-mm-gate-p profile img (fn-adm-cfg-at cfg j) limit tot))
           (let ((c (fn-adm-capacity-down profile img cfg limit tot k)))
             (and (natp c) (<= j c))))
  :hints (("Goal" :induct (fn-adm-capacity-down profile img cfg limit tot k)
           :in-theory (disable fn-mm-gate-p fn-adm-cfg-at)))))

(local (defthm fn-adm-cfg-connections-natp
  (natp (fn-mm-cfg-connections cfg))
  :rule-classes :type-prescription))

; KEYSTONE (C' fits): C' is at most C and the gate holds at C' connections.
(defthm fn-adm-capacity-fits
  (implies (fn-adm-capacity profile img cfg limit tot)
           (let ((c (fn-adm-capacity profile img cfg limit tot)))
             (and (natp c)
                  (<= c (fn-mm-cfg-connections cfg))
                  (fn-mm-gate-p profile img (fn-adm-cfg-at cfg c) limit tot))))
  :hints (("Goal" :in-theory (disable fn-mm-gate-p fn-adm-cfg-at fn-adm-capacity-down
                                      fn-mm-cfg-connections)
           :use ((:instance fn-adm-capacity-down-fits (k (fn-mm-cfg-connections cfg)))))))

; KEYSTONE (C' is the most): every count up to C the gate holds at is at most
; C'; with none, C' is NIL.
(defthm fn-adm-capacity-is-the-most
  (implies (and (natp j)
                (<= j (fn-mm-cfg-connections cfg))
                (fn-mm-gate-p profile img (fn-adm-cfg-at cfg j) limit tot))
           (let ((c (fn-adm-capacity profile img cfg limit tot)))
             (and (natp c) (<= j c))))
  :hints (("Goal" :in-theory (disable fn-mm-gate-p fn-adm-cfg-at fn-adm-capacity-down
                                      fn-mm-cfg-connections)
           :use ((:instance fn-adm-capacity-down-is-the-most (k (fn-mm-cfg-connections cfg)))))))

(local (defthm fn-adm-gate-monotone-in-the-limit
  (implies (and (fn-mm-gate-p profile img cfg l1 tot) (natp l2) (<= l1 l2))
           (fn-mm-gate-p profile img cfg l2 tot))
  :hints (("Goal" :in-theory (e/d (fn-mm-gate-p) (fn-mm-sum fn-mm-reopen-need))))))

; KEYSTONE: a larger limit holds at least as many connections.
(defthm fn-adm-capacity-monotone-in-the-limit
  (implies (and (natp l2) (<= l1 l2)
                (fn-adm-capacity profile img cfg l1 tot))
           (and (natp (fn-adm-capacity profile img cfg l2 tot))
                (<= (fn-adm-capacity profile img cfg l1 tot)
                    (fn-adm-capacity profile img cfg l2 tot))))
  :hints (("Goal" :in-theory (disable fn-mm-gate-p fn-adm-cfg-at fn-adm-capacity
                                      fn-mm-cfg-connections fn-adm-capacity-fits
                                      fn-adm-capacity-is-the-most)
           :use ((:instance fn-adm-capacity-fits (limit l1))
                 (:instance fn-adm-gate-monotone-in-the-limit
                            (cfg (fn-adm-cfg-at cfg (fn-adm-capacity profile img cfg l1 tot))))
                 (:instance fn-adm-capacity-is-the-most
                            (limit l2) (j (fn-adm-capacity profile img cfg l1 tot)))))))

(local (defthm fn-adm-gate-antitone-in-the-store
  (implies (and (fn-mm-gate-p profile img cfg limit b) (fn-mm-tot-le a b))
           (fn-mm-gate-p profile img cfg limit a))
  :hints (("Goal" :in-theory (e/d (fn-mm-gate-p) (fn-mm-sum fn-mm-reopen-need fn-mm-tot-le))
           :use (fn-mm-sum-grows-with-the-store
                 (:instance fn-mm-img-le-reflexive (i img))
                 (:instance fn-mm-reopen-need-monotone (i1 img) (i2 img)))))))

; KEYSTONE: a smaller store (a prefix, or what a reclaim leaves) holds at
; least as many connections.
(defthm fn-adm-capacity-antitone-in-the-store
  (implies (and (fn-mm-tot-le a b)
                (fn-adm-capacity profile img cfg limit b))
           (and (natp (fn-adm-capacity profile img cfg limit a))
                (<= (fn-adm-capacity profile img cfg limit b)
                    (fn-adm-capacity profile img cfg limit a))))
  :hints (("Goal" :in-theory (disable fn-mm-gate-p fn-adm-cfg-at fn-adm-capacity
                                      fn-mm-cfg-connections fn-adm-capacity-fits
                                      fn-adm-capacity-is-the-most fn-mm-tot-le)
           :use ((:instance fn-adm-capacity-fits (tot b))
                 (:instance fn-adm-gate-antitone-in-the-store
                            (cfg (fn-adm-cfg-at cfg (fn-adm-capacity profile img cfg limit b))))
                 (:instance fn-adm-capacity-is-the-most
                            (tot a) (j (fn-adm-capacity profile img cfg limit b)))))))

; KEYSTONE: the line says :configured exactly when C' is C.
(defthm fn-adm-capacity-binding-configured-exactly-at-c
  (equal (equal (fn-adm-capacity-binding profile img cfg limit tot) :configured)
         (equal (fn-adm-capacity profile img cfg limit tot)
                (fn-mm-cfg-connections cfg)))
  :hints (("Goal" :in-theory (disable fn-mm-gate-p fn-adm-cfg-at fn-adm-capacity
                                      fn-mm-cfg-connections fn-mm-sum fn-mm-reopen-need
                                      fn-mm-cfg-holders fn-mm-over-window-octets))))

; THE HANDLE SPACE (K-BOUND P3; Builder M, memory landing 4b, 2026-10-10; Codex rev-7
; finding 5).  A row's handle is the arena's count at its seal and a seal adds one
; (books/payload-arena.lisp fn-arena-seal-new-handle, fn-arena-seal-count), so the handle domain
; (unsigned-byte-p 64), the one fn-adm-held-share reads, is the arena invariant
; (unsigned-byte-p 64 (fn-arena-count fn-arena)).  It is DECIDED, never a guard: a batch of N
; seals is admitted only when the count after it is a u64, else it is refused by the word
; :handle-space before a handle is predicted.  The POST's intern decides it at N = 1
; (host/owner-host.lisp fn-owner-prepare, fn-owner-prepare-buffer); reclaim's tombstone batch
; and replay's re-intern decide it at their seal counts (PR-RECLAIM, PR-REPLAY).
(defun fn-adm-handle-room-p (count n)
  (declare (xargs :guard t))
  (and (natp count) (natp n) (<= (+ count n) (1- (expt 2 64)))))

; KEYSTONE: a batch the decision admits seals at a u64 handle and leaves a u64 count.
(defthm fn-adm-handle-room-is-u64-room
  (implies (fn-adm-handle-room-p count n)
           (and (unsigned-byte-p 64 count)
                (unsigned-byte-p 64 (+ count n)))))

; The POST's seal (either form) under the decision at N = 1: the new row's handle, the old
; count, is a u64 and so is the count after it.
(defthm fn-adm-handle-room-keeps-every-handle-u64
  (implies (fn-adm-handle-room-p (fn-arena-count fn-arena) 1)
           (and (unsigned-byte-p 64 (fn-arena-count fn-arena))
                (unsigned-byte-p 64 (fn-arena-count (fn-arena-seal-list xs fn-arena)))
                (unsigned-byte-p 64 (fn-arena-count (fn-arena-seal-buffer fn-octets fn-arena)))))
  :hints (("Goal" :in-theory (e/d (fn-arena-count) (fn-arena-seal-buffer fn-arena-seal-list)))))
;
; K-BOUND AGGREGATE (revision 8; Builder M, memory landing 4b, 2026-10-10; Codex approved the
; statement to prove, build/memory/l34/m10/codex-kbound8.final.md).  The profile bound
; (books/memory-model.lisp fn-mm-profile-bound-tot) holds over every store whose rows are each
; within the per-row invariant, whose record count is within T and whose budget charge is within H.
; PROVED here, conditional on the per-row invariant FN-ADM-ROW-WITHIN-P.  The producer facts -- that
; every row the node interns or restores satisfies it at the store's admitting profile -- are still
; owed (PF-INTERN, PF-COMPOSITE, PF-EVENT, PF-IDENTITY, PR-APPEND, PR-REPLAY, PR-CKPT, PR-KEYRING,
; PR-RECLAIM, PR-PROFILE).  A row's HISTORY share is its allowance plus 3 x its CHARGE: the row
; itself, the payload's headers once more in its facts, and a verified statement once more in its
; context delta.
(defun fn-adm-row-within-p (row profile)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((tot (fn-ct-row-tot row :resident))
         (c (fn-sbud-row-octets row))
         (rlog (fn-adm-row-allowance profile))
         (g (nfix (fn-bs-profile-max-groups-per-article profile))))
    (and (mv-let (err tl plen) (fn-hp-x-rowlen row) (declare (ignore tl plen)) (not err))
         (<= (fn-mm-tot-arena tot) c)
         (<= (fn-mm-tot-hcharge tot) (* (+ *fn-sbud-header-weight* *fn-sbud-msgid-weight*) c))
         (<= (fn-mm-tot-memberships tot) g)
         (<= (fn-mm-tot-events tot) c)
         (<= (fn-mm-tot-log tot) (+ rlog c))
         (<= (fn-mm-tot-history tot) (+ rlog (* 3 c))))))
(defun fn-adm-rows-within (records profile)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (fn-adm-row-within-p (car records) profile)
           (fn-adm-rows-within (cdr records) profile))
    t))
(encapsulate ()
(local (defthm kb-nfix-nfix (equal (nfix (nfix a)) (nfix a))))
(local (defthm kb-tot-fields-of-make
  (and (equal (fn-mm-tot-records (fn-mm-make-tot a b c d e f g h r)) (nfix a))
       (equal (fn-mm-tot-arena (fn-mm-make-tot a b c d e f g h r)) (nfix b))
       (equal (fn-mm-tot-hcharge (fn-mm-make-tot a b c d e f g h r)) (nfix c))
       (equal (fn-mm-tot-memberships (fn-mm-make-tot a b c d e f g h r)) (nfix d))
       (equal (fn-mm-tot-events (fn-mm-make-tot a b c d e f g h r)) (nfix e))
       (equal (fn-mm-tot-log (fn-mm-make-tot a b c d e f g h r)) (nfix f))
       (equal (fn-mm-tot-history (fn-mm-make-tot a b c d e f g h r)) (nfix g))
       (equal (fn-mm-tot-charge (fn-mm-make-tot a b c d e f g h r)) (nfix h))
       (equal (fn-mm-tot-paged-p (fn-mm-make-tot a b c d e f g h r)) (equal r :paged)))
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                                   fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log
                                   fn-mm-tot-history fn-mm-tot-charge fn-mm-tot-paged-p
                                   fn-mm-nat fn-mm-make-tot) (nfix))))))
(local (defthm kb-tot-natp
  (and (natp (fn-mm-tot-records a)) (natp (fn-mm-tot-arena a)) (natp (fn-mm-tot-hcharge a))
       (natp (fn-mm-tot-memberships a)) (natp (fn-mm-tot-events a)) (natp (fn-mm-tot-log a))
       (natp (fn-mm-tot-history a)) (natp (fn-mm-tot-charge a)))
  :hints (("Goal" :in-theory (enable fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge
                                     fn-mm-tot-memberships fn-mm-tot-events fn-mm-tot-log
                                     fn-mm-tot-history fn-mm-tot-charge fn-mm-nat)))))
(local (in-theory (disable fn-mm-tot-records fn-mm-tot-arena fn-mm-tot-hcharge fn-mm-tot-memberships
                           fn-mm-tot-events fn-mm-tot-log fn-mm-tot-history fn-mm-tot-charge
                           fn-mm-tot-paged-p)))
(local (defthm kb-tot-fields-of-plus
  (and (equal (fn-mm-tot-records (fn-mm-tot-plus a b)) (+ (fn-mm-tot-records a) (fn-mm-tot-records b)))
       (equal (fn-mm-tot-arena (fn-mm-tot-plus a b)) (+ (fn-mm-tot-arena a) (fn-mm-tot-arena b)))
       (equal (fn-mm-tot-hcharge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-hcharge a) (fn-mm-tot-hcharge b)))
       (equal (fn-mm-tot-memberships (fn-mm-tot-plus a b)) (+ (fn-mm-tot-memberships a) (fn-mm-tot-memberships b)))
       (equal (fn-mm-tot-events (fn-mm-tot-plus a b)) (+ (fn-mm-tot-events a) (fn-mm-tot-events b)))
       (equal (fn-mm-tot-log (fn-mm-tot-plus a b)) (+ (fn-mm-tot-log a) (fn-mm-tot-log b)))
       (equal (fn-mm-tot-history (fn-mm-tot-plus a b)) (+ (fn-mm-tot-history a) (fn-mm-tot-history b)))
       (equal (fn-mm-tot-charge (fn-mm-tot-plus a b)) (+ (fn-mm-tot-charge a) (fn-mm-tot-charge b)))
       (equal (fn-mm-tot-paged-p (fn-mm-tot-plus a b)) (fn-mm-tot-paged-p a)))
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-plus) (fn-mm-make-tot))))))
(local (defthm kb-fields-of-zero
  (and (equal (fn-mm-tot-records (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-arena (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-hcharge (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-memberships (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-events (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-log (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-history (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-charge (fn-ct-zero-tot res)) 0)
       (equal (fn-mm-tot-paged-p (fn-ct-zero-tot res)) (equal res :paged)))
  :hints (("Goal" :in-theory (enable fn-ct-zero-tot)))))
(local (defthm kb-fields-of-row-tot
  (and (equal (fn-mm-tot-records (fn-ct-row-tot row res)) 1)
       (equal (fn-mm-tot-charge (fn-ct-row-tot row res)) (nfix (fn-sbud-row-octets row)))
       (equal (fn-mm-tot-paged-p (fn-ct-row-tot row res)) (equal res :paged))
       (equal (fn-mm-tot-arena (fn-ct-row-tot row res)) (nfix (nth 0 (fn-ct-row row))))
       (equal (fn-mm-tot-hcharge (fn-ct-row-tot row res)) (nfix (nth 1 (fn-ct-row row))))
       (equal (fn-mm-tot-memberships (fn-ct-row-tot row res)) (nfix (nth 2 (fn-ct-row row))))
       (equal (fn-mm-tot-events (fn-ct-row-tot row res)) (nfix (nth 3 (fn-ct-row row))))
       (equal (fn-mm-tot-log (fn-ct-row-tot row res)) (nfix (fn-ct-row-log row)))
       (equal (fn-mm-tot-history (fn-ct-row-tot row res)) (nfix (fn-ct-row-history row))))
  :hints (("Goal" :use fn-ct-row-charge
           :in-theory (e/d (fn-ct-row-tot) (nfix fn-mm-make-tot fn-ct-row fn-ct-row-log fn-ct-row-history
                                            fn-ct-row-charge fn-sbud-row-octets))))))
(local (defthm kb-row-octets-natp (natp (fn-sbud-row-octets row))
  :hints (("Goal" :in-theory (enable fn-sbud-row-octets)))
  :rule-classes :type-prescription))
(local (defthm kb-nfix-row-octets (equal (nfix (fn-sbud-row-octets row)) (fn-sbud-row-octets row))
  :hints (("Goal" :in-theory (enable nfix) :use kb-row-octets-natp))))
(local (defthm kb-record-octets-natp (natp (fn-sbud-record-octets rs))
  :hints (("Goal" :in-theory (enable fn-sbud-record-octets)))
  :rule-classes :type-prescription))
(local (in-theory (disable fn-ct-row-tot fn-mm-tot-plus fn-ct-zero-tot fn-mm-make-tot
                           fn-ct-charged fn-adm-row-within-p fn-sbud-record-octets
                           fn-ct-row fn-ct-row-log fn-ct-row-history fn-sbud-row-octets fn-hp-x-rowlen)))
(local (defthm kb-charged-cons
  (equal (fn-ct-charged (cons r rs) res)
         (fn-mm-tot-plus (fn-ct-row-tot r res) (fn-ct-charged rs res)))
  :hints (("Goal" :in-theory (enable fn-ct-charged)))))
(local (defthm kb-charged-atom
  (implies (not (consp rs)) (equal (fn-ct-charged rs res) (fn-ct-zero-tot res)))
  :hints (("Goal" :in-theory (enable fn-ct-charged)))))
(local (defthm kb-record-octets-cons
  (equal (fn-sbud-record-octets (cons r rs))
         (+ (fn-sbud-row-octets r) (fn-sbud-record-octets rs)))
  :hints (("Goal" :in-theory (enable fn-sbud-record-octets)))))
(local (defthm kb-record-octets-atom
  (implies (not (consp rs)) (equal (fn-sbud-record-octets rs) 0))
  :hints (("Goal" :in-theory (enable fn-sbud-record-octets)))))
(local (defthm kb-within-cons
  (equal (fn-adm-rows-within (cons r rs) p)
         (and (fn-adm-row-within-p r p) (fn-adm-rows-within rs p)))))
(local (defthm kb-row-within-nth
  (implies (fn-adm-row-within-p row p)
           (let ((c (fn-sbud-row-octets row))
                 (a (fn-adm-row-allowance p)))
             (and (<= (nfix (nth 0 (fn-ct-row row))) c)
                  (<= (nfix (nth 1 (fn-ct-row row))) (* (+ *fn-sbud-header-weight* *fn-sbud-msgid-weight*) c))
                  (<= (nfix (nth 2 (fn-ct-row row))) (nfix (fn-bs-profile-max-groups-per-article p)))
                  (<= (nfix (nth 3 (fn-ct-row row))) c)
                  (<= (nfix (fn-ct-row-log row)) (+ a c))
                  (<= (nfix (fn-ct-row-history row)) (+ a (* 3 c))))))
  :hints (("Goal" :in-theory (e/d (fn-adm-row-within-p kb-fields-of-row-tot)
                                  (fn-hp-x-rowlen fn-ct-row fn-ct-row-log fn-ct-row-history
                                   fn-sbud-row-octets fn-adm-row-allowance nfix))))
  :rule-classes nil))
(local (defun kb-concl (rs p res)
  (declare (xargs :guard t :verify-guards nil))
  (let ((tot (fn-ct-charged rs res))
        (c (fn-sbud-record-octets rs))
        (rlog (fn-adm-row-allowance p))
        (n (len rs)))
    (and (equal (fn-mm-tot-records tot) n)
         (<= (fn-mm-tot-arena tot) c)
         (<= (fn-mm-tot-hcharge tot) (* (+ *fn-sbud-header-weight* *fn-sbud-msgid-weight*) c))
         (<= (fn-mm-tot-memberships tot) (* n (nfix (fn-bs-profile-max-groups-per-article p))))
         (<= (fn-mm-tot-events tot) c)
         (<= (fn-mm-tot-log tot) (+ (* n rlog) c))
         (<= (fn-mm-tot-history tot) (+ (* n rlog) (* 3 c)))
         (equal (fn-mm-tot-charge tot) c)
         (equal (fn-mm-tot-paged-p tot) (equal res :paged))))))
(local (in-theory (disable kb-concl fn-adm-row-allowance fn-mm-profile-record-log
                           fn-bs-profile-max-groups-per-article nfix)))
(local (defthm kb-concl-atom
  (implies (not (consp rs)) (kb-concl rs p res))
  :hints (("Goal" :in-theory (enable kb-concl kb-charged-atom kb-record-octets-atom)))))
(local (defthm kb-step-0
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (equal (fn-mm-tot-records tot) n)))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-1
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-arena tot) c)))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-2
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-hcharge tot) (* (+ *fn-sbud-header-weight* *fn-sbud-msgid-weight*) c))))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-3
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-memberships tot) (* n (nfix (fn-bs-profile-max-groups-per-article p))))))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-4
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-events tot) c)))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-5
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-log tot) (+ (* n rlog) c))))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-6
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (<= (fn-mm-tot-history tot) (+ (* n rlog) (* 3 c)))))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-7
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (equal (fn-mm-tot-charge tot) c)))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-step-8
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (let ((tot (fn-ct-charged (cons r rs) res)) (c (fn-sbud-record-octets (cons r rs)))
                 (rlog (fn-adm-row-allowance p)) (n (len (cons r rs))))
             (declare (ignorable tot c rlog n))
             (equal (fn-mm-tot-paged-p tot) (equal res :paged))))
  :hints (("Goal" :in-theory (enable kb-concl)
           :use ((:instance kb-row-within-nth (row r)))))))
(local (defthm kb-concl-step
  (implies (and (fn-adm-row-within-p r p) (kb-concl rs p res))
           (kb-concl (cons r rs) p res))
  :hints (("Goal" :in-theory (union-theories '(kb-concl) (disable kb-concl-atom kb-charged-cons kb-record-octets-cons))
           :use (kb-step-0 kb-step-1 kb-step-2 kb-step-3 kb-step-4 kb-step-5 kb-step-6 kb-step-7 kb-step-8)))))
(local (defthm kb-aggregate
  (implies (fn-adm-rows-within rs p) (kb-concl rs p res))
  :hints (("Goal" :induct (fn-ct-charged rs res)
           :in-theory (e/d ((:induction fn-ct-charged)) ())
           :expand ((fn-adm-rows-within rs p)))
          (and stable-under-simplificationp
               '(:use ((:instance kb-concl-step (r (car rs)) (rs (cdr rs)))))))))
(local (defthm kb-mono
  (implies (and (natp a) (natp b) (natp c) (<= a b)) (<= (* a c) (* b c)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil))
(local (defthm kb-allowance-natp (natp (fn-adm-row-allowance p))
  :hints (("Goal" :in-theory (enable fn-adm-row-allowance fn-mm-profile-record-log)))
  :rule-classes :type-prescription))
(local (defthm kb-nfix-natp (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm kb-nfix-natp2 (natp (nfix x)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nfix)))))
(local (defthm kb-bound-fields
  (let ((b (fn-mm-profile-bound-tot p r))
        (tt (nfix (fn-bs-profile-max-transactions p)))
        (h (nfix (fn-bs-profile-max-history-octets p)))
        (g (nfix (fn-bs-profile-max-groups-per-article p)))
        (a (fn-adm-row-allowance p)))
    (and (equal (fn-mm-tot-records b) tt)
         (equal (fn-mm-tot-arena b) h)
         (equal (fn-mm-tot-hcharge b) (* (+ *fn-sbud-header-weight* *fn-sbud-msgid-weight*) h))
         (equal (fn-mm-tot-memberships b) (* tt g))
         (equal (fn-mm-tot-events b) h)
         (equal (fn-mm-tot-log b) (+ (* tt a) h))
         (equal (fn-mm-tot-history b) (+ (* tt a) (* 3 h)))
         (equal (fn-mm-tot-charge b) h)
         (equal (fn-mm-tot-paged-p b) (equal r :paged))))
  :hints (("Goal" :in-theory (e/d (fn-mm-profile-bound-tot) (fn-adm-row-allowance nfix))))))
(defthm fn-mm-profile-bound-holds-every-admitted-store
  (implies (and (<= (len records) (nfix (fn-bs-profile-max-transactions p)))
                (<= (fn-sbud-record-octets records) (nfix (fn-bs-profile-max-history-octets p)))
                (fn-adm-rows-within records p))
           (fn-mm-tot-le (fn-ct-charged records r) (fn-mm-profile-bound-tot p r)))
  :hints (("Goal" :in-theory (e/d (fn-mm-tot-le kb-concl) (kb-aggregate fn-adm-row-allowance fn-mm-profile-bound-tot
                                                 fn-bs-profile-max-transactions fn-bs-profile-max-history-octets
                                                 fn-bs-profile-max-groups-per-article))
           :use ((:instance kb-aggregate (rs records) (res r))
                 (:instance kb-mono (a (len records)) (b (nfix (fn-bs-profile-max-transactions p)))
                            (c (fn-adm-row-allowance p)))
                 (:instance kb-mono (a (len records)) (b (nfix (fn-bs-profile-max-transactions p)))
                            (c (nfix (fn-bs-profile-max-groups-per-article p))))))))
)
