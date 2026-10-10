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
  (let ((c (fn-adm-capacity profile img cfg limit tot)))
    (implies c
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
