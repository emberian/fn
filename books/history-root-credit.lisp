; Allocation demand for the live P3 root candidate. Encoder length is counted
; without materializing its octets; a page grow is funded before the flat
; resize. The permanent generation grant survives publication completion.
(in-package "ACL2")
(include-book "history-image-row-step")
(include-book "memory-credits")
(include-book "history-paged-adopt")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-hroot-nat-octets (n)
  (declare (xargs :guard (natp n)))
  (+ 1 (ceiling (integer-length n) 8)))
(defun fn-hroot-string-octets (s)
  (declare (xargs :guard (stringp s)))
  (+ (fn-hroot-nat-octets (length s)) (length s)))
(defun fn-hroot-tree-octets (x)
  (declare (xargs :guard t))
  (cond ((fn-scc-octets-valuep x) (+ 1 (fn-hroot-nat-octets (len x)) (len x)))
        ((consp x) (+ 1 (fn-hroot-tree-octets (car x)) (fn-hroot-tree-octets (cdr x))))
        ((null x) 1)
        ((natp x) (+ 1 (fn-hroot-nat-octets x)))
        ((integerp x) (+ 1 (fn-hroot-nat-octets (- -1 x))))
        ((characterp x) 2)
        ((stringp x) (+ 1 (fn-hroot-string-octets x)))
        ((symbolp x) (+ 2 (fn-hroot-string-octets (symbol-name x))))
        (t 1)))

(defun fn-hroot-page-octets (np)
  (declare (xargs :guard (natp np)))
  (+ (* 8 (+ (* 2048 np) (* 2 np) (pgs-ntables np))) 512))
(defun fn-hroot-memory-octets (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c))
  (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
             (n)
             (* 8 (+ (pgs-w-length pgs-mem) (pgs-m-length pgs-mem)
                     (pgs-t-length pgs-mem) (pgs-d-length pgs-mem)
                     (pgs-v-length pgs-mem) (pgs-tv-length pgs-mem)))
             (+ n (* 8 (fn-hrc-sfx-length fn-hrecs$c)) 4096)))
(defun fn-hroot-retain-demand (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)))
  (+ (fn-hroot-memory-octets fn-hrecs$c) (* 64 (fn-hrc-count fn-hrecs$c))))
(defun fn-hroot-event-demand (ev ordinal fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (natp ordinal)))
  (declare (ignore ev))
  (+ (fn-hroot-memory-octets fn-hrecs$c) (* 64 (+ 1 ordinal))
     (fn-hroot-page-octets 1)))
(defun fn-hroot-grow-demand (cursor ordinal fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-hpr-cursorp cursor) (natp ordinal)
                              (fn-hrc-wfp fn-hrecs$c)
                              (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
                  :verify-guards nil))
  (+ (fn-hroot-memory-octets fn-hrecs$c) (* 64 (+ 1 ordinal))
     (fn-hroot-page-octets (cadr (fn-hpr-final-placement cursor)))))

; The per-event decode transient (96 octets a tree octet of the event, beside
; a constant): NOT part of a generation's resident credit.  It is its own
; credit, drawn before the decode and released after it (host/history-root-host.lisp
; fn-owner-hroot-transient), so it draws the article pool as an ops credit and is
; refused by name when the pool is short.  The reserve holds the images only.
(defun fn-hroot-event-transient (ev)
  (declare (xargs :guard t))
  (* 96 (+ 8 (fn-hroot-tree-octets ev))))
(defun fn-hroot-grow-transient (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c
                  :guard (and (fn-hrc-wfp fn-hrecs$c)
                              (< (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)))
                  :verify-guards nil))
  (fn-hroot-event-transient (fn-hrc-sfxi (fn-hrc-lo fn-hrecs$c) fn-hrecs$c)))
(defun fn-hroot-credit-key (generation)
  (declare (xargs :guard (posp generation)))
  (cons :history-root generation))

(defun fn-hroot-tail-demand (ev ordinal fn-hist$p)
  (declare (xargs :stobjs fn-hist$p :guard (natp ordinal)) (ignore ev))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (amount)
             (+ (* 2 (fn-hroot-memory-octets fn-hrecs$c))
                (* 64 (+ 1 ordinal)))
             amount))

; The stored SCC length cell is scalar metadata. Read it before decoding the
; event, so the consumer can fund its temporary words/octets/tree allocation.
(defun fn-hroot-read-demand (ordinal retained fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (natp ordinal) (natp retained)
                              (fn-hist$p-wfp fn-hist$p))
                  :verify-guards nil))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (verdict amount)
             (if (< ordinal (fn-hrc-nimg fn-hrecs$c))
                 (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                            (v n)
                            (fn-hp-x-cell 1 ordinal (fn-hrc-starts fn-hrecs$c) pgs-mem)
                            (mv v (+ retained 512 (* 96 (nfix n)))))
               (mv :ok (+ retained 64)))
             (mv verdict amount)))
(defun fn-hroot-index-demand (ordinal fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (natp ordinal) (fn-hist$p-wfp fn-hist$p))
                  :verify-guards nil))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (retained)
             (fn-hroot-retain-demand fn-hrecs$c)
             (fn-hroot-read-demand ordinal retained fn-hist$p)))

(defun fn-hroot-root-retain-demand (fn-hist$p)
  (declare (xargs :stobjs fn-hist$p :guard (fn-hist$p-wfp fn-hist$p)
                  :verify-guards nil))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (amount) (fn-hroot-retain-demand fn-hrecs$c) amount))

(defthm fn-hroot-memory-natural
 (natp (fn-hroot-memory-octets c))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-hroot-memory-octets))))
(defthm fn-hroot-retain-natural
 (implies (and (fn-hrecs$cp c) (fn-hrc-wfp c)) (natp (fn-hroot-retain-demand c)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (e/d (fn-hroot-retain-demand fn-hrc-count fn-hrc-wfp)
                            (fn-hroot-memory-octets fn-hrecs$cp fn-hrc-fields fn-hrc-updaters)))))
(verify-guards fn-hroot-grow-demand
 :hints (("Goal" :in-theory (e/d (fn-hrc-wfp fn-hpr-final-placement fn-hpr-cursorp)
 (fn-hrc-fields fn-hrc-updaters fn-hrecs$cp fn-hroot-memory-octets fn-hroot-tree-octets)))))
(verify-guards fn-hroot-grow-transient
 :hints (("Goal" :in-theory (e/d (fn-hrc-wfp)
 (fn-hrc-fields fn-hrc-updaters fn-hrecs$cp fn-hroot-memory-octets fn-hroot-tree-octets)))))
(verify-guards fn-hroot-read-demand
 :hints (("Goal" :in-theory (e/d (fn-hist$p-wfp fn-hrc-wfp fn-hp-starts-okp)
 (fn-hist$p-root-ready fn-hrc-fields fn-hrc-updaters fn-hrecs$cp fn-hist$pp fn-hp-x-cell)))))
(verify-guards fn-hroot-index-demand
 :hints (("Goal" :use ((:instance fn-hist$p-root-is-physical (p fn-hist$p))
                      (:instance fn-hroot-retain-natural (c (fn-hist$p-root fn-hist$p))))
 :in-theory (e/d (fn-hist$p-wfp)
 (fn-hist$pp fn-hrecs$cp fn-hrc-wfp fn-hist$p-root-ready fn-hroot-retain-demand fn-hroot-read-demand)))))
(verify-guards fn-hroot-root-retain-demand
 :hints (("Goal" :in-theory (e/d (fn-hist$p-wfp)
 (fn-hrc-wfp fn-hist$p-root-ready fn-hroot-retain-demand)))))

; -----------------------------------------------------------------------------
; A refused begin and a refused refresh are named (lane s-heap2, 2026-10-08).
; `fn-owner-hroot-begin' (host/history-root-host.lisp) funds a generation's
; first allocation; `fnn-owner-history-root-refresh' returns its word and the
; maintain step reports it.  ACL2 decides the word and the status the host
; reports; the history stobj is not an argument of either, so a refusal
; cannot touch it.

(defun fn-hroot-begin-ask ()
  (declare (xargs :guard t))
  (+ 4096 (fn-hroot-page-octets 1)))

; The octets the reserve still has for GENERATION's key.
(defun fn-hroot-begin-room (l generation)
  (declare (xargs :guard (posp generation)))
  (nfix (- (fn-mcr-hroot l)
           (fn-mcr-hroot-sum-with l (fn-hroot-credit-key generation) 0))))

(defun fn-hroot-begin-resize (l generation)
  (declare (xargs :guard (posp generation)))
  (fn-mcr-hroot-resize l (fn-hroot-credit-key generation) (fn-hroot-begin-ask)))

; :funded, or (:refused REASON ASK ROOM) with REASON the resize's own.
(defun fn-hroot-begin-word (l generation)
  (declare (xargs :guard (posp generation)))
  (let ((r (fn-hroot-begin-resize l generation)))
    (if (equal (car r) :ok)
        :funded
      (list :refused (cadr r) (fn-hroot-begin-ask) (fn-hroot-begin-room l generation)))))

; The ledger after the begin: the resize's on :funded, the same ledger otherwise.
(defun fn-hroot-begin-ledger (l generation)
  (declare (xargs :guard (posp generation)))
  (let ((r (fn-hroot-begin-resize l generation)))
    (if (equal (car r) :ok) (cadr r) l)))

; What the host reports and the status column renders, from the whole
; refresh word: begin's :funded, the refresh's (:building G) / (:installed G),
; any (:refused R . DETAIL) passed through by name, and anything else
; :uncertain -- never read as building.
(defun fn-hroot-refresh-status (w)
  (declare (xargs :guard t))
  (cond ((or (equal w :funded)
             (and (consp w) (member-equal (car w) '(:building :installed))))
         (list :history-root :building))
        ((and (consp w) (equal (car w) :refused) (consp (cdr w)))
         (cons :history-root (cons :refused (cdr w))))
        (t (list :history-root :uncertain))))

; The theorems from here through the building-iff are -unfolds: each
; selects a branch of the definition above and restates it, not a keystone.
; The claim with teeth is the host composition (word -> status -> line, two
; host calls, no single ACL2 function), witnessed by fn-hroot-begin-teeth-*
; and books/history-root-status.lisp fn-hrs-teeth-*.
(defthm fn-hroot-begin-word-refused-is-the-resizes-own-unfolds
  (implies (equal (car (fn-hroot-begin-resize l g)) :refused)
           (and (equal (fn-hroot-begin-word l g)
                       (list :refused (cadr (fn-hroot-begin-resize l g))
                             (fn-hroot-begin-ask) (fn-hroot-begin-room l g)))
                (equal (fn-hroot-begin-ledger l g) l)
                (equal (fn-hroot-refresh-status (fn-hroot-begin-word l g))
                       (list :history-root :refused (cadr (fn-hroot-begin-resize l g))
                             (fn-hroot-begin-ask) (fn-hroot-begin-room l g))))))

(defthm fn-hroot-begin-word-funded-is-the-resizes-own-unfolds
  (implies (equal (car (fn-hroot-begin-resize l g)) :ok)
           (and (equal (fn-hroot-begin-word l g) :funded)
                (equal (fn-hroot-begin-ledger l g) (cadr (fn-hroot-begin-resize l g)))
                (equal (fn-hroot-refresh-status (fn-hroot-begin-word l g))
                       '(:history-root :building)))))

(defthm fn-hroot-begin-word-refuses-exactly-when-the-resize-does-unfolds
  (equal (equal (fn-hroot-begin-word l g) :funded)
         (equal (car (fn-hroot-begin-resize l g)) :ok)))

; K3: every refused word is reported refused with its own reason and detail,
; never building; a word nobody recognises is :uncertain.
(defthm fn-hroot-refresh-status-of-a-refusal-unfolds
  (implies (and (consp w) (equal (car w) :refused) (consp (cdr w)))
           (equal (fn-hroot-refresh-status w)
                  (list* :history-root :refused (cdr w)))))

(defthm fn-hroot-refresh-status-of-a-refusal-is-not-building-unfolds
  (implies (and (consp w) (equal (car w) :refused) (consp (cdr w)))
           (and (equal (cadr (fn-hroot-refresh-status w)) :refused)
                (not (equal (fn-hroot-refresh-status w) '(:history-root :building)))
                (not (equal (fn-hroot-refresh-status w) '(:history-root :uncertain))))))

(defthm fn-hroot-refresh-status-is-building-exactly-for-the-ok-words-unfolds
  (iff (equal (fn-hroot-refresh-status w) '(:history-root :building))
         (or (equal w :funded)
             (and (consp w) (member-equal (car w) '(:building :installed)))))
  :hints (("Goal" :in-theory (enable fn-hroot-refresh-status)
           :cases ((equal w :funded) (not (consp w)) (and (consp w) (equal (car w) :building)) (and (consp w) (equal (car w) :installed)) (and (consp w) (equal (car w) :refused))))))

; Teeth.  Exhausted: the reserve is 0 (CONVERGE-2's ledger without a reserve).
(defthm fn-hroot-begin-teeth-exhausted
  (let ((l (fn-mcr-make 5624942530 2815331266 0 2789392384 16777216 0 nil 0 nil)))
    (and (fn-mcr-fundedp l)
         (equal (fn-hroot-begin-word l 2)
                (list :refused :history-root-reserve-exhausted (fn-hroot-begin-ask) 0))
         (equal (fn-hroot-begin-ledger l 2) l)
         (equal (fn-hroot-refresh-status (fn-hroot-begin-word l 2))
                (list :history-root :refused :history-root-reserve-exhausted
                      (fn-hroot-begin-ask) 0))))
  :rule-classes nil)

; Hypothesis removal: the same ledger with the reserve raised to the ask.
(defthm fn-hroot-begin-teeth-funded
  (let ((l (fn-mcr-make (+ 5624942530 (fn-hroot-begin-ask)) 2815331266 0 2789392384 16777216 0 nil
                        (fn-hroot-begin-ask) nil)))
    (and (fn-mcr-fundedp l)
         (equal (fn-hroot-begin-word l 2) :funded)
         (equal (fn-mcr-credit-of (fn-hroot-credit-key 2) (fn-mcr-hroots (fn-hroot-begin-ledger l 2)))
                (fn-hroot-begin-ask))
         (equal (fn-hroot-refresh-status (fn-hroot-begin-word l 2)) '(:history-root :building))))
  :rule-classes nil)
