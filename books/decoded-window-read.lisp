; Exact scalar publication of a physically returned stored window.
(in-package "ACL2")
(include-book "page-window-executor")
(include-book "decoded-window-begin")
(include-book "decoded-window-lease")

(defun fn-pwz-plan-matches-token (z token)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))
                  :guard-hints (("Goal" :in-theory (enable fn-pwz-tokenp)))))
  (let ((s (nth 1 z)))
    (and (fn-pwz-tokenp token)
         (equal (nth 8 s) (fn-pwz-nth 1 token))
         (equal (nth 10 s) token)
         (equal (list (nth 1 s) (nth 2 s) (nth 3 s) (nth 11 s) (nth 12 s)
                      (nth 3 z) (nth 6 s) (nth 2 z) (fn-pwz-nth 10 token))
                (cddr token))
         (equal (nth 13 s) (nth 12 s))
         (equal (nth 5 s) 0)
         (equal (nth 4 z) (min 16384 (nfix (- (nfix (nth 2 z)) (nfix (nth 3 z)))))))))

(local
 (defthm fn-pwz-nth-is-nth-by-definition
   (implies (natp i) (equal (fn-pwz-nth i fields) (nth i fields)))
   :hints (("Goal" :in-theory (enable fn-pwz-nth)))))

(local
 (defthm fn-pwz-nine-naturals-shape
   (implies (fn-pwz-naturals 9 fields)
            (and (natp (nth 0 fields)) (natp (nth 1 fields)) (natp (nth 2 fields)) (natp (nth 3 fields)) (natp (nth 4 fields)) (natp (nth 5 fields)) (natp (nth 6 fields)) (natp (nth 7 fields)) (natp (nth 8 fields))
                 (equal fields (list (nth 0 fields) (nth 1 fields) (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields) (nth 7 fields) (nth 8 fields)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :expand ((fn-pwz-naturals 9 fields) (fn-pwz-naturals 8 (cdr fields)) (fn-pwz-naturals 7 (cdr (cdr fields))) (fn-pwz-naturals 6 (cdr (cdr (cdr fields)))) (fn-pwz-naturals 5 (cdr (cdr (cdr (cdr fields))))) (fn-pwz-naturals 4 (cdr (cdr (cdr (cdr (cdr fields)))))) (fn-pwz-naturals 3 (cdr (cdr (cdr (cdr (cdr (cdr fields))))))) (fn-pwz-naturals 2 (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields)))))))) (fn-pwz-naturals 1 (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields))))))))) (fn-pwz-naturals 0 (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr fields)))))))))))
           :in-theory (enable fn-pwz-naturals)))))

(defthm fn-pwz-begin-captures-typed-request
  (implies (fn-pwz-tokenp token)
           (fn-pwz-plan-matches-token
             (mv-nth 0 (fn-pwz-begin token incarnation pgs-digest-state
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) token))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-nine-naturals-shape (fields (cddr token))))
           :in-theory (e/d (fn-pwz-plan-matches-token fn-pwz-begin fn-pwz-tokenp
                              fn-pwz-descriptorp fn-ewz-begin fn-ewz-state fn-ews-begin fn-ewp-begin fn-ewp-state)
                             (fn-pwz-naturals fn-pwz-nth fn-pwz-dictionary fn-pzw-initialize fn-pzd-budget pgs-dcb-begin)))))

(defun fn-pwz-outcome (ledger worker token z)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (cond ((fn-pwx-boundp ledger worker token :cancelled-returned) :cancelled)
        ((not (fn-pwx-boundp ledger worker token :returned)) :stale-job)
        ((not (fn-pwz-plan-matches-token z token)) '(:fault :state))
        ((fn-ewz-publication z) :ready)
        (t (list :fault (nth 0 z) (nth 0 (nth 1 z)) (nth 8 z)))))

(defun fn-pwz-byte (ledger worker token z i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome nil)
      (if (and (natp i) (natp (nth 4 z)) (<= (nth 4 z) 16384) (< i (nth 4 z)))
          (mv :byte (fn-ew-bytesi i fn-ew-buffer))
        (mv :unavailable nil)))))

; All physical/codec coordinates remain checked by the core. DICT-ID is
; the immutable shipped ID selected at initial captured request discovery.
(defun fn-pwz-byte-at (ledger worker token z file eoff elen poff compressed trailer decoded dict-id i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer
                  :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((outcome (fn-pwz-outcome ledger worker token z)))
    (if (not (eq outcome :ready)) (mv outcome nil)
      (if (and (equal (list file eoff elen poff compressed trailer decoded dict-id)
                     (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                           (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                           (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
               (natp i) (natp decoded) (< i decoded)
               (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i))
          (fn-pwz-byte ledger worker token z (- i (fn-pwz-nth 7 token)) fn-ew-buffer)
        (mv :unavailable nil)))))

;; ---------------------------------------------------------------------------
;; The verified-window cache for a decoded window (lane w-window, 2026-10-04;
;; the raw window's is fn-pwc-* in books/page-window-read.lisp).  A returned
;; decoded job whose outcome is :ready (fn-pwz-outcome: its controller is its
;; token's and published) may be released into the cache instead of freed
;; (fn-pwz-cache); the host keeps the job's token and its window buffer.  A
;; later scalar read borrows from such an entry (fn-pwz-cache-byte-at) while
;; the ledger still holds the token's :cached row, without a worker, a read or
;; a settlement.  The controller Z is NOT kept: for a published window it is
;; a function of the token (fn-pwz-plan-matches-token: the window starts at
;; the token's offset and is min(16384, DECODED - OFFSET) octets), so the hit
;; derives the window's extent from the token alone.

(defun fn-pwz-cache (ledger w token z keep)
  (declare (xargs :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (if (not (equal (fn-pwz-outcome ledger w token z) :ready))
      (mv :stale-job w ledger)
    (mv-let (word ledger1) (fn-pwz-cache-lease ledger token keep)
      (if (equal word :cached)
          (mv :cached (list (fn-prl-nth 0 w) (fn-prl-nth 1 w) :idle nil) ledger1)
        (mv :uncached w ledger)))))

(defun fn-pwz-cachedp (ledger token)
  (declare (xargs :guard t))
  (and (fn-pwz-tokenp token)
       (equal (fn-prl-nth 1 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))) :cached)))

; The window a decoded token names: OFFSET .. OFFSET + (min 16384 (DECODED -
; OFFSET)), the extent fn-pwz-plan-matches-token holds a published
; controller to.
(defun fn-pwz-token-window-length (token)
  (declare (xargs :guard t))
  (min 16384 (nfix (- (nfix (fn-pwz-nth 9 token)) (nfix (fn-pwz-nth 7 token))))))

(defun fn-pwz-cache-byte-at (ledger token file eoff elen poff compressed trailer decoded dict-id i
                                    fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard t))
  (if (and (fn-pwz-cachedp ledger token)
           (equal (list file eoff elen poff compressed trailer decoded dict-id)
                  (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                        (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                        (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))
           (natp i) (natp decoded) (< i decoded)
           (natp (fn-pwz-nth 7 token)) (<= (fn-pwz-nth 7 token) i)
           (< (- i (fn-pwz-nth 7 token)) (fn-pwz-token-window-length token)))
      (mv :byte (fn-ew-bytesi (- i (fn-pwz-nth 7 token)) fn-ew-buffer))
    (mv :miss nil)))

; KEYSTONE (the cache admits only a published window).  fn-pwz-cache answers
; :cached exactly when the job's outcome is :ready, and then its ledger is the
; lease's.
(defthm fn-pwz-cache-only-a-published-window
  (implies (equal (mv-nth 0 (fn-pwz-cache ledger w token z keep)) :cached)
           (and (equal (fn-pwz-outcome ledger w token z) :ready)
                (equal (mv-nth 1 (fn-pwz-cache-lease ledger token keep)) 
                       (mv-nth 2 (fn-pwz-cache ledger w token z keep)))
                (fn-pwz-cachedp (mv-nth 2 (fn-pwz-cache ledger w token z keep)) token)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache fn-pwz-cachedp fn-pwz-cache-lease fn-prl-build
                                     fn-prl-nth fn-prl-binding))))

; KEYSTONE (a hit is the published window).  For a job whose outcome was
; :ready and whose token the ledger holds :cached, a cache borrow of decoded
; byte I answers exactly what the job's own returned borrow
; (fn-pwz-byte-at, the same request) answered: a byte when and only when that
; borrow gave one, and the same byte.  A hit therefore only ever answers
; within its exact window (the whole descriptor, the requested offset, the
; published length) and never anything the window did not publish.
(defthm fn-pwz-a-hit-is-the-published-window
  (implies (and (equal (fn-pwz-outcome ledger worker token z) :ready)
                (fn-pwz-cachedp ledger2 token))
           (let ((hit (fn-pwz-cache-byte-at ledger2 token file eoff elen poff
                                            (fn-pwz-nth 6 token) trailer decoded
                                            (fn-pwz-nth 10 token) i fn-ew-buffer))
                 (borrow (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                         (fn-pwz-nth 6 token) trailer decoded
                                         (fn-pwz-nth 10 token) i fn-ew-buffer)))
             (and (iff (equal (mv-nth 0 hit) :byte) (equal (mv-nth 0 borrow) :byte))
                  (equal (mv-nth 1 hit) (mv-nth 1 borrow)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-byte-at fn-pwz-byte-at fn-pwz-byte fn-pwz-outcome
                                     fn-pwz-cachedp fn-pwz-token-window-length
                                     fn-pwz-plan-matches-token fn-ewz-publication))))

; A hit requires a :cached row and the exact descriptor; any other read is a
; miss (the host reads cold).
(defthm fn-pwz-hit-requires-a-cached-exact-window
  (implies (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed
                                                  trailer decoded dict-id i fn-ew-buffer))
                  :byte)
           (and (fn-pwz-cachedp ledger token)
                (equal (list file eoff elen poff compressed trailer decoded dict-id)
                       (list (fn-pwz-nth 2 token) (fn-pwz-nth 3 token) (fn-pwz-nth 4 token)
                             (fn-pwz-nth 5 token) (fn-pwz-nth 6 token) (fn-pwz-nth 8 token)
                             (fn-pwz-nth 9 token) (fn-pwz-nth 10 token)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-cache-byte-at))))

(in-theory (disable fn-pwz-plan-matches-token fn-pwz-outcome fn-pwz-byte fn-pwz-byte-at
                    fn-pwz-cache fn-pwz-cachedp fn-pwz-token-window-length fn-pwz-cache-byte-at))
