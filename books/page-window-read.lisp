; Physical worker/window publication join; fn-ews is the actual byte digest.
(in-package "ACL2")
(include-book "page-window-executor")
(include-book "extent-window-stream")

(defun fn-pwr-plan-matches-token (s token)
  (declare (xargs :guard (true-listp s)
                  :guard-hints (("Goal" :in-theory (enable fn-pwx-tokenp)))))
  (and (fn-pwx-tokenp token)
       (equal (fn-prl-nth 0 token) :window) (fn-prw-descriptorp (cddr token))
       (equal (nth 8 s) (fn-prl-nth 1 token))
       (equal (nth 10 s) token)
       (equal (list (nth 1 s) (nth 2 s) (nth 3 s) (nth 11 s)
                    (nth 12 s) (nth 13 s) (nth 6 s))
              (cddr token))))

; Scalar only: no vector/list alias can escape the physical borrow. I is
; relative to the requested window. Bounds and publication are core choices.
(defun fn-pwr-byte (ledger worker token s i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard (true-listp s)))
  (if (and (fn-pwx-boundp ledger worker token :returned)
           (fn-pwr-plan-matches-token s token)
           (fn-ewp-publication s)
           (natp i) (natp (nth 5 s)) (<= (nth 5 s) 16384) (< i (nth 5 s)))
      (mv :byte (fn-ew-bytesi i fn-ew-buffer))
    (mv :unavailable nil)))

(defthm fn-pwr-byte-authorization-by-definition
  (implies (equal (mv-nth 0 (fn-pwr-byte ledger worker token s i fn-ew-buffer)) :byte)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token)
                (fn-ewp-publication s)
                (natp i) (< i (nth 5 s)) (<= (nth 5 s) 16384)
                (equal (mv-nth 1 (fn-pwr-byte ledger worker token s i fn-ew-buffer))
                       (nth i (nth 0 fn-ew-buffer)))))
  :rule-classes nil)

(in-theory (disable fn-pwr-plan-matches-token fn-pwr-byte))

; The terminal failure phases of an actual plan: a short or failed read
; (:read), a damaged prefix or trailer, a broken plan.
(defun fn-pwr-fault-phasep (s)
  (declare (xargs :guard (true-listp s)))
  (and (member-eq (nth 0 s) '(:bounds :commitment :digest :state :read)) t))

; An authenticated terminal success, a failed read and stale ownership are
; separate core answers. A failed integrity check never asks for a rescan.
; Cancellation revokes publication only: a cancelled job whose own returned
; plan ended in a failure answers that fault (specs/storage.md PRF-1057,
; SCN-216: "A late store fault stops the owner even after its original
; request returned 403"); any other cancelled job, including a verified one
; and one stopped before its first read, is :cancelled.
(defun fn-pwr-outcome (ledger worker token s)
  (declare (xargs :guard (true-listp s)))
  (cond ((fn-pwx-boundp ledger worker token :cancelled-returned)
         (if (and (fn-pwr-plan-matches-token s token) (fn-pwr-fault-phasep s))
             (list :fault (nth 0 s))
           :cancelled))
        ((not (fn-pwx-boundp ledger worker token :returned)) :stale-job)
        ((not (fn-pwr-plan-matches-token s token)) '(:fault :state))
        ((fn-ewp-publication s) :ready)
        ((fn-pwr-fault-phasep s) (list :fault (nth 0 s)))
        (t '(:fault :state))))

(defthm fn-pwr-ready-requires-exact-publication-by-definition
  (implies (equal (fn-pwr-outcome ledger worker token s) :ready)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)))
  :rule-classes nil)

; KEYSTONE (PRF-1057 / SCN-216, the window arm).  A returned job whose
; plan is its token's and ended in a failure answers that failure, whether
; or not its request was cancelled first: a late short read, read error or
; damaged extent is a named fault, never swallowed by the cancellation.
(defthm fn-pwr-a-late-fault-is-a-fault-cancelled-or-not
  (implies (and (or (fn-pwx-boundp ledger worker token :returned)
                    (fn-pwx-boundp ledger worker token :cancelled-returned))
                (fn-pwr-plan-matches-token s token)
                (fn-pwr-fault-phasep s))
           (equal (fn-pwr-outcome ledger worker token s)
                  (list :fault (nth 0 s))))
  :hints (("Goal" :in-theory (enable fn-ewp-publication fn-pwr-fault-phasep))))

; KEYSTONE.  A cancelled job never publishes: its outcome is :cancelled or
; its own fault, never :ready.
(defthm fn-pwr-a-cancelled-job-never-publishes
  (implies (fn-pwx-boundp ledger worker token :cancelled-returned)
           (member-equal (fn-pwr-outcome ledger worker token s)
                         (list :cancelled (list :fault (nth 0 s)))))
  :rule-classes nil)

(in-theory (disable fn-pwr-outcome fn-pwr-fault-phasep))

; The arena passes payload-relative I. The core alone chooses the relative
; window index, after checking the unchanged physical/payload descriptor.
(defun fn-pwr-byte-at (ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard (true-listp s)))
  (let ((outcome (fn-pwr-outcome ledger worker token s)))
    (if (not (equal outcome :ready)) (mv outcome nil)
      (if (and (fn-pwx-tokenp token)
           (equal (list file eoff elen poff plen trailer)
                  (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                        (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                        (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
           (natp i) (natp plen) (< i plen)
           (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i))
      (fn-pwr-byte ledger worker token s (- i (fn-prl-nth 7 token)) fn-ew-buffer)
    (mv :unavailable nil)))))

(defthm fn-pwr-byte-at-refines-payload-coordinate-by-definition
  (implies (equal (mv-nth 0 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer)) :byte)
           (and (fn-pwx-boundp ledger worker token :returned)
                (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                (natp i) (natp plen) (< i plen)
                (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i)
                (< (- i (fn-prl-nth 7 token)) (nth 5 s))
                (equal (mv-nth 1 (fn-pwr-byte-at ledger worker token s file eoff elen poff plen trailer i fn-ew-buffer))
                       (nth (- i (fn-prl-nth 7 token)) (nth 0 fn-ew-buffer)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-outcome))))

(defun fn-pwr-cold-descriptor (file eoff elen poff plen trailer i)
  (declare (xargs :guard t))
  (list file eoff elen poff plen i trailer))

;; ---------------------------------------------------------------------------
;; The verified-window cache (lane window-read, 2026-10-04).  A returned job
;; whose outcome is :ready (fn-pwr-outcome: its plan is its token's and was
;; published) may be released into the cache instead of freed
;; (fn-pwc-cache); the host keeps the job's token, its plan S and its window
;; buffer.  A later scalar read borrows from such an entry (fn-pwc-byte-at)
;; while the ledger still holds the token's :cached row, without a worker,
;; a pread or a settlement: the realizer's warm path on the window route.

(defun fn-pwc-cache (ledger w token s keep)
  (declare (xargs :guard (true-listp s)))
  (if (not (equal (fn-pwr-outcome ledger w token s) :ready))
      (mv :stale-job w ledger)
    (fn-pwx-cache ledger w token keep)))

(defun fn-pwc-cachedp (ledger token)
  (declare (xargs :guard t))
  (and (fn-pwx-tokenp token)
       (equal (fn-prl-nth 1 (cdr (fn-prl-binding token (fn-prl-nth 3 ledger)))) :cached)))

(defun fn-pwc-byte-at (ledger token s file eoff elen poff plen trailer i fn-ew-buffer)
  (declare (xargs :stobjs fn-ew-buffer :guard (true-listp s)))
  (if (and (fn-pwc-cachedp ledger token)
           (fn-pwr-plan-matches-token s token)
           (fn-ewp-publication s)
           (equal (list file eoff elen poff plen trailer)
                  (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                        (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                        (fn-prl-nth 6 token) (fn-prl-nth 8 token)))
           (natp i) (natp plen) (< i plen)
           (natp (fn-prl-nth 7 token)) (<= (fn-prl-nth 7 token) i)
           (natp (nth 5 s)) (<= (nth 5 s) 16384)
           (< (- i (fn-prl-nth 7 token)) (nth 5 s)))
      (mv :byte (fn-ew-bytesi (- i (fn-prl-nth 7 token)) fn-ew-buffer))
    (mv :miss nil)))

; KEYSTONE (the cache's lease, read side).  Only a published job is cached:
; fn-pwc-cache answers :cached exactly when the job's outcome is :ready and
; its returned slot's buffer moves to a :cached row (fn-pwx-cache).
(defthm fn-pwc-cache-only-a-published-window
  (implies (equal (mv-nth 0 (fn-pwc-cache ledger w token s keep)) :cached)
           (and (equal (fn-pwr-outcome ledger w token s) :ready)
                (equal (mv-list 3 (fn-pwc-cache ledger w token s keep))
                       (mv-list 3 (fn-pwx-cache ledger w token keep)))
                (fn-pwc-cachedp (mv-nth 2 (fn-pwc-cache ledger w token s keep)) token)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwx-cache fn-prw-cache fn-pwx-boundp fn-pwx-tokenp
                                     fn-prl-build fn-prl-nth fn-prl-binding))))

; KEYSTONE (a hit is the published window).  For a job whose outcome was
; :ready and whose token the ledger holds :cached, a cache borrow of payload
; byte I answers exactly what the job's own returned borrow answered: a
; byte when and only when that borrow gave one, and the same byte.  So a
; hit only ever answers within its exact window (descriptor, requested
; offset, published length) and never anything the window did not publish.
(defthm fn-pwc-a-hit-is-the-published-window
  (implies (and (equal (fn-pwr-outcome ledger worker token s) :ready)
                (fn-pwc-cachedp ledger2 token))
           (let ((hit (fn-pwc-byte-at ledger2 token s file eoff elen poff plen trailer i fn-ew-buffer))
                 (borrow (fn-pwr-byte-at ledger worker token s file eoff elen poff plen trailer i
                                         fn-ew-buffer)))
             (and (iff (equal (mv-nth 0 hit) :byte) (equal (mv-nth 0 borrow) :byte))
                  (equal (mv-nth 1 hit) (mv-nth 1 borrow)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-byte-at fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome
                                     fn-pwc-cachedp))))

; A hit requires a :cached row, a plan published for its token and the
; exact descriptor; any other read is a miss (the host reads cold).
(defthm fn-pwc-hit-requires-a-cached-published-exact-window
  (implies (equal (mv-nth 0 (fn-pwc-byte-at ledger token s file eoff elen poff plen trailer i
                                            fn-ew-buffer)) :byte)
           (and (fn-pwc-cachedp ledger token)
                (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                (equal (list file eoff elen poff plen trailer)
                       (list (fn-prl-nth 2 token) (fn-prl-nth 3 token)
                             (fn-prl-nth 4 token) (fn-prl-nth 5 token)
                             (fn-prl-nth 6 token) (fn-prl-nth 8 token)))))
  :rule-classes nil)

(in-theory (disable fn-pwr-byte-at fn-pwr-cold-descriptor fn-pwc-cache fn-pwc-cachedp
                    fn-pwc-byte-at))
