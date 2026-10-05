; Witnesses and teeth of the decoded window's verified-window cache (lane
; w-window, 2026-10-04): books/decoded-window-lease.lisp fn-pwz-cache-lease,
; books/decoded-window-read.lisp fn-pwz-cache / fn-pwz-cache-byte-at,
; books/decoded-worker-job.lisp fn-dwj-cache.  Every state is REACHED through
; the actual decoded job (fn-dwj-assign, -begin, -one, -read-observation), as
; tests/acl2/decoded-worker-reuse-execution-tests.lisp does.
(in-package "ACL2")
(include-book "../../books/decoded-worker-job")
(include-book "decoded-worker-reuse-execution-tests")
(include-book "must-fail-checked")

(defconst *dwct-keep* '(16 0 0 0 0))

; One decoded job to :ready, returned, then cached with KEEP (or refused).
; Answers the facts the checks below compare: the job's own borrow at byte 0
; and byte 250, the cache result, the ledger rows, and the cache's borrows
; (through the job's window buffer, the buffer the host moves) at the same
; bytes, beyond the window, under another descriptor and after eviction.
(defun dwct-run (keep fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :verify-guards nil))
  (let* ((compressed '(115 116 28 177 0 0)) (decoded 251)
         (message (append '(9 8) compressed '(7)))
         (digest (fn-blake3 message)) (trailer (fn-bch-pack digest))
         (archive (append message digest))
         (ledger (nth 1 (mv-list 2 (fn-prl-register (fn-prl-make '(200000 0 2 1 20))
                                                    7 '(64 0 1 0 0)))))
         (admit (mv-list 3 (fn-pwz-admit ledger
                     (list 7 100 (len message) 102 (len compressed) 0 trailer decoded 0)
                     '(0 0 0 1 1))))
         (token (nth 1 admit))
         (acquire (mv-list 3 (fn-pwx-acquire (nth 2 admit) (fn-pxe-new 0) token))))
    (mv-let (assigned fn-decoded-job)
      (fn-dwj-assign (nth 2 acquire) (nth 1 acquire) token token 47 fn-decoded-job)
      (declare (ignore assigned))
      (mv-let (begun fn-decoded-job) (fn-dwj-begin token fn-decoded-job)
        (declare (ignore begun))
        (mv-let (terminal fn-decoded-job) (dwret-drive 10000 archive token fn-decoded-job)
          (declare (ignore terminal))
          (let* ((returned (mv-list 3 (fn-pwx-return (nth 2 acquire) (nth 1 acquire) token)))
                 (ledger (nth 2 returned)) (worker (nth 1 returned))
                 (outcome (fn-dwj-outcome ledger worker token fn-decoded-job))
                 (b0 (mv-list 2 (fn-dwj-byte-at ledger worker token 7 100 (len message) 102
                                                (len compressed) trailer decoded 0 0 fn-decoded-job)))
                 (b250 (mv-list 2 (fn-dwj-byte-at ledger worker token 7 100 (len message) 102
                                                  (len compressed) trailer decoded 0 250 fn-decoded-job))))
            (mv-let (cword cworker cledger fn-decoded-job)
              (fn-dwj-cache ledger worker token keep fn-decoded-job)
              (let* ((hits (stobj-let ((fn-ew-buffer (fn-dwj-window fn-decoded-job)))
                             (hits)
                             (list (mv-list 2 (fn-pwz-cache-byte-at cledger token 7 100 (len message) 102
                                              (len compressed) trailer decoded 0 0 fn-ew-buffer))
                                   (mv-list 2 (fn-pwz-cache-byte-at cledger token 7 100 (len message) 102
                                              (len compressed) trailer decoded 0 250 fn-ew-buffer))
                                   (mv-list 2 (fn-pwz-cache-byte-at cledger token 7 100 (len message) 102
                                              (len compressed) trailer decoded 0 251 fn-ew-buffer))
                                   (mv-list 2 (fn-pwz-cache-byte-at cledger token 7 100 (len message) 103
                                              (len compressed) trailer decoded 0 0 fn-ew-buffer))
                                   (mv-list 2 (fn-pwz-cache-byte-at cledger token 7 100 (len message) 102
                                              (len compressed) trailer decoded 1 0 fn-ew-buffer))
                                   (mv-list 2 (fn-pwz-cache-byte-at (nth 1 (mv-list 2 (fn-prl-evict cledger token)))
                                              token 7 100 (len message) 102
                                              (len compressed) trailer decoded 0 0 fn-ew-buffer)))
                             hits))
                     (stale (mv-list 2 (fn-dwj-byte-at ledger worker token 7 100 (len message) 102
                                                       (len compressed) trailer decoded 0 0
                                                       fn-decoded-job))))
                (mv (list (nth 0 admit) outcome b0 b250 cword
                          (cdr (fn-prl-binding token (fn-prl-nth 3 cledger)))
                          (fn-prl-nth 3 (fn-prl-nth 1 cledger)) ; worker slots charged
                          hits stale
                          (equal cledger ledger) (equal cworker worker)
                          (nth 0 (mv-list 2 (fn-prl-evict cledger token)))
                          (fn-prl-nth 1 (nth 1 (mv-list 2 (fn-prl-evict cledger token))))
                          (fn-prl-nth 1 ledger))
                    fn-decoded-job)))))))))

(defun dwct-reach (keep)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-decoded-job
    (mv-let (answer fn-decoded-job)
      (let ((fn-decoded-job (fn-dwj-reserve fn-decoded-job)))
        (dwct-run keep fn-decoded-job))
      answer)))

; REACHABLE POSITIVE (KEYSTONES fn-pwz-cache-only-a-published-window,
; fn-pwz-cache-lease-keeps-only-the-buffer-and-stays-funded,
; fn-dwj-cache-only-a-ready-job, fn-pwz-a-hit-is-the-published-window,
; fn-dwj-cached-job-refuses-scalar-publication): a published decoded window
; is cached; its row is (KEEP :cached nil) and no worker slot is charged; the
; cache answers the job's own borrow at both ends of the window, nothing
; past it, nothing under another descriptor (compressed 103's POFF, another
; dictionary id), and nothing once the row is evicted, which releases KEEP
; alone; the cached job answers no borrow of the persistent worker.
(assert-event
 (let ((r (dwct-reach *dwct-keep*)))
   (and (equal (nth 0 r) :admitted)
        (equal (nth 1 r) :ready)
        (equal (nth 2 r) '(:byte 65)) (equal (nth 3 r) '(:byte 65))
        (equal (nth 4 r) :cached)
        (equal (nth 5 r) (list *dwct-keep* :cached nil))
        (equal (nth 6 r) 0)
        (equal (nth 7 r) (list (nth 2 r) (nth 3 r) '(:miss nil) '(:miss nil) '(:miss nil) '(:miss nil)))
        (not (equal (car (nth 8 r)) :byte))
        (equal (nth 11 r) :evicted)
        ; evicting the cached row leaves exactly what a plain release leaves
        (equal (nth 12 r) (fn-prs-release-reusable (nth 13 r) '(0 0 0 1 1))))))

; HYPOTHESIS REMOVAL (the pool cannot fund KEEP): the same job answers
; :uncached, the ledger and worker are unchanged, and the job is NOT retired
; (it is released as before): its own borrow still answers.
(assert-event
 (let ((r (dwct-reach '(100000000 0 0 0 0))))
   (and (equal (nth 1 r) :ready)
        (equal (nth 4 r) :uncached)
        (equal (nth 9 r) t) (equal (nth 10 r) t)
        (equal (car (nth 8 r)) :byte)
        (equal (nth 7 r) (list '(:miss nil) '(:miss nil) '(:miss nil) '(:miss nil) '(:miss nil) '(:miss nil))))))

; TEETH.  (a) the lease without the returned-phase and funding checks would
; cache an unreturned window: the statement fails for an arbitrary ledger.
(must-fail-checked
 (defthm dwct-tooth-any-window-caches
   (equal (mv-nth 0 (fn-pwz-cache-lease ledger token keep)) :cached)
   :rule-classes nil))
; (b) a hit without the :cached row hypothesis is not the job's borrow: the
; borrow answers a byte while the cache (no row) misses.
(must-fail-checked
 (defthm dwct-tooth-hit-needs-the-cached-row
   (implies (equal (fn-pwz-outcome ledger worker token z) :ready)
            (let ((hit (fn-pwz-cache-byte-at ledger2 token file eoff elen poff
                                             (fn-pwz-nth 6 token) trailer decoded
                                             (fn-pwz-nth 10 token) i fn-ew-buffer))
                  (borrow (fn-pwz-byte-at ledger worker token z file eoff elen poff
                                          (fn-pwz-nth 6 token) trailer decoded
                                          (fn-pwz-nth 10 token) i fn-ew-buffer)))
              (iff (equal (mv-nth 0 hit) :byte) (equal (mv-nth 0 borrow) :byte))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-cache-byte-at fn-pwz-byte-at fn-pwz-byte fn-pwz-outcome
                                      fn-pwz-cachedp fn-pwz-token-window-length
                                      fn-pwz-plan-matches-token fn-ewz-publication)))))
; (c) caching without the outcome hypothesis: any controller caches.
(must-fail-checked
 (defthm dwct-tooth-any-outcome-caches
   (equal (mv-nth 0 (fn-pwz-cache ledger w token z keep)) :cached)
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-pwz-cache)))))
