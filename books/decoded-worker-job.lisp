; One private physical decoded activation. The actual pool draw must precede
; construction; this book establishes no complete allocator/GC tariff.
(in-package "ACL2")
(include-book "decoded-worker-assignment")

(defstobj fn-decoded-job
  (fn-dwj-carry :type fn-pww-carry)
  (fn-dwj-input :type fn-octets)
  (fn-dwj-hash :type pgs-digest-state)
  (fn-dwj-zin :type fn-zin-st)
  (fn-dwj-win :type fn-zin-win)
  (fn-dwj-tab :type fn-zin-tab)
  (fn-dwj-out :type fn-zin-out)
  (fn-dwj-window :type fn-ew-buffer)
  :inline t)

(defun fn-dwj-assign (ledger worker token root incarnation fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (fn-octets (fn-dwj-input fn-decoded-job)))
    (word fn-pww-carry fn-octets)
    (mv-let (word fn-pww-carry)
      (fn-dwa-assign ledger worker token root incarnation fn-pww-carry)
      (let ((fn-octets (if (eq word :decoded-assigned)
                          (fn-octets-reserve 64 fn-octets) fn-octets)))
        (mv word fn-pww-carry fn-octets)))
    (mv word fn-decoded-job)))

(defun fn-dwj-begin (token fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (pgs-digest-state (fn-dwj-hash fn-decoded-job))
              (fn-zin-st (fn-dwj-zin fn-decoded-job))
              (fn-zin-win (fn-dwj-win fn-decoded-job))
              (fn-zin-tab (fn-dwj-tab fn-decoded-job))
              (fn-zin-out (fn-dwj-out fn-decoded-job)))
    (word fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (fn-dwc-begin token fn-pww-carry pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv word fn-decoded-job)))

(defun fn-dwj-one (token fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (fn-octets (fn-dwj-input fn-decoded-job))
              (pgs-digest-state (fn-dwj-hash fn-decoded-job))
              (fn-zin-st (fn-dwj-zin fn-decoded-job))
              (fn-zin-win (fn-dwj-win fn-decoded-job))
              (fn-zin-tab (fn-dwj-tab fn-decoded-job))
              (fn-zin-out (fn-dwj-out fn-decoded-job))
              (fn-ew-buffer (fn-dwj-window fn-decoded-job)))
    (word effect fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
    (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
    (mv word effect fn-decoded-job)))

(defun fn-dwj-read-observation (token revision status fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (fn-octets (fn-dwj-input fn-decoded-job))
              (pgs-digest-state (fn-dwj-hash fn-decoded-job))
              (fn-ew-buffer (fn-dwj-window fn-decoded-job)))
    (word fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
    (fn-dwc-read-observation token revision status fn-pww-carry fn-octets pgs-digest-state fn-ew-buffer)
    (mv word fn-decoded-job)))

(defun fn-dwj-outcome (ledger worker token fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job)))
    (word)
    (let ((z (fn-dwa-controller fn-pww-carry)))
      (if (and (true-listp z) (true-listp (nth 1 z)))
          (fn-pwz-outcome ledger worker token z) :stale-decoded-worker))
    word))

(defun fn-dwj-byte-at (ledger worker token file eoff elen poff compressed trailer decoded dict-id i fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job))
              (fn-ew-buffer (fn-dwj-window fn-decoded-job)))
    (word byte)
    (let ((z (fn-dwa-controller fn-pww-carry)))
      (if (and (true-listp z) (true-listp (nth 1 z)))
          (fn-pwz-byte-at ledger worker token z
                   file eoff elen poff compressed trailer decoded dict-id i fn-ew-buffer)
        (mv :stale-decoded-worker nil)))
    (mv word byte)))

(verify-guards fn-dwj-assign)
(verify-guards fn-dwj-begin)
(verify-guards fn-dwj-one)
(verify-guards fn-dwj-read-observation)
(verify-guards fn-dwj-outcome)
(verify-guards fn-dwj-byte-at)

; Retire only authority-bearing metadata. Private byte arrays remain reserved
; for this physical worker and cannot escape through the scalar borrow API.
(defun fn-dwj-retire (ledger worker token fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job)))
    (word fn-pww-carry)
    (fn-dwa-retire ledger worker token fn-pww-carry)
    (mv word fn-decoded-job)))
(verify-guards fn-dwj-retire)

(defthm fn-dwj-retirement-preserves-private-backing
  (let ((next (mv-nth 1 (fn-dwj-retire ledger worker token job))))
    (and (equal (fn-dwj-input next) (fn-dwj-input job))
         (equal (fn-dwj-hash next) (fn-dwj-hash job))
         (equal (fn-dwj-zin next) (fn-dwj-zin job))
         (equal (fn-dwj-win next) (fn-dwj-win job))
         (equal (fn-dwj-tab next) (fn-dwj-tab job))
         (equal (fn-dwj-out next) (fn-dwj-out job))
         (equal (fn-dwj-window next) (fn-dwj-window job))))
  :hints (("Goal" :in-theory (disable fn-dwa-retire))))

;; The verified-window cache (lane w-window): the returned job's window buffer
;; leaves the persistent worker for the realizer's cache instead of being freed.
;; ONE step, ACL2's: the job's controller is read from its own carry
;; (fn-pwz-cache: only a :ready outcome is cached, the ledger row becomes the
;; :cached row KEEP), and the carry's authority is retired against the
;; PRE-cache ledger (fn-dwa-retire needs the :returned row the lease replaces),
;; so a cached job is a retired job: it refuses every scalar borrow.  Refused
;; unchanged (word :uncached or :stale-*) it is released as before; the host
;; moves the window buffer only on :cached.
(defun fn-dwj-cache (ledger worker token keep fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t :verify-guards nil))
  (stobj-let ((fn-pww-carry (fn-dwj-carry fn-decoded-job)))
    (word worker1 ledger1 fn-pww-carry)
    (let ((z (fn-dwa-controller fn-pww-carry)))
      (if (and (true-listp z) (true-listp (nth 1 z)))
          (mv-let (cword worker2 ledger2) (fn-pwz-cache ledger worker token z keep)
            (if (not (equal cword :cached))
                (mv cword worker ledger fn-pww-carry)
              (mv-let (rword fn-pww-carry) (fn-dwa-retire ledger worker token fn-pww-carry)
                (if (equal rword :reusable)
                    (mv :cached worker2 ledger2 fn-pww-carry)
                  (mv :uncached worker ledger fn-pww-carry)))))
        (mv :stale-decoded-worker worker ledger fn-pww-carry)))
    (mv word worker1 ledger1 fn-decoded-job)))
(verify-guards fn-dwj-cache)

; KEYSTONE (only a published job is cached).  :cached is answered only for a
; job whose own outcome is :ready, and then the ledger and worker are the
; cache's (fn-pwz-cache over the job's controller).
(defthm fn-dwj-cache-only-a-ready-job
  (implies (equal (mv-nth 0 (fn-dwj-cache ledger worker token keep job)) :cached)
           (and (equal (fn-dwj-outcome ledger worker token job) :ready)
                (equal (mv-nth 1 (fn-dwj-cache ledger worker token keep job))
                       (mv-nth 1 (fn-pwz-cache ledger worker token (fn-dwa-controller (fn-dwj-carry job)) keep)))
                (equal (mv-nth 2 (fn-dwj-cache ledger worker token keep job))
                       (mv-nth 2 (fn-pwz-cache ledger worker token (fn-dwa-controller (fn-dwj-carry job)) keep)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-dwj-cache fn-dwj-outcome fn-dwa-controller)
                                  (fn-dwa-retire fn-pwz-cache fn-pwz-outcome))
           :use ((:instance fn-pwz-cache-only-a-published-window
                            (w worker) (z (fn-dwa-controller (fn-dwj-carry job))))))))

; Run under the startup baseline before any executor thread or job. Reserve
; changes capacity only; all logical bytes/authority remain exactly unchanged.
(defun fn-dwj-reserve (fn-decoded-job)
  (declare (xargs :stobjs fn-decoded-job :guard t))
  (stobj-let ((fn-octets (fn-dwj-input fn-decoded-job))
              (fn-zin-win (fn-dwj-win fn-decoded-job))
              (fn-zin-tab (fn-dwj-tab fn-decoded-job))
              (fn-zin-out (fn-dwj-out fn-decoded-job)))
    (fn-octets fn-zin-win fn-zin-tab fn-zin-out)
    (let* ((fn-octets (fn-octets-reserve 64 fn-octets))
           (fn-zin-win (fn-zin-win-reserve *fn-zin-win-octets* fn-zin-win))
           (fn-zin-tab (fn-zin-tab-reserve *fn-zin-tab-octets* fn-zin-tab))
           (fn-zin-out (fn-zin-out-reserve 64 fn-zin-out)))
      (mv fn-octets fn-zin-win fn-zin-tab fn-zin-out))
    fn-decoded-job))

(defthm fn-dwj-retired-job-refuses-scalar-publication
  (implies (equal (mv-nth 0 (fn-dwj-retire ledger worker token job)) :reusable)
    (not (equal (mv-nth 0
             (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                             trailer decoded dict-id i
                             (mv-nth 1 (fn-dwj-retire ledger worker token job))))
           :byte)))
  :hints (("Goal" :in-theory (e/d (fn-dwj-retire fn-dwj-byte-at fn-dwa-controller
                                           fn-pwz-byte-at fn-pwz-outcome fn-pwz-plan-matches-token fn-ewz-publication)
                                  (fn-dwa-retire fn-pwx-boundp))
           :use ((:instance fn-dwa-retirement-revokes-prior-authority
                            (carry (fn-dwj-carry job)))))))

; KEYSTONE (a cached job is a retired job).  After :cached the job's carry is
; retired (its authority revoked), so no scalar borrow of the persistent
; worker's backing is answered: the window the cache now owns is not also
; readable through the worker that is about to be reused.
(defthm fn-dwj-cached-job-refuses-scalar-publication
  (implies (equal (mv-nth 0 (fn-dwj-cache ledger worker token keep job)) :cached)
    (not (equal (mv-nth 0
             (fn-dwj-byte-at query-ledger query-worker query-token file eoff elen poff compressed
                             trailer decoded dict-id i
                             (mv-nth 3 (fn-dwj-cache ledger worker token keep job))))
           :byte)))
  :hints (("Goal" :in-theory (e/d (fn-dwj-cache fn-dwj-byte-at fn-dwa-controller
                                           fn-pwz-byte-at fn-pwz-outcome fn-pwz-plan-matches-token
                                           fn-ewz-publication)
                                  (fn-dwa-retire fn-pwx-boundp fn-pwz-cache))
           :use ((:instance fn-dwa-retirement-revokes-prior-authority
                            (carry (fn-dwj-carry job)))))))
