; Scheduling of retained TCPCL work, independent of protocol decisions.
; A quantum bounds one physical attempt; it is not a stored-data limit.
(in-package "ACL2")
(defun fn-tcrt-read-limit () (declare (xargs :guard t)) 4096)
(defun fn-tcrt-write-end (offset total)
 (declare (xargs :guard t))
 (min (nfix total) (+ (nfix offset) (fn-tcrt-read-limit))))
(defun fn-tcrt-write-deadline (now)
 (declare (xargs :guard t)) (+ (nfix now) 30000))
(defun fn-tcrt-action (source-pending source-more writep messagesp input-due pump closing phase now deadline)
 (declare (xargs :guard t))
 (cond
  (writep (if (and (natp deadline) (<= deadline (nfix now))) :lost :write))
  (messagesp :encode)
  (closing :done)
  ((equal phase :closed) :done)
  (source-pending :source)
  (source-more :buffer)
  (input-due :read)
  (pump :pump)
  (t :local)))
(defthm fn-tcrt-write-range-is-bounded
 (implies (and (natp offset) (integerp total) (<= offset total))
  (and (<= offset (fn-tcrt-write-end offset total))
       (<= (fn-tcrt-write-end offset total) total)
       (<= (- (fn-tcrt-write-end offset total) offset) (fn-tcrt-read-limit)))))
(defthm fn-tcrt-source-custody-excludes-input
 (implies (and source-pending (not writep) (not messagesp)
               (not closing) (not (equal phase :closed)))
  (equal (fn-tcrt-action source-pending source-more writep messagesp input-due pump closing phase now deadline) :source)))
(defthm fn-tcrt-ready-write-precedes-source-and-close
 (implies (and writep (not (and (natp deadline) (<= deadline (nfix now)))))
  (equal (fn-tcrt-action source-pending source-more writep messagesp input-due pump closing phase now deadline) :write)))

; RFC9174 section4.1: close a TCP connection whose peer Contact Header never
; completes. Sixty seconds is fn's reception policy (RFC SHOULD <=60s), not a
; bound on an established session, transfer, stored source or publication.
(defun fn-tcrt-contact-deadline (now)
 (declare (xargs :guard t)) (+ (nfix now) 60000))
(defun fn-tcrt-contact-timeout-p (phase now deadline buffered)
 (declare (xargs :guard t))
 (and (not buffered) (member-eq phase '(:tcp-connected :contact))
      (natp now) (natp deadline) (<= deadline now) t))
(defthm fn-tcrt-contact-timeout-only-before-header-by-definition
 (implies (fn-tcrt-contact-timeout-p phase now deadline buffered)
  (and (not buffered) (member-eq phase '(:tcp-connected :contact))
       (natp now) (natp deadline) (<= deadline now)))
 :rule-classes nil)
(defthm fn-tcrt-established-contact-is-never-expired-by-definition
 (not (fn-tcrt-contact-timeout-p :established now deadline buffered))
 :rule-classes nil)

; Local session setup policy. RFC9174 section4.6 precedes ready-to-transfer;
; section5.1.1's negotiated idle interval does not yet exist in :messaging.
; Capture this deadline once on entering messaging; partial input never renews.
(defun fn-tcrt-init-deadline (phase now prior)
 (declare (xargs :guard t))
 (and (equal phase :messaging)
      (if (natp prior) prior (+ (nfix now) 60000))))
(defun fn-tcrt-init-timeout-p (phase now deadline buffered)
 (declare (xargs :guard t))
 (and (not buffered) (equal phase :messaging)
      (natp now) (natp deadline) (<= deadline now) t))
(defthm fn-tcrt-init-deadline-does-not-renew
 (implies (and (equal phase :messaging) (natp prior))
  (equal (fn-tcrt-init-deadline phase now prior) prior)))
(defthm fn-tcrt-init-timeout-excludes-established
 (implies (fn-tcrt-init-timeout-p phase now deadline buffered)
  (equal phase :messaging))
 :rule-classes nil)
