; S9 guarded live boundary. The raw branch carries the established feed
; invariant; it does not run fn-feedp. The MBE guard theorem equates every
; resulting feed, durable record and effect to the total reference driver.
(in-package "ACL2")
(include-book "peer-feed-counts")
(include-book "peer-feed-invariants")

(defun fn-fcv-raw-enqueue (f msgid tick)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (or (not t)
          (not (fn-feed-namep msgid))
          (consp (fn-feed-find msgid (fn-feed-queue f)))
          (<= (fn-feed-max-queue (fn-feed-limits-of f))
              (nfix (fn-feed-undelivered f))))
      f
      (fn-feed-with-queue-counted
       f (append (fn-feed-queue f)
                 (list (fn-feed-entry msgid :queued 0 (nfix tick))))
       (+ 1 (nfix (fn-feed-undelivered f))) (fn-feed-retry-dropped f))))

(defun fn-fcv-raw-selection (f obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (and t
           (fn-clock-observationp obs)
           (fn-sched-contact-holdsp (fn-feed-contact f) obs)
           (natp (fn-feed-conn f))
           (<= (nfix (fn-feed-backoff-until f))
               (nfix (fn-clock-monotonic obs)))
           (equal (fn-feed-inflight-count (fn-feed-queue f)) 0))
      (fn-feed-head-queued (fn-feed-queue f))
      nil))

(defun fn-fcv-raw-offer (f msgid)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  ; The one-in-flight rule is enforced HERE and not only in the selection: an
  ; offer made while another entry is in flight would break `fn-feedp', and a
  ; recognizer a transition can break is not a carried invariant.
  (if (or (not t)
          (not (equal (fn-feed-state-of msgid (fn-feed-queue f)) :queued))
          (not (equal (fn-feed-inflight-count (fn-feed-queue f)) 0))
          (not (natp (fn-feed-conn f))))
      (mv f nil)
      (let ((attempt (fn-feed-next-attempt f)))
        (mv (fn-feed-make-counted (fn-feed-peer f) (fn-feed-limits-of f)
                          (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                                   (fn-feed-offered attempt))
                          (fn-feed-contact f) (fn-feed-backoff-until f)
                          (fn-feed-conn f) (+ 1 attempt) (fn-feed-undelivered f) (fn-feed-retry-dropped f))
            (list (list :command (fn-feed-conn f)
                        (fn-feed-offer-line
                         msgid
                         (fn-feed-streamingp (fn-feed-limits-of f)))))))))

(defun fn-fcv-raw-send (f msgid article)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (or (not t)
          (not (fn-feed-offeredp (fn-feed-state-of msgid (fn-feed-queue f))))
          (not (natp (fn-feed-conn f))))
      (mv f nil)
      (let ((attempt (fn-feed-state-attempt
                      (fn-feed-state-of msgid (fn-feed-queue f)))))
        (mv (fn-feed-with-queue-preserving-counts
             f (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                        (fn-feed-sent attempt)))
            (list (list :command (fn-feed-conn f)
                        (if (fn-feed-streamingp (fn-feed-limits-of f))
                            (append (fn-feed-takethis-line msgid) article)
                            article)))))))

(defun fn-fcv-raw-done (f msgid)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (or (not t)
          (not (fn-feed-state-inflightp
                (fn-feed-state-of msgid (fn-feed-queue f)))))
      f
      (fn-feed-with-queue-counted
       f (fn-feed-queue-retire (fn-feed-queue f) msgid)
       (nfix (- (nfix (fn-feed-undelivered f)) 1)) (fn-feed-retry-dropped f))))

(defun fn-fcv-raw-back-off (f msgid obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (or (not t)
          (not (fn-feed-state-inflightp
                (fn-feed-state-of msgid (fn-feed-queue f)))))
      f
      (let* ((entry (fn-feed-find msgid (fn-feed-queue f)))
             (attempts (nfix (fn-feed-entry-attempts entry)))
             (now (nfix (fn-clock-monotonic obs)))
             (delay (fn-feed-backoff-delay
                     (fn-feed-backoff-base (fn-feed-limits-of f)) attempts)))
        (fn-feed-with-backoff
         (fn-feed-with-queue-preserving-counts
          f (fn-feed-queue-requeue (fn-feed-queue f) msgid now))
         (+ now delay)))))

(defun fn-fcv-raw-lost (f obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (not t)
      f
      (let* ((now (nfix (fn-clock-monotonic obs)))
             (delay (fn-feed-backoff-delay
                     (fn-feed-backoff-base (fn-feed-limits-of f)) 0)))
        (fn-feed-with-backoff
         (fn-feed-with-conn
          (fn-feed-with-queue-preserving-counts
           f (fn-feed-queue-requeue-inflight (fn-feed-queue f) now))
          nil)
         (+ now delay)))))

(defun fn-fcv-raw-give-up (f msgid reason)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (or (not t)
          (not (consp (fn-feed-find msgid (fn-feed-queue f))))
          (fn-feed-droppedp (fn-feed-state-of msgid (fn-feed-queue f))))
      f
      (fn-feed-with-queue-counted
       f (fn-feed-queue-set-state (fn-feed-queue f) msgid
                                  (fn-feed-dropped reason))
       (fn-feed-undelivered f)
       (+ (nfix (fn-feed-retry-dropped f))
          (fn-fct-retry-drop-bit (fn-feed-dropped reason))))))

(defun fn-fcv-raw-observe (f response article obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (not t)
      (mv f nil)
      (let ((code (fn-feed-response-code response))
            (msgid (fn-feed-response-msgid response)))
        (cond ((member-equal code '(335 238)) (fn-fcv-raw-send f msgid article))
              ((member-equal code '(235 239 435 438 437 439))
               (mv (fn-fcv-raw-done f msgid) nil))
              ((member-equal code '(431 436))
               (let ((g (fn-fcv-raw-back-off f msgid obs)))
                 (mv (if (fn-feed-retry-exhaustedp g msgid)
                         (fn-fcv-raw-give-up g msgid :retry-bound)
                         g)
                     nil)))
              (t (mv (fn-fcv-raw-lost f obs) nil))))))

(defun fn-fcv-raw-restart (f)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (not t)
      f
      (fn-feed-without-backoff
       (fn-feed-with-conn
        (fn-feed-with-queue-preserving-counts f (fn-feed-queue-settle (fn-feed-queue f)))
        nil))))

(defun fn-fcv-raw-tick-step (f obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (let ((selected (fn-fcv-raw-selection f obs)))
    (if (null selected)
        (mv f nil)
        (fn-fcv-raw-offer f selected))))

(defun fn-fcv-raw-enqueue-records (f msgid tick)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (and t (fn-feed-namep msgid)
           (not (consp (fn-feed-find msgid (fn-feed-queue f))))
           (< (nfix (fn-feed-undelivered f))
              (fn-feed-max-queue (fn-feed-limits-of f))))
      (list (fn-feed-journal-entry :feed-enqueue
              (list (fn-feed-peer f) msgid (nfix tick))))
    nil))

(defun fn-fcv-raw-tick-records (f obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (let ((selected (fn-fcv-raw-selection f obs)))
    (if selected
        (list (fn-feed-journal-entry :feed-offer
                (list (fn-feed-peer f) selected (fn-feed-next-attempt f)
                      (nfix (fn-clock-monotonic obs)))))
      nil)))

(defun fn-fcv-raw-lost-records (f obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if t
      (list (fn-feed-journal-entry :feed-lost
              (list (fn-feed-peer f) (nfix (fn-clock-monotonic obs)))))
    nil))

(defun fn-fcv-raw-observe-records (f response obs)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if (not t) nil
    (let* ((code (fn-feed-response-code response))
           (msgid (fn-feed-response-msgid response))
           (st (fn-feed-state-of msgid (fn-feed-queue f)))
           (attempt (fn-feed-state-attempt st)))
      (cond
       ((member-equal code '(335 238))
        (if (and (fn-feed-offeredp st) (natp (fn-feed-conn f)))
            (list (fn-feed-journal-entry :feed-sent
                    (list (fn-feed-peer f) msgid attempt))) nil))
       ((member-equal code '(235 239 435 438 437 439))
        (if (fn-feed-state-inflightp st)
            (list (fn-feed-journal-entry :feed-outcome
                    (list (fn-feed-peer f) msgid attempt code))) nil))
       ((member-equal code '(431 436))
        (let* ((g (fn-fcv-raw-back-off f msgid obs))
               (gs (fn-feed-state-of msgid (fn-feed-queue g))))
          (append
           (if (fn-feed-state-inflightp st)
               (list (fn-feed-journal-entry :feed-retry
                       (list (fn-feed-peer f) msgid attempt code
                             (nfix (fn-clock-monotonic obs))))) nil)
           (if (and (fn-feed-retry-exhaustedp g msgid)
                    (not (fn-feed-droppedp gs)))
               (list (fn-feed-journal-entry :feed-drop
                       (list (fn-feed-peer f) msgid :retry-bound))) nil))))
       (t (fn-fcv-raw-lost-records f obs))))))

(defun fn-fcv-raw-restart-records (f)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (if t
      (list (fn-feed-journal-entry :feed-restart (list (fn-feed-peer f)))) nil))

(defun fn-fcv-raw-live-next (f event)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (case (fn-frame-item 0 event)
    (:enqueue (fn-fcv-raw-enqueue f (fn-frame-item 1 event) (fn-frame-item 2 event)))
    (:tick (mv-let (next effects) (fn-fcv-raw-tick-step f (fn-frame-item 1 event))
             (declare (ignore effects)) next))
    (:reply (mv-let (next effects)
              (fn-fcv-raw-observe f (fn-frame-item 1 event)
                               (fn-frame-item 2 event) (fn-frame-item 3 event))
              (declare (ignore effects)) next))
    (:lost (fn-fcv-raw-lost f (fn-frame-item 1 event)))
    (:restart (fn-fcv-raw-restart f))
    (:connect (if (or (null (fn-frame-item 1 event))
                      (natp (fn-frame-item 1 event)))
                  (fn-feed-with-conn f (fn-frame-item 1 event)) f))
    (otherwise f)))

(defun fn-fcv-raw-live-records (f event)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (case (fn-frame-item 0 event)
    (:enqueue (fn-fcv-raw-enqueue-records f (fn-frame-item 1 event) (fn-frame-item 2 event)))
    (:tick (fn-fcv-raw-tick-records f (fn-frame-item 1 event)))
    (:reply (fn-fcv-raw-observe-records f (fn-frame-item 1 event) (fn-frame-item 3 event)))
    (:lost (fn-fcv-raw-lost-records f (fn-frame-item 1 event)))
    (:restart (fn-fcv-raw-restart-records f))
    (otherwise nil)))

(defun fn-fcv-raw-live-effects (f event)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (case (fn-frame-item 0 event)
    (:tick (mv-let (next effects) (fn-fcv-raw-tick-step f (fn-frame-item 1 event))
             (declare (ignore next)) effects))
    (:reply (mv-let (next effects)
              (fn-fcv-raw-observe f (fn-frame-item 1 event)
                               (fn-frame-item 2 event) (fn-frame-item 3 event))
              (declare (ignore next)) effects))
    (otherwise nil)))

(defun fn-fcv-raw-live-port-step (f event)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil))
  (let ((records (fn-fcv-raw-live-records f event)))
    (if (and t (fn-feed-records-portp records))
        (list :accepted (fn-fcv-raw-live-next f event) records
              (fn-fcv-raw-live-effects f event))
      (list :refused f nil nil))))

(local
 (defthm fn-fcv-raw-enqueue-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-enqueue f msgid tick) (fn-feed-enqueue f msgid tick)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-enqueue fn-feed-enqueue fn-feed-count-relationp)
                (fn-feedp fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-selection-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-selection f obs) (fn-feed-selection f obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-selection fn-feed-selection)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-offer-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (mv-list 2 (fn-fcv-raw-offer f msgid)) (mv-list 2 (fn-feed-offer f msgid))))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-offer fn-feed-offer)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-send-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (mv-list 2 (fn-fcv-raw-send f msgid article)) (mv-list 2 (fn-feed-send f msgid article))))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-send fn-feed-send)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-done-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-done f msgid) (fn-feed-done f msgid)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-done fn-feed-done)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-back-off-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-back-off f msgid obs) (fn-feed-back-off f msgid obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-back-off fn-feed-back-off)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-lost-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-lost f obs) (fn-feed-lost f obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-lost fn-feed-lost)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-give-up-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-give-up f msgid reason) (fn-feed-give-up f msgid reason)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-give-up fn-feed-give-up)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-observe-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (mv-list 2 (fn-fcv-raw-observe f response article obs)) (mv-list 2 (fn-feed-observe f response article obs))))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-observe fn-feed-observe)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-restart-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-restart f) (fn-feed-restart f)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-restart fn-feed-restart)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-tick-step-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (mv-list 2 (fn-fcv-raw-tick-step f obs)) (mv-list 2 (fn-feed-tick-step f obs))))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-tick-step fn-feed-tick-step)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-enqueue-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-enqueue-records f msgid tick) (fn-feed-enqueue-records f msgid tick)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-enqueue-records fn-feed-enqueue-records fn-feed-count-relationp)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-tick-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-tick-records f obs) (fn-feed-tick-records f obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-tick-records fn-feed-tick-records)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-lost-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-lost-records f obs) (fn-feed-lost-records f obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-lost-records fn-feed-lost-records)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-observe-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-observe-records f response obs) (fn-feed-observe-records f response obs)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-observe-records fn-feed-observe-records)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-restart-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-restart-records f) (fn-feed-restart-records f)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-restart-records fn-feed-restart-records)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-live-next-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-live-next f event) (fn-feed-live-next f event)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-live-next fn-feed-live-next)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-live-records-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-live-records f event) (fn-feed-live-records f event)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-live-records fn-feed-live-records)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-effects fn-fcv-raw-live-port-step))))))

(local
 (defthm fn-fcv-raw-live-effects-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-live-effects f event) (fn-feed-live-effects f event)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-live-effects fn-feed-live-effects)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-port-step))))))

(defthm fn-fcv-raw-live-port-step-is-reference
  (implies (and (fn-feedp f) (fn-feed-count-relationp f))
           (equal (fn-fcv-raw-live-port-step f event) (fn-feed-live-port-step f event)))
  :hints (("Goal" :in-theory
           (e/d (fn-fcv-raw-live-port-step fn-feed-live-port-step)
                (fn-feedp fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects)))))

(defun fn-feed-live-port-step-carried (f event)
  (declare (xargs :guard (and (fn-feedp f) (fn-feed-count-relationp f))
                  :verify-guards nil
                  :guard-hints (("Goal" :use fn-fcv-raw-live-port-step-is-reference
                                 :in-theory (disable fn-feed-live-port-step
                                                    fn-fcv-raw-live-port-step)))))
  (mbe :logic (fn-feed-live-port-step f event)
       :exec (fn-fcv-raw-live-port-step f event)))

(local
 (defthm fn-fcv-feedp-next-attempt-natural
   (implies (fn-feedp f) (natp (fn-feed-next-attempt f)))
   :hints (("Goal" :in-theory (enable fn-feedp)))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm fn-fcv-feedp-limit-fields-natural
   (implies (fn-feedp f)
            (and (natp (fn-feed-max-queue (fn-feed-limits-of f)))
                 (natp (fn-feed-backoff-base (fn-feed-limits-of f)))))
   :hints (("Goal" :in-theory (enable fn-feedp fn-feed-limitsp fn-feed-max-queue
                                      fn-feed-backoff-base)))
   :rule-classes (:rewrite :forward-chaining)))

(verify-guards fn-fcv-raw-enqueue)
(verify-guards fn-fcv-raw-selection)
(verify-guards fn-fcv-raw-offer)
(verify-guards fn-fcv-raw-send)
(verify-guards fn-fcv-raw-done)
(verify-guards fn-fcv-raw-back-off)
(verify-guards fn-fcv-raw-lost)
(verify-guards fn-fcv-raw-give-up)
(verify-guards fn-fcv-raw-observe)
(verify-guards fn-fcv-raw-restart)
(verify-guards fn-fcv-raw-tick-step)
(verify-guards fn-fcv-raw-enqueue-records)
(verify-guards fn-fcv-raw-tick-records)
(verify-guards fn-fcv-raw-lost-records)
(verify-guards fn-fcv-raw-observe-records)
(verify-guards fn-fcv-raw-restart-records)
(verify-guards fn-fcv-raw-live-next)
(verify-guards fn-fcv-raw-live-records)
(verify-guards fn-fcv-raw-live-effects)
(verify-guards fn-fcv-raw-live-port-step)

(verify-guards fn-feed-live-port-step-carried)

(in-theory (disable fn-fcv-raw-enqueue fn-fcv-raw-selection fn-fcv-raw-offer fn-fcv-raw-send fn-fcv-raw-done fn-fcv-raw-back-off fn-fcv-raw-lost fn-fcv-raw-give-up fn-fcv-raw-observe fn-fcv-raw-restart fn-fcv-raw-tick-step fn-fcv-raw-enqueue-records fn-fcv-raw-tick-records fn-fcv-raw-lost-records fn-fcv-raw-observe-records fn-fcv-raw-restart-records fn-fcv-raw-live-next fn-fcv-raw-live-records fn-fcv-raw-live-effects fn-fcv-raw-live-port-step fn-feed-live-port-step-carried))
