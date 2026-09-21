; The records emitted by the actual live feed transitions. No durable field
; is projected away: only the socket connection is transient. Legacy outcomes
; without time remain decodable; new retry/loss records retain the observation.
(in-package "ACL2")
(include-book "peer-feed")
(local (in-theory (enable fn-feed-vocabulary)))

(defun fn-feed-durable-projection (f)
  (declare (xargs :guard t))
  (fn-feed-with-conn f nil))

(defun fn-feed-enqueue-records (f msgid tick)
  (declare (xargs :guard t))
  (if (and (fn-feedp f) (fn-feed-namep msgid)
           (not (consp (fn-feed-find msgid (fn-feed-queue f))))
           (< (len (fn-feed-queue f))
              (fn-feed-max-queue (fn-feed-limits-of f))))
      (list (fn-feed-journal-entry :feed-enqueue
              (list (fn-feed-peer f) msgid (nfix tick))))
    nil))

(defun fn-feed-tick-records (f obs)
  (declare (xargs :guard t))
  (let ((selected (fn-feed-selection f obs)))
    (if selected
        (list (fn-feed-journal-entry :feed-offer
                (list (fn-feed-peer f) selected (fn-feed-next-attempt f)
                      (nfix (fn-clock-monotonic obs)))))
      nil)))

(defun fn-feed-lost-records (f obs)
  (declare (xargs :guard t))
  (if (fn-feedp f)
      (list (fn-feed-journal-entry :feed-lost
              (list (fn-feed-peer f) (nfix (fn-clock-monotonic obs)))))
    nil))

(defun fn-feed-observe-records (f response obs)
  (declare (xargs :guard t))
  (if (not (fn-feedp f)) nil
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
        (let* ((g (fn-feed-back-off f msgid obs))
               (gs (fn-feed-state-of msgid (fn-feed-queue g))))
          (append
           (if (fn-feed-state-inflightp st)
               (list (fn-feed-journal-entry :feed-retry
                       (list (fn-feed-peer f) msgid attempt code
                             (nfix (fn-clock-monotonic obs))))) nil)
           (if (and (fn-feed-retry-exhaustedp g msgid)
                    (not (equal gs :done)) (not (fn-feed-droppedp gs)))
               (list (fn-feed-journal-entry :feed-drop
                       (list (fn-feed-peer f) msgid :retry-bound))) nil))))
       (t (fn-feed-lost-records f obs))))))

(defun fn-feed-restart-records (f)
  (declare (xargs :guard t))
  (if (fn-feedp f)
      (list (fn-feed-journal-entry :feed-restart (list (fn-feed-peer f)))) nil))

; This driver merely selects the existing live entry; the correspondence
; theorem below is not about executing the replay transition twice.
(defun fn-feed-live-next (f event)
  (declare (xargs :guard t))
  (case (fn-frame-item 0 event)
    (:enqueue (fn-feed-enqueue f (fn-frame-item 1 event) (fn-frame-item 2 event)))
    (:tick (mv-nth 0 (fn-feed-tick-step f (fn-frame-item 1 event))))
    (:reply (mv-nth 0 (fn-feed-observe f (fn-frame-item 1 event)
                                     (fn-frame-item 2 event) (fn-frame-item 3 event))))
    (:lost (fn-feed-lost f (fn-frame-item 1 event)))
    (:restart (fn-feed-restart f))
    (:connect (if (or (null (fn-frame-item 1 event))
                      (natp (fn-frame-item 1 event)))
                  (fn-feed-with-conn f (fn-frame-item 1 event)) f))
    (otherwise f)))

(defun fn-feed-live-records (f event)
  (declare (xargs :guard t))
  (case (fn-frame-item 0 event)
    (:enqueue (fn-feed-enqueue-records f (fn-frame-item 1 event) (fn-frame-item 2 event)))
    (:tick (fn-feed-tick-records f (fn-frame-item 1 event)))
    (:reply (fn-feed-observe-records f (fn-frame-item 1 event) (fn-frame-item 3 event)))
    (:lost (fn-feed-lost-records f (fn-frame-item 1 event)))
    (:restart (fn-feed-restart-records f))
    (otherwise nil)))

(defun fn-feed-live-run (f events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (atom events) f
    (fn-feed-live-run (fn-feed-live-next f (car events)) (cdr events))))

(defun fn-feed-live-history (f events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (atom events) nil
    (append (fn-feed-live-records f (car events))
            (fn-feed-live-history (fn-feed-live-next f (car events)) (cdr events)))))

; This is only the existing field grammar's encodability, not drivenp:
; it says nothing about whether an offer/sent/outcome was admissible in the
; replay state. Successful FNFD serialization is the host boundary for it.
(defun fn-feed-live-serializablep (f events)
  (declare (xargs :guard t :measure (acl2-count events)))
  (if (atom events) t
    (and (fn-feed-journalp (fn-feed-live-records f (car events)))
         (fn-feed-live-serializablep (fn-feed-live-next f (car events))
                                    (cdr events)))))
