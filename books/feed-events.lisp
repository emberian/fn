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

; The logical feed has mathematical-natural counters, while the FNFD port has
; eight-octet naturals and a bounded payload.  This predicate is the one ACL2
; decision at that boundary: it retains neither a truncated number nor a
; partially representable record.
(defconst *fn-feed-port-digest* (make-list 32 :initial-element 0))

(defun fn-feed-record-portp (entry)
  (declare (xargs :guard t))
  (and (fn-feed-journal-entryp entry)
       ; Call the real encoder with a fixed valid-shaped trailer.  `:bad'
       ; therefore covers both the u64 field domain and the actual FNFD
       ; payload ceiling in the same path the host will seal later.
       (not (equal (fn-feed-encode (fn-feed-journal-kind entry)
                                   (fn-feed-journal-values entry)
                                   *fn-feed-port-digest*)
                   :bad))))

(defun fn-feed-records-portp (records)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (atom records)
      (null records)
    (and (fn-feed-record-portp (car records))
         (fn-feed-records-portp (cdr records)))))

; This driver merely selects the existing live entry; the correspondence
; theorem below is not about executing the replay transition twice.
(defun fn-feed-live-next (f event)
  (declare (xargs :guard t))
  (case (fn-frame-item 0 event)
    (:enqueue (fn-feed-enqueue f (fn-frame-item 1 event) (fn-frame-item 2 event)))
    (:tick (mv-let (next effects) (fn-feed-tick-step f (fn-frame-item 1 event))
             (declare (ignore effects)) next))
    (:reply (mv-let (next effects)
              (fn-feed-observe f (fn-frame-item 1 event)
                               (fn-frame-item 2 event) (fn-frame-item 3 event))
              (declare (ignore effects)) next))
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

; Effects are read from the same transition calls the live driver uses.  The
; port step below releases them only with an accepted, representable record
; batch; it never manufactures command octets in a second state machine.
(defun fn-feed-live-effects (f event)
  (declare (xargs :guard t))
  (case (fn-frame-item 0 event)
    (:tick (mv-let (next effects) (fn-feed-tick-step f (fn-frame-item 1 event))
             (declare (ignore next)) effects))
    (:reply (mv-let (next effects)
              (fn-feed-observe f (fn-frame-item 1 event)
                               (fn-frame-item 2 event) (fn-frame-item 3 event))
              (declare (ignore next)) effects))
    (otherwise nil)))

(defun fn-feed-port-step-status (result)
  (declare (xargs :guard t))
  (fn-frame-item 0 result))
(defun fn-feed-port-step-feed (result)
  (declare (xargs :guard t))
  (fn-frame-item 1 result))
(defun fn-feed-port-step-records (result)
  (declare (xargs :guard t))
  (fn-frame-item 2 result))
(defun fn-feed-port-step-effects (result)
  (declare (xargs :guard t))
  (fn-frame-item 3 result))

; This is the ACL2 boundary contract a host adapter must call before it sends
; an effect or publishes a record.  A refusal preserves every unit of queued
; work and exposes neither a record nor an effect.  It is deliberately a
; separate bounded-port profile: `fn-feed-live-next' remains total over the
; abstract natural-number feed model.
(defun fn-feed-live-port-step (f event)
  (declare (xargs :guard t))
  (let ((records (fn-feed-live-records f event)))
    (if (and (fn-feedp f) (fn-feed-records-portp records))
        (list :accepted (fn-feed-live-next f event) records
              (fn-feed-live-effects f event))
      (list :refused f nil nil))))

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

; Export theory.  The dispatchers over an event and the port check leave
; closed.  Each opens every event kind, every reply code and the FNFD encoder
; (fn-feed-record-portp calls the real encoder), and a book above that states
; a bridge over fn-feed-live-port-step opened them unless it closed them in
; its own hint: 34 to 47 definitions and 35 s between feed-totality and
; owner-feed-port before their hints closed them
; (planning/evidence/feed-wire-cost-2026-09-23.md).  A proof about one
; dispatcher enables it by name, as feed-correspondence and feed-totality
; already do.  The per-kind record emitters stay enabled: owner-feed builds
; its own record functions on them.
(deftheory fn-feed-events-vocabulary
  '((:d fn-feed-live-next) (:d fn-feed-live-records) (:d fn-feed-live-effects)
    (:d fn-feed-records-portp) (:d fn-feed-record-portp)))

(in-theory (disable fn-feed-events-vocabulary))
