; E2 committed Store prefix projection.  This is the one interpreter used by
; live finish and reopen; it does not authorize a proposed or staged write.
(in-package "ACL2")
(include-book "store-events")

; NIL means no bootstrap has committed.  Once initialized, the consumer
; state's frontier is the next dense Store journal sequence, including every
; article and nonarticle record after bootstrap.
(defun fn-cpe-projection-advance (s next)
  (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 2 s) next
               (fn-cp-nth 4 s) (fn-cp-nth 5 s)))

(defun fn-cpe-projection-decision (s op)
  (case (fn-cp-nth 0 op)
    (:register
     (fn-cp-register s (fn-cp-nth 2 op) (fn-cp-nth 1 op)
                     (fn-cp-nth 3 op) (fn-cp-nth 4 op) (fn-cp-nth 5 op)))
    (:ack
     (let ((cursor (fn-cp-nth 1 op)))
       (fn-cp-ack s (fn-cp-nth 4 cursor) (fn-cp-nth 6 cursor)
                  (fn-cp-nth 7 cursor) cursor)))
    (:rebase
     (fn-cp-rebase s (fn-cp-nth 2 op) (fn-cp-nth 1 op)
                   (fn-cp-nth 3 op) (fn-cp-nth 4 op) (fn-cp-nth 5 op)))
    (:unregister
     (let ((entry (fn-cp-find (fn-cp-nth 1 op) (fn-cp-nth 5 s))))
       (fn-cp-unregister s (fn-cp-nth 2 entry) (fn-cp-nth 1 op))))
    (otherwise (list :refused :operation))))

; Result is (:ok projection) or (:refused reason).  The envelope's exact
; sequence is checked here as well as by Store files.  A replay that drops a
; nonarticle record therefore cannot silently renumber an issued cursor.
(defun fn-cpe-projection-step (s event expected)
  (if (or (not (fn-store-event-p event))
          (not (fn-cp-uintp expected))
          (equal expected *fn-cbor-max-uint*)
          (not (equal (fn-store-event-sequence event) expected)))
      (list :refused :sequence)
    (if (not (fn-cpe-eventp event))
        (if (null s) (list :ok nil)
          (if (equal (fn-cp-nth 3 s) expected)
              (list :ok (fn-cpe-projection-advance s (1+ expected)))
            (list :refused :frontier)))
      (let* ((op (fn-cpe-operation event))
             (kind (fn-cp-nth 0 op)))
        (cond
         ((eq kind :bootstrap)
          (if (null s)
              (list :ok (fn-cp-initial (fn-cp-nth 1 op)
                                       (fn-cp-nth 2 op) (1+ expected)))
            (list :refused :duplicate-bootstrap)))
         ((null s) (list :refused :unbootstrapped))
         ((not (equal (fn-cp-nth 3 s) expected))
          (list :refused :frontier))
         ((eq kind :rollover)
          (if (equal (fn-cp-nth 1 op) (fn-cp-nth 2 s))
              (list :refused :same-incarnation)
            (list :ok
                  (fn-cp-state (fn-cp-nth 1 s) (fn-cp-nth 1 op)
                               (1+ expected) (fn-cp-nth 4 s) nil))))
         ((equal (fn-cpe-projection-decision s op) (list :write op))
          (list :ok (fn-cpe-projection-advance (fn-cp-apply s op)
                                                 (1+ expected))))
         (t (list :refused :operation)))))))

(defun fn-cpe-projection-replay (s records expected)
  (declare (xargs :measure (len records)))
  (if (not (consp records))
      (if (null records) (list :ok s) (list :refused :records))
    (let ((one (fn-cpe-projection-step s (car records) expected)))
      (if (eq (car one) :ok)
          (fn-cpe-projection-replay (fn-cp-nth 1 one) (cdr records)
                                    (1+ (nfix expected)))
        one))))

(verify-guards fn-cpe-projection-advance)
(verify-guards fn-cpe-projection-decision)
(verify-guards fn-cpe-projection-step)
(verify-guards fn-cpe-projection-replay)

(defthm fn-cpe-projection-step-ok-pair-by-definition
  (implies (eq (car (fn-cpe-projection-step s event expected)) :ok)
           (equal (fn-cpe-projection-step s event expected)
                  (list :ok (fn-cp-nth 1
                             (fn-cpe-projection-step s event expected)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-cpe-projection-step))))

(defthm fn-cpe-projection-replay-append-one
  (implies (and (natp start)
                (true-listp prefix)
                (equal (fn-cpe-projection-replay s prefix start)
                       (list :ok after)))
           (equal (fn-cpe-projection-replay
                   s (append prefix (list event)) start)
                  (fn-cpe-projection-step after event
                                          (+ start (len prefix)))))
  :hints (("Goal" :induct (fn-cpe-projection-replay s prefix start)
           :in-theory (enable fn-cpe-projection-replay))))

; Store integration will prove this result equals the projection carried by
; its finish path.  No native or checkpoint caller uses this book alone.
(in-theory (disable (:d fn-cpe-projection-step)
                    (:d fn-cpe-projection-replay)))
