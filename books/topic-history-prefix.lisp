; Experimental topic projection over an ordered completed Store prefix.
; Recovery may scan history; a served path must carry this projection instead.
(in-package "ACL2")
(include-book "store-events")

; (:ok next snapshots accepted anchors) or (:fault next snapshots accepted
; anchors reason). The caller's installed administrator is independent of
; the topic event's own claimed administrator.
(defun fn-th-prefix-state (status next snapshots accepted anchors tail)
  (declare (xargs :guard t))
  (list status next snapshots accepted anchors tail))
(defun fn-th-prefix-find-ref (ref accepted)
  (declare (xargs :guard t))
  (if (consp accepted)
      (if (and (fn-stxa-p (car accepted))
               (equal ref (fn-th-auth-ref-of (car accepted))))
          (car accepted)
        (fn-th-prefix-find-ref ref (cdr accepted)))
    nil))

(defun fn-th-prefix-step (projection event installed-admin)
  (declare (xargs :guard t))
  (let ((status (fn-th-at 0 projection))
        (next (fn-th-at 1 projection))
        (snapshots (fn-th-at 2 projection))
        (accepted (fn-th-at 3 projection))
        (anchors (fn-th-at 4 projection)))
    (cond
     ((not (equal status :ok)) projection)
     ((or (not (fn-store-event-p event))
          (not (equal next (fn-store-event-sequence event))))
      (fn-th-prefix-state :fault next snapshots accepted anchors :sequence))
     ((fn-stxk-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) (cons event snapshots)
                          accepted anchors nil))
     ((fn-stxa-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) snapshots
                          (cons event accepted) anchors nil))
     ((fn-th-topic-eventp event)
      (let* ((ref (if (eq (fn-th-at 0 event) :topic-anchor)
                      (fn-th-at 5 event) (fn-th-at 7 event)))
             (source (fn-th-prefix-find-ref ref accepted))
             (snapshot (and source
                            (fn-stxk-find (fn-stxa-keyring-generation source)
                                          snapshots)))
             (updated
              (if (and source snapshot)
                  (if (eq (fn-th-at 0 event) :topic-anchor)
                      (fn-th-commit-anchor event source snapshot
                                           installed-admin anchors)
                    (fn-th-commit-report event source snapshot anchors))
                (fn-stmt-error :missing-historical-authorship))))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                (fn-stmt-value updated) nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors
                              (fn-stmt-value updated)))))
     (t (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted anchors nil)))))

(defun fn-th-prefix-loop (projection records installed-admin)
  (declare (xargs :guard t :measure (len records)))
  (if (consp records)
      (fn-th-prefix-loop
       (fn-th-prefix-step projection (car records) installed-admin)
       (cdr records) installed-admin)
    (if (null records) projection
      (fn-th-prefix-state :fault (fn-th-at 1 projection) (fn-th-at 2 projection)
                          (fn-th-at 3 projection) (fn-th-at 4 projection)
                          :improper-prefix))))

(defun fn-th-prefix-project (records installed-admin)
  (declare (xargs :guard t))
  (fn-th-prefix-loop (fn-th-prefix-state :ok 0 nil nil nil nil)
                     records installed-admin))

(defthm fn-th-prefix-step-failure-sticks
  (implies (not (equal (fn-th-at 0 projection) :ok))
           (equal (fn-th-prefix-step projection event installed-admin) projection))
  :hints (("Goal" :in-theory (enable fn-th-prefix-step))))

(defthm fn-th-prefix-step-topic-success-uses-prior-authorship
  (implies (and (equal (fn-th-at 0 projection) :ok)
                (fn-store-event-p event)
                (fn-th-topic-eventp event)
                (not (fn-stxk-p event))
                (not (fn-stxa-p event))
                (equal (fn-store-event-sequence event) (fn-th-at 1 projection))
                (equal (fn-th-at 0
                         (fn-th-prefix-step projection event installed-admin))
                       :ok))
           (fn-th-prefix-find-ref
            (if (eq (fn-th-at 0 event) :topic-anchor)
                (fn-th-at 5 event) (fn-th-at 7 event))
            (fn-th-at 3 projection)))
  :hints (("Goal" :in-theory
           (e/d (fn-th-prefix-step)
                (fn-store-event-p fn-th-topic-eventp
                 fn-stxk-p fn-stxa-p
                 fn-th-commit-anchor fn-th-commit-report
                 fn-th-prefix-find-ref
                 fn-th-prepare-anchor fn-th-prepare-report)))))

(in-theory (disable (:d fn-th-prefix-step) (:d fn-th-prefix-loop)))
