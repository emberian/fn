; Experimental topic projection over an ordered completed Store prefix.
; Recovery may scan history; a served path must carry this projection instead.
(in-package "ACL2")
(include-book "store-events")

; (:ok next snapshots accepted anchors installed-admin nil), or :fault with
; a reason in the last slot. Historical installation comes from a preceding
; Store event, never from a replay caller-supplied ID.
(defun fn-th-prefix-state (status next snapshots accepted anchors installed tail)
  (declare (xargs :guard t))
  (list status next snapshots accepted anchors installed tail))
(defun fn-th-prefix-find-ref (ref accepted)
  (declare (xargs :guard t))
  (if (consp accepted)
      (if (and (fn-stxa-p (car accepted))
               (equal ref (fn-th-auth-ref-of (car accepted))))
          (car accepted)
        (fn-th-prefix-find-ref ref (cdr accepted)))
    nil))

(defun fn-th-prefix-step (projection event)
  (declare (xargs :guard t))
  (let ((status (fn-th-at 0 projection))
        (next (fn-th-at 1 projection))
        (snapshots (fn-th-at 2 projection))
        (accepted (fn-th-at 3 projection))
        (anchors (fn-th-at 4 projection))
        (installed (fn-th-at 5 projection)))
    (cond
     ((not (equal status :ok)) projection)
     ((or (not (fn-store-event-p event))
          (not (equal next (fn-store-event-sequence event))))
      (fn-th-prefix-state :fault next snapshots accepted anchors installed
                          :sequence))
     ((fn-stxk-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) (cons event snapshots)
                          accepted anchors installed nil))
     ((fn-stxa-p event)
      (fn-th-prefix-state :ok (1+ (nfix next)) snapshots
                          (cons event accepted) anchors installed nil))
     ((fn-th-local-admin-eventp event)
      (let ((updated (fn-th-local-admin-commit event installed)))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                anchors (fn-stmt-value updated) nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              :administrator-install))))
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
                      (if (fn-th-topic-v1-anchorp event)
                          (fn-th-commit-anchor event source snapshot
                                               (fn-th-at 5 installed) anchors)
                        (fn-th-commit-anchor-installed-v2
                         event source snapshot installed anchors))
                    (fn-th-commit-report event source snapshot anchors))
                (fn-stmt-error :missing-historical-authorship))))
        (if (fn-stmt-okp updated)
            (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted
                                (fn-stmt-value updated) installed nil)
          (fn-th-prefix-state :fault next snapshots accepted anchors installed
                              (fn-stmt-value updated)))))
     (t (fn-th-prefix-state :ok (1+ (nfix next)) snapshots accepted anchors
                            installed nil)))))

(defun fn-th-prefix-loop (projection records)
  (declare (xargs :guard t :measure (len records)))
  (if (consp records)
      (fn-th-prefix-loop
       (fn-th-prefix-step projection (car records))
       (cdr records))
    (if (null records) projection
      (fn-th-prefix-state :fault (fn-th-at 1 projection) (fn-th-at 2 projection)
                          (fn-th-at 3 projection) (fn-th-at 4 projection)
                          (fn-th-at 5 projection)
                          :improper-prefix))))

(defun fn-th-prefix-project (records)
  (declare (xargs :guard t))
  (fn-th-prefix-loop (fn-th-prefix-state :ok 0 nil nil nil nil nil)
                     records))

(defthm fn-th-prefix-step-failure-sticks
  (implies (not (equal (fn-th-at 0 projection) :ok))
           (equal (fn-th-prefix-step projection event) projection))
  :hints (("Goal" :in-theory (enable fn-th-prefix-step))))

(defthm fn-th-prefix-step-topic-success-uses-prior-authorship
  (implies (and (equal (fn-th-at 0 projection) :ok)
                (fn-store-event-p event)
                (fn-th-topic-eventp event)
                (not (fn-stxk-p event))
                (not (fn-stxa-p event))
                (not (fn-th-local-admin-eventp event))
                (equal (fn-store-event-sequence event) (fn-th-at 1 projection))
                (equal (fn-th-at 0
                         (fn-th-prefix-step projection event))
                       :ok))
           (fn-th-prefix-find-ref
            (if (eq (fn-th-at 0 event) :topic-anchor)
                (fn-th-at 5 event) (fn-th-at 7 event))
            (fn-th-at 3 projection)))
  :hints (("Goal" :in-theory
           (e/d (fn-th-prefix-step)
                (fn-store-event-p fn-th-topic-eventp
                 fn-stxk-p fn-stxa-p fn-th-local-admin-eventp
                 fn-th-commit-anchor fn-th-commit-report
                 fn-th-prefix-find-ref
                 fn-th-prepare-anchor fn-th-prepare-report)))))

; The recovery/Store completion step checks v2 against the earlier installed
; event carried by this prefix. The old v1 arm intentionally has no such
; generation claim and remains available only for historical replay.
(defthm fn-th-prefix-step-v2-anchor-binds-install-generation
  (implies (and (equal (fn-th-at 0 projection) :ok)
                (fn-store-event-p event)
                (fn-th-topic-eventp event)
                (not (fn-stxk-p event))
                (not (fn-stxa-p event))
                (not (fn-th-local-admin-eventp event))
                (eq (fn-th-at 0 event) :topic-anchor)
                (equal (len event) 9)
                (equal (fn-store-event-sequence event)
                       (fn-th-at 1 projection))
                (equal (fn-th-at 0 (fn-th-prefix-step projection event))
                       :ok))
           (and (fn-th-local-admin-eventp (fn-th-at 5 projection))
                (equal (fn-th-at 7 event)
                       (fn-th-at 5 (fn-th-at 5 projection)))
                (equal (fn-th-at 8 event)
                       (fn-th-at 3 (fn-th-at 5 projection)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-th-commit-anchor-installed-v2-binds-installation
                            (topic-event event)
                            (accepted (fn-th-prefix-find-ref
                                       (fn-th-at 5 event)
                                       (fn-th-at 3 projection)))
                            (snapshot
                             (and (fn-th-prefix-find-ref
                                   (fn-th-at 5 event)
                                   (fn-th-at 3 projection))
                                  (fn-stxk-find
                                   (fn-stxa-keyring-generation
                                    (fn-th-prefix-find-ref
                                     (fn-th-at 5 event)
                                     (fn-th-at 3 projection)))
                                   (fn-th-at 2 projection))))
                            (installed (fn-th-at 5 projection))
                            (anchors (fn-th-at 4 projection))))
           :in-theory
           (e/d (fn-th-prefix-step fn-th-topic-v1-anchorp)
                (fn-store-event-p fn-th-topic-eventp fn-stxk-p fn-stxa-p
                 fn-th-local-admin-eventp fn-th-commit-anchor
                 fn-th-commit-anchor-installed-v2 fn-th-commit-report
                 fn-th-prefix-find-ref fn-stxk-find)))))

(in-theory (disable (:d fn-th-prefix-step) (:d fn-th-prefix-loop)))
