; One immutable local operator binding for the experimental root-only profile.
; The OS supplies a connected same-euid peer observation. ACL2 owns the
; bounded UID, fresh observed ID, and authorization comparison. Neither is a
; portable topic controller or an NNTP principal.
(in-package "ACL2")
(include-book "topic-history-admission")

(defun fn-th-local-admin-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event) (equal (len event) 6)
       (eq (fn-th-at 0 event) :topic-admin-install)
       (fn-record-uint32p (fn-th-at 1 event))
       (fn-record-uint32p (fn-th-at 2 event))
       (fn-record-uint32p (fn-th-at 3 event))
       (fn-record-uint32p (fn-th-at 4 event))
       (fn-th-exact-octets-p (fn-th-at 5 event) 32)))

(defun fn-th-local-admin-install (sequence txid generation observed-uid
                                            entropy-id installed)
  (declare (xargs :guard t))
  (cond ((not (null installed)) (fn-stmt-error :already-installed))
        ((not (fn-record-uint32p observed-uid))
         (fn-stmt-error :uid))
        ((not (fn-th-exact-octets-p entropy-id 32))
         (fn-stmt-error :administrator-id))
        (t (let ((event (list :topic-admin-install sequence txid generation
                              observed-uid entropy-id)))
             (if (fn-th-local-admin-eventp event)
                 (fn-stmt-ok event)
               (fn-stmt-error :coordinates))))))

; Completion and historical replay install precisely the immutable event.
; Replay does not compare an old caller with the current process UID.
(defun fn-th-local-admin-commit (event installed)
  (declare (xargs :guard t))
  (if (and (null installed) (fn-th-local-admin-eventp event))
      (fn-stmt-ok event)
    (fn-stmt-error :administrator-install)))

(defun fn-th-local-admin-current-id (installed observed-uid)
  (declare (xargs :guard t))
  (if (and (fn-th-local-admin-eventp installed)
           (fn-record-uint32p observed-uid)
           (equal observed-uid (fn-th-at 4 installed)))
      (fn-th-at 5 installed)
    nil))

(defun fn-th-prepare-anchor-local
    (sequence txid generation accepted snapshot observed-uid quota
              installed anchors)
  (declare (xargs :guard t))
  (let ((caller-id (fn-th-local-admin-current-id installed observed-uid)))
    (if (not caller-id) (fn-stmt-error :administrator)
      (fn-th-prepare-anchor sequence txid generation accepted snapshot
                            caller-id (fn-th-at 5 installed) quota anchors))))

(defthm fn-th-prepare-anchor-local-requires-installed-uid
  (implies (fn-stmt-okp
            (fn-th-prepare-anchor-local
             sequence txid generation accepted snapshot observed-uid
             quota installed anchors))
           (and (fn-th-local-admin-eventp installed)
                (equal observed-uid (fn-th-at 4 installed))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-th-prepare-anchor-local fn-th-local-admin-current-id)
                (fn-th-prepare-anchor fn-th-local-admin-eventp)))))
