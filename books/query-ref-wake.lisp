; A completed/cancelled query can unblock its source owner without an I/O
; completion. The owner is a real machine reference; pool slots are not IDs.
(in-package "ACL2")
(include-book "core-scheduler-wake")
(include-book "enqueue-trace")

(defun fn2-core-query-heldp (slot gen fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (held)
  (fn2-pool-query-heldp slot gen fn2-pool) held))
(in-theory (disable fn2-core-query-heldp))

(defun fn2-query-live-phases (name states)
 (declare (xargs :verify-guards nil))
 (if (atom states) nil
  (if (member-eq (car states) '(:free :retired))
      (fn2-query-live-phases name (cdr states))
    (cons `(equal phase ,(fn2-machine-phase-constant name (car states)))
          (fn2-query-live-phases name (cdr states))))))
(defun fn2-query-live-clauses (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((name (car names))
         (kind (fn2-columns-pre "*" (fn2-columns-sym name "-KIND*")))
         (phases (fn2-query-live-phases name (fn2-machine-property name :states world)))
         (stopped (assoc-eq 'stopped (fn2-machine-property name :columns world))))
   (cons `((equal kind ,kind)
           (and (or ,@phases)
                ,(if stopped `(equal (,(fn2-machine-row-reader name 'stopped) owner fn2-core) 0) t)))
         (fn2-query-live-clauses (cdr names) world)))))
(defun fn2-query-snapshot-codes (names)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (cons (fn2-columns-sym (car names) "-SNAPSHOT-READ-CODE")
        (fn2-query-snapshot-codes (cdr names)))))
(make-event
 (value
  `(defun fn2-query-owner-livep (kind owner generation fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                    :guard-hints (("Goal" :in-theory (e/d ,(fn2-query-snapshot-codes (fn2-machine-names (w state)))
                                                          (fn2-core-wfp))))))
    (and (fn2-machine-idp owner fn2-core)
         (eq (fn2-machine-phase-read-code owner fn2-core) :ok)
         (equal (fn2-machine-kind owner fn2-core) kind)
         (equal (fn2-machine-generation owner fn2-core) generation)
         (let ((phase (fn2-machine-phase owner fn2-core)))
          (cond ,@(fn2-query-live-clauses (fn2-machine-names (w state)) (w state))
                (t nil)))))))
(in-theory (disable fn2-query-owner-livep))

(local (in-theory (disable fn2-id-decides-rows fn2-id-decides-qwake
                           fn2-id-decides-qk fn2-id-decides-qs fn2-id-decides-qg)))
(local (defthm fn2-core-id-decides-type-fc
         (implies (fn2-corep fn2-core)
                  (fn2-id-decidesp (fn2-core-id-decides fn2-core)))
         :rule-classes :forward-chaining))

; QWAKE is produced only by an actual last-reference release. Consume the
; pending notification even when its old owner has retired or been reused.
; A live source is inserted directly with the shared scheduler primitive;
; the ordinary callback wake handoff remains untouched.
; A new query must not overwrite its owner tuple while QWAKE is pending.
; Consume only a delivered or obsolete notification. A scheduler refusal
; leaves the bit retained in the stopped core; diagnostic loss never does.
(defun fn2-query-ref-consume (tx fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core))) (fn2-id-decides)
  (if (and (natp tx) (< tx (fn2-id-decides-rows fn2-id-decides)))
      (fn2-id-decides-set-qwake tx 0 fn2-id-decides) fn2-id-decides)
  fn2-core))
(fn2-core-preserves fn2-query-ref-consume (tx fn2-core) :rows nil)
(in-theory (disable fn2-query-ref-consume))

(defun fn2-query-ref-flush (tx fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (if (fn2-core-stopped-p fn2-core) fn2-core
  (stobj-let ((fn2-id-decides (fn2-core-id-decides fn2-core)))
   (pending kind owner generation)
   (if (and (natp tx) (< tx (fn2-id-decides-rows fn2-id-decides))
            (equal (fn2-id-decides-qwake tx fn2-id-decides) 1))
       (mv t (fn2-id-decides-qk tx fn2-id-decides)
             (fn2-id-decides-qs tx fn2-id-decides) (fn2-id-decides-qg tx fn2-id-decides))
     (mv nil 0 0 0))
   (cond ((not pending) fn2-core)
         ((not (fn2-query-owner-livep kind owner generation fn2-core))
          (fn2-query-ref-consume tx fn2-core))
         (t
          (let ((fn2-core (fn2-core-scheduler-wake owner fn2-core)))
           (if (fn2-core-stopped-p fn2-core) fn2-core
             (let ((fn2-core (fn2-core-record-enqueue owner fn2-core)))
              (fn2-query-ref-consume tx fn2-core)))))))))
(fn2-core-preserves fn2-query-ref-flush (tx fn2-core) :rows nil)
(in-theory (disable fn2-query-ref-flush))
