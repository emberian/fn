; Props, before implementation: the due/request/capture/done/abandoned result
; and all ten post-fields equal the previous host read/decision/write
; composition. Capture advances serial, and abandonment requires holdsp for
; (inflight, pass, serial). Done uses the count-based release rule it used
; before this move; it does not acquire a new serial condition. Recovery
; installs the stripped base and clears eight fields, preserving serial.
(in-package "ACL2")
(include-book "owner-publication-state")
(include-book "owner-publication-lifecycle")
(include-book "owner-compact-request")
(include-book "store-checkpoint-arena-writer")

(defun fn-opub-due (r profile count suffix budget space now)
  (declare (xargs :guard t))
  (if (not profile) (mv :idle r)
    (let ((next (fn-ock-requested-next
                 (fn-opub-get :durable r) count suffix
                 (fn-opl-attempted (fn-opub-get :deferred r)
                                   (fn-opub-get :attempted r) count now)
                 (fn-opub-get :inflight r)
                 (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now)
                 (fn-opub-get :requested r))))
      (cond ((eq next :coalesce) (mv :inflight (fn-opub-put :pending t r)))
            ((eq next :inflight) (mv :inflight r))
            ((eq next :due) (mv next (fn-opub-put :pending nil r)))
            (t (mv next (fn-opub-put :requested nil (fn-opub-put :pending nil r))))))))

(defun fn-opub-request (r profile count budget space now)
  (declare (xargs :guard t))
  (if (not profile) (mv :nothing-to-compact r)
    (let ((word (fn-ock-request-word
                 (fn-opub-get :durable r) count
                 (fn-opl-attempted (fn-opub-get :deferred r)
                                   (fn-opub-get :attempted r) count now)
                 (fn-opub-get :inflight r)
                 (fn-opl-blockedp (fn-opub-get :deferred r) budget space count now))))
      (mv word (fn-opub-put :requested (and (member-eq word '(:requested :coalesced)) t) r)))))

(defun fn-opub-capture (r count)
  (declare (xargs :guard t))
  (let* ((serial (fn-opl-next-serial (fn-opub-get :serial r)))
         (r (fn-opub-put :attempted count r))
         (r (fn-opub-put :inflight count r))
         (r (fn-opub-put :serial serial r))
         (r (fn-opub-put :requested nil r)))
    (mv serial r)))

(defun fn-opub-capture-context
  (r count configs records segment budget frontier free revision identity)
  (declare (xargs :guard (natp count)))
  (mv-let (serial next) (fn-opub-capture r count)
    (let ((durable (fn-opub-get :durable r)))
      (mv (list (fn-opub-get :base r) configs records segment count
                (- count (if (natp durable) durable 0)) budget frontier free revision
                (fn-opub-get :base-payloads r) identity serial)
          next))))

; The host-called capture carries exactly the slot transition proved below;
; the entire return tuple is constructed here, with no host-side state reads.
(defthm fn-opub-capture-context-slot-by-definition
  (equal (mv-nth 1 (fn-opub-capture-context
                   r count configs records segment budget frontier free revision identity))
         (mv-nth 1 (fn-opub-capture r count))))

(defthm fn-opub-capture-context-serial-by-definition
  (equal (nth 12 (mv-nth 0 (fn-opub-capture-context
                          r count configs records segment budget frontier free revision identity)))
         (mv-nth 0 (fn-opub-capture r count))))

(defun fn-opub-done (r next payloads durablep verdict)
  (declare (xargs :guard t))
  (let* ((r (fn-opub-put :base (fn-scka-strip-base next) r))
         (r (fn-opub-put :base-payloads (and (natp payloads) payloads) r))
         (released (fn-orc-release-slot (list :publication (fn-sco-sequence next))
                                       (fn-opub-get :pass r) (fn-opub-get :inflight r)))
         (r (fn-opub-put :inflight (cadr released) r))
         (r (if durablep (fn-opub-put :durable (fn-sco-sequence next) r) r))
         (r (fn-opub-put :deferred
                         (cond ((and (consp verdict) (eq (car verdict) :deferred)) verdict)
                               (durablep nil) (t (fn-opub-get :deferred r))) r)))
    (mv (if durablep (fn-sco-sequence next) :none) r)))

(defun fn-opub-abandoned (r count serial outcome now)
  (declare (xargs :guard t))
  (let* ((pass (fn-opub-get :pass r))
         (inflight (fn-opub-get :inflight r))
         (current (fn-opub-get :serial r))
         (result (fn-opl-settle count serial outcome now pass inflight current
                                (fn-opub-get :deferred r)))
         (r (fn-opub-put :inflight (cadr result) r))
         (r (fn-opub-put :deferred (caddr result) r)))
    (mv (if (fn-opl-holdsp count serial pass inflight current) (caddr result) :stale) r)))

(defun fn-opub-install (r base)
  (declare (xargs :guard t))
  (list nil base nil nil nil nil nil nil (fn-opub-get :serial r) nil))

(defun fn-opub-reclaim-install (r base count)
  (declare (xargs :guard t))
  (list count base nil nil count nil (fn-opub-get :pending r)
        (fn-opub-get :requested r) (fn-opub-get :serial r) nil))

(defthm fn-opub-capture-serial-increases
  (< (nfix (fn-opub-get :serial r)) (mv-nth 0 (fn-opub-capture r count)))
  :hints (("Goal" :in-theory (enable fn-opl-next-serial))))

(defthm fn-opub-capture-establishes-holder
  (implies (and (natp count)
                (or (not (fn-opub-get :pass r)) (equal (fn-opub-get :pass r) :dry-run)))
           (let ((next (mv-nth 1 (fn-opub-capture r count))))
             (fn-opl-holdsp count (mv-nth 0 (fn-opub-capture r count))
                           (fn-opub-get :pass next) (fn-opub-get :inflight next)
                           (fn-opub-get :serial next))))
  :hints (("Goal" :in-theory (e/d (fn-opl-holdsp) (fn-opub-get fn-opub-put)))))

(defthm fn-opub-done-does-not-release-another-holder
  (implies (or (and (fn-opub-get :pass r) (not (equal (fn-opub-get :pass r) :dry-run)))
               (not (equal (fn-opub-get :inflight r) (fn-sco-sequence next))))
           (equal (fn-opub-get :inflight (mv-nth 1 (fn-opub-done r next payloads durablep verdict)))
                  (fn-opub-get :inflight r)))
  :hints (("Goal" :in-theory (e/d (fn-orc-release-slot) (fn-opub-get fn-opub-put)))))

(defthm fn-opub-abandoned-stale-fields-unchanged
  (implies (not (fn-opl-holdsp count serial (fn-opub-get :pass r)
                             (fn-opub-get :inflight r) (fn-opub-get :serial r)))
           (and (equal (mv-nth 0 (fn-opub-abandoned r count serial outcome now)) :stale)
                (equal (fn-opub-get field (mv-nth 1 (fn-opub-abandoned r count serial outcome now)))
                       (fn-opub-get field r))))
  :hints (("Goal" :in-theory (disable fn-opub-get fn-opub-put fn-opl-settle fn-opl-holdsp))))

(defthm fn-opub-install-preserves-serial
  (equal (fn-opub-get :serial (fn-opub-install r base)) (fn-opub-get :serial r)))

(defun fn-opub-coherentp (r)
  (declare (xargs :guard t))
  (let ((inflight (fn-opub-get :inflight r))
        (pass (fn-opub-get :pass r))
        (serial (fn-opub-get :serial r)))
    (or (not (natp inflight))
        (and pass (not (equal pass :dry-run)))
        (fn-opl-holdsp inflight serial pass inflight serial))))

(defthm fn-opub-capture-preserves-coherence
  (fn-opub-coherentp (mv-nth 1 (fn-opub-capture r count)))
  :hints (("Goal" :in-theory (e/d (fn-opub-coherentp fn-opl-holdsp)
                                  (fn-opub-get fn-opub-put)))))

(defthm fn-opub-due-preserves-coherence
  (implies (fn-opub-coherentp r)
           (fn-opub-coherentp (mv-nth 1 (fn-opub-due r profile count suffix budget space now))))
  :hints (("Goal" :in-theory (e/d (fn-opub-coherentp)
                                  (fn-opub-get fn-opub-put fn-opl-holdsp)))))

(defthm fn-opub-request-preserves-coherence
  (implies (fn-opub-coherentp r)
           (fn-opub-coherentp (mv-nth 1 (fn-opub-request r profile count budget space now))))
  :hints (("Goal" :in-theory (e/d (fn-opub-coherentp)
                                  (fn-opub-get fn-opub-put fn-opl-holdsp)))))

(defthm fn-opub-done-preserves-coherence
  (implies (fn-opub-coherentp r)
           (fn-opub-coherentp (mv-nth 1 (fn-opub-done r next payloads durablep verdict))))
  :hints (("Goal" :in-theory (e/d (fn-opub-coherentp fn-orc-release-slot fn-opl-holdsp)
                                  (fn-opub-get fn-opub-put)))))

(defthm fn-opub-abandoned-preserves-coherence
  (implies (fn-opub-coherentp r)
           (fn-opub-coherentp (mv-nth 1 (fn-opub-abandoned r count serial outcome now))))
  :hints (("Goal" :in-theory (e/d (fn-opub-coherentp fn-opl-settle fn-orc-release-slot fn-opl-holdsp)
                                  (fn-opub-get fn-opub-put)))))

(defthm fn-opub-install-establishes-coherence
  (fn-opub-coherentp (fn-opub-install r base))
  :hints (("Goal" :in-theory (enable fn-opub-coherentp))))

(defthm fn-opub-reclaim-install-establishes-coherence
  (fn-opub-coherentp (fn-opub-reclaim-install r base count))
  :hints (("Goal" :in-theory (enable fn-opub-coherentp))))

(in-theory (disable fn-opub-due fn-opub-request fn-opub-capture fn-opub-done
                    fn-opub-abandoned fn-opub-install fn-opub-reclaim-install))
