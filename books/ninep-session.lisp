; Concrete per-connection fid and outstanding-request custody.
; Capacity is installed profile storage, never a bound on stored data.
; Internal OWNED entries compose only with genuine source/allocator issuers.
(in-package "ACL2")
(include-book "ninep-refusal")

(defstobj fn-ninep-session
 (fn-9ps-phase :type t :initially :unversioned)
 (fn-9ps-msize :type (integer 0 *) :initially 0)
 (fn-9ps-mount-source :type t :initially nil)
 (fn-9ps-mount-token :type t :initially nil)
 (fn-9ps-fids :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-fid-phase :type (array t (1)) :initially :idle :resizable t)
 (fn-9ps-selection :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-fid-borrows :type (array (integer 0 *) (1)) :initially 0 :resizable t)
 (fn-9ps-tags :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-request-phase :type (array t (1)) :initially :idle :resizable t)
 (fn-9ps-request-receipt :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-request-fid-slot :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-request-borrow :type (array t (1)) :initially nil :resizable t)
 (fn-9ps-mount-phase :type t :initially :empty)
 (fn-9ps-mount-intent :type t :initially nil)
 (fn-9ps-drain-index :type (integer 0 *) :initially 0)
 (fn-9ps-pending-version :type t :initially nil)
 :inline t)

(defun fn-9ps-fid-slotp (slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (and (natp slot) (< slot (fn-9ps-fids-length fn-ninep-session))
      (< slot (fn-9ps-fid-phase-length fn-ninep-session))
      (< slot (fn-9ps-selection-length fn-ninep-session))
      (< slot (fn-9ps-fid-borrows-length fn-ninep-session))))

(defun fn-9ps-request-slotp (slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (and (natp slot) (< slot (fn-9ps-tags-length fn-ninep-session))
      (< slot (fn-9ps-request-phase-length fn-ninep-session))
      (< slot (fn-9ps-request-receipt-length fn-ninep-session))
      (< slot (fn-9ps-request-fid-slot-length fn-ninep-session))
      (< slot (fn-9ps-request-borrow-length fn-ninep-session))))

; This storage provisioner is INTERNAL and must be prepaid before entry.
; It cannot install a mount or change session readiness.
(defun fn-9ps-provision-internal (fids requests fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session
                 :guard (and (posp fids) (posp requests))))
 (if (not (and (eq (fn-9ps-phase fn-ninep-session) :unversioned)
               (eq (fn-9ps-mount-phase fn-ninep-session) :empty))) fn-ninep-session
 (let* ((fn-ninep-session (resize-fn-9ps-fids fids fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-fid-phase fids fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-selection fids fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-fid-borrows fids fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-tags requests fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-request-phase requests fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-request-receipt requests fn-ninep-session))
        (fn-ninep-session (resize-fn-9ps-request-fid-slot requests fn-ninep-session)))
  (resize-fn-9ps-request-borrow requests fn-ninep-session))))

; One lookup cell per scheduler action. Rflush releases protocol tag use,
; while the cancelled physical record remains in its separate retained slot.
; No whole table recognition/scan.
(defun fn-9ps-find-tag-step (tag slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (cond ((not (and (natp tag) (< tag 65535) (natp slot))) (mv :invalid nil slot))
       ((not (fn-9ps-request-slotp slot fn-ninep-session)) (mv :missing nil slot))
       ((and (eq (fn-9ps-request-phasei slot fn-ninep-session) :running)
             (equal tag (fn-9ps-tagsi slot fn-ninep-session))) (mv :found slot slot))
       (t (mv :yield nil (1+ slot)))))

(defun fn-9ps-find-fid-step (fid slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (cond ((not (and (natp fid) (< fid 4294967295) (natp slot))) (mv :invalid nil slot))
       ((not (fn-9ps-fid-slotp slot fn-ninep-session)) (mv :missing nil slot))
       ((and (member-eq (fn-9ps-fid-phasei slot fn-ninep-session) '(:walked :open))
             (equal fid (fn-9ps-fidsi slot fn-ninep-session))) (mv :found slot slot))
       (t (mv :yield nil (1+ slot)))))

; The wrapper must derive RECEIPT from its real issued operation, not wire
; input. The retained receipt is never made from a tag, fid, or tuple shape.
; Duplicate-tag search precedes this internal known-free-slot composition.
(defun fn-9ps-request-register-owned (slot tag receipt fid-slot borrow fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (if (not (and (fn-9ps-request-slotp slot fn-ninep-session)
               (natp tag) (< tag 65535) receipt
               (eq (fn-9ps-phase fn-ninep-session) :base)
               (eq (fn-9ps-request-phasei slot fn-ninep-session) :idle)
               (or (not borrow)
                   (and (fn-9ps-fid-slotp fid-slot fn-ninep-session)
                        (eq (fn-9ps-fid-phasei fid-slot fn-ninep-session) :open)
                        (natp (fn-9ps-fid-borrowsi fid-slot fn-ninep-session))))))
     (mv :unavailable fn-ninep-session)
  (let* ((fn-ninep-session
           (if borrow
               (update-fn-9ps-fid-borrowsi fid-slot
                 (1+ (fn-9ps-fid-borrowsi fid-slot fn-ninep-session)) fn-ninep-session)
             fn-ninep-session))
         (fn-ninep-session (update-fn-9ps-tagsi slot tag fn-ninep-session))
         (fn-ninep-session (update-fn-9ps-request-receipti slot receipt fn-ninep-session))
         (fn-ninep-session (update-fn-9ps-request-fid-sloti slot fid-slot fn-ninep-session))
         (fn-ninep-session (update-fn-9ps-request-borrowi slot borrow fn-ninep-session))
         (fn-ninep-session (update-fn-9ps-request-phasei slot :running fn-ninep-session)))
   (mv :retained fn-ninep-session))))

; Called after core's bounded tag lookup; absent oldtag uses NIL SLOT.
; Cancellation suppresses reply publication but changes no source ownership.
(defun fn-9ps-flush-at (tag oldtag slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (if (not (and (natp tag) (< tag 65535) (natp oldtag) (< oldtag 65535)))
     (mv '(:close :invalid-flush) fn-ninep-session)
  (let ((fn-ninep-session
         (if (and (fn-9ps-request-slotp slot fn-ninep-session)
                  (equal oldtag (fn-9ps-tagsi slot fn-ninep-session))
                  (member-eq (fn-9ps-request-phasei slot fn-ninep-session)
                             '(:running :cancelled)))
             (update-fn-9ps-request-phasei slot :cancelled fn-ninep-session)
           fn-ninep-session)))
   (mv (list :reply (append '(7 0 0 0 109) (fn-9p-u16-octets tag)))
       fn-ninep-session))))

; Definite producer return consumes precisely the retained operation receipt.
; A stale callback cannot clear a reused slot with a different issued receipt.
; No Boolean "completed" or NIL-alias inference authorizes this call.
(defun fn-9ps-request-return-owned (slot receipt fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (if (not (and (fn-9ps-request-slotp slot fn-ninep-session) receipt
               (equal receipt (fn-9ps-request-receipti slot fn-ninep-session))
               (member-eq (fn-9ps-request-phasei slot fn-ninep-session)
                          '(:running :cancelled))))
     (mv :stale fn-ninep-session)
  (let* ((borrow (fn-9ps-request-borrowi slot fn-ninep-session))
         (fid-slot (fn-9ps-request-fid-sloti slot fn-ninep-session)))
   (if (and borrow
            (not (and (fn-9ps-fid-slotp fid-slot fn-ninep-session)
                      (posp (fn-9ps-fid-borrowsi fid-slot fn-ninep-session)))))
       (mv :recovery-required fn-ninep-session)
    (let* ((word (if (eq (fn-9ps-request-phasei slot fn-ninep-session) :cancelled)
                     :discard :publish))
           (fn-ninep-session
             (if borrow
                 (update-fn-9ps-fid-borrowsi fid-slot
                   (1- (fn-9ps-fid-borrowsi fid-slot fn-ninep-session)) fn-ninep-session)
               fn-ninep-session))
           (fn-ninep-session (update-fn-9ps-request-borrowi slot nil fn-ninep-session))
           (fn-ninep-session (update-fn-9ps-request-phasei slot :idle fn-ninep-session)))
     (mv word fn-ninep-session))))))

(defun fn-9ps-clunk-at (fid slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (if (not (and (fn-9ps-fid-slotp slot fn-ninep-session)
               (natp fid) (equal fid (fn-9ps-fidsi slot fn-ninep-session))
               (not (eq (fn-9ps-fid-phasei slot fn-ninep-session) :idle))))
     (mv :unknown-fid fn-ninep-session)
  (let ((fn-ninep-session (update-fn-9ps-fid-phasei slot :clunking fn-ninep-session)))
   (mv :clunking fn-ninep-session))))

; Source selection can be dropped only after every actual borrow returned.
; Completion of this cell does not release the mount's independent pin.
(defun fn-9ps-fid-retire-step (slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (cond ((not (fn-9ps-fid-slotp slot fn-ninep-session)) (mv :unavailable fn-ninep-session))
       ((not (eq (fn-9ps-fid-phasei slot fn-ninep-session) :clunking))
        (mv :unavailable fn-ninep-session))
       ((not (equal (fn-9ps-fid-borrowsi slot fn-ninep-session) 0))
        (mv :await-return fn-ninep-session))
       (t (let* ((fn-ninep-session (update-fn-9ps-selectioni slot nil fn-ninep-session))
                 (fn-ninep-session (update-fn-9ps-fid-phasei slot :idle fn-ninep-session)))
            (mv :retired fn-ninep-session)))))

; Reset/disconnect cancels one request or marks one fid per tick. It retains
; the source and mount token until the actual mount-return producer joins.
(defun fn-9ps-drain-step (slot fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (let* ((fn-ninep-session (update-fn-9ps-phase :draining fn-ninep-session))
        (fn-ninep-session
          (if (and (fn-9ps-request-slotp slot fn-ninep-session)
                   (eq (fn-9ps-request-phasei slot fn-ninep-session) :running))
              (update-fn-9ps-request-phasei slot :cancelled fn-ninep-session)
            fn-ninep-session))
        (fn-ninep-session
          (if (and (fn-9ps-fid-slotp slot fn-ninep-session)
                   (not (eq (fn-9ps-fid-phasei slot fn-ninep-session) :idle)))
              (update-fn-9ps-fid-phasei slot :clunking fn-ninep-session)
            fn-ninep-session)))
  (mv :draining fn-ninep-session)))


(defun fn-9ps-version-at (server-msize cursor fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-octets fn-ninep-session) :guard t))
 (let ((answer (fn-9p-version-at server-msize cursor fn-octets)))
  (cond ((not (eq (car answer) :version)) (mv answer fn-ninep-session))
        ; Version kills all old fids/requests. The caller first runs the
        ; bounded drain; it cannot replace a retained mount while aliases run.
        ((not (eq (fn-9ps-phase fn-ninep-session) :unversioned))
         (let* ((fn-ninep-session (update-fn-9ps-pending-version answer fn-ninep-session))
                (fn-ninep-session (update-fn-9ps-phase :draining fn-ninep-session))
                (fn-ninep-session (update-fn-9ps-drain-index 0 fn-ninep-session)))
          (mv '(:drain-required) fn-ninep-session)))
        (t (let* ((fn-ninep-session (update-fn-9ps-msize (nfix (cadr answer)) fn-ninep-session))
                   (fn-ninep-session (update-fn-9ps-phase
                     (if (eq (caddr answer) :base) :base :unknown) fn-ninep-session)))
             (mv answer fn-ninep-session))))))

; SELECTED is the actual ACL2 provider result and remains internal. No host
; path string, publication tuple, qid or backing pointer installs a fid.
(defun fn-9ps-fid-bind-owned (slot fid selected fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (if (not (and (fn-9ps-fid-slotp slot fn-ninep-session)
               (natp fid) (< fid 4294967295) selected
               (eq (fn-9ps-phase fn-ninep-session) :base)
               (eq (fn-9ps-mount-phase fn-ninep-session) :held)
               (fn-9ps-mount-source fn-ninep-session) (fn-9ps-mount-token fn-ninep-session)
               (eq (fn-9ps-fid-phasei slot fn-ninep-session) :idle)
               (equal (fn-9ps-fid-borrowsi slot fn-ninep-session) 0)))
     (mv :unavailable fn-ninep-session)
   (let* ((fn-ninep-session (update-fn-9ps-fidsi slot fid fn-ninep-session))
          (fn-ninep-session (update-fn-9ps-selectioni slot selected fn-ninep-session))
          (fn-ninep-session (update-fn-9ps-fid-phasei slot :walked fn-ninep-session)))
     (mv :bound fn-ninep-session))))

(defun fn-9ps-open-at (fid slot mode fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (cond ((not (and (fn-9ps-fid-slotp slot fn-ninep-session)
                  (natp fid) (equal fid (fn-9ps-fidsi slot fn-ninep-session))
                  (eq (fn-9ps-phase fn-ninep-session) :base)
                  (eq (fn-9ps-fid-phasei slot fn-ninep-session) :walked)))
        (mv :unknown-fid fn-ninep-session))
       ; OTRUNC/ORCLOSE and write modes all refuse; no mutation fallback.
       ((not (equal mode 0)) (mv :read-only fn-ninep-session))
       (t (let ((fn-ninep-session (update-fn-9ps-fid-phasei slot :open fn-ninep-session)))
            (mv :opened fn-ninep-session)))))

; Only a fully successful Twalk changes newfid. The composed provider
; accumulates at most MAXWELEM16 qids, but walks may span arbitrarily many
; separate requests. Partial reply leaves both fid cells untouched.
(defun fn-9ps-walk-finish-owned (old-slot new-slot new-fid wanted reached selected fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (cond ((not (and (fn-9ps-fid-slotp old-slot fn-ninep-session)
                  (fn-9ps-fid-slotp new-slot fn-ninep-session)
                  (eq (fn-9ps-fid-phasei old-slot fn-ninep-session) :walked)
                  (natp new-fid) (< new-fid 4294967295)
                  (natp wanted) (<= wanted 16) (natp reached) (<= reached wanted)
                  (or (and (equal old-slot new-slot)
                           (equal new-fid (fn-9ps-fidsi old-slot fn-ninep-session)))
                      (and (not (equal old-slot new-slot)) (eq (fn-9ps-fid-phasei new-slot fn-ninep-session) :idle)))))
        (mv :invalid-walk fn-ninep-session))
       ((and (< reached wanted) (zp reached)) (mv :not-found fn-ninep-session))
       ((< reached wanted) (mv :partial-walk fn-ninep-session))
       ((not selected) (mv :unavailable fn-ninep-session))
       (t (let* ((fn-ninep-session (update-fn-9ps-fidsi new-slot new-fid fn-ninep-session))
                  (fn-ninep-session (update-fn-9ps-selectioni new-slot selected fn-ninep-session))
                  (fn-ninep-session (update-fn-9ps-fid-phasei new-slot :walked fn-ninep-session)))
            (mv :walked fn-ninep-session)))))

(defthm fn-9ps-partial-walk-never-installs-fid
 (implies (equal (mv-nth 0 (fn-9ps-walk-finish-owned old new fid wanted reached selected fn-ninep-session)) :partial-walk)
  (equal (mv-nth 1 (fn-9ps-walk-finish-owned old new fid wanted reached selected fn-ninep-session)) fn-ninep-session)))

(defthm fn-9ps-mutation-open-is-refused-without-effect
 (implies (and (fn-9ps-fid-slotp slot fn-ninep-session)
               (natp fid) (equal fid (fn-9ps-fidsi slot fn-ninep-session))
               (eq (fn-9ps-phase fn-ninep-session) :base)
               (eq (fn-9ps-fid-phasei slot fn-ninep-session) :walked)
               (not (equal mode 0)))
  (equal (fn-9ps-open-at fid slot mode fn-ninep-session) (mv :read-only fn-ninep-session))))


(defun fn-9ps-drain-begin (fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (let* ((fn-ninep-session (update-fn-9ps-phase :draining-requests fn-ninep-session))
        (fn-ninep-session (update-fn-9ps-drain-index 0 fn-ninep-session)))
  fn-ninep-session))

; No new request/fid may be admitted once draining starts. One actual cell
; is checked/retired each call. :mount-return-ready is produced here, never
; supplied as a completion Boolean by the socket worker.
(defun fn-9ps-quiesce-step (fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (let ((slot (fn-9ps-drain-index fn-ninep-session)))
  (cond
   ((eq (fn-9ps-phase fn-ninep-session) :draining-requests)
    (cond ((fn-9ps-request-slotp slot fn-ninep-session)
           (if (eq (fn-9ps-request-phasei slot fn-ninep-session) :idle)
               (let ((fn-ninep-session (update-fn-9ps-drain-index (1+ slot) fn-ninep-session)))
                (mv :yield fn-ninep-session))
             (let ((fn-ninep-session (update-fn-9ps-request-phasei slot :cancelled fn-ninep-session)))
              (mv :await-return fn-ninep-session))))
          (t (let* ((fn-ninep-session (update-fn-9ps-phase :draining-fids fn-ninep-session))
                    (fn-ninep-session (update-fn-9ps-drain-index 0 fn-ninep-session)))
               (mv :yield fn-ninep-session)))))
   ((eq (fn-9ps-phase fn-ninep-session) :draining-fids)
    (cond ((fn-9ps-fid-slotp slot fn-ninep-session)
           (if (not (equal (fn-9ps-fid-borrowsi slot fn-ninep-session) 0))
               (mv :await-return fn-ninep-session)
             (let* ((fn-ninep-session (update-fn-9ps-selectioni slot nil fn-ninep-session))
                    (fn-ninep-session (update-fn-9ps-fid-phasei slot :idle fn-ninep-session))
                    (fn-ninep-session (update-fn-9ps-drain-index (1+ slot) fn-ninep-session)))
              (mv :yield fn-ninep-session))))
          (t (let ((fn-ninep-session (update-fn-9ps-phase :mount-return-ready fn-ninep-session)))
               (mv :mount-return-ready fn-ninep-session)))))
   ((eq (fn-9ps-phase fn-ninep-session) :mount-return-ready)
    (mv :mount-return-ready fn-ninep-session))
   (t (mv :unavailable fn-ninep-session)))))

(defthm fn-9ps-flush-preserves-mount-and-borrow-authority
 (let ((next (mv-nth 1 (fn-9ps-flush-at tag oldtag slot fn-ninep-session))))
  (and (equal (fn-9ps-mount-source next) (fn-9ps-mount-source fn-ninep-session))
       (equal (fn-9ps-mount-token next) (fn-9ps-mount-token fn-ninep-session))
       (equal (nth 7 next) (nth 7 fn-ninep-session))
       (equal (nth 10 next) (nth 10 fn-ninep-session))
       (equal (nth 12 next) (nth 12 fn-ninep-session)))))

(defthm fn-9ps-stale-request-return-changes-nothing
 (implies (or (not (fn-9ps-request-slotp slot fn-ninep-session))
              (not receipt)
              (not (equal receipt (fn-9ps-request-receipti slot fn-ninep-session)))
              (not (member-eq (fn-9ps-request-phasei slot fn-ninep-session)
                              '(:running :cancelled))))
  (equal (fn-9ps-request-return-owned slot receipt fn-ninep-session)
         (mv :stale fn-ninep-session))))

(defthm fn-9ps-fid-with-borrow-cannot-retire
 (implies (and (fn-9ps-fid-slotp slot fn-ninep-session)
               (eq (fn-9ps-fid-phasei slot fn-ninep-session) :clunking)
               (not (equal (fn-9ps-fid-borrowsi slot fn-ninep-session) 0)))
  (equal (fn-9ps-fid-retire-step slot fn-ninep-session)
         (mv :await-return fn-ninep-session))))

(defthm fn-9ps-drain-retains-mount-source-and-token
 (let ((next (mv-nth 1 (fn-9ps-drain-step slot fn-ninep-session))))
  (and (equal (fn-9ps-mount-source next) (fn-9ps-mount-source fn-ninep-session))
       (equal (fn-9ps-mount-token next) (fn-9ps-mount-token fn-ninep-session)))))

(defthm fn-9ps-successful-request-return-is-once-only
 (implies (and (fn-ninep-sessionp fn-ninep-session)
               (member-eq (mv-nth 0 (fn-9ps-request-return-owned slot receipt fn-ninep-session))
                          '(:publish :discard)))
  (let ((next (mv-nth 1 (fn-9ps-request-return-owned slot receipt fn-ninep-session))))
   (equal (fn-9ps-request-return-owned slot receipt next) (mv :stale next))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-ninep-sessionp))))
