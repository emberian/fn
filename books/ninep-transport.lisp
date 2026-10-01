; Core-owned resumable connection framing. Transport moves the ranges and
; octets selected here; it neither decodes fields nor constructs replies.
; INTERNAL: callers need the installed phase allowance before constructors.
(in-package "ACL2")
(include-book "ninep-dispatch")

; Fixed7: tag, phase, supported message limit, header, fields, dispatch, reply.
; The received buffer remains borrowed through reply completion and provider
; work. No in-flight borrowed span is cleared at a socket timeout or Flush.
(defun fn-9pt-begin (limit)
 (declare (xargs :guard t))
 (list :ninep-transport :header limit nil nil nil nil))

; Official connection cursor. Native callers cannot inject a parsed header,
; rewrite the retained reply, or replay a saved cursor to clear a new frame.
(defstobj fn-ninep-transport
 (fn-9pt-owned-cursor :type t :initially nil)
 (fn-9pt-input-quantum :type (integer 0 *) :initially 0)
 :inline t)

(defun fn-9pt-provision-internal (limit quantum fn-ninep-transport)
 (declare (xargs :stobjs fn-ninep-transport :guard t))
 (if (not (and (fn-9p-profile-msizep limit) (posp quantum)
               (not (fn-9pt-owned-cursor fn-ninep-transport))))
     (mv :unavailable fn-ninep-transport)
   (let* ((fn-ninep-transport
           (update-fn-9pt-owned-cursor (fn-9pt-begin limit) fn-ninep-transport))
         (fn-ninep-transport (update-fn-9pt-input-quantum quantum fn-ninep-transport)))
    (mv :provisioned fn-ninep-transport))))

(defun fn-9pt-reply-octets (answer)
 (declare (xargs :guard t))
 (case (fn-9p-metadata-at 0 answer)
  (:version (fn-9p-metadata-at 3 answer))
  (:refused (fn-9p-metadata-at 2 answer))
  (:reply (fn-9p-metadata-at 1 answer))
  (otherwise nil)))

; No mounted generation is settled here. The absent/returned cases contain
; no retained generation alias; a held mount must go through actual return.
(defun fn-9pt-version-after-quiescence (fn-ninep-session)
 (declare (xargs :stobjs fn-ninep-session :guard t))
 (let ((answer (fn-9ps-pending-version fn-ninep-session)))
  (if (not (and (eq (fn-9ps-phase fn-ninep-session) :mount-return-ready)
                (member-eq (fn-9ps-mount-phase fn-ninep-session) '(:empty :returned))
                (not (fn-9ps-mount-token fn-ninep-session))
                (not (fn-9ps-mount-source fn-ninep-session))
                (eq (fn-9p-metadata-at 0 answer) :version)
                (fn-9p-profile-msizep (fn-9p-metadata-at 1 answer))))
      (mv :await-mount-return nil fn-ninep-session)
    (let* ((fn-ninep-session
             (update-fn-9ps-msize (fn-9p-metadata-at 1 answer) fn-ninep-session))
           (fn-ninep-session
             (update-fn-9ps-phase
               (if (eq (fn-9p-metadata-at 2 answer) :base) :base :unknown)
               fn-ninep-session))
           (fn-ninep-session (update-fn-9ps-pending-version nil fn-ninep-session))
           (fn-ninep-session (update-fn-9ps-mount-phase :empty fn-ninep-session))
           (fn-ninep-session (update-fn-9ps-mount-intent nil fn-ninep-session)))
     (mv :version answer fn-ninep-session)))))

(defun fn-9pt-step (cursor fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-octets fn-ninep-session) :guard t :verify-guards nil))
 (let* ((phase (fn-9p-metadata-at 1 cursor))
        (limit (fn-9p-metadata-at 2 cursor))
        (header (fn-9p-metadata-at 3 cursor))
        (fields (fn-9p-metadata-at 4 cursor))
        (dispatch (fn-9p-metadata-at 5 cursor))
        (answer (fn-9p-metadata-at 6 cursor))
        (msize (if (eq (fn-9ps-phase fn-ninep-session) :unversioned)
                   limit (fn-9ps-msize fn-ninep-session))))
  (cond
   ((not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-transport)
              (fn-9p-profile-msizep limit)))
    (mv '(:close :invalid-transport) cursor fn-ninep-session))
   ((eq phase :header)
    (let ((next (fn-9p-header-at 0 (fn-octets-len fn-octets) msize fn-octets)))
     (cond ((eq (fn-9p-metadata-at 0 next) :need-header)
            (mv (list :receive (fn-9p-metadata-at 1 next)) cursor fn-ninep-session))
           ((eq (fn-9p-metadata-at 0 next) :header)
            (mv '(:yield) (list :ninep-transport :body limit next nil nil nil)
                fn-ninep-session))
           (t (mv (list :close next) cursor fn-ninep-session)))))
   ((eq phase :body)
    (let ((action (fn-9p-body-action header (fn-octets-len fn-octets))))
     (cond ((eq (fn-9p-metadata-at 0 action) :need-body)
            (mv (list :receive (fn-9p-metadata-at 1 action)) cursor fn-ninep-session))
           ((and (eq (fn-9p-metadata-at 0 action) :frame)
                 (equal (fn-9p-metadata-at 5 header) (fn-octets-len fn-octets)))
            (mv '(:yield)
                (list :ninep-transport :parse limit header
                      (fn-9p-fields-start header) nil nil) fn-ninep-session))
           (t (mv '(:close :invalid-frame-range) cursor fn-ninep-session)))))
   ((eq phase :parse)
    (if (not (and (fn-9p-fields-ready-p fields)
                  (<= (nth 4 fields) (fn-octets-len fn-octets))))
        (mv '(:close :invalid-parser-carry) cursor fn-ninep-session)
      (mv-let (word next) (fn-9p-fields-step fields fn-octets)
       (cond ((eq word :yield)
              (mv '(:yield) (list :ninep-transport :parse limit header next nil nil)
                  fn-ninep-session))
             ((member-eq word '(:parsed :readonly))
              (mv '(:yield)
                  (list :ninep-transport :dispatch limit header next
                        (fn-9p-dispatch-begin next) nil) fn-ninep-session))
             (t (mv (list :close word) cursor fn-ninep-session))))))
   ((eq phase :dispatch)
    (mv-let (reply next fn-ninep-session)
     (fn-9p-dispatch-step limit dispatch fn-octets fn-ninep-session)
     (case (fn-9p-metadata-at 0 reply)
      (:yield (mv reply (list :ninep-transport :dispatch limit header fields next nil)
                  fn-ninep-session))
      (:drain-required
       (let ((fn-ninep-session (fn-9ps-drain-begin fn-ninep-session)))
        (mv '(:yield) (list :ninep-transport :drain limit header fields next nil)
            fn-ninep-session)))
      (:mount-acquire
       (mv (list :provider reply fields)
           (list :ninep-transport :provider limit header fields next nil) fn-ninep-session))
      (:close (mv reply cursor fn-ninep-session))
      (otherwise
       (if (consp (fn-9pt-reply-octets reply))
           (mv '(:yield) (list :ninep-transport :reply limit header fields next reply)
               fn-ninep-session)
         (mv '(:close :invalid-core-reply) cursor fn-ninep-session))))))
   ((eq phase :drain)
    (mv-let (word fn-ninep-session) (fn-9ps-quiesce-step fn-ninep-session)
     (if (not (eq word :mount-return-ready))
         (mv (list word) cursor fn-ninep-session)
       (mv-let (finished reply fn-ninep-session)
        (fn-9pt-version-after-quiescence fn-ninep-session)
        (if (eq finished :version)
            (mv '(:yield) (list :ninep-transport :reply limit header fields dispatch reply)
                fn-ninep-session)
          (mv (list finished) cursor fn-ninep-session))))))
   ((eq phase :provider) (mv (list :provider fields) cursor fn-ninep-session))
   ((eq phase :reply)
    (if (consp (fn-9pt-reply-octets answer))
        (mv (list :send (fn-9pt-reply-octets answer)) cursor fn-ninep-session)
      (mv '(:close :invalid-core-reply) cursor fn-ninep-session)))
   (t (mv '(:close :invalid-phase) cursor fn-ninep-session)))))

(local
 (defthm fn-9pt-parser-end-natural
  (implies (fn-9p-fields-ready-p fields) (natp (nth 4 fields)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-9p-fields-ready-p)
                                  (fn-wildmat-at-mostp))))))
(verify-guards fn-9pt-step
 :hints (("Goal" :in-theory
  (disable fn-9p-header-at fn-9p-body-action fn-9p-fields-start
           fn-9p-fields-step fn-9p-dispatch-begin fn-9p-dispatch-step
           fn-9pt-reply-octets fn-9ps-drain-begin fn-9ps-quiesce-step
           fn-9pt-version-after-quiescence fn-9p-profile-msizep))))

; Called only AFTER all response bytes have actually returned from I/O and
; local response/input aliases are relinquished. Failed/partial sends do not
; call this epilogue. No supplied Boolean licenses a mount/query release.
(defun fn-9pt-reply-returned (cursor fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-octets fn-ninep-session) :guard t))
 (if (not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-transport)
               (eq (fn-9p-metadata-at 1 cursor) :reply)))
     (mv :stale cursor fn-octets fn-ninep-session)
   (let ((fn-octets (fn-octets-clear fn-octets)))
    (mv :returned (fn-9pt-begin (fn-9p-metadata-at 2 cursor)) fn-octets fn-ninep-session))))

(local
 (defthm fn-9pt-clunk-mount-frame
  (let ((next (mv-nth 1 (fn-9ps-clunk-at fid slot session))))
   (and (equal (nth 2 next) (nth 2 session))
        (equal (nth 3 next) (nth 3 session))))
  :hints (("Goal" :in-theory (e/d (fn-9ps-clunk-at) (nth update-nth))))))
(local
 (defthm fn-9pt-flush-mount-frame
  (let ((next (mv-nth 1 (fn-9ps-flush-at tag oldtag slot session))))
   (and (equal (nth 2 next) (nth 2 session))
        (equal (nth 3 next) (nth 3 session))))
  :hints (("Goal" :in-theory (e/d (fn-9ps-flush-at) (nth update-nth))))))

(defthm fn-9pt-step-retains-mount-custody
 (implies (fn-ninep-sessionp fn-ninep-session)
 (let ((next (mv-nth 2 (fn-9pt-step cursor fn-octets fn-ninep-session))))
  (and (equal (fn-9ps-mount-token next) (fn-9ps-mount-token fn-ninep-session))
       (equal (fn-9ps-mount-source next) (fn-9ps-mount-source fn-ninep-session)))))
 :hints (("Goal" :in-theory
  (e/d (fn-9pt-step fn-9pt-version-after-quiescence fn-9p-dispatch-step
         fn-9ps-version-at fn-9ps-quiesce-step fn-9ps-drain-begin)
       (fn-9p-fields-step fn-9p-header-at fn-9p-body-action fn-9p-version-at
        fn-9ps-flush-at fn-9ps-clunk-at nth update-nth)))))

(defthm fn-9pt-stale-reply-return-complete-effect
 (implies (not (and (eq (fn-9p-metadata-at 0 cursor) :ninep-transport)
                    (eq (fn-9p-metadata-at 1 cursor) :reply)))
  (equal (fn-9pt-reply-returned cursor fn-octets fn-ninep-session)
         (list :stale cursor fn-octets fn-ninep-session))))

(defthm fn-9pt-held-mount-blocks-version-return
 (implies (or (fn-9ps-mount-token fn-ninep-session)
              (fn-9ps-mount-source fn-ninep-session))
  (equal (fn-9pt-version-after-quiescence fn-ninep-session)
         (list :await-mount-return nil fn-ninep-session))))

(defun fn-9pt-bounded-wire-action (action quantum)
 (declare (xargs :guard t))
 (if (not (eq (fn-9p-metadata-at 0 action) :receive)) action
  (let ((count (fn-9p-metadata-at 1 action)))
   (if (and (posp count) (posp quantum)) (list :receive (min count quantum))
    '(:close :invalid-receive-bound)))))

(defun fn-9pt-current-step (fn-ninep-transport fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-ninep-transport fn-octets fn-ninep-session) :guard t))
 (mv-let (action next fn-ninep-session)
  (fn-9pt-step (fn-9pt-owned-cursor fn-ninep-transport) fn-octets fn-ninep-session)
  (let ((fn-ninep-transport (update-fn-9pt-owned-cursor next fn-ninep-transport)))
   (mv (fn-9pt-bounded-wire-action action (fn-9pt-input-quantum fn-ninep-transport))
       fn-ninep-transport fn-ninep-session))))

(defun fn-9pt-current-reply-returned (fn-ninep-transport fn-octets fn-ninep-session)
 (declare (xargs :stobjs (fn-ninep-transport fn-octets fn-ninep-session) :guard t))
 (mv-let (word next fn-octets fn-ninep-session)
  (fn-9pt-reply-returned (fn-9pt-owned-cursor fn-ninep-transport) fn-octets fn-ninep-session)
  (let ((fn-ninep-transport (update-fn-9pt-owned-cursor next fn-ninep-transport)))
   (mv word fn-ninep-transport fn-octets fn-ninep-session))))

(defthm fn-9pt-current-step-complete-correspondence
 (let ((result (fn-9pt-step (fn-9pt-owned-cursor fn-ninep-transport) fn-octets fn-ninep-session)))
  (equal (fn-9pt-current-step fn-ninep-transport fn-octets fn-ninep-session)
         (list (fn-9pt-bounded-wire-action (mv-nth 0 result)
                 (fn-9pt-input-quantum fn-ninep-transport))
               (update-fn-9pt-owned-cursor (mv-nth 1 result) fn-ninep-transport)
               (mv-nth 2 result))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-9pt-current-step) (fn-9pt-step)))))

(defthm fn-9pt-receive-never-exceeds-installed-quantum
 (implies (eq (car (fn-9pt-bounded-wire-action action quantum)) :receive)
  (and (posp (cadr (fn-9pt-bounded-wire-action action quantum)))
       (<= (cadr (fn-9pt-bounded-wire-action action quantum)) quantum)
       (<= (cadr (fn-9pt-bounded-wire-action action quantum))
           (fn-9p-metadata-at 1 action)))))
