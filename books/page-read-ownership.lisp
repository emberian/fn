; fn: ownership of one issued cold extent read (PRF-1057).
; The host stores these rows under the extent mutex. Cancellation revokes
; publication, not worker ownership. Only actual I/O completion settles.
; A row's immutable token names request incarnation and full extent identity.
(in-package "ACL2")

; R = (ID CID FILE EOFF ELEN TRAILER PHASE). ID is process-monotonic,
; never a descriptor number or a reusable connection slot.
(defun fn-pio-rowp (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 7)
       (natp (nth 0 r)) (natp (nth 1 r)) (natp (nth 2 r))
       (natp (nth 3 r)) (natp (nth 4 r)) (natp (nth 5 r))
       (member-eq (nth 6 r) '(:issued :cancelled :settled)) t))

(defun fn-pio-token (r)
  (declare (xargs :guard (true-listp r)))
  (list (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r) (nth 5 r)))

(defun fn-pio-issue (next cid file eoff elen trailer)
  (declare (xargs :guard (and (natp next) (natp cid) (natp file)
                              (natp eoff) (natp elen) (natp trailer))))
  (mv (+ 1 next) (list next cid file eoff elen trailer :issued)))

(defun fn-pio-cancel (r token)
  (declare (xargs :guard t))
  (if (and (fn-pio-rowp r) (equal token (fn-pio-token r))
           (eq (nth 6 r) :issued))
      (append (fn-pio-token r) (list :cancelled))
    r))

; VERDICT is the observed I/O result plus ACL2's commitment verdict:
; :ok only after the complete read passes fn-arx-entry-verdict-buffer;
; :read, :trailer, :digest or :error are named faults. No bytes are made here.
; A duplicate or stale completion neither settles nor publishes again.
(defun fn-pio-complete (r token verdict)
  (declare (xargs :guard t))
  (if (and (fn-pio-rowp r) (equal token (fn-pio-token r))
           (not (eq (nth 6 r) :settled)))
      (mv (append (fn-pio-token r) (list :settled))
          (cond ((not (eq verdict :ok)) (list :fault verdict))
                ((eq (nth 6 r) :cancelled) :cancelled)
                (t :publish)))
    (mv r :stale)))

(defun fn-pio-file-clear-p (file rows)
  (declare (xargs :guard t))
  (if (atom rows)
      t
    (and (not (and (fn-pio-rowp (car rows))
                   (equal (nth 2 (car rows)) file)
                   (not (eq (nth 6 (car rows)) :settled))))
         (fn-pio-file-clear-p file (cdr rows)))))

(defthm fn-pio-issue-establishes-row
  (implies (and (natp next) (natp cid) (natp file)
                (natp eoff) (natp elen) (natp trailer))
           (and (fn-pio-rowp (mv-nth 1 (fn-pio-issue next cid file eoff elen trailer)))
                (equal (nth 0 (mv-nth 1 (fn-pio-issue next cid file eoff elen trailer))) next)
                (< next (mv-nth 0 (fn-pio-issue next cid file eoff elen trailer))))))

(defthm fn-pio-cancel-preserves-row
  (implies (fn-pio-rowp r) (fn-pio-rowp (fn-pio-cancel r token))))

(defthm fn-pio-complete-preserves-row
  (implies (fn-pio-rowp r) (fn-pio-rowp (mv-nth 0 (fn-pio-complete r token verdict)))))

; Completion's literal publication criterion: positive advancement, exact
; token, still live request, verified commitment, and ownership settled once.
(defthm fn-pio-completion-publishes-only-the-issued-identity
  (implies (equal (mv-nth 1 (fn-pio-complete r token verdict)) :publish)
           (and (fn-pio-rowp r) (equal token (fn-pio-token r))
                (eq (nth 6 r) :issued) (eq verdict :ok)
                (equal (fn-pio-token (mv-nth 0 (fn-pio-complete r token verdict))) token)
                (eq (nth 6 (mv-nth 0 (fn-pio-complete r token verdict))) :settled)))
  :rule-classes nil)

(defthm fn-pio-matching-success-advances
  (implies (and (fn-pio-rowp r) (equal token (fn-pio-token r))
                (eq (nth 6 r) :issued) (eq verdict :ok))
           (and (equal (mv-nth 1 (fn-pio-complete r token verdict)) :publish)
                (eq (nth 6 (mv-nth 0 (fn-pio-complete r token verdict))) :settled))))

(defthm fn-pio-cancellation-retains-worker-ownership
  (implies (not (eq (nth 6 r) :settled))
           (and (equal (fn-pio-token (fn-pio-cancel r token)) (fn-pio-token r))
                (not (eq (nth 6 (fn-pio-cancel r token)) :settled)))))

(defthm fn-pio-stale-completion-does-nothing
  (implies (or (not (fn-pio-rowp r)) (not (equal token (fn-pio-token r)))
               (eq (nth 6 r) :settled))
           (and (equal (mv-nth 0 (fn-pio-complete r token verdict)) r)
                (equal (mv-nth 1 (fn-pio-complete r token verdict)) :stale))))

(defthm fn-pio-close-waits-for-every-worker
  (implies (and (member-equal r rows) (fn-pio-rowp r)
                (equal (nth 2 r) file) (not (eq (nth 6 r) :settled)))
           (not (fn-pio-file-clear-p file rows))))

; A reaper quantum inspects one owned worker, not the whole pool. These
; are work limits/OS-observation decisions, never ceilings on stored data.
(defun fn-pio-reap-work ()
  (declare (xargs :guard t))
  1)

(defun fn-pio-worker-death-step (deadp)
  (declare (xargs :guard (booleanp deadp)))
  (if deadp :settle :rotate))

(in-theory (disable fn-pio-rowp fn-pio-token fn-pio-complete fn-pio-cancel
                    fn-pio-file-clear-p fn-pio-issue))
