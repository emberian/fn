; Teeth for books/store-log-durable (lane m1-durable, 2026-10-04): the
; keystone fn-lgu-acknowledged-records-are-recovered-at-every-cut, its open
; corollary, the count the host holds and the COMPLETE's acknowledgements,
; on a ground log: two records recovered at the open, a third taken, sealed
; (the segment extended first), fenced and acknowledged; every cut under
; explicit crash choices; then one witness per removed hypothesis, and the
; witnesses for the run's two rules: the host fences only a batch in flight,
; and takes only a record its verdict admits.
;
; Crash images are fn-bs-crash under explicit choices with
; fn-bs-crash-choicesp asserted (fn-bs-crash-imagep is a defun-sk and is
; not executable: fn-bs-crash-imagep-suff makes each one an image).
(in-package "ACL2")
(include-book "../../books/store-log-durable")
(include-book "../../books/frame-trailer")
; The record codec seam's attachment: the recovered kernel's next txid reads
; the records through fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

(defun lgut-unit () (declare (xargs :guard t)) 4)
(defun lgut-max () (declare (xargs :guard t)) 4096)
(defun lgut-genesis () (declare (xargs :guard t :verify-guards nil)) *fn-lg-genesis*)
(defun lgut-r (i) (declare (xargs :guard t)) (list i (+ 1 (nfix i)) 7))
; A record large enough that its append needs the segment extended.
(defun lgut-big () (declare (xargs :guard t)) (make-list 700 :initial-element 5))
; A record the log cannot frame at MAX: its 32-octet chain and its octets
; exceed the bound (fn-lg-recordp fails).
(defun lgut-oversize () (declare (xargs :guard t)) (make-list 4070 :initial-element 6))
(defun lgut-store (content pending)
  (declare (xargs :guard t))
  (fn-bs-make (lgut-unit) (list (cons 0 content)) nil pending 1))
(defun lgut-sels (count sel)
  (declare (xargs :guard t :verify-guards nil))
  (if (zp count) nil (cons sel (lgut-sels (1- count) sel))))
; What the next open recovers from a crash image.
(defun lgut-open (image)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image 0)
                                    (lgut-genesis) (lgut-unit) (lgut-max) 0)))
; The keystone's conclusion at PAIR for the image the choices leave, with
; the choices admissible.
(defun lgut-holds-p (pair choices)
  (declare (xargs :guard t :verify-guards nil))
  (let ((a (fn-lgk-acked (cdr pair)))
        (recovered (lgut-open (fn-bs-crash (car pair) choices))))
    (and (fn-bs-crash-choicesp choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
         (<= a (len recovered))
         (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))

; The segment a crash left: two records logged, a torn unit, zeros.
(defun lgut-content ()
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lg-log (list (lgut-r 1) (lgut-r 2)) (lgut-genesis) (lgut-unit))
          '(9 9 9 9 0 0 0 0 0 0 0 0)
          (fn-bs-zeros 512)))
(defun lgut-bs-raw () (declare (xargs :guard t :verify-guards nil)) (lgut-store (lgut-content) nil))
(defun lgut-ks0 ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-recovered-kernel (lgut-bs-raw) 0 (lgut-genesis) (lgut-max) 0))
(defun lgut-recover-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-run (lgut-bs-raw) (lgut-ks0) (fn-lg-recover-program) nil 0))
(defun lgut-opened () (declare (xargs :guard t :verify-guards nil)) (car (last (lgut-recover-run))))

; The served run: the third record taken at the kernel's next txid, the
; seal (extension and write :ok), the barrier :ok, one acknowledgement.
(defun lgut-take (record)
  (declare (xargs :guard t :verify-guards nil))
  (list :take record (fn-lgk-next-txid (cdr (lgut-opened))) 0 0 64 1048576 (lgut-unit)))
(defun lgut-ops (record)
  (declare (xargs :guard t :verify-guards nil))
  (list (lgut-take record) (list :seal :ok :ok :ok) (list :fence :ok) (list :finish-one)))
(defun lgut-run (record)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgu-host-run (car (lgut-opened)) (cdr (lgut-opened)) (lgut-ops record) 0 (lgut-max)))
(defun lgut-pending-units (pair)
  (declare (xargs :guard t :verify-guards nil))
  (floor (len (nth 3 (car (fn-bs-pending (car pair))))) (lgut-unit)))

; -----------------------------------------------------------------------------
; Reachable: the opened state is related; the run's cuts are the start, the
; take, the extension's two cuts, log-written, log-fenced and the
; acknowledgement; at the end three records are acknowledged.
(assert-event
 (let ((run (lgut-run (lgut-big))))
   (and (fn-lgk-relp (car (lgut-opened)) (cdr (lgut-opened)) 0 (lgut-genesis) (lgut-max))
        (equal (fn-lgu-take-verdict (lgut-big) (lgut-max)) :admissible)
        (equal (len (lgut-recover-run)) 4)
        (equal (len run) 11)
        (consp (fn-bs-pending (car (nth 3 run))))              ; log-extended
        (null (fn-bs-pending (car (nth 4 run))))               ; log-extent-fenced
        (consp (fn-bs-pending (car (nth 5 run))))              ; log-written
        (equal (fn-lgk-phase (cdr (nth 5 run))) :appended)
        (null (fn-bs-pending (car (nth 7 run))))               ; log-fenced
        (equal (fn-lgk-acked (cdr (nth 1 run))) 2)
        (equal (fn-lgk-acked (cdr (car (last run)))) 3)
        (equal (fn-lgk-committed (cdr (car (last run))))
               (list (lgut-r 1) (lgut-r 2) (lgut-big))))))

; The keystone at every cut, under explicit choices: log-extended's zeros
; landed whole, not at all, torn; log-written's batch landed whole, not at
; all, its first unit, with a hole; the rest nothing pending.  At the last
; cut the conclusion names three records.
(assert-event
 (let ((run (lgut-run (lgut-big))))
   (and (lgut-holds-p (nth 0 run) nil)
        (lgut-holds-p (nth 2 run) nil)
        (lgut-holds-p (nth 3 run) (list (lgut-sels (lgut-pending-units (nth 3 run)) :new)))
        (lgut-holds-p (nth 3 run) (list nil))
        (lgut-holds-p (nth 3 run) (list (list :new :old :zero)))
        (lgut-holds-p (nth 4 run) nil)
        (lgut-holds-p (nth 5 run) (list (lgut-sels (lgut-pending-units (nth 5 run)) :new)))
        (lgut-holds-p (nth 5 run) (list nil))
        (lgut-holds-p (nth 5 run) (list (list :new)))
        (lgut-holds-p (nth 5 run) (list (list :old :new :old)))
        (lgut-holds-p (nth 7 run) nil)
        (lgut-holds-p (car (last run)) nil)
        (equal (take 3 (lgut-open (fn-bs-crash (car (car (last run))) nil)))
               (list (lgut-r 1) (lgut-r 2) (lgut-big))))))

; Every cut of P-LOG-RECOVER, :ok and with the zeroing write failed part
; way: the open corollary's first disjunct; its conclusion names r1 and r2.
(assert-event
 (let ((ok (lgut-recover-run))
       (torn (fn-lg-run (lgut-bs-raw) (lgut-ks0) (fn-lg-recover-program)
                        (list (cons :eio 4)) 0)))
   (and (equal (len torn) 1)
        (lgut-holds-p (nth 0 ok) (list (lgut-sels (lgut-pending-units (nth 0 ok)) :new)))
        (lgut-holds-p (nth 0 ok) (list nil))
        (lgut-holds-p (nth 3 ok) nil)
        (lgut-holds-p (nth 0 torn) (list (list (list :garble 1 2 3 4))))
        (equal (fn-lgk-acked (cdr (nth 0 ok))) 2)
        (equal (take 2 (lgut-open (fn-bs-crash (car (nth 0 ok)) (list nil))))
               (list (lgut-r 1) (lgut-r 2))))))

; A failed barrier (nothing of the batch landed): the kernel faults, nothing
; more is acknowledged, every later cut holds; the third record, never
; acknowledged, is not recovered.
(defun lgut-failed-run ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgu-host-run (car (lgut-opened)) (cdr (lgut-opened))
                   (list (lgut-take (lgut-r 3)) (list :seal :ok :ok :ok)
                         (list :fence (cons :eio (list nil)))
                         (list :fence :ok) (list :finish-one))
                   0 (lgut-max)))
(assert-event
 (let ((run (lgut-failed-run)))
   (and (equal (fn-lgk-phase (cdr (car (last run)))) :fault)
        (equal (fn-lgk-acked (cdr (car (last run)))) 2)
        (lgut-holds-p (car (last run)) nil)
        (equal (lgut-open (fn-bs-crash (car (car (last run))) nil))
               (list (lgut-r 1) (lgut-r 2))))))

; The count the host holds: the concrete kernel from fn-lgc-open of the
; segment read as a string, after the run's kernel operations, acknowledges
; three, the logical kernel's count.
(defun lgut-chars (octets)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom octets) nil (cons (code-char (nfix (car octets))) (lgut-chars (cdr octets)))))
(defun lgut-segment-string ()
  (declare (xargs :guard t :verify-guards nil))
  (coerce (lgut-chars (lgut-content)) 'string))
; The concrete kernel fnn-log-recover opens (fn-lgc-open's second value).
(defun lgut-opened-concrete ()
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (records c) (fn-lgc-open (lgut-segment-string) (lgut-genesis) (lgut-unit) (lgut-max) 0)
    (declare (ignore records))
    c))
(assert-event
 (let* ((ops (lgut-ops (lgut-big)))
        (final (fn-lgu-host-final (car (lgut-opened)) (cdr (lgut-opened)) ops 0 (lgut-max)))
        (host (fn-lgc-host-run (lgut-opened-concrete)
                               (fn-lgu-host-kops (car (lgut-opened)) (cdr (lgut-opened)) ops 0 (lgut-max)))))
   (and (equal (fn-lgd-octets (lgut-segment-string)) (lgut-content))
        (equal (fn-lgu-host-kops (car (lgut-opened)) (cdr (lgut-opened)) ops 0 (lgut-max))
               (list (lgut-take (lgut-big))
                     (list :seal (lgut-unit) (len (fn-bs-durable-content (car (lgut-opened)) 0)))
                     (list :fence (lgut-unit)) (list :finish-one)))
        (equal (fn-lgc-acked host) 3)
        (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
        (lgut-holds-p final nil))))

; The COMPLETE: from the fenced-on-arrival state of the run (r1, r2
; acknowledged, the big record in flight), the fence and one acknowledgement
; per member acknowledge exactly the committed records then the batch.
(assert-event
 (let* ((ks (cdr (nth 5 (lgut-run (lgut-big)))))
        (k2 (fn-lgk-host-run (fn-lgk-fence ks (lgut-unit))
                             (fn-lgu-finishes (len (fn-lgk-inflight ks))))))
   (and (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
        (true-listp (fn-lgk-committed ks)) (true-listp (fn-lgk-inflight ks))
        (equal (take (fn-lgk-acked k2) (fn-lgk-committed k2))
               (list (lgut-r 1) (lgut-r 2) (lgut-big))))))

; -----------------------------------------------------------------------------
; Hypothesis removal, one witness each, for the keystone.  Every retained
; hypothesis is asserted, the omitted one is asserted false, and the
; conclusion is false.

; (fn-lgk-relp bs ks ...) removed: a CORRUPTED-STATE witness.  The kernel
; says r9 is committed and acknowledged; the segment holds r1 and r2.
(defun lgut-bad-ks ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-make (list (lgut-r 1) (lgut-r 2) (lgut-r 9))
               (fn-lgk-last (cdr (lgut-opened))) (fn-lgk-frontier (cdr (lgut-opened)))
               (fn-lgk-next-txid (cdr (lgut-opened))) nil nil 3 :ready))
(assert-event
 (let* ((bs (car (lgut-opened)))
        (pair (car (fn-lgu-host-run bs (lgut-bad-ks) nil 0 (lgut-max)))))
   (and (not (fn-lgk-relp bs (lgut-bad-ks) 0 (lgut-genesis) (lgut-max)))
        (member-equal pair (fn-lgu-host-run bs (lgut-bad-ks) nil 0 (lgut-max)))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (not (lgut-holds-p pair nil)))))

; The take's verdict (fn-lgu-take-verdict, the gate fnn-log-publish asks
; before it fences): a record the log cannot frame at MAX is refused by name
; and the run goes on without it; three acknowledged would need it.
(assert-event
 (let* ((run (lgut-run (lgut-oversize))) (pair (car (last run))))
   (and (equal (fn-lgu-take-verdict (lgut-oversize) (lgut-max)) :record-exceeds-log-frame)
        (not (fn-lg-recordp (lgut-oversize) (lgut-max)))
        (equal (fn-lgk-acked (cdr pair)) 2)
        (not (member-equal (lgut-oversize) (fn-lgk-committed (cdr pair))))
        (lgut-holds-p pair nil))))

; The gate's witness: bypass it (the kernel takes the oversize record, as
; it would without the verdict); the related state is lost at once, and the
; rest of the run (seal, barrier, one acknowledgement) acknowledges a third
; record the open cannot read: two recovered.
(assert-event
 (let* ((taken (fn-lgk-host-step (cdr (lgut-opened)) (lgut-take (lgut-oversize))))
        (run (fn-lgu-host-run (car (lgut-opened)) taken (cdr (lgut-ops (lgut-oversize))) 0 (lgut-max)))
        (pair (car (last run))))
   (and (fn-lgk-relp (car (lgut-opened)) (cdr (lgut-opened)) 0 (lgut-genesis) (lgut-max))
        (not (fn-lgk-relp (car (lgut-opened)) taken 0 (lgut-genesis) (lgut-max)))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (equal (fn-lgk-acked (cdr pair)) 3)
        (equal (lgut-open (fn-bs-crash (car pair) nil)) (list (lgut-r 1) (lgut-r 2)))
        (not (lgut-holds-p pair nil)))))

; (member-equal pair (fn-lgu-host-run ...)) removed: a MUTATION witness.
; The kernel acknowledges the batch at log-written, before its barrier;
; that pair is no cut of the run, and with nothing landed the record is not
; recovered.
(assert-event
 (let* ((run (lgut-run (lgut-big)))
        (written (nth 5 run))
        (pair (cons (car written)
                    (fn-lgk-finish-one (fn-lgk-fence (cdr written) (lgut-unit))))))
   (and (fn-lgk-relp (car (lgut-opened)) (cdr (lgut-opened)) 0 (lgut-genesis) (lgut-max))
        (equal (fn-lgu-take-verdict (lgut-big) (lgut-max)) :admissible)
        (not (member-equal pair run))
        (fn-bs-crash-choicesp (list nil) (fn-bs-pending (car pair)) (fn-bs-unit (car pair)))
        (equal (fn-lgk-acked (cdr pair)) 3)
        (not (lgut-holds-p pair (list nil))))))

; (fn-bs-crash-imagep (car pair) image) removed: an "image" no crash of the
; last cut leaves (the segment wiped to zeros); the open recovers nothing.
(assert-event
 (let* ((run (lgut-run (lgut-big))) (pair (car (last run)))
        (wiped (lgut-store (fn-bs-zeros (len (fn-bs-durable-content (car pair) 0))) nil)))
   (and (fn-lgk-relp (car (lgut-opened)) (cdr (lgut-opened)) 0 (lgut-genesis) (lgut-max))
        (equal (fn-lgu-take-verdict (lgut-big) (lgut-max)) :admissible)
        (member-equal pair run)
        (null (fn-bs-pending (car pair)))
        (not (equal wiped (fn-bs-crash (car pair) nil)))
        (equal (fn-lgk-acked (cdr pair)) 3)
        (equal (lgut-open wiped) nil))))

; The run's rule (fn-lgu-host-step's :fence, the host's sealed-count gate):
; the host fences only a batch in flight.  After a failed barrier that
; landed nothing, a later :ok barrier and the kernel's fence of the faulted
; kernel (what fn-lg-fence-program would do) then one acknowledgement: three
; acknowledged, two recovered.  The run itself refuses that fence (the
; faulted kernel stays faulted with two acknowledged, above).
(defun lgut-barrier (bs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s) (fn-bs-fsync-file bs 0 :ok) (declare (ignore r)) s))
(assert-event
 (let* ((run (lgut-failed-run))
        (failed (nth 5 run))
        (bypass (cons (lgut-barrier (car failed))
                      (fn-lgk-finish-one (fn-lgk-fence (cdr failed) (lgut-unit))))))
   (and (equal (fn-lgk-phase (cdr failed)) :fault)
        (consp (fn-lgk-inflight (cdr failed)))
        (equal (fn-lgk-acked (cdr bypass)) 3)
        (not (member-equal bypass run))
        (fn-bs-crash-choicesp nil (fn-bs-pending (car bypass)) (fn-bs-unit (car bypass)))
        (not (lgut-holds-p bypass nil)))))
