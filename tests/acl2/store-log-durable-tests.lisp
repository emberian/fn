; Teeth for books/store-log-durable (lane m1-durable, 2026-10-04): the
; lemma fn-lgu-acknowledged-records-are-recovered-at-every-cut (the
; host-entry keystone fn-lgu-acknowledge-acknowledges-only-recoverable-records
; states it over the function the host calls), its open
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
(include-book "../../books/defkeystone")
(include-book "teeth-ground-lemma")

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
; The state the open's copy leaves (books/store-log-recover-copy.lisp K1):
; the segment durably holds the read's validated prefix [0, F), then zeros,
; nothing pending; the kernel is the read's.
(defun lgut-opened ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((f (fn-lgk-frontier (lgut-ks0))))
    (cons (lgut-store (append (fn-bs-take f (lgut-content))
                              (fn-bs-zeros (- (len (lgut-content)) f)))
                      nil)
          (lgut-ks0))))

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

; -----------------------------------------------------------------------------
; Lane m1-durable-2.  The log's frame bound (fn-lgu-log-max-frames-every-
; record-within-r, fn-lgu-log-max-refuses-past-r).  At R = 64 a record of R
; octets is framed at R + 32 and was refused at the old bound R (the batch-6
; regression: shipped profiles admit records of R-31..R octets); R + 1 is
; refused at both.
(defun lgut-octets (n) (declare (xargs :guard t :verify-guards nil)) (make-list n :initial-element 7))
(assert-event (equal (fn-lgu-take-verdict (lgut-octets 64) (fn-lgu-log-max 64)) :admissible))
(assert-event (equal (fn-lgu-take-verdict (lgut-octets 64) 64) :record-exceeds-log-frame))
(assert-event (equal (fn-lgu-take-verdict (lgut-octets 33) 64) :record-exceeds-log-frame))
(assert-event (equal (fn-lgu-take-verdict (lgut-octets 65) (fn-lgu-log-max 64))
                     :record-exceeds-log-frame))
; Over the development preset's own R: a record of exactly R octets is framed.
(defconst *lgut-dev-r*
  (fn-bs-profile-max-record-octets (fn-bs-config-for-profile :development)))
(assert-event (and (posp *lgut-dev-r*)
                   (equal (fn-lgu-take-verdict (lgut-octets *lgut-dev-r*)
                                               (fn-lgu-log-max *lgut-dev-r*))
                          :admissible)
                   (equal (fn-lgu-take-verdict (lgut-octets *lgut-dev-r*) *lgut-dev-r*)
                          :record-exceeds-log-frame)))

; fn-lgu-acknowledge (the host's one call): over the concrete kernel of the
; opened segment with two committed records, after the third's take, seal
; and fence, acknowledging 1 is one fn-lgc-finish-one, and asking for more
; than the committed records stops at their count.
(defun lgut-concrete (record)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgc-of (cdr (car (last (lgut-run record))))))
(assert-event
 (let ((c (lgut-concrete (lgut-r 3))))
   (and (equal (fn-lgu-acknowledge c 1) (fn-lgc-finish-one c))
        (equal (fn-lgu-acknowledge c 0) c)
        (equal (fn-lgc-acked (fn-lgu-acknowledge c 9)) (fn-lgc-count c)))))
;
; TEETH-21 BEGIN
; Teeth (TEETH CONTRACT v1) for the store-log-durable keystones.  Where a
; hypothesis is fn-bs-crash-imagep (a defun-sk no evaluator runs) each witness
; is a ground lemma (tests/acl2/teeth-ground-lemma.lisp) over fixtures computed
; once (defconst-eval): the prover evaluates literals, never a run.
; Owed, no ground counterexample found: fn-lgu-crash-keeps-the-prefix's `ino'
; and `(natp f)'; fn-lgu-complete-acknowledges-the-fenced-batch's
; `(true-listp (fn-lgk-committed ks))' (the fence appends it whole; shares the
; `lists' label with the inflight list, whose removal is witnessed).
; Not written: fn-lgu-recover-program-establishes-the-relation and
; fn-lgu-open-run-acknowledges-only-recoverable-records state their claim over
; fn-lg-recovered-kernel, whose next txid reads fn-record-decode-exact, an
; attached seam the prover cannot evaluate: no ground lemma.
(defun lgut-s5 () (declare (xargs :guard t :verify-guards nil)) (car (nth 5 (lgut-run (lgut-big)))))
(defun lgut-s4 () (declare (xargs :guard t :verify-guards nil)) (car (nth 4 (lgut-run (lgut-big)))))
(defun lgut-land (s)
  (declare (xargs :guard t :verify-guards nil))
  (list (lgut-sels (floor (len (nth 3 (car (fn-bs-pending s)))) (lgut-unit)) :new)))
(defconst *lgut-c-ckp*
  '(() (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                     (<= f (len (fn-bs-durable-content s ino)))
                     (fn-bs-crash-imagep s image))
                (let ((c2 (fn-bs-durable-content image ino)))
                  (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                       (<= f (len c2)))))))
(defconst-eval *lgut-k-s5* (lgut-s5))
(defconst-eval *lgut-k-i5* (fn-bs-crash (lgut-s5) nil))
(teeth-ground-lemma lgut-gl-ckp-witness *lgut-c-ckp*
  ((s *lgut-k-s5*) (ino 0) (f 88) (image *lgut-k-i5*))
  :suff (*lgut-k-s5* *lgut-k-i5* nil))
(defconst-eval *lgut-k-land5* (lgut-land (lgut-s5)))
(defconst-eval *lgut-k-s4* (lgut-s4))
(defconst-eval *lgut-k-i4* (fn-bs-crash (lgut-s4) nil))
(defconst-eval *lgut-k-landed5* (fn-bs-crash (lgut-s5) (lgut-land (lgut-s5))))
(defconst-eval *lgut-k-wiped* (lgut-store (fn-bs-zeros (len (fn-bs-durable-content (lgut-s5) 0))) nil))
(teeth-ground-lemma lgut-gl-ckp-no-writes *lgut-c-ckp*
  ((s *lgut-k-s5*) (ino 0) (f 1000) (image *lgut-k-landed5*))
  :mutation (:conclusion (implies (and ino (natp f) (<= f (len (fn-bs-durable-content s ino)))
                                       (fn-bs-crash-imagep s image))
                                  (let ((c2 (fn-bs-durable-content image ino)))
                                    (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                         (<= f (len c2))))))
  :suff (*lgut-k-s5* *lgut-k-landed5* *lgut-k-land5*))
(teeth-ground-lemma lgut-gl-ckp-no-within *lgut-c-ckp*
  ((s *lgut-k-s4*) (ino 0) (f 5000) (image *lgut-k-i4*))
  :mutation (:conclusion (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                                       (fn-bs-crash-imagep s image))
                                  (let ((c2 (fn-bs-durable-content image ino)))
                                    (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                         (<= f (len c2))))))
  :suff (*lgut-k-s4* *lgut-k-i4* nil))
(teeth-ground-lemma lgut-gl-ckp-no-image *lgut-c-ckp*
  ((s *lgut-k-s5*) (ino 0) (f 88) (image *lgut-k-wiped*))
  :mutation (:conclusion (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                                       (<= f (len (fn-bs-durable-content s ino))))
                                  (let ((c2 (fn-bs-durable-content image ino)))
                                    (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                         (<= f (len c2))))))
  :keystone fn-lgu-crash-keeps-the-prefix)

(defteeth fn-lgu-crash-keeps-the-prefix
  :claim (() (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                           (<= f (len (fn-bs-durable-content s ino)))
                           (fn-bs-crash-imagep s image))
                      (let ((c2 (fn-bs-durable-content image ino)))
                        (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                             (<= f (len c2))))))
  :subject fn-bs-crash
  :witness ((s *lgut-k-s5*) (ino 0) (f 88) (image *lgut-k-i5*))
  :witness-lemma lgut-gl-ckp-witness
  :mutations ((writes-below-f
               (:conclusion (implies (and ino (natp f) (<= f (len (fn-bs-durable-content s ino)))
                                          (fn-bs-crash-imagep s image))
                                     (let ((c2 (fn-bs-durable-content image ino)))
                                       (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                            (<= f (len c2))))))
               ((s *lgut-k-s5*) (ino 0) (f 1000) (image *lgut-k-landed5*))
               :fault "a pending write below the frontier that lands over the committed prefix"
               :lemma lgut-gl-ckp-no-writes)
              (frontier-past-content
               (:conclusion (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                                          (fn-bs-crash-imagep s image))
                                     (let ((c2 (fn-bs-durable-content image ino)))
                                       (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                            (<= f (len c2))))))
               ((s *lgut-k-s4*) (ino 0) (f 5000) (image *lgut-k-i4*))
               :fault "a frontier past the stored octets: the image cannot keep a prefix it never had"
               :lemma lgut-gl-ckp-no-within)
              (not-a-crash-image
               (:conclusion (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                                          (<= f (len (fn-bs-durable-content s ino))))
                                     (let ((c2 (fn-bs-durable-content image ino)))
                                       (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                                            (<= f (len c2))))))
               ((s *lgut-k-s5*) (ino 0) (f 88) (image *lgut-k-wiped*))
               :fault "a wiped segment offered as the image of a store whose committed prefix is nonzero"
               :lemma lgut-gl-ckp-no-image)))

(defconst-eval *lgut-k-g* (lgut-genesis))
(defconst-eval *lgut-k-ks5* (cdr (nth 5 (lgut-run (lgut-big)))))
(defconst-eval *lgut-k-open-s* (car (lgut-opened)))
(defconst-eval *lgut-k-open-ks* (cdr (lgut-opened)))
(defconst-eval *lgut-k-badks* (lgut-bad-ks))
(defconst-eval *lgut-k-i-open* (fn-bs-crash (car (lgut-opened)) nil))
(defconst-eval *lgut-k-i-last* (fn-bs-crash (car (car (last (lgut-run (lgut-big))))) nil))
(defconst *lgut-c-scan*
  '(((safe (fn-lgu-safep bs ks ino genesis max)) (img (fn-bs-crash-imagep bs image)))
    (let* ((c (fn-bs-durable-content bs ino)) (c2 (fn-bs-durable-content image ino))
           (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
      (equal (car (fn-lg-scan c2 genesis unit max))
             (append (fn-lgk-committed ks)
                     (car (fn-lg-scan (nthcdr f c2)
                                      (fn-lg-scan-last (fn-bs-take f c) genesis unit max)
                                      unit max)))))))
(teeth-ground-lemma lgut-gl-scan-witness *lgut-c-scan*
  ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-landed5*))
  :suff (*lgut-k-s5* *lgut-k-landed5* *lgut-k-land5*))
(teeth-ground-lemma lgut-gl-scan-no-safe *lgut-c-scan*
  ((bs *lgut-k-open-s*) (ks *lgut-k-badks*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-i-open*))
  :without safe :suff (*lgut-k-open-s* *lgut-k-i-open* nil))
(teeth-ground-lemma lgut-gl-scan-no-img *lgut-c-scan*
  ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-wiped*))
  :without img :keystone fn-lgu-safe-image-scans-the-committed-records-first)

(defteeth fn-lgu-safe-image-scans-the-committed-records-first
  :claim (((safe (fn-lgu-safep bs ks ino genesis max)) (img (fn-bs-crash-imagep bs image)))
          (let* ((c (fn-bs-durable-content bs ino)) (c2 (fn-bs-durable-content image ino))
                 (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
            (equal (car (fn-lg-scan c2 genesis unit max))
                   (append (fn-lgk-committed ks)
                           (car (fn-lg-scan (nthcdr f c2)
                                            (fn-lg-scan-last (fn-bs-take f c) genesis unit max)
                                            unit max))))))
  :subject fn-lg-scan
  :witness ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-landed5*))
  :witness-lemma lgut-gl-scan-witness
  :breaks ((safe ((bs *lgut-k-open-s*) (ks *lgut-k-badks*) (image *lgut-k-i-open*))
                 :lemma lgut-gl-scan-no-safe)
           (img ((image *lgut-k-wiped*)) :lemma lgut-gl-scan-no-img))
  :mutations (:not-applicable "the removal witnesses are this keystone's teeth: its two hypotheses are both labelled"))

(defconst *lgut-c-recovers*
  '(((safe (fn-lgu-safep bs ks ino genesis max)) (img (fn-bs-crash-imagep bs image)))
    (let ((a (fn-lgk-acked ks))
          (recovered (fn-lgk-committed
                      (fn-lgk-recover (fn-bs-durable-content image ino)
                                      genesis (fn-bs-unit bs) max next-txid))))
      (and (<= a (len recovered))
           (equal (take a recovered) (take a (fn-lgk-committed ks)))))))
(teeth-ground-lemma lgut-gl-rec-witness *lgut-c-recovers*
  ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-landed5*) (next-txid 0))
  :suff (*lgut-k-s5* *lgut-k-landed5* *lgut-k-land5*))
(teeth-ground-lemma lgut-gl-rec-no-safe *lgut-c-recovers*
  ((bs *lgut-k-open-s*) (ks *lgut-k-badks*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-i-open*) (next-txid 0))
  :without safe :suff (*lgut-k-open-s* *lgut-k-i-open* nil))
(teeth-ground-lemma lgut-gl-rec-no-img *lgut-c-recovers*
  ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-wiped*) (next-txid 0))
  :without img :keystone fn-lgu-safe-image-recovers-the-acknowledged-records)
(defteeth fn-lgu-safe-image-recovers-the-acknowledged-records
  :claim (((safe (fn-lgu-safep bs ks ino genesis max)) (img (fn-bs-crash-imagep bs image)))
          (let ((a (fn-lgk-acked ks))
                (recovered (fn-lgk-committed
                            (fn-lgk-recover (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max next-txid))))
            (and (<= a (len recovered))
                 (equal (take a recovered) (take a (fn-lgk-committed ks))))))
  :subject fn-lgk-recover
  :witness ((bs *lgut-k-s5*) (ks *lgut-k-ks5*) (ino 0) (genesis *lgut-k-g*) (max 4096) (image *lgut-k-landed5*) (next-txid 0))
  :witness-lemma lgut-gl-rec-witness
  :breaks ((safe ((bs *lgut-k-open-s*) (ks *lgut-k-badks*) (image *lgut-k-i-open*))
                 :lemma lgut-gl-rec-no-safe)
           (img ((image *lgut-k-wiped*)) :lemma lgut-gl-rec-no-img))
  :mutations (:not-applicable "the removal witnesses are this keystone's teeth: its two hypotheses are both labelled"))

(defconst-eval *lgut-k-ops-big* (lgut-ops (lgut-big)))
(defconst-eval *lgut-k-run-big* (lgut-run (lgut-big)))
(defconst-eval *lgut-k-pair5* (nth 5 (lgut-run (lgut-big))))

(defconst-eval *lgut-k-bad-pair-s*
  (car (car (fn-lgu-host-run (car (lgut-opened)) (lgut-bad-ks) nil 0 (lgut-max)))))
(defconst-eval *lgut-k-bad-pair*
  (car (fn-lgu-host-run (car (lgut-opened)) (lgut-bad-ks) nil 0 (lgut-max))))
(defconst-eval *lgut-k-bad-pair-i*
  (fn-bs-crash (car (car (fn-lgu-host-run (car (lgut-opened)) (lgut-bad-ks) nil 0 (lgut-max)))) nil))
(defconst-eval *lgut-k-early-pair*
  (cons (car (nth 5 (lgut-run (lgut-big))))
        (fn-lgk-finish-one (fn-lgk-fence (cdr (nth 5 (lgut-run (lgut-big)))) (lgut-unit)))))
(defconst-eval *lgut-k-early-i*
  (fn-bs-crash (car (nth 5 (lgut-run (lgut-big)))) (list nil)))
(defconst-eval *lgut-k-pair-last* (car (last (lgut-run (lgut-big)))))
(defconst-eval *lgut-k-wiped-last*
  (lgut-store (fn-bs-zeros (len (fn-bs-durable-content (car (car (last (lgut-run (lgut-big))))) 0))) nil))
(defconst *lgut-c-cut*
  '(((rel (fn-lgk-relp bs ks ino genesis max))
     (member (member-equal pair (fn-lgu-host-run bs ks ops ino max)))
     (img (fn-bs-crash-imagep (car pair) image)))
    (let ((a (fn-lgk-acked (cdr pair)))
          (recovered (fn-lgk-committed
                      (fn-lgk-recover (fn-bs-durable-content image ino)
                                      genesis (fn-bs-unit (car pair)) max next-txid))))
      (and (<= a (len recovered))
           (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))
(teeth-ground-lemma lgut-gl-cut-witness *lgut-c-cut*
  ((bs *lgut-k-open-s*) (ks *lgut-k-open-ks*) (ino 0) (genesis *lgut-k-g*) (max 4096)
   (pair *lgut-k-pair5*) (ops *lgut-k-ops-big*) (image *lgut-k-landed5*) (next-txid 0))
  :suff (*lgut-k-s5* *lgut-k-landed5* *lgut-k-land5*))
(teeth-ground-lemma lgut-gl-cut-no-rel *lgut-c-cut*
  ((bs *lgut-k-open-s*) (ks *lgut-k-badks*) (ino 0) (genesis *lgut-k-g*) (max 4096)
   (pair *lgut-k-bad-pair*) (ops nil) (image *lgut-k-bad-pair-i*) (next-txid 0))
  :without rel :suff (*lgut-k-bad-pair-s* *lgut-k-bad-pair-i* nil))
(teeth-ground-lemma lgut-gl-cut-no-member *lgut-c-cut*
  ((bs *lgut-k-open-s*) (ks *lgut-k-open-ks*) (ino 0) (genesis *lgut-k-g*) (max 4096)
   (pair *lgut-k-early-pair*) (ops *lgut-k-ops-big*) (image *lgut-k-early-i*) (next-txid 0))
  :without member :suff (*lgut-k-s5* *lgut-k-early-i* (quote (nil))))
(teeth-ground-lemma lgut-gl-cut-no-img *lgut-c-cut*
  ((bs *lgut-k-open-s*) (ks *lgut-k-open-ks*) (ino 0) (genesis *lgut-k-g*) (max 4096)
   (pair *lgut-k-pair-last*) (ops *lgut-k-ops-big*) (image *lgut-k-wiped-last*) (next-txid 0))
  :without img :keystone fn-lgu-acknowledged-records-are-recovered-at-every-cut)
(defteeth fn-lgu-acknowledged-records-are-recovered-at-every-cut
  :claim (((rel (fn-lgk-relp bs ks ino genesis max))
           (member (member-equal pair (fn-lgu-host-run bs ks ops ino max)))
           (img (fn-bs-crash-imagep (car pair) image)))
          (let ((a (fn-lgk-acked (cdr pair)))
                (recovered (fn-lgk-committed
                            (fn-lgk-recover (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit (car pair)) max next-txid))))
            (and (<= a (len recovered))
                 (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))
  :subject fn-lgu-host-run
  :witness ((bs *lgut-k-open-s*) (ks *lgut-k-open-ks*) (ino 0) (genesis *lgut-k-g*) (max 4096)
            (pair *lgut-k-pair5*) (ops *lgut-k-ops-big*) (image *lgut-k-landed5*) (next-txid 0))
  :witness-lemma lgut-gl-cut-witness
  :breaks ((rel ((ks *lgut-k-badks*) (pair *lgut-k-bad-pair*) (ops nil) (image *lgut-k-bad-pair-i*))
                :lemma lgut-gl-cut-no-rel)
           (member ((pair *lgut-k-early-pair*) (image *lgut-k-early-i*))
                   :lemma lgut-gl-cut-no-member)
           (img ((pair *lgut-k-pair-last*) (image *lgut-k-wiped-last*))
                :lemma lgut-gl-cut-no-img))
  :mutations (:not-applicable "the removal witnesses are this keystone's teeth: its three hypotheses are all labelled"))

(defun lgut-mk (ks committed inflight acked)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgk-make committed (fn-lgk-last ks) (fn-lgk-frontier ks) (fn-lgk-next-txid ks)
               (fn-lgk-batch ks) inflight acked (fn-lgk-phase ks)))
(defconst-eval *lgut-k-ks-acked1*
  (let ((ks (cdr (nth 5 (lgut-run (lgut-big))))))
    (lgut-mk ks (fn-lgk-committed ks) (fn-lgk-inflight ks) 1)))
(defconst-eval *lgut-k-ks-improper-inflight*
  (let ((ks (cdr (nth 5 (lgut-run (lgut-big))))))
    (lgut-mk ks (fn-lgk-committed ks) (list* (lgut-big) 'x) (fn-lgk-acked ks))))
(defteeth fn-lgu-complete-acknowledges-the-fenced-batch
  :claim (((all-acknowledged (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks))))
           (lists (and (true-listp (fn-lgk-committed ks)) (true-listp (fn-lgk-inflight ks)))))
          (let ((k2 (fn-lgk-host-run (fn-lgk-fence ks unit)
                                     (fn-lgu-finishes (len (fn-lgk-inflight ks))))))
            (equal (take (fn-lgk-acked k2) (fn-lgk-committed k2))
                   (append (fn-lgk-committed ks) (fn-lgk-inflight ks)))))
  :subject fn-lgu-finishes
  :witness ((ks *lgut-k-ks5*) (unit 4))
  :breaks ((all-acknowledged ((ks *lgut-k-ks-acked1*)))
           (lists ((ks *lgut-k-ks-improper-inflight*))
                  :logical "an improper inflight list is outside the guard of append"))
  :mutations ((batch-dropped
               (:conclusion (let ((k2 (fn-lgk-host-run (fn-lgk-fence ks unit)
                                                       (fn-lgu-finishes (len (fn-lgk-inflight ks))))))
                              (equal (take (fn-lgk-acked k2) (fn-lgk-committed k2))
                                     (fn-lgk-committed ks))))
               ((ks *lgut-k-ks5*) (unit 4))
               :fault "the COMPLETE acknowledging only the committed records and not the fenced batch")))
(defteeth fn-lgu-take-verdict-admits-exactly-log-records
  :claim (() (and (member-equal (fn-lgu-take-verdict record max)
                                '(:admissible :record-exceeds-log-frame))
                  (iff (equal (fn-lgu-take-verdict record max) :admissible)
                       (fn-lg-recordp record max))))
  :subject fn-lgu-take-verdict
  :witness ((record (lgut-octets 3)) (max 4096))
  :mutations ((refuses-a-framable-record
               (:conclusion (equal (fn-lgu-take-verdict record max) :record-exceeds-log-frame))
               ((record (lgut-octets 3)) (max 4096))
               :fault "the verdict refusing a record the log frames")
              (admits-an-unframable-record
               (:conclusion (iff (equal (fn-lgu-take-verdict record max) :admissible)
                                 (not (fn-lg-recordp record max))))
               ((record (lgut-oversize)) (max 4096))
               :fault "the verdict inverted: admitting exactly the records the log cannot frame")))

; TEETH-21 END
