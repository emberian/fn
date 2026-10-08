; PHASE 1c executable DRAFT. No production function is redefined.
; Proposed host entry: fn-ocp-gc-host-step. Existing operations are called
; directly; statements.lisp names the equations to current host-called cores.
; The native adapter does NOT call this entry yet. No claim of host refinement,
; byte-store crash refinement, or actual renderer provenance is made here.
(in-package "ACL2")
(include-book "../../../books/owner-reader-view")
(include-book "../../../books/owner-queued-work")
(include-book "../../../books/store-log-durable")

; Extend the EXISTING kernel with one bit: BATCH has been appended behind
; INFLIGHT and is frozen. Do not duplicate its history, counters or codec.
; After the first fence BATCH stays pending; promotion uses fn-lgk-append
; as a logical move, with no second physical write if BEHIND was true.
(defun fn-lgk-pipe-make (ks behind) (list ks (if behind t nil)))
(defun fn-lgk-pipe-ks (p) (nth 0 p))
(defun fn-lgk-pipe-behind (p) (nth 1 p))
(defun fn-lgk-pipe-d (p) (len (fn-lgk-committed (fn-lgk-pipe-ks p))))
(defun fn-lgk-pipe-acked (p) (fn-lgk-acked (fn-lgk-pipe-ks p)))
(defun fn-lgk-pipe-okp (p h)
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (true-listp p) (equal (len p) 2) (booleanp (fn-lgk-pipe-behind p))
         (true-listp ks) (true-listp h)
         (true-listp (fn-lgk-committed ks)) (true-listp (fn-lgk-inflight ks))
         (true-listp (fn-lgk-batch ks)) (fn-olr-linkp h ks)
         (fn-frame-digestp (fn-lgk-last ks))
         (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
         (implies (fn-lgk-pipe-behind p) (consp (fn-lgk-batch ks))))))

; The virtual fence computes the following offset/chain head using the
; existing codec. It does NOT install a durable kernel or acknowledge A.
; The returned write plan is for successful append receipt modeling; physical
; writing and its uncertain cuts need the new multi-write byte-store relation.
(defun fn-lgk-behind-write (p unit)
  (let ((tail (fn-lgk-fence (fn-lgk-pipe-ks p) unit)))
    (list :write (fn-lgk-frontier tail) (fn-lgk-append-octets tail unit))))
(defun fn-lgk-behind-admitsp (p unit extent)
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (not (fn-lgk-pipe-behind p)) (equal (fn-lgk-phase ks) :appended)
         (consp (fn-lgk-inflight ks)) (consp (fn-lgk-batch ks))
         (posp unit) (fn-lgk-fitsp (fn-lgk-fence ks unit) unit extent))))
(defun fn-lgk-append-behind (p unit extent)
  (if (fn-lgk-behind-admitsp p unit extent)
      (mv :appended (fn-lgk-pipe-make (fn-lgk-pipe-ks p) t)
          (fn-lgk-behind-write p unit))
    (mv :refused p nil)))
(defun fn-lgk-pipe-fence (p unit)
  (let ((ks (fn-lgk-pipe-ks p)))
    (if (equal (fn-lgk-phase ks) :appended)
        (fn-lgk-pipe-make (fn-lgk-fence ks unit) (fn-lgk-pipe-behind p)) p)))
(defun fn-lgk-pipe-fail (p)
  (fn-lgk-pipe-make (fn-lgk-fence-failed (fn-lgk-pipe-ks p)) (fn-lgk-pipe-behind p)))
(defun fn-lgk-pipe-ack (p n)
  (fn-lgk-pipe-make
   (fn-lgk-host-run (fn-lgk-pipe-ks p) (fn-lgu-finishes (nfix n)))
   (fn-lgk-pipe-behind p)))

; Proposed profile preflight counts ENCODED, padded log octets. The native
; profile must accommodate one maximal legal record. No arbitrary data cap.
(defun fn-olr-gc-profile-fitp (ks record bmax omax unit)
  (and (posp bmax) (natp omax) (posp unit)
       (<= (fn-lgc-append-len (fn-lgc-of (fn-lgk-prepare ks record)) unit) omax)))
(defun fn-lgk-pipe-take (p record txid count octets bmax omax unit)
  (let ((ks (fn-lgk-pipe-ks p)))
    (if (or (fn-lgk-pipe-behind p)
            (not (fn-olr-gc-profile-fitp ks record bmax omax unit)))
        (list :full p (fn-olr-entry-octets (len record) unit))
      (let ((a (fn-olr-take ks record txid count octets bmax omax unit)))
        (list (car a) (fn-lgk-pipe-make (cadr a) nil) (caddr a))))))
; Pure bounded START/START-NEXT plan: all records must fit before the owner
; consumes this selected quantum. Work still left remains in its input queue.
(defun fn-olr-gc-prepare (p records bmax omax unit)
  (declare (xargs :measure (len records)))
  (if (atom records) (mv t p)
    (let* ((ks (fn-lgk-pipe-ks p))
           (a (fn-lgk-pipe-take p (car records) (fn-lgk-next-txid ks)
                 (len (fn-lgk-batch ks)) (fn-lg-pack-len (fn-lgk-batch ks)) bmax omax unit)))
      (if (equal (car a) :taken)
          (fn-olr-gc-prepare (cadr a) (cdr records) bmax omax unit)
        (mv nil p)))))

; Composition fields (all draft/logical, concrete refinement still owed):
; 0 kernel+bit, 1 OCP scheduler, 2 OCVM views, 3 record history,
; 4 current job phase, 5 next job phase, 6/7 current/next member outcomes,
; 8 record dependency cuts, 9 releases, 10 unit, 11 extent, 12 BMAX,
; 13 OMAX, 14 append-behind write plan. Member counts are NOT record counts:
; a refusal may depend on earlier records without adding a record of its own.
(defun fn-ocp-gc-profilep (unit extent bmax omax)
  (and (posp unit) (natp extent) (posp bmax) (natp omax)))
(defun fn-ocp-gc-init (unit extent bmax omax)
  (list (fn-lgk-pipe-make (fn-lgk-make nil (make-list 32 :initial-element 0)
                                     0 1 nil nil 0 :ready) nil)
        (fn-ocp-init) (fn-ocvm-init) nil :idle :idle nil nil nil nil
        unit extent bmax omax nil))

; STATE invariant, not an implication from a supplied :fenced observation.
; Phase/frontier coupling must be established initially and preserved by the
; machine below. It is NOT checked as an admission test by any transition.
; Output safety is deliberately not a conjunct: the corollary is over STEP.
(defun fn-ocp-gc-linkedp (x)
  (let* ((p (nth 0 x)) (ks (fn-lgk-pipe-ks p)) (s (nth 1 x)) (m (nth 2 x))
         (phase (nth 4 x)) (np (nth 5 x)) (d (fn-lgk-pipe-d p))
         (c (fn-ocvm-c m)) (a (fn-ocvm-a m)) (b (fn-ocvm-b m)))
    (and (true-listp x) (equal (len x) 15)
         (fn-ocp-gc-profilep (nth 10 x) (nth 11 x) (nth 12 x) (nth 13 x))
         (fn-lgk-pipe-okp p (nth 3 x)) (fn-ocvm-inv m)
         (equal (fn-ocvm-w m) (len (nth 3 x)))
         (true-listp (nth 6 x)) (true-listp (nth 7 x))
         (equal b (len (fn-lgk-batch ks)))
         (equal (fn-ocp-open-next s) (if (posp b) t nil))
         (if (posp b) (member-eq np '(:intents :extend :append :fence)) (equal np :idle))
         (equal (fn-lgk-pipe-behind p) (if (equal np :fence) t nil))
         (cond
          ((equal phase :idle)
           (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :idle)
                (member-eq (fn-lgk-phase ks) '(:ready :fenced))
                (equal a 0) (equal b 0) (equal c d) (not (fn-lgk-inflight ks))))
          ((equal phase :stopped)
           (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :failed)
                (equal (fn-lgk-phase ks) :fault)
                (or (and (equal c d) (equal a (len (fn-lgk-inflight ks))))
                    (and (equal d (+ c a)) (not (fn-lgk-inflight ks))))))
          ((member-eq phase '(:intents :extend :append :fence))
           (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :staged)
                (equal (fn-lgk-phase ks) :appended) (posp a)
                (equal c d) (equal a (len (fn-lgk-inflight ks)))))
          ((member-eq phase '(:resolutions :done))
           (and (equal (fn-ocs-phase (fn-ocp-ocs s)) :staged)
                (equal (fn-lgk-phase ks) :fenced) (posp a)
                (equal d (+ c a)) (not (fn-lgk-inflight ks))))
          (t nil)))))

; Executable multiple-value projections (ACL2 rejects raw MV-NTH of these
; calls inside DEFUN). Equations in statements.lisp name the direct calls.
(defun fn-ocp-gc-event-action (s e)
  (mv-let (action after) (fn-ocp-commit-event s e) (declare (ignore after)) action))
(defun fn-ocp-gc-event-state (s e)
  (mv-let (action after) (fn-ocp-commit-event s e) (declare (ignore action)) after))
(defun fn-ocp-gc-pick (s w)
  (mv-let (class after) (fn-ocp-next s w) (declare (ignore class)) after))
(defun fn-lgk-behind-state (p unit extent)
  (mv-let (word after effect) (fn-lgk-append-behind p unit extent)
    (declare (ignore word effect)) after))
(defun fn-lgk-behind-effect (p unit extent)
  (mv-let (word after effect) (fn-lgk-append-behind p unit extent)
    (declare (ignore word after)) effect))

(defun fn-ocp-gc-stop (x)
  (let* ((action (fn-ocp-gc-event-action (nth 1 x) :failed))
         (s (fn-ocp-gc-event-state (nth 1 x) :failed))
         (rs (fn-ocs-member-releases action (append (nth 6 x) (nth 7 x)))))
    (update-nth 9 rs (update-nth 4 :stopped
      (update-nth 1 s (update-nth 0 (fn-lgk-pipe-fail (nth 0 x)) x))))))
(defun fn-ocp-gc-start (x records outcomes nextp)
  (let* ((p (nth 0 x)) (s (nth 1 x)) (m (nth 2 x))
         (unit (nth 10 x)) (extent (nth 11 x)))
    (if (and (consp records) (true-listp records) (true-listp outcomes)
             (if nextp
                 (and (member-eq (nth 4 x) '(:intents :extend :append :fence))
                      (equal (nth 5 x) :idle) (not (fn-ocp-open-next s)))
               (equal (nth 4 x) :idle)))
        (mv-let (ok q) (fn-olr-gc-prepare p records (nth 12 x) (nth 13 x) unit)
          (let ((ks (fn-lgk-pipe-ks q)))
            (if (and ok (or nextp (fn-lgc-append-admitsp (fn-lgc-of ks) unit extent)))
                (let* ((event (if nextp :next-started :started))
                       (v (if nextp :next :start))
                       (q (if nextp q (fn-lgk-pipe-make (fn-lgk-append ks unit extent) nil))))
                  (update-nth (if nextp 7 6) outcomes
                   (update-nth (if nextp 5 4) (fn-oqw-start :batch)
                    (update-nth 3 (append (nth 3 x) records)
                     (update-nth 2 (fn-ocvm-step m (list v (len records)))
                      (update-nth 1 (fn-ocp-gc-event-state s event)
                       (update-nth 0 q x)))))))
              x)))
      x)))

; IO step is the RECEIPT of exactly one fn-oqw phase. The next job can run
; through its append but cannot fence until promoted: one sync outstanding.
; Unknown/late events stutter. Failures are sticky, never erased by late OK.
(defun fn-ocp-gc-io (x nextp word)
  (let* ((slot (if nextp 5 4)) (phase (nth slot x)) (p (nth 0 x))
         (m (nth 2 x)) (unit (nth 10 x)) (extent (nth 11 x)))
    (if (or (not (member-eq phase (if nextp '(:intents :extend :append)
                                   '(:intents :extend :append :fence :resolutions))))
            (and nextp (equal phase :append)
                 (or (not (equal (nth 4 x) :fence))
                     (not (fn-lgk-behind-admitsp p unit extent)))))
        x
      (let ((x (if (and (not nextp) (equal phase :resolutions))
                   (update-nth 8 (list (+ (fn-ocvm-c m) (fn-ocvm-a m))) x) x)))
        (if (not (equal word :ok)) (fn-ocp-gc-stop x)
          (let* ((q (cond ((and nextp (equal phase :append))
                          (fn-lgk-behind-state p unit extent))
                         ((and (not nextp) (equal phase :fence)) (fn-lgk-pipe-fence p unit))
                         (t p)))
                 (effect (if (and nextp (equal phase :append))
                             (fn-lgk-behind-effect p unit extent) nil)))
            (update-nth 14 effect
             (update-nth slot (fn-oqw-step :batch phase word) (update-nth 0 q x)))))))))

(defun fn-ocp-gc-collect (x)
  (if (not (equal (nth 4 x) :done)) x
    (let* ((s (nth 1 x)) (m (nth 2 x)) (unit (nth 10 x)) (extent (nth 11 x))
           (action (fn-ocp-gc-event-action s :fenced))
           (s1 (fn-ocp-gc-event-state s :fenced))
           (p1 (fn-lgk-pipe-ack (nth 0 x) (fn-ocvm-a m)))
           (ks (fn-lgk-pipe-ks p1)) (nextp (posp (fn-ocvm-b m))))
      ; No partly consumed completion on a refused promotion. Its immutable
      ; capture can wait for an off-owner extent extension before this step.
      (if (and nextp (not (fn-lgc-append-admitsp (fn-lgc-of ks) unit extent))) x
        (let ((p2 (if nextp (fn-lgk-pipe-make (fn-lgk-append ks unit extent) nil) p1)))
          (list p2 (fn-ocp-gc-event-state s1 :completed)
                (fn-ocvm-step m '(:complete)) (nth 3 x)
                (if nextp (nth 5 x) :idle) :idle (if nextp (nth 7 x) nil) nil
                (list (+ (fn-ocvm-c m) (fn-ocvm-a m)))
                (fn-ocs-member-releases action (nth 6 x))
                unit extent (nth 12 x) (nth 13 x) nil))))))

(defun fn-ocp-gc-host-step (x event)
  (let* ((x (update-nth 14 nil (update-nth 9 nil (update-nth 8 nil x))))
         (kind (car event)))
    (if (equal (nth 4 x) :stopped) x
      (case kind
        (:start (fn-ocp-gc-start x (nth 1 event) (nth 2 event) nil))
        (:next (fn-ocp-gc-start x (nth 1 event) (nth 2 event) t))
        (:io (fn-ocp-gc-io x (equal (nth 1 event) :next) (nth 2 event)))
        (:collect (fn-ocp-gc-collect x))
        (:reader (update-nth 8 (list (fn-ocv-reader-view (fn-ocvm-views (nth 2 x))
                                                       (fn-ocvm-w (nth 2 x)))) x))
        (:pick (update-nth 1 (fn-ocp-gc-pick (nth 1 x) (nth 1 event)) x))
        (otherwise x)))))
(defun fn-ocp-gc-run (x events)
  (declare (xargs :measure (len events)))
  (if (atom events) x (fn-ocp-gc-run (fn-ocp-gc-host-step x (car events)) (cdr events))))
(defun fn-ocv-gc-prefix-durablep (h p cut)
  (and (natp cut) (<= cut (fn-lgk-pipe-d p))
       (fn-lg-prefixp (take cut h) (fn-lgk-committed (fn-lgk-pipe-ks p)))))
(defun fn-ocp-gc-cuts-okp (h p cuts)
  (if (atom cuts) t
    (and (fn-ocv-gc-prefix-durablep h p (car cuts)) (fn-ocp-gc-cuts-okp h p (cdr cuts)))))
(defun fn-ocp-gc-reveals-okp (x)
  (fn-ocp-gc-cuts-okp (nth 3 x) (nth 0 x) (nth 8 x)))

; Failure statement includes the actual current job's :fence receipt, both
; batches, and an arbitrary post-stop event suffix: no late receipt can ACK.
(defun fn-ocp-gc-failure-hyp (x)
  (and (fn-ocp-gc-linkedp x) (equal (nth 4 x) :fence)
       (consp (nth 6 x)) (consp (nth 7 x))))
(defun fn-ocp-gc-failure-okp (x events)
  (let* ((y (fn-ocp-gc-host-step x '(:io :current :uncertain)))
         (z (fn-ocp-gc-run y events)))
    (and (equal (nth 4 y) :stopped) (equal (nth 4 z) :stopped)
         (equal (fn-lgk-phase (fn-lgk-pipe-ks (nth 0 z))) :fault)
         (equal (fn-lgk-pipe-d (nth 0 z)) (fn-lgk-pipe-d (nth 0 x)))
         (equal (fn-lgk-pipe-acked (nth 0 z)) (fn-lgk-pipe-acked (nth 0 x)))
         (<= (fn-lgk-pipe-acked (nth 0 z)) (fn-lgk-pipe-d (nth 0 x)))
         (equal (len (nth 9 y)) (+ (len (nth 6 x)) (len (nth 7 x))))
         (subsetp-equal (nth 9 y) '(:own-uncertain :uncertain-reply :close)))))

(defun fn-olr-gc-membership-hyp (h p record txid count octets bmax omax unit)
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (fn-lgk-pipe-okp p h)
         (equal count (len (fn-lgk-batch ks)))
         (equal octets (fn-lg-pack-len (fn-lgk-batch ks)))
         (equal (car (fn-lgk-pipe-take p record txid count octets bmax omax unit)) :taken))))
(defun fn-olr-gc-membership-okp (h p record txid count octets bmax omax unit)
  (let* ((ks (fn-lgk-pipe-ks p))
         (after (fn-lgk-pipe-ks (cadr (fn-lgk-pipe-take p record txid count octets bmax omax unit))))
         (d (len (fn-lgk-committed ks))) (seal (+ d (len (fn-lgk-inflight ks))))
         (h2 (append h (list record))))
    (and (equal (fn-lgk-inflight after) (fn-lgk-inflight ks))
         (equal (fn-lgk-batch after) (nthcdr seal h2))
         (equal (append (fn-lgk-inflight after) (fn-lgk-batch after)) (nthcdr d h2))
         (<= (len (fn-lgk-batch after)) bmax)
         (<= (fn-lgc-append-len (fn-lgc-of after) unit) omax))))
