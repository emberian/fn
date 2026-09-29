; fn: the readers during a batch's barrier read at the durable view (lane
; scheduler-2-rebase, 2026-09-27; coordinator decision PKT-828: "while a
; batch's barrier is in flight the owner admits READS and new POST prepares
; that queue into the NEXT batch; the fsync holds no owner-level exclusion;
; only the in-flight batch's members wait for their replies").
;
; books/owner-commit-steps.lisp admits :reader quanta while a batch is in
; flight (fn-ocs-in-flight-admits-only-inspect-commit-and-reader).  The
; START of a batch runs each member through its sequential life, so the
; owner's working view (books/owner.lisp fn-own-view) already holds the
; batch's records when its barrier starts.  A reader must not see them:
;
;   THE READER VIEW.  Before a START drains its members the owner's view is
;   captured (host/owner-host.lisp fn-owner-reader-views-capture :start);
;   before a START-NEXT drains the next batch, the view then is captured as
;   the NEXT reader view (:next); a COMPLETE, after its replies, makes the
;   next reader view current (:complete), or, with no next batch, releases
;   the capture (the working view is the durable one again).  A reader
;   quantum runs its entry on the owner with the reader view put in place
;   of the working view (fn-ocfg-with-view), and the working view is put
;   back after it.
;
; What this book proves:
;
;   KEYSTONE fn-ocvm-reader-view-is-the-completed-prefix: in the capture
;   discipline's count model (views as the record counts they are views
;   of), along every legal sequence of START, START-NEXT, COMPLETE and drop
;   events, the reader view is the view at C, the number of records whose
;   batch COMPLETED -- whose barrier returned fenced
;   (fn-ocp-complete-only-after-the-barrier) -- and never counts a record
;   of the batch in flight or of the next one.
;
;   KEYSTONE fn-ocl-relation-of-a-view-captured-before-appends: a view
;   captured from a related owner (books/config-owner-live-complete.lisp
;   fn-ocl-relation), put into a related owner whose Store has only
;   APPENDED records since (same configuration history and configuration),
;   gives a related owner.  So every served-read theorem stated under the
;   relation (books/served-span.lisp fn-scar-ocfg-read-span-is-reference-
;   under-ocl-relation among them) holds of the read at the reader view,
;   and that view is the replay of at most the records the Store held at
;   the capture (fn-ocl-view-historyp's version bound).
;
;   KEYSTONE fn-olr-take-never-joins-the-batch-in-flight: the log's take
;   (books/store-log-route.lisp fn-olr-take, which host/native/io.lisp
;   fnn-log-take calls for every member a START or START-NEXT drains) never
;   changes the kernel's batch in flight; a taken record joins the open
;   batch, which is appended only after the batch in flight is fenced
;   (fn-ocp-sync-only-when-none-in-flight).  So a POST a reader queued
;   during a barrier never joins the batch in flight.
(in-package "ACL2")
(include-book "owner-commit-pipeline")
(include-book "config-owner-live-complete")
(include-book "store-log-route")

; -----------------------------------------------------------------------------
; The capture discipline.  VIEWS is nil (no capture: readers read the
; working view), (D) (the batch in flight's reader view), or (D N) (and the
; next batch's, captured before its START-NEXT).  CURRENT is the owner's
; working view at the event.

(defun fn-ocv-capture (views event current)
  (declare (xargs :guard t))
  (cond ((eq event :start)
         (if (consp views) views (list current)))
        ((eq event :next)
         (if (and (consp views) (not (consp (cdr views))))
             (list (car views) current)
           views))
        ((eq event :complete)
         (if (and (consp views) (consp (cdr views)))
             (list (cadr views))
           nil))
        ;; :unnext -- the START-NEXT took nobody: no next batch.
        ((eq event :unnext)
         (if (consp views) (list (car views)) nil))
        ;; :drop -- the START took nobody, or the owner stops.
        (t nil)))

(defun fn-ocv-reader-view (views current)
  (declare (xargs :guard t))
  (if (consp views) (car views) current))

; -----------------------------------------------------------------------------
; The count model: M = (W C A B VIEWS), W the working view's record count, C
; the count of records whose batch COMPLETED, A the batch in flight's
; members, B the next batch's.  An event is (:start K), (:next J),
; (:unnext), (:complete) or (:drop).

(defun fn-ocvm-make (w c a b views) (declare (xargs :guard t)) (list w c a b views))
(defun fn-ocvm-w (m) (declare (xargs :guard t)) (nfix (if (consp m) (car m) 0)))
(defun fn-ocvm-c (m) (declare (xargs :guard t))
  (nfix (if (and (consp m) (consp (cdr m))) (cadr m) 0)))
(defun fn-ocvm-a (m) (declare (xargs :guard t))
  (nfix (if (and (consp m) (consp (cdr m)) (consp (cddr m))) (caddr m) 0)))
(defun fn-ocvm-b (m) (declare (xargs :guard t))
  (nfix (if (and (consp m) (consp (cdr m)) (consp (cddr m)) (consp (cdddr m)))
            (cadddr m) 0)))
(defun fn-ocvm-views (m) (declare (xargs :guard t))
  (if (and (consp m) (consp (cdr m)) (consp (cddr m)) (consp (cdddr m))
           (consp (cddddr m)))
      (car (cddddr m))
    nil))

(defun fn-ocvm-init () (declare (xargs :guard t)) (fn-ocvm-make 0 0 0 0 nil))

(defun fn-ocvm-arg (ev) (declare (xargs :guard t))
  (nfix (if (and (consp ev) (consp (cdr ev))) (cadr ev) 0)))

; Legal: a START only at an idle owner, a START-NEXT only behind a batch in
; flight with no next batch (fn-ocp-start-next-only-behind-a-sync), a
; COMPLETE only with a batch in flight, a drop only of a START that took
; nobody.
(defun fn-ocvm-legalp (m ev)
  (declare (xargs :guard t))
  (let ((views (fn-ocvm-views m))
        (kind (if (consp ev) (car ev) nil)))
    (cond ((eq kind :start) (not (consp views)))
          ((eq kind :next) (and (consp views) (not (consp (cdr views)))
                                (posp (fn-ocvm-a m))))
          ((eq kind :unnext) (and (consp views) (consp (cdr views))
                                  (equal (fn-ocvm-b m) 0)))
          ((eq kind :complete) (consp views))
          ((eq kind :drop) (and (consp views) (not (consp (cdr views)))
                                (equal (fn-ocvm-a m) 0)))
          (t nil))))

(defun fn-ocvm-step (m ev)
  (declare (xargs :guard t))
  (let ((w (fn-ocvm-w m)) (c (fn-ocvm-c m)) (a (fn-ocvm-a m)) (b (fn-ocvm-b m))
        (views (fn-ocvm-views m))
        (kind (if (consp ev) (car ev) nil))
        (k (fn-ocvm-arg ev)))
    (cond ((eq kind :start)
           (fn-ocvm-make (+ w k) c k b (fn-ocv-capture views :start w)))
          ((eq kind :next)
           (fn-ocvm-make (+ w k) c a k (fn-ocv-capture views :next w)))
          ((eq kind :unnext)
           (fn-ocvm-make w c a b (fn-ocv-capture views :unnext w)))
          ((eq kind :complete)
           (fn-ocvm-make w (+ c a) b 0 (fn-ocv-capture views :complete w)))
          (t (fn-ocvm-make w c a b (fn-ocv-capture views :drop w))))))

(defun fn-ocvm-inv (m)
  (declare (xargs :guard t))
  (let ((w (fn-ocvm-w m)) (c (fn-ocvm-c m)) (a (fn-ocvm-a m)) (b (fn-ocvm-b m))
        (views (fn-ocvm-views m)))
    (cond ((not (consp views)) (and (equal a 0) (equal b 0) (equal w c)))
          ((not (consp (cdr views)))
           (and (equal (car views) c) (equal b 0) (equal w (+ c a))))
          (t (and (equal (car views) c) (equal (cadr views) (+ c a))
                  (equal w (+ c a b)) (not (consp (cddr views))))))))

(defthm fn-ocvm-inv-init (fn-ocvm-inv (fn-ocvm-init)))

(local
 (defthm fn-ocvm-accessors-of-make
   (and (equal (fn-ocvm-w (fn-ocvm-make w c a b views)) (nfix w))
        (equal (fn-ocvm-c (fn-ocvm-make w c a b views)) (nfix c))
        (equal (fn-ocvm-a (fn-ocvm-make w c a b views)) (nfix a))
        (equal (fn-ocvm-b (fn-ocvm-make w c a b views)) (nfix b))
        (equal (fn-ocvm-views (fn-ocvm-make w c a b views)) views))))

(local (in-theory (disable fn-ocvm-make fn-ocvm-w fn-ocvm-c fn-ocvm-a fn-ocvm-b
                           fn-ocvm-views fn-ocvm-arg)))

(defthm fn-ocvm-step-preserves-inv
  (implies (and (fn-ocvm-inv m) (fn-ocvm-legalp m ev))
           (fn-ocvm-inv (fn-ocvm-step m ev)))
  :hints (("Goal" :cases ((equal (car ev) :start) (equal (car ev) :next)
                          (equal (car ev) :unnext) (equal (car ev) :complete)))))

(defun fn-ocvm-legal-run-p (m evs)
  (declare (xargs :guard t :measure (acl2-count evs)))
  (if (consp evs)
      (and (fn-ocvm-legalp m (car evs))
           (fn-ocvm-legal-run-p (fn-ocvm-step m (car evs)) (cdr evs)))
    t))

(defun fn-ocvm-run (m evs)
  (declare (xargs :guard t :measure (acl2-count evs)))
  (if (consp evs) (fn-ocvm-run (fn-ocvm-step m (car evs)) (cdr evs)) m))

(local (in-theory (disable fn-ocvm-step fn-ocvm-inv fn-ocvm-legalp)))

(defthm fn-ocvm-run-preserves-inv
  (implies (and (fn-ocvm-inv m) (fn-ocvm-legal-run-p m evs))
           (fn-ocvm-inv (fn-ocvm-run m evs))))

(local
 (defthm fn-ocvm-inv-gives-the-completed-prefix
   (implies (fn-ocvm-inv m)
            (and (equal (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m))
                        (fn-ocvm-c m))
                 (equal (fn-ocvm-w m)
                        (+ (fn-ocvm-c m) (fn-ocvm-a m) (fn-ocvm-b m)))))
   :hints (("Goal" :in-theory (enable fn-ocvm-inv fn-ocv-reader-view)))))

; KEYSTONE (the reader view).  Along every legal run from an idle owner the
; reader view is the view at C: the records of every COMPLETED batch and
; none of the batch in flight (A) or of the next batch (B), which the
; working view W = C + A + B already holds.
(defthm fn-ocvm-reader-view-is-the-completed-prefix
  (implies (fn-ocvm-legal-run-p (fn-ocvm-init) evs)
           (let ((m (fn-ocvm-run (fn-ocvm-init) evs)))
             (and (equal (fn-ocv-reader-view (fn-ocvm-views m) (fn-ocvm-w m))
                         (fn-ocvm-c m))
                  (equal (fn-ocvm-w m)
                         (+ (fn-ocvm-c m) (fn-ocvm-a m) (fn-ocvm-b m))))))
  :hints (("Goal" :use ((:instance fn-ocvm-run-preserves-inv (m (fn-ocvm-init)))
                        (:instance fn-ocvm-inv-gives-the-completed-prefix
                                   (m (fn-ocvm-run (fn-ocvm-init) evs))))
           :in-theory (disable fn-ocvm-run fn-ocvm-legal-run-p fn-ocvm-inv
                               fn-ocvm-run-preserves-inv
                               fn-ocvm-inv-gives-the-completed-prefix
                               fn-ocv-reader-view fn-ocvm-views fn-ocvm-w
                               fn-ocvm-c fn-ocvm-a fn-ocvm-b (fn-ocvm-init)))))

; -----------------------------------------------------------------------------
; A POST queued during a barrier never joins the batch in flight.

(defthm fn-olr-take-never-joins-the-batch-in-flight
  (and (equal (fn-lgk-inflight (cadr (fn-olr-take ks record txid count octets bmax omax unit)))
              (fn-lgk-inflight ks))
       (implies (equal (car (fn-olr-take ks record txid count octets bmax omax unit)) :taken)
                (equal (fn-lgk-batch (cadr (fn-olr-take ks record txid count octets bmax omax unit)))
                       (append (true-list-fix (fn-lgk-batch ks)) (list record)))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-olr-take fn-lgk-prepare fn-lgk-make fn-lgk-inflight
                                fn-lgk-batch fn-lgk-committed fn-lgk-last fn-lgk-frontier
                                fn-lgk-next-txid fn-lgk-acked fn-lgk-phase nth-add1
                                nth-0-cons car-cons cdr-cons nth)
                              (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The owner with another view.

(defun fn-own-with-view (o v)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) v (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)
               (fn-own-node-secret o) (fn-own-refused o)))

(defun fn-ocfg-with-view (oc v)
  (declare (xargs :guard t))
  (fn-ocfg-with-owner oc (fn-own-with-view (fn-ocfg-owner oc) v)))

; The owner a reader quantum runs on: the reader view in place of the
; working view while a capture is held, the owner itself otherwise.
(defun fn-ocfg-at-reader-view (oc views)
  (declare (xargs :guard t))
  (if (consp views)
      (fn-ocfg-with-view oc (fn-ocv-reader-view views (fn-own-view (fn-ocfg-owner oc))))
    oc))

(defthm fn-ocfg-at-reader-view-reads-the-reader-view
  (implies (consp views)
           (equal (fn-own-view (fn-ocfg-owner (fn-ocfg-at-reader-view oc views)))
                  (car views))))

(defthm fn-ocfg-with-view-keeps-the-rest
  (let ((o2 (fn-ocfg-owner (fn-ocfg-with-view oc v)))
        (o (fn-ocfg-owner oc)))
    (and (equal (fn-own-view o2) v)
         (equal (fn-own-store o2) (fn-own-store o))
         (equal (fn-own-conns o2) (fn-own-conns o))
         (equal (fn-own-queue o2) (fn-own-queue o))
         (equal (fn-ocfg-config (fn-ocfg-with-view oc v)) (fn-ocfg-config oc))
         (equal (fn-ocfg-pins (fn-ocfg-with-view oc v)) (fn-ocfg-pins oc))
         (equal (fn-ocfg-staged (fn-ocfg-with-view oc v)) (fn-ocfg-staged oc)))))

; -----------------------------------------------------------------------------
; The relation of the owner at a captured view.

(local
 (defthm fn-orv-take-of-append
   (implies (<= (nfix n) (len xs))
            (equal (fn-own-take n (append xs ys)) (fn-own-take n xs)))
   :hints (("Goal" :in-theory (enable fn-own-take)))))

(local (in-theory (disable fn-own-take)))

(defthm fn-ocl-view-historyp-of-a-view-captured-before-appends
  (implies (and (fn-ocl-view-historyp o0)
                (equal (fn-sf-records (fn-sn-files (fn-own-store o)))
                       (append (fn-sf-records (fn-sn-files (fn-own-store o0))) extra))
                (equal (fn-sn-config-history (fn-own-store o))
                       (fn-sn-config-history (fn-own-store o0))))
           (fn-ocl-view-historyp (fn-own-with-view o (fn-own-view o0))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-historyp)
                                  (fn-cst-replay-node fn-node-statep fn-ctl-visible-state)))))

(defthm fn-ocl-view-configp-of-a-view-captured-before-appends
  (implies (and (fn-ocl-view-configp oc0)
                (fn-ocl-view-historyp (fn-ocfg-owner oc0))
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                       (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                               extra))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)))
           (fn-ocl-view-configp (fn-ocfg-with-view oc (fn-own-view (fn-ocfg-owner oc0)))))
  :hints (("Goal" :in-theory (e/d (fn-ocl-view-configp fn-ocl-view-historyp)
                                  (fn-cst-replay-node fn-node-statep fn-ctl-visible-state
                                   fn-cpr-replay)))))

; Everything of the relation but its two view conjuncts reads the owner's
; Store, connections and the configuration's pins, which the view does not
; touch.
(local
 (defthm fn-orv-with-view-fields
   (let ((oc2 (fn-ocfg-with-view oc v)))
     (and (equal (fn-own-store (fn-ocfg-owner oc2)) (fn-own-store (fn-ocfg-owner oc)))
          (equal (fn-own-conns (fn-ocfg-owner oc2)) (fn-own-conns (fn-ocfg-owner oc)))
          (equal (fn-own-view (fn-ocfg-owner oc2)) v)
          (equal (fn-own-max-conns (fn-ocfg-owner oc2)) (fn-own-max-conns (fn-ocfg-owner oc)))
          (equal (fn-own-next-id (fn-ocfg-owner oc2)) (fn-own-next-id (fn-ocfg-owner oc)))
          (equal (fn-own-ledger (fn-ocfg-owner oc2)) (fn-own-ledger (fn-ocfg-owner oc)))
          (equal (fn-own-clock (fn-ocfg-owner oc2)) (fn-own-clock (fn-ocfg-owner oc)))
          (equal (fn-own-facts (fn-ocfg-owner oc2)) (fn-own-facts (fn-ocfg-owner oc)))
          (fn-own-shapep (fn-ocfg-owner oc2))
          (fn-ocfg-shapep oc2)
          (equal (fn-ocfg-config oc2) (fn-ocfg-config oc))
          (equal (fn-ocfg-pins oc2) (fn-ocfg-pins oc))
          (equal (fn-ocfg-staged oc2) (fn-ocfg-staged oc))))
   :hints (("Goal" :in-theory (enable fn-ocfg-with-owner fn-own-with-view)))))

(local (in-theory (disable fn-ocfg-with-view)))

(local
 (defthm fn-orv-conn-config-of-with-view
   (equal (fn-ocfg-conn-config (fn-ocfg-with-view oc v) id)
          (fn-ocfg-conn-config oc id))
   :hints (("Goal" :in-theory (enable fn-ocfg-conn-config)))))

(local
 (defthm fn-orv-conn-historyp-of-with-view
   (equal (fn-ocl-conn-historyp (fn-ocfg-with-view oc v) conn)
          (fn-ocl-conn-historyp oc conn))
   :hints (("Goal" :in-theory (union-theories '(fn-ocl-conn-historyp
                                                fn-orv-with-view-fields
                                                fn-orv-conn-config-of-with-view)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-orv-conns-historyp-of-with-view
   (equal (fn-ocl-conns-historyp (fn-ocfg-with-view oc v) conns)
          (fn-ocl-conns-historyp oc conns))
   :hints (("Goal" :in-theory (enable fn-ocl-conns-historyp)))))

(local
 (defthm fn-orv-config-historyp-of-with-view
   (equal (fn-ocl-config-historyp (fn-ocfg-with-view oc v))
          (fn-ocl-config-historyp oc))
   :hints (("Goal" :in-theory (union-theories '(fn-ocl-config-historyp
                                                fn-orv-with-view-fields)
                                              (theory 'minimal-theory))))))

; KEYSTONE (the read at the reader view is a read of a related owner).  The
; view of a related owner OC0, put into a related owner OC whose Store has
; only appended records to OC0's (the same configuration history and
; configuration), gives a related owner: every served-read theorem stated
; under fn-ocl-relation holds of the read a reader quantum runs during a
; barrier, over the replay of at most OC0's records.  The subject is
; fn-ocfg-with-view, which host/owner-host.lisp fn-owner-at-reader-view calls
; for every reader entry while a capture is held.
(defthm fn-ocl-relation-of-a-view-captured-before-appends
  (implies (and (fn-ocl-relation oc0)
                (fn-ocl-relation oc)
                (equal (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                       (append (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))
                               extra))
                (equal (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                       (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc0))))
                (equal (fn-ocfg-config oc) (fn-ocfg-config oc0)))
           (and (fn-ocl-relation (fn-ocfg-with-view oc (fn-own-view (fn-ocfg-owner oc0))))
                (<= (fn-own-view-version (fn-own-view (fn-ocfg-owner oc0)))
                    (len (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc0))))))))
  :hints (("Goal" :use ((:instance fn-ocl-view-historyp-of-a-view-captured-before-appends
                                   (o0 (fn-ocfg-owner oc0)) (o (fn-ocfg-owner oc)))
                        (:instance fn-ocl-view-configp-of-a-view-captured-before-appends))
           :in-theory (e/d (fn-ocl-vocabulary) ; withdrawn by config-owner-live-complete
                           (fn-ocl-view-historyp-of-a-view-captured-before-appends
                            fn-ocl-view-configp-of-a-view-captured-before-appends
                            fn-ocl-conns-historyp fn-ocl-config-historyp
                            fn-ocfg-pins-okp fn-ocfg-conns-pinnedp fn-ocfg-pins-pin-conns-only
                            fn-own-ledger-durablep fn-own-facts-okp fn-cst-relation
                            fn-ocl-unique-conn-idsp fn-own-ids-below-next-p
                            fn-cfgp fn-cfg-recordp)))))
