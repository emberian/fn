;; The principal ledger in the served core (layer D, D7 3/n; design:
;; fn2/docs/d-machines-nntp.md section 13.4): the ledger registered as a
;; core child, the defcosts of the operations the machines call, and their
;; core wrappers (fn2-account-events, materialized after the core instance
;; in assembly-callbacks-d.lisp). The ledger itself is the library
;; accounts.lisp.
(in-package "ACL2")
(include-book "accounts")
(include-book "machines-a")
(fn2-book-layer :d)

;; Every wrapper checks the ledger's shape (the core's wfp covers its
;; columns, not its dimension arrays) and answers :state when it fails;
;; callers stop.
(defcorechild fn2-core-accounts fn2-accounts
 :init (fn2-accounts-init profile fn2-accounts) :profilep (fn2-accounts-profilep profile)
 :why "Principal ledger rows: limits, reserves, holdings and charges per principal slot and the system row (ROUND2 B.2).")

;; Charge dimensions as constants, for the checked arm language.
(defconst *fn2-account-charge-rx* (fn2-account-charge-dim :rx-octets))
(defconst *fn2-account-charge-tx* (fn2-account-charge-dim :tx-octets))
(defconst *fn2-account-charge-requests* (fn2-account-charge-dim :requests))
(defconst *fn2-account-charge-run-steps* (fn2-account-charge-dim :run-steps))
(defconst *fn2-account-charge-run-bytes* (fn2-account-charge-dim :run-bytes))

(defcost fn2-account-book-admitted :tables (fn2-core-accounts)
  :doc "Book one connection row on a principal unless the admission was into the partition's reserve row (an attribution of a resource the admission acquired: no D0 effect).")
(defcost fn2-account-book :answers t :tables (fn2-core-accounts)
  :doc "Book one :connection-row on a principal (the listener at Accept issue, A's S1; an attribution of the row the Accept reserves: no D0 effect).")
(defcost fn2-account-unbook-ref :answers t :tables (fn2-core-accounts)
  :doc "Release the booking a row's account-ref names, if any; charges stay.")
(defcost fn2-account-request-core :answers (:ok :queued :limit :shared :refused :bounds :state)
  :tables (fn2-core-accounts) :effects ((:acquire (:principal-reservation)))
  :doc "D7 4/n-a: a principal's request; :queued while its FIFO is non-empty (no barging), :refused for a request limit of 0.")
(defcost fn2-account-request-release :answers t :tables (fn2-core-accounts) :effects ((:release (:principal-reservation)))
  :doc "D7 4/n-a: a request's reservation released at its reply's last octet.")
(defcost fn2-account-request-park :answers (:ok :bounds) :tables (fn2-core-accounts fn2-core-machines)
  :own-writes (wait-reason ready-prev ready-next)
  :doc "D7 4/n-a: park a refused request on its principal's FIFO in the same transition.")
;; The :principal-reservation wait kind is D's (MACHINE-FORM 6.10): a refused
;; request parks on its principal's FIFO; the ledger's pair grants it.
(defwait :principal-reservation :ready fn2-account-grant-ready-p :grant fn2-account-grant-one
  :park fn2-account-request-park
  :doc "A request parked on its principal's FIFO, granted (acquired, dequeued) once its reservation fits.")
(defcost fn2-account-charge-core :tables (fn2-core-accounts)
  :doc "Add a completion count to a principal's charge dimension (monotone).")

(defun fn2-account-frame-child-events (op args children)
  (declare (xargs :verify-guards nil))
  (if (atom children) nil
    (cons `(defthm ,(fn2-columns-sym op (concatenate 'string "-FRAME-" (symbol-name (caar children))))
             (equal (,(caar children) (mv-nth 1 (,op ,@args))) (,(caar children) fn2-core))
             :hints (("Goal" :in-theory (enable ,op))))
          (fn2-account-frame-child-events op args (cdr children)))))
(defun fn2-account-frame-events (ops children)
  (declare (xargs :verify-guards nil))
  (if (atom ops) nil
    (append (fn2-account-frame-child-events (caar ops) (cadar ops) children)
            (fn2-account-frame-events (cdr ops) children))))

(defmacro fn2-account-events ()
 '(progn
(defmacro fn2-account-with-ledger (form)
  `(stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
     (code fn2-accounts)
     (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
         ,form
       (mv :state fn2-accounts))
     (mv code fn2-core)))
(defun fn2-account-book (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger (fn2-account-acquire p (fn2-account-holding :connection-row) 1 fn2-accounts)))
(fn2-core-preserves fn2-account-book (p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-account-unbook (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger (fn2-account-release p (fn2-account-holding :connection-row) 1 fn2-accounts)))
(fn2-core-preserves fn2-account-unbook (p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; The connection's two uses, so no arm branches on the core: a row
;; admitted into the partition's reserve row (REFUSED 1) books nothing and
;; answers :refused; a row whose account-ref is *fn2-none* holds no
;; booking and releases nothing.
(defun fn2-account-book-admitted (refused p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (equal refused 1) (mv :refused fn2-core) (fn2-account-book p fn2-core)))
(fn2-core-preserves fn2-account-book-admitted (refused p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-account-unbook-ref (ref fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (equal ref *fn2-none*) (mv :ok fn2-core) (fn2-account-unbook ref fn2-core)))
(fn2-core-preserves fn2-account-unbook-ref (ref fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-account-charge-core (p k a fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger (fn2-account-charge p k a fn2-accounts)))
(fn2-core-preserves fn2-account-charge-core (p k a fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Seam S2 (layer doc 13.6): the scheduler charges each principal run's
;; steps and bytes to its principal (the system row for service runs).
(defun fn2-account-charge-run (principal bytes steps fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (code fn2-core)
    (fn2-account-charge-core principal *fn2-account-charge-run-steps* steps fn2-core)
    (if (eq code :ok)
        (fn2-account-charge-core principal *fn2-account-charge-run-bytes* bytes fn2-core)
      (mv code fn2-core))))
(fn2-core-preserves fn2-account-charge-run (principal bytes steps fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; D7 4/n-a (layer doc 13.8): a principal's request, and its release.
(defun fn2-account-request-core (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger (fn2-account-request p fn2-accounts)))
(fn2-core-preserves fn2-account-request-core (p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-account-request-release (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger (fn2-account-release p *fn2-account-request-dim* 1 fn2-accounts)))
(fn2-core-preserves fn2-account-request-release (p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; The FIFO's ends and the grant cursor, read and written through the core
;; (the parks and the grant, fn2-account-request-events, need the directory
;; too, so they are materialized after the machine access events).
(defun fn2-account-core-ends (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (ok head tail)
    (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)
             (natp p) (< p (fn2-accounts-rows fn2-accounts)))
        (mv t (fn2-accounts-wait-head p fn2-accounts) (fn2-accounts-wait-tail p fn2-accounts))
      (mv nil *fn2-none* *fn2-none*))
    (mv ok head tail)))
(defun fn2-account-core-set-ends (p head tail fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (fn2-accounts)
    (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)
             (natp p) (< p (fn2-accounts-rows fn2-accounts)) (unsigned-byte-p 32 head) (unsigned-byte-p 32 tail))
        (let ((fn2-accounts (fn2-accounts-set-wait-head p head fn2-accounts)))
          (fn2-accounts-set-wait-tail p tail fn2-accounts))
      fn2-accounts)
    fn2-core))
(fn2-core-preserves fn2-account-core-set-ends (p head tail fn2-core) :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Whether P's FIFO head is H and its request fits (the bounded wait's
;; premise, D7 4/n-a).
(defun fn2-account-core-headed-fits (p h fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts)
             (natp p) (< p (fn2-accounts-rows fn2-accounts))
             (not (equal h *fn2-none*)) (equal (fn2-accounts-wait-head p fn2-accounts) h)
             (fn2-account-fits p *fn2-account-request-dim* 1 fn2-accounts))
    v))
;; The grant's choice (*fn2-none* when no head fits), and a grant: the
;; reservation acquired for P and the cursor moved past P, in the ledger.
(defun fn2-account-core-grant-next (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (p) (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
            (fn2-account-grant-next fn2-accounts) *fn2-none*)
    p))
(defun fn2-account-core-grant (p fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (fn2-account-with-ledger
   (mv-let (code fn2-accounts) (fn2-account-acquire p *fn2-account-request-dim* 1 fn2-accounts)
     (let ((rows (fn2-accounts-rows fn2-accounts)))
       (if (and (eq code :ok) (natp p) (< p rows) (unsigned-byte-p 32 (+ 1 p)))
           (let ((fn2-accounts (fn2-accounts-set-grant-at (- rows 1) (if (< (+ 1 p) rows) (+ 1 p) 0) fn2-accounts)))
             (mv :ok fn2-accounts))
         (mv (if (eq code :ok) :bounds code) fn2-accounts))))))
(fn2-core-preserves fn2-account-core-grant (p fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Readers for the checkers and tests (never called by a machine).
(defun fn2-account-core-hold (p d fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
            (fn2-account-hold p d fn2-accounts) 0)
    v))
(defun fn2-account-core-charged (p k fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
            (fn2-account-charged p k fn2-accounts) 0)
    v))
(defun fn2-account-core-limit (p d fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
            (fn2-account-limit p d fn2-accounts) 0)
    v))
(defun fn2-account-core-reserve (p d fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (if (and (fn2-accountsp fn2-accounts) (fn2-accounts-wfp fn2-accounts) (fn2-accounts-shapep fn2-accounts))
            (fn2-account-reserve p d fn2-accounts) 0)
    v))
(defun fn2-account-core-rows (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (fn2-accounts-rows fn2-accounts) v))
(defun fn2-account-core-conservedp (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-accounts (fn2-core-accounts fn2-core)))
    (v) (fn2-accounts-conservedp fn2-accounts) v))
;; Frames: a ledger operation changes only the ledger child, so every other
;; child of the core reads the same after it (one lemma per child and
;; operation, generated over the registry).
(make-event
 (value (cons 'progn (fn2-account-frame-events
                      '((fn2-account-book (p fn2-core)) (fn2-account-unbook (p fn2-core))
                        (fn2-account-book-admitted (refused p fn2-core)) (fn2-account-unbook-ref (ref fn2-core))
                        (fn2-account-charge-core (p k a fn2-core))
                        (fn2-account-charge-run (principal bytes steps fn2-core))
                        (fn2-account-request-core (p fn2-core)) (fn2-account-request-release (p fn2-core))
                        (fn2-account-core-grant (p fn2-core)))
                      (remove-assoc-eq 'fn2-core-accounts *fn2-core-children*)))))
(in-theory (disable fn2-account-book fn2-account-unbook fn2-account-book-admitted fn2-account-unbook-ref
                    fn2-account-charge-core fn2-account-charge-run fn2-account-request-core
                    fn2-account-request-release fn2-account-core-ends fn2-account-core-set-ends
                    fn2-account-core-grant-next fn2-account-core-grant fn2-account-core-headed-fits))))

;; The request FIFO over the directory's links, and the ledger's grant
;; source attached to the pair its defwait constrains (machines.lisp: the
;; access section declares it); materialized after fn2-machine-access-events
;; (assembly-access).
(defmacro fn2-account-request-events ()
 '(progn
;; Park ID on P's request FIFO in the transition its request was refused
;; (:queued, :limit or :shared): its wait reason :principal-reservation, its
;; links appended at the tail. :bounds for an id or principal outside the
;; core; a row already parked there is left as it is.
(defun fn2-account-request-park-on (p id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (b* (((unless (and (unsigned-byte-p 32 id) (not (equal id *fn2-none*)) (fn2-machine-idp id fn2-core)
                     (eq (fn2-machine-wait-reason-read-code id fn2-core) :ok)))
        (mv :bounds fn2-core))
       ((when (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-principal-reservation*)) (mv :ok fn2-core))
       ((mv ok head tail) (fn2-account-core-ends p fn2-core))
       ((unless (and ok (unsigned-byte-p 32 head) (unsigned-byte-p 32 tail)
                     (or (equal tail *fn2-none*) (fn2-machine-idp tail fn2-core))))
        (mv :bounds fn2-core))
       (fn2-core (fn2-machine-put id (wait-reason *fn2-wait-principal-reservation*) (ready-prev tail)
                                  (ready-next *fn2-none*)))
       (fn2-core (if (equal tail *fn2-none*) fn2-core (fn2-machine-write-ready-next tail id fn2-core))))
    (let ((fn2-core (fn2-account-core-set-ends p (if (equal tail *fn2-none*) id head) id fn2-core)))
      (mv :ok fn2-core))))
(fn2-core-preserves fn2-account-request-park-on (p id fn2-core) :position 1 :rows nil)
;; The park the arm language's (:park :principal-reservation) calls: on the
;; FIFO of the row's own principal.
(defun fn2-account-request-park (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (not (eq (fn2-machine-principal-slot-read-code id fn2-core) :ok)) (mv :bounds fn2-core)
    (fn2-account-request-park-on (fn2-machine-principal-slot id fn2-core) id fn2-core)))
(fn2-core-preserves fn2-account-request-park (id fn2-core) :position 1 :rows nil)
;; The source: ready when some principal's FIFO head would be granted; the
;; grant acquires its reservation, moves the cursor past its principal,
;; dequeues it and clears its wait, in one transition, and returns it. A
;; head whose links or acquisition fail stops the core (the ledger and the
;; FIFO disagree: an invariant broken), still answering the head, so the
;; source's liveness is by construction.
(defun fn2-account-grant-head (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (let ((p (fn2-account-core-grant-next fn2-core)))
    (if (equal p *fn2-none*) (mv p *fn2-none*)
      (mv-let (ok head tail) (fn2-account-core-ends p fn2-core)
        (declare (ignore tail))
        (mv p (if ok head *fn2-none*))))))
(defun fn2-account-grant-ready (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (p id) (fn2-account-grant-head fn2-core)
    (declare (ignore p))
    (not (equal id *fn2-none*))))
(defun fn2-account-grant-take (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (p id) (fn2-account-grant-head fn2-core)
    (if (equal id *fn2-none*) (mv *fn2-none* fn2-core)
      (b* (((mv & & tail) (fn2-account-core-ends p fn2-core))
           ((unless (and (fn2-machine-idp id fn2-core) (eq (fn2-machine-ready-next-read-code id fn2-core) :ok)
                         (eq (fn2-machine-wait-reason-read-code id fn2-core) :ok)
                         (equal (fn2-machine-wait-reason id fn2-core) *fn2-wait-principal-reservation*)))
            (let ((fn2-core (fn2-machine-refuse-write fn2-core))) (mv id fn2-core)))
           (next (fn2-machine-ready-next id fn2-core))
           ((unless (and (unsigned-byte-p 32 next) (unsigned-byte-p 32 tail)
                         (or (equal next *fn2-none*) (fn2-machine-idp next fn2-core))))
            (let ((fn2-core (fn2-machine-refuse-write fn2-core))) (mv id fn2-core)))
           ((mv gcode fn2-core) (fn2-account-core-grant p fn2-core))
           ((unless (eq gcode :ok)) (let ((fn2-core (fn2-machine-refuse-write fn2-core))) (mv id fn2-core)))
           (fn2-core (fn2-account-core-set-ends p next (if (equal next *fn2-none*) *fn2-none* tail) fn2-core))
           (fn2-core (if (equal next *fn2-none*) fn2-core (fn2-machine-write-ready-prev next *fn2-none* fn2-core))))
        (let ((fn2-core (fn2-machine-put id (wait-reason *fn2-wait-none*) (ready-prev *fn2-none*) (ready-next *fn2-none*))))
          (mv id fn2-core))))))
(fn2-core-preserves fn2-account-grant-take (fn2-core) :position 1 :rows nil)
(defthm fn2-account-grant-take-live
  (implies (fn2-account-grant-ready fn2-core)
           (not (equal (mv-nth 0 (fn2-account-grant-take fn2-core)) *fn2-none*)))
  :hints (("Goal" :in-theory (enable fn2-account-grant-take fn2-account-grant-head fn2-account-grant-ready))))
(defattach (fn2-account-grant-ready-p fn2-account-grant-ready) (fn2-account-grant-one fn2-account-grant-take)
  :hints (("Goal" :use ((:instance fn2-account-grant-take-live)))))
(in-theory (disable fn2-account-request-park-on fn2-account-request-park fn2-account-grant-head fn2-account-grant-ready fn2-account-grant-take))
))
