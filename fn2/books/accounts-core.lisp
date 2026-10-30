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
(defcost fn2-account-book :tables (fn2-core-accounts)
  :doc "Book one :connection-row on a principal (the listener at Accept issue, A's S1; an attribution of the row the Accept reserves: no D0 effect).")
(defcost fn2-account-unbook-ref :tables (fn2-core-accounts)
  :doc "Release the booking a row's account-ref names, if any; charges stay.")
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
;; Seam S5: the ledger's grant source for the timer/grant service. No row
;; parks on a principal's request FIFO before D7 4/n (the request bundle),
;; so there is nothing to grant yet; 4/n gives these their bodies.
(defun fn2-account-grant-ready-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)) (ignore fn2-core))
  nil)
(defun fn2-account-grant-one (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv *fn2-none* fn2-core))
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
                        (fn2-account-charge-run (principal bytes steps fn2-core)))
                      (remove-assoc-eq 'fn2-core-accounts *fn2-core-children*)))))
(in-theory (disable fn2-account-book fn2-account-unbook fn2-account-book-admitted fn2-account-unbook-ref
                    fn2-account-charge-core fn2-account-charge-run fn2-account-grant-ready-p
                    fn2-account-grant-one))))
