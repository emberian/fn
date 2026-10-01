;;; PARKED at stage 0 (2026-10-01; planning/design-store-representation-2026-10-01.md
;;; section 4, D43, MODE 2026-10-01 section 2b): the POST captured-identity
;;; precheck runtime of host/native/owner.lisp (Codex, e3f6720ef and after),
;;; moved here unchanged from e9a2a0ba9^ so the code stays in the tree.  No
;;; build loads this file and no loaded host line calls these functions: the
;;; precheck's books (books/post-identity-captured* over the reverted
;;; acceptance binding, D43) are outside every image world, and
;;; fn-owner-pic-begin/-next/-confirm/-retire have no host definition.  The
;;; precheck returns with D43's relay-v1 subject binding as typed words and a
;;; certified fn-pic-run-arena closing theorem (stage-0 unwired item 4); then
;;; this file is loaded again (or merged back into owner.lisp), the runtime is
;;; installed at startup with a real issuer and the precheck replaces the
;;; buffer check in fnn-owner-attempt.

(in-package "ACL2")

(defstruct (fnn-owner-pic-runtime (:constructor %make-fnn-owner-pic-runtime))
  token input-copy mio arena octets pool digest quantum begin next confirm retire)

(defun fnn-owner-pic-runtime-make (token input-copy mio arena octets pool digest quantum)
  (%make-fnn-owner-pic-runtime
   :token token :input-copy input-copy :mio mio :arena arena :octets octets
   :pool pool :digest digest :quantum quantum
   :begin (fnn-fixed-raw-callback 'fn-owner-pic-begin)
   :next (fnn-fixed-raw-callback 'fn-owner-pic-next)
   :confirm (fnn-fixed-raw-callback 'fn-owner-pic-confirm)
   :retire (fnn-fixed-raw-callback 'fn-owner-pic-retire)))

(defun fnn-owner-pic-runtime-install-locked
    (service input-copy mio arena octets pool digest quantum)
  "Startup-only subject. Never called by the attempt or from parser state."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (when (fnn-owner-service-captured-runtime service)
      (fnn-fixed-callback-fail 'fn-owner-pic-runtime-issue :already-retained nil))
    (multiple-value-bind (word token)
        (fnn-core-mv 'fn-owner-pic-runtime-issue
          (fn-owner-pic-runtime-issue pool *the-live-state*))
      (unless (eq word :admitted)
        (return-from fnn-owner-pic-runtime-install-locked word))
      ;; Retain issuance before the allocating holder constructor can escape.
      ;; An ambiguous constructor failure leaves TOKEN held, never refunded.
      (setf (fnn-owner-service-captured-runtime service) token)
      (setf (fnn-owner-service-captured-runtime service)
            (fnn-owner-pic-runtime-make token input-copy mio arena octets
                                        pool digest quantum))
      word)))

(defun fnn-owner-pic-call-locked (runtime callback fuel)
  "One core-selected bounded call; transport its word and retained effects."
  (multiple-value-bind (erp word left mio pool digest state)
      (fnn-core-mv 'fn-owner-pic-next
        (funcall callback fuel
          (fnn-owner-pic-runtime-input-copy runtime)
          (fnn-owner-pic-runtime-mio runtime)
          (fnn-owner-pic-runtime-arena runtime)
          (fnn-owner-pic-runtime-octets runtime)
          (fnn-owner-pic-runtime-pool runtime)
          (fnn-owner-pic-runtime-digest runtime) *the-live-state*))
    (declare (ignore state))
    ;; Preserve all actual returned mutable objects before an error can escape.
    (setf (fnn-owner-pic-runtime-mio runtime) mio
          (fnn-owner-pic-runtime-pool runtime) pool
          (fnn-owner-pic-runtime-digest runtime) digest)
    (when erp (fnn-fixed-callback-fail 'fn-owner-pic-next :captured-step-error erp))
    (values word left)))

(defun fnn-owner-captured-precheck-locked (service)
  "Between post precheck and frontier: actual source->step->confirm->retire."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((runtime (fnn-owner-service-captured-runtime service)))
      (unless runtime
        ;; Actual authority is the core readout, even when installation is
        ;; absent. No buffer fill, legacy comparator or default constructor.
        (multiple-value-bind (word ignored)
            (fnn-core-mv 'fn-owner-pic-demand
              (fn-owner-pic-demand (fnn-live-page-read-pool) *the-live-state*))
          (declare (ignore ignored))
          (return-from fnn-owner-captured-precheck-locked word)))
      (unless (fnn-owner-pic-runtime-p runtime)
        (fnn-fixed-callback-fail 'fn-owner-pic-runtime-issue :construction-retained runtime))
      (multiple-value-bind (word left)
          (fnn-owner-pic-call-locked runtime (fnn-owner-pic-runtime-next runtime)
                                     (fnn-owner-pic-runtime-quantum runtime))
        (case word
          (:confirmation-required
           (multiple-value-bind (confirmation remaining)
               (fnn-owner-pic-call-locked runtime
                 (fnn-owner-pic-runtime-confirm runtime) left)
             (if (eq confirmation :confirmed)
                 ;; The SAME remaining quantum crosses confirmation and
                 ;; retirement; there is no independent callback allowance.
                 (fnn-owner-pic-call-locked runtime
                   (fnn-owner-pic-runtime-retire runtime) remaining)
               (values confirmation remaining))))
          (otherwise (values word left)))))))

