;;; Dedicated account preparation pool boundary.
;;; The actual account driver already holds the owner mutex. Only acquire
;;; extent here: owner -> extent. Never acquire owner from extent.
;;; This adapter does not install an allowance or classify a core decision.
(in-package "ACL2")

(defun fnn-account-preparation-admit (job-source work-descriptor)
  "Return every core MV as fnn-call's literal result list, retaining pool/STATE.
The actual callable must be exported/qualified with its installed turn before
this adapter can activate an allocating candidate tick."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (fnn-call 'fn-owner-account-preparation-admit
              job-source work-descriptor
              (fnn-live-page-read-pool) *the-live-state*)))
