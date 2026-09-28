; tools/extract/post-ref.lisp -- the SBCL reference for the POST sessions.
; The image's `--fn model' serves read-only, so the POST transcripts are run
; here, in ACL2 on SBCL, through the same functions and the same host loop as
; tools/extract/served-main.scm's `post' verb: posting allowed, one fixed
; clock observation, reset, one fn-reader-chunk per chunk, a refused outcome
; after a submission, stop at close.  Test harness only.
(in-package "ACL2")
(program)
(set-state-ok t)

(defun xt-post-loop (chunks acc fn-arena state)
  (declare (xargs :stobjs (fn-arena state)))
  (if (endp chunks)
      (mv acc fn-arena state)
    (mv-let (erp v state) (fn-reader-chunk (car chunks) fn-arena state)
      (declare (ignore erp v))
      (let ((acc (revappend (f-get-global 'fn-reader-output state) acc)))
        (mv-let (acc state)
          (if (f-get-global 'fn-reader-submit-octets state)
              (mv-let (erp v state) (fn-reader-outcome :refused state)
                (declare (ignore erp v))
                (mv (revappend (f-get-global 'fn-reader-output state) acc) state))
            (mv acc state))
          (if (f-get-global 'fn-reader-closep state)
              (mv acc fn-arena state)
            (xt-post-loop (cdr chunks) acc fn-arena state)))))))

(defun xt-post-session (chunks fn-arena state)
  (declare (xargs :stobjs (fn-arena state)))
  (mv-let (erp v state) (fn-reader-set-posting t state)
    (declare (ignore erp v))
    (mv-let (erp v fn-arena state) (fn-reader-use-seed fn-arena state)
      (declare (ignore erp v))
      (mv-let (erp v state) (fn-reader-observe-clock 123456 843000000000 1000 state)
        (declare (ignore erp v))
        (mv-let (erp v state) (fn-reader-reset state)
          (declare (ignore erp v))
          (mv-let (acc fn-arena state)
            (xt-post-loop chunks (reverse (f-get-global 'fn-reader-output state)) fn-arena state)
            (mv (reverse acc) fn-arena state)))))))

(defun xt-write-bytes (octets ch state)
  (if (endp octets) state
    (let ((state (write-byte$ (car octets) ch state)))
      (xt-write-bytes (cdr octets) ch state))))

(defun xt-write-octets (path octets state)
  (mv-let (ch state) (open-output-channel path :byte state)
    (let ((state (xt-write-bytes octets ch state)))
      (close-output-channel ch state))))

