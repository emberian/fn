; The model side of the native host's served differential.
;
; tests/test_served_differential.py types one expression at the ACL2 prompt to
; obtain what `fn-served-run' replies to a chunk list; the native host has no
; prompt, so this wrapper is that expression.  It performs the same
; `fn-served-open' the reader's own reset performs -- the same archive, the
; same line and body limits, the same posting configuration and the same clock
; observation, read from the same globals -- and then one `fn-served-run' over
; the whole chunk list.  Model and socket therefore differ in exactly one
; thing, how the input was cut, which is what
; `fn-served-run-is-the-concatenated-step' says is invisible.
;
; Nothing here decides anything: the reply framing is `fn-served-reply-octets'
; (books/served.lisp), as it is on the served path itself.
(in-package "ACL2")
; `fn-reader-post-config' and the reader globals this wrapper reads are
; host/reader-host.lisp's, and `fn-served-open' / `fn-served-run' come
; with it from books/served.  `ld' it here so the differential wrapper is
; loadable on its own and host/native/build.lisp's order is not a decision.
(ld "../reader-host.lisp" :ld-error-action :error)

(defun fn-reader-model-octets (chunks state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((archive (if (boundp-global 'fn-reader-archive state)
                      (f-get-global 'fn-reader-archive state)
                    nil))
         (config (fn-reader-post-config
                  archive
                  (and (boundp-global 'fn-reader-allow-post state)
                       (f-get-global 'fn-reader-allow-post state))))
         (clock (if (boundp-global 'fn-reader-clock state)
                    (f-get-global 'fn-reader-clock state)
                  nil))
         (opened (fn-served-open archive 510 8192 config clock clock
                                  (fn-auth-open-config)))
         (ran (fn-served-run (fn-served-result-conn opened) chunks)))
    (value (fn-served-reply-octets
            (append (fn-served-result-effects opened)
                    (fn-served-result-effects ran))))))
