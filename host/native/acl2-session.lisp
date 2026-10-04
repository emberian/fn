; The developer image's own ACL2 session (lane python-diet-2, T5 of
; planning/python-diet-2026-09-28.md).
;
; `fn acl2 session' runs ACL2's read-eval-print loop over the world this image
; was saved with, reading forms from standard input and printing each value
; and the prompt on standard output, exactly as a plain ACL2 session with the
; books included would.  A test fixture that needs a value only ACL2 may
; compute -- a content identity (fn-store-subject-id-of-payload), a BP
; application request (fn-bpa-encode), a bundle or fragment a scripted peer
; sends, a staged store frame -- asks the image's own proved functions here,
; so no test starts a second ACL2 with the books (the retired Python host's
; bridge session, tools/run_store.py Acl2Store) and no Python computes a value
; ACL2 owns.
;
; Developer images only (fnn-register-developer-verb): a production image has
; no such verb, and the loop reads the developer's own forms, never external
; data.  The developer image's world is `full' (tools/build_native_host.sh),
; so every certified function is there to evaluate.  Guard checking stays as
; the image has it (t; fnn-main checks); invariant-risk mode is fnn-main's (t).

(defun fnn-command-acl2 (command args)
  (cond
    ((and (string= command "session") (null args))
     (let ((state *the-live-state*))
       ;; A nested LD over standard input: fn-native-entry itself runs inside
       ;; the one-form LD that :return-from-lp starts, with its prompt and
       ;; printing switched off; this loop restores both for its own reads.
       ;; ACL2's loop evaluates through *1* counterparts, which check each
       ;; guard before the raw body, so it runs in a dispatcher extent
       ;; (host/native/raw-trap.lisp; a developer-sealed image only).
       (fnn-raw-session-extent
        (lambda ()
          (ld-fn (list (cons 'standard-oi *standard-oi*)
                       (cons 'standard-co *standard-co*)
                       (cons 'proofs-co *standard-co*)
                       (cons 'ld-prompt t)
                       (cons 'ld-verbose nil)
                       (cons 'ld-pre-eval-print nil)
                       (cons 'ld-post-eval-print :command-conventions)
                       (cons 'ld-error-action :continue))
                 state
                 nil))))
     (finish-output *standard-output*)
     +fnn-exit-ok+)
    ((and (string= command "raw-traps") (null args))
     ;; D40 (host/native/raw-trap.lisp): for every raw-dispatched entry, a
     ;; host call of its target outside a dispatcher extent faults however
     ;; it is spelled -- the literal symbol, a symbol interned from its name,
     ;; its function binding, under a binding of a same-named slot symbol,
     ;; from a thread started inside an extent -- and the dispatcher applies
     ;; the captured object.  The trap tests the extent before it calls, so
     ;; each probe passes the entry's arity in NILs and never runs the entry.
     ;; One line per entry, then the mechanism's own probe and the summary.
     (flet ((outcome (thunk)
              (handler-case (progn (funcall thunk) "returned")
                (fnn-raw-dispatch-trap () "trapped")
                (serious-condition () "failed"))))
       (let ((bad 0) (names (fnn-raw-dispatch-names)))
         (dolist (name names)
           (let* ((raw (fnn-raw-dispatch-target name))
                  (args (make-list (max 0 (fnn-raw-dispatch-arity name))))
                  (direct (outcome (lambda () (apply raw args))))
                  (interned (outcome (lambda ()
                                       (apply (intern (symbol-name raw) (symbol-package raw))
                                              args))))
                  (binding (outcome (lambda () (apply (symbol-function raw) args))))
                  (forged (outcome (lambda ()
                                     (progv (list (make-symbol "FNN-RAW-EXTENT")) (list t)
                                       (apply raw args)))))
                  (dispatch (if (fnn-raw-dispatch-captured-p name) "captured" "other")))
             (unless (and (equal direct "trapped") (equal interned "trapped")
                          (equal binding "trapped") (equal forged "trapped")
                          (or *fnn-dispatch-counterpart* (equal dispatch "captured")))
               (incf bad))
             (fnn-out "FN_RAW_TRAP ~(~a~) direct=~a interned=~a binding=~a forged=~a dispatch=~a"
                      name direct interned binding forged dispatch)))
         (multiple-value-bind (served callback direct interned forged thread)
             (fnn-raw-trap-self-probe)
           (unless (and (equal served "served") (equal callback "served")
                        (equal direct "trapped") (equal interned "trapped")
                        (equal forged "trapped") (equal thread "trapped"))
             (incf bad))
           (fnn-out "FN_RAW_TRAP_PROBE dispatch=~a callback=~a direct=~a interned=~a forged=~a thread=~a"
                    served callback direct interned forged thread))
         (fnn-out "FN_RAW_TRAPS ~d intact=~d bad=~d"
                  (length names) (fnn-raw-dispatch-traps-intact) bad)
         (if (zerop bad) +fnn-exit-ok+ +fnn-exit-fault+))))
    (t
     (fnn-out "usage: fn acl2 session   (developer image: ACL2's loop over this image's world, forms on standard input)")
     (fnn-out "       fn acl2 raw-traps (developer image: each raw-dispatched entry's trap, D40)")
     (if (string= command "help") +fnn-exit-ok+ +fnn-exit-usage+))))

(fnn-register-developer-verb "acl2" #'fnn-command-acl2)
