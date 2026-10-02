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
       ;; guard before the raw body: a dispatcher (io.lisp, THE TRAP).
       (let ((*fnn-in-core* t))
       (ld-fn (list (cons 'standard-oi *standard-oi*)
                    (cons 'standard-co *standard-co*)
                    (cons 'proofs-co *standard-co*)
                    (cons 'ld-prompt t)
                    (cons 'ld-verbose nil)
                    (cons 'ld-pre-eval-print nil)
                    (cons 'ld-post-eval-print :command-conventions)
                    (cons 'ld-error-action :continue))
              state
              nil)))
     (finish-output *standard-output*)
     +fnn-exit-ok+)
    ((and (string= command "raw-traps") (null args))
     ;; D40 (io.lisp, THE TRAP): for every raw-dispatched entry, a host call
     ;; of its target outside the dispatcher faults however it is spelled
     ;; (the literal symbol, a symbol interned from its name, its function
     ;; binding), the trap passes inside the dispatcher's extent (the
     ;; captured function then refuses the empty argument list itself), and
     ;; the dispatcher applies the captured object.  One line per entry.
     (flet ((outcome (thunk)
              (handler-case (progn (funcall thunk) "returned")
                (fnn-raw-dispatch-trap () "trapped")
                (serious-condition () "passed"))))
       (let ((bad 0) (names nil))
         (maphash (lambda (name raw) (declare (ignore raw)) (push name names))
                  *fnn-raw-dispatch*)
         (dolist (name (sort names #'string< :key #'symbol-name))
           (let* ((raw (gethash name *fnn-raw-dispatch*))
                  (direct (outcome (lambda () (funcall raw))))
                  (interned (outcome (lambda ()
                                       (funcall (intern (symbol-name raw)
                                                        (symbol-package raw))))))
                  (binding (outcome (lambda () (funcall (symbol-function raw)))))
                  (inside (outcome (lambda () (let ((*fnn-in-core* t)) (funcall raw)))))
                  (dispatch (if (eq (fnn-dispatch-function name)
                                    (gethash raw *fnn-raw-captured*))
                                "captured" "other")))
             (unless (and (equal direct "trapped") (equal interned "trapped")
                          (equal binding "trapped") (equal inside "passed")
                          (or *fnn-dispatch-counterpart* (equal dispatch "captured")))
               (incf bad))
             (fnn-out "FN_RAW_TRAP ~(~a~) direct=~a interned=~a binding=~a inside=~a dispatch=~a"
                      name direct interned binding inside dispatch)))
         (fnn-out "FN_RAW_TRAPS ~d intact=~d bad=~d"
                  (length names) (fnn-raw-dispatch-traps-intact) bad)
         (if (zerop bad) +fnn-exit-ok+ +fnn-exit-fault+))))
    (t
     (fnn-out "usage: fn acl2 session   (developer image: ACL2's loop over this image's world, forms on standard input)")
     (fnn-out "       fn acl2 raw-traps (developer image: each raw-dispatched entry's trap, D40)")
     (if (string= command "help") +fnn-exit-ok+ +fnn-exit-usage+))))

(fnn-register-developer-verb "acl2" #'fnn-command-acl2)
