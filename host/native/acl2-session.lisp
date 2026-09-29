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
       (ld-fn (list (cons 'standard-oi *standard-oi*)
                    (cons 'standard-co *standard-co*)
                    (cons 'proofs-co *standard-co*)
                    (cons 'ld-prompt t)
                    (cons 'ld-verbose nil)
                    (cons 'ld-pre-eval-print nil)
                    (cons 'ld-post-eval-print :command-conventions)
                    (cons 'ld-error-action :continue))
              state
              nil))
     (finish-output *standard-output*)
     +fnn-exit-ok+)
    (t
     (fnn-out "usage: fn acl2 session   (developer image: ACL2's loop over this image's world, forms on standard input)")
     (if (string= command "help") +fnn-exit-ok+ +fnn-exit-usage+))))

(fnn-register-developer-verb "acl2" #'fnn-command-acl2)
