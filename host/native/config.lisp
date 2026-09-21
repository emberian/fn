;;; Native `config PROFILE-PATH` diagnostic verb.
;;;
;;; This file deliberately has no TOML parser, defaults, or field checks.  It
;;; reads one bounded byte vector and calls the ACL2 wrapper whose subject is
;;; `fn-native-config-load`.  host/native/build.lisp should load it after
;;; io.lisp; until that integration lands, the wrapper and ACL2 test book are
;;; directly runnable and this verb is not advertised by the saved image.

(in-package "ACL2")

(defun fnn-command-config-profile (path)
  (let* ((bound (fnn-core-state 'fn-native-config-host-max-octets))
         (octets (fnn-read-regular-bounded path bound))
         (answer (fnn-core-state 'fn-native-config-host-load
                                 (fnn-octet-list octets))))
    (cond ((equal (car answer) :accepted)
           (fnn-out "accepted config")
           +fnn-exit-ok+)
          ((equal (car answer) :refused)
           (fnn-err "refused config: ~a" (car (cdr answer)))
           +fnn-exit-refused+)
          (t (fnn-fault "native configuration core returned an invalid result")))))

(fnn-register-verb "config"
                   (lambda (command rest)
                     (if (and (string= command "check")
                              (consp rest) (null (cdr rest)))
                         (fnn-command-config-profile (car rest))
                       (error 'fnn-usage-error
                              :message "config check PROFILE-PATH"))))
