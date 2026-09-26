; Developer-only store runtime image.  It executes host/native/io.lisp's real
; fnn-main/store commands after loading the certified store dependencies, but
; deliberately omits unrelated owner, BP, TCPCL, and service modules.  It is
; evidence tooling, never an operator-selectable production host profile.
(in-package "ACL2")
; The fn-wide outcome classes and exit codes host/native/io.lisp reads (PRF-143).
(include-book "books/outcome-class")
(include-book "books/replay")
(include-book "books/store-config")
(include-book "books/identity")
(include-book "books/article-fields")
(include-book "books/frame")
(include-book "books/store-observed")
(include-book "books/store-node-resolution")
(include-book "books/store-observed-traces")
(include-book "books/store-node")
(include-book "books/node-config")
(include-book "books/nntp")
(include-book "books/served")
(include-book "books/nntp-effects")
(include-book "books/native-config")
(include-book "books/native-admin")
(include-book "books/native-config-observation")
(include-book "books/bp-receipt-records")
(include-book "books/bp-workflow-records")
(include-book "books/journal-publish")
(include-book "books/app-journal")
(include-book "books/tcpcl-session")
(include-book "books/tcpcl-spool")
(include-book "books/bp-node")
(include-book "books/bp-node-records")
(include-book "books/bp-node-machine")
(include-book "books/bp-node-machine-codec")
;; The committed-history boundary: io.lisp fnn-mark-committed and
;; fnn-check-history-marker call fn-hm-after-commit and fn-hm-open-verdict.
(include-book "books/store-history-marker")
;; D31: the history requirement and the recovery catch-up: io.lisp
;; fnn-check-history-marker, fnn-recover and fnn-command-upgrade-profile call
;; fn-hmr-open-verdict, fn-hmr-catch-up and fn-hmr-upgrade-verdict.
(include-book "books/store-history-required")
;; The store bridge's record dispatchers (host/store-host.lisp,
;; host/store-node-host.lisp) call the concrete twins of books/records-concrete.
(include-book "books/records-concrete")
;; D13 (STO-014): the duplicate-versus-conflict verdict over a store that may
;; hold tombstones.  host/owner-host.lisp and host/store-node-host.lisp call
;; fn-rcl-existing-action (list payload) and fn-rclb-existing-action (buffer).
(include-book "books/store-reclaim-buffer")
(ld "host/store-host.lisp" :ld-error-action :error)
(ld "host/native-admin-host.lisp" :ld-error-action :error)
(ld "host/store-node-host.lisp" :ld-error-action :error)
(ld "host/config-host.lisp" :ld-error-action :error)
(defttag :fn-native-store-test)
(defun fn-native-entry (state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "fn-native-store-test: raw entry not installed~%")
          (value :missing)))
(progn! (set-raw-mode t)
        (load "host/native/crypto.lisp")
        (fnn-crypto-initialize)
        (load "host/native/io.lisp")
        (defun fn-native-entry (st)
          (declare (ignore st))
          (fnn-crypto-startup)
          (fnn-main)
          (values nil :exited *the-live-state*))
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))
:q
(save-exec "build/fn-host-store-test" "fn native store test host"
           :return-from-lp '(fn-native-entry state)
           :inert-args t :host-lisp-args "--noinform"
           :toplevel-args "--disable-debugger")
