; host/native/build.lisp -- ACL2 session script that saves build/fn-host.
;
; Run through tools/build_native_host.sh from the repository root, which feeds
; this file to a certified ACL2 on standard input and refuses the image when
; any error marker, an uncertified-book warning, or a missing ready marker
; appears in the log.  Every include-book below is a certification root of the
; Makefile, so the image holds exactly the certified definitions; the host
; wrappers are the same :program files tools/run_store.py and
; tools/run_reader.py ld today.  The one trust tag names the raw-Lisp adapter,
; host/native/io.lisp, and is retired before the image is saved.

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
(include-book "books/bp-receipt-records")
(include-book "books/bp-workflow-records")

(ld "host/store-host.lisp" :ld-error-action :error)
(ld "host/store-node-host.lisp" :ld-error-action :error)
; The configuration record the core builds for a fresh store; it uses the
; octet-list helpers store-host defines above it, as run_store.py's bridge does.
(ld "host/config-host.lisp" :ld-error-action :error)
(ld "host/reader-host.lisp" :ld-error-action :error)
; The differential model side, over the same fn-served-open reader-host uses.
(ld "host/native/reader-model-host.lisp" :ld-error-action :error)
(ld "host/workflow-host.lisp" :ld-error-action :error)
(ld "host/bp-receipt-journal-host.lisp" :ld-error-action :error)

; The entry save-exec's :return-from-lp form calls.  Its raw definition in
; host/native/io.lisp replaces this body; this one only reports its absence.
(defttag :fn-native-host)
(defun fn-native-entry (state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "fn-native: raw entry not installed~%") (value :missing)))
(progn! (set-raw-mode t)
        (load "host/native/io.lisp")
        ; The saved image is a host, not a session: no ACL2 banner on stdout.
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))

:q
(save-exec "build/fn-host" "fn native host"
           :return-from-lp '(fn-native-entry state)
           :inert-args t
           :toplevel-args "--disable-debugger")
