; host/native/build-dtn.lisp -- the DTN-only variant of host/native/build.lisp.
;
; The same image without the NNTP reader: `books/served`, `books/nntp-effects`,
; `host/reader-host.lisp` and `host/native/reader-model-host.lisp` are left
; out, and with them the `reader` and `model` verbs.  Everything the TCPCLv4
; convergence layer needs is here, and nothing the layer needs was dropped.
;
; WHY THIS EXISTS.  The DTN path does not read news, and the two reader books
; are the slowest in the closure, so a lane that needs a convergence layer on
; a contended box should not wait for them.  It is a fallback, not the
; deployment image: `tools/build_native_host.sh` still builds
; host/native/build.lisp by default, and an image built from this file must
; say so in its evidence record.
;
; What it costs: `--fn reader ...` and `--fn model ...` reach `fnn-call` for a
; `fn-reader-*` counterpart that is not in this image and fault with
; "ACL2 executable counterpart missing", which is the honest answer and not a
; silent wrong one.  Every reference to those functions in
; host/native/io.lisp is a quoted symbol resolved at call time, so the raw
; file loads unchanged.
;
; Build it with:  FN_NATIVE_BUILD=host/native/build-dtn.lisp \
;                 FN_NATIVE_IMAGE=build/fn-host-dtn sh tools/build_native_host.sh

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
(include-book "books/bp-receipt-records")
(include-book "books/bp-workflow-records")
; The TCPCLv4 convergence layer: the octet grammar and the session machine the
; native host's host/native/tcpcl.lisp drives.  books/tcpcl-session includes
; books/tcpcl-octets and books/tcpcl-records; all three are Makefile roots.
(include-book "books/tcpcl-session")

(ld "host/store-host.lisp" :ld-error-action :error)
(ld "host/store-node-host.lisp" :ld-error-action :error)
; The configuration record the core builds for a fresh store; it uses the
; octet-list helpers store-host defines above it, as run_store.py's bridge does.
(ld "host/config-host.lisp" :ld-error-action :error)
;; The external freshness anchor.  Without it the image cannot answer the
;; anchor question at all and `recover' silently omitted the field the Python
;; host prints (HANDOFF-w3-native-host.md, "the differential's four findings").
(ld "host/anchor-host.lisp" :ld-error-action :error)
(ld "host/workflow-host.lisp" :ld-error-action :error)
(ld "host/bp-receipt-journal-host.lisp" :ld-error-action :error)
; The ACL2 side of the TCPCLv4 host: every protocol value the convergence
; layer needs, so that host/native/tcpcl.lisp computes none of them.
(ld "host/tcpcl-host.lisp" :ld-error-action :error)

; The entry save-exec's :return-from-lp form calls.  Its raw definition in
; host/native/io.lisp replaces this body; this one only reports its absence.
(defttag :fn-native-host)
(defun fn-native-entry (state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "fn-native: raw entry not installed~%") (value :missing)))
(progn! (set-raw-mode t)
        (load "host/native/io.lisp")
        ; The convergence layer, over io.lisp's socket surface and nothing else.
        (load "host/native/tcpcl.lisp")
        ; The saved image is a host, not a session: no ACL2 banner on stdout,
        ; and `--noinform' below keeps SBCL's own banner off it too.  The
        ; `model' verb writes reply octets to stdout and nothing else may.
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))

:q
(save-exec "build/fn-host-dtn" "fn native host (DTN only, no NNTP reader)"
           :return-from-lp '(fn-native-entry state)
           :inert-args t
           :host-lisp-args "--noinform"
           :toplevel-args "--disable-debugger")
