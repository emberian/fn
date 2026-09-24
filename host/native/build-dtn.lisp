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
; What it costs: the default specialized image keeps io.lisp's production profile, so
; `--fn reader ...` is refused at dispatch and `--fn model ...` reaches
; `fnn-call` for a counterpart that is not in this image and faults with
; "ACL2 executable counterpart missing".  Every reference to the omitted
; reader functions in host/native/io.lisp is a quoted symbol resolved at call
; time, so the raw file loads unchanged.
;
; Build it with:  FN_NATIVE_BUILD=host/native/build-dtn.lisp \
;                 FN_NATIVE_IMAGE=build/fn-host-dtn sh tools/build_native_host.sh

(include-book "books/replay")
; Every codec seam's attachment (books/codec-attach.lisp): the books above
; the seams call the constrained encoders and decoders, and this is what makes
; them evaluate here.  It changes no theorem.
(include-book "books/codec-attach")
(include-book "books/store-config")
(include-book "books/identity")
(include-book "books/article-fields")
(include-book "books/frame")
(include-book "books/store-observed")
(include-book "books/store-node-resolution")
(include-book "books/store-observed-traces")
(include-book "books/store-node")
(include-book "books/node-config")
(include-book "books/native-admin")
(include-book "books/nntp")
(include-book "books/bp-receipt-records")
(include-book "books/bp-workflow-records")
(include-book "books/bp-release")
(include-book "books/bp-outbound")
(include-book "books/bp-ion-workflow")
(include-book "books/journal-publish")
(include-book "books/app-journal")
; The TCPCLv4 convergence layer: the octet grammar and the session machine the
; native host's host/native/tcpcl.lisp drives.  books/tcpcl-session includes
; books/tcpcl-octets and books/tcpcl-records; all three are Makefile roots.
(include-book "books/tcpcl-session")
; The spool recovery plan the raw convergence host calls before socket I/O.
(include-book "books/tcpcl-spool")
; The BPv7 bundle codec and the node: what `bp send' authors and what
; `bp receive' decodes.
(include-book "books/bp-node")
(include-book "books/bp-node-records")
(include-book "books/bp-authored-wire")
(include-book "books/bp-node-machine")
(include-book "books/bp-contact-service")
(include-book "books/bp-node-machine-codec")
; Carry the verified step guards into this image as well as the default one.
(include-book "books/bp-node-machine-guards")
(include-book "books/bp-node-fragment-guards")
(include-book "books/bp-node-receive-boundary")
(include-book "books/bp-fnbs-replay")
(include-book "books/bp-fnbs-inspect")
(include-book "books/bp-fnbs-namespace")
(include-book "books/bp-fnbs-publication")
(include-book "books/bp-clock-domain")
(include-book "books/bp-fnbs-delivery-replay")
(include-book "books/bp-fnbs-delivery-publication")
(include-book "books/bp-fnbs-family-publication")
(include-book "books/bp-fnbs-dispatch-publication")
(include-book "books/bp-fnbs-forward-publication")
(include-book "books/bp-fnbs-deletion-publication")
(include-book "books/bp-report-author")
(include-book "books/bp-node-progress")
(include-book "books/bp-node-progress-guards")
(include-book "books/bp-report-observe")
(include-book "books/bp-report-guards")
(include-book "books/bp-app-handoff")
(include-book "books/bp-receive-evidence")

(ld "host/store-host.lisp" :ld-error-action :error)
(ld "host/store-node-host.lisp" :ld-error-action :error)
; Opening a Store reads the clone fence (io.lisp `fnn-clone-fence-path'), whose
; name is ACL2's `fn-store-checkpoint-clone-fence-name'.  Without this file
; the DTN images could not `store init' (native-subsets-6c0626c5, failure 2).
; Every host file build.lisp loads and this one omits is listed, with its
; reason, in tools/build_lists_check.py, which `make check' runs.
(ld "host/checkpoint-host.lisp" :ld-error-action :error)
; The configuration record the core builds for a fresh store; it uses the
; octet-list helpers store-host defines above it, as run_store.py's bridge does.
(ld "host/config-host.lisp" :ld-error-action :error)
(ld "host/native-admin-host.lisp" :ld-error-action :error)
;; The external freshness anchor.  Without it the image cannot answer the
;; anchor question at all and `recover' silently omitted the field the Python
;; host prints (HANDOFF-w3-native-host.md, "the differential's four findings").
(ld "host/anchor-host.lisp" :ld-error-action :error)
(ld "host/workflow-host.lisp" :ld-error-action :error)
(ld "host/bp-receipt-journal-host.lisp" :ld-error-action :error)
(ld "host/journal-publish-host.lisp" :ld-error-action :error)
; The ACL2 side of the TCPCLv4 host: every protocol value the convergence
; layer needs, so that host/native/tcpcl.lisp computes none of them.
(ld "host/tcpcl-host.lisp" :ld-error-action :error)
; The ACL2 side of the BPv7 node: the bundle codec, the node's send and
; receive, and the endpoint/clock/configuration constructors the `bp' verb
; needs.  host/native/bp.lisp computes none of them.
(ld "host/bp-node-host.lisp" :ld-error-action :error)
(ld "host/bp-node-machine-host.lisp" :ld-error-action :error)
(ld "host/bp-receive-evidence-host.lisp" :ld-error-action :error)

; The entry save-exec's :return-from-lp form calls.  Its raw definition in
; host/native/io.lisp replaces this body; this one only reports its absence.
(defttag :fn-native-host)
(defun fn-native-entry (state)
  (declare (xargs :mode :program :stobjs state))
  (prog2$ (cw "fn-native: raw entry not installed~%") (value :missing)))
(progn! (set-raw-mode t)
        (load "host/native/io.lisp")
        ; Select once during construction, before any diagnostic module loads.
        ; A restart-time FN_NATIVE_PROFILE cannot promote this saved image.
        (fnn-select-image-profile)
        (load "host/native/immutable-publish.lisp")
        (load "host/native/admin.lisp")
        (load "host/native/workflow.lisp")
        ; The convergence layer, over io.lisp's socket surface and nothing else.
        (load "host/native/tcpcl.lisp")
        ; The BPv7 node, over the convergence layer above it and nothing else.
        (load "host/native/bp.lisp")
        (load "host/native/bp-service.lisp")
        (load "host/native/bp-contact.lisp")
        ; The saved image is a host, not a session: no ACL2 banner on stdout,
        ; and `--noinform' below keeps SBCL's own banner off it too.  The
        ; `model' verb writes reply octets to stdout and nothing else may.
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))

:q
(save-exec (or (sb-ext:posix-getenv "FN_NATIVE_IMAGE") "build/fn-host-dtn")
           "fn native host (DTN only, no NNTP reader)"
           :return-from-lp '(fn-native-entry state)
           :inert-args t
           :host-lisp-args "--noinform"
           :toplevel-args "--disable-debugger")
