; Developer-only store runtime image.  It executes host/native/io.lisp's real
; fnn-main/store commands after loading the certified store dependencies, but
; deliberately omits unrelated owner, BP, TCPCL, and service modules.  It is
; evidence tooling, never an operator-selectable production host profile.
(in-package "ACL2")
; The fn-wide outcome classes and exit codes host/native/io.lisp reads (PRF-143).
(include-book "books/outcome-class")
(include-book "books/replay")
; Every codec seam's attachment (books/codec-attach.lisp), as in build.lisp:
; `store recover' decodes the journal (host/store-host.lisp
; fn-store-record-sequence -> fn-store-event-decode-exact), and without the
; attachment the constrained decoder has no body (hbox 08:27Z: "ACL2 error in
; fn-store-record-sequence: EV-FNCALL-NULL-BODY-ER ... FN-RECORD-DECODE-EXACT").
(include-book "books/codec-attach")
;; The record encoder's attachment over the concrete recognizer
;; (books/records-attach-concrete.lisp), as in build.lisp.
(include-book "books/records-attach-concrete")
;; The payload arena's byte-array attachment (books/payload-arena-attach.lisp)
;; must precede the first book that introduces the generic `fn-arena' (ACL2
;; refuses the attach-stobj once the name is in use).  Since the records flip
;; the held record reaches the arena, so nearly every book below does: it
;; comes right after the codec and record attachments, before any of them.
(include-book "books/payload-arena-attach")
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
;; D34: `store export' and `store import': io.lisp fnn-command-store-export and
;; fnn-command-store-import call fn-sxp-entries, fn-sxp-manifest and
;; fn-sxp-import-plan; fnn-command-store-import follows fn-bs-imp-program's
;; publication (staged, validated, no-replace rename, parent fenced) and
;; classifies a leftover staged directory through fn-bs-imp-classify.
(include-book "books/store-export")
(include-book "books/store-import-publication")
;; `operator init` publishes the empty store by the same program (PKT-647):
;; fnn-command-init-published asks fn-bs-init-pub-admission.
(include-book "books/store-init-publication")
;; The store bridge's record dispatchers (host/store-host.lisp,
;; host/store-node-host.lisp) call the concrete twins of books/records-concrete.
(include-book "books/records-concrete")
;; D13 (STO-014): the tombstone-aware same-article test over the buffer
;; (fn-rclb-same-articlep), which fn-pidx-existing-action, the served POST's
;; duplicate verdict, calls.
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
        ; A developer image by definition (the header): its `store' selectors
        ; are developer-image selectors, refused by a production profile.
        (fnn-select-image-profile "developer")
        (fnn-select-release-version)
        (defun fn-native-entry (st)
          (declare (ignore st))
          (fnn-crypto-startup)
          (fnn-main)
          (values nil :exited *the-live-state*))
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))
:q
; The saved world is the full certified world (this is evidence tooling, never
; a release image); tools/build_native_host.sh checks the marker
; host/native/strip-world.lisp prints for it (HST-025).
(load "host/native/strip-world.lisp")
(fnn-save-world-flavor "full" "build/fn-host-store-test")
(save-exec "build/fn-host-store-test" "fn native store test host"
           :return-from-lp '(fn-native-entry state)
           :inert-args t :host-lisp-args "--noinform"
           :toplevel-args "--disable-debugger")
