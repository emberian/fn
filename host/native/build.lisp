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
; Every codec seam's attachment (books/codec-attach.lisp): the books above
; the seams call the constrained encoders and decoders, and this is what makes
; them evaluate here.  It changes no theorem.
(include-book "books/codec-attach")
;; The record encoder's attachment over the concrete recognizer
;; (books/records-attach-concrete.lisp): fn-rcon-record-encode-impl, equal to
;; fn-record-encode-impl on every input.
(include-book "books/records-attach-concrete")
(include-book "books/store-config")
(include-book "books/identity")
(include-book "books/hybrid-store-injected")
(include-book "books/peer-authored-accept")
(include-book "books/login-binding")
(include-book "books/consumer-poll-projection")
(include-book "books/article-fields")
(include-book "books/frame")
(include-book "books/store-observed")
(include-book "books/store-node-resolution")
(include-book "books/store-observed-traces")
(include-book "books/store-node")
(include-book "books/checkpoint-publish")
(include-book "books/checkpoint-pack-retire")
; The native pack-reclaim command calls fn-bs-pack-reclaim-plan from this
; guard-verified book; checkpoint-publish does not include it.
(include-book "books/byte-store-compaction-correspondence")
; Recovery after a reclaim calls fn-ccp-observe-framed and fn-ccp-coverage-framed
; through host/checkpoint-host.lisp.
(include-book "books/checkpoint-compaction-preservation")
; The pack chain the open walks and compaction extends (P5).
(include-book "books/checkpoint-pack-chain")
(include-book "books/node-config")
(include-book "books/nntp")
(include-book "books/served")
(include-book "books/served-tls-prefix")
(include-book "books/owner-tls-prefix")
(include-book "books/owner-config-observe")
(include-book "books/owner-served-carried")
(include-book "books/owner-commit-carried")
(include-book "books/owner-prepare-carried")
;; fn-owner-io (host/owner-host.lisp) calls fn-rcon-ocfg-io.
(include-book "books/records-concrete-owner")
;; The octet buffer (D27 boundary 6) and the existing-article test over it:
;; fn-owner-existing-action-buffer and fn-owner-prepare-buffer
;; (host/owner-host.lisp) call fn-pbb-existing-action.
(include-book "books/octets-stobj")
(include-book "books/poster-bytes-buffer")
;; D13 (STO-014): the duplicate-versus-conflict verdict over a store that may
;; hold tombstones.  host/owner-host.lisp and host/store-node-host.lisp call
;; fn-rcl-existing-action (list payload) and fn-rclb-existing-action (buffer).
(include-book "books/store-reclaim-buffer")
;; The subject digest over the buffer (D27 wave C): host/native/io.lisp
;; fnn-subject-id-buffer calls fn-shb-subject-id-bounded.
(include-book "books/sha256-buffer")
(include-book "books/owner-advance-carried")
(include-book "books/owner-intent-carried")
(include-book "books/owner-commit-ocl")
(include-book "books/owner-served-invariants")
(include-book "books/owner-agent")
(include-book "books/owner-log")
(include-book "books/nntp-effects")
(include-book "books/native-config")
(include-book "books/native-auth-profile")
(include-book "books/native-auth-admin")
(include-book "books/native-admin")
(include-book "books/feed-filename")
; Outbound feed connection establishment and reply framing remain ACL2-owned.
(include-book "books/feed-wire-input")
(include-book "books/feed-auth-profile")
(include-book "books/feed-connection")
(include-book "books/feed-connection-invariants")
(include-book "books/native-operator")
(include-book "books/native-control")
(include-book "books/native-hybrid-control")
(include-book "books/peer-invite")
(include-book "books/bp-receipt-records")
(include-book "books/bp-native-app-fast")
(include-book "books/bp-workflow-records")
(include-book "books/bp-release")
; Canonical Store events own retention. The workflow wrapper below projects
; that Store into workflow state; the former reverse-copy join was removed.
(include-book "books/bp-outbound")
(include-book "books/bp-ion-workflow")
(include-book "books/bp-request-plan")
(include-book "books/journal-publish")
(include-book "books/app-journal")
; The TCPCLv4 convergence layer: the octet grammar and the session machine the
; native host's host/native/tcpcl.lisp drives.  books/tcpcl-session includes
; books/tcpcl-octets and books/tcpcl-records; all three are Makefile roots.
(include-book "books/tcpcl-session")
; The spool recovery plan the raw convergence host calls before socket I/O.
(include-book "books/tcpcl-spool")
(include-book "books/bp-node")
(include-book "books/bp-node-records")
(include-book "books/bp-authored-wire")
(include-book "books/bp-node-machine")
(include-book "books/bp-contact-service")
(include-book "books/bp-node-machine-codec")
; Guard events for the exact fn-bpnf-step called by bp-service and its
; outbound fn-bpn-step base.  Certification alone does not put guard events
; into this saved image's ACL2 world.
(include-book "books/bp-node-machine-guards")
(include-book "books/bp-node-fragment-guards")
(include-book "books/bp-fragment-send")
(include-book "books/bp-node-receive-boundary")
(include-book "books/bp-fnbs-replay")
(include-book "books/bp-fnbs-inspect")
(include-book "books/bp-fnbs-namespace")
(include-book "books/bp-fnbs-publication")
(include-book "books/bp-clock-domain")
(include-book "books/bp-fnbs-delivery-replay")
(include-book "books/bp-fnbs-delivery-publication")
(include-book "books/bp-app-handoff")
(include-book "books/bp-receive-evidence")
(include-book "books/bp-app-handoff-time")
(include-book "books/bp-fnbs-family-publication")
(include-book "books/bp-fnbs-dispatch-publication")
(include-book "books/bp-fnbs-forward-publication")
(include-book "books/bp-node-receipt-send")
;; Routed queued jobs, offered once per contact (PRF-103).
(include-book "books/bp-node-contact-driver")
(include-book "books/bp-fnbs-deletion-publication")
(include-book "books/bp-fnbs-conflict-publication")
(include-book "books/bp-report-author")
(include-book "books/bp-node-progress")
(include-book "books/bp-node-progress-guards")
;; N16: the generation selection, recovery from a checkpoint and the
;; publication driver fnn-bps-open and `bp-node checkpoint' call.
(include-book "books/bp-node-rotation")
(include-book "books/bp-node-retire")
(include-book "books/bp-report-observe")
(include-book "books/bp-report-guards")
(include-book "books/bp-handoff-status")
(include-book "books/anchor-wire")
(include-book "books/anchor-servers")
(include-book "books/anchor-replace")

;; The committed-history boundary: io.lisp fnn-mark-committed and
;; fnn-check-history-marker call fn-hm-after-commit and fn-hm-open-verdict.
(include-book "books/store-history-marker")
;; D31: the history requirement and the recovery catch-up: io.lisp
;; fnn-check-history-marker, fnn-recover and fnn-command-upgrade-profile call
;; fn-hmr-open-verdict, fn-hmr-catch-up and fn-hmr-upgrade-verdict.
(include-book "books/store-history-required")
(ld "host/store-host.lisp" :ld-error-action :error)
(ld "host/store-node-host.lisp" :ld-error-action :error)
(ld "host/checkpoint-host.lisp" :ld-error-action :error)
; The configuration record the core builds for a fresh store; it uses the
; octet-list helpers store-host defines above it, as run_store.py's bridge does.
(ld "host/config-host.lisp" :ld-error-action :error)
;; The external freshness anchor.  Without it the image cannot answer the
;; anchor question at all and `recover' silently omitted the field the Python
;; host prints (HANDOFF-w3-native-host.md, "the differential's four findings").
(ld "host/anchor-host.lisp" :ld-error-action :error)
(ld "host/anchor-wire-host.lisp" :ld-error-action :error)
(ld "host/anchor-server-host.lisp" :ld-error-action :error)
(ld "host/reader-host.lisp" :ld-error-action :error)
(ld "host/owner-host.lisp" :ld-error-action :error)
(ld "host/native-config-host.lisp" :ld-error-action :error)
(ld "host/native-auth-host.lisp" :ld-error-action :error)
(ld "host/native-auth-admin-host.lisp" :ld-error-action :error)
(ld "host/native-admin-host.lisp" :ld-error-action :error)
(ld "host/feed-filename-host.lisp" :ld-error-action :error)
(ld "host/native-operator-host.lisp" :ld-error-action :error)
; The status report, offline and from the running owner.
(ld "host/native-live-status-host.lisp" :ld-error-action :error)
(ld "host/native-control-host.lisp" :ld-error-action :error)
(ld "host/native-hybrid-control-host.lisp" :ld-error-action :error)
(ld "host/hybrid-signature-host.lisp" :ld-error-action :error)
(ld "host/peer-invite-host.lisp" :ld-error-action :error)
(ld "host/topic-history-metadata-host.lisp" :ld-error-action :error)
; The differential model side, over the same fn-served-open reader-host uses.
(ld "host/native/reader-model-host.lisp" :ld-error-action :error)
(ld "host/workflow-host.lisp" :ld-error-action :error)
(ld "host/bp-release-owner-host.lisp" :ld-error-action :error)
(ld "host/bp-receipt-journal-host.lisp" :ld-error-action :error)
(ld "host/bp-native-app-host.lisp" :ld-error-action :error)
(ld "host/journal-publish-host.lisp" :ld-error-action :error)
; The ACL2 side of the TCPCLv4 host: every protocol value the convergence
; layer needs, so that host/native/tcpcl.lisp computes none of them.
(ld "host/tcpcl-host.lisp" :ld-error-action :error)
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
        ; Native cryptographic observations are a required process facility.
        ; Validate them before saving and again after the saved image starts.
        ; crypto.lisp and tls.lisp load with :dont-save t, so SBCL does not
        ; serialize build-host foreign-library paths into a relocatable core.
        ; Serialized readiness and the OpenSSL pair are cleared on restart.
        (load "host/native/crypto.lisp")
        (fnn-crypto-initialize)
        (load "host/native/io.lisp")
        ; Build-time entry profile.  tools/build_native_host.sh always supplies
        ; one of these two values.  It is serialized into the image: the
        ; restarted process cannot expose diagnostics by changing its
        ; environment.
        (fnn-select-image-profile)
        ; OpenSSL 3 is the explicit native STARTTLS trust boundary.  It loads
        ; after io.lisp because its deadline/descriptor helpers are physical
        ; transport primitives, not protocol decisions.
        (load "host/native/tls.lisp")
        ; D09 uses the same process-wide OpenSSL pair as TLS and refuses the
        ; image unless that pair provides ML-DSA-65 (OpenSSL >= 3.5).  The
        ; restart revalidates that requirement against the bundled pair.
        (load "host/native/signatures.lisp")
        (fnn-hsig-initialize)
        (defun fn-native-entry (st)
          (declare (ignore st))
          ; A refused start exits 5 with its reason (io.lisp).
          (fnn-native-startup (lambda ()
                                (fnn-crypto-startup)
                                (fnn-tls-reset)
                                (fnn-hsig-reset)
                                (fnn-hsig-initialize)))
          (fnn-main)
          (values nil :exited *the-live-state*))
        ; Bounded raw file read only; parsing, defaults and availability are
        ; all ACL2's fn-native-config-load profile.
        (load "host/native/config.lisp")
        (load "host/native/feed-filename.lisp")
        ; Bounded credential transport.  ACL2 parses and owns every field;
        ; this module also defines the composable pre-listen owner hook.
        (load "host/native/auth.lisp")
        ; Offline credential administration.  ACL2 owns argv plans, verifier
        ; derivation, serialization, reporting and persistence transitions.
        (load "host/native/auth-admin.lisp")
        (load "host/native/immutable-publish.lisp")
        (load "host/native/admin.lisp")
        ; The writable NNTP owner.  It registers the `owner' verb and calls
        ; only host/owner-host.lisp wrappers for protocol and state decisions.
        (load "host/native/owner.lisp")
        ; The outbound feed is a lifecycle extension of that same owner.  The
        ; public operator activates it; the developer-only low-level owner
        ; entry retains its separate diagnostic surface.
        (load "host/native/feed-service.lisp")
        ; The NEWNEWS pull feed, the same owner's other lifecycle extension.
        (load "host/native/pull-service.lisp")
        (load "host/native/control.lisp")
        (load "host/native/topic-local.lisp")
        (load "host/native/consumer-local.lisp")
        (load "host/native/hybrid-control.lisp")
        ; Public operator grammar follows the owner so its normalized run
        ; callback is present; it can call the already-loaded private admin
        ; executor for the ACL2-planned group/capacity actions.
        (load "host/native/operator.lisp")
        (load "host/native/signature-command.lisp")
        ; Peering invitations (PRF-097): after the hybrid control handler it
        ; wraps, the signing commands it reuses and the admin publisher.
        (load "host/native/peer-invite.lisp")
        (load "host/native/checkpoint.lisp")
        (load "host/native/workflow.lisp")
        ; The convergence layer, over io.lisp's socket surface and nothing else.
        (load "host/native/tcpcl.lisp")
        (load "host/native/bp.lisp")
        ; The application receiver is loaded after both owner and BP so its
        ; callback joins their existing objects instead of opening a second
        ; Store or convergence interpreter.
        (load "host/native/bp-app.lisp")
        (load "host/native/bp-service.lisp")
        (load "host/native/bp-contact.lisp")
        ; After FNBS: `bp-obligation request' hands its ADU to the carrier.
        (load "host/native/bp-obligation.lisp")
        (load "host/native/bp-node.lisp")
        ; Native anchor acquisition and its real primitive facility.  The
        ; anchor command calls fnn-crypto-startup in the restarted image, so
        ; it never trusts the serialized FFI readiness state.
        (load "host/native/anchor.lisp")
        ; The saved image is a host, not a session: no ACL2 banner on stdout,
        ; and `--noinform' below keeps SBCL's own banner off it too.  The
        ; `model' verb writes reply octets to stdout and nothing else may.
        (setq *print-startup-banner* nil))
(defttag nil)
(value-triple (prog2$ (cw "FN_NATIVE_BUILD_LOADED~%") :loaded))

:q
(save-exec (or (sb-ext:posix-getenv "FN_NATIVE_IMAGE") "build/fn-host")
           "fn native host"
           :return-from-lp '(fn-native-entry state)
           :inert-args t
           :host-lisp-args "--noinform"
           :toplevel-args "--disable-debugger")
