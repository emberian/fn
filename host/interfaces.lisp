; fn: the host-called entries, declared (G7, books/definterface.lisp).
;
; Loaded by host/native/build.lisp after every ACL2-mode host file, so each
; declaration is checked against the image's own world when the image is
; built: its class (guard-verified or not), the kinds the host entry guard
; evaluates (host/native/io.lisp fnn-entry-guard), its keystones.  A
; declaration the world refutes stops the build.  tools/interface_emit.py
; reads these forms (and host/interfaces-extract.lisp's) without evaluating
; them and generates planning/interfaces.json and tools/extract/roots.sh
; (the extractor's ROOTS and EXTRA), and gives tools/harness_check.py its
; exempt formals; its host-binding check reads the raw host for the
; dispatch sites.
;
; Declared: the extraction roots and EXTRA functions (tools/extract/build.sh),
; every entry with a byte-carrying formal its guard leaves unkinded (the
; former ENTRY_KIND_EXEMPT), the two direct applications, and then every
; other entry the raw host dispatches, by subsystem.  interface_emit --check
; refuses a dispatched entry no declaration names; planning/interfaces-gaps.md
; lists the declared entries with no keystone or no guard verification.

(in-package "ACL2")
(include-book "../books/definterface")
; Keystones the declarations below name, in books no host file otherwise
; brings into the image world (decision-keystones-5; host_check --books).
(include-book "../books/bp-handoff-report")
(include-book "../books/tcpcl-delivery-invariants")
(include-book "../books/resource-syncer")
(include-book "../books/response-identity")

; A private owner syncer ledger is installed only after the parent's real
; startup :hold.  This is thread resident/worker custody, not full resource
; admission accounting; unresolved costs are explicit in the operation row.
(definterface create-fn-resource-ledger :class :common-lisp-compliant
  :raw-guarded (0 nil (fn-resource-ledger)))
(definterface fn-ros-install-syncer :class :common-lisp-compliant)
(definterface fn-ros-issue
  :class :common-lisp-compliant
  :operation (:stage :projection :funding fn-ros-install-syncer
              :tariff fn-ros-worker-vector :draw fn-rl-draw
              :principal :owner :slot 2
              :physical fn-ros-physical :outcome fn-ros-outcome
              :retention :physical-and-operation
              :coverage (:resident :workers)
              :unaccounted (fn-rl-wfp fn-rl-draw mv-nth)))
(definterface fn-ros-physical :class :common-lisp-compliant)
(definterface fn-ros-outcome :class :common-lisp-compliant)
(definterface fn-ros-drainedp :class :common-lisp-compliant)

(definterface fn-rid-connection :class :common-lisp-compliant)
(definterface fn-rid-response :class :common-lisp-compliant)

; Guarded private output methods preserve typed representation. Complete
; free-chain/bank correspondence and allocation tariff remain PRF-1259; no gate.
(definterface fn-rlo-install :class :common-lisp-compliant)
(definterface fn-rlo-issue :class :common-lisp-compliant)
(definterface fn-heap-figure-octets :class :common-lisp-compliant)
(definterface fn-orv-startup-slots :class :common-lisp-compliant)
(definterface fn-orv-startup-grant :class :common-lisp-compliant)
(definterface fn-rlo-output :class :common-lisp-compliant)
(definterface fn-rlo-physical :class :common-lisp-compliant)
(definterface fn-rlo-drainedp :class :common-lisp-compliant)

; -----------------------------------------------------------------------------
; The extraction roots: the functions the extracted served program's driver
; calls (tools/extract/build.sh ROOTS, in that order).

(definterface create-fn-arena
  :class :common-lisp-compliant
  :root :extract)

(definterface fn-reader-use-seed
  :class :common-lisp-compliant
  :keystones ((fn-rdc-selection-establishes :via fn-rdc-selection))
  :root :extract)

(definterface fn-reader-set-posting
  :class :common-lisp-compliant
  :root :extract)

(definterface fn-reader-model-octets
  :class :common-lisp-compliant
  :root :extract)

(definterface fn-reader-reset
  :class :common-lisp-compliant
  :keystones ((fn-rdc-reset-is-served-open :via fn-rdc-reset))
  :root :extract)

(definterface fn-reader-chunk
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp))
  :keystones ((fn-oag-served-step-submission-names-the-pinned-agent :via fn-served-step))
  :root :extract)

(definterface fn-reader-outcome
  :class :common-lisp-compliant
  :keystones ((fn-own-consumed-completion-is-240-or-uncertain
               :via fn-served-post-outcome))
  :root :extract)

(definterface fn-reader-observe-clock
  :class :common-lisp-compliant
  :keystones ((fn-clock-observation-shapep-of-fn-clock-observation
               :via fn-clock-observation))
  :root :extract)

(definterface fn-outcome-code
  :class :common-lisp-compliant
  :keystones (fn-nh-exit-code-is-zero-or-past-the-outcome-codes)
  :root :extract)

(definterface fn-ns-file-render
  :class :common-lisp-compliant
  :keystones (fn-ns-file-parse-of-render)
  :root :extract)

(definterface fn-intern-events
  :class :common-lisp-compliant
  :kinds ((generation natp))
  :keystones (fn-arx-intern-events-refines fn-lzr-intern-events-refines)
  :root :extract)

(definterface fn-arx-entry-ok-buffer
  :class :common-lisp-compliant
  :keystones (fn-arx-entry-ok-buffer-is-the-frame-check)
  :root :extract)

(definterface fn-arx-read-cache-entries
  :class :common-lisp-compliant
  :root :extract)

; host/native/owner.lisp's checkpoint release reads the live arena's file
; count (lane composed-owner-4, row A6).
(definterface fn-arx-file-count
  :class :common-lisp-compliant
  :kinds ((f natp))
  :root :extract)

; fn-xo-open-store: host/interfaces-extract.lisp (the image does not load
; host/store-open-host.lisp).

(definterface fn-reader-use-store
  :class :common-lisp-compliant
  :keystones ((fn-rdc-store-selection-unfolds :via fn-rdc-store-selection))
  :root :extract)

(definterface fn-lzr-lz-read
  :class :common-lisp-compliant
  :kinds ((dict fn-cbor-octet-listp) (c fn-cbor-octet-listp) (n natp))
  :keystones (fn-lzr-lz-read-is-the-lz-value)
  :root :extract)

; The extractor's EXTRA functions (tools/extract/build.sh EXTRA): the
; realizer's buffer stobjs' creators and the digests' references.

(definterface create-fn-octets-rd
  :class :common-lisp-compliant
  :root :extract-extra)

(definterface create-fn-octets-lg
  :class :common-lisp-compliant
  :root :extract-extra)

(definterface fn-blake3-stobj
  :class :common-lisp-compliant
  :keystones (fn-blake3-stobj-is-blake3)
  :root :extract-extra)

(definterface fn-blake3-of-prefixed-buffer
  :class :common-lisp-compliant
  :kinds ((prefix true-listp))
  :keystones (fn-blake3-of-prefixed-buffer-is-blake3)
  :root :extract-extra)

(definterface fn-blake3-of-prefixed-range
  :class :common-lisp-compliant
  :kinds ((prefix true-listp) (a natp) (wn natp))
  :keystones (fn-blake3-of-prefixed-range-is-blake3)
  :root :extract-extra)

(definterface fn-sha256
  :class :common-lisp-compliant
  :keystones (fn-sha256-is-of-octets-on-octets)
  :root :extract-extra)

; -----------------------------------------------------------------------------
; Entries with a byte-carrying formal (tools/harness_check.py
; ENTRY_KIND_FORMAL) that the guard does not kind, each with the reason.

(definterface fn-native-operator-host-inspect-report
  :class :program
  :exempt ((msgid-octets "the host passes a LIST of Message-IDs (msgid-list); the name is historical")))

(definterface fn-native-operator-host-mission-run
  :class :program
  :kinds ((path-octets fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted by fn-native-operator-host-preflight")))

(definterface fn-native-operator-host-preflight
  :class :program
  :exempt ((argv-octets "the argv preflight is the check: it refuses a malformed argv by name")))

(definterface fn-native-operator-host-run-at
  :class :program
  :kinds ((cwd fn-cbor-octet-listp) (config-path fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted (fn-native-operator-host-preflight)")
           (config-octets "read by fnn-operator-read-config, bounded; NIL when absent")))

(definterface fn-owner-control-submit
  :class :common-lisp-compliant
  :kinds ((msgid-octets fn-cbor-octet-listp) (group-octets fn-octet-list-listp))
  :exempt ((payload "the received article's buffer (host/native/hybrid-control.lisp)"))
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))


(definterface fn-native-health-host-exit
  :class :program
  :exempt ((octets "the health report's summary structure (fnn-operator-health-report)")))

; Counts named after octets.

(definterface fn-srs-chunk-fullp
  :class :common-lisp-compliant
  :exempt ((octets "a count of octets (natp in the body)")))

(definterface fn-ockp-segment-octets
  :class :common-lisp-compliant
  :exempt ((record-octets "a count of octets (nfix)"))
  :keystones (fn-ockp-segment-octets-bounds))

(definterface fn-lgc-take
  :class :common-lisp-compliant
  :kinds ((c true-listp))
  :exempt ((octets "the open batch's running octet count"))
  :keystones (fn-lgc-take-refines))

; Total decoders over any value: a non-octet argument decodes to the
; decoder's own refusal, which the host names.

(definterface fn-ns-file-parse
  :class :common-lisp-compliant
  :exempt ((octets "total parser; NIL is refused by fnn-node-secret-read-entry"))
  :keystones (fn-ns-file-parse-of-render))

(definterface fn-pull-journal-scan
  :class :common-lisp-compliant
  :exempt ((frame "total journal scan (guard t)")))

(definterface fn-cu-journal-scan
  :class :common-lisp-compliant
  :exempt ((frame "total journal scan (guard t; peer-catchup's FNCU twin of fn-pull-journal-scan)")))

; Not guard-verified (:ideal): the host's call runs the logic definition.
(definterface fn-bpnf-inspect-adu
  :class :common-lisp-compliant
  :exempt ((frame "total unframe (fn-bpnf-stored-recordp gates it)")))

(definterface fn-bpnpf-node-profile-write-octets
  :class :common-lisp-compliant
  :exempt ((octets "a count (the octets limit), gated by fn-bpnpf-profile-upgradep (bp-rotation: the format-3 writer the host dispatches)"))
  :keystones (fn-bpnpf-node-profile-write-never-lowers))

(definterface fn-heap-limit-of-octets
  :class :common-lisp-compliant
  :exempt ((octets "total parser of a limit file (true-listp tested)")))

; -----------------------------------------------------------------------------
; Applied by the raw host directly, not through fnn-call's entry guard.

(definterface fn-octets$c-reserve
  :class :common-lisp-compliant
  :kinds ((n natp))
  :keystones (fn-octets-reserve{correspondence})
  :direct "the octet buffer's stobj primitive (host/native/io.lisp fnn-live-octets)")

(definterface fn-outcome-host-condition-exit-code
  :class :common-lisp-compliant
  :keystones (fn-outcome-host-condition-fences-iff-indeterminate)
  ; the raw host reaches it through fn-fs-exit-code (books/failure-scope.lisp)
  ; since lane failure-scope; the extracted driver's exit for the condition
  ; that ended a store verb (tools/extract/served-main.scm store-report; lane
  ; extract-writable)
  :root :extract)

;; The failure scope of a host boundary (books/failure-scope.lisp; lane
;; failure-scope, t45): the host names a condition's concrete class and the
;; boundary's last durable step, ACL2 decides the kind; the service's exit
;; escalates on a lattice.  All four run in handlers, called directly.
(definterface fn-fs-classify
  :class :common-lisp-compliant
  :keystones (fn-fs-unknown-class-is-a-fault fn-fs-refusal-only-from-the-table
              fn-fs-indeterminate-iff fn-fs-os-error-after-a-durable-step-is-the-fence)
  :direct "runs in handlers (fnn-owner-classify-escape-locked, fnn-owner-thread-escape), where a dispatcher's own fault would recurse")
(definterface fn-fs-classify-job
  :class :common-lisp-compliant
  :keystones (fn-fs-classify-job-differs-only-on-an-early-os-error
              fn-fs-classify-job-fences-after-a-durable-step)
  :direct "runs in the exporter's handler, where a dispatcher's own fault would recurse")
(definterface fn-fs-exit-code
  :class :common-lisp-compliant
  :keystones (fn-fs-exit-code-is-fenced-iff-indeterminate)
  :direct "runs in handlers (fnn-exit-code-for), where a dispatcher's own fault would recurse")
(definterface fn-fs-stop-exit-escalate
  :class :common-lisp-compliant
  :keystones (fn-fs-stop-exit-fence-is-never-masked fn-fs-stop-exit-escalate-is-monotone
              fn-fs-stop-exit-ok-is-the-bottom)
  :direct "runs under the roster mutex inside the fence (fnn-owner-stop-service-locked), which must not fail")
;; The declared owner sections (lane WRAPPER: def-section, host/native/
;; owner.lisp): ACL2 accepts a declaration at load and decides each entry's
;; class, admission and unwind inside the one envelope, called directly (the
;; envelope's gate and fence paths run in handlers).
(definterface fn-fs-section-declp
  :class :common-lisp-compliant
  :keystones (fn-fs-section-declp-refuses-an-unlisted-cleanup-purpose)
  :direct "runs at load in fnn-section-declare, before fnn-call's dispatcher serves")
(definterface fn-fs-section-class-ok
  :class :common-lisp-compliant
  :keystones (fn-fs-section-class-ok-only-for-a-declared-class)
  :direct "runs inside the envelope's gate handler (fnn-section-envelope), where a dispatcher's own fault would recurse")
(definterface fn-fs-section-admit
  :class :common-lisp-compliant
  :keystones (fn-fs-a-live-section-is-refused-once-stopping fn-fs-section-admit-runs-before-the-stop)
  :direct "runs under the owner mutex inside the fence boundary (fnn-section-run)")
(definterface fn-fs-unwind
  :class :common-lisp-compliant
  :keystones (fn-fs-unwind-faults-an-unexplained-exit)
  :direct "runs in the envelope's unwind under the owner mutex, which must not fail")

;; Physical lifecycle: these guard-t decisions run in the boundary itself.
(definterface fn-fs-actor-exit-kind
  :class :common-lisp-compliant
  :keystones (fn-fs-actor-early-exit-survives-spawn-publication)
  :direct "fnn-owner-actor-run classifies its final unwind without recursing through dispatcher faults")
(definterface fn-fs-actor-step
  :class :common-lisp-compliant
  :keystones (fn-fs-actor-only-physical-end-or-failed-spawn-deregisters
              fn-fs-actor-failed-join-retains-custody)
  :direct "native actor start/run/join advances the guard-t physical lifecycle while holding roster exclusion")
(definterface fn-fs-actor-join-action
  :class :common-lisp-compliant
  :keystones (fn-fs-actor-failed-join-retains-custody)
  :direct "fnn-owner-actor-join classifies physical termination separately from fault escalation")
(definterface fn-fs-actor-receipt
  :class :common-lisp-compliant
  :keystones (fn-fs-actor-failed-join-produces-no-receipt
              fn-fs-actor-receipt-carries-the-recorded-exit)
  :direct "fnn-owner-actor-join emits only the lifecycle receipt after physical termination")
(definterface fn-fs-inbox-admit
  :class :common-lisp-compliant
  :direct "fnn-mux-adopt-place decides admission under the same inbox lock as closure")

;; Private committer control: immutable, guard-t values off the owner section.
(definterface fn-cmt-init
  :class :common-lisp-compliant
  :keystones (fn-cmt-init-is-valid)
  :direct "fnn-owner-committer-loop creates its private immutable control state")
(definterface fn-cmt-step
  :class :common-lisp-compliant
  :keystones (fn-cmt-step-state-is-valid fn-cmt-pipeline-requires-its-captured-passes
              fn-cmt-wrong-snapshot-ticket-faults)
  :direct "fnn-owner-committer-loop interprets private actor actions; no shared live state or protected stobj")
(definterface fn-cmt-pass-target
  :class :common-lisp-compliant
  :direct "fnn-owner-loops-snapshot captures each mux pass target under commit exclusion")
(definterface fn-cmt-pass-ready
  :class :common-lisp-compliant
  :direct "fnn-owner-loops-passed-p observes progress against the retained snapshot")

; ======================================================================; Every other entry the raw host dispatches through fnn-call, by subsystem
; (tools/interface_emit.py SUBSYSTEMS).  Class and kinds are the image
; world's; a keystone is a cited theorem (planning/proofs.json) whose
; conclusion is about the entry or whose name carries it.  No :keystones is
; a gap, listed in planning/interfaces-gaps.md.

; -----------------------------------------------------------------------------
; store (262 entries)

(definterface fn-arena-count
  :class ::common-lisp-compliant
  :keystones (fn-arena-seal-lz-extent-payload
              fn-arena-seal-extent-payload
              fn-arena-reseat-extent-payload))

(definterface fn-arena-release
  :class ::common-lisp-compliant
  :kinds ((h natp)))

(definterface fn-arena-seal-buffer
  :class ::common-lisp-compliant)

(definterface fn-arena-seal-list
  :class ::common-lisp-compliant
  :kinds ((xs fn-cbor-octet-listp))
  :keystones (fn-scol-okp-of-seal-list
              fn-arn-store-corr-of-commit
              fn-arena-seal-range-is-seal-list))

(definterface fn-arx-commit-reseats
  :class ::common-lisp-compliant
  :keystones (fn-arx-commit-reseats-keep-the-arena))



(definterface fn-arx-list-places
  :class ::common-lisp-compliant
  :kinds ((tail true-listp) (p natp) (count natp) (ep natp) (en natp) (qtail true-listp) (q natp) (qend natp) (acc true-listp))
  :keystones (fn-lgb-entry-places-is-list-places))

(definterface fn-b3-left-chunks
  :class ::common-lisp-compliant
  :kinds ((p natp) (n natp)))

(definterface fn-blake3-of-prefixed-buffer-any
  :class ::common-lisp-compliant)

(definterface fn-bs-config-encode
  :class ::common-lisp-compliant)

(definterface fn-bs-imp-classify
  :class ::common-lisp-compliant
  :keystones (fn-bs-imp-classify-by-what-is-known))

(definterface fn-bs-init-log-subdir-names
  :class ::common-lisp-compliant)

(definterface fn-bs-init-pub-admission
  :class ::common-lisp-compliant
  :keystones (fn-bs-init-pub-admission-proceeds-only-on-nothing
              fn-bs-init-pub-admission-decides-by-what-is-present))

(definterface fn-clock-observation
  :class ::common-lisp-compliant)

(definterface fn-cpe-decode-exact
  :class ::common-lisp-compliant)

(definterface fn-cpe-encode
  :class ::common-lisp-compliant)

(definterface fn-frame-trailer
  :class ::common-lisp-compliant)

(definterface fn-lg-extent-okp
  :class ::common-lisp-compliant)

(definterface fn-lg-recover-tail
  :class ::common-lisp-compliant
  :kinds ((ks true-listp)))

(definterface fn-lg-workload-prefixp
  :class ::ideal)

(definterface fn-lg-workload-record
  :class ::ideal)

(definterface fn-lgb-decode-next
  :class ::common-lisp-compliant)

(definterface fn-lgb-entry-places
  :class ::common-lisp-compliant
  :kinds ((pos natp) (count natp))
  :keystones (fn-lgb-entry-places-is-list-places))

(definterface fn-lgc-acked
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-append
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-append-admitsp
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-append-octets
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-consume-to
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-count
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-extension-needed-p
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-extension-target
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-fence
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-fence-failed
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-finish-one
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-frontier
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-last
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-next-txid
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-phase
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

;; K's range (fn-lg-rotation-indexp) and the chain's last digest are guard
;; conjuncts no entry kind names (*fn-entry-guard-kinds*): fnn-log-rotate
;; passes the index ACL2 answered (nil = segment-index-exhausted, refused).
(definterface fn-lgc-rotate
  :class ::common-lisp-compliant
  :kinds ((c true-listp) (unit natp))
  :keystones (fn-lgc-rotate-refines))

;; The rotation entry the host writes at offset 0 of the rotated-to segment
;; (lane store-lineage; books/store-log-kernel-concrete.lisp).
(definterface fn-lgc-rotation-octets
  :class ::common-lisp-compliant
  :kinds ((c true-listp) (unit natp)))

;; The open's lineage decision over the checkpoint's F row and the segment's
;; head (books/store-log-lineage.lisp, PRF-979; host fnn-log-lineage-genesis).
(definterface fn-lgl-open
  :class ::ideal
  :keystones (fn-lgl-open-of-rotated-segment))

(definterface fn-lgl-head-prev
  :class ::ideal)

(definterface fn-lgl-head-len
  :class ::common-lisp-compliant)

(definterface fn-lgl-refusal-text
  :class ::common-lisp-compliant)

(definterface fn-lgc-rotate-admitsp
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-rotate-needed-p
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgc-t-prepare
  :class ::common-lisp-compliant
  :kinds ((c true-listp)))

(definterface fn-lgdm-chain-continues-p
  :class ::common-lisp-compliant)

(definterface fn-lgdm-done-p
  :class ::common-lisp-compliant
  :kinds ((ps true-listp)))

(definterface fn-lgdm-effective
  :class ::common-lisp-compliant
  :keystones (fn-lgdm-repair-is-only-the-confirmed-damage))

(definterface fn-lgdm-entry-len-bounded
  :class :common-lisp-compliant
  :kinds ((ps true-listp))
  :keystones (fn-lgdm-entry-len-bounded-step
              fn-lgdm-entry-len-bounded-is-entry-len))

(definterface fn-lgw-entry-len-bounded
  :class :common-lisp-compliant
  :kinds ((st true-listp))
  :keystones (fn-lgw-entry-len-bounded-step
              fn-lgw-entry-len-bounded-is-entry-len))

(definterface fn-lgdm-header-len
  :class ::common-lisp-compliant
  :kinds ((ps true-listp)))

(definterface fn-lgdm-history-break-text
  :class ::common-lisp-compliant)

(definterface fn-lgdm-q
  :class ::common-lisp-compliant
  :kinds ((ps true-listp)))

(definterface fn-lgdm-quarantine-name
  :class ::common-lisp-compliant)

(definterface fn-lgdm-refusal-text
  :class ::common-lisp-compliant
  :keystones (fn-lgdm-refusal-text-refuses-exactly-a-break-or-damage))

(definterface fn-lgdm-refused-p
  :class ::common-lisp-compliant)

(definterface fn-lgdm-repair-text
  :class ::common-lisp-compliant)

(definterface fn-lgdm-report-text
  :class ::common-lisp-compliant)

(definterface fn-lgdm-start
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-lgdm-step
  :class ::common-lisp-compliant
  :kinds ((ps true-listp)))

(definterface fn-lgdm-verdict
  :class ::common-lisp-compliant
  :kinds ((st true-listp) (ps true-listp)))

(definterface fn-lgs-listing-bound
  :class ::common-lisp-compliant)

(definterface fn-lgs-next-segment
  :class ::common-lisp-compliant)

(definterface fn-lgs-open-plan
  :class ::common-lisp-compliant
  :keystones (fn-lgs-open-plan-scan-ignores-covered))

(definterface fn-lgs-segment-index
  :class ::common-lisp-compliant)

(definterface fn-lgs-segment-name
  :class ::common-lisp-compliant)

(definterface fn-lgw-header-len
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-lgw-kernel
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-lgw-pos
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-lgw-set-next
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-lgw-start
  :class ::common-lisp-compliant)

(definterface fn-lgw-stop
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

(definterface fn-log-sink-close-wait-seconds
  :class ::common-lisp-compliant)

(definterface fn-log-sink-init
  :class ::common-lisp-compliant
  :keystones (fn-log-sink-init-okp))

(definterface fn-log-sink-offer
  :class ::common-lisp-compliant
  :keystones (fn-log-sink-offer-preserves-okp
              fn-log-sink-offer-drops-only-past-the-bound))

(definterface fn-log-sink-pending-bound
  :class ::common-lisp-compliant)

(definterface fn-log-sink-take
  :class ::common-lisp-compliant
  :keystones (fn-log-sink-take-preserves-okp))

(definterface fn-lzr-append-decide
  :class ::common-lisp-compliant
  :kinds ((dict fn-cbor-octet-listp) (r fn-cbor-octet-listp) (k natp) (n natp))
  :keystones (fn-lzr-append-decide-refuses-exactly-a-bad-candidate
              fn-lzr-append-decide-keeps-only-without-gain
              fn-lzr-append-decide-framed-is-the-seal
              fn-lzr-append-decide-framed-is-shorter
              fn-lzr-append-decide-framed-expands))

(definterface fn-own-bp-transit-kind-word
  :class ::common-lisp-compliant)

(definterface fn-lzr-append-plan
  :class ::common-lisp-compliant
  :kinds ((r fn-cbor-octet-listp))
  :keystones (fn-lzr-config-min-without-a-row-is-off
              fn-lzr-append-plan-off))

(definterface fn-lzr-append-refusal-text
  :class ::common-lisp-compliant
  :keystones (fn-lzr-append-refusal-text-refuses-exactly-a-lying-encoder))

(definterface fn-lzr-append-octets
  :class ::common-lisp-compliant
  :keystones (fn-lzr-append-octets-of-decide
              fn-lzr-append-refusal-text-refuses-exactly-a-lying-encoder))

(definterface fn-lzr-candidate-cap
  :class ::common-lisp-compliant)

(definterface fn-lzr-commit-reseats
  :class ::common-lisp-compliant
  :keystones (fn-lzr-commit-reseats-keep-the-arena))

(definterface fn-lzr-dicts-initial
  :class ::common-lisp-compliant)



(definterface fn-lzr-read-refusal-text
  :class ::common-lisp-compliant
  :keystones (fn-lzr-read-refusal-text-refuses-exactly-what-does-not-expand))

(definterface fn-lzr-read-step
  :class ::common-lisp-compliant
  :kinds ((tally true-listp) (z fn-cbor-octet-listp)))

(definterface fn-lzr-tally-empty
  :class ::common-lisp-compliant)

(definterface fn-lzr-tally-text
  :class ::common-lisp-compliant
  :kinds ((tally true-listp)))

(definterface fn-ns-create-entry
  :class ::common-lisp-compliant)

(definterface fn-ns-entry-epoch
  :class ::common-lisp-compliant)

(definterface fn-ns-entryp
  :class ::common-lisp-compliant)

(definterface fn-ns-rotate-entry
  :class ::common-lisp-compliant)

(definterface fn-ns-secret-width
  :class ::common-lisp-compliant)

(definterface fn-ock-capture-budget
  :class ::common-lisp-compliant)

(definterface fn-ock-request-status
  :class ::common-lisp-compliant)

(definterface fn-ockp-donep
  :class ::common-lisp-compliant)

(definterface fn-ockp-initial-state
  :class ::common-lisp-compliant)

(definterface fn-ockp-step
  :class ::common-lisp-compliant
  :kinds ((b natp) (bytes natp) (seg natp) (s natp))
  :keystones (fn-ockp-step-preserves-statep
              fn-ockp-step-preserves-encodable))

(definterface fn-olr-bmax
  :class ::common-lisp-compliant)

(definterface fn-olr-omax
  :class ::common-lisp-compliant)

(definterface fn-otm-admit-post
  :class ::common-lisp-compliant
  :keystones (fn-otm-space-recovers
              fn-otm-peer-reader-read-only-while-shedding
              fn-otm-past-the-deadline-sheds
              fn-otm-full-sheds
              fn-otm-decisions-read-only-the-journal-state))

(definterface fn-otm-commit-event
  :class ::common-lisp-compliant
  :keystones (fn-otm-commit-event-is-ocp-commit-event))

(definterface fn-otm-committer-wake
  :class ::common-lisp-compliant)

(definterface fn-otm-disk
  :class ::common-lisp-compliant
  :keystones (fn-otm-space-event-keeps-the-disk
              fn-otm-shed-only-past-the-deadline
              fn-otm-observe-keeps-the-disk
              fn-otm-next-is-ocp-next
              fn-otm-commit-event-is-ocp-commit-event))

(definterface fn-otm-disk-stalled
  :class ::common-lisp-compliant)

(definterface fn-otm-disk-step
  :class ::common-lisp-compliant
  :keystones (fn-otm-disk-step-unfolds))

(definterface fn-otm-init
  :class ::common-lisp-compliant)

(definterface fn-otm-journal-exit
  :class ::common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-otm-journal-report
  :class ::common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp))
  :keystones (fn-otm-journal-report-of-a-run))

(definterface fn-otm-jw-after
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-closed-line
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-cut-line
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-drop
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-init
  :class ::common-lisp-compliant
  :keystones (fn-otm-jw-gap-is-the-first-lost
              fn-otm-jw-file-reads-agrees-or-gap))

(definterface fn-otm-jw-open-first
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-open-step
  :class ::common-lisp-compliant
  :kinds ((start natp))
  :keystones (fn-otm-jw-open-step-is-the-cut
              fn-otm-jw-open-step-cuts-a-written-file))

(definterface fn-otm-jw-plan
  :class ::common-lisp-compliant)

(definterface fn-otm-jw-truncated
  :class ::common-lisp-compliant)

(definterface fn-otm-next
  :class ::common-lisp-compliant
  :keystones (fn-otm-next-is-ocp-next))

(definterface fn-otm-note-step
  :class ::common-lisp-compliant)

(definterface fn-otm-observe
  :class ::common-lisp-compliant
  :keystones (fn-otm-observe-keeps-the-disk))

(definterface fn-otm-peer-read-class
  :class ::common-lisp-compliant)

(definterface fn-otm-peer-read-proceeds-p
  :class ::common-lisp-compliant)

(definterface fn-otm-space-due-p
  :class ::common-lisp-compliant)

(definterface fn-otm-stall-releases
  :class ::common-lisp-compliant
  :keystones (fn-otm-stall-tells-no-member-its-outcome))

(definterface fn-otm-start-line
  :class ::common-lisp-compliant)

(definterface fn-otm-wait-ms
  :class ::common-lisp-compliant
  :keystones (fn-otm-decisions-read-only-the-journal-state))

(definterface fn-otm-wall-reading
  :class ::common-lisp-compliant
  :keystones (fn-otm-wall-reading-shape fn-clkr-wall-reading-is-the-ns-decision))

(definterface fn-otm-wall-seconds
  :class ::common-lisp-compliant
  :keystones (fn-otm-wall-seconds-is-natural fn-clkr-wall-seconds-is-the-ns-decision))

(definterface fn-otm-monotonic-ms
  :class ::common-lisp-compliant
  :keystones (fn-clkr-monotonic-readings-are-the-ns-decision))

(definterface fn-otm-boottime-ms
  :class ::common-lisp-compliant
  :keystones (fn-clkr-monotonic-readings-are-the-ns-decision))

(definterface fn-otm-wordp
  :class ::common-lisp-compliant)

(definterface fn-sbud-post-boundary
  :class ::common-lisp-compliant
  :keystones (fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound
              fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted
              fn-pvc-post-boundary-carried-is-sbud-post-boundary))

(definterface fn-sbud-post-boundary-refusal
  :class ::common-lisp-compliant
  :keystones (fn-sbud-post-boundary-refusals-are-distinct
              fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted))

(definterface fn-scka-seal-n
  :class ::common-lisp-compliant
  :kinds ((i natp) (end natp) (n natp))
  :keystones (fn-scka-seal-n-compose))

(definterface fn-scka-srcs-n
  :class ::common-lisp-compliant
  :kinds ((n natp))
  :keystones (fn-scka-srcs-n-compose
              fn-scka-srcs-n-complete))

(definterface fn-scka-write-donep
  :class ::common-lisp-compliant)

(definterface fn-scka-write-step
  :class ::common-lisp-compliant
  :kinds ((pst true-listp) (n natp) (count natp) (s natp)))

(definterface fn-sidb-subject-id-bounded
  :class ::common-lisp-compliant)

(definterface fn-smid-durability-warning
  :class ::common-lisp-compliant
  :keystones (fn-smid-durability-warning-warns-exactly-when-the-mount-is-unsafe))

(definterface fn-smid-init-policy
  :class ::common-lisp-compliant)

(definterface fn-smid-linux-observation
  :class ::common-lisp-compliant)

(definterface fn-smid-mountinfo-line-max
  :class ::common-lisp-compliant)

(definterface fn-smid-mountinfo-step
  :class ::common-lisp-compliant
  :keystones (fn-smid-mountinfo-step-preserves-best-okp))

(definterface fn-smid-open-decision
  :class ::common-lisp-compliant
  :keystones (fn-smid-open-decision-is-the-verdict))

(definterface fn-smid-rebind-plan
  :class ::common-lisp-compliant)

(definterface fn-smid-rebind-text
  :class ::common-lisp-compliant)

(definterface fn-smid-record-frame-limit
  :class ::common-lisp-compliant)

(definterface fn-smid-record-plan
  :class ::common-lisp-compliant)

(definterface fn-smid-refusal-text
  :class ::common-lisp-compliant
  :keystones (fn-smid-refusal-text-is-nil-exactly-for-start
              fn-smid-refusal-text-is-nil-exactly-for-open
              fn-smid-refusal-text-is-nil-exactly-for-an-open-decision))

(definterface fn-smid-start-verdict
  :class ::common-lisp-compliant
  :keystones (fn-smid-start-refused-iff-required-and-unsafe))

(definterface fn-smid-statfs-observation
  :class ::common-lisp-compliant)

(definterface fn-smid-unrecorded-warning
  :class ::common-lisp-compliant)





(definterface fn-store-cfg-generation
  :class ::program)

(definterface fn-store-cfg-last-octets
  :class ::program)

(definterface fn-store-cfg-last-reason
  :class ::program)

(definterface fn-store-cfg-native-admin-authorize
  :class ::program
  :kinds ((octet-records fn-octet-list-listp) (config-octet-records fn-octet-list-listp) (record-octets fn-cbor-octet-listp) (observed-name-octets fn-octet-list-listp)))

(definterface fn-store-cfg-native-admin-authorize-carried
  :class ::program
  :kinds ((config-octet-records fn-octet-list-listp) (record-octets fn-cbor-octet-listp) (observed-name-octets fn-octet-list-listp)))

(definterface fn-store-charge
  :class ::common-lisp-compliant
  :keystones (fn-store-charge-is-positive-exactly-for-a-length-and-is-the-receipt-charge))

(definterface fn-store-checkpoint-clone-fence-name
  :class ::program)

(definterface fn-store-checkpoint-clone-fence-read-bound
  :class ::program)

(definterface fn-store-checkpoint-clone-input-pathp
  :class ::program)

(definterface fn-store-checkpoint-clone-max-bytes
  :class ::program)

(definterface fn-store-checkpoint-clone-max-depth
  :class ::program)

(definterface fn-store-checkpoint-clone-max-entries
  :class ::program)

(definterface fn-store-checkpoint-clone-path-bound
  :class ::program)

(definterface fn-store-checkpoint-clone-phase
  :class ::program
  :kinds ((marker-octets fn-cbor-octet-listp)))

(definterface fn-store-checkpoint-rollover-proposal
  :class ::program)

(definterface fn-store-compress-min-octets
  :class ::program)

(definterface fn-store-config-observation-limit
  :class ::program)

(definterface fn-store-decode-records
  :class ::program
  :kinds ((octet-records fn-octet-list-listp)))

(definterface fn-store-event-kind
  :class ::common-lisp-compliant)

(definterface fn-store-frame-constants
  :class ::ideal)

(definterface fn-store-genesis-chain
  :class ::ideal)

(definterface fn-store-genesis-file-name
  :class ::ideal)

(definterface fn-store-genesis-install
  :class ::program)

(definterface fn-store-genesis-octets
  :class ::ideal
  :delegates fn-gen-octets-for)

(definterface fn-store-genesis-open
  :class ::ideal
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-store-genesis-refusal-text
  :class ::ideal
  :delegates fn-gen-refusal-text)

(definterface fn-store-group-codes
  :class ::ideal
  :kinds ((name-octets fn-octet-list-listp) (domain-octets fn-octet-list-listp)))

(definterface fn-store-identity-text
  :class ::ideal)

(definterface fn-store-log-initial-extent
  :class ::ideal)

(definterface fn-store-log-partial-segment-verdict
  :class ::ideal)

(definterface fn-store-log-next-txid-join
  :class ::program)

(definterface fn-store-log-next-txid-step
  :class ::program)

(definterface fn-store-log-reclaim-decide-recorded
  :class ::program)

(definterface fn-store-log-reclaim-decide-stream
  :class ::program)

(definterface fn-store-log-reclaim-event
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-store-log-segment-name
  :class ::ideal)

(definterface fn-store-log-unit
  :class ::ideal)

(definterface fn-store-metadata-config-decode
  :class ::ideal
  :kinds ((octets fn-cbor-octet-listp))
  :delegates fn-bs-config-decode)

(definterface fn-store-metadata-config-frame
  :class ::ideal
  :delegates fn-bs-config-frame-for-profile)

(definterface fn-store-metadata-config-open
  :class ::ideal
  :kinds ((octets fn-cbor-octet-listp))
  :delegates fn-spo-config-open)

(definterface fn-store-metadata-config-refusal-text
  :class ::ideal
  :delegates fn-spo-refusal-text)

(definterface fn-store-metadata-frontier-decode
  :class ::ideal
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-store-metadata-frontier-frame
  :class ::ideal)

(definterface fn-store-metadata-frontier-next
  :class ::ideal)

(definterface fn-store-obligation-id-of
  :class ::ideal)

(definterface fn-store-open-refusal-text
  :class ::program)

(definterface fn-store-open-stop-text
  :class ::program)

(definterface fn-store-profile-admittedp
  :class ::ideal
  :delegates fn-bs-profile-admittedp)

(definterface fn-store-profile-logp
  :class ::ideal
  :delegates fn-bs-profile-logp)

(definterface fn-store-profile-max-record-octets
  :class ::ideal
  :delegates fn-bs-profile-max-record-octets)

(definterface fn-store-profile-read-bound
  :class ::common-lisp-compliant
  :keystones (fn-store-profile-read-bound-covers-every-admitted-publication))

(definterface fn-store-profile-report
  :class ::ideal
  :delegates fn-bs-profile-report)

(definterface fn-store-prov-for-msgid
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp)))

(definterface fn-store-prov-post
  :class ::program)

(definterface fn-store-publication-admissibility
  :class ::common-lisp-compliant
  :keystones (fn-store-publication-admissibility-admits-exactly-within-the-profile
              fn-store-profile-read-bound-covers-every-admitted-publication))

(definterface fn-store-reclaim-context
  :class ::program)

(definterface fn-store-reclaim-context-recorded
  :class ::program)

(definterface fn-store-reclaim-ctx-classes
  :class ::program)

(definterface fn-store-reclaim-init
  :class ::program)

(definterface fn-store-reclaim-instant-record
  :class ::program)

(definterface fn-store-reclaim-step
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-store-record-sequence
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-store-repair-control-text
  :class ::program)

(definterface fn-store-sco-clear
  :class ::program)

(definterface fn-store-sco-file-name
  :class ::program)

(definterface fn-store-sco-file-read-bound
  :class ::program)

(definterface fn-store-sco-last-record-octets
  :class ::program)

(definterface fn-store-sco-log-position
  :class ::program)

(definterface fn-store-sco-observed-count
  :class ::program)

(definterface fn-store-sco-pass-begin
  :class ::program)

(definterface fn-store-sco-pass-step
  :class ::program)

(definterface fn-store-sco-prefix-octets-range
  :class ::program)

(definterface fn-store-sco-segment-admit
  :class ::program)

; S045: the staged checkpoint read back before its rename
; (host/native/io.lisp fnn-state-checkpoint-verify).
(definterface fn-sccv-initial
  :class :common-lisp-compliant)

(definterface fn-sccv-step
  :class :common-lisp-compliant
  :keystones (fn-sccv-step-is-seg-step))

(definterface fn-sccv-final
  :class :common-lisp-compliant
  :keystones (fn-sccv-final-ok-is-runs-ok))

(definterface fn-store-sco-segment-header-octets
  :class ::program)

(definterface fn-store-sco-segment-read-bound
  :class ::program)

(definterface fn-store-sco-select
  :class ::program)

(definterface fn-store-sco-trailer-octets
  :class ::program)

(definterface fn-store-sn-article-count
  :class ::program)

(definterface fn-store-sn-article-verdict-word
  :class ::program)

(definterface fn-store-sn-existing-action
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp) (payload fn-cbor-octet-listp)))

(definterface fn-store-sn-finish
  :class ::program)

(definterface fn-store-sn-group-next
  :class ::program)

(definterface fn-store-sn-headroom
  :class ::program)

(definterface fn-store-sn-io
  :class ::program)

(definterface fn-store-sn-known-abort
  :class ::program)

(definterface fn-store-sn-lookup
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp)))

(definterface fn-store-sn-lookup-foundp
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp)))

(definterface fn-store-sn-next-txid
  :class ::program)

(definterface fn-store-sn-pending-octets
  :class ::program)

(definterface fn-store-sn-pending-sequence
  :class ::program)

(definterface fn-store-sn-pin-count
  :class ::program)

(definterface fn-store-sn-prepare
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp) (payload fn-cbor-octet-listp) (id-octets fn-cbor-octet-listp) (subject-octets fn-cbor-octet-listp) (evidence-octets fn-cbor-octet-listp)))

(definterface fn-store-sn-recover-from-checkpoint
  :class ::program
  :kinds ((config-octet-records fn-octet-list-listp)))

(definterface fn-store-sn-recover-records
  :class ::program
  :kinds ((octet-records fn-octet-list-listp) (config-octet-records fn-octet-list-listp)))

(definterface fn-store-sn-recover-rows
  :class ::program
  :kinds ((config-octet-records fn-octet-list-listp)))

(definterface fn-store-sn-refuse-reservation
  :class ::program)

(definterface fn-store-sn-replay-digest-report
  :class ::program)

(definterface fn-store-sn-reserved
  :class ::program)

(definterface fn-store-sn-reset
  :class ::program)

(definterface fn-store-sn-staging-observation-limit
  :class ::program)

(definterface fn-store-sn-sweep-round
  :class ::program)

(definterface fn-store-subject-id-of-payload
  :class ::ideal)

(definterface fn-sxd-archive-verdict
  :class ::common-lisp-compliant)

(definterface fn-sxi-final
  :class ::common-lisp-compliant)

(definterface fn-sxi-head
  :class ::common-lisp-compliant)

(definterface fn-sxi-same-verdict
  :class ::common-lisp-compliant)

(definterface fn-sxi-st-mm
  :class ::common-lisp-compliant)

(definterface fn-sxi-start
  :class ::common-lisp-compliant)

(definterface fn-sxi-step
  :class ::common-lisp-compliant)

(definterface fn-sxi-want
  :class ::common-lisp-compliant)

(definterface fn-sxp-export-chunk
  :class ::common-lisp-compliant)

(definterface fn-sxp-export-head
  :class ::common-lisp-compliant)

; -----------------------------------------------------------------------------
; owner (190 entries)

(definterface fn-acct-host-owner-redeem-waitingp
  :class ::program)

(definterface fn-ocs-class-index
  :class ::common-lisp-compliant)

(definterface fn-ocs-classp
  :class ::common-lisp-compliant)

(definterface fn-ocs-commit-step
  :class ::common-lisp-compliant)

(definterface fn-ocs-member-releases
  :class ::common-lisp-compliant)

(definterface fn-ocs-publication-class
  :class ::common-lisp-compliant)

(definterface fn-ocs-start-event
  :class ::common-lisp-compliant
  :keystones (fn-ocs-unstaged-start-tells-its-refusals
              fn-ocp-unstaged-start-issues-no-sync))

(definterface fn-ocs-told-at-drain-p
  :class ::common-lisp-compliant
  :keystones (fn-ocs-told-at-drain-p-by-definition))

(definterface fn-ores-feed-publication-p
  :class ::common-lisp-compliant
  :keystones (fn-ores-submission-resolution-publication-is-well-formed
              fn-ores-submission-intent-publication-is-well-formed
              fn-ores-feed-port-publication-p-without-effects
              fn-ofa-publication-is-well-formed))

(definterface fn-ores-feedpub-command
  :class ::common-lisp-compliant)

(definterface fn-ores-feedpub-log-line
  :class ::common-lisp-compliant)

(definterface fn-ores-feedpub-plan
  :class ::common-lisp-compliant)

(definterface fn-ores-feedpub-word
  :class ::common-lisp-compliant)

(definterface fn-ores-submission-taken-p
  :class ::common-lisp-compliant)

(definterface fn-ores-taken-groups
  :class ::common-lisp-compliant)

(definterface fn-ores-taken-id
  :class ::common-lisp-compliant)

(definterface fn-ores-taken-msgid
  :class ::common-lisp-compliant)

(definterface fn-ores-taken-octets
  :class ::common-lisp-compliant)

(definterface fn-ores-taken-word
  :class ::common-lisp-compliant)

(definterface fn-osd-drain-next
  :class ::common-lisp-compliant
  :keystones (fn-osd-drain-stops-by-the-deadline
              fn-osd-drain-next-step-unfolds))

(definterface fn-osd-log-line
  :class ::common-lisp-compliant)

(definterface fn-osd-poll-ms
  :class ::common-lisp-compliant)

(definterface fn-otb-answer-early
  :class ::common-lisp-compliant
  :keystones (fn-otb-answer-early-answers-each-untold-member-once))

(definterface fn-otb-issue
  :class ::common-lisp-compliant)

(definterface fn-otb-ledger-init
  :class ::common-lisp-compliant)

(definterface fn-oqw-start
  :class :common-lisp-compliant
  :keystones (fn-oqw-batch-effect-order))

(definterface fn-oqw-step
  :class :common-lisp-compliant
  ;; Batch order is a theorem of the START/TRACE/FINAL composition above;
  ;; this entry's literal host-called subject is the individual STEP.
  :keystones (fn-oqw-a-failed-effect-ends-the-job))

(definterface fn-oqw-receipt
  :class :common-lisp-compliant
  :keystones (fn-oqw-receipt-outcomes-are-distinct))

;; RECEIPT's distinct-outcomes theorem names RECEIPT, not this projection.
;; The projection's separate boundary claim remains PRF-393/1255 debt.
(definterface fn-oqw-outcome-of-final
  :class :common-lisp-compliant)


(definterface fn-own-intent-refusal-word
  :class ::common-lisp-compliant
  :keystones (fn-own-intent-refusal-word-is-a-refusal))

(definterface fn-owner-account-outcome
  :class ::program)

(definterface fn-owner-app-bind-receipt-store
  :class ::program)

(definterface fn-owner-app-current-generation
  :class ::program)

(definterface fn-owner-app-refusal-log
  :class ::program)

(definterface fn-owner-app-unbind-receipt-store
  :class ::program)

(definterface fn-owner-barrier-limits
  :class :common-lisp-compliant)

(definterface fn-owner-bound-commit-gate
  :class :common-lisp-compliant
  :kinds ((group-octets fn-octet-list-listp)))

(definterface fn-owner-bp-receipt-gatep
  :class ::program)

(definterface fn-owner-bp-receipt-release-detail
  :class ::program)

(definterface fn-owner-bp-receipt-release-record
  :class ::program)

(definterface fn-owner-bp-receipt-signature-plan
  :class ::program)

(definterface fn-owner-bp-release-line
  :class ::program)

(definterface fn-owner-bp-request-refusal-line
  :class ::program)

(definterface fn-owner-bp-request-trustedp
  :class ::program)

(definterface fn-owner-bp-route-table
  :class ::program)

(definterface fn-owner-bp-source-decision-line
  :class ::program)

(definterface fn-owner-bp-tcpcl-ingress
  :class ::program)

(definterface fn-owner-bp-transit-outcome
  :class ::program)

(definterface fn-owner-bp-transit-raw
  :class :common-lisp-compliant)

(definterface fn-owner-cat-prepare-sealed
  :class :common-lisp-compliant)

; host/native/owner.lisp asks it before the POST's seal (lane arena-forget).
(definterface fn-owner-cat-may-seal
  :class :common-lisp-compliant)
; Its named host wrapper equality is -by-definition. The old Boolean gate
; restatement is not a prepare-transition keystone; that relation remains owed.

(definterface fn-owner-catchup-plans
  :class :common-lisp-compliant)

(definterface fn-owner-cfg-native-admin-authorize-carried
  :class :common-lisp-compliant
  :kinds ((record-octets fn-cbor-octet-listp))
  :keystones ((fn-olau-authorize-carried-is-the-observed-authorization
               :via fn-olau-authorize-carried)))

(definterface fn-owner-cfg-next-name
  :class :common-lisp-compliant)

(definterface fn-owner-checkpoint-clone-phase
  :class :common-lisp-compliant
  :kinds ((marker-octets fn-cbor-octet-listp)))

(definterface fn-owner-clock-observation
  :class :common-lisp-compliant)

(definterface fn-owner-close
  :class :common-lisp-compliant)

(definterface fn-owner-compress-min-octets
  :class :common-lisp-compliant)

(definterface fn-owner-config-generation
  :class :common-lisp-compliant)

(definterface fn-owner-config-served
  :class ::program)

(definterface fn-owner-connection-budget
  :class ::program)

(definterface fn-owner-consumer-local-ack
  :class :common-lisp-compliant
  :kinds ((cursor-octets fn-cbor-octet-listp)))

(definterface fn-owner-consumer-local-bootstrap
  :class :common-lisp-compliant)

(definterface fn-owner-consumer-local-bound-ack
  :class ::program
  :kinds ((cursor-octets fn-cbor-octet-listp)))

(definterface fn-owner-consumer-local-bound-poll
  :class ::program)

(definterface fn-owner-consumer-local-poll
  :class ::program)

(definterface fn-owner-consumer-local-position
  :class :common-lisp-compliant)

(definterface fn-owner-consumer-local-register
  :class ::program)

(definterface fn-owner-consumer-local-status
  :class :common-lisp-compliant)

(definterface fn-owner-consumer-local-unregister
  :class :common-lisp-compliant)

(definterface fn-owner-consumer-local-wait-admit
  :class :common-lisp-compliant)

(definterface fn-owner-consumer-local-wait-step
  :class ::program)

(definterface fn-owner-credits-batch-done
  :class ::program)

(definterface fn-owner-credits-seal
  :class ::program)

(definterface fn-owner-credits-settle
  :class ::program)

(definterface fn-owner-credits-stop
  :class ::program)

(definterface fn-owner-domain
  :class ::program)

(definterface fn-owner-exposure-charge
  :class ::program)

(definterface fn-owner-exposure-idle
  :class ::program)

(definterface fn-owner-exposure-install-set
  :class :common-lisp-compliant)

(definterface fn-owner-exposure-open
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp))
  :keystones ((fn-olog-socket-connection-line-is-one-line :via fn-olog-socket-connection-line)))

(definterface fn-owner-exposure-progress
  :class ::program
  :keystones ((fn-exp-idle-keeps-after-progress :via fn-exp-progress)))

(definterface fn-owner-exposure-release
  :class ::program)

(definterface fn-owner-fault
  :class :common-lisp-compliant)

(definterface fn-owner-feed-auth-policy
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-backoff-ms
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-send-quantum
  :class ::common-lisp-compliant)

(definterface fn-owner-feed-connect-timeout
  :class :common-lisp-compliant)

(definterface fn-owner-feed-dial-open
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-has-queued
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-host
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-journal-begin
  :class :common-lisp-compliant)

(definterface fn-owner-feed-journal-offset
  :class :common-lisp-compliant)

(definterface fn-owner-feed-journal-prefix-size
  :class :common-lisp-compliant)

(definterface fn-owner-feed-journal-scan
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp) (frame fn-cbor-octet-listp)))

(definterface fn-owner-feed-port
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-profile-decode
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-profile-max-octets
  :class :common-lisp-compliant)

(definterface fn-owner-feed-read-limit
  :class :common-lisp-compliant)

(definterface fn-owner-feed-reconcile-apply
  :class ::program)

(definterface fn-owner-feed-reply-chunk
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp) (octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-security
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-tls-established
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-finish
  :class :common-lisp-compliant)

(definterface fn-owner-finish-identity
  :class ::program)

(definterface fn-owner-finish-submission
  :class ::program)

(definterface fn-owner-group-codes
  :class ::program
  :kinds ((name-octets fn-octet-list-listp)))

(definterface fn-owner-hybrid-current-enrollment
  :class :common-lisp-compliant)

(definterface fn-owner-hybrid-snapshots
  :class :common-lisp-compliant)

(definterface fn-owner-identity-publication-verdict
  :class ::program)

(definterface fn-owner-install-node-secret
  :class :common-lisp-compliant)

(definterface fn-owner-install-profile
  :class ::program)

(definterface fn-owner-io
  :class :common-lisp-compliant
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

;; The POST's take (host/native/owner.lisp fnn-owner-take).  Undeclared until
;; lane post-guard-off: the raw host reached it through fnn-owner-result,
;; which the host reading does not see, so it now dispatches it through
;; fnn-owner-core and checks the result's recognizer itself.
(definterface fn-owner-take
  :class :common-lisp-compliant
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-key-statement-event
  :class ::program)

(definterface fn-owner-key-statement-log-line
  :class :common-lisp-compliant)

(definterface fn-owner-key-statement-pending
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-owner-key-statement-plan
  :class ::program)

(definterface fn-owner-key-statement-redecide-event
  :class ::program)

(definterface fn-owner-key-statement-redecide-find
  :class ::program)

(definterface fn-owner-key-statement-redecide-log-line
  :class :common-lisp-compliant)

(definterface fn-owner-key-statement-redecide-plan
  :class ::program)

(definterface fn-owner-key-statement-request
  :class :common-lisp-compliant)

(definterface fn-owner-known-abort
  :class :common-lisp-compliant
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-limit-carried
  :class ::program)

(definterface fn-owner-limit-decided
  :class ::program)

(definterface fn-owner-live-post-config
  :class :common-lisp-compliant)

(definterface fn-owner-log-bounds
  :class :common-lisp-compliant)

(definterface fn-owner-log-reopen
  :class :common-lisp-compliant)

(definterface fn-owner-login-bindings-plan
  :class :common-lisp-compliant)

(definterface fn-owner-login-gate-buffer
  :class :common-lisp-compliant
  :keystones ((fn-ars-lb-ocfg-gate-is-reference :via fn-ars-lb-ocfg-gate)))

(definterface fn-owner-moderation-plan
  :class :common-lisp-compliant)

(definterface fn-owner-next-store-coordinates
  :class :common-lisp-compliant)

(definterface fn-owner-next-txid
  :class :common-lisp-compliant)

(definterface fn-owner-observe
  :class :common-lisp-compliant)

(definterface fn-owner-open
  :class :common-lisp-compliant)

(definterface fn-owner-open-peer
  :class :common-lisp-compliant
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-operator-refusal-reason
  :class :common-lisp-compliant
  :kinds ((msgid-octets fn-cbor-octet-listp) (group-octets fn-octet-list-listp) (payload fn-cbor-octet-listp)))

(definterface fn-owner-outcome
  :class ::program)

(definterface fn-owner-peer-carried-relay-event
  :class ::program)

(definterface fn-owner-peer-carrier-form-buffer
  :class :common-lisp-compliant
  :keystones ((fn-ars-carrier-form-is-reference :via fn-ars-carrier-form)))

(definterface fn-owner-peer-carrier-plan
  :class ::program)

(definterface fn-owner-peer-for-socket-address
  :class ::program)

(definterface fn-owner-pending-octets
  :class :common-lisp-compliant)

(definterface fn-owner-pending-sequence
  :class :common-lisp-compliant)

(definterface fn-owner-post-boundary
  :class ::program
  :kinds ((msgid-octets fn-cbor-octet-listp) (payload-length natp)))

(definterface fn-owner-posting-configure
  :class ::program)

(definterface fn-owner-prepare-consumer
  :class :common-lisp-compliant
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-prepare-identity
  :class :common-lisp-compliant
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-prepare-retention
  :class :common-lisp-compliant
  :kinds ((id-octets fn-cbor-octet-listp) (subject-octets fn-cbor-octet-listp) (evidence-octets fn-cbor-octet-listp))
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-prepare-topic
  :class :common-lisp-compliant
  ;; RAW: its guard walks the whole Store (fn-sn-statep); raw dispatch over
  ;; host/owner-served-carried.lisp's row, under A-OWNER-INVARIANT-CARRIED
  ;; (specs/failures.md: the writers that row owes are unproved).
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-prov-post
  :class :common-lisp-compliant)

(definterface fn-owner-publication-verdict
  :class ::program)

(definterface fn-owner-pull-plans
  :class :common-lisp-compliant)

(definterface fn-owner-queue-head-served-p
  :class :common-lisp-compliant)

(definterface fn-owner-read-octets
  :class ::program)

(definterface fn-owner-reader-views-capture
  :class ::program)

(definterface fn-owner-reconfigure-authorizedp
  :class :common-lisp-compliant)

(definterface fn-owner-reconfigure-complete
  :class ::program)

(definterface fn-owner-reconfigure-unstage
  :class :common-lisp-compliant)

(definterface fn-owner-recover-from-store-open
  :class ::program)

(definterface fn-owner-refuse-reservation
  :class :common-lisp-compliant
  :raw-with (:carried fn-owner-served-carried :assuming A-OWNER-INVARIANT-CARRIED))

(definterface fn-owner-sco-capture
  :class ::program)

; host/native/admin.lisp dispatches it (lane operability-7, row S3b).
(definterface fn-owner-oex-capture
  :class ::program)

; host/native/owner.lisp dispatches it (lane operability-7, row S3b).
(definterface fn-store-sco-encode-chunk
  :class ::program)

(definterface fn-owner-sco-due
  :class ::program)

(definterface fn-owner-sco-note-base-payloads
  :class :common-lisp-compliant)

(definterface fn-owner-sco-note-durable
  :class :common-lisp-compliant)


(definterface fn-owner-sco-publication-done
  :class :common-lisp-compliant)

(definterface fn-owner-sco-request
  :class ::program)

(definterface fn-owner-served-carried-word
  :class :common-lisp-compliant)

(definterface fn-owner-served-post-word
  :class :common-lisp-compliant)

(definterface fn-owner-set-auth-config
  :class :common-lisp-compliant)

(definterface fn-owner-shed-outcome
  :class ::program)

(definterface fn-owner-signed-event-boundary
  :class ::program)

(definterface fn-owner-snapshot
  :class :common-lisp-compliant)

(definterface fn-owner-space-need
  :class :common-lisp-compliant)

(definterface fn-owner-stamp-status
  :class :common-lisp-compliant)

(definterface fn-owner-statement-fence
  :class :common-lisp-compliant)

(definterface fn-owner-tls-established
  :class ::program)

(definterface fn-owner-topic-propose
  :class :common-lisp-compliant)

(definterface fn-owner-transit-decide
  :class ::program
  :kinds ((id-octets fn-cbor-octet-listp) (subject-octets fn-cbor-octet-listp)))

(definterface fn-owner-transit-evidence
  :class :common-lisp-compliant)

(definterface fn-owner-transit-log-line
  :class :common-lisp-compliant)

(definterface fn-owner-transit-outcome
  :class ::program)

(definterface fn-owner-transit-reason
  :class :common-lisp-compliant)

(definterface fn-owner-transit-refusal-class
  :class ::program)

(definterface fn-owner-transit-verdict
  :class ::program)

(definterface fn-owner-transit-verdict-buffer
  :class :common-lisp-compliant
  :keystones ((fn-ars-transit-verdict-is-reference :via fn-ars-transit-verdict)))

(definterface fn-owner-workflow-forward-pinnedp
  :class ::program)

; host/native/bp-obligation.lisp dispatches it (lane reclaim-retention).
(definterface fn-owner-workflow-request-plan
  :class ::program)

(definterface fn-owner-workflow-store-release
  :class ::program)

(definterface fn-owner-workflow-store-undertake
  :class ::program)

(definterface fn-owner-workflow-sync-store-node
  :class ::program)

(definterface fn-splan-donep
  :class ::common-lisp-compliant)

(definterface fn-splan-step-closep
  :class ::common-lisp-compliant)

(definterface fn-splan-step-consumed
  :class ::common-lisp-compliant)

(definterface fn-splan-step-exposure-close
  :class ::common-lisp-compliant)

(definterface fn-splan-step-handshake-owed
  :class ::common-lisp-compliant)

(definterface fn-splan-step-p
  :class ::common-lisp-compliant)

(definterface fn-splan-step-refusal-lines
  :class ::common-lisp-compliant)

(definterface fn-splan-step-submittedp
  :class ::common-lisp-compliant)

(definterface fn-splan-window
  :class ::common-lisp-compliant
  :kinds ((w natp))
  :keystones (fn-splan-window-is-a-prefix-of-the-reply))

(definterface fn-splan-at-cursorp
  :class ::common-lisp-compliant
  :keystones (fn-splan-window-size-is-positive-until-done))

(definterface fn-splan-cursor-step
  :class ::common-lisp-compliant
  :kinds ((w natp))
  ;; The keystone must call the entry: this one does (fn-splan-cw-drain-is-the-
  ;; expanded-reply calls it only through fn-splan-cw-drain; hbox host-ld at
  ;; 899634977 refused that).
  :keystones (fn-splan-cursor-step-keeps-cw-remaining))

(definterface fn-splan-cursor-window
  :class ::common-lisp-compliant)

(definterface fn-splan-cursor-resume-ms
  :class ::common-lisp-compliant)

(definterface fn-splan-window-size
  :class ::common-lisp-compliant
  :keystones (fn-splan-window-size-is-positive-until-done))

; -----------------------------------------------------------------------------
; nntp/served (21 entries)

(definterface fn-cbud-tls-refusal-line
  :class ::common-lisp-compliant)

(definterface fn-native-auth-host-config
  :class ::program)

(definterface fn-native-auth-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-auth-host-load-bindings
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-auth-host-max-octets
  :class ::program)

(definterface fn-native-auth-host-reason
  :class ::program)

(definterface fn-native-auth-host-status
  :class ::program)

(definterface fn-splan-step-plan
  :class ::common-lisp-compliant
  :keystones (fn-splan-step-plan-remaining))

(definterface fn-tlsr-host-acceptp
  :class ::program)

(definterface fn-tlsr-host-decide
  :class ::program)

(definterface fn-tlsr-host-facts
  :class ::program)

(definterface fn-tlsr-host-log-line
  :class ::program)

(definterface fn-tlsr-host-refusal
  :class ::program)

(definterface fn-tlsr-host-reply-line
  :class ::program)

(definterface fn-tlsr-host-reply-read
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tlsr-host-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tlsr-host-request-encode
  :class ::program)

(definterface fn-tlsr-host-start-decide
  :class ::program)

(definterface fn-tlsr-host-start-refusal-line
  :class ::program)

(definterface fn-tlsr-host-status-client-line
  :class ::program)

(definterface fn-wire-event-kind
  :class ::common-lisp-compliant)

; -----------------------------------------------------------------------------
; peer/feed (88 entries)

(definterface fn-anchor-host-accept
  :class ::program)

(definterface fn-anchor-host-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-anchor-host-frame-limit
  :class ::program)

(definterface fn-anchor-host-protected
  :class ::program)

(definterface fn-anchor-rp-action
  :class ::common-lisp-compliant)

(definterface fn-anchor-rp-outcome
  :class ::common-lisp-compliant
  :keystones (fn-anchor-rp-outcome-is-terminal-only-after-the-directory-barrier))

(definterface fn-anchor-rp-recover-start
  :class ::common-lisp-compliant)

(definterface fn-anchor-rp-start
  :class ::common-lisp-compliant)

(definterface fn-anchor-rp-step
  :class ::common-lisp-compliant)

(definterface fn-anchor-server-host-select
  :class ::program
  :kinds ((name-octets fn-cbor-octet-listp)))

(definterface fn-anchor-wire-host-parse
  :class ::program)

(definterface fn-anchor-wire-host-request
  :class ::program)

(definterface fn-cu-fresh-cursor
  :class ::common-lisp-compliant)

(definterface fn-cu-journal-prefix-size
  :class ::common-lisp-compliant)

(definterface fn-cu-records-replay
  :class ::common-lisp-compliant
  :keystones (fn-cu-resume-asks-from-the-journaled-cursor
              fn-cu-records-replay-is-the-last-cursor))

(definterface fn-cu-session-begin-pair
  :class ::common-lisp-compliant)

(definterface fn-cu-session-log-line
  :class ::common-lisp-compliant)

(definterface fn-cu-session-step-pair
  :class ::common-lisp-compliant)

(definterface fn-feed-filename-host-component
  :class ::program)

(definterface fn-feed-filename-host-count
  :class ::program)

(definterface fn-feed-filename-host-decode
  :class ::program)

(definterface fn-feed-filename-host-max-components
  :class ::program)

(definterface fn-feed-filename-host-max-v1-chunks
  :class ::program)

(definterface fn-feed-filename-host-observation-limit
  :class ::program)

(definterface fn-feed-filename-host-observation-remaining
  :class ::program)

(definterface fn-feed-filename-host-okp
  :class ::program)

(definterface fn-feed-journal-phase-step
  :class ::common-lisp-compliant)

(definterface fn-feed-journal-prefix
  :class ::common-lisp-compliant)

(definterface fn-feed-journal-wrap
  :class ::common-lisp-compliant)

(definterface fn-flb-drop-line
  :class ::common-lisp-compliant)

(definterface fn-flb-lost
  :class ::common-lisp-compliant)

(definterface fn-flb-ready
  :class ::common-lisp-compliant)

(definterface fn-hsig-authorized-injected-carried-submission-event
  :class ::common-lisp-compliant
  :keystones (fn-hsig-authorized-injected-carried-submission-event-decides))

(definterface fn-hsig-host-authored-source-fields
  :class ::program)

(definterface fn-hsig-host-authored-source-id
  :class ::program)

(definterface fn-hsig-host-authorize
  :class ::program)

(definterface fn-hsig-host-keyring-snapshot-octets
  :class ::program)

(definterface fn-hsig-host-max-preimage-octets
  :class ::program)

(definterface fn-hsig-host-max-received-octets
  :class ::program)

(definterface fn-hsig-host-max-source-octets
  :class ::program)

(definterface fn-hsig-host-preimage
  :class ::program)

(definterface fn-hsig-host-received-carrier-plan
  :class ::program)

(definterface fn-hsig-host-render-carrier
  :class ::program)

(definterface fn-hsig-injected-carrier-octets
  :class ::common-lisp-compliant)

(definterface fn-hsig-injected-carrier-reason
  :class ::common-lisp-compliant)

(definterface fn-jpub-host-action
  :class ::ideal)

(definterface fn-jpub-host-authorized-initialp
  :class ::ideal)

(definterface fn-jpub-host-outcome
  :class ::ideal)

(definterface fn-jpub-host-phase
  :class ::ideal)

(definterface fn-jpub-host-step
  :class ::ideal)

(definterface fn-jpub-host-terminalp
  :class ::ideal)

(definterface fn-peer-dial-log-line
  :class ::common-lisp-compliant)

(definterface fn-peer-dial-target
  :class ::common-lisp-compliant
  :keystones (fn-peer-dial-target-decides-the-path))

(definterface fn-peer-tls-verification
  :class ::common-lisp-compliant
  :keystones (fn-peer-tls-verification-sni-is-never-a-literal
              fn-peer-tls-verification-selects-one-check))

(definterface fn-pinv-host-bindings-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-pinv-host-bindings-request-encode
  :class ::program)

(definterface fn-pinv-host-confirm-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-pinv-host-confirm-request-encode
  :class ::program)

(definterface fn-pinv-host-genesis-principal
  :class ::program)

(definterface fn-pinv-host-invitation-source
  :class ::program)

(definterface fn-pinv-host-kind
  :class ::program)

(definterface fn-pinv-host-observation-subject
  :class ::program)

(definterface fn-pinv-host-owner-invitations
  :class ::program)

(definterface fn-pinv-host-owner-peers
  :class ::program)

(definterface fn-pinv-host-redecide-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-pinv-host-redecide-request-encode
  :class ::program)

(definterface fn-pinv-host-request-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-pinv-host-request-encode
  :class ::program)

(definterface fn-pull-fresh-cursor
  :class ::common-lisp-compliant)

(definterface fn-pull-journal-prefix-size
  :class ::common-lisp-compliant)

(definterface fn-pull-plan-for
  :class ::common-lisp-compliant)

(definterface fn-pull-plan-host
  :class ::common-lisp-compliant)

(definterface fn-pull-plan-peer
  :class ::common-lisp-compliant)

(definterface fn-pull-plan-port
  :class ::common-lisp-compliant)

(definterface fn-pull-plan-profile-path
  :class ::common-lisp-compliant)

(definterface fn-pull-records-replay
  :class ::common-lisp-compliant
  :keystones (fn-pull-records-replay-is-the-replay
              fn-pull-records-replay-ignores-an-uncommitted-tail))

(definterface fn-pull-schedule
  :class ::common-lisp-compliant)

(definterface fn-pull-session-begin-pair
  :class ::common-lisp-compliant)

(definterface fn-pull-session-log-line-why
  :class ::common-lisp-compliant)

(definterface fn-pull-session-step-triple
  :class ::common-lisp-compliant)

(definterface fn-redeem-lost
  :class ::common-lisp-compliant
  :keystones (fn-redeem-lost-is-fenced-and-server-answers-are-not))

(definterface fn-redeem-outcome-class
  :class ::common-lisp-compliant
  :keystones (fn-redeem-lost-is-fenced-and-server-answers-are-not))

(definterface fn-redeem-step
  :class ::common-lisp-compliant)

(definterface fn-redeem-text
  :class ::common-lisp-compliant)

(definterface fn-sched-pull-due
  :class ::common-lisp-compliant
  :keystones (fn-sched-pull-due-is-due-and-idle))

(definterface fn-sched-pull-finish
  :class ::common-lisp-compliant
  :keystones (fn-sched-pull-finished-waits-its-interval))

(definterface fn-sched-pull-start
  :class ::common-lisp-compliant
  :keystones (fn-sched-pull-started-is-not-due))

(definterface fn-th-select-verified-source
  :class ::common-lisp-compliant)

; -----------------------------------------------------------------------------
; bp (243 entries)

(definterface fn-aj-initializedp
  :class ::ideal)

(definterface fn-bpah-handoff-report
  :class ::common-lisp-compliant
  :keystones (fn-bpah-handoff-report-is-application-disposition))

(definterface fn-bpah-outbox-effective-status
  :class ::common-lisp-compliant)

(definterface fn-bpah-outbox-peer-matchp
  :class ::common-lisp-compliant)

(definterface fn-bpah-outbox-view-after
  :class ::common-lisp-compliant)

(definterface fn-bpah-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpah-publication-authorize-admits-exactly-the-issued-pending-delivery))

(definterface fn-bpah-publication-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpah-publication-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpah-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpah-publication-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpaj-eid-text
  :class ::common-lisp-compliant)

(definterface fn-bpapp-receive
  :class ::program)

(definterface fn-bpapp-receive-adu
  :class ::program)

(definterface fn-bpapp-receive-destination
  :class ::program)

(definterface fn-bpapp-receive-identity
  :class ::program)

(definterface fn-bpapp-receive-outcome
  :class ::program)

(definterface fn-bpapp-receive-reason
  :class ::program)

(definterface fn-bpapp-receive-source
  :class ::program)

(definterface fn-bpb-payload
  :class ::common-lisp-compliant)

(definterface fn-bpcc-journal-config
  :class ::common-lisp-compliant)

(definterface fn-bpcd-final-name
  :class ::common-lisp-compliant)

(definterface fn-bpcd-frame-limit
  :class ::common-lisp-compliant)

(definterface fn-bpfs-fragment-outcome
  :class ::common-lisp-compliant
  :keystones (fn-bpfs-fragment-outcome-refines-ordered-send)
  :kinds ((index natp)))

(definterface fn-bpfs-plan
  :class ::common-lisp-compliant
  :keystones (fn-bpfs-plan-fragments-restore-parent
              fn-bpfs-plan-fragments-reassemble-within-caps
              fn-bpfs-plan-fragments-reassemble-uncapped
              fn-bpfs-plan-fragments-reassemble-exactly
              fn-bpfs-plan-fragments-fit-mru))

(definterface fn-bphp-recover-auto-event
  :class ::common-lisp-compliant
  :keystones (fn-bphp-recover-auto-event-is-bpnr))

(definterface fn-bprpf-row-admit
  :class ::common-lisp-compliant
  :keystones (fn-bprpf-admitted-row-has-bounded-adu))

(definterface fn-bprpf-selection-admit
  :class ::common-lisp-compliant
  :keystones (fn-bprpf-admitted-checkpoint-bounds-every-held-adu))

(definterface fn-bprpf-admit-recovery
  :class ::common-lisp-compliant
  :keystones (fn-bprpf-ready-recovery-bounds-every-held-adu))

(definterface fn-bpn-host-authored-retry
  :class ::ideal)

(definterface fn-bpn-host-authored-wire-authorize
  :class ::ideal
  :delegates fn-bpn-authored-wire-authorize)

(definterface fn-bpn-host-authored-wire-name
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-authored-wire-name-names-the-reserved-sequence))

(definterface fn-bpn-host-authored-wire-operation-label
  :class ::ideal)

(definterface fn-bpn-host-authored-wire-operation-name
  :class ::ideal)

(definterface fn-bpn-host-authored-wire-operation-publication
  :class ::ideal)

(definterface fn-bpn-host-authored-wire-operation-wire
  :class ::ideal)

(definterface fn-bpn-host-authored-wire-operationp
  :class ::ideal)

(definterface fn-bpn-host-config
  :class ::ideal)

(definterface fn-bpn-host-eid
  :class ::ideal)

(definterface fn-bpn-host-evidence-authorize
  ; an exact alias; the callee's keystone is PRF-1007
  ; (fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity)
  :class ::common-lisp-compliant
  :delegates fn-bpn-evidence-authorize)

(definterface fn-bpn-host-evidence-directory-name
  :class ::ideal)

(definterface fn-bpn-host-evidence-max-entries
  :class ::ideal)

(definterface fn-bpn-host-evidence-next-result-name
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-evidence-next-result-name-names-exactly-the-next-record))

(definterface fn-bpn-host-evidence-next-wire-name
  :class ::ideal)

(definterface fn-bpn-host-evidence-operation-result-name
  :class ::ideal)

(definterface fn-bpn-host-evidence-operation-result-publication
  :class ::ideal)

(definterface fn-bpn-host-evidence-operation-successor
  :class ::ideal)

(definterface fn-bpn-host-evidence-operation-wire-name
  :class ::ideal)

(definterface fn-bpn-host-evidence-operation-wire-publication
  :class ::ideal)

(definterface fn-bpn-host-evidence-operationp
  ; an exact alias of the boolean recognizer; the keystone naming it is
  ; PRF-1007 (fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity)
  :class ::ideal
  :delegates fn-bpn-evidence-operationp)

(definterface fn-bpn-host-evidence-readyp
  :class ::ideal)

(definterface fn-bpn-host-evidence-recover
  :class ::ideal)

(definterface fn-bpn-host-existing-sequence
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence))

(definterface fn-bpn-host-existing-sequence-p
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence))

(definterface fn-bpn-host-existing-sequence-value
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-existing-sequence-reuses-exactly-the-keyed-jobs-sequence))

(definterface fn-bpn-host-lifecycle-frame-limit
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-publication-authorize
  ; an exact alias; the callee's keystone is PRF-985
  ; (fn-bpn-lifecycle-publication-authorize-admits-exactly-the-pending-persist)
  :class ::ideal
  :delegates fn-bpn-lifecycle-publication-authorize)

(definterface fn-bpn-host-lifecycle-publication-operation-publication
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-publication-operation-record
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-publication-operation-token
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-publication-operationp
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-record-frame
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-record-name
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-record-unframe
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-recovery
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-recovery-agrees-p
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-lifecycle-recovery-agrees-with-the-replayed-machine))

(definterface fn-bpn-host-lifecycle-recovery-ready-p
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-recovery-records
  :class ::ideal)

(definterface fn-bpn-host-lifecycle-recovery-stages
  :class ::ideal)

(definterface fn-bpn-host-machine-max-jobs
  :class ::ideal)

(definterface fn-bpn-host-machine-max-octets
  :class ::ideal)

(definterface fn-bpn-host-node-idp
  :class ::ideal)

(definterface fn-bpn-host-observation
  :class ::ideal)

(definterface fn-bpn-host-ready-peers
  :class ::ideal)

(definterface fn-bpn-host-receive
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-receive-keeps-the-three-outcomes-distinct
              fn-bpn-host-receive-of-host-send-hands-over-the-adu))

(definterface fn-bpn-host-receive-adu
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-receive-keeps-the-three-outcomes-distinct
              fn-bpn-host-receive-of-host-send-hands-over-the-adu))

(definterface fn-bpn-host-receive-outcome
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-receive-keeps-the-three-outcomes-distinct
              fn-bpn-host-receive-of-host-send-hands-over-the-adu))

(definterface fn-bpn-host-receive-reason
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-receive-keeps-the-three-outcomes-distinct))

(definterface fn-bpn-host-send
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-receive-of-host-send-hands-over-the-adu))

(definterface fn-bpn-host-sent-summary
  :class ::ideal)

(definterface fn-bpn-host-sequence-frame-limit
  :class ::ideal)

(definterface fn-bpn-host-sequence-frontier
  :class ::ideal)

(definterface fn-bpn-host-sequence-ready-p
  :class ::ideal)

(definterface fn-bpn-host-sequence-recover
  :class ::ideal)

(definterface fn-bpn-host-sequence-reservation-frame
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling))

(definterface fn-bpn-host-sequence-reservation-sequence
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling))

(definterface fn-bpn-host-sequence-reservationp
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling))

(definterface fn-bpn-host-sequence-reserve
  :class ::common-lisp-compliant
  :keystones (fn-bpn-host-sequence-reserve-reserves-exactly-below-the-ceiling))

(definterface fn-bpn-machine-invariantp
  :class ::common-lisp-compliant)

(definterface fn-bpn-nth
  :class ::common-lisp-compliant
  :keystones (fn-bpnr-rotation-crash-recovers-old-or-new
              fn-bpnp-rotate-step-proposes-only-own-projection
              fn-bpah-carrier-without-release-row-releases-nothing))

(definterface fn-bpn-report-job-matchp
  :class ::common-lisp-compliant)

(definterface fn-bpn-report-observe-next
  :class ::common-lisp-compliant
  :keystones (fn-bpn-report-observe-next-selects-exactly-the-least-yielding-row))

(definterface fn-bpn-report-outbox-next
  :class ::common-lisp-compliant
  :keystones (fn-bpn-report-outbox-next-selects-exactly-the-least-yielding-row))

(definterface fn-bpn-report-outbox-peer-matchp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-answer-effects
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-step-emits-no-release-and-no-receipt-prepare))

(definterface fn-bpnf-answer-state
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-step-preserves-guard-premises
              fn-bpnj-step-preserves-guard-premises))

(definterface fn-bpnf-base
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-uncertain-receipt-transfer-keeps-the-job-owed
              fn-bpnp-receipt-reoffer-after-uncertain
              fn-bpnp-receipt-contact-offers-the-queued-job
              fn-bpnp-receipt-contact-event-needs-a-queued-job
              fn-bpnj-contact-offers-while-a-ready-job-remains
              fn-bpnj-step-forwarded-needs-a-durable-finished-record
              fn-bpnj-new-arms-preserve-the-lifecycle-invariant
              fn-bpnj-named-result-is-the-transport-outcome
              fn-bpnj-encoder-refusal-settles-the-pending-record
              fn-bpnj-contact-job-step-preserves-the-base-invariants))

(definterface fn-bpnf-base-job-count
  :class ::common-lisp-compliant)

(definterface fn-bpnf-callback-result
  :class ::common-lisp-compliant)

(definterface fn-bpnf-clock-domain-plan
  :class ::common-lisp-compliant)

(definterface fn-bpnf-clock-domain-plan-frame
  :class ::common-lisp-compliant)

(definterface fn-bpnf-clock-domain-plan-publication
  :class ::common-lisp-compliant)

(definterface fn-bpnf-clock-domain-plan-status
  :class ::common-lisp-compliant)

(definterface fn-bpnf-conflict-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpnf-conflict-publication-success-binds-exact-echo))

(definterface fn-bpnf-conflict-publication-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-conflict-publication-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-conflict-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-conflict-publication-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-delete-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpnf-delete-publication-authorize-admits-exactly-the-issued-pending-deletion))

(definterface fn-bpnf-delete-publication-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-delete-publication-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-delete-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-delete-publication-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-epoch
  :class ::common-lisp-compliant)

;; Q4a increment B: the reassembly job the host carries between steps
;; (books/bp-node-fragment-job, books/bp-node-fragment-step).
(definterface fn-bpfj-next-candidate
  :class ::common-lisp-compliant
  :kinds ((tried true-listp)))

(definterface fn-bpnf-find-arrival
  :class ::common-lisp-compliant)

(definterface fn-bpfj-start
  :class ::common-lisp-compliant)

(definterface fn-bpfj-step
  :class ::common-lisp-compliant
  :kinds ((quantum natp)))

(definterface fn-bpfj-finishedp
  :class ::common-lisp-compliant)

(definterface fn-bpnpf-held-octets
  :class ::common-lisp-compliant)
(definterface fn-bpnf-family-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpnf-family-publication-authorize-admits-exactly-the-issued-pending-family))

(definterface fn-bpnf-family-publication-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-family-publication-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-family-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-family-publication-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-find-held
  :class ::common-lisp-compliant)

(definterface fn-bpnf-held-list
  :class ::common-lisp-compliant)

(definterface fn-bpnf-initial-state
  :class ::common-lisp-compliant)

(definterface fn-bpnf-inspect-readyp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-inspect-value
  :class ::common-lisp-compliant)

(definterface fn-bpnf-mixed-legacy-names
  :class ::common-lisp-compliant
  :kinds ((plan true-listp)))

(definterface fn-bpnf-mixed-legacy-observed
  :class ::common-lisp-compliant)

(definterface fn-bpnf-mixed-received-names
  :class ::common-lisp-compliant
  :kinds ((plan true-listp)))

(definterface fn-bpnf-mixed-recovery-plan
  :class ::common-lisp-compliant)

(definterface fn-bpnf-mixed-recovery-planp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-namespace-max-entries
  :class ::common-lisp-compliant)

(definterface fn-bpnf-publication-authorize
  :class ::common-lisp-compliant)

(definterface fn-bpnf-publication-operation-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-publication-operation-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-publication-operation-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnf-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-receive-wire-event-value
  :class ::common-lisp-compliant)

(definterface fn-bpnf-receive-wire-readyp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-stored-frame-limit
  :class ::common-lisp-compliant)

(definterface fn-bpnf-stored-record-name
  :class ::common-lisp-compliant)

(definterface fn-bpnj-attempt-token
  :class ::common-lisp-compliant)

(definterface fn-bpnj-host-eventp
  :class ::common-lisp-compliant
  :keystones (fn-bpnj-host-refuses-an-unnamed-transport-result))

(definterface fn-bpnj-step
  :class ::common-lisp-compliant
  :keystones (fn-bpnj-step-preserves-guard-premises
              fn-bpnj-step-forwarded-needs-a-durable-finished-record
              fn-bpnj-stale-job-result-settles-nothing))

(definterface fn-bpnjc-contact-close
  :class ::common-lisp-compliant)

(definterface fn-bpnjc-contact-cursor
  :class ::common-lisp-compliant
  :keystones (fn-bpnjc-open-establishes-the-relation))

(definterface fn-bpnjc-contact-next
  :class ::common-lisp-compliant
  :keystones (fn-bpnjc-offer-keeps-the-relation
              fn-bpnjc-contact-next-is-the-head-scan
              fn-bpnjc-ask-position-bounds))

(definterface fn-bpnb-read
  :class ::common-lisp-compliant
  :keystones (fn-bpnb-installed-backoff-refuses-another-backoff
              fn-bpnb-installed-retries-refuses-another-retries
              fn-bpnb-input-past-read-bound-is-refused))

(definterface fn-bpnp-configured-budgets
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-configured-budgets-admits-exactly-the-frame-bounded-positive-budgets))

(definterface fn-bpnp-delivery-view
  :class ::common-lisp-compliant)

(definterface fn-bpnp-dispatch-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-dispatch-publication-authorize-admits-exactly-the-issued-pending-dispatch))

(definterface fn-bpnp-dispatch-publication-frame
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnp-dispatch-publication-name
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnp-dispatch-publication-operationp
  :class ::common-lisp-compliant)

(definterface fn-bpnp-dispatch-publication-publisher
  :class ::common-lisp-compliant
  :kinds ((operation true-listp)))

(definterface fn-bpnp-forward-plan
  :class ::common-lisp-compliant
  :kinds ((held true-listp))
  :keystones (fn-bpnp-forward-plan-offers-a-row-on-one-session
              fn-bpnp-forward-plan-has-one-session-per-peer))

(definterface fn-bpnp-forward-publication-authorize
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward))

(definterface fn-bpnp-forward-publication-name
  :class ::common-lisp-compliant)

(definterface fn-bpnp-forward-publication-octets
  :class ::common-lisp-compliant)

(definterface fn-bpnp-forward-publication-operationp
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward))

(definterface fn-bpnp-forward-publication-publisher
  :class ::common-lisp-compliant)

(definterface fn-bpnp-forward-unrouted
  :class ::common-lisp-compliant
  :kinds ((held true-listp)))

(definterface fn-bpnp-host-routes
  :class ::common-lisp-compliant)

(definterface fn-bpnp-tcpcl-outcome
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-tcpcl-outcome-keeps-sent-refused-failed-and-uncertain-distinct))

(definterface fn-bpnp-used
  :class ::common-lisp-compliant)

(definterface fn-bpnpf-admitted-receive-event
  :class ::common-lisp-compliant
  :keystones (fn-bpnpf-admission-ready-is-within-profile))

(definterface fn-bpnpf-file-name
  :class ::common-lisp-compliant)

(definterface fn-bpnpf-node-profile-base
  :class ::common-lisp-compliant
  :keystones (fn-bpnpf-node-profile-base-is-a-profile))

(definterface fn-bpnpf-node-profile-read
  :class ::common-lisp-compliant
  :keystones (fn-bpnpf-node-profile-read-of-older
              fn-bpnpf-node-profile-read-of-octets
              fn-bpnpf-node-profile-read-is-valid))

(definterface fn-bpnpf-read-bound
  :class ::common-lisp-compliant)

(definterface fn-bpnpf-rotate-records
  :class ::common-lisp-compliant)

(definterface fn-bpnr-checkpoint-octets
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-rotate-step-proposes-only-own-projection))

(definterface fn-bpnr-checkpoint-of-event
  :class ::ideal)

(definterface fn-bpnr-clock-domain-evidence
  :class ::ideal)

(definterface fn-bpnr-depth-budget
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-rotate-step-proposes-only-own-projection))

(definterface fn-bpnr-generation-directory
  :class ::common-lisp-compliant)

(definterface fn-bpnr-next-generation
  :class ::common-lisp-compliant)

(definterface fn-bpnr-plan-directory
  :class ::ideal)

(definterface fn-bpnr-plan-generation
  :class ::ideal)

(definterface fn-bpnr-publish-action
  :class ::common-lisp-compliant)

(definterface fn-bpnr-publish-outcome
  :class ::common-lisp-compliant
  :keystones (fn-bpnr-publish-outcome-is-pending-exactly-while-the-loop-runs
              fn-bpnr-publish-outcome-names-the-stopped-phase))

(definterface fn-bpnr-publish-step
  :class ::common-lisp-compliant)

(definterface fn-bpnr-read-bound
  :class ::common-lisp-compliant)

(definterface fn-bpnr-retire-ops
  :class ::ideal)

(definterface fn-bpnr-retired-names
  :class ::common-lisp-compliant
  :keystones (fn-bpnr-retired-names-never-the-selected-directory))

(definterface fn-bpnr-selection-name
  :class ::common-lisp-compliant)

(definterface fn-bpnrb-selection-plan
  :class ::common-lisp-compliant
  :keystones (fn-bpnrb-selection-plan-is-selection-plan))

(definterface fn-bpnrd-due-rotation-event
  :class ::ideal
  :keystones (fn-bpnrd-due-rotation-event-by-definition))

(definterface fn-bpnrd-serve-rotation-due-p
  :class ::ideal)

(definterface fn-bprc-class
  :class ::common-lisp-compliant
  :keystones (fn-bprc-uncertain-article-fences
              fn-bprc-fence-is-never-masked))

(definterface fn-bprc-decode-exit-code
  :class ::common-lisp-compliant)

(definterface fn-bprc-effect-evidence
  :class ::common-lisp-compliant)

(definterface fn-bprc-empty
  :class ::common-lisp-compliant)

(definterface fn-bprc-note
  :class ::common-lisp-compliant)

(definterface fn-bprc-publication-evidence
  :class ::common-lisp-compliant)

(definterface fn-bprc-run-exit-code
  :class ::common-lisp-compliant
  :keystones (fn-bprc-run-exit-code-is-fenced-iff-fenced))

(definterface fn-bprc-session-evidence
  :class ::common-lisp-compliant)

(definterface fn-bprc-with-articles
  :class ::common-lisp-compliant)

(definterface fn-bprj-apply
  :class ::program)

(definterface fn-bprj-config-status
  :class ::program)

(definterface fn-bprj-install
  :class ::program)

(definterface fn-bprj-pending-receipt-resolution
  :class ::program)

(definterface fn-bprj-preflight
  :class ::program)

(definterface fn-bprj-preview-receipt
  :class ::program)

(definterface fn-bprj-receipt-adu
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-action
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-bound-generation
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-bound-inbound-id
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-planned-result
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-receipt-id
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-result
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-transit-context-record
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-request-transit-intent-record
  :class ::program)

(definterface fn-bprj-request-work-id
  :class ::program
  :kinds ((request-octets fn-cbor-octet-listp)))

(definterface fn-bprj-reset
  :class ::program)

(definterface fn-bprj-valid-config
  :class ::program)

(definterface fn-bprt-job-route
  :class ::common-lisp-compliant)

(definterface fn-bprt-outbound-choice
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-table-route-peer-is-the-routed-hop))

(definterface fn-bpsc-contact-decision
  :class ::common-lisp-compliant)

(definterface fn-bpsc-contact-event
  :class ::common-lisp-compliant)

(definterface fn-bpsc-relative-window
  :class ::common-lisp-compliant)

(definterface fn-bpsr-host-encode
  :class ::common-lisp-compliant)

(definterface fn-bpsr-host-preimage
  :class ::common-lisp-compliant)

(definterface fn-id-hex-octets
  :class ::common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tcl-delivery-plan
  :class ::common-lisp-compliant
  :keystones (fn-tcl-delivery-plan-decides-exactly-by-the-held-final-ack-and-the-callback))

(definterface fn-tcl-delivery-plan-detail
  :class ::common-lisp-compliant)

(definterface fn-tcl-delivery-plan-messages
  :class ::common-lisp-compliant)

(definterface fn-tcl-delivery-plan-progress-p
  :class ::common-lisp-compliant)

(definterface fn-tcl-delivery-plan-status
  :class ::common-lisp-compliant)

(definterface fn-tcl-host-active-closep
  :class ::ideal)

(definterface fn-tcl-host-drive
  :class ::ideal
  :keystones (fn-tcl-host-drive-bundle-has-held-final))

(definterface fn-tcl-host-encode
  ; an exact alias; the callee's keystones are PRF-1006 (the per-kind
  ; fn-tcl-decode-message-of-encode-* round trips and
  ; fn-tcl-accepted-message-is-canonical)
  :class ::ideal
  :delegates fn-tcl-encode)

(definterface fn-tcl-host-event-digests
  :class ::ideal)

(definterface fn-tcl-host-initial
  :class ::ideal)

(definterface fn-tcl-host-keepalive
  :class ::ideal)

(definterface fn-tcl-host-open
  :class ::ideal)

(definterface fn-tcl-host-params
  :class ::ideal)

(definterface fn-tcl-host-paramsp
  :class ::ideal)

(definterface fn-tcl-host-phase
  :class ::ideal)

(definterface fn-tcl-host-pump
  :class ::ideal)

(definterface fn-tcl-host-replay
  :class ::ideal)

(definterface fn-tcl-host-send
  :class ::ideal
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-tcl-host-spool-recovery-plan
  :class ::ideal)

(definterface fn-tcl-host-tcp-closed
  :class ::ideal)

(definterface fn-tcl-host-terminate
  :class ::ideal)

(definterface fn-tcl-host-tick
  :class ::ideal)

(definterface fn-tcl-negotiated-peer-node-id
  :class ::common-lisp-compliant)

(definterface fn-tcl-negotiated-transfer-mtu
  :class ::common-lisp-compliant)

(definterface fn-tcl-session-negotiated
  :class ::common-lisp-compliant)

; -----------------------------------------------------------------------------
; web (21 entries)

(definterface fn-web-host-action-kind
  :class ::program)

(definterface fn-web-host-article-limit
  :class ::program)

(definterface fn-web-host-frame
  :class ::program)

(definterface fn-web-host-head
  :class ::program)

(definterface fn-web-host-limits
  :class ::program)

(definterface fn-web-host-max-events
  :class ::program)

(definterface fn-web-host-parse
  :class ::program)

(definterface fn-web-host-plan
  :class ::program
  :kinds ((config-octets fn-cbor-octet-listp)))

(definterface fn-web-host-plan-address
  :class ::program)

(definterface fn-web-host-plan-config
  :class ::program)

(definterface fn-web-host-plan-family
  :class ::program)

(definterface fn-web-host-plan-port
  :class ::program)

(definterface fn-web-host-plan-refusal
  :class ::program)

(definterface fn-web-host-plan-tls
  :class ::program)

(definterface fn-web-host-plan-web-p
  :class ::program)

(definterface fn-web-host-refusal-body
  :class ::program)

(definterface fn-web-host-refusal-fields
  :class ::program)

(definterface fn-web-host-request-seconds
  :class ::program)

(definterface fn-web-host-reset
  :class ::program)

(definterface fn-web-host-step
  :class ::program
  :keystones ((fn-web-health-step-preserves-sessions-and-bounds-body :via fn-web-step)))

(definterface fn-web-req-clen
  :class ::common-lisp-compliant)

; -----------------------------------------------------------------------------
; admin/operator (175 entries)

(definterface fn-acct-host-code-digest-text
  :class ::ideal
  :kinds ((code-octets fn-cbor-octet-listp)))

(definterface fn-acct-host-code-text
  :class ::ideal)

(definterface fn-acct-host-entropy-octets
  :class ::ideal)

(definterface fn-acct-host-invite-argv
  :class ::ideal)

(definterface fn-acct-host-owner-redeem-log-line
  :class ::program)

(definterface fn-acct-host-owner-redeem-word
  :class ::program)

(definterface fn-acct-host-salt-octets
  :class ::ideal)

(definterface fn-aj-host-authorize
  :class ::ideal)

(definterface fn-aj-host-initial
  :class ::ideal)

(definterface fn-aj-host-max-record-length
  :class ::ideal)

(definterface fn-aj-host-next-name
  :class ::ideal)

(definterface fn-aj-host-operation-label
  :class ::ideal)

(definterface fn-aj-host-operation-name
  :class ::ideal)

(definterface fn-aj-host-operation-publication
  :class ::ideal)

(definterface fn-aj-host-operation-successor
  :class ::ideal)

(definterface fn-aj-host-operationp
  :class ::ideal)

(definterface fn-aj-host-recover
  :class ::ideal)

(definterface fn-bs-profile-resolve
  :class ::common-lisp-compliant
  :keystones (fn-native-mission-profiles-valid
              fn-heap-article-held-meets-the-article-relations))

(definterface fn-cfg-host-initial-octets-at
  :class ::program
  :kinds ((name-octets-list fn-octet-list-listp)))

(definterface fn-cfgc-readback-verdict
  :class ::common-lisp-compliant)

(definterface fn-heap-decision-exit-code
  :class ::common-lisp-compliant
  :keystones (fn-heap-reserve-thread-refusal-exits-1
              fn-heap-decision-exit-code-of-a-refusal))

(definterface fn-heap-history-listing-bound
  :class ::common-lisp-compliant)

(definterface fn-heap-init-budget-note
  :class ::common-lisp-compliant
  :keystones (fn-heap-init-budget-note-only-when-named-below-machine-by-definition
              fn-heap-init-budget-note-names-the-budget-init-sized-for))

(definterface fn-heap-init-budget-note-line
  :class ::common-lisp-compliant)

(definterface fn-heap-init-decide
  :class ::common-lisp-compliant
  :keystones (fn-heap-init-decide-sized-init-is-held
              fn-heap-init-decide-refuses-the-operators-request-past-the-budget
              fn-heap-init-decide-largest-takes-scale-when-it-fits
              fn-heap-init-decide-honors-the-operators-request
              fn-heap-init-decide-fits-the-budget-and-the-machine
              fn-heap-init-decide-conservative-takes-the-top-rung-when-it-fits
              fn-heap-init-decide-conservative-is-a-friend-rung
              fn-heap-init-decide-conservative-holds-the-floor
              fn-heap-init-budget-note-names-the-budget-init-sized-for))

(definterface fn-heap-init-decision-request
  :class ::common-lisp-compliant
  :keystones (fn-heap-init-decide-largest-takes-scale-when-it-fits
              fn-heap-init-decide-conservative-takes-the-top-rung-when-it-fits))

(definterface fn-heap-init-exit-code
  :class ::common-lisp-compliant)

(definterface fn-heap-init-report-line
  :class ::common-lisp-compliant)

(definterface fn-heap-machine-octets
  :class ::common-lisp-compliant
  :keystones (fn-heap-machine-octets-is-at-most-each-observation
              fn-heap-init-budget-is-the-named-below-the-machine))

(definterface fn-heap-mux-loops
  :class ::common-lisp-compliant)

(definterface fn-heap-nursery-trigger
  :class ::common-lisp-compliant)

(definterface fn-heap-open-nursery-trigger
  :class ::common-lisp-compliant
  :keystones (fn-heap-open-nursery-trigger-natp
              fn-heap-open-nursery-trigger-bounds))

(definterface fn-heap-operation-observes-p
  :class ::common-lisp-compliant)

(definterface fn-heap-reserve-init-connections
  :class ::common-lisp-compliant)

(definterface fn-heap-reserve-operation-decide
  :class ::common-lisp-compliant
  :keystones (fn-heap-status-decide-is-the-launchers-run-reservation
              fn-heap-reserve-operation-decide-holds-the-operation))

(definterface fn-crv-extend-reservation
  :class ::common-lisp-compliant
  :keystones (fn-crv-accepted-launch-fits-observed-machine
              fn-crv-accepted-launch-funds-pool-dynamic-allowance))

(definterface fn-orv-extend-reservation
  :class :common-lisp-compliant
  :keystones (fn-orv-accepted-launch-fits-observed-machine
              fn-orv-accepted-launch-funds-output-dynamic-allowance))

(definterface fn-heap-reserve-report-line
  :class ::common-lisp-compliant)

(definterface fn-heap-reserve-run-connections
  :class ::common-lisp-compliant)

(definterface fn-heap-status-decide
  :class ::common-lisp-compliant
  :keystones (fn-heap-status-decide-is-the-launchers-run-reservation))

(definterface fn-heap-thread-count
  :class ::common-lisp-compliant)

(definterface fn-native-admin-host-apply
  :class ::program)

(definterface fn-native-admin-host-clock-observation
  :class ::ideal)

(definterface fn-native-admin-host-clock-stamp
  :class ::ideal)

(definterface fn-native-admin-host-clock-status
  :class ::ideal)

(definterface fn-native-admin-host-config-name
  :class ::ideal)

(definterface fn-native-admin-host-owner-requestp
  :class ::ideal)

(definterface fn-native-admin-host-plan
  :class ::ideal)

(definterface fn-native-admin-host-publication-generation
  :class ::ideal)

(definterface fn-native-admin-host-publication-jpub
  :class ::ideal)

(definterface fn-native-admin-host-publication-name
  :class ::ideal)

(definterface fn-native-admin-host-publication-reason
  :class ::ideal)

(definterface fn-native-admin-host-publication-status
  :class ::ideal)

(definterface fn-native-admin-host-query-report
  :class ::program)

(definterface fn-native-admin-host-queryp
  :class ::ideal)

(definterface fn-native-admin-host-reason
  :class ::ideal)

(definterface fn-native-admin-host-report-kind
  :class ::ideal)

(definterface fn-native-admin-host-status
  :class ::ideal)

(definterface fn-native-config-host-listener-addresses
  :class ::program
  :kinds ((host-octets fn-cbor-octet-listp)))

(definterface fn-native-config-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-config-host-max-octets
  :class ::program)

(definterface fn-native-health-host-last-run
  :class ::program)

(definterface fn-native-health-host-log-tail-octets
  :class ::program)


(definterface fn-native-health-host-not-running-lines
  :class ::program)


(definterface fn-native-health-host-run-started-line
  :class ::program)

(definterface fn-native-health-host-run-opened-line
  :class ::program)

(definterface fn-native-health-host-run-stopped-line
  :class ::program)

(definterface fn-native-health-host-step
  :class ::program)

(definterface fn-native-live-pages-host-answer
  :class ::program)

(definterface fn-native-live-pages-host-client-step
  :class ::program)

(definterface fn-native-live-pages-host-offline-start
  :class ::program)

(definterface fn-native-live-pages-host-offline-step
  :class ::program)

(definterface fn-native-live-pages-host-pagedp
  :class ::program)

(definterface fn-native-live-pages-host-request-encode
  :class ::program)


(definterface fn-native-live-status-host-answer
  :class ::program)

(definterface fn-native-live-status-host-client-step-chunks
  :class ::program)

(definterface fn-native-live-status-host-inspect-group-exit
  :class ::program
  :exempt ((octets "the report's own octets, read back for its exit (fn-oig-report-exit decides 0 or 1 from the report's first word)")))

(definterface fn-native-live-status-host-max-frame
  :class ::program)

(definterface fn-native-live-status-host-max-restarts
  :class ::program)

(definterface fn-native-live-status-host-offline
  :class ::program)

(definterface fn-native-live-status-host-request-encode
  :class ::program)


(definterface fn-native-live-status-host-route
  :class ::program)

(definterface fn-native-operator-host-account-hash-text
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-operator-host-control-outcome
  :class ::program)

(definterface fn-native-operator-host-init-marker-octets
  :class ::program)

(definterface fn-native-operator-host-init-outcome
  :class ::program)

(definterface fn-native-operator-host-mission-outcome
  :class ::program)

(definterface fn-native-operator-host-preflight-needs-config-p
  :class ::program)

(definterface fn-native-operator-host-preflight-needs-config-path-p
  :class ::program)

(definterface fn-native-operator-host-result-account-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-account-hash-login
  :class ::program)

(definterface fn-native-operator-host-result-account-invite-seconds
  :class ::program)

(definterface fn-native-operator-host-result-admin-argv
  :class ::program)

(definterface fn-native-operator-host-result-admin-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-admin-plan
  :class ::program)

(definterface fn-native-operator-host-result-archive-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-arguments
  :class ::program)

(definterface fn-native-operator-host-result-carry-fields
  :class ::program)

(definterface fn-native-operator-host-result-command
  :class ::program)



(definterface fn-native-operator-host-result-config-mission
  :class ::program)

(definterface fn-native-operator-host-result-exit-code
  :class ::program)

(definterface fn-native-operator-host-result-health-min-percent
  :class ::program)

(definterface fn-native-operator-host-result-hint
  :class ::program)

(definterface fn-native-operator-host-result-import-request
  :class ::program)

(definterface fn-native-operator-host-result-init-group-octets
  :class ::program)

(definterface fn-native-operator-host-result-init-profile
  :class ::program)

(definterface fn-native-operator-host-result-inspect-group
  :class ::program)

(definterface fn-native-operator-host-result-inspect-msgid-octets
  :class ::program)

(definterface fn-native-operator-host-result-keys-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-keys-msgid-octets
  :class ::program)

(definterface fn-native-operator-host-result-mission-directory-octets
  :class ::program)

(definterface fn-native-operator-host-result-mission-octets
  :class ::program)

(definterface fn-native-operator-host-result-moderate-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-moderate-request
  :class ::program)

(definterface fn-native-operator-host-result-native-action
  :class ::program)

(definterface fn-native-operator-host-result-peering-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-peering-words
  :class ::program)

(definterface fn-native-operator-host-result-post-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-group-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-msgid-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-payload-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-principal-account-result
  :class ::program)

(definterface fn-native-operator-host-result-principal-auth-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-principal-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-principal-plan
  :class ::program)

(definterface fn-native-operator-host-result-principal-store-octets
  :class ::program)

(definterface fn-native-operator-host-result-reason
  :class ::program)

(definterface fn-native-operator-host-result-rebind-policy
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-protected-onlyp
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-requiredp
  :class ::program)

(definterface fn-native-operator-host-result-run-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-cold-resources
  :class ::program)

(definterface fn-native-operator-host-result-run-output-resources
  :class :program)

(definterface fn-native-operator-host-result-run-implicit-tls-port
  :class ::program)

(definterface fn-native-operator-host-result-run-listener-host-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-listener-port
  :class ::program)

(definterface fn-native-operator-host-result-run-max-connections
  :class ::program)

(definterface fn-native-operator-host-result-run-oncep
  :class ::program)

(definterface fn-native-operator-host-result-run-posting-enabledp
  :class ::program)

(definterface fn-native-operator-host-result-run-store-octets
  :class ::program)

(definterface fn-native-operator-host-result-show-octets
  :class ::program)

(definterface fn-native-operator-host-result-status
  :class ::program)

(definterface fn-native-operator-host-result-status-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-status-kind
  :class ::program)

(definterface fn-native-operator-host-result-status-log-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-status-watch
  :class ::program)

(definterface fn-native-operator-host-result-store-root
  :class ::program)

(definterface fn-native-operator-host-result-tls-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-store-outcome
  :class ::program)

(definterface fn-native-operator-result-arguments
  :class ::common-lisp-compliant)

(definterface fn-nls-capacity-line
  :class ::common-lisp-compliant)

(definterface fn-nop-developer-init
  :class ::common-lisp-compliant)

(definterface fn-ores-config-octets
  :class ::common-lisp-compliant)

(definterface fn-ores-config-reason
  :class ::common-lisp-compliant)

(definterface fn-ores-config-word
  :class ::common-lisp-compliant)

(definterface fn-workflow-carry-apply
  :class ::program)

(definterface fn-workflow-carry-install
  :class ::program)

(definterface fn-workflow-carry-preflight
  :class ::program)

(definterface fn-workflow-carry-record
  :class ::program)

(definterface fn-workflow-carry-report
  :class ::program)

(definterface fn-workflow-enqueue-record
  :class ::program)

(definterface fn-workflow-fencedp
  :class ::program)

(definterface fn-workflow-ion-helper-seconds
  :class ::program)

(definterface fn-workflow-ion-attempt-plan
  :class ::program)

(definterface fn-workflow-ion-observation-record
  :class ::program)

(definterface fn-workflow-ion-request-adu
  :class ::program)

(definterface fn-workflow-ion-route-record
  :class ::program)

(definterface fn-workflow-ion-status
  :class ::program)

(definterface fn-workflow-receipt-record
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-workflow-recovery-plan
  :class ::program)

(definterface fn-workflow-release-record
  :class ::program)

(definterface fn-workflow-take-submit
  :class ::program)

(definterface fn-workflow-undertake-record
  :class ::program)

(definterface fn-workflow-valid-config
  :class ::ideal)

(definterface fn-workflow-work-status
  :class ::program)

; -----------------------------------------------------------------------------
; control (76 entries)

(definterface fn-cp-cursor-decode
  :class ::common-lisp-compliant)

(definterface fn-cp-cursor-encode
  :class ::common-lisp-compliant)

(definterface fn-cp-nth
  :class ::common-lisp-compliant
  :kinds ((n natp))
  :keystones (fn-col-scope-entry-position-is-natural))

(definterface fn-cpj-max-cursor-octets
  :class ::common-lisp-compliant)

(definterface fn-cpj-max-event-octets
  :class ::common-lisp-compliant)

(definterface fn-cpj-project
  :class ::common-lisp-compliant)

(definterface fn-hl-host-enroll-event
  :class ::program)

(definterface fn-hl-host-revoke-event
  :class ::program)

(definterface fn-hl-host-store-history
  :class ::program)

(definterface fn-native-control-completion-status
  :class ::common-lisp-compliant)

(definterface fn-native-control-host-admin-encode
  :class ::program)

(definterface fn-native-control-host-consumer-article-json
  :class ::program)

(definterface fn-native-control-host-consumer-cli-after
  :class ::program)

(definterface fn-native-control-host-consumer-cli-plan
  :class ::program)

(definterface fn-native-control-host-consumer-client-read
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-consumer-json-line
  :class ::program)

(definterface fn-native-control-host-consumer-poll-reply-encode
  :class ::program)


(definterface fn-native-control-host-consumer-reasoned-request-encode
  :class ::program)

(definterface fn-native-control-host-consumer-reply-encode
  :class ::program)

(definterface fn-native-control-host-consumer-report-summary
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))


(definterface fn-native-control-host-consumer-request-encode
  :class ::program)

(definterface fn-native-control-host-consumer-secret-of-file
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-consumer-status-reply-encode
  :class ::program)

(definterface fn-native-control-host-launch-disposition
  :class ::program)

(definterface fn-native-control-host-lease-path
  :class ::program)

(definterface fn-native-control-host-liveness
  :class ::program)

(definterface fn-native-control-host-liveness-note
  :class ::program)

(definterface fn-native-control-host-max-active-clients
  :class ::program)

(definterface fn-native-control-host-max-article
  :class ::program)

(definterface fn-native-control-host-max-frame
  :class ::program)


(definterface fn-native-control-host-moderation-encode
  :class ::program)

(definterface fn-native-control-host-read-bound
  :class ::program)

(definterface fn-native-control-host-reasoned-admin-encode
  :class ::program)




(definterface fn-native-control-host-refusal-status
  :class ::program)

(definterface fn-native-control-host-reply-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-reply-detail
  :class ::program)

(definterface fn-native-control-host-reply-encode
  :class ::program)

(definterface fn-native-control-host-status-class
  :class ::program)

(definterface fn-native-control-host-status-exit-code
  :class ::program)

(definterface fn-native-control-host-statuses
  :class ::program)

(definterface fn-native-control-host-topic-cli-plan
  :class ::program)

(definterface fn-native-control-host-topic-reply-decode
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(definterface fn-native-control-host-topic-reply-encode
  :class ::program)


(definterface fn-native-control-host-topic-request-encode
  :class ::program)

(definterface fn-native-control-host-topic-status-exit-code
  :class ::program)

(definterface fn-native-control-host-transport-outcome
  :class ::program)

(definterface fn-native-control-host-transport-word
  :class ::program)

(definterface fn-native-control-max-active-clients
  :class ::common-lisp-compliant)

(definterface fn-native-hybrid-control-host-author-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-author-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-event
  :class ::program)

(definterface fn-native-hybrid-control-host-read-bound
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-event
  :class ::program)

(definterface fn-native-hybrid-control-host-uint32
  :class ::program)

(definterface fn-ncl-usage-text
  :class ::common-lisp-compliant)

(definterface fn-nhc-author-refusal
  :class ::common-lisp-compliant
  :keystones (fn-nhc-author-refusal-names-an-unserved-group
              fn-nhc-author-refusal-is-a-named-refusal))

(definterface fn-owner-control-filing
  :class ::program
  :kinds ((group-octets fn-octet-list-listp)))

(definterface fn-owner-control-filing-buffer
  :class :common-lisp-compliant
  :kinds ((group-octets fn-octet-list-listp))
  :keystones ((fn-ars-filing-plan-is-reference :via fn-ars-filing-plan)))

(definterface fn-owner-control-outcome
  :class ::program)

(definterface fn-owner-control-profile-bounds
  :class ::program)

(definterface fn-record-stamp-of-observation
  :class ::common-lisp-compliant)

(definterface fn-tlsr-host-reply-encode
  :class ::program)

; -----------------------------------------------------------------------------
; Entries the raw host dispatched with no declaration at the batch BE head
; (tranches 4-6 and the queue merges, 2026-09-29): interface_emit --check
; refused 111 of them and every native image build stopped at its
; interfaces-check.  Each names the book or host file that defines it, the
; raw host file that dispatches it, and the lane that brought the call.
; Classes and kinds are the definitions' own (guard-verification by the
; book's xargs and verify-guards events; kinds as fn-di-world-kinds derives
; them); the lanes add keystones.

;; books/arena-reader-pins.lisp

; host/native/io.lisp dispatches it (lane composed-owner-5).
(definterface fn-arpn-initial
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner-5).
(definterface fn-arpn-step
  :class ::common-lisp-compliant)

(definterface fn-rpin-step
  :class :common-lisp-compliant
  :keystones (fn-rpin-step-preserves-funded-ownership))

;; books/control-request-word.lisp

; host/native/operator-live.lisp dispatches it (lane online-reclaim-5).
(definterface fn-crqw-request-word
  :class ::common-lisp-compliant)

;; books/deflate-inflate.lisp

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-buffer-sizes
  :class ::common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-buffers-ready
  :class ::common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-feed
  :class ::common-lisp-compliant
  :kinds ((b natp) (start natp) (end natp) (lim natp)))

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-refusal-text
  :class ::common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-reset
  :class ::common-lisp-compliant)

;; books/deflate-pool.lisp

; host/native/deflate.lisp dispatches it (lane compress-3).
(definterface fn-zpl-decode-bufs
  :class ::common-lisp-compliant
  :kinds ((dict fn-cbor-octet-listp) (end natp) (n natp)))

;; books/extent-retire.lisp

; host/native/owner.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-quiet-files
  :class ::common-lisp-compliant
  :kinds ((named true-listp))
  :keystones ((fn-xrt-quiet-files-are-unnamed :via fn-xrt-quiet-files)))

; host/native/owner.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-reseat-checkpoint-frame
  :class ::common-lisp-compliant
  :kinds ((file natp) (start natp) (end natp))
  :keystones ((fn-xrt-reseat-checkpoint-frame-keeps-the-arena :via fn-xrt-reseat-checkpoint-frame)))

; host/native/io.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-step-handles
  :class ::common-lisp-compliant
  :kinds ((pst true-listp)))

;; books/history-image-snapshot.lisp

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-base-octets
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-binding
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-image-header
  :class ::common-lisp-compliant
  :kinds ((np natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-image-header-np
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-np
  :class ::common-lisp-compliant
  :kinds ((acc natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-release
  :class ::common-lisp-compliant)

(definterface fn-his-readback-header-p
  :class ::common-lisp-compliant
  :kinds ((np natp)))

(definterface fn-his-readback-page
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-skip-octets
  :class ::common-lisp-compliant
  :kinds ((np natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-words
  :class ::common-lisp-compliant
  :kinds ((sel natp) (a natp)))

;; books/history-image-builder.lisp, the native publisher's incremental API.
; The audited registered zero-arg constructor allocates a PRIVATE snapshot,
; never ACL2's live-stobj counterpart returned by an ordinary creator route.
(definterface create-fn-hrecs$c :class ::common-lisp-compliant
  :raw-guarded (0 nil (fn-hrecs$c)))

(definterface fn-his-build-source-count
  :class ::common-lisp-compliant
  :kinds ((records true-listp)))
(definterface fn-his-build-yieldp
  :class ::common-lisp-compliant
  :kinds ((ordinal natp)))

(definterface fn-his-build-begin
  :class ::common-lisp-compliant
  :kinds ((salt natp)))

(definterface fn-his-build-row
  :class ::common-lisp-compliant)

(definterface fn-his-build-finish
  :class ::common-lisp-compliant
  :kinds ((expected-count natp)))

;; books/limits-live.lisp

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decide
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decision-reason
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decision-status
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-reply-line
  :class :common-lisp-compliant)

; host/native/heap.lisp dispatches it (lane limits-live).
(definterface fn-lim-values-lines
  :class :common-lisp-compliant)

;; books/native-admin-shape.lisp

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-capacity
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-kind
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-name
  :class ::common-lisp-compliant)

;; books/native-admin.lisp

; host/native/admin.lisp dispatches it (lane operability-5).
(definterface fn-native-admin-result-inspect-msgid
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches them (lane operability-7, row S3b).
(definterface fn-native-admin-result-export-dir
  :class :common-lisp-compliant)

(definterface fn-native-admin-result-export-statusp
  :class :common-lisp-compliant)

;; books/owner-export-request.lisp (row S3b): the running owner's export
;; request and status (host/native/admin.lisp) and the client's reading
;; and lines (host/native/operator.lisp).
(definterface fn-oex-request-word
  :class :common-lisp-compliant)

(definterface fn-oex-request-status
  :class :common-lisp-compliant)

(definterface fn-oex-request-line
  :class :common-lisp-compliant
  :kinds ((dir stringp)))

(definterface fn-oex-status-word
  :class :common-lisp-compliant)

(definterface fn-oex-status-status
  :class :common-lisp-compliant)

(definterface fn-oex-outcome-line
  :class :common-lisp-compliant
  :kinds ((dir stringp)))

(definterface fn-oex-word-of-octets
  :class :common-lisp-compliant
  :exempt ((octets "compared whole with each reason word's octets (fn-oex-word-reads-back); other octets are no word (nil)")))

(definterface fn-oex-status-no-owner-line
  :class :common-lisp-compliant)

;; books/owner-snapshot-request.lisp (row S7, PRF-1050): the running owner's
;; snapshot request and status (host/native/admin.lisp), the blessing's
;; verdict (host/native/io.lisp fnn-command-store-bless-snapshot), the
;; marker's text and the client's lines (host/native/operator.lisp).
(definterface fn-nop-parse-store
  :class :common-lisp-compliant)

(definterface fn-osn-bless-open-needed
  :class :common-lisp-compliant)

(definterface fn-osn-bless-word
  :class :common-lisp-compliant)

(definterface fn-osn-bless-status
  :class :common-lisp-compliant)

(definterface fn-osn-bless-line
  :class :common-lisp-compliant
  :kinds ((dir stringp) (transactions natp)))

;; books/native-control-reason.lisp

; host/native/control.lisp dispatches it (lane correctness-remainder).
(definterface fn-native-control-host-refusal-reason
  :class ::common-lisp-compliant)

;; books/nntp-compress.lisp

; host/native/deflate.lisp dispatches it (lane compress-8).
(definterface fn-zc-deflate-params
  :class ::common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane compress-8).
(definterface fn-zc-render-window-size
  :class :common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress-8).
(definterface fn-zc-sync-output-octets
  :class :common-lisp-compliant)

;; books/octets-stobj.lisp

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-oct-line-end
  :class ::common-lisp-compliant
  :kinds ((i natp)))

;; books/open-frontier-wire.lisp

; host/native/io.lisp dispatches it (lane limits-live-5).
(definterface fn-ofw-wire-next
  :class :common-lisp-compliant)

;; books/owner-maintenance-request.lisp

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-control-path-octets
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-header-octets
  :class ::common-lisp-compliant)

; host/native/io.lisp, host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-held-line
  :class ::common-lisp-compliant
  :kinds ((verb stringp)))

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-live-report
  :class :common-lisp-compliant
  :exempt ((msgid-octets "rendered into the report's line as the operator typed it (fn-native-operator-inspect-report); any list renders")
           (word-octets "compared whole with the reason word of :found (fn-omr-inspect-foundp): any value decides absent")))

; host/native/admin.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-status
  :class ::common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-word
  :class ::common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-recover-line
  :class ::common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-recover-status
  :class ::common-lisp-compliant)

; host/native/io.lisp, host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-route
  :class ::common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-status-replayp
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (`store ROOT status [--replay]', lane
; operability-9): the operator verb's decision for the store verb.
(definterface fn-omr-store-status-word
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-stopped-health-report
  :class :ideal
  :exempt ((journal-octets "a COUNT of octets (the journal files' lstat sizes), a natural the report nfixes; not bytes")
           (config-octets "fn-spo-config-open decides the open verdict first and refuses a malformed config by name")))

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-stopped-report
  :class :ideal
  :exempt ((journal-octets "a COUNT of octets (the journal files' lstat sizes), a natural the report nfixes; not bytes")
           (config-octets "fn-spo-config-open decides the open verdict first and refuses a malformed config by name")))

;; books/owner-time-bars.lisp

; host/native/owner.lisp dispatches it (lane composed-owner-3 (row A4)).
(definterface fn-otb-dependency-step
  :class ::common-lisp-compliant)

; host/native/owner.lisp fnn-owner-cold-await dispatches it (lane served-live:
; a re-run line's deadline from its first miss).
(definterface fn-otb-line-dependency-step
  :class :common-lisp-compliant)

;; books/payload-arena-extent-logic.lisp

; host/native/extent.lisp dispatches it (lane compress-5 (NNT-055)).
(definterface fn-arn-lz-extentp
  :class :common-lisp-compliant
  :direct "the raw body of A-ARENA-STORED's realizer (host/native/extent.lisp fn-arena-stored) recognizes the compressed extent itself; guard t")

;; books/assumptions-pgs-host-io.lisp

; host/native/extent.lisp applies them in A-PGS-HOST-IO's frame fill
; (fn-pgs-fill-frame, lane stage-0-4).
(definterface fn-pgs-frame-len
  :class :common-lisp-compliant
  :direct "the raw body of A-PGS-HOST-IO's frame fill (host/native/extent.lisp fn-pgs-fill-frame) reads the selected array's length to refuse a range outside it; SEL checked against 0, 1, 2 first")
(definterface fn-pgs-frame-put
  :class :common-lisp-compliant
  :kinds ((base natp))
  :direct "the raw body of A-PGS-HOST-IO's frame fill (host/native/extent.lisp fn-pgs-fill-frame) is the constraint's right-hand side, the put of fn-pgs-fill-realize's 2048 u64 words at BASE; the selector and range are checked first, the words are the realizer's")

;; books/payload-extent-read.lisp

(definterface fn-owner-chunk-span :class :program)
(definterface fn-owner-unavailable-line-at :class :program)
(definterface fn-store-sco-decode :class :program)
(definterface fn-store-sco-decode-finish :class :program)
(definterface fn-owner-resource-unavailable-line-at :class :program)
(definterface fn-owner-page-read-close-preview :class :common-lisp-compliant)
(definterface fn-owner-page-read-close :class :common-lisp-compliant)

;; host/page-read-host.lisp: the dedicated carried resource stobj.
(definterface fn-owner-page-read-admit :class :common-lisp-compliant)
(definterface fn-owner-page-cache-evict :class :common-lisp-compliant)
(definterface fn-pio-own-admitted-token
  :class :common-lisp-compliant
  :keystones ((fn-pio-admitted-resource-token-establishes-owned-read :via fn-pio-own-admitted-token)))

;; books/page-read-ownership.lisp (PRF-1057).
(definterface fn-pio-complete
  :class :common-lisp-compliant
  :keystones ((fn-pio-completion-publishes-only-the-issued-identity :via fn-pio-complete)))
;; The issued table's helpers (books/page-read-direct.lisp; the funded arm's
;; sites host/native/extent.lisp fnn-extent-issue-read / -complete-read keep
;; the one table through them; lane def-holder).
(definterface fn-pio-issued-put :class :common-lisp-compliant)
(definterface fn-pio-issued-row :class :common-lisp-compliant)
(definterface fn-pio-issued-remove :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane extent-identity).
(definterface fn-arx-attach-trailers-buffer
  :class :common-lisp-compliant
  :kinds ((places true-listp) (base natp)))

; host/native/extent.lisp dispatches it (lane extent-identity).
(definterface fn-arx-entry-verdict-buffer
  :class :common-lisp-compliant)

;; books/payload-extent.lisp

; host/native/io.lisp dispatches it (lane extent-identity).
(definterface fn-arx-attach-trailers
  :class :common-lisp-compliant
  :kinds ((places true-listp) (base natp) (octets true-listp)))

;; books/payload-lz-dicts.lisp

; host/native/io.lisp dispatches it (lane compress-2).
(definterface fn-lzd-current-id
  :class ::common-lisp-compliant)

; host/native/io.lisp dispatches it (lane compress-2).
(definterface fn-lzd-lookup
  :class ::common-lisp-compliant)

;; books/peer-set.lisp

; host/native/peer-invite.lisp dispatches it (lane operability-3 (S5)).
(definterface fn-pset-login-argv
  :class :common-lisp-compliant)

; host/native/peer-invite.lisp dispatches it (lane operability-3 (S5)).
(definterface fn-pset-login-file
  :class :common-lisp-compliant)

;; books/records-shape.lisp

; host/native/admin.lisp dispatches it (lane operability-3).
(definterface fn-record-octets-string
  :class ::common-lisp-compliant)

; host/native/admin.lisp, host/native/operator.lisp dispatches it (lane operability-3).
(definterface fn-record-string-octets
  :class ::common-lisp-compliant)

;; books/store-checkpoint-open.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-sco-records
  :class ::common-lisp-compliant)

;; host/bp-release-owner-host.lisp

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-pending-waivers
  :class ::program)

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-store-waive
  :class ::program)

;; host/native-admin-host.lisp

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-native-admin-host-reclaim-mode
  :class :ideal)

;; host/native-control-host.lisp

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-decode-frame
  :class ::program)

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-client-step
  :class :program
  :kinds ((octets fn-cbor-octet-listp)))

; host/native/operator-live.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-detail
  :class :program)

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-lined-reply-encode
  :class :program)

;; host/native-operator-host.lisp

; host/native/operator.lisp dispatches it (lane correctness-remainder-3).
(definterface fn-native-operator-host-result-account-hash-auth-path-octets
  :class ::program)

;; host/owner-host.lisp

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-owner-apply-limit-profile
  :class :common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane compress-8).
(definterface fn-owner-compress-owed
  :class ::program)

; host/native/owner.lisp dispatches it (lane correctness-remainder).
(definterface fn-owner-control-reason
  :class ::program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-admit
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-done
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-leave
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget-3).
(definterface fn-owner-proxy-begin
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget-3).
(definterface fn-owner-proxy-step
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget-3).
(definterface fn-owner-proxy-timeout-line
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget-3).
(definterface fn-owner-proxy-handover
  :class :program)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-owner-limit-use
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-capture
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-chunk
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-classes
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-ctx
  :class ::program)

; host/native/owner.lisp dispatches it once the pass is done with its
; context (lane reclaim-retention).
(definterface fn-owner-orc-ctx-free
  :class :common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-decide
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-finish
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-init
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-request
  :class ::program)

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-request-status
  :class :common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-capture
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-finish
  :class ::program)

; host/native/owner.lisp dispatches it (lane arena-forget: the deferred
; reclaim seals nothing).
(definterface fn-orcs-predict
  :class ::common-lisp-compliant
  :kinds ((generation natp) (h natp))
  :keystones (fn-orcs-predict-seal-refines-intern))

(definterface fn-orcs-seal
  :class ::common-lisp-compliant
  :keystones (fn-orcs-seal-is-the-intern))

(definterface fn-orcs-seal-word
  :class ::common-lisp-compliant
  :keystones (fn-orcs-seal-word-swap-means-base))

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-keyring
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-load-columns
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-rebuild
  :class :ideal
  :keystones (fn-owner-orcp-rebuild-establishes-retain-carry))

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-salt
  :class ::program)

(definterface fn-owner-orcp-key
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-swap
  :class ::common-lisp-compliant :kinds ((rebuilt true-listp)))

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-swap-word
  :class ::program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-view-index
  :class ::program)

; host/native/mux.lisp dispatches it (lane compress-8 (sasl union)).
(definterface fn-owner-sasl-binding-octets
  :class :program)

; host/native/owner.lisp dispatches it (lane compress-8 (sasl union)).
(definterface fn-owner-sasl-context
  :class :program)

; host/native/owner.lisp dispatches it (lane compress-8 (sasl union)).
(definterface fn-owner-sasl-seed-octets
  :class :program)

; host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-owner-sco-next
  :class ::program)

; host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-owner-sco-setup-of
  :class ::program)

;; host/store-host.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-store-genesis-ident
  :class ::program)

;; host/store-node-host.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-his-file-octets
  :class :common-lisp-compliant)

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-his-stream-free
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-cfg-next-txid
  :class ::program
  :kinds ((octet-records fn-octet-list-listp)))

; host/native/admin.lisp, host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-lim-effective
  :class ::program
  :kinds ((octet-records fn-octet-list-listp)))

; host/native/admin.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-lim-use
  :class ::program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-image-open
  :class ::program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-note-checkpoint-digest
  :class ::program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-publish-next
  :class ::program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-publish-setup-of
  :class ::program
  :exempt ((segment-octets "a segment descriptor, not bytes")))

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-want-checkpoint-digest
  :class ::program)

; Serialized BP node local control (route-only first increment).
(definterface fn-bpnc-config-bound
  :class ::common-lisp-compliant)
(definterface fn-bpnc-startup
  :class ::common-lisp-compliant
  :keystones (fn-bpnc-ready-startup-binds-the-parsed-store))
(definterface fn-bpnc-socket-initial
  :class ::common-lisp-compliant
  :keystones (fn-bpnc-open-run-live-iff-both-completions-succeed))
(definterface fn-bpnc-socket-action
  :class ::common-lisp-compliant
  :keystones (fn-bpnc-retirement-stops-the-control-listener))
(definterface fn-bpnc-socket-step
  :class ::common-lisp-compliant
  :keystones (fn-bpnc-open-run-live-iff-both-completions-succeed
              fn-bpnc-retirement-stops-the-control-listener))

(definterface fn-bpnc-status-unavailable
  :class ::common-lisp-compliant)
; Called directly only while installing dispatch from the loaded image world.
(definterface fn-di-raw-with-problem
  :class :program
  :direct "Image-build declaration lint over the loaded world; no client data or served decision")

; Actual world ABI/guard and creator-EXEC checks at image installation.
(definterface fn-di-raw-guarded-problem
  :class :program
  :direct "Image-build exact guard and stobj ABI validation over the exported ACL2 world")
(definterface fn-di-raw-guarded-target
  :class :program
  :direct "Image-build resolution of actual compiled callback or registered creator EXEC")
(definterface fn-di-raw-creatorp
  :class :program
  :direct "fnn-install-raw-dispatch identifies exact registered startup creators from the validated immutable image world")

; Serialized BP listener installation and actual owner configuration control.
(definterface fn-bplc-step
  :class ::common-lisp-compliant
  :keystones (fn-bplc-failed-completion-fences-without-rollback
              fn-bplc-installed-runtime-is-the-completed-target
              fn-bplc-step-preserves-listener-credit
              fn-bplc-bind-and-retire-account-exact-descriptor-completions
              fn-bplc-rebind-retains-the-accepted-session-generation))
(definterface fn-bplc-action :class ::common-lisp-compliant)
(definterface fn-bplc-accept-plan :class ::common-lisp-compliant)
(definterface fn-bplc-runtime-line :class ::common-lisp-compliant)
(definterface fn-bplc-cut-plan
  :class ::common-lisp-compliant
  :keystones (fn-bplc-every-death-cut-is-a-fenced-process-crash))
(definterface fn-owner-bplc-recover :class ::program)
(definterface fn-owner-bplc-begin :class ::program)
(definterface fn-owner-bplc-turn-plan :class ::program)

(definterface fn-pio-reap-work :class :common-lisp-compliant)

(definterface fn-owner-page-file-issue :class :common-lisp-compliant
  :keystones ((fn-pio-bounded-file-issue-spends-a-fresh-representable-name :via fn-pio-file-issue-with-limit)))
(definterface fn-owner-page-read-register-path :class :common-lisp-compliant)

;; Persistent cold worker, exact assigned and settled resource binding.
(definterface fn-pxe-new :class :common-lisp-compliant :kinds ((slot natp)))
(definterface fn-pxe-return :class :common-lisp-compliant
  :keystones ((fn-pxe-stale-completion-cannot-return-a-reused-worker :via fn-pxe-return)))
(definterface fn-owner-page-executor-acquire :class :common-lisp-compliant
  :keystones ((fn-pxe-acquired-token-cannot-own-a-second-worker :via fn-pxe-acquire)))
(definterface fn-owner-page-executor-commit :class :common-lisp-compliant
  :keystones ((fn-pxe-commit-requires-returned-settled-exact-job :via fn-pxe-commit)))

(definterface fn-pio-worker-death-step :class :common-lisp-compliant
  :kinds ((deadp booleanp)))

;; books/page-read-direct.lisp (lane cold-read-ownership): the unfunded cold
;; line's issued rows and bounded persistent workers (host/native/extent.lisp
;; fnn-extent-direct-start, fnn-extent-issue-direct, fnn-extent-direct-settle).
(definterface fn-pio-direct-workers :class :common-lisp-compliant)
(definterface fn-pio-direct-admit :class :common-lisp-compliant
  :keystones ((fn-pio-direct-admit-binds-an-idle-worker-to-the-issued-identity :via fn-pio-direct-admit)
              (fn-pio-direct-cancelled-read-still-pins-its-file :via fn-pio-direct-admit)))
(definterface fn-pio-direct-settle :class :common-lisp-compliant
  :keystones ((fn-pio-direct-settle-publishes-only-the-issued-identity :via fn-pio-direct-settle)
              (fn-pio-direct-settle-observes-every-outcome :via fn-pio-direct-settle)
              (fn-pio-direct-settle-stale-changes-nothing :via fn-pio-direct-settle)
              (fn-pio-direct-settle-happens-once :via fn-pio-direct-settle)))
;; lane def-holder: the timeout's cancel, the close's one lookup (KEYSTONE
;; fn-pio-direct-quiet-is-clear: under the carried agreement of the issued and
;; holds tables it is the walk fnn-extent-close used to run), the tables'
;; initial (fnn-extent-direct-start).
(definterface fn-pio-direct-cancel :class :common-lisp-compliant)
(definterface fn-pio-direct-quiet-p :class :common-lisp-compliant
  :keystones ((fn-pio-direct-quiet-is-clear :via fn-pio-direct-quiet-p)))
(definterface fn-pio-direct-initial :class :common-lisp-compliant)



(definterface fn-native-operator-host-result-init-budget
  :class ::program)

(definterface fn-native-operator-host-result-init-sizing
  :class ::program)

(definterface fn-native-operator-host-result-retire-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-self-signed
  :class :program)

(definterface fn-native-operator-host-self-signed-outcome
  :class :program
  :exempt ((cert-exists "the host's lstat of tls_cert, a boolean ACL2 reads as observed")
           (key-exists "the host's lstat of tls_key, a boolean ACL2 reads as observed")))

(definterface fn-native-operator-host-self-signed-refused
  :class :program
  :exempt ((reason "the refusal word fn-tls-self-signed-host-plan or -pem returned; any other value is refused as :self-signed")))

(definterface fn-nret-begin-answer
  :class :common-lisp-compliant)

(definterface fn-nret-begin-log-line
  :class :common-lisp-compliant)

(definterface fn-nret-end-log-line
  :class :common-lisp-compliant)

(definterface fn-nret-no-report-line
  :class :common-lisp-compliant)

(definterface fn-nret-not-running-line
  :class :common-lisp-compliant)

(definterface fn-nret-refusal-line
  :class :common-lisp-compliant)

(definterface fn-nret-refused-log-line
  :class :common-lisp-compliant)

(definterface fn-nret-report-file-name
  :class :common-lisp-compliant)

(definterface fn-nret-request
  :class :common-lisp-compliant
  :keystones (fn-nret-request-of-request-argv
              fn-nret-request-window-is-bounded))

(definterface fn-owner-retire-report
  :class ::program
  :keystones ((fn-oret-report-carries-the-obligations-report :via fn-oret-report)))

(definterface fn-owner-retire-step
  :class ::program
  ;; The host step is fn-ort-drain-step-counted since 1bf2ddcaf (carried
  ;; counts and both producer fences), so its keystones are the counted
  ;; drain's: the window ends it, and before the window it waits unless the
  ;; fenced count is zero.
  :keystones ((fn-ort-deadline-is-independent-of-the-fences :via fn-ort-drain-step-counted)
              (fn-ort-counted-drain-waits-before-window-without-fenced-zero
               :via fn-ort-drain-step-counted)))

(definterface fn-tls-self-signed-host-certificate-pem
  :class :program
  :kinds ((tbs fn-cbor-octet-listp) (sig fn-cbor-octet-listp))
  :keystones ((fn-ssc-certificate-pem-carries-the-body :via fn-ssc-certificate-pem)))

(definterface fn-tls-self-signed-host-key-pem
  :class :program
  :kinds ((der fn-cbor-octet-listp))
  :keystones ((fn-ssc-key-pem-carries-the-key :via fn-ssc-key-pem)))

(definterface fn-tls-self-signed-host-plan
  :class :program
  :kinds ((serial fn-cbor-octet-listp) (spki fn-cbor-octet-listp))
  :exempt ((names "ACL2's own names from fn-native-operator-host-result-self-signed, handed back unchanged; fn-ssc-plan refuses a bad one by name")
           (days "ACL2's own days from the same request")
           (now-ms "the wall reading fn-otm-wall-reading returned")
           (has-wall "the wall reading's usable flag; fn-ssc-plan refuses :clock without it"))
  :keystones ((fn-ssc-plan-body-is-one-sequence :via fn-ssc-plan)))

(definterface fn-tls-self-signed-host-serial-octets
  :class :program)

(definterface fn-pxe-cache-mode :class :common-lisp-compliant
  :kinds ((enabledp booleanp)))

;; Typed, unverified checkpoint discovery buffer; never a verified read token.
(definterface fn-owner-page-read-direct-mode :class :common-lisp-compliant)
(definterface fn-owner-page-read-discovery-admit :class :common-lisp-compliant
  :keystones ((fn-prd-admit-preserves-pool-funding :via fn-prd-admit)))
(definterface fn-owner-page-read-discovery-release :class :common-lisp-compliant)

; Actual statement streaming and material dispatch declarations.
; Source: books/native-statement-material.lisp, all three guards T.
(definterface fn-nsm-plan
  :class :common-lisp-compliant)
(definterface fn-nsm-render
  :class :common-lisp-compliant)
(definterface fn-nsm-check-rendered
  :class :common-lisp-compliant)
; Source: books/statement-recover-stream.lisp. The worker's state/dictionary
; predicates are not recognized host kind predicates; no raw-dispatch claim.
(definterface fn-ssr-intern-step
  :class :common-lisp-compliant
  :keystones (fn-ssr-resident-step-of-append
              fn-ssr-extent-step-refines-resident
              fn-ssr-lz-step-refines-resident))
(definterface fn-ssr-rows
  :class :common-lisp-compliant)
(definterface fn-ssr-seed
  :class :common-lisp-compliant)
; Source: host/store-node-host.lisp, program mode over STATE.
(definterface fn-store-statement-replay-seed
  :class :program)
; Source: books/stx-keyring-records.lisp, guard T.
(definterface fn-stxk-initial-context
  :class :common-lisp-compliant)
; Q10d bounded observation for the owner's web readiness route.
(definterface fn-web-host-health-observe
  :class :program
  :keystones ((fn-whl-success-requires-observed-clear-owner :via fn-whl-observe)))
(definterface fn-owner-page-read-settle :class :common-lisp-compliant
  :keystones ((fn-prl-completion-refunds-at-most-once :via fn-prl-settle)))

(definterface fn-owner-page-file-pin :class :common-lisp-compliant
  :keystones ((fn-prf-acquire-preserves-pool-funding :via fn-prf-acquire)
              (fn-prf-acquired-file-is-held :via fn-prf-acquire)))
(definterface fn-owner-page-file-unpin :class :common-lisp-compliant)
(definterface fn-hrs-h-file :class :common-lisp-compliant)
(definterface fn-owner-page-file-pin-file :class :common-lisp-compliant)
(definterface fn-owner-page-file-pin-read :class :common-lisp-compliant
  :keystones ((fn-prd-admit-preserves-pool-funding :via fn-prd-admit)))

;; Staged exact raw extent window. Demand/allocator and served reachability
;; are separate obligations; these declarations do not activate a consumer.
(definterface fn-crw-supportedp :class :common-lisp-compliant)
(definterface fn-ews-begin :class :common-lisp-compliant
  :kinds ((file natp) (eoff natp) (elen natp) (poff natp) (plen natp) (offset natp) (expected natp)))
(definterface fn-ews-effect :class :common-lisp-compliant
  :kinds ((s true-listp)))
(definterface fn-ews-tick :class :common-lisp-compliant
  :kinds ((s true-listp)))
(definterface fn-ews-read :class :common-lisp-compliant
  :kinds ((s true-listp))
  :keystones ((fn-ews-read-publication-requires-core-integrity :via fn-ews-read)))
(definterface fn-owner-page-read-ledger :class :common-lisp-compliant)
(definterface fn-pwx-tokenp :class :common-lisp-compliant
  :direct "Guard-t fixed-shape worker kind discrimination avoids an unpriced global guard-cache entry")
(definterface fn-pwx-boundp :class :common-lisp-compliant)
(definterface fn-owner-page-window-executor-acquire :class :common-lisp-compliant)
(definterface fn-owner-page-window-executor-acquire-funded :class :common-lisp-compliant)
(definterface fn-owner-page-window-executor-return :class :common-lisp-compliant)
(definterface fn-owner-page-window-executor-release :class :common-lisp-compliant
  :keystones ((fn-pwx-release-requires-exact-returned-window-and-slot :via fn-pwx-release)))
(definterface fn-owner-page-window-byte :class :common-lisp-compliant
  :kinds ((plan true-listp)))

(definterface fn-owner-page-window-byte-at :class :common-lisp-compliant
  :kinds ((plan true-listp)))
(definterface fn-pwr-cold-descriptor :class :common-lisp-compliant)

(definterface fn-owner-page-window-outcome :class :common-lisp-compliant
  :kinds ((plan true-listp)))

(definterface fn-owner-page-window-executor-cancel :class :common-lisp-compliant)
(definterface fn-owner-page-window-executor-settle-cancelled :class :common-lisp-compliant)
(definterface fn-owner-page-window-work-permittedp :class :common-lisp-compliant)

(definterface fn-owner-page-window-current-octet :class :common-lisp-compliant
  :kinds ((h natp) (i natp)))
(definterface fn-owner-page-window-decoded-refusal :class :common-lisp-compliant)

; Exact private cache declarations imported from 4b9be704b.
(definterface fn-cgb-roster :class :common-lisp-compliant
  :direct "Fixed guard-t literal roster used before dedicated cache preparation")
(definterface fn-cgb-namep :class :common-lisp-compliant
  :direct "Guard-t fixed roster membership avoids recursive entry-cache construction")
(definterface fn-cgb-planp :class :common-lisp-compliant
  :direct "Guard-t core plan check before allocating the dedicated cold guard cache")
(definterface fn-cgb-specp :class :common-lisp-compliant
  :direct "Guard-t bounded cached-metadata validation in the funded fixed roster prewarm")

; Exact logical view declarations imported from producer 57b70ff2b.
(definterface fn-owner-payload-view-acquire :class :program)
(definterface fn-owner-payload-view-live-p :class :program)
(definterface fn-owner-payload-view-release :class :program)
(definterface fn-owner-payload-view-reset :class :program)
(definterface fn-pvl-runtime-step :class ::common-lisp-compliant)
(definterface fn-owner-payload-view-owned-p :class :program)

; Stage 0 (D46): host/account-adoption-interfaces.lisp is not included; its
; entries' dispatcher (host/native/account-adoption.lisp) is not loaded.

(definterface fn-par-host-accept-record-plan
  :class ::common-lisp-compliant
  :delegates fn-par-accept-record-plan)

(definterface fn-owner-runtime-bootstrap-admit
 :class :common-lisp-compliant :root :extract)

; Actual fixed callbacks captured by the image-owned bootstrap carrier.
; Source declarations do not qualify the changed composition.
(definterface fn-owner-runtime-ats-construct-internal
 :class :common-lisp-compliant :root :extract)
(definterface fn-owner-runtime-operation-binding-install-internal
 :class :common-lisp-compliant :root :extract)
(definterface fn-owner-runtime-bootstrap-fence-internal
 :class :common-lisp-compliant :root :extract)
(definterface fn-owner-recovery-prs-install
 :class :common-lisp-compliant :root :extract)

(definterface fn-ats-finish-owned
 :class :common-lisp-compliant :root :extract)

; Stage 0 (2026-10-01): the six entries above were :raw-guarded routes of the
; runtime bootstrap (host/native/runtime-bootstrap.lisp, owner-control-turn),
; which stage 0 took off the start (host/native/build.lisp fn-native-entry);
; the raw routes, and the fn-allocation-turn-slots ABI the DTN world lacks,
; return with the bootstrap producer (planning/design-store-representation-
; 2026-10-01.md section 4, stage 6).

(definterface fn-pwz-tokenp :class :common-lisp-compliant
  :direct "Guard-t full decoded token discrimination precedes raw token destructuring; decoded execution remains refused")

; Stage 0 (2026-10-01, planning/design-store-representation-2026-10-01.md
; section 4): the entries the Codex-era host dispatched without declaring
; them (interface_emit --check at dev e014f2c5a: 33), and the page pool's
; context entry stage 0 dispatches (host/native/extent.lisp
; fnn-extent-pool-open-context).  Declared as the raw host calls them;
; their classes are the sources' (tools/interface_emit.py --check).
(definterface fn-crb-open :class :common-lisp-compliant)
(definterface fn-cre-header-octets :class :common-lisp-compliant)
(definterface fn-cre-header-plan :class :common-lisp-compliant)
(definterface fn-cre-receive-failure :class :common-lisp-compliant)
(definterface fn-log-sink-pending-lines :class :common-lisp-compliant)
(definterface fn-log-sink-pending-octets :class :common-lisp-compliant)
(definterface fn-ort-fenced-input-consumed :class :common-lisp-compliant)
(definterface fn-ort-intake-action :class :common-lisp-compliant)
(definterface fn-ort-log-close-action :class :common-lisp-compliant)
(definterface fn-ort-log-close-exit :class :common-lisp-compliant
  :kinds ((prior integerp) (uncertain integerp)))
(definterface fn-ort-report-close-action :class :common-lisp-compliant)
(definterface fn-ort-service-claim-action :class :common-lisp-compliant)
(definterface fn-ort-service-settlement-action :class :common-lisp-compliant)
(definterface fn-ort-service-start-action :class :common-lisp-compliant)
(definterface fn-ort-service-start-reason :class :common-lisp-compliant)
(definterface fn-ort-store-close-action :class :common-lisp-compliant)
(definterface fn-ort-window-step :class :common-lisp-compliant)
(definterface fn-owner-consumer-publication-verdict :class :program)
(definterface fn-owner-identity-reservation :class :program)
(definterface fn-owner-page-read-open-context :class :common-lisp-compliant)
(definterface fn-owner-remote-ingress :class :program)
(definterface fn-owner-remote-operation-preflight :class :common-lisp-compliant)
(definterface fn-owner-retire-intake-refused :class :program)
(definterface fn-splan-of-effects :class :common-lisp-compliant)
(definterface fn-tcl-final-count-ready-p :class :common-lisp-compliant)
(definterface fn-tcl-final-count-value :class :common-lisp-compliant)
(definterface fn-tcl-final-held-count :class :common-lisp-compliant)
(definterface fn-tcl-host-source-drive :class :ideal :kinds ((buf fn-cbor-octet-listp)))
(definterface fn-tcl-host-source-more-p :class :ideal)
(definterface fn-tcl-source-result-action :class :common-lisp-compliant)
(definterface fn-tcl-source-result-token :class :common-lisp-compliant)

; Resumable pull/catch-up scheduling decisions consumed by pull-service.
(definterface fn-prd-key :class :common-lisp-compliant)
(definterface fn-prd-select :class :common-lisp-compliant :kinds ((active true-listp)))
(definterface fn-prd-sweep :class :common-lisp-compliant :kinds ((active true-listp))
  :keystones (fn-prd-sweep-visits-all-admitted-rounds))
(definterface fn-prd-action :class :common-lisp-compliant)
(definterface fn-prd-deadline :class :common-lisp-compliant)
(definterface fn-prd-resume-at :class :common-lisp-compliant)
(definterface fn-prd-read-limit :class :common-lisp-compliant)
(definterface fn-prd-write-end :class :common-lisp-compliant)
(definterface fn-prd-feed-action :class :common-lisp-compliant)
(definterface fn-prd-write-quantum-end :class :common-lisp-compliant)
(definterface fn-prd-idle-ms :class :common-lisp-compliant)
(definterface fn-prd-loss-class-ok :class :common-lisp-compliant)

; ACL2 bounds operator observation without terminating owner custody.
(definterface fn-nret-observation-step :class :common-lisp-compliant
  :keystones (fn-nret-observation-expiry-is-uncertain
              fn-nret-observation-report-requires-stopped))
(definterface fn-nret-observation-poll-seconds :class :common-lisp-compliant)
(definterface fn-nret-observation-expired-line :class :common-lisp-compliant)
(definterface fn-nret-observation-fault-line :class :common-lisp-compliant)

; HTTP reactor uses these actual ACL2 scheduling and lease projections.
(definterface fn-web-host-connection-limit :class ::program)
(definterface fn-web-host-request-end :class ::program)
(definterface fn-web-host-window-end :class ::program)
(definterface fn-web-host-read-size :class ::program)
(definterface fn-web-host-event-cid :class ::program)
(definterface fn-web-host-reserve-size :class ::program)

; PRF-1272: allocation-generation producer, distinct from history version.
; Program global/native installation refinement remains pending.
(definterface fn-owner-catalog-root-reserve :class :program)
(definterface fn-owner-catalog-root-current :class :program)

(definterface fn-web-host-page-cursor :class ::program)
(definterface fn-web-host-page-step :class ::program)

(definterface fn-web-host-private-reply-p :class ::program)
(definterface fn-web-host-private-reply-step :class ::program)
