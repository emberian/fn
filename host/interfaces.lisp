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

(definterface fn-native-operator-host-run
  :class :program
  :exempt ((argv-octets "a list of argument octet lists, preflighted (fn-native-operator-host-preflight)")
           (config-octets "read by fnn-operator-read-config, bounded; NIL when absent")))

(definterface fn-owner-control-submit
  :class :program
  :kinds ((msgid-octets fn-cbor-octet-listp) (group-octets fn-octet-list-listp))
  :exempt ((payload "the received article's buffer (host/native/hybrid-control.lisp)")))


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
  :direct "runs in handlers, where a dispatcher's own fault would recurse"
  ; the extracted driver's exit for the condition that ended a store verb
  ; (tools/extract/served-main.scm store-report; lane extract-writable)
  :root :extract)

; =============================================================================
; Every other entry the raw host dispatches through fnn-call, by subsystem
; (tools/interface_emit.py SUBSYSTEMS).  Class and kinds are the image
; world's; a keystone is a cited theorem (planning/proofs.json) whose
; conclusion is about the entry or whose name carries it.  No :keystones is
; a gap, listed in planning/interfaces-gaps.md.

; -----------------------------------------------------------------------------
; store (262 entries)

(definterface fn-arena-clear
  :class ::common-lisp-compliant
  :keystones (fn-sca-ocl-relation-at-full-open))

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

(definterface fn-arx-intern-step
  :class ::common-lisp-compliant
  :keystones (fn-arx-intern-step-refines))

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

(definterface fn-lgdm-entry-len
  :class ::common-lisp-compliant
  :kinds ((ps true-listp)))

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

(definterface fn-lgw-entry-len
  :class ::common-lisp-compliant
  :kinds ((st true-listp)))

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

(definterface fn-lzr-append-plan
  :class ::common-lisp-compliant
  :kinds ((r fn-cbor-octet-listp))
  :keystones (fn-lzr-config-min-without-a-row-is-off
              fn-lzr-append-plan-off))

(definterface fn-lzr-append-refusal-text
  :class ::common-lisp-compliant
  :keystones (fn-lzr-append-refusal-text-refuses-exactly-a-lying-encoder))

(definterface fn-lzr-candidate-cap
  :class ::common-lisp-compliant)

(definterface fn-lzr-commit-reseats
  :class ::common-lisp-compliant
  :keystones (fn-lzr-commit-reseats-keep-the-arena))

(definterface fn-lzr-dicts-initial
  :class ::common-lisp-compliant)

(definterface fn-lzr-intern-step
  :class ::common-lisp-compliant
  :keystones (fn-lzr-intern-step-refines))

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

(definterface fn-srs-intern-step
  :class ::common-lisp-compliant
  :keystones (fn-srs-checked-step-is-the-step
              fn-lzr-intern-step-refines
              fn-arx-intern-step-refines))

(definterface fn-srs-rows
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

(definterface fn-otb-complete
  :class ::common-lisp-compliant
  :keystones (fn-otb-a-late-completion-is-consumed-once))

(definterface fn-otb-issue
  :class ::common-lisp-compliant)

(definterface fn-otb-ledger-init
  :class ::common-lisp-compliant)

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

(definterface fn-owner-bp-listener-ports
  :class ::program)

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

(definterface fn-owner-catchup-plans
  :class :common-lisp-compliant)

(definterface fn-owner-cfg-native-admin-authorize
  :class ::program
  :kinds ((config-octet-records fn-octet-list-listp) (record-octets fn-cbor-octet-listp) (observed-name-octets fn-octet-list-listp)))

(definterface fn-owner-checkpoint-clone-phase
  :class :common-lisp-compliant
  :kinds ((marker-octets fn-cbor-octet-listp)))

(definterface fn-owner-clock-observation
  :class :common-lisp-compliant)

(definterface fn-owner-close
  :class ::program)

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
  :class ::program)

(definterface fn-owner-exposure-open
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-exposure-release
  :class ::program)

(definterface fn-owner-fault
  :class ::program)

(definterface fn-owner-feed-auth-policy
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-feed-backoff-ms
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

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
  :class ::program)

(definterface fn-owner-install-profile
  :class ::program)

(definterface fn-owner-io
  :class :common-lisp-compliant)

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
  :class :common-lisp-compliant)

(definterface fn-owner-live-post-config
  :class :common-lisp-compliant)

(definterface fn-owner-log-bounds
  :class :common-lisp-compliant)

(definterface fn-owner-log-reopen
  :class :common-lisp-compliant)

(definterface fn-owner-login-bindings-plan
  :class :common-lisp-compliant)

(definterface fn-owner-login-gate
  :class :common-lisp-compliant)

(definterface fn-owner-moderation-plan
  :class :common-lisp-compliant)

(definterface fn-owner-next-store-coordinates
  :class :common-lisp-compliant)

(definterface fn-owner-next-txid
  :class :common-lisp-compliant)

(definterface fn-owner-observe
  :class :common-lisp-compliant)

(definterface fn-owner-open
  :class ::program)

(definterface fn-owner-open-peer
  :class ::program
  :kinds ((peer-octets fn-cbor-octet-listp)))

(definterface fn-owner-operator-refusal-reason
  :class :common-lisp-compliant
  :kinds ((msgid-octets fn-cbor-octet-listp) (group-octets fn-octet-list-listp) (payload fn-cbor-octet-listp)))

(definterface fn-owner-outcome
  :class ::program)

(definterface fn-owner-peer-carried-relay-event
  :class ::program)

(definterface fn-owner-peer-carrier-form
  :class ::program)

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
  :class :common-lisp-compliant)

(definterface fn-owner-prepare-identity
  :class :common-lisp-compliant)

(definterface fn-owner-prepare-retention
  :class ::program
  :kinds ((id-octets fn-cbor-octet-listp) (subject-octets fn-cbor-octet-listp) (evidence-octets fn-cbor-octet-listp)))

(definterface fn-owner-prepare-topic
  :class :common-lisp-compliant)

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
  :class :common-lisp-compliant)

(definterface fn-owner-sco-capture
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

(definterface fn-owner-workflow-forward-pinnedp
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
  :class ::ideal
  :keystones (fn-bpah-handoff-report-is-application-disposition))

(definterface fn-bpah-outbox-effective-status
  :class ::common-lisp-compliant)

(definterface fn-bpah-outbox-peer-matchp
  :class ::common-lisp-compliant)

(definterface fn-bpah-outbox-view-after
  :class ::common-lisp-compliant)

(definterface fn-bpah-publication-authorize
  :class ::ideal
  :keystones (fn-bpah-publication-authorize-admits-exactly-the-issued-pending-delivery))

(definterface fn-bpah-publication-frame
  :class ::ideal)

(definterface fn-bpah-publication-name
  :class ::ideal)

(definterface fn-bpah-publication-operationp
  :class ::ideal)

(definterface fn-bpah-publication-publisher
  :class ::ideal)

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
  :kinds ((index natp)))

(definterface fn-bpfs-plan
  :class ::common-lisp-compliant
  :keystones (fn-bpfs-plan-fragments-restore-parent
              fn-bpfs-plan-fragments-reassemble-within-caps
              fn-bpfs-plan-fragments-reassemble-uncapped
              fn-bpfs-plan-fragments-reassemble-exactly
              fn-bpfs-plan-fragments-fit-mru))

(definterface fn-bphp-recover-auto-event
  :class ::ideal
  :keystones (fn-bphp-recover-auto-event-is-bpnr))

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
  :class ::ideal)

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
  :class ::ideal)

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
              fn-bpnp-contact-closes-only-when-nothing-owed-remains
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
  :class ::ideal
  :keystones (fn-bpnf-conflict-publication-success-binds-exact-echo))

(definterface fn-bpnf-conflict-publication-frame
  :class ::ideal)

(definterface fn-bpnf-conflict-publication-name
  :class ::ideal)

(definterface fn-bpnf-conflict-publication-operationp
  :class ::ideal)

(definterface fn-bpnf-conflict-publication-publisher
  :class ::ideal)

(definterface fn-bpnf-delete-publication-authorize
  :class ::ideal
  :keystones (fn-bpnf-delete-publication-authorize-admits-exactly-the-issued-pending-deletion))

(definterface fn-bpnf-delete-publication-frame
  :class ::ideal)

(definterface fn-bpnf-delete-publication-name
  :class ::ideal)

(definterface fn-bpnf-delete-publication-operationp
  :class ::ideal)

(definterface fn-bpnf-delete-publication-publisher
  :class ::ideal)

(definterface fn-bpnf-epoch
  :class ::common-lisp-compliant)

(definterface fn-bpnf-family-next
  :class ::common-lisp-compliant
  :keystones (fn-bpnf-family-next-selects-exactly-the-first-ready-family))

(definterface fn-bpnf-family-publication-authorize
  :class ::ideal
  :keystones (fn-bpnf-family-publication-authorize-admits-exactly-the-issued-pending-family))

(definterface fn-bpnf-family-publication-frame
  :class ::ideal)

(definterface fn-bpnf-family-publication-name
  :class ::ideal)

(definterface fn-bpnf-family-publication-operationp
  :class ::ideal)

(definterface fn-bpnf-family-publication-publisher
  :class ::ideal)

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
  :class ::ideal)

(definterface fn-bpnf-mixed-legacy-observed
  :class ::common-lisp-compliant)

(definterface fn-bpnf-mixed-received-names
  :class ::ideal)

(definterface fn-bpnf-mixed-recovery-plan
  :class ::common-lisp-compliant)

(definterface fn-bpnf-mixed-recovery-planp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-namespace-max-entries
  :class ::ideal)

(definterface fn-bpnf-publication-authorize
  :class ::ideal)

(definterface fn-bpnf-publication-operation-frame
  :class ::ideal)

(definterface fn-bpnf-publication-operation-name
  :class ::ideal)

(definterface fn-bpnf-publication-operation-publisher
  :class ::ideal)

(definterface fn-bpnf-publication-operationp
  :class ::ideal)

(definterface fn-bpnf-receive-wire-event-value
  :class ::common-lisp-compliant)

(definterface fn-bpnf-receive-wire-readyp
  :class ::common-lisp-compliant)

(definterface fn-bpnf-stored-frame-limit
  :class ::ideal)

(definterface fn-bpnf-stored-record-name
  :class ::ideal)

(definterface fn-bpnj-attempt-token
  :class ::ideal)

(definterface fn-bpnj-host-eventp
  :class ::ideal
  :keystones (fn-bpnj-host-refuses-an-unnamed-transport-result))

(definterface fn-bpnj-step
  :class ::ideal
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

(definterface fn-bpnp-configured-budgets
  :class ::common-lisp-compliant
  :keystones (fn-bpnp-configured-budgets-admits-exactly-the-frame-bounded-positive-budgets))

(definterface fn-bpnp-delivery-view
  :class ::common-lisp-compliant)

(definterface fn-bpnp-dispatch-publication-authorize
  :class ::ideal
  :keystones (fn-bpnp-dispatch-publication-authorize-admits-exactly-the-issued-pending-dispatch))

(definterface fn-bpnp-dispatch-publication-frame
  :class ::ideal)

(definterface fn-bpnp-dispatch-publication-name
  :class ::ideal)

(definterface fn-bpnp-dispatch-publication-operationp
  :class ::ideal)

(definterface fn-bpnp-dispatch-publication-publisher
  :class ::ideal)

(definterface fn-bpnp-forward-plan
  :class ::common-lisp-compliant
  :kinds ((held true-listp))
  :keystones (fn-bpnp-forward-plan-offers-a-row-on-one-session
              fn-bpnp-forward-plan-has-one-session-per-peer))

(definterface fn-bpnp-forward-publication-authorize
  :class ::ideal
  :keystones (fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward))

(definterface fn-bpnp-forward-publication-name
  :class ::ideal)

(definterface fn-bpnp-forward-publication-octets
  :class ::ideal)

(definterface fn-bpnp-forward-publication-operationp
  :class ::ideal
  :keystones (fn-bpnp-forward-publication-authorize-admits-exactly-the-issued-pending-forward))

(definterface fn-bpnp-forward-publication-publisher
  :class ::ideal)

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
  :class ::ideal)

(definterface fn-bpsr-host-preimage
  :class ::ideal)

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
  :class ::program)

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
  :class ::program)

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
  :class ::program)

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

(definterface fn-workflow-request-plan
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
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner-5).
(definterface fn-arpn-step
  :class :common-lisp-compliant)

;; books/control-request-word.lisp

; host/native/operator-live.lisp dispatches it (lane online-reclaim-5).
(definterface fn-crqw-request-word
  :class :common-lisp-compliant)

;; books/deflate-inflate.lisp

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-buffer-sizes
  :class :common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-buffers-ready
  :class :common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-feed
  :class :common-lisp-compliant
  :kinds ((b natp) (start natp) (end natp) (lim natp)))

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-refusal-text
  :class :common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress).
(definterface fn-zin-reset
  :class :common-lisp-compliant)

;; books/deflate-pool.lisp

; host/native/deflate.lisp dispatches it (lane compress-3).
(definterface fn-zpl-decode-bufs
  :class :common-lisp-compliant
  :kinds ((dict fn-cbor-octet-listp) (end natp) (n natp)))

;; books/extent-retire.lisp

; host/native/owner.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-quiet-files
  :class :common-lisp-compliant
  :kinds ((named true-listp)))

; host/native/owner.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-reseat-checkpoint-frame
  :class :common-lisp-compliant
  :kinds ((file natp) (start natp) (end natp)))

; host/native/io.lisp dispatches it (lane online-reclaim (composed-owner-4)).
(definterface fn-xrt-step-handles
  :class :common-lisp-compliant
  :kinds ((pst true-listp)))

;; books/history-image-snapshot.lisp

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-base-octets
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-binding
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-image-header
  :class :common-lisp-compliant
  :kinds ((np natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-image-header-np
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-np
  :class :common-lisp-compliant
  :kinds ((acc natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-release
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-skip-octets
  :class :common-lisp-compliant
  :kinds ((np natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-snapshot
  :class :common-lisp-compliant
  :kinds ((records true-listp) (salt natp)))

; host/native/io.lisp dispatches it (lane composed-owner).
(definterface fn-his-words
  :class :common-lisp-compliant
  :kinds ((sel natp) (a natp)))

;; books/limits-live.lisp

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-apply-row
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decide
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decision-reason
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-decision-status
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-funded-after
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-lim-reply-line
  :class :common-lisp-compliant)

; host/native/heap.lisp dispatches it (lane limits-live).
(definterface fn-lim-values-lines
  :class :common-lisp-compliant)

;; books/native-admin-shape.lisp

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-capacity
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-kind
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2).
(definterface fn-native-admin-result-name
  :class :common-lisp-compliant)

;; books/native-admin.lisp

; host/native/admin.lisp dispatches it (lane operability-5).
(definterface fn-native-admin-result-inspect-msgid
  :class :common-lisp-compliant)

;; books/native-control-reason.lisp

; host/native/control.lisp dispatches it (lane correctness-remainder).
(definterface fn-native-control-host-refusal-reason
  :class :common-lisp-compliant)

;; books/nntp-compress.lisp

; host/native/deflate.lisp dispatches it (lane compress-8).
(definterface fn-zc-deflate-params
  :class :common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane compress-8).
(definterface fn-zc-render-window-size
  :class :common-lisp-compliant)

; host/native/deflate.lisp dispatches it (lane compress-8).
(definterface fn-zc-sync-output-octets
  :class :common-lisp-compliant)

;; books/octets-stobj.lisp

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-oct-line-end
  :class :common-lisp-compliant
  :kinds ((i natp)))

;; books/open-frontier-wire.lisp

; host/native/io.lisp dispatches it (lane limits-live-5).
(definterface fn-ofw-wire-next
  :class :common-lisp-compliant)

;; books/owner-maintenance-request.lisp

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-control-path-octets
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-header-octets
  :class :common-lisp-compliant)

; host/native/io.lisp, host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-held-line
  :class :common-lisp-compliant
  :kinds ((verb stringp)))

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-live-report
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-status
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-inspect-word
  :class :common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-recover-line
  :class :common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-recover-status
  :class :common-lisp-compliant)

; host/native/io.lisp, host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-route
  :class :common-lisp-compliant)

; host/native/operator.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-status-replayp
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-stopped-health-report
  :class :ideal)

; host/native/io.lisp dispatches it (lane operability-2/-5).
(definterface fn-omr-stopped-report
  :class :ideal)

;; books/owner-time-bars.lisp

; host/native/owner.lisp dispatches it (lane composed-owner-3 (row A4)).
(definterface fn-otb-dependency-step
  :class :common-lisp-compliant)

;; books/payload-arena-extent-logic.lisp

; host/native/extent.lisp dispatches it (lane compress-5 (NNT-055)).
(definterface fn-arn-lz-extentp
  :class :common-lisp-compliant
  :direct "the raw body of A-ARENA-STORED's realizer (host/native/extent.lisp fn-arena-stored) recognizes the compressed extent itself; guard t")

;; books/payload-extent-read.lisp

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
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane compress-2).
(definterface fn-lzd-lookup
  :class :common-lisp-compliant)

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
  :class :common-lisp-compliant)

; host/native/admin.lisp, host/native/operator.lisp dispatches it (lane operability-3).
(definterface fn-record-string-octets
  :class :common-lisp-compliant)

;; books/store-checkpoint-open.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-sco-records
  :class :common-lisp-compliant)

;; host/bp-release-owner-host.lisp

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-pending-waivers
  :class :program)

; host/native/bp-obligation.lisp dispatches it (lane carry-abandon).
(definterface fn-owner-workflow-store-waive
  :class :program)

;; host/native-admin-host.lisp

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-native-admin-host-reclaim-mode
  :class :ideal)

;; host/native-control-host.lisp

; host/native/control.lisp dispatches it (lane d27-representation-3).
(definterface fn-native-control-host-decode-frame
  :class :program)

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
  :class :program)

;; host/owner-host.lisp

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-owner-apply-limit-profile
  :class :program)

; host/native/owner.lisp dispatches it (lane compress-8).
(definterface fn-owner-compress-owed
  :class :program)

; host/native/owner.lisp dispatches it (lane correctness-remainder).
(definterface fn-owner-control-reason
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-admit
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-done
  :class :program)

; host/native/mux.lisp dispatches it (lane tls-handshake-budget).
(definterface fn-owner-handshake-leave
  :class :program)

; host/native/admin.lisp dispatches it (lane limits-live).
(definterface fn-owner-limit-use
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-capture
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-chunk
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-classes
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-ctx
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-decide
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-finish
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-init
  :class :common-lisp-compliant)

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-request
  :class :program)

; host/native/admin.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orc-request-status
  :class :common-lisp-compliant)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-capture
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-finish
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-intern-chunk
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-keyring
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-load-columns
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-rebuild
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-salt
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-swap
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-swap-word
  :class :program)

; host/native/owner.lisp dispatches it (lane online-reclaim).
(definterface fn-owner-orcp-view-index
  :class :program)

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
  :class :program)

; host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-owner-sco-setup-of
  :class :program)

;; host/store-host.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner).
(definterface fn-store-genesis-ident
  :class :program)

;; host/store-node-host.lisp

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-his-file-octets
  :class :common-lisp-compliant)

; host/native/io.lisp, host/native/owner.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-his-stream-free
  :class :common-lisp-compliant)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-cfg-next-txid
  :class :program)

; host/native/admin.lisp, host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-lim-effective
  :class :program)

; host/native/admin.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-lim-use
  :class :program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-image-open
  :class :program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-note-checkpoint-digest
  :class :program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-publish-next
  :class :program)

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-publish-setup-of
  :class :program
  :exempt ((segment-octets "a segment descriptor, not bytes")))

; host/native/io.lisp dispatches it (lane composed-owner / limits-live / correctness-remainder).
(definterface fn-store-sco-want-checkpoint-digest
  :class :program)
