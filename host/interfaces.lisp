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
; Declared so far: the extraction roots and EXTRA functions
; (tools/extract/build.sh), and every entry with a byte-carrying formal its
; guard leaves unkinded (the former ENTRY_KIND_EXEMPT).  An undeclared entry
; is not refused; the registry says how many of the host's entries are
; declared.

(in-package "ACL2")
(include-book "../books/definterface")

; -----------------------------------------------------------------------------
; The extraction roots: the functions the extracted served program's driver
; calls (tools/extract/build.sh ROOTS, in that order).

(definterface create-fn-arena
  :class :common-lisp-compliant
  :root :extract)

(definterface fn-reader-use-seed
  :class :program
  :keystones ((fn-rdc-selection-establishes :via fn-rdc-selection))
  :root :extract)

(definterface fn-reader-set-posting
  :class :program
  :root :extract)

(definterface fn-reader-model-octets
  :class :program
  :root :extract)

(definterface fn-reader-reset
  :class :program
  :keystones ((fn-rdc-reset-is-served-open :via fn-rdc-reset))
  :root :extract)

(definterface fn-reader-chunk
  :class :program
  :kinds ((octets fn-cbor-octet-listp))
  :keystones ((fn-oag-served-step-submission-names-the-pinned-agent :via fn-served-step))
  :root :extract)

(definterface fn-reader-outcome
  :class :program
  :keystones ((fn-own-consumed-completion-is-240-or-uncertain
               :via fn-served-post-outcome))
  :root :extract)

(definterface fn-reader-observe-clock
  :class :program
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

; fn-xo-open-store: host/interfaces-extract.lisp (the image does not load
; host/store-open-host.lisp).

(definterface fn-reader-use-store
  :class :program
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

(definterface fn-store-sco-publish-setup
  :class :program
  :exempt ((segment-octets "a segment descriptor, not bytes")))

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
  :class :ideal
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
  :direct "runs in handlers, where a dispatcher's own fault would recurse")
