; Experimental BP ADU host boundary.  The only article grammar/admission path
; below is the certified fn-bpi composition; host code supplies bounded octets
; and observed, explicitly configured local transport provenance.
(in-package "ACL2")
(include-book "../books/bp-ingress")
(include-book "../books/bp-primary")
(include-book "../books/clock")
;
; Loaded here, not left to a bridge's `ld' order: this file uses names
; host/store-node-host.lisp (and host/store-host.lisp under it) defines, so a session that loads this file alone
; must get them too.  A second `ld' of a file already in the session
; re-admits identical definitions, which ACL2 accepts as redundant.
(ld "store-node-host.lisp" :ld-error-action :error)

(defconst *fn-bpi-host-destination* "dtn://fn.lab/inbox")
(defconst *fn-bpi-host-group-map*
  (list (list '(102 110 46 108 101 116 116 101 114 115) "fn.letters")
        (list '(102 110 46 116 101 115 116) "fn.test")))
(defconst *fn-bpi-host-policy-id* "bp-lab-policy-v0")
(defconst *fn-bpi-host-terms-id* "bp-lab-terms-v0")
(defconst *fn-bpi-host-issuer-eid* "dtn://fn.lab/issuer")

(defun fn-bpi-host-textp (octets)
  ; IDs are a host boundary representation only.  Source EID and local BID
  ; retain their observed value; none enters an article identity decision.
  (fn-store-text-octetsp octets))

(defun fn-bpi-host-policy (archive-id subject evidence charge)
  ; The host obtains these per-ADU values only after fn-bpi-host-message-id
  ; invokes the ACL2 article/field grammar.  It must not parse headers itself.
  (fn-bpi-make-policy *fn-bpi-host-destination* *fn-bpi-host-destination*
                      *fn-bpi-host-group-map* archive-id subject evidence charge
                      *fn-bpi-host-policy-id* *fn-bpi-host-terms-id*
                      *fn-bpi-host-issuer-eid*))

(defun fn-bpi-host-context (destination source-eid bundle-id lifetime)
  (fn-bpi-make-context (fn-store-octets->string destination)
                       (fn-store-octets->string source-eid)
                       (fn-store-octets->string bundle-id) lifetime))

(defun fn-bpi-host-inputsp (destination source-eid bundle-id lifetime
                                        archive-id subject evidence charge)
  (and (fn-bpi-host-textp destination) (fn-bpi-host-textp source-eid)
       (fn-bpi-host-textp bundle-id) (fn-record-uint32p lifetime)
       (fn-bpi-host-textp archive-id) (fn-bpi-host-textp subject)
       (fn-bpi-host-textp evidence) (fn-record-uint32p charge) (posp charge)))

(defun fn-bpi-host-message-id (adu state)
  ; Return only a successful exact Message-ID octet list.  This is the host's
  ; sole extraction boundary before it calls run_store.metadata; no host text
  ; parser, regular expression, or normalization selects headers.
  (declare (xargs :stobjs state :mode :program))
  (let ((parsed (fn-article-parse adu)))
    (if (not (fn-article-result-okp parsed))
        (value nil)
      (let ((proto (fn-af-proto-article-check
                    (fn-article-result-article parsed))))
        (if (and (equal (car proto) :ok) (car (cdr proto)))
            (value (car (cdr proto)))
          (value nil))))))

(defun fn-bpi-host-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-store-sn-reset state))

(defun fn-bpi-host-prepare (destination source-eid bundle-id lifetime
                                         archive-id subject evidence charge adu state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-bpi-host-inputsp destination source-eid bundle-id lifetime
                                 archive-id subject evidence charge))
      (value :invalid)
    (let ((result (fn-bpi-ingress-prepare
                   (f-get-global 'fn-store-sn state)
                   (fn-bpi-host-policy (fn-store-octets->string archive-id)
                                       (fn-store-octets->string subject)
                                       (fn-store-octets->string evidence) charge)
                   (fn-bpi-host-context destination source-eid bundle-id lifetime)
                   adu)))
      (if (equal (fn-bpi-result-kind result) :prepared)
          (let ((state (f-put-global 'fn-store-sn
                                     (fn-bpi-result-store result) state)))
            (value :prepared))
        (value :rejected)))))

; An exact durable replay is recognized by the certified parser/field/group
; composition and node binding before another allocator reservation is made.
; This gives a host a narrow basis to delete a still-staged BPA BID after a
; prior durable article acceptance; malformed and conflicting ADUs stay staged.
(defun fn-bpi-host-already-durablep (destination source-eid bundle-id lifetime
                                                 archive-id subject evidence charge
                                                 adu state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-bpi-host-inputsp destination source-eid bundle-id lifetime
                                 archive-id subject evidence charge))
      (value nil)
    (value (fn-bpi-adu-durably-acceptedp
            (f-get-global 'fn-store-sn state)
            (fn-bpi-host-policy (fn-store-octets->string archive-id)
                                (fn-store-octets->string subject)
                                (fn-store-octets->string evidence) charge)
            (fn-bpi-host-context destination source-eid bundle-id lifetime)
            adu))))

; -----------------------------------------------------------------------------
; Bundle identity and expiry (RFC 9171 sections 4.1, 4.2.7, 4.3.1 and 5.5)
;
; Added for the receive boundary: the host hands over the raw octets one BPA
; produced and ACL2 answers three questions about them -- is this a bundle we
; can identify at all, what is its identity, and is it still live.  Nothing in
; Python decides any of these, and the BID the agent issued is not consulted.
;
; RFC 9171 section 4.1 frames a bundle as an indefinite-length CBOR array whose
; first element is the primary block.  `books/bp-primary.lisp` models the
; primary block and not that frame, so the split is here: check the one
; indefinite-array head octet, decode exactly one CBOR item from what follows
; with the certified decoder, and hand those octets -- and only those -- to
; `fn-bpp-decode`, which re-encodes them and refuses any non-canonical
; spelling.  No other block is examined, so the payload length is not
; available and `fn-bpp-bundle-id` is not the identity used here; see
; `fn-bpp-primary-identity` for what that costs and why it is sound for
; staging.

(defconst *fn-bpi-host-bundle-head* 159)   ; CBOR indefinite-length array head
(defconst *fn-bpi-host-dtn-epoch-ms* 946684800000) ; 2000-01-01T00:00:00Z, Unix ms

(defun fn-bpi-host-primary-octets (bundle)
  ; The exact octets of the bundle's first CBOR item, or nil.
  (declare (xargs :mode :program))
  (if (not (and (fn-cbor-octet-listp bundle)
                (consp bundle)
                (equal (car bundle) *fn-bpi-host-bundle-head*)))
      nil
    (let* ((rest (cdr bundle))
           (decoded (fn-bpc-decode rest)))
      (if (not (fn-cbor-result-okp decoded))
          nil
        (let ((consumed (- (len rest) (len (fn-cbor-result-rest decoded)))))
          (if (or (not (natp consumed)) (equal consumed 0))
              nil
            (take consumed rest)))))))

(defun fn-bpi-host-bundle-block (bundle)
  ; The decoded primary block, or a distinct refusal.  Three outcomes stay
  ; apart: :not-a-bundle (no indefinite array head, or no first CBOR item),
  ; the codec's own reason, and :anonymous (a dtn:none source, which RFC 9171
  ; section 4.2.3 says is not uniquely identifiable at all).
  (declare (xargs :mode :program))
  (let ((octets (fn-bpi-host-primary-octets bundle)))
    (if (null octets)
        (fn-bpp-error :not-a-bundle)
      (let ((result (fn-bpp-decode octets)))
        (if (not (fn-bpp-result-okp result))
            result
          (if (not (fn-bpp-identifiablep (fn-bpp-result-block result)))
              (fn-bpp-error :anonymous)
            result))))))

(defun fn-bpi-host-observation (monotonic-ns wall-ns wall-error-ms has-wall)
  ; The host reads two counters and states one error bound; the units and the
  ; DTN epoch are converted here, not in Python.  A wall reading before the
  ; DTN epoch, or a host that claims no wall clock, yields has-wall nil, which
  ; `fn-clock-expiry-decision` answers :uncertain for.
  (declare (xargs :mode :program))
  (let* ((monotonic (if (natp monotonic-ns) (floor monotonic-ns 1000000) 0))
         (unix-ms (if (natp wall-ns) (floor wall-ns 1000000) 0))
         (usable (and has-wall (natp wall-ns)
                      (<= *fn-bpi-host-dtn-epoch-ms* unix-ms)
                      (natp wall-error-ms)))
         (wall (if usable (- unix-ms *fn-bpi-host-dtn-epoch-ms*) 0)))
    (fn-clock-observation (min monotonic *fn-clock-max*)
                          (min wall *fn-clock-max*)
                          (if usable (min wall-error-ms *fn-clock-max*) 0)
                          usable)))

(defun fn-bpi-host-bundle-report (bundle monotonic-ns wall-ns wall-error-ms has-wall)
  ; One answer for the whole receive boundary.  A refusal is (:REFUSED reason);
  ; an acceptance is (:OK identity decision source creation sequence offset
  ; total), where `identity` is the canonical primary-block identity octets,
  ; `decision` is fn-clock-expiry-decision`s verdict and the rest is what the
  ; differential test compares against the agent`s own metadata.
  (declare (xargs :mode :program))
  (let ((result (fn-bpi-host-bundle-block bundle)))
    (if (not (fn-bpp-result-okp result))
        (list :refused (nth 1 result))
      (let* ((b (fn-bpp-result-block result))
             (obs (fn-bpi-host-observation monotonic-ns wall-ns
                                           wall-error-ms has-wall)))
        (list :ok
              (fn-bpp-primary-identity b)
              (fn-clock-expiry-decision (fn-bpp-creation-time b)
                                        (fn-bpp-lifetime b) nil obs)
              (fn-bpp-source b)
              (fn-bpp-creation-time b)
              (fn-bpp-sequence b)
              (fn-bpp-fragment-offset b)
              (fn-bpp-total-adu-length b))))))

; The bundle frame, for a laboratory that needs one bundle`s exact octets: the
; indefinite-array head and the certified primary-block encoding.  A caller
; appends the remaining blocks and the break stop code, which this boundary
; does not interpret -- exactly as the host appends the integrity trailer to a
; frame prefix it did not build.
(defun fn-bpi-host-bundle-prefix (b)
  (declare (xargs :mode :program))
  (if (not (fn-bpp-blockp b))
      :invalid
    (cons *fn-bpi-host-bundle-head* (fn-bpp-encode b))))
