; Experimental BP ADU host boundary.  The only article grammar/admission path
; below is the certified fn-bpi composition; host code supplies bounded octets
; and observed, explicitly configured local transport provenance.
(in-package "ACL2")
(include-book "../books/bp-ingress")
(include-book "../books/bp-ingress-carried")
(include-book "../books/article-header-census")
(include-book "../books/bp-primary")
(include-book "../books/clock")
;; host-decisions-2 packet C: the reading-to-observation decision (fn-clkr-).
(include-book "../books/clock-reading")
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

(defun fn-bpi-host-policy (archive-id subject evidence charge)
  ; The host obtains these per-ADU values only after fn-bpi-host-message-id
  ; invokes the ACL2 article/field grammar.  It must not parse headers itself.
  (fn-bpi-make-policy *fn-bpi-host-destination* *fn-bpi-host-destination*
                      *fn-bpi-host-group-map* archive-id subject evidence charge
                      *fn-bpi-host-policy-id* *fn-bpi-host-terms-id*
                      *fn-bpi-host-issuer-eid*))

(defun fn-bpi-host-observation (monotonic-ns wall-ns wall-error-ms has-wall)
  ; The host reads two counters and states one error bound; the units, the
  ; DTN epoch and whether the wall is usable are ACL2's
  ; (books/clock-reading.lisp fn-clkr-observation-of-ns, KEYSTONE
  ; fn-clkr-observation-of-ns-decides-the-wall).  A wall reading before the
  ; DTN epoch, or a host that claims no wall clock, yields has-wall nil, which
  ; `fn-clock-expiry-decision` answers :uncertain for.
  (fn-clkr-observation-of-ns monotonic-ns wall-ns wall-error-ms has-wall))

(defun fn-bpi-host-context (destination source-eid bundle-id lifetime
                                       monotonic-ns wall-ns wall-error-ms has-wall)
  (fn-bpi-make-context (fn-store-octets->string destination)
                       (fn-store-octets->string source-eid)
                       (fn-store-octets->string bundle-id) lifetime
                       (fn-bpi-host-observation monotonic-ns wall-ns
                                                wall-error-ms has-wall)))

(defun fn-bpi-host-inputsp (destination source-eid bundle-id lifetime
                                        archive-id subject evidence charge)
  ; IDs are a host boundary representation only.  Source EID and local BID
  ; retain their observed value; none enters an article identity decision.
  ; The check is ACL2's: books/post-fields.lisp fn-pfld-bp-ingress-inputsp.
  (fn-pfld-bp-ingress-inputsp destination source-eid bundle-id lifetime
                              archive-id subject evidence charge))

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

; The article gate for an ADU, asked before the allocator reservation as the
; native `store post' asks it: `fn-store-sn-article-verdict' (the count gate
; and the history gate at `fn-sbud-article-figure') at the record
; `fn-bpi-ingress-prepare' would build, whose payload is the ADU and whose
; groups are its Newsgroups mapped through the host policy.  An ADU that
; composition rejects (syntax, Message-ID, an unmapped group) answers
; :rejected, never a budget word.
; A header past the profile's limits (PRF-230, PKT-660) answers the limit's
; name, as the served POST refuses it: `fn-article-census-refusal' against
; `fn-bs-profile-header-limits' of the same profile.
(defun fn-bpi-host-article-verdict (profile adu state)
  (declare (xargs :stobjs state :mode :program))
  (let ((parsed (fn-article-parse adu))
        (limit (fn-article-census-refusal
                (fn-article-header-census adu)
                (fn-bs-profile-header-limits profile))))
    (if (not (fn-article-result-okp parsed))
        (value :rejected)
      (if limit (value limit)
      (let ((proto (fn-af-proto-article-check
                    (fn-article-result-article parsed))))
        (if (not (and (equal (car proto) :ok) (car (cdr proto))))
            (value :rejected)
          (let ((mapped (fn-bpi-map-groups (car (cdr (cdr proto)))
                                           *fn-bpi-host-group-map*)))
            (if (not (equal (car mapped) :ok))
                (value :rejected)
              (fn-store-sn-article-verdict profile (len adu)
                                           (len (car (cdr mapped)))
                                           state)))))))))

(defun fn-bpi-host-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-store-sn-reset state))

; The records flip: the ADU is staged as the ROW interned at the arena's
; count, and sealed into the arena exactly when the Store staged it.  This
; entry READS the arena only (its count): an entry that updates the arena
; carries ACL2's invariant-risk, so it would run through its *1* body (every
; guard-verified callee checking its guard).  It answers (:seal ADU) and the
; host seals the ADU with one call of the guard-verified fn-arena-seal-list
; (tools/run_bp_ingress.py ingress_prepare -> run_store seal_named).  The
; prepare is the carried one (books/bp-ingress-carried.lisp KEYSTONE
; fn-bpi-ingress-prepare-carried-is-prepare, under fn-snt-relation: no replay
; of the durable history per ADU); with the seal it is the book's entry
; (books/bp-ingress.lisp fn-bpi-ingress-prepare-interned-unfolds; KEYSTONE
; fn-bpi-ingress-prepare-interned-row-is-the-received-adu).  The answer is
; (mv nil VALUE fn-arena state).
(defun fn-bpi-host-prepare (destination source-eid bundle-id lifetime
                                         archive-id subject evidence charge adu
                                         monotonic-ns wall-ns wall-error-ms has-wall
                                         fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (if (not (fn-bpi-host-inputsp destination source-eid bundle-id lifetime
                                 archive-id subject evidence charge))
      (mv nil :invalid fn-arena state)
    (let ((result
           (fn-bpi-ingress-prepare-carried
            (f-get-global 'fn-store-sn state)
            (fn-bpi-host-policy (fn-store-octets->string archive-id)
                                (fn-store-octets->string subject)
                                (fn-store-octets->string evidence) charge)
            (fn-bpi-host-context destination source-eid bundle-id lifetime
                                 monotonic-ns wall-ns wall-error-ms has-wall)
            adu (fn-arena-count fn-arena))))
      (if (equal (fn-bpi-result-kind result) :prepared)
          (let ((state (f-put-global 'fn-store-sn
                                     (fn-bpi-result-store result) state)))
            (mv nil (list :seal adu) fn-arena state))
        (mv nil (if (equal (fn-bpi-result-store result) :clock-unusable)
                    :clock-unusable
                  :rejected)
            fn-arena state)))))

; An exact durable replay is recognized by the certified parser/field/group
; composition and node binding before another allocator reservation is made.
; This gives a host a narrow basis to delete a still-staged BPA BID after a
; prior durable article acceptance; malformed and conflicting ADUs stay staged.
(defun fn-bpi-host-already-durablep (destination source-eid bundle-id lifetime
                                                 archive-id subject evidence charge
                                                 adu monotonic-ns wall-ns wall-error-ms
                                                 has-wall fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (if (not (fn-bpi-host-inputsp destination source-eid bundle-id lifetime
                                 archive-id subject evidence charge))
      (value nil)
    (value (fn-bpi-adu-durably-acceptedp
            (f-get-global 'fn-store-sn state)
            (fn-bpi-host-policy (fn-store-octets->string archive-id)
                                (fn-store-octets->string subject)
                                (fn-store-octets->string evidence) charge)
            (fn-bpi-host-context destination source-eid bundle-id lifetime
                                 monotonic-ns wall-ns wall-error-ms has-wall)
            adu fn-arena))))

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
