; Experimental BP ADU host boundary.  The only article grammar/admission path
; below is the certified fn-bpi composition; host code supplies bounded octets
; and observed, explicitly configured local transport provenance.
(in-package "ACL2")
(include-book "../books/bp-ingress")

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
