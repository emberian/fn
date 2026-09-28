;; fn: the BP ingress prepare over the retained row, without the history
;; replay (lane post-alloc, 2026-09-27).
;
; books/bp-ingress.lisp fn-bpi-ingress-prepare stages the ADU's row through
; fn-sn-prepare, the specification, whose file gate replays the whole durable
; history plus the candidate on every ADU: measured through
; tools/run_bp_ingress.py, 5.5 ms per prepare on an empty store and 322 ms
; after 200 ADUs.  fn-bpi-ingress-prepare-carried is that function with the
; one call replaced by the carried fn-pcar-spc-prepare
; (books/owner-prepare-carried.lisp), as books/store-prepare-carried.lisp
; does for the standalone store's POST.  Every other step (policy, parse,
; groups, record, intern at H) is the same text.
;
; KEYSTONE fn-bpi-ingress-prepare-carried-is-prepare: under fn-snt-relation
; (books/store-node-traces-prepare.lisp; established by the standalone open
; and kept by every live mutator, fn-spc-observed-open-run-maintains-
; relation) it IS fn-bpi-ingress-prepare, every argument.  The host line:
; host/bp-ingress-host.lisp fn-bpi-host-prepare.

(in-package "ACL2")
(include-book "bp-ingress")
(include-book "store-prepare-carried")
(local (include-book "article-properties"))

; The policy test without the whole-store recognizer: fn-bpi-policy-appliesp
; begins with (fn-sn-statep store), a walk of the whole durable history per
; ADU.  The carried prepare's guard is that recognizer, and the relation its
; keystone assumes implies it, so the carried test omits it.
(defun fn-bpi-policy-appliesp-carried (store policy context)
  (declare (xargs :guard t))
  (and (fn-bpi-policy-p policy) (fn-bpi-context-p context)
       (equal (fn-bpi-context-destination context)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-policy-endpoint policy)
              (fn-bpi-policy-destination policy))
       (equal (fn-bpi-map-values (fn-bpi-policy-group-map policy))
              (fn-sn-groups store))))

(defthm fn-bpi-policy-appliesp-carried-is-appliesp
  (implies (fn-sn-statep store)
           (equal (fn-bpi-policy-appliesp-carried store policy context)
                  (fn-bpi-policy-appliesp store policy context)))
  :hints (("Goal" :in-theory (enable fn-bpi-policy-appliesp))))

(defun fn-bpi-ingress-prepare-carried (store policy context adu h)
  (declare (xargs :guard (fn-sn-statep store) :verify-guards nil))
  (mbe :logic
(if (not (fn-bpi-policy-appliesp-carried store policy context))
      (list :rejected :policy-or-destination)
    (if (not (and (fn-cbor-octet-listp adu)
                  (<= (len adu) *fn-article-max-octets*)
                  (equal (fn-sf-phase (fn-sn-files store)) :reserved)))
        (list :rejected :adu-or-store-phase)
      (let ((parsed (fn-article-parse adu)))
        (if (not (fn-article-result-okp parsed))
            (list :rejected :article-syntax)
          (let ((proto (fn-af-proto-article-check
                        (fn-article-result-article parsed))))
            (if (not (equal (car proto) :ok))
                (list :rejected (car (cdr proto)))
              (let ((msgid (car (cdr proto)))
                    (groups (car (cdr (cdr proto)))))
                (if (not msgid)
                    (list :rejected :message-id-missing)
                  (let ((mapped (fn-bpi-map-groups
                                 groups (fn-bpi-policy-group-map policy))))
                    (if (not (equal (car mapped) :ok))
                        (list :rejected (car (cdr mapped)))
                      (let ((record (fn-bpi-record-for store policy context msgid groups adu)))
                        (if (equal record :clock-unusable)
                            (list :rejected :clock-unusable)
                        (if (and (fn-record-p record)
                                 (fn-selection-validp (fn-record-groups record)
                                                      (fn-sn-groups store)))
                            (let* ((row (fn-intern-row-at
                                         record (fn-sn-keyring store)
                                         (fn-sn-keyring-generation store) (nfix h)))
                                   (next (fn-pcar-spc-prepare store row)))
                              (if (equal next store)
                                  (list :rejected :store-refused)
                                (list :prepared next row record)))
                          (list :rejected :groups-or-record))))))))))))))
       :exec
(if (not (fn-bpi-policy-appliesp-carried store policy context))
      (list :rejected :policy-or-destination)
    (if (not (and (fn-cbor-octet-listp adu)
                  (<= (len adu) *fn-article-max-octets*)
                  (equal (fn-sf-phase (fn-sn-files store)) :reserved)))
        (list :rejected :adu-or-store-phase)
      (let ((parsed (fn-article-parse adu)))
        (if (not (fn-article-result-okp parsed))
            (list :rejected :article-syntax)
          (let ((proto (fn-af-proto-article-check
                        (fn-bpi-ag-result-article parsed))))
            (if (not (equal (fn-ag-car proto) :ok))
                (list :rejected (fn-ag-car (fn-ag-cdr proto)))
              (let ((msgid (fn-ag-car (fn-ag-cdr proto)))
                    (groups (fn-ag-car (fn-ag-cdr (fn-ag-cdr proto)))))
                (if (not msgid)
                    (list :rejected :message-id-missing)
                  (let ((mapped (fn-bpi-map-groups
                                 groups (fn-bpi-policy-group-map policy))))
                    (if (not (equal (fn-ag-car mapped) :ok))
                        (list :rejected (fn-ag-car (fn-ag-cdr mapped)))
                      (let ((record (fn-bpi-record-for store policy context msgid groups adu)))
                        (if (equal record :clock-unusable)
                            (list :rejected :clock-unusable)
                        (if (and (fn-record-p record)
                                 (fn-selection-validp (fn-bpi-ag-record-groups record)
                                                      (fn-sn-groups store)))
                            (let* ((row (fn-intern-row-at
                                         record (fn-sn-keyring store)
                                         (fn-sn-keyring-generation store) (nfix h)))
                                   (next (fn-pcar-spc-prepare store row)))
                              (if (equal next store)
                                  (list :rejected :store-refused)
                                (list :prepared next row record)))
                          (list :rejected :groups-or-record))))))))))))))))

(verify-guards fn-bpi-ingress-prepare-carried
  :hints (("Goal" :use ((:instance fn-article-successful-parse-syntax-p (octets adu)))
           :in-theory (disable fn-article-successful-parse-syntax-p fn-article-parse
                               fn-article-syntax-p fn-article-result-okp
                               fn-article-result-article fn-sn-article-record
                               fn-intern-row-at fn-pcar-spc-prepare fn-af-proto-article-check
                               fn-bpi-map-groups fn-record-stamp-of-observation
                               fn-bpi-policy-appliesp-carried))))

; KEYSTONE (the host's prepare line): on a related store the carried prepare
; is the specification's, every result.
(defthm fn-bpi-ingress-prepare-carried-is-prepare
  (implies (fn-snt-relation store)
           (equal (fn-bpi-ingress-prepare-carried store policy context adu h)
                  (fn-bpi-ingress-prepare store policy context adu h)))
  :hints (("Goal"
           :use ((:instance fn-spc-prepare-equals-specification-under-relation
                  (s store)
                  (record (fn-intern-row-at
                           (fn-bpi-record-for store policy context
                                              (car (cdr (fn-af-proto-article-check
                                                         (fn-article-result-article
                                                          (fn-article-parse adu)))))
                                              (car (cdr (cdr (fn-af-proto-article-check
                                                              (fn-article-result-article
                                                               (fn-article-parse adu))))))
                                              adu)
                           (fn-sn-keyring store) (fn-sn-keyring-generation store)
                           (nfix h)))))
           :in-theory (e/d (fn-bpi-ingress-prepare-carried fn-bpi-ingress-prepare
                            fn-pcar-spc-prepare-is-spc-prepare
                            fn-bpi-policy-appliesp-carried-is-appliesp)
                           (fn-snt-relation fn-spc-prepare fn-sn-prepare
                            fn-pcar-spc-prepare fn-intern-row-at fn-record-p
                            fn-article-parse fn-article-syntax-p fn-article-result-okp
                            fn-article-result-article fn-af-proto-article-check
                            fn-bpi-map-groups fn-bpi-record-for fn-bpi-policy-appliesp
                            fn-bpi-policy-appliesp-carried fn-article-parse-lines fn-cbor-octet-listp
                            fn-selection-validp)))))
