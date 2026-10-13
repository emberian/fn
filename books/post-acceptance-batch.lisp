; The acceptance machine binds batch output to the event's own transaction.
(in-package "ACL2")
(include-book "post-acceptance")
(include-book "post-acceptance-batch-bound")
(include-book "owner-prepare-deferred-carried")
(include-book "store-intern")
(include-book "runtime-contract-host-pool")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-pth-cs-is-derived
 (equal *fn-pth-cs* 65667) :rule-classes nil)

(local (defthm pbatch-norm-idempotent-l
 (equal (fn-pacc-norm (fn-pacc-norm a)) (fn-pacc-norm a))
 :hints (("Goal" :in-theory (union-theories '(fn-pacc-norm fn-pctx-get) (theory 'ground-zero))))))
(local (defthm pbatch-begin-normal-l
 (equal (fn-pacc-norm (fn-pacc-begin x)) (fn-pacc-begin x))
 :hints (("Goal" :in-theory (union-theories '(fn-pacc-norm fn-pacc-begin fn-pctx-get len) (theory 'ground-zero))))))
(local (defthm pbatch-feed-normal-l
 (equal (fn-pacc-feed* (fn-pacc-norm a) windows) (fn-pacc-norm a))
 :hints (("Goal" :induct (fn-pacc-feed* (fn-pacc-norm a) windows)
          :in-theory (union-theories '(fn-pacc-feed* fn-pacc-feed pbatch-norm-idempotent-l) (theory 'ground-zero))))))
(local (defthm pbatch-feed-begin-l
 (equal (fn-pacc-feed* (fn-pacc-begin x) windows) (fn-pacc-begin x))
 :hints (("Goal" :use ((:instance pbatch-feed-normal-l (a (fn-pacc-begin x))))
          :in-theory (union-theories '(pbatch-begin-normal-l) (theory 'ground-zero))))))
(local (defthm pbatch-context-natural-txid-l
 (implies (fn-pctx-p ctx) (natp (nth 0 ctx)))
 :hints (("Goal" :in-theory (union-theories '(fn-pctx-p) (theory 'ground-zero))))))

(defthm fn-pacc-end-of-a-stale-context-refuses
  (implies (not (equal ktxid (nth 0 ctx)))
           (not (mv-nth 0 (fn-pacc-end (fn-pacc-feed* (fn-pacc-begin (list ktxid ctx)) windows) blen))))
 :hints (("Goal" :use pbatch-context-natural-txid-l :in-theory
 (union-theories '(fn-pacc-end fn-pacc-begin fn-pctx-get pbatch-begin-normal-l
                   pbatch-feed-begin-l pbatch-context-natural-txid-l
                   (:executable-counterpart fn-pctx-p))
                 (theory 'ground-zero)))))

(defthm fn-pacc-batch-lays-out-only-at-its-txid
  (implies (mv-nth 0 (fn-pacc-end (fn-pacc-feed* (fn-pacc-begin (list ktxid (fn-pctx-of-batch row))) windows) blen))
           (equal (fn-rcon-store-event-txid row) ktxid))
 :hints (("Goal" :use ((:instance fn-pacc-end-of-a-stale-context-refuses (ctx (fn-pctx-of-batch row))))
 :in-theory (union-theories '(fn-pctx-of-batch) (theory 'ground-zero)))))

(local (defthm pbatch-wire-kind-l
 (implies (fn-pbatch-rowp row)
  (and (fn-wire-event-p row) (not (fn-held-p row)) (not (fn-hstxa-p row))
       (not (fn-record-p row)) (not (fn-stxa-p row))))
 :hints (("Goal" :use ((:instance fn-held-is-no-wire-event (x row))
                       (:instance fn-hstxa-is-no-wire-event (x row))
                       (:instance fn-record-is-no-other-wire-event (x row))
                       (:instance fn-stxa-is-no-other-wire-event (x row)))
 :in-theory (union-theories '(fn-pbatch-rowp fn-wire-event-p) (theory 'ground-zero))))))
(local (defthm pbatch-retention-txid-l
 (implies (fn-store-retention-event-p row) (and (natp (fn-store-event-nth 3 row)) (< (fn-store-event-nth 3 row) (expt 2 64))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory
   (union-theories '(fn-store-retention-event-p fn-record-uint32p) (theory 'ground-zero))))))
(local (defthm pbatch-stxe-txid-l
 (implies (fn-stxe-p row) (and (natp (fn-stxe-txid row)) (< (fn-stxe-txid row) (expt 2 64))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory
   (union-theories '(fn-stxe-p fn-record-uint32p) (theory 'ground-zero))))))
(local (defthm pbatch-stxk-txid-l
 (implies (fn-stxk-p row) (and (natp (fn-stxk-txid row)) (< (fn-stxk-txid row) (expt 2 64))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory
   (union-theories '(fn-stxk-p fn-record-uint32p) (theory 'ground-zero))))))
(local (defthm pbatch-consumer-txid-l
 (implies (fn-cpe-eventp row) (and (natp (fn-cpe-txid row)) (< (fn-cpe-txid row) (expt 2 64))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory
   (union-theories '(fn-cpe-eventp fn-cpe-txid fn-cp-uintp fn-record-uint32p) (theory 'ground-zero))))))
(local (defthm pbatch-topic-txid-l
 (implies (fn-th-topic-eventp row) (and (natp (fn-th-at 2 row)) (< (fn-th-at 2 row) (expt 2 64))))
 :rule-classes (:rewrite :forward-chaining)
 :hints (("Goal" :in-theory
   (union-theories '(fn-th-topic-eventp fn-record-uint32p) (theory 'ground-zero))))))
(local (defthm pbatch-txid-u64-l
 (implies (fn-pbatch-rowp row)
  (and (natp (fn-rcon-store-event-txid row))
       (< (fn-rcon-store-event-txid row) (expt 2 64))))
 :hints (("Goal" :in-theory
  (union-theories '(fn-pbatch-rowp fn-rcon-store-event-txid fn-store-event-txid
                    pbatch-wire-kind-l pbatch-retention-txid-l pbatch-stxe-txid-l
                    pbatch-stxk-txid-l pbatch-consumer-txid-l pbatch-topic-txid-l)
                  (theory 'ground-zero))))))
(local (defthm pbatch-context-p-l
 (implies (fn-pbatch-rowp row) (fn-pctx-p (fn-pctx-of-batch row)))
 :hints (("Goal" :use pbatch-txid-u64-l
 :in-theory (union-theories '(fn-pctx-p fn-pctx-of-batch nth len
                             (:executable-counterpart fn-cbor-octet-listp)
                             (:executable-counterpart fn-adm-acc-out-max))
                            (theory 'ground-zero))))))

(local (defthm pbatch-retention-staged-row-l
 (implies (fn-pout-stagedp s (fn-pdc-sn-prepare-retention s event))
  (equal (fn-sf-record-candidate (fn-sn-files (fn-pdc-sn-prepare-retention s event))) event))
 :hints (("Goal" :in-theory
  (union-theories '(fn-pdc-sn-prepare-retention fn-pout-stagedp fn-pcar-stage-record
                    fn-sn-files-of-fn-sn-update fn-sf-phase fn-sf-record-candidate
                    fn-sf-make-fields)
                  (theory 'ground-zero))))))
(defthm fn-pacc-retention-producer-stages-a-batch-event
  (let* ((after (fn-pdc-sn-prepare-retention s event))
         (row (fn-sf-record-candidate (fn-sn-files after))))
    (implies (and (fn-sn-statep s) (fn-store-retention-event-p event) (fn-pout-stagedp s after))
             (and (fn-store-retention-event-p row) (fn-pctx-p (fn-pctx-of-batch row)))))
 :hints (("Goal" :use ((:instance pbatch-context-p-l (row event)))
 :in-theory (union-theories '(pbatch-retention-staged-row-l fn-pbatch-rowp) (theory 'ground-zero)))))

(local (defthm pbatch-identity-staged-row-l
 (implies (fn-pout-stagedp s (fn-ccar-sn-prepare-identity s event))
  (equal (fn-sf-record-candidate (fn-sn-files (fn-ccar-sn-prepare-identity s event))) event))
 :hints (("Goal" :in-theory
  (union-theories '(fn-ccar-sn-prepare-identity fn-pout-stagedp fn-pcar-stage-record
                    fn-sn-files-of-fn-sn-update fn-sf-phase fn-sf-record-candidate
                    fn-sf-make-fields)
                  (theory 'ground-zero))))))
(defthm fn-pacc-identity-producer-stages-a-batch-event
  (let* ((after (fn-ccar-sn-prepare-identity s event))
         (row (fn-sf-record-candidate (fn-sn-files after))))
    (implies (and (fn-sn-statep s) (or (fn-stxk-p event) (fn-stxe-p event)) (fn-pout-stagedp s after))
             (and (or (fn-stxk-p row) (fn-stxe-p row)) (fn-pctx-p (fn-pctx-of-batch row)))))
 :hints (("Goal" :use ((:instance pbatch-context-p-l (row event)))
 :in-theory (union-theories '(pbatch-identity-staged-row-l fn-pbatch-rowp) (theory 'ground-zero)))))

(local (defthm pbatch-consumer-staged-row-l
 (implies (fn-pout-stagedp s (fn-pdc-sn-prepare-consumer s event))
  (equal (fn-sf-record-candidate (fn-sn-files (fn-pdc-sn-prepare-consumer s event))) event))
 :hints (("Goal" :in-theory
  (union-theories '(fn-pdc-sn-prepare-consumer fn-pout-stagedp fn-pcar-stage-record
                    fn-sn-files-of-fn-sn-update fn-sf-phase fn-sf-record-candidate
                    fn-sf-make-fields)
                  (theory 'ground-zero))))))
(defthm fn-pacc-consumer-producer-stages-a-batch-event
  (let* ((after (fn-pdc-sn-prepare-consumer s event))
         (row (fn-sf-record-candidate (fn-sn-files after))))
    (implies (and (fn-sn-statep s) (fn-cpe-eventp event) (fn-pout-stagedp s after))
             (and (fn-cpe-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))
 :hints (("Goal" :use ((:instance pbatch-context-p-l (row event)))
 :in-theory (union-theories '(pbatch-consumer-staged-row-l fn-pbatch-rowp) (theory 'ground-zero)))))

(local (defthm pbatch-topic-staged-row-l
 (implies (fn-pout-stagedp s (fn-pdc-sn-prepare-topic s event))
  (equal (fn-sf-record-candidate (fn-sn-files (fn-pdc-sn-prepare-topic s event))) event))
 :hints (("Goal" :in-theory
  (union-theories '(fn-pdc-sn-prepare-topic fn-pout-stagedp fn-pcar-stage-record
                    fn-sn-files-of-fn-sn-update fn-sf-phase fn-sf-record-candidate
                    fn-sf-make-fields)
                  (theory 'ground-zero))))))
(defthm fn-pacc-topic-producer-stages-a-batch-event
  (let* ((after (fn-pdc-sn-prepare-topic s event))
         (row (fn-sf-record-candidate (fn-sn-files after))))
    (implies (and (fn-sn-statep s) (fn-th-topic-eventp event) (fn-pout-stagedp s after))
             (and (fn-th-topic-eventp row) (fn-pctx-p (fn-pctx-of-batch row)))))
 :hints (("Goal" :use ((:instance pbatch-context-p-l (row event)))
 :in-theory (union-theories '(pbatch-topic-staged-row-l fn-pbatch-rowp) (theory 'ground-zero)))))

(local (defthm pbatch-u16-length-l
 (equal (len (fn-cbor-u16-bytes n)) 2)
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-u16-bytes len) (theory 'ground-zero))))))
(local (defthm pbatch-arg-five-l
 (<= (len (fn-cbor-encode-argument major n)) 5)
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-encode-argument len pbatch-u16-length-l fn-cp-u32-bytes-four) (theory 'ground-zero))))))
(local (defthm pbatch-uint-five-l
 (<= (len (fn-cbor-encode-bounded (cons :uint n) budget)) 5)
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-encode-bounded pbatch-arg-five-l) (theory 'ground-zero))))))
(local (defthm pbatch-bytes-five-l
 (<= (len (fn-cbor-encode-bounded (cons :bytes xs) budget)) (+ 5 (len xs)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-encode-bounded pbatch-arg-five-l fn-cp-len-append) (theory 'ground-zero))))))
(local (defthm pbatch-arg-sixty-four-l
 (implies (and (natp n) (<= n 64)) (<= (len (fn-cbor-encode-argument 2 n)) 2))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-encode-argument len) (theory 'ground-zero))))))
(local (defthm pbatch-bytes-sixty-four-l
 (implies (<= (len xs) 64)
   (<= (len (fn-cbor-encode-bounded (cons :bytes xs) budget)) 66))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-cbor-encode-bounded pbatch-arg-sixty-four-l fn-cp-len-append) (theory 'ground-zero))))))
(local (defthm pbatch-keyring-field-lengths-l
 (implies (fn-stxk-p row)
  (and (<= (len (fn-stxk-profile row)) *fn-stxk-max-profile*)
       (<= (len (fn-stxk-snapshot row)) *fn-stxk-max-snapshot*)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-stxk-p fn-stxe-bounded-octetsp) (theory 'ground-zero))))))
(local (defthm pbatch-keyring-codec-l
 (implies (fn-stxk-p row) (<= (len (fn-stxk-encode row)) *fn-pbatch-max*))
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-stxk-encode fn-stxk-items fn-stxe-encode-items-bounded
                    fn-cp-len-append pbatch-keyring-field-lengths-l pbatch-uint-five-l
                    pbatch-bytes-five-l pbatch-bytes-sixty-four-l
                    (:executable-counterpart fn-cbor-encode-bounded))
                  (theory 'ground-zero))))))

(local (defthm pbatch-evidence-field-lengths-l
 (implies (fn-stxe-p row)
  (and (<= (len (fn-record-string-octets (fn-stxe-msgid row))) *fn-record-max-msgid*)
       (<= (len (fn-stxe-profile row)) *fn-stxe-max-profile*)
       (<= (len (fn-stxe-detail row)) *fn-stxe-max-detail*)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories '(fn-stxe-p fn-stxe-bounded-octetsp fn-record-msgidp fn-record-nonempty-at-mostp) (theory 'ground-zero))))))
(local (defthm pbatch-evidence-codec-l
 (implies (fn-stxe-p row) (<= (len (fn-stxe-encode row)) *fn-pbatch-max*))
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-stxe-encode fn-stxe-items fn-stxe-encode-items fn-cbor-encode
                    fn-cp-len-append pbatch-evidence-field-lengths-l pbatch-uint-five-l
                    pbatch-bytes-five-l (:executable-counterpart fn-cbor-encode-bounded))
                  (theory 'ground-zero))))))
(local (defthm pbatch-retention-field-lengths-l
 (implies (fn-store-retention-event-p row)
  (and (<= (len (fn-record-string-octets (fn-store-event-obligation-id row))) *fn-record-max-metadata*)
       (<= (len (fn-record-string-octets (fn-store-event-subject row))) *fn-record-max-metadata*)
       (<= (len (fn-record-string-octets (fn-store-event-evidence row))) *fn-record-max-metadata*)))
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-store-retention-event-p fn-store-event-obligation-id fn-store-event-subject
                    fn-store-event-evidence fn-record-metadata-bytes-p fn-record-nonempty-at-mostp)
                  (theory 'ground-zero))))))
(local (defthm pbatch-retention-codec-l
 (implies (fn-store-retention-event-p row) (<= (len (fn-store-retention-event-encode row)) *fn-pbatch-max*))
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-store-retention-event-encode fn-cbor-encode fn-cp-len-append
                    pbatch-retention-field-lengths-l pbatch-uint-five-l pbatch-bytes-five-l
                    (:executable-counterpart fn-cbor-encode-bounded))
                  (theory 'ground-zero))))))
(local (defthm pbatch-cp-fields-length-l
 (implies (fn-cp-fields-validp vals kinds)
  (<= (len (fn-cp-fields-encode vals kinds)) (* 65 (len kinds))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cp-fields-encode vals kinds)
  :in-theory (union-theories '(fn-cp-fields-validp fn-cp-fields-encode fn-cp-id-bytes
                              fn-cp-id-length-bound fn-cp-u32-bytes-four fn-cp-len-append len)
                            (theory 'ground-zero))))))
(local (defthm pbatch-three-u32-length-l
 (equal (len (fn-cp-fields-encode (list a b c) '(:uint :uint :uint))) 12)
 :hints (("Goal" :in-theory
  (union-theories '(fn-cp-fields-encode fn-cp-u32-bytes-four fn-cp-len-append len)
                  (theory 'ground-zero))))))

(local (defthm pbatch-cursor-length-l
 (<= (len (fn-cp-cursor-encode cursor)) 346)
 :rule-classes :linear
 :hints (("Goal" :use fn-cp-cursor-encode-length-bound :in-theory (theory 'ground-zero)))))

(local (defthm pbatch-consumer-codec-l
 (implies (fn-cpe-eventp row) (<= (len (fn-cpe-encode row)) *fn-pbatch-max*))
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-cpe-encode fn-cpe-eventp fn-cpe-operationp fn-cpe-operation fn-cpe-kinds
                    fn-cp-nth fn-cpe-sequence fn-cpe-txid fn-cpe-generation pbatch-three-u32-length-l
                    fn-cp-len-append fn-cp-u32-bytes-four pbatch-cursor-length-l
                    pbatch-cp-fields-length-l len)
                  (theory 'ground-zero))))))
(local (defthm pbatch-at-most-length-l
 (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
 :rule-classes :linear
 :hints (("Goal" :use fn-cp-at-most-length :in-theory (theory 'ground-zero)))))
(local (defthm pbatch-topic-codec-l
 (<= (len (fn-th-topic-event-encode row)) *fn-pbatch-max*)
 :rule-classes :linear
 :hints (("Goal" :in-theory
  (union-theories '(fn-th-topic-event-encode pbatch-at-most-length-l len) (theory 'ground-zero))))))

(local (defthm pbatch-alpha-is-row-l
 (implies (fn-pbatch-rowp row) (equal (fn-row-wire-of row fn-arena) row))
 :hints (("Goal" :use pbatch-wire-kind-l
  :in-theory (union-theories '(fn-row-wire-of) (theory 'ground-zero))))))
(defthm fn-pbatch-encoded-event-bounded
  (implies (fn-pbatch-rowp row)
           (<= (len (fn-rcon-store-event-encode (fn-row-wire-of row fn-arena))) *fn-pbatch-max*))
 :hints (("Goal" :use pbatch-wire-kind-l
  :in-theory (union-theories '(fn-rcon-store-event-encode fn-rcon-record-p-is-record-p
                              fn-pbatch-rowp pbatch-alpha-is-row-l
                              pbatch-keyring-codec-l pbatch-evidence-codec-l
                              pbatch-retention-codec-l pbatch-consumer-codec-l pbatch-topic-codec-l)
                            (theory 'ground-zero)))))
