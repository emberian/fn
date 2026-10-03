; HST-047/PRF-1259: private typed output-pool projection. The flat bank is
; shared across connections; original archive/text references are not copied
; or charged again. Complete allocation tariffs and principal delegation are
; still owed before this projection can become an accounted operation gate.
(in-package "ACL2")
(include-book "resource-vector-exec")
(include-book "output-reservation")

(defun fn-rlo-resident-vector (octets)
  (declare (xargs :guard t))
  (list (nfix octets) 0 0 0 0 0 0 0 0))

; Private output instance column meanings (no shared live stobj): IDS is a
; free-row link, CIDS the connection identity, FILES its generation, EOFFS
; the independent window operation generation, ELENS the output receipt,
; TRAILERS the physical dependency receipt. Scalars NEXT and FILE-LIMIT are
; the free head and quantum heap lease. These do not alter FN-RL-BANK.
(defun fn-rlo-free-init (slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger) (natp slot)
                              (<= slot (fn-rl-count fn-resource-ledger)))
                  :measure (nfix (- (nfix (fn-rl-count fn-resource-ledger)) (nfix slot)))))
  (if (not (and (natp slot) (natp (fn-rl-count fn-resource-ledger))
                (< slot (fn-rl-count fn-resource-ledger)))) fn-resource-ledger
    (let ((fn-resource-ledger
           (update-fn-rl-idsi slot
             (if (< (+ 1 slot) (fn-rl-count fn-resource-ledger)) (+ 1 slot) 0)
             fn-resource-ledger)))
      (fn-rlo-free-init (+ 1 slot) fn-resource-ledger))))

(defun fn-rlo-install (dynamic store-need cold policy slots fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (if (not (fn-rl-wfp fn-resource-ledger))
      (mv :invalid-output-install-state fn-resource-ledger)
    (let ((grant (fn-orv-startup-grant dynamic store-need cold policy slots)))
    (if (not (eq (car grant) :hold)) (mv (cadr grant) fn-resource-ledger)
      (mv-let (word fn-resource-ledger)
        (fn-rl-install (fn-rlo-resident-vector (nth 1 grant))
                       (fn-rlo-resident-vector (nth 3 grant))
                       (fn-rlo-resident-vector (nth 2 grant))
                       slots fn-resource-ledger)
        (if (not (eq word :installed)) (mv word fn-resource-ledger)
         (if (not (and (fn-rl-wfp fn-resource-ledger)
                       (<= 3 (fn-rl-count fn-resource-ledger))
                       (unsigned-byte-p 64 (nth 2 grant))))
             (mv :invalid-output-install-state fn-resource-ledger)
          (let* ((fn-resource-ledger (fn-rlo-free-init 2 fn-resource-ledger))
                 (fn-resource-ledger (update-fn-rl-next 2 fn-resource-ledger))
                 (fn-resource-ledger (update-fn-rl-file-limit (nth 2 grant) fn-resource-ledger))
                 (fn-resource-ledger (update-fn-rl-mode 2 fn-resource-ledger)))
            (mv :installed fn-resource-ledger)))))))))

(defun fn-rlo-ready-p (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t))
  (and (fn-rl-wfp fn-resource-ledger) (equal (fn-rl-mode fn-resource-ledger) 2)
       (posp (fn-rl-file-limit fn-resource-ledger))
       (<= 3 (fn-rl-count fn-resource-ledger))))

; Read the installed private ledger rather than mutable service configuration.
; Zero means this instance cannot authorize a response lease.
(defun fn-rlo-capacity (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t))
  (if (fn-rlo-ready-p fn-resource-ledger)
      (fn-rl-file-limit fn-resource-ledger)
    0))

(defthm fn-rlo-capacity-unfolds
  (equal (fn-rlo-capacity ledger)
         (if (fn-rlo-ready-p ledger) (fn-rl-file-limit ledger) 0)))

(defun fn-rlo-token (cid connection-gen slot draw-gen)
  (declare (xargs :guard t))
  (list :resource (list :connection cid connection-gen) slot draw-gen))

; Fixed constructor shape, bounded checks even on malformed input. Tokens
; are internal custody values; they are never parsed by the Lisp reader.
(defun fn-rlo-tokenp (token)
  (declare (xargs :guard t))
  (and (consp token) (eq (car token) :resource)
       (consp (cdr token)) (consp (cddr token)) (consp (cdddr token))
       (null (cddddr token))
       (let ((owner (cadr token)))
         (and (consp owner) (eq (car owner) :connection)
              (consp (cdr owner)) (consp (cddr owner)) (null (cdddr owner))
              (natp (cadr owner)) (natp (caddr owner))))
       (natp (caddr token)) (<= 2 (caddr token)) (natp (cadddr token))))

(defun fn-rlo-livep (token operation-gen fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-rlo-ready-p fn-resource-ledger) (fn-rlo-tokenp token)
       (< (caddr token) (fn-rl-count fn-resource-ledger))
       (equal (fn-rl-phasesi (caddr token) fn-resource-ledger) 1)
       (equal (fn-rl-gensi (caddr token) fn-resource-ledger) (cadddr token))
       (equal (fn-rl-cidsi (caddr token) fn-resource-ledger) (cadr (cadr token)))
       (equal (fn-rl-filesi (caddr token) fn-resource-ledger) (caddr (cadr token)))
       (equal (fn-rl-eoffsi (caddr token) fn-resource-ledger) operation-gen)))

; Issue before semantic materialization. :NONE asserts this scoped quantum
; issues no physical I/O; :ISSUED must retain its draw through actual terminal
; confirmation. Neither timeout nor closing a socket changes either receipt.
(defun fn-rlo-issue (cid connection-gen operation-gen dependency fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond
   ((not (and (natp cid) (<= cid *fn-rl-word-max*)
              (natp connection-gen) (<= connection-gen *fn-rl-word-max*)
              (natp operation-gen) (<= operation-gen *fn-rl-word-max*)
              (member-eq dependency '(:none :issued))))
    (mv :invalid-output-identity nil fn-resource-ledger))
   ((not (fn-rlo-ready-p fn-resource-ledger)) (mv :not-installed nil fn-resource-ledger))
   ((equal (fn-rl-next fn-resource-ledger) 0) (mv :no-output-window nil fn-resource-ledger))
   (t
    (let ((slot (fn-rl-next fn-resource-ledger)))
      (if (not (and (<= 2 slot) (< slot (fn-rl-count fn-resource-ledger))
                    (< (fn-rl-idsi slot fn-resource-ledger) (fn-rl-count fn-resource-ledger))))
          (mv :invalid-output-free-row nil fn-resource-ledger)
        (mv-let (word gen fn-resource-ledger)
          (fn-rl-draw slot (fn-rlo-resident-vector (fn-rl-file-limit fn-resource-ledger))
                     fn-resource-ledger)
          (if (not (eq word :drawn)) (mv word nil fn-resource-ledger)
            (let* ((fn-resource-ledger (update-fn-rl-next (fn-rl-idsi slot fn-resource-ledger) fn-resource-ledger))
                   (fn-resource-ledger (update-fn-rl-cidsi slot cid fn-resource-ledger))
                   (fn-resource-ledger (update-fn-rl-filesi slot connection-gen fn-resource-ledger))
                   (fn-resource-ledger (update-fn-rl-eoffsi slot operation-gen fn-resource-ledger))
                   (fn-resource-ledger (update-fn-rl-elensi slot 0 fn-resource-ledger))
                   (fn-resource-ledger (update-fn-rl-trailersi slot (if (eq dependency :none) 1 0) fn-resource-ledger)))
              (mv :drawn (fn-rlo-token cid connection-gen slot gen) fn-resource-ledger)))))))))

(defun fn-rlo-settle-ready (slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (fn-rl-wfp fn-resource-ledger) (natp slot)
                              (< slot (fn-rl-count fn-resource-ledger)))))
  (if (not (and (equal (fn-rl-elensi slot fn-resource-ledger) 1)
                 (equal (fn-rl-trailersi slot fn-resource-ledger) 1)))
      (mv :pending fn-resource-ledger)
    (mv-let (word fn-resource-ledger)
      (fn-rl-settle slot (fn-rl-gensi slot fn-resource-ledger) fn-resource-ledger)
      (if (not (eq word :settled)) (mv word fn-resource-ledger)
        (let* ((fn-resource-ledger (update-fn-rl-idsi slot (fn-rl-next fn-resource-ledger) fn-resource-ledger))
               (fn-resource-ledger (update-fn-rl-next slot fn-resource-ledger)))
          (mv :settled fn-resource-ledger))))))

(defun fn-rlo-output (token operation-gen receipt fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond ((not (fn-rlo-livep token operation-gen fn-resource-ledger)) (mv :stale fn-resource-ledger))
        ((not (member-eq receipt '(:drained :discarded))) (mv :pending fn-resource-ledger))
        (t (let ((fn-resource-ledger (update-fn-rl-elensi (caddr token) 1 fn-resource-ledger)))
             (fn-rlo-settle-ready (caddr token) fn-resource-ledger)))))

(defun fn-rlo-physical (token operation-gen receipt fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (cond ((not (fn-rlo-livep token operation-gen fn-resource-ledger)) (mv :stale fn-resource-ledger))
        ((not (member-eq receipt '(:terminal :no-actor-created))) (mv :pending fn-resource-ledger))
        (t (let ((fn-resource-ledger (update-fn-rl-trailersi (caddr token) 1 fn-resource-ledger)))
             (fn-rlo-settle-ready (caddr token) fn-resource-ledger)))))

; Fixed resident projection read, never a scan of the connection table.
; Native shutdown additionally requires its retained custody roster empty.
(defun fn-rlo-drainedp (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-rlo-ready-p fn-resource-ledger)
       (equal (fn-rl-drawni 0 fn-resource-ledger)
              (+ (nfix (fn-rl-c0i 0 fn-resource-ledger))
                 (nfix (fn-rl-c0i 1 fn-resource-ledger))))))

 ; Typed representation and guards cover the actual private output methods.
; Free-row protocol/bank correspondence and complete allocation tariffs remain
; PRF-1259 work; this is not yet a complete accounted-operation gate.
 ; Typed representation and guards cover the actual private output methods.
; Free-row protocol/bank correspondence and complete allocation tariffs remain
; PRF-1259 work; this is not yet a complete accounted-operation gate.
(verify-guards fn-rlo-free-init :hints (("Goal" :in-theory (enable fn-rl-wfp))))
(verify-guards fn-rlo-livep :hints (("Goal" :in-theory (enable fn-rlo-ready-p fn-rl-wfp))))
(verify-guards fn-rlo-drainedp :hints (("Goal" :in-theory (enable fn-rlo-ready-p fn-rl-wfp))))
(encapsulate ()
(local (defthm fn-rlo-scalar-types
 (implies (fn-resource-ledgerp ledger)
  (and (unsigned-byte-p 32 (fn-rl-count ledger))
       (unsigned-byte-p 64 (fn-rl-next ledger))
       (unsigned-byte-p 64 (fn-rl-file-limit ledger))))
 :hints (("Goal" :in-theory
  (union-theories
   '(fn-resource-ledgerp fn-rl-count fn-rl-countp fn-rl-next fn-rl-nextp
     fn-rl-file-limit fn-rl-file-limitp unsigned-byte-p integer-range-p)
   (theory 'minimal-theory))))))

(local (defthm fn-rlo-count-nat
 (implies (fn-resource-ledgerp ledger) (natp (fn-rl-count ledger)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :use fn-rlo-scalar-types :in-theory (e/d (unsigned-byte-p integer-range-p) (fn-resource-ledgerp fn-rl-count fn-rlo-scalar-types))))))

(local (defthm fn-rlo-next-word
 (implies (fn-resource-ledgerp ledger) (unsigned-byte-p 64 (fn-rl-next ledger)))
 :hints (("Goal" :use fn-rlo-scalar-types :in-theory (disable fn-resource-ledgerp fn-rl-next fn-rlo-scalar-types)))))

(local (defthm fn-rlo-count-bound
 (implies (fn-resource-ledgerp ledger) (< (fn-rl-count ledger) 4294967296))
 :rule-classes :linear
 :hints (("Goal" :use fn-rlo-scalar-types :in-theory (e/d (unsigned-byte-p integer-range-p) (fn-resource-ledgerp fn-rl-count fn-rlo-scalar-types))))))

(local (defmacro fn-rlo-array-proof-facts (field bits)
  (let* ((base (symbol-name field))
         (pred (intern-in-package-of-symbol (concatenate 'string base "P") field))
         (read (intern-in-package-of-symbol (concatenate 'string base "I") field))
         (length (intern-in-package-of-symbol (concatenate 'string base "-LENGTH") field))
         (update (intern-in-package-of-symbol (concatenate 'string "UPDATE-" base "I") field))
         (nth-type (intern-in-package-of-symbol (concatenate 'string base "P-NTH-TYPE") field))
         (pred-update (intern-in-package-of-symbol (concatenate 'string base "P-UPDATE") field))
         (read-type (intern-in-package-of-symbol (concatenate 'string base "I-TYPE") field))
         (read-nat (intern-in-package-of-symbol (concatenate 'string base "I-NAT") field))
         (update-type (intern-in-package-of-symbol (concatenate 'string "FN-RL-UPDATE-" (subseq base 6 nil) "I-KEEPS-TYPE") field))
         (update-wfp (intern-in-package-of-symbol (concatenate 'string "FN-RL-UPDATE-" (subseq base 6 nil) "I-KEEPS-WFP") field)))
    `(progn
(defthm ,nth-type
 (implies (and (,pred xs) (natp i) (< i (len xs)))
          (unsigned-byte-p ,bits (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable ,pred))))
(defthm ,pred-update
 (implies (and (,pred xs) (natp i) (< i (len xs)) (unsigned-byte-p ,bits v))
          (,pred (update-nth i v xs)))
 :hints (("Goal" :induct (update-nth i v xs) :in-theory (enable ,pred))))
(defthm ,read-type
 (implies (and (fn-resource-ledgerp ledger) (natp i)
               (< i (,length ledger)))
          (unsigned-byte-p ,bits (,read i ledger)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp ,read ,length)
                                (,pred unsigned-byte-p integer-range-p)))))
(defthm ,read-nat
 (implies (and (fn-resource-ledgerp ledger) (natp i)
               (< i (,length ledger)))
          (natp (,read i ledger)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :use ,read-type :in-theory (e/d (unsigned-byte-p integer-range-p)
                     (fn-resource-ledgerp ,read ,length ,read-type)))))
(defthm ,update-type
 (implies (and (fn-resource-ledgerp ledger) (natp i) (< i (,length ledger))
               (unsigned-byte-p ,bits v))
          (fn-resource-ledgerp (,update i v ledger)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp ,update ,length)
                                (fn-rl-budgetp fn-rl-drawnp fn-rl-phasesp fn-rl-gensp fn-rl-c0p fn-rl-c1p fn-rl-c2p fn-rl-c3p fn-rl-c4p fn-rl-c5p fn-rl-c6p fn-rl-c7p fn-rl-c8p unsigned-byte-p integer-range-p)))))
(defthm ,update-wfp
 (implies (and (fn-rl-wfp ledger) (natp i) (< i (,length ledger)))
          (fn-rl-wfp (,update i v ledger)))
 :hints (("Goal" :in-theory (enable fn-rl-wfp ,update ,length))))))))

(local (fn-rlo-array-proof-facts fn-rl-ids 64))

(local (fn-rlo-array-proof-facts fn-rl-cids 64))

(local (fn-rlo-array-proof-facts fn-rl-files 64))

(local (fn-rlo-array-proof-facts fn-rl-eoffs 64))

(local (fn-rlo-array-proof-facts fn-rl-elens 64))

(local (fn-rlo-array-proof-facts fn-rl-trailers 64))

(local (defthm fn-rlo-next-nat
 (implies (fn-resource-ledgerp ledger) (natp (fn-rl-next ledger)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :use fn-rlo-scalar-types :in-theory (e/d (unsigned-byte-p integer-range-p) (fn-resource-ledgerp fn-rl-next fn-rlo-scalar-types fn-rlo-next-word))))))

(local (defthm fn-rlo-file-limit-nat
 (implies (fn-resource-ledgerp ledger) (natp (fn-rl-file-limit ledger)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :use fn-rlo-scalar-types :in-theory (e/d (unsigned-byte-p integer-range-p) (fn-resource-ledgerp fn-rl-file-limit fn-rlo-scalar-types fn-rlo-next-word))))))

(local (defthm fn-rlo-charge-from-frame
 (implies (and (natp f) (not (member-equal f '(1 5 6 7 8 9 10 11 12 13))))
  (equal (nth f (fn-rl-charge-from i slot demand ledger)) (nth f ledger)))
 :hints (("Goal" :induct (fn-rl-charge-from i slot demand ledger)
 :in-theory (e/d (fn-rl-charge-from fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rlo-draw-keeps-count
 (equal (fn-rl-count (mv-nth 2 (fn-rl-draw slot demand ledger))) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count fn-rl-draw fn-rl-charge) (fn-rl-charge-from nth update-nth))))))

(local (defmacro fn-rlo-update-count-fact (update)
 (let ((name (intern-in-package-of-symbol (concatenate 'string (symbol-name update) "-RLO-COUNT") update)))
 `(defthm ,name
 (equal (fn-rl-count (,update i v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count ,update) (nth update-nth))))))))

(local (fn-rlo-update-count-fact update-fn-rl-cidsi))

(local (fn-rlo-update-count-fact update-fn-rl-filesi))

(local (fn-rlo-update-count-fact update-fn-rl-eoffsi))

(local (fn-rlo-update-count-fact update-fn-rl-elensi))

(local (fn-rlo-update-count-fact update-fn-rl-trailersi))

(local (defthm fn-rlo-next-update-keeps-count
 (equal (fn-rl-count (update-fn-rl-next v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count update-fn-rl-next) (nth update-nth))))))

(local (defthm fn-rlo-ids-slot-bound
 (implies (and (fn-rl-wfp ledger) (< slot (fn-rl-count ledger)))
          (< slot (fn-rl-ids-length ledger)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-rl-wfp)))))

(local (defthm fn-rlo-ids-update-keeps-count
 (equal (fn-rl-count (update-fn-rl-idsi slot v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count update-fn-rl-idsi) (nth update-nth))))))

(local (defthm fn-rlo-free-init-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (and (fn-resource-ledgerp (fn-rlo-free-init slot ledger))
       (fn-rl-wfp (fn-rlo-free-init slot ledger))))
 :hints (("Goal" :induct (fn-rlo-free-init slot ledger)
 :in-theory (e/d (fn-rlo-free-init unsigned-byte-p integer-range-p)
                (fn-resource-ledgerp fn-rl-wfp fn-rl-count
                 update-fn-rl-idsi fn-rl-ids-length))))))

(local (defthm fn-rlo-next-update-keeps-wfp
 (equal (fn-rl-wfp (update-fn-rl-next v ledger)) (fn-rl-wfp ledger))
 :hints (("Goal" :in-theory (enable fn-rl-wfp update-fn-rl-next)))))

(local (defthm fn-rlo-next-update-keeps-type
 (implies (and (fn-resource-ledgerp ledger) (unsigned-byte-p 64 v))
  (fn-resource-ledgerp (update-fn-rl-next v ledger)))
 :hints (("Goal" :in-theory
 (e/d (fn-resource-ledgerp update-fn-rl-next fn-rl-nextp)
      (fn-rl-budgetp fn-rl-drawnp fn-rl-phasesp fn-rl-gensp fn-rl-c0p fn-rl-c1p fn-rl-c2p fn-rl-c3p fn-rl-c4p fn-rl-c5p fn-rl-c6p fn-rl-c7p fn-rl-c8p fn-rl-idsp fn-rl-cidsp fn-rl-filesp fn-rl-eoffsp fn-rl-elensp fn-rl-trailersp unsigned-byte-p integer-range-p))))))

(local (defmacro fn-rlo-column-length-bound (field)
 (let* ((length (intern-in-package-of-symbol (concatenate 'string (symbol-name field) "-LENGTH") field))
        (name (intern-in-package-of-symbol (concatenate 'string (symbol-name field) "-RLO-LENGTH-BOUND") field)))
 `(defthm ,name
   (implies (fn-rl-wfp ledger) (<= (fn-rl-count ledger) (,length ledger)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-rl-wfp)))))))

(local (fn-rlo-column-length-bound fn-rl-ids))

(local (fn-rlo-column-length-bound fn-rl-cids))

(local (fn-rlo-column-length-bound fn-rl-files))

(local (fn-rlo-column-length-bound fn-rl-eoffs))

(local (fn-rlo-column-length-bound fn-rl-elens))

(local (fn-rlo-column-length-bound fn-rl-trailers))

(local (defthm fn-rlo-hold-has-slot-domain
 (implies (equal (car (fn-orv-startup-grant dynamic store-need cold policy slots)) :hold)
          (and (natp slots) (<= 3 slots) (< slots 4294967296)))
 :hints (("Goal" :in-theory (e/d (fn-orv-startup-grant) (fn-crv-nth fn-orv-policy-p fn-orv-bookkeeping-octets))))))

(local (defthm fn-rlo-update-ci-keeps-count
 (equal (fn-rl-count (fn-rl-update-ci i slot v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rlo-release-keeps-count
 (equal (fn-rl-count (fn-rl-release-from i slot mask ledger)) (fn-rl-count ledger))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
          :in-theory (e/d (fn-rl-release-from) (fn-rl-update-ci nth update-nth))))))

(local (defthm fn-rlo-phase-update-keeps-count
 (equal (fn-rl-count (update-fn-rl-phasesi slot v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (update-fn-rl-phasesi fn-rl-count) (nth update-nth))))))

(local (defthm fn-rlo-settle-keeps-count
 (equal (fn-rl-count (mv-nth 1 (fn-rl-settle slot gen ledger))) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-settle fn-rl-slotp) (fn-rl-count update-fn-rl-phasesi fn-rl-release-from nth update-nth))))))

(local (defmacro fn-rlo-metadata-proof-facts (field)
 (let* ((base (symbol-name field))
        (length (intern-in-package-of-symbol (concatenate 'string base "-LENGTH") field))
        (update (intern-in-package-of-symbol (concatenate 'string "UPDATE-" base "I") field))
        (name (intern-in-package-of-symbol (concatenate 'string base "-RLO-WFP") field)))
 `(defthm ,name
   (implies (and (fn-rl-wfp ledger) (natp i) (< i (,length ledger)))
            (fn-rl-wfp (,update i v ledger)))
   :hints (("Goal" :in-theory (enable fn-rl-wfp ,update ,length)))))))

(local (fn-rlo-metadata-proof-facts fn-rl-elens))

(local (fn-rlo-metadata-proof-facts fn-rl-trailers))

(local (defmacro fn-rlo-scalar-update-facts (field bits)
 (let* ((base (symbol-name field))
 (update (intern-in-package-of-symbol (concatenate 'string "UPDATE-" base) field))
 (pred (intern-in-package-of-symbol (concatenate 'string base "P") field))
 (type (intern-in-package-of-symbol (concatenate 'string base "-RLO-UPDATE-TYPE") field))
 (wfp (intern-in-package-of-symbol (concatenate 'string base "-RLO-UPDATE-WFP") field)))
 `(progn
 (defthm ,type
  (implies (and (fn-resource-ledgerp ledger) (unsigned-byte-p ,bits v))
   (fn-resource-ledgerp (,update v ledger)))
  :hints (("Goal" :in-theory
   (e/d (fn-resource-ledgerp ,update ,pred)
    (fn-rl-budgetp fn-rl-drawnp fn-rl-phasesp fn-rl-gensp fn-rl-c0p fn-rl-c1p fn-rl-c2p fn-rl-c3p fn-rl-c4p fn-rl-c5p fn-rl-c6p fn-rl-c7p fn-rl-c8p fn-rl-idsp fn-rl-cidsp fn-rl-filesp fn-rl-eoffsp fn-rl-elensp fn-rl-trailersp unsigned-byte-p integer-range-p)))))
 (defthm ,wfp
  (equal (fn-rl-wfp (,update v ledger)) (fn-rl-wfp ledger))
  :hints (("Goal" :in-theory (enable fn-rl-wfp ,update))))))))

(local (fn-rlo-scalar-update-facts fn-rl-file-limit 64))

(local (fn-rlo-scalar-update-facts fn-rl-mode 8))

(local (defthm fn-rlo-settle-ready-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (natp slot) (< slot (fn-rl-count ledger)))
  (let ((after (mv-nth 1 (fn-rlo-settle-ready slot ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
 :hints (("Goal"
  :use ((:instance fn-rl-update-idsi-keeps-type
          (i slot) (v (fn-rl-next (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger))))
          (ledger (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger))))
       (:instance fn-rl-update-idsi-keeps-wfp
          (i slot) (v (fn-rl-next (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger))))
          (ledger (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger))))
       (:instance fn-rlo-scalar-types (ledger (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger))))
       (:instance fn-rl-settle-keeps-representation
         (gen (fn-rl-gensi slot ledger))))
 :in-theory (e/d (fn-rlo-settle-ready unsigned-byte-p integer-range-p)
  (fn-resource-ledgerp fn-rl-wfp fn-rl-settle fn-rl-next fn-rl-count
   fn-rl-gensi fn-rl-elensi fn-rl-trailersi update-fn-rl-idsi update-fn-rl-next
   fn-rl-ids-length fn-rl-file-limit fn-rlo-next-word fn-rlo-scalar-types fn-rl-update-idsi-keeps-type fn-rl-update-idsi-keeps-wfp fn-rl-settle-keeps-representation))))))

(defthm fn-rlo-hold-has-slot-domain
 (implies (equal (car (fn-orv-startup-grant dynamic store-need cold policy slots)) :hold)
          (and (natp slots) (<= 3 slots) (< slots 4294967296)))
 :hints (("Goal" :in-theory (e/d (fn-orv-startup-grant) (fn-crv-nth fn-orv-policy-p fn-orv-bookkeeping-octets)))))

(verify-guards fn-rlo-install
 :hints (("Goal"
 :use ((:instance fn-rl-install-keeps-representation
       (ledger fn-resource-ledger)
       (budget (fn-rlo-resident-vector (nth 1 (fn-orv-startup-grant dynamic store-need cold policy slots))))
       (baseline (fn-rlo-resident-vector (nth 3 (fn-orv-startup-grant dynamic store-need cold policy slots))))
       (reserve (fn-rlo-resident-vector (nth 2 (fn-orv-startup-grant dynamic store-need cold policy slots))))
       (nslots slots)))
 :in-theory (e/d (fn-rlo-resident-vector)
  (fn-resource-ledgerp fn-rl-install fn-rlo-free-init fn-rl-count
   fn-rl-install-keeps-representation fn-orv-startup-grant)))))

(verify-guards fn-rlo-issue
 :hints (("Goal"
  :use ((:instance fn-rl-draw-keeps-representation
          (ledger fn-resource-ledger) (slot (fn-rl-next fn-resource-ledger))
          (demand (fn-rlo-resident-vector (fn-rl-file-limit fn-resource-ledger))))
        (:instance fn-rl-idsi-type
          (ledger fn-resource-ledger) (i (fn-rl-next fn-resource-ledger)))
        (:instance fn-rl-idsi-type
          (ledger (mv-nth 2 (fn-rl-draw (fn-rl-next fn-resource-ledger)
                     (fn-rlo-resident-vector (fn-rl-file-limit fn-resource-ledger))
                     fn-resource-ledger)))
          (i (fn-rl-next fn-resource-ledger))))
  :in-theory
  (e/d (fn-rlo-ready-p fn-rl-wfp fn-rlo-resident-vector unsigned-byte-p update-fn-rl-next update-fn-rl-cidsi update-fn-rl-filesi update-fn-rl-eoffsi update-fn-rl-elensi update-fn-rl-trailersi)
       (fn-resource-ledgerp fn-rl-draw fn-rl-count fn-rl-charge-from
        fn-rl-next fn-rl-file-limit fn-rl-idsi


        fn-rl-draw-keeps-representation fn-rl-idsi-type fn-rl-idsi-nat)))))

(verify-guards fn-rlo-settle-ready
 :hints (("Goal"
 :use ((:instance fn-rl-settle-keeps-representation
         (ledger fn-resource-ledger) (gen (fn-rl-gensi slot fn-resource-ledger))))
 :in-theory (e/d (fn-rl-wfp unsigned-byte-p)
       (fn-resource-ledgerp fn-rl-settle update-fn-rl-idsi fn-rl-next fn-rl-count fn-rl-settle-keeps-representation)))))

(verify-guards fn-rlo-output
 :hints (("Goal" :use ((:instance fn-rl-elens-rlo-wfp (ledger fn-resource-ledger) (i (caddr token)) (v 1)))
 :in-theory (e/d (fn-rlo-livep fn-rlo-ready-p fn-rl-wfp) (fn-resource-ledgerp fn-rl-count update-fn-rl-elensi fn-rl-elens-rlo-wfp)))))

(verify-guards fn-rlo-physical
 :hints (("Goal" :use ((:instance fn-rl-trailers-rlo-wfp (ledger fn-resource-ledger) (i (caddr token)) (v 1)))
 :in-theory (e/d (fn-rlo-livep fn-rlo-ready-p fn-rl-wfp) (fn-resource-ledgerp fn-rl-count update-fn-rl-trailersi fn-rl-trailers-rlo-wfp)))))

(defthm fn-rlo-install-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (let ((after (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
 :hints (("Goal" :in-theory (e/d (fn-rlo-install)
 (fn-resource-ledgerp fn-rl-wfp fn-rl-install fn-rlo-free-init
  fn-rlo-resident-vector fn-orv-startup-grant fn-rl-count
  update-fn-rl-next update-fn-rl-file-limit update-fn-rl-mode)))))

(defthm fn-rlo-issue-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (let ((after (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
 :hints (("Goal"
  :use ((:instance fn-rl-draw-keeps-representation
          (slot (fn-rl-next ledger))
          (demand (fn-rlo-resident-vector (fn-rl-file-limit ledger))))
        (:instance fn-rl-idsi-type
          (ledger (mv-nth 2 (fn-rl-draw (fn-rl-next ledger)
                  (fn-rlo-resident-vector (fn-rl-file-limit ledger)) ledger)))
          (i (fn-rl-next ledger))))
  :in-theory (e/d (fn-rlo-issue fn-rlo-ready-p unsigned-byte-p)
   (fn-resource-ledgerp fn-rl-wfp fn-rl-draw fn-rl-count fn-rl-next
    fn-rl-idsi fn-rl-file-limit fn-rlo-resident-vector
    update-fn-rl-next update-fn-rl-cidsi update-fn-rl-filesi
    update-fn-rl-eoffsi update-fn-rl-elensi update-fn-rl-trailersi
    fn-rl-ids-length fn-rl-cids-length fn-rl-files-length fn-rl-eoffs-length fn-rl-elens-length fn-rl-trailers-length fn-rl-idsi-type fn-rl-draw-keeps-representation)))))

(defthm fn-rlo-output-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (let ((after (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
 :hints (("Goal" :in-theory (e/d (fn-rlo-output fn-rlo-livep fn-rlo-ready-p fn-rlo-tokenp)
  (fn-resource-ledgerp fn-rl-wfp fn-rlo-settle-ready update-fn-rl-elensi
   fn-rl-ids-length fn-rl-elens-length fn-rl-trailers-length fn-rl-count fn-rl-phasesi fn-rl-gensi fn-rl-cidsi fn-rl-filesi fn-rl-eoffsi)))))

(defthm fn-rlo-physical-keeps-representation
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger))
  (let ((after (mv-nth 1 (fn-rlo-physical token operation-gen receipt ledger))))
   (and (fn-resource-ledgerp after) (fn-rl-wfp after))))
 :hints (("Goal" :in-theory (e/d (fn-rlo-physical fn-rlo-livep fn-rlo-ready-p fn-rlo-tokenp)
  (fn-resource-ledgerp fn-rl-wfp fn-rlo-settle-ready update-fn-rl-trailersi
   fn-rl-ids-length fn-rl-elens-length fn-rl-trailers-length fn-rl-count fn-rl-phasesi fn-rl-gensi fn-rl-cidsi fn-rl-filesi fn-rl-eoffsi)))))
)
