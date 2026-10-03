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
  ; A zero-count ledger with padded, previously populated slot arrays is not
  ; a fresh bank. Reject it before resizing can preserve an active hidden row.
  ; Keep the established already-installed refusal for positive counts.
  (if (not (and (fn-rl-wfp fn-resource-ledger)
                (or (not (equal (fn-rl-count fn-resource-ledger) 0))
                    (fn-rl-freshp fn-resource-ledger))))
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
        ; An exhausted generation cannot be issued again. Retire this idle
        ; row instead of blocking every reusable row behind it at the head.
        (if (not (< (fn-rl-gensi slot fn-resource-ledger) *fn-rl-word-max*))
            (mv :settled fn-resource-ledger)
          (let* ((fn-resource-ledger (update-fn-rl-idsi slot (fn-rl-next fn-resource-ledger) fn-resource-ledger))
                 (fn-resource-ledger (update-fn-rl-next slot fn-resource-ledger)))
            (mv :settled fn-resource-ledger)))))))

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
; Free-row protocol validity and complete allocation tariffs remain
; PRF-1259 work; this is not yet a complete accounted-operation gate.
 ; Typed representation and guards cover the actual private output methods.
; Free-row protocol validity and complete allocation tariffs remain
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

(local (defthm fn-rlo-gens-list-read-nat
 (implies (and (fn-rl-gensp xs) (natp i) (< i (len xs))) (natp (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable fn-rl-gensp)))))

(local (defthm fn-rlo-gens-reader-nat
 (implies (and (fn-resource-ledgerp ledger) (natp i) (< i (fn-rl-gens-length ledger)))
          (natp (fn-rl-gensi i ledger)))
 :hints (("Goal" :in-theory (e/d (fn-resource-ledgerp fn-rl-gensi fn-rl-gens-length)
                                (fn-rl-gensp nth))))))


(verify-guards fn-rlo-settle-ready
 :hints (("Goal"
 :use ((:instance fn-rl-settle-keeps-representation
         (ledger fn-resource-ledger) (gen (fn-rl-gensi slot fn-resource-ledger)))
       (:instance fn-rlo-gens-reader-nat (i slot)
         (ledger (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot fn-resource-ledger) fn-resource-ledger)))))
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
; A successful issuer result is usable by the actual receipt consumers.
; This does not establish free-chain completeness or physical receipt truth.
(local (include-book "std/lists/update-nth" :dir :system))
(local (defthm fn-rlo-drawn-header-and-generation
 (implies (and (natp slot)
               (eq (mv-nth 0 (fn-rl-draw slot demand ledger)) :drawn))
  (let ((after (mv-nth 2 (fn-rl-draw slot demand ledger))))
   (and (equal (fn-rl-count after) (fn-rl-count ledger))
        (equal (fn-rl-mode after) (fn-rl-mode ledger))
        (equal (fn-rl-file-limit after) (fn-rl-file-limit ledger))
        (equal (fn-rl-phasesi slot after) 1)
        (equal (fn-rl-gensi slot after)
               (mv-nth 1 (fn-rl-draw slot demand ledger))))))
 :hints (("Goal" :in-theory
  (e/d (fn-rl-draw fn-rl-charge fn-rl-count fn-rl-mode fn-rl-file-limit
        fn-rl-phasesi fn-rl-gensi)
       (nth update-nth fn-rl-charge-from
        fn-resource-ledgerp fn-rl-wfp fn-rl-draw-keeps-okp))))))

(local (defthm fn-rlo-gens-length-bound
 (implies (fn-rl-wfp ledger) (<= (fn-rl-count ledger) (fn-rl-gens-length ledger)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-rl-wfp)))))

(local (defthm fn-rlo-drawn-generation-is-natural
 (implies (and (natp (fn-rl-gensi slot ledger))
               (eq (mv-nth 0 (fn-rl-draw slot demand ledger)) :drawn))
          (natp (mv-nth 1 (fn-rl-draw slot demand ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-draw fn-rl-charge)
   (fn-rl-gensi fn-rl-charge-from nth update-nth))))))

(local (defthm fn-rlo-drawn-input-is-shaped
 (implies (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn)
          (fn-rl-wfp ledger))
 :hints (("Goal" :in-theory (e/d (fn-rlo-issue fn-rlo-ready-p)
   (fn-rl-wfp fn-rl-draw nth update-nth))))))

(local (defthm fn-rlo-draw-keeps-header-nth
 (implies (and (natp field) (or (equal field 2) (<= 14 field)))
  (equal (nth field (mv-nth 2 (fn-rl-draw slot demand ledger))) (nth field ledger)))
 :hints (("Goal" :in-theory
  (e/d (fn-rl-draw fn-rl-charge) (nth update-nth fn-rl-charge-from))))))


(defthm fn-rlo-issued-token-is-live
 (implies (and (fn-resource-ledgerp ledger)
               (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn))
  (fn-rlo-livep (mv-nth 1 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))
               operation-gen
               (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger))))
 :hints (("Goal"
  :use ((:instance fn-rlo-drawn-input-is-shaped)
        (:instance fn-rlo-issue-keeps-representation)
        (:instance fn-rlo-next-nat)
        (:instance fn-rlo-gens-length-bound)
        (:instance fn-rlo-drawn-generation-is-natural
          (slot (fn-rl-next ledger))
          (demand (fn-rlo-resident-vector (fn-rl-file-limit ledger))))
        (:instance fn-rlo-gens-reader-nat (i (fn-rl-next ledger)))
        (:instance fn-rlo-drawn-header-and-generation
          (slot (fn-rl-next ledger))
          (demand (fn-rlo-resident-vector (fn-rl-file-limit ledger)))))
  :in-theory (e/d (fn-rlo-issue fn-rlo-livep fn-rlo-token fn-rlo-tokenp fn-rlo-ready-p)
                 (fn-resource-ledgerp fn-rl-wfp fn-rl-draw fn-rl-charge-from nth update-nth)))))

)

; The custody metadata columns are outside the bank projection. The actual
; producer, draw and independent receipt methods refine the existing guarded
; bank operations; no new vector/tree semantics or free-chain validity claim.
(encapsulate ()
(local (include-book "std/lists/update-nth" :dir :system))
(local (defthm fn-rlo-metadata-update-rows
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-rows-from i (update-nth field v ledger)) (fn-rl-rows-from i ledger)))
 :hints (("Goal" :induct (fn-rl-rows-from i ledger)
 :in-theory (e/d (fn-rl-rows-from fn-rl-demand-list fn-rl-count)
                 (nth update-nth))))))

(local (defthm fn-rlo-metadata-update-bank
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-bank (update-nth field v ledger)) (fn-rl-bank ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rl-bank fn-rl-budget-list fn-rl-drawn-list)
                                 (nth update-nth fn-rl-rows-from))))))

(local (defmacro fn-rlo-metadata-bank-frame (update)
 (let ((name (intern-in-package-of-symbol (concatenate 'string (symbol-name update) "-RLO-BANK-FRAME") update)))
 `(defthm ,name
  (equal (fn-rl-bank (,update i v ledger)) (fn-rl-bank ledger))
  :hints (("Goal" :in-theory (e/d (,update) (fn-rl-bank update-nth nth))))))))

(local (fn-rlo-metadata-bank-frame update-fn-rl-idsi))

(local (fn-rlo-metadata-bank-frame update-fn-rl-cidsi))

(local (fn-rlo-metadata-bank-frame update-fn-rl-filesi))

(local (fn-rlo-metadata-bank-frame update-fn-rl-eoffsi))

(local (fn-rlo-metadata-bank-frame update-fn-rl-elensi))

(local (fn-rlo-metadata-bank-frame update-fn-rl-trailersi))

(local (defthm fn-rlo-next-update-bank-frame
 (equal (fn-rl-bank (update-fn-rl-next v ledger)) (fn-rl-bank ledger))
 :hints (("Goal" :in-theory (e/d (update-fn-rl-next) (fn-rl-bank update-nth nth))))))

(local (defthm fn-rlo-metadata-update-ci-read
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-ci i slot (update-nth field v ledger)) (fn-rl-ci i slot ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rl-ci) (nth update-nth))))))

(local (defthm fn-rlo-metadata-update-drawn-read
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-drawni i (update-nth field v ledger)) (fn-rl-drawni i ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rl-drawni) (nth update-nth))))))

(local (defthm fn-rlo-metadata-update-ci-write
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-update-ci i slot val (update-nth field v ledger))
   (update-nth field v (fn-rl-update-ci i slot val ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-update-ci) (nth update-nth))))))

(local (defthm fn-rlo-metadata-update-drawn-write
 (implies (and (natp field) (<= 14 field))
  (equal (update-fn-rl-drawni i val (update-nth field v ledger))
   (update-nth field v (update-fn-rl-drawni i val ledger))))
 :hints (("Goal" :in-theory (e/d (update-fn-rl-drawni) (nth update-nth))))))

(local (defthm fn-rlo-metadata-update-accounting-write
 (implies (and (natp field) (<= 14 field) (natp small) (< small 14))
  (equal (update-nth small val (update-nth field v ledger))
         (update-nth field v (update-nth small val ledger))))
 :hints (("Goal" :use (:instance update-nth-of-update-nth-diff
   (n1 small) (v1 val) (n2 field) (v2 v) (x ledger))
   :in-theory (e/d (nfix) (update-nth update-nth-of-update-nth-diff))))))

(local (defthm fn-rlo-metadata-update-release
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-release-from i slot mask (update-nth field v ledger))
   (update-nth field v (fn-rl-release-from i slot mask ledger))))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
 :in-theory (e/d (fn-rl-release-from)
                 (fn-rl-update-ci fn-rl-ci fn-rl-drawni update-fn-rl-drawni nth update-nth))))))

(local (defthm fn-rlo-metadata-update-settle-bank
 (implies (and (natp field) (<= 14 field))
  (equal (fn-rl-bank (mv-nth 1 (fn-rl-settle slot gen (update-nth field v ledger))))
         (fn-rl-bank (mv-nth 1 (fn-rl-settle slot gen ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-rl-settle fn-rl-slotp fn-rl-count fn-rl-phasesi fn-rl-gensi update-fn-rl-phasesi)
                 (update-nth-of-update-nth-diff fn-rl-bank fn-rl-release-from nth update-nth))))))

(local (defthm fn-rlo-settle-ready-bank-correspondence
 (equal (fn-rl-bank (mv-nth 1 (fn-rlo-settle-ready slot ledger)))
  (if (and (equal (fn-rl-elensi slot ledger) 1) (equal (fn-rl-trailersi slot ledger) 1))
      (fn-rl-bank (mv-nth 1 (fn-rl-settle slot (fn-rl-gensi slot ledger) ledger)))
    (fn-rl-bank ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rlo-settle-ready)
  (fn-rl-bank fn-rl-settle fn-rl-gensi fn-rl-elensi fn-rl-trailersi
   update-fn-rl-next update-fn-rl-idsi fn-rl-next))))))

(local (defthm fn-rlo-free-init-bank-frame
 (equal (fn-rl-bank (fn-rlo-free-init slot ledger)) (fn-rl-bank ledger))
 :hints (("Goal" :induct (fn-rlo-free-init slot ledger)
  :in-theory (e/d (fn-rlo-free-init)
   (fn-rl-bank fn-rl-count update-fn-rl-idsi fn-rl-idsi))))))

(local (defthm fn-rlo-startup-refusal-not-installed
 (implies (not (eq (car (fn-orv-startup-grant dynamic store-need cold policy slots)) :hold))
          (not (eq (cadr (fn-orv-startup-grant dynamic store-need cold policy slots)) :installed)))
 :hints (("Goal" :in-theory (e/d (fn-orv-startup-grant)
  (fn-orv-policy-p fn-native-config-cold-resources-wfp fn-crv-nth fn-orv-bookkeeping-octets))))))

(defthm fn-rlo-issue-keeps-bank-okp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rv-okp (fn-rl-bank ledger)))
  (fn-rv-okp (fn-rl-bank (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)))))
 :hints (("Goal"
 :use ((:instance fn-rl-draw-keeps-okp (slot (fn-rl-next ledger))
         (demand (fn-rlo-resident-vector (fn-rl-file-limit ledger)))))
 :in-theory (e/d (fn-rlo-issue) (fn-resource-ledgerp fn-rl-wfp fn-rv-okp fn-rl-bank
   fn-rlo-ready-p fn-rl-draw fn-rl-next fn-rl-count fn-rl-idsi fn-rl-file-limit
   fn-rlo-resident-vector update-fn-rl-next update-fn-rl-cidsi update-fn-rl-filesi
   update-fn-rl-eoffsi update-fn-rl-elensi update-fn-rl-trailersi
   fn-rl-draw-keeps-okp)))))

(defthm fn-rlo-issue-drawn-bank-correspondence
 (implies (eq (mv-nth 0 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)) :drawn)
  (equal (fn-rl-bank (mv-nth 2 (fn-rlo-issue cid connection-gen operation-gen dependency ledger)))
         (fn-rl-bank (mv-nth 2 (fn-rl-draw (fn-rl-next ledger)
           (fn-rlo-resident-vector (fn-rl-file-limit ledger)) ledger)))))
 :hints (("Goal" :in-theory (e/d (fn-rlo-issue)
   (fn-rl-bank fn-rlo-ready-p fn-rl-draw fn-rl-next fn-rl-count fn-rl-idsi
    fn-rl-file-limit fn-rlo-resident-vector update-fn-rl-next update-fn-rl-cidsi
    update-fn-rl-filesi update-fn-rl-eoffsi update-fn-rl-elensi update-fn-rl-trailersi)))))

(defthm fn-rlo-install-bank-correspondence
 (implies (eq (mv-nth 0 (fn-rlo-install dynamic store-need cold policy slots ledger)) :installed)
  (let ((grant (fn-orv-startup-grant dynamic store-need cold policy slots)))
   (equal (fn-rl-bank (mv-nth 1 (fn-rlo-install dynamic store-need cold policy slots ledger)))
    (fn-rl-bank (mv-nth 1 (fn-rl-install (fn-rlo-resident-vector (nth 1 grant))
       (fn-rlo-resident-vector (nth 3 grant)) (fn-rlo-resident-vector (nth 2 grant)) slots ledger))))))
 :hints (("Goal" :use fn-rlo-startup-refusal-not-installed :in-theory (e/d (fn-rlo-install update-fn-rl-file-limit update-fn-rl-mode)
  (fn-rl-bank fn-rl-wfp fn-rl-count fn-rl-install fn-rlo-free-init update-fn-rl-next
   fn-rlo-startup-refusal-not-installed fn-rlo-resident-vector fn-orv-startup-grant nth update-nth update-nth-of-update-nth-diff)))))

(defthm fn-rlo-output-bank-correspondence
 (equal (fn-rl-bank (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger)))
  (if (and (fn-rlo-livep token operation-gen ledger)
           (member-eq receipt '(:drained :discarded))
           (equal (fn-rl-trailersi (caddr token) ledger) 1))
      (fn-rl-bank (mv-nth 1 (fn-rl-settle (caddr token) (fn-rl-gensi (caddr token) ledger) ledger)))
    (fn-rl-bank ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rlo-output update-fn-rl-elensi fn-rl-elensi fn-rl-trailersi fn-rl-gensi)
  (update-nth-of-update-nth-diff fn-rlo-livep fn-rlo-settle-ready fn-rl-bank fn-rl-settle nth update-nth)))))

(defthm fn-rlo-physical-bank-correspondence
 (equal (fn-rl-bank (mv-nth 1 (fn-rlo-physical token operation-gen receipt ledger)))
  (if (and (fn-rlo-livep token operation-gen ledger)
           (member-eq receipt '(:terminal :no-actor-created))
           (equal (fn-rl-elensi (caddr token) ledger) 1))
      (fn-rl-bank (mv-nth 1 (fn-rl-settle (caddr token) (fn-rl-gensi (caddr token) ledger) ledger)))
    (fn-rl-bank ledger)))
 :hints (("Goal" :in-theory (e/d (fn-rlo-physical update-fn-rl-trailersi fn-rl-elensi fn-rl-trailersi fn-rl-gensi)
  (update-nth-of-update-nth-diff fn-rlo-livep fn-rlo-settle-ready fn-rl-bank fn-rl-settle nth update-nth)))))

(defthm fn-rlo-output-keeps-bank-okp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rv-okp (fn-rl-bank ledger)))
  (fn-rv-okp (fn-rl-bank (mv-nth 1 (fn-rlo-output token operation-gen receipt ledger)))))
 :hints (("Goal"
 :use ((:instance fn-rl-settle-keeps-okp (slot (caddr token)) (gen (fn-rl-gensi (caddr token) ledger))))
 :in-theory (disable fn-resource-ledgerp fn-rl-wfp fn-rv-okp fn-rl-bank
   fn-rlo-output fn-rlo-livep fn-rl-settle fn-rl-gensi fn-rl-trailersi
   fn-rl-settle-keeps-okp))))

(defthm fn-rlo-physical-keeps-bank-okp
 (implies (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
               (fn-rv-okp (fn-rl-bank ledger)))
  (fn-rv-okp (fn-rl-bank (mv-nth 1 (fn-rlo-physical token operation-gen receipt ledger)))))
 :hints (("Goal"
 :use ((:instance fn-rl-settle-keeps-okp (slot (caddr token)) (gen (fn-rl-gensi (caddr token) ledger))))
 :in-theory (disable fn-resource-ledgerp fn-rl-wfp fn-rv-okp fn-rl-bank
   fn-rlo-physical fn-rlo-livep fn-rl-settle fn-rl-gensi fn-rl-elensi
   fn-rl-settle-keeps-okp))))
)

; Receipt replay cannot push the same released row onto the free chain twice.
; This is a local custody property, not free-chain completeness or receipt authenticity.
(encapsulate ()
(local (include-book "std/lists/update-nth" :dir :system))
(local (defthm fn-rlo-settled-row-is-idle
 (implies (and (natp slot)
               (eq (mv-nth 0 (fn-rlo-settle-ready slot ledger)) :settled))
          (equal (fn-rl-phasesi slot (mv-nth 1 (fn-rlo-settle-ready slot ledger))) 0))
 :hints (("Goal" :in-theory (e/d (fn-rlo-settle-ready fn-rl-settle fn-rl-phasesi)
   (fn-rl-release-from nth update-nth))))))
(defthm fn-rlo-output-settled-token-is-not-live
 (implies (eq (mv-nth 0 (fn-rlo-output token op receipt ledger)) :settled)
  (not (fn-rlo-livep token op (mv-nth 1 (fn-rlo-output token op receipt ledger)))))
 :hints (("Goal" :use ((:instance fn-rlo-settled-row-is-idle
    (slot (caddr token)) (ledger (update-fn-rl-elensi (caddr token) 1 ledger))))
   :in-theory (e/d (fn-rlo-output fn-rlo-livep fn-rlo-tokenp)
      (fn-rlo-ready-p fn-rlo-settle-ready fn-rl-phasesi update-fn-rl-elensi)))))
(defthm fn-rlo-physical-settled-token-is-not-live
 (implies (eq (mv-nth 0 (fn-rlo-physical token op receipt ledger)) :settled)
  (not (fn-rlo-livep token op (mv-nth 1 (fn-rlo-physical token op receipt ledger)))))
 :hints (("Goal" :use ((:instance fn-rlo-settled-row-is-idle
    (slot (caddr token)) (ledger (update-fn-rl-trailersi (caddr token) 1 ledger))))
   :in-theory (e/d (fn-rlo-physical fn-rlo-livep fn-rlo-tokenp)
      (fn-rlo-ready-p fn-rlo-settle-ready fn-rl-phasesi update-fn-rl-trailersi)))))
(defthm fn-rlo-output-settles-once
 (implies (eq (mv-nth 0 (fn-rlo-output token op receipt ledger)) :settled)
  (let ((after (mv-nth 1 (fn-rlo-output token op receipt ledger))))
   (and (equal (fn-rlo-output token op again after) (list :stale after))
        (equal (fn-rlo-physical token op physical after) (list :stale after)))))
 :hints (("Goal" :use fn-rlo-output-settled-token-is-not-live
  :in-theory (e/d (fn-rlo-output fn-rlo-physical)
   (fn-rlo-livep fn-rlo-settle-ready update-fn-rl-elensi update-fn-rl-trailersi)))))
(defthm fn-rlo-physical-settles-once
 (implies (eq (mv-nth 0 (fn-rlo-physical token op receipt ledger)) :settled)
  (let ((after (mv-nth 1 (fn-rlo-physical token op receipt ledger))))
   (and (equal (fn-rlo-output token op output after) (list :stale after))
        (equal (fn-rlo-physical token op again after) (list :stale after)))))
 :hints (("Goal" :use fn-rlo-physical-settled-token-is-not-live
  :in-theory (e/d (fn-rlo-output fn-rlo-physical)
   (fn-rlo-livep fn-rlo-settle-ready update-fn-rl-elensi update-fn-rl-trailersi)))))

)

; Exhaustion retires a row without blocking the remaining free chain.
(encapsulate ()
(local (include-book "std/lists/update-nth" :dir :system))
(local (defthm fn-rlo-release-preserves-generation-and-head-fields
 (implies (member-equal field '(4 20))
  (equal (nth field (fn-rl-release-from i slot mask ledger)) (nth field ledger)))
 :hints (("Goal" :induct (fn-rl-release-from i slot mask ledger)
  :in-theory (e/d (fn-rl-release-from fn-rl-update-ci) (nth update-nth))))))
(local (defthm fn-rlo-base-settlement-frames-generation-and-head
 (let ((after (mv-nth 1 (fn-rl-settle slot gen ledger))))
  (and (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger))
       (equal (fn-rl-next after) (fn-rl-next ledger))))
 :hints (("Goal" :in-theory (e/d (fn-rl-settle fn-rl-gensi fn-rl-next)
   (fn-rl-release-from nth update-nth))))))
(defthm fn-rlo-exhausted-settlement-keeps-free-head
 (implies (<= *fn-rl-word-max* (fn-rl-gensi slot ledger))
  (let ((after (mv-nth 1 (fn-rlo-settle-ready slot ledger))))
   (and (equal (fn-rl-next after) (fn-rl-next ledger))
        (equal (fn-rl-gensi slot after) (fn-rl-gensi slot ledger)))))
 :hints (("Goal" :use ((:instance fn-rlo-base-settlement-frames-generation-and-head
    (gen (fn-rl-gensi slot ledger))))
  :in-theory (e/d (fn-rlo-settle-ready)
   (fn-rl-settle fn-rl-gensi fn-rl-next update-fn-rl-next update-fn-rl-idsi)))))
)
