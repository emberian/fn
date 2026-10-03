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
            (mv :installed fn-resource-ledger))))))))

(defun fn-rlo-ready-p (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t))
  (and (fn-rl-wfp fn-resource-ledger) (equal (fn-rl-mode fn-resource-ledger) 2)
       (posp (fn-rl-file-limit fn-resource-ledger))
       (<= 3 (fn-rl-count fn-resource-ledger))))

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

; Mutation guards for install and issue, free-row chain preservation, and
; full typed/result projection remain PRF-1259 work. No complete allocation
; tariff or accounted-operation gate is declared by this source slice.
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
(local (defthm fn-rlo-elens-keeps-count
 (equal (fn-rl-count (update-fn-rl-elensi i v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count update-fn-rl-elensi) (nth update-nth))))))
(local (defthm fn-rlo-trailers-keeps-count
 (equal (fn-rl-count (update-fn-rl-trailersi i v ledger)) (fn-rl-count ledger))
 :hints (("Goal" :in-theory (e/d (fn-rl-count update-fn-rl-trailersi) (nth update-nth))))))
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

)
