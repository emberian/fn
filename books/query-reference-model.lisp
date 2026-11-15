; Independent logical model and local accounting algebra. No served scans.
; New proof events below are source proposals, UNRUN in this lane.
(in-package "ACL2")
(include-book "identity")
(include-book "pool")
(fn2-book-layer :c)

; Count a descriptor's own active bit and exact handle. Neither a pool
; counter nor an operation result decides this multiplicity.
(defun fn2-qr-reference-on (mask bit source source-gen slot gen)
 (declare (xargs :guard t))
 (if (and (natp mask) (logbitp (nfix bit) mask) (equal source slot) (equal source-gen gen)) 1 0))
(defun fn2-qr-row-count (i slot gen fn2-id-decides)
 (declare (xargs :stobjs fn2-id-decides :verify-guards nil))
 (+ (fn2-qr-reference-on (fn2-id-decides-qmask i fn2-id-decides) 0
                         (fn2-id-decides-q1slot i fn2-id-decides) (fn2-id-decides-q1gen i fn2-id-decides) slot gen)
    (fn2-qr-reference-on (fn2-id-decides-qmask i fn2-id-decides) 1
                         (fn2-id-decides-q2slot i fn2-id-decides) (fn2-id-decides-q2gen i fn2-id-decides) slot gen)))
(defun fn2-qr-reference-count (n slot gen fn2-id-decides)
 (declare (xargs :stobjs fn2-id-decides :verify-guards nil :measure (nfix n)))
 (if (zp n) 0
  (+ (fn2-qr-row-count (- n 1) slot gen fn2-id-decides)
     (fn2-qr-reference-count (- n 1) slot gen fn2-id-decides))))

; Independent physical source validity: current generation, actual owner,
; readable phase and a fully present bounded window. No pool acceptance
; primitive or query implementation is called by this observer.
(defun fn2-qr-window-validp (slot gen off len ok os og fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (and (natp slot) (< slot (fn2-pool-rows fn2-pool))
      (equal gen (fn2-pool-gen slot fn2-pool))
      (member-equal (fn2-pool-state slot fn2-pool)
                    (list *fn2-pool-state-workspace* *fn2-pool-state-leased-out*))
      (equal ok (fn2-pool-owner-kind slot fn2-pool))
      (equal os (fn2-pool-owner-slot slot fn2-pool))
      (equal og (fn2-pool-owner-gen slot fn2-pool))
      (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
      (<= (+ off len) (fn2-pool-fill slot fn2-pool))))
(defun fn2-qr-row-validp (i fn2-id-decides fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-pool) :verify-guards nil))
 (let ((mask (fn2-id-decides-qmask i fn2-id-decides))
       (ok (fn2-id-decides-qk i fn2-id-decides)) (os (fn2-id-decides-qs i fn2-id-decides))
       (og (fn2-id-decides-qg i fn2-id-decides)))
  (and (natp mask) (<= mask 3)
       (implies (< 0 mask)
                (member-equal (fn2-id-decides-phase i fn2-id-decides)
                              (list *fn2-id-decide-phase-summary* *fn2-id-decide-phase-candidate*)))
       (implies (logbitp 0 mask)
                (and (posp (fn2-id-decides-q1len i fn2-id-decides))
                     (<= (fn2-id-decides-q1len i fn2-id-decides) 250)
                     (fn2-qr-window-validp (fn2-id-decides-q1slot i fn2-id-decides)
                       (fn2-id-decides-q1gen i fn2-id-decides) (fn2-id-decides-q1off i fn2-id-decides)
                       (fn2-id-decides-q1len i fn2-id-decides) ok os og fn2-pool)))
       (implies (logbitp 1 mask)
                (and (equal (fn2-id-decides-q2len i fn2-id-decides) 32)
                     (fn2-qr-window-validp (fn2-id-decides-q2slot i fn2-id-decides)
                       (fn2-id-decides-q2gen i fn2-id-decides) (fn2-id-decides-q2off i fn2-id-decides)
                       (fn2-id-decides-q2len i fn2-id-decides) ok os og fn2-pool))))))
(defun fn2-qr-descriptors-validp (n fn2-id-decides fn2-pool)
 (declare (xargs :stobjs (fn2-id-decides fn2-pool) :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (and (fn2-qr-row-validp (- n 1) fn2-id-decides fn2-pool)
       (fn2-qr-descriptors-validp (- n 1) fn2-id-decides fn2-pool))))
(defun fn2-qr-counts-matchp (n fn2-pool fn2-id-decides)
 (declare (xargs :stobjs (fn2-pool fn2-id-decides) :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (let ((slot (- n 1)))
   (and (equal (fn2-pool-query-ref-count slot fn2-pool)
               (fn2-qr-reference-count (fn2-id-decides-rows fn2-id-decides) slot
                                      (fn2-pool-gen slot fn2-pool) fn2-id-decides))
        (fn2-qr-counts-matchp (- n 1) fn2-pool fn2-id-decides)))))
(defun fn2-query-references-accountedp (fn2-pool fn2-id-decides)
 (declare (xargs :stobjs (fn2-pool fn2-id-decides) :verify-guards nil))
 (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
      (fn2-id-decidesp fn2-id-decides) (fn2-id-decides-wfp fn2-id-decides)
      (fn2-qr-descriptors-validp (fn2-id-decides-rows fn2-id-decides) fn2-id-decides fn2-pool)
      (fn2-qr-counts-matchp (fn2-pool-rows fn2-pool) fn2-pool fn2-id-decides)))

; One query row's complete accounting key. Qwake, incarnation and result
; facts intentionally do not decide active-window multiplicity/validity.
(defun-nx fn2-qr-row-key (i d)
 (list (fn2-id-decides-phase i d) (fn2-id-decides-qmask i d)
       (fn2-id-decides-qk i d) (fn2-id-decides-qs i d) (fn2-id-decides-qg i d)
       (fn2-id-decides-q1slot i d) (fn2-id-decides-q1gen i d)
       (fn2-id-decides-q1off i d) (fn2-id-decides-q1len i d)
       (fn2-id-decides-q2slot i d) (fn2-id-decides-q2gen i d)
       (fn2-id-decides-q2off i d) (fn2-id-decides-q2len i d)))
(defun-sk fn2-qr-keys-except (s a b)
 (forall i (implies (and (natp i) (not (equal i s)))
                    (equal (fn2-qr-row-key i b) (fn2-qr-row-key i a)))))
(defthm fn2-qr-row-count-except
 (implies (and (fn2-qr-keys-except s a b) (natp i) (not (equal i s)))
          (equal (fn2-qr-row-count i r g b) (fn2-qr-row-count i r g a)))
 :hints (("Goal" :use fn2-qr-keys-except-necc
          :in-theory (enable fn2-qr-row-key fn2-qr-row-count))))
(defthm fn2-qr-reference-count-natural
 (natp (fn2-qr-reference-count n slot gen d))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn2-qr-reference-count n slot gen d)
          :in-theory (enable fn2-qr-reference-count fn2-qr-row-count fn2-qr-reference-on))))
(defthm fn2-qr-reference-count-row-lower-bound
 (implies (and (natp s) (< s (nfix n)))
          (<= (fn2-qr-row-count s r g d) (fn2-qr-reference-count n r g d)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn2-qr-reference-count n r g d)
          :in-theory (enable fn2-qr-reference-count))))
(defthm fn2-qr-reference-count-single-row-update
 (implies (and (fn2-qr-keys-except s a b) (natp s))
  (equal (fn2-qr-reference-count n r g b)
         (if (< s (nfix n))
             (+ (fn2-qr-reference-count n r g a)
                (- (fn2-qr-row-count s r g b) (fn2-qr-row-count s r g a)))
           (fn2-qr-reference-count n r g a))))
 :hints (("Goal" :induct (fn2-qr-reference-count n r g b)
          :in-theory (enable fn2-qr-reference-count))))

; Pool query acquisition/release affect no source liveness, ownership,
; readable window, generation or I/O borrow key.
(defun-nx fn2-qr-pool-source-key (r p)
 (list (fn2-pool-gen r p) (fn2-pool-state r p) (fn2-pool-fill r p)
       (fn2-pool-owner-kind r p) (fn2-pool-owner-slot r p) (fn2-pool-owner-gen r p)))
(defun-sk fn2-qr-source-keys-equal (a b)
 (forall r (implies (natp r) (equal (fn2-qr-pool-source-key r b) (fn2-qr-pool-source-key r a)))))
(defun-nx fn2-qr-sources-equal (a b)
 (and (equal (fn2-pool-rows b) (fn2-pool-rows a)) (fn2-qr-source-keys-equal a b)))
(defthm fn2-qr-window-validp-source-frame
 (implies (fn2-qr-sources-equal a b)
          (equal (fn2-qr-window-validp s g o n k i e b) (fn2-qr-window-validp s g o n k i e a)))
 :hints (("Goal" :use (:instance fn2-qr-source-keys-equal-necc (r s))
          :in-theory (enable fn2-qr-sources-equal fn2-qr-pool-source-key fn2-qr-window-validp))))
(defthm fn2-qr-descriptors-validp-source-frame
 (implies (fn2-qr-sources-equal a b)
          (equal (fn2-qr-descriptors-validp n d b) (fn2-qr-descriptors-validp n d a)))
 :hints (("Goal" :induct (fn2-qr-descriptors-validp n d b)
          :in-theory (enable fn2-qr-descriptors-validp fn2-qr-row-validp))))
(defthm fn2-qr-window-validp-readable-refinement
 (implies (fn2-pool-wfp p)
  (equal (fn2-qr-window-validp s g o n k i e p)
         (and (eq (fn2-pool-readable-code s g k i e p) :ok)
              (unsigned-byte-p 32 o) (unsigned-byte-p 32 n)
              (<= (+ o n) (fn2-pool-fill s p)))))
 :hints (("Goal" :in-theory (enable fn2-qr-window-validp fn2-pool-readable-code
                                   fn2-pool-handle-code fn2-pool-ownerp))))
(defthm fn2-pool-query-acquire-counter-effect
 (implies (and (fn2-pool-wfp fn2-pool) (natp r) (< r (fn2-pool-rows fn2-pool)))
  (mv-let (code after) (fn2-pool-query-acquire slot gen off len ok os og fn2-pool)
   (if (eq code :ok)
       (equal (fn2-pool-query-ref-count r after)
              (+ (fn2-pool-query-ref-count r fn2-pool) (if (equal r slot) 1 0)))
     (equal after fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-pool-query-acquire))))
(defthm fn2-pool-query-release-counter-effect
 (implies (and (fn2-pool-wfp fn2-pool) (natp r) (< r (fn2-pool-rows fn2-pool)))
  (mv-let (code last after) (fn2-pool-query-release slot gen fn2-pool)
   (and (equal last (and (eq code :ok) (equal (fn2-pool-query-ref-count slot fn2-pool) 1)))
        (if (eq code :ok)
            (equal (fn2-pool-query-ref-count r after)
                   (- (fn2-pool-query-ref-count r fn2-pool) (if (equal r slot) 1 0)))
          (equal after fn2-pool)))))
 :hints (("Goal" :in-theory (enable fn2-pool-query-release))))
(defthm fn2-pool-query-acquire-source-frame
 (implies (fn2-pool-wfp fn2-pool)
  (fn2-qr-sources-equal fn2-pool (mv-nth 1 (fn2-pool-query-acquire slot gen off len ok os og fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-qr-sources-equal fn2-pool-query-acquire fn2-qr-pool-source-key)
          :use fn2-qr-source-keys-equal-suff)))
(defthm fn2-pool-query-release-source-frame
 (implies (fn2-pool-wfp fn2-pool)
  (fn2-qr-sources-equal fn2-pool (mv-nth 2 (fn2-pool-query-release slot gen fn2-pool))))
 :hints (("Goal" :in-theory (enable fn2-qr-sources-equal fn2-pool-query-release fn2-qr-pool-source-key)
          :use fn2-qr-source-keys-equal-suff)))

; A reusable one-row conservation boundary. Actual callees below must
; establish this delta; it is not added to the global invariant's H.
(defun-sk fn2-qr-counter-delta (s p q a b)
 (forall r
  (implies (and (natp r) (< r (fn2-pool-rows p)))
   (equal (fn2-pool-query-ref-count r q)
          (+ (fn2-pool-query-ref-count r p)
             (- (fn2-qr-row-count s r (fn2-pool-gen r p) b)
                (fn2-qr-row-count s r (fn2-pool-gen r p) a)))))))
(defthm fn2-qr-counts-match-single-row
 (implies (and (fn2-qr-counts-matchp (fn2-pool-rows p) p a)
               (fn2-qr-sources-equal p q)
               (equal (fn2-id-decides-rows a) (fn2-id-decides-rows b))
               (natp s) (< s (fn2-id-decides-rows a))
               (fn2-qr-keys-except s a b) (fn2-qr-counter-delta s p q a b))
          (fn2-qr-counts-matchp (fn2-pool-rows q) q b))
 :hints (("Goal" :induct (fn2-qr-counts-matchp (fn2-pool-rows p) p a)
          :in-theory (enable fn2-qr-counts-matchp fn2-qr-sources-equal)
          :use fn2-qr-counter-delta-necc)))
(defun fn2-query-output-counts (n fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons (fn2-pool-out-count (- n 1) fn2-pool) (fn2-query-output-counts (- n 1) fn2-pool))))

(defun-nx fn2-qr-transitionp (p q d e)
 (and (fn2-pool-semanticp q) (fn2-query-references-accountedp q e)
      (equal (fn2-id-decides-rows d) (fn2-id-decides-rows e))
      (fn2-qr-sources-equal p q)
      (equal (fn2-query-output-counts (fn2-pool-rows p) q)
             (fn2-query-output-counts (fn2-pool-rows p) p))))
; This leaf establishes nonnegative row contribution before larger proofs.
(defthm fn2-qr-row-count-natural
 (natp (fn2-qr-row-count i r g d))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn2-qr-row-count fn2-qr-reference-on))))

; Result/wake/namespace metadata do not enter the accounting key. These
; are typed setter frames, not permission to mutate phase/active handles.
(defmacro fn2-qr-metadata-frame (field width)
 (let ((setter (fn2-columns-pre "FN2-ID-DECIDES-SET-" field))
       (name (fn2-columns-pre "FN2-QR-FRAME-" field)))
  `(defthm ,name
    (implies (and (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
                  (unsigned-byte-p ,width v))
             (fn2-query-references-accountedp p (,setter i v d)))
    :hints (("Goal" :in-theory (enable fn2-query-references-accountedp fn2-qr-descriptors-validp
                                     fn2-qr-counts-matchp fn2-qr-reference-count fn2-qr-row-validp
                                     fn2-qr-row-count))))))
(fn2-qr-metadata-frame qnamespace 60)
(fn2-qr-metadata-frame qprofile 8)
(fn2-qr-metadata-frame qalgorithm 8)
(fn2-qr-metadata-frame qwake 1)
(fn2-qr-metadata-frame query-incarnation 60)
(fn2-qr-metadata-frame sfound 1)
(fn2-qr-metadata-frame selected 60)
(fn2-qr-metadata-frame candidates 60)
(fn2-qr-metadata-frame gaps 60)
(fn2-qr-metadata-frame cfound 1)
(fn2-qr-metadata-frame h 60)
(fn2-qr-metadata-frame evidence 60)
(fn2-qr-metadata-frame qualified 1)
(fn2-qr-metadata-frame local 1)

; Bridge the independent sum to the actual held-source gate. This is the
; prerequisite for framing all other pool mutators, not just query calls.
(defthm fn2-qr-counts-matchp-entry
 (implies (and (fn2-qr-counts-matchp n p d) (natp r) (< r (nfix n)))
          (equal (fn2-pool-query-ref-count r p)
                 (fn2-qr-reference-count (fn2-id-decides-rows d) r (fn2-pool-gen r p) d)))
 :hints (("Goal" :induct (fn2-qr-counts-matchp n p d)
          :in-theory (enable fn2-qr-counts-matchp))))
(defthm fn2-qr-descriptors-validp-entry
 (implies (and (fn2-qr-descriptors-validp n d p) (natp i) (< i (nfix n)))
          (fn2-qr-row-validp i d p))
 :hints (("Goal" :induct (fn2-qr-descriptors-validp n d p)
          :in-theory (enable fn2-qr-descriptors-validp))))
(defthm fn2-qr-first-active-reference-positive
 (implies (and (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
               (logbitp 0 (fn2-id-decides-qmask i d)))
          (< 0 (fn2-pool-query-ref-count (fn2-id-decides-q1slot i d) p)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn2-query-references-accountedp fn2-qr-row-validp
                                   fn2-qr-window-validp fn2-qr-row-count fn2-qr-reference-on)
          :use ((:instance fn2-qr-reference-count-row-lower-bound
                 (s i) (n (fn2-id-decides-rows d)) (r (fn2-id-decides-q1slot i d))
                 (g (fn2-id-decides-q1gen i d)))))))
(defthm fn2-qr-second-active-reference-positive
 (implies (and (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
               (logbitp 1 (fn2-id-decides-qmask i d)))
          (< 0 (fn2-pool-query-ref-count (fn2-id-decides-q2slot i d) p)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn2-query-references-accountedp fn2-qr-row-validp
                                   fn2-qr-window-validp fn2-qr-row-count fn2-qr-reference-on)
          :use ((:instance fn2-qr-reference-count-row-lower-bound
                 (s i) (n (fn2-id-decides-rows d)) (r (fn2-id-decides-q2slot i d))
                 (g (fn2-id-decides-q2gen i d)))))))
(defthm fn2-qr-same-handle-two-references-counted
 (implies (and (fn2-query-references-accountedp p d) (natp i) (< i (fn2-id-decides-rows d))
               (equal (fn2-id-decides-qmask i d) 3)
               (equal (fn2-id-decides-q1slot i d) (fn2-id-decides-q2slot i d))
               (equal (fn2-id-decides-q1gen i d) (fn2-id-decides-q2gen i d)))
          (<= 2 (fn2-pool-query-ref-count (fn2-id-decides-q1slot i d) p)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn2-query-references-accountedp fn2-qr-row-validp
                                   fn2-qr-window-validp fn2-qr-row-count fn2-qr-reference-on)
          :use ((:instance fn2-qr-reference-count-row-lower-bound
                 (s i) (n (fn2-id-decides-rows d)) (r (fn2-id-decides-q1slot i d))
                 (g (fn2-id-decides-q1gen i d)))))))

(defun-nx fn2-qr-local-deltap (s p q d e)
 (and (fn2-qr-sources-equal p q) (equal (fn2-id-decides-rows d) (fn2-id-decides-rows e))
      (fn2-qr-keys-except s d e) (fn2-qr-counter-delta s p q d e)))
