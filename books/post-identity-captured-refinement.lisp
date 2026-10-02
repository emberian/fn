; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only virtual-message join for the actual captured digest adapter.
; Full PRF-1148 remains open: parser inverse and funded host authority are
; separate obligations. No list denotation runs in the served controller.
(in-package "ACL2")
(include-book "post-identity-captured-digest-block")
(include-book "pagestore-digest-cursor-semantics")

(local
 (defthm fn-pic-digest-begin-establishes-virtual-semantics
  (implies
    (and (equal (fn-pic-get phase c) :digest-begin)
         (posp fuel) (natp limit) (<= limit 63)
         (equal (len (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
                (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
         (fn-b3-octet-listp (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
         (<= (pgs-dcb-word-count
               (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
             (* 128 (expt 2 limit))))
    (pgs-dcs-invariantp limit
      (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))
      (fn-pic-span-value (fn-pic-get digest-desc c) incoming)
      (mv-nth 3 (fn-pic-digest-effect c fuel pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal"
    :use ((:instance pgs-dcs-begin-establishes-invariant
            (byte-total (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
            (sel 0) (base 0) (capture (fn-pic-get selected c)) (lease (fn-pic-get grant c))))
    :in-theory (e/d (fn-pic-digest-effect)
      (pgs-dcs-invariantp pgs-dcb-begin fn-pic-at fn-pic-spanp fn-pic-span-value
       fn-pic-span-length fn-b3-octet-listp pgs-dcb-word-count))))))

(local
 (defthm fn-pic-semantic-invariant-implies-scalar-guard
   (implies (pgs-dcs-invariantp limit byte-total msg pgs-digest-state)
            (fn-pic-digest-scalar-guardp byte-total pgs-digest-state))
   :hints (("Goal"
     :use (pgs-dcs-invariant-implies-domain pgs-dbd-domain-implies-byte-step-guard)
     :in-theory (e/d (fn-pic-digest-scalar-guardp)
       (pgs-dcs-invariantp pgs-dbd-domainp pgs-dcb-word-count nth update-nth))))))

(local
 (defthm fn-pic-digest-terminal-effect-is-virtual-blake3
  (implies
    (and (equal (fn-pic-get phase c) :digest-next) (posp fuel)
         (equal (pgs-dc-mode pgs-digest-state) :done)
         (equal (pgs-dc-capture pgs-digest-state) (fn-pic-get selected c))
         (equal (pgs-dc-lease pgs-digest-state) (fn-pic-get grant c))
         (pgs-dcs-invariantp limit
           (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))
           (fn-pic-span-value (fn-pic-get digest-desc c) incoming) pgs-digest-state))
    (equal (mv-nth 1 (fn-pic-digest-effect c fuel pgs-digest-state))
           (list :digest-result
             (fn-blake3 (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))))
  :rule-classes nil
  :hints (("Goal"
    :use ((:instance pgs-dcs-done-result-is-blake3
            (byte-total (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))))
    :in-theory (e/d (fn-pic-digest-effect)
      (pgs-dcs-invariantp pgs-dcb-result-octets fn-blake3 fn-pic-at fn-pic-span-value
       fn-pic-span-length fn-pic-digest-scalar-guardp))))))

; Conditional trajectory join. The collector-to-block theorem below must
; discharge this exact block premise on every consuming commit.
(local
 (defthm fn-pic-digest-commit-preserves-virtual-semantics
  (implies
    (and (equal (fn-pic-get phase c) :digest-commit) (posp fuel)
         (equal (pgs-dc-capture pgs-digest-state) (fn-pic-get selected c))
         (equal (pgs-dc-lease pgs-digest-state) (fn-pic-get grant c))
         (pgs-dcs-invariantp limit
           (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))
           (fn-pic-span-value (fn-pic-get digest-desc c) incoming) pgs-digest-state)
         (pgs-dcs-blockp (fn-pic-digest-block c)
           (fn-pic-span-value (fn-pic-get digest-desc c) incoming) pgs-digest-state))
    (pgs-dcs-invariantp limit
      (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c))
      (fn-pic-span-value (fn-pic-get digest-desc c) incoming)
      (mv-nth 3 (fn-pic-digest-effect c fuel pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal"
    :use ((:instance pgs-dcs-byte-step-preserves-invariant
            (byte-total (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
            (block (fn-pic-digest-block c))))
    :in-theory (e/d (fn-pic-digest-effect)
      (pgs-dcs-invariantp pgs-dcs-blockp pgs-dcb-step fn-pic-at fn-pic-span-value
       fn-pic-span-length fn-pic-digest-scalar-guardp fn-pic-digest-block))))))


; Product representation invariant for the actual digest continuations.
; Logical incoming denotes the unchanged concrete fn-octets subject.
; This predicate is proof-only and never scans a served input.
(defun-nx fn-pic-digest-trajectoryp (limit c incoming pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :verify-guards nil))
  (let* ((phase (fn-pic-get phase c)) (d (fn-pic-get digest-desc c))
         (n (fn-pic-span-length d (fn-pic-get incoming-n c)))
         (msg (fn-pic-span-value d incoming)))
    (and (fn-pic-spanp d (len incoming))
         (equal (fn-pic-get incoming-n c) (len incoming))
         (fn-b3-octet-listp msg) (natp limit) (<= limit 63)
         (<= (pgs-dcb-word-count n) (* 128 (expt 2 limit)))
         (member-eq phase '(:digest-begin :digest-next :digest-read :digest-commit
                           :digest-compare :groups :done))
         (implies (not (equal phase :digest-begin))
           (and (pgs-dcs-invariantp limit n msg pgs-digest-state)
                (equal (pgs-dc-capture pgs-digest-state) (fn-pic-get selected c))
                (equal (pgs-dc-lease pgs-digest-state) (fn-pic-get grant c))))
         (implies (member-eq phase '(:digest-read :digest-commit))
           (and (fn-pic-block-prefixp c incoming)
                (equal (fn-pic-get block-start c) (pgs-dcb-next-byte-offset pgs-digest-state))
                (equal (fn-pic-get block-count c) (pgs-dcb-read-demand n pgs-digest-state))))
         (implies (equal phase :digest-commit)
           (equal (fn-pic-get pos c) (fn-pic-get block-count c)))
         (implies (member-eq phase '(:digest-compare :groups :done))
           (and (equal (pgs-dc-mode pgs-digest-state) :done)
                (equal (fn-pic-get digest c) (fn-blake3 msg)))))))

(local (defthm fn-pic-product-take-zero (equal (take 0 x) nil) :hints (("Goal" :in-theory (enable take)))))
(local (defthm fn-pic-product-at-is-nth
  (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
  :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-product-len-take
  (implies (natp n) (equal (len (take n x)) n))))
(local (defthm fn-pic-product-len-tail
  (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-pic-product-len-append
  (equal (len (append x y)) (+ (len x) (len y)))
  :hints (("Goal" :induct (append x y) :in-theory (enable binary-append len)))))
(local (defthm fn-pic-product-span-length
  (implies (fn-pic-spanp d (len incoming))
    (equal (len (fn-pic-span-value d incoming)) (fn-pic-span-length d (len incoming))))
  :hints (("Goal" :in-theory (e/d (fn-pic-spanp fn-pic-span-value fn-pic-span-length)
                                   (take nthcdr fn-pic-at nth binary-append))))))
(local (defthm fn-pic-product-invariant-natural-positions
  (implies (pgs-dcs-invariantp limit n msg pgs-digest-state)
    (and (natp (pgs-dc-pos pgs-digest-state)) (natp (pgs-dc-end pgs-digest-state))))
  :hints (("Goal" :use ((:instance pgs-dcs-invariant-implies-domain (byte-total n)))
    :in-theory (e/d (pgs-dbd-domainp pgs-dcd-domainp)
      (pgs-dcs-invariantp pgs-dcs-invariant-implies-domain pgs-dcd-framesp pgs-dbd-framesp pgs-dcd-powerp pgs-dc-pos pgs-dc-end nth))))))
(local (defthm fn-pic-product-invariant-step-status
  (implies (pgs-dcs-invariantp limit n msg pgs-digest-state)
    (member-eq (mv-nth 0 (pgs-dcb-step n block pgs-digest-state)) '(:continue :done)))
  :hints (("Goal" :use ((:instance pgs-dcs-invariant-implies-domain (byte-total n))
                        (:instance pgs-dbd-byte-step-is-never-invalid (byte-total n)))
    :in-theory (disable pgs-dcs-invariantp pgs-dbd-domainp pgs-dcb-step pgs-dcs-invariant-implies-domain pgs-dbd-byte-step-is-never-invalid)))))
(local (defthm fn-pic-product-byte-begin-aliases-unfolds
  (and (equal (pgs-dc-capture (pgs-dcb-begin sel base n capture lease pgs-digest-state)) capture)
       (equal (pgs-dc-lease (pgs-dcb-begin sel base n capture lease pgs-digest-state)) lease))
  :hints (("Goal" :in-theory (enable pgs-dcb-begin pgs-dc-begin pgs-dc-capture pgs-dc-lease)))))
(local (defthm fn-pic-product-invariant-valid-demand
  (implies (pgs-dcs-invariantp limit n msg pgs-digest-state)
    (and (natp (pgs-dcb-next-byte-offset pgs-digest-state))
         (<= (+ (pgs-dcb-next-byte-offset pgs-digest-state)
                (pgs-dcb-read-demand n pgs-digest-state)) n)))
  :hints (("Goal"
    :use ((:instance pgs-dcs-invariant-implies-domain (byte-total n))
          (:instance pgs-dbd-domain-implies-byte-step-guard (byte-total n))
          fn-pic-product-invariant-natural-positions)
    :in-theory (e/d (pgs-dcb-next-byte-offset pgs-dcb-read-demand)
      (pgs-dcs-invariantp pgs-dbd-domainp pgs-dc-needs-block pgs-dc-pos pgs-dc-end
       pgs-dbd-domain-scalars fn-pic-product-invariant-natural-positions pgs-dcs-invariant-implies-domain pgs-dbd-domain-implies-byte-step-guard))))))
(local
 (defthm fn-pic-digest-next-preserves-full-virtual-trajectory-natural-fuel
  (implies (and (fn-pic-digest-trajectoryp limit c incoming pgs-digest-state) (natp fuel))
    (fn-pic-digest-trajectoryp limit
      (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming
      (mv-nth 3 (fn-pic-digest-next c fuel pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal"
    :cases ((equal (fn-pic-get phase c) :digest-begin)
            (equal (fn-pic-get phase c) :digest-next)
            (equal (fn-pic-get phase c) :digest-commit))
    :use ((:instance fn-pic-product-invariant-natural-positions
            (n (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
          (:instance fn-pic-product-invariant-valid-demand
            (n (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming)))
          (:instance fn-pic-product-invariant-step-status
            (n (fn-pic-span-length (fn-pic-get digest-desc c) (fn-pic-get incoming-n c)))
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) incoming))
            (block (fn-pic-digest-block c)))
          fn-pic-digest-begin-establishes-virtual-semantics
          fn-pic-digest-terminal-effect-is-virtual-blake3
          fn-pic-digest-commit-preserves-virtual-semantics
          fn-pic-completed-collector-satisfies-digest-block
          fn-pic-digest-next-establishes-requested-prefix)
    :in-theory (e/d (fn-pic-digest-trajectoryp fn-pic-digest-next
          fn-pic-digest-effect fn-pic-feed-funded fn-pic-feed
          fn-pic-demand fn-pic-observation-okp)
      (pgs-dcs-invariantp pgs-dcs-blockp pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets
       fn-pic-block-prefixp fn-pic-at fn-pic-spanp fn-pic-span-value fn-pic-span-length
       fn-pic-digest-block fn-pic-digest-scalar-guardp fn-blake3 fn-b3-octet-listp
       pgs-dc-capture pgs-dc-lease pgs-dc-mode pgs-dc-pos pgs-dc-end
       fn-pic-product-invariant-natural-positions fn-pic-product-invariant-valid-demand
       fn-pic-product-invariant-step-status pgs-dcb-word-count pgs-dcb-read-demand pgs-dcb-next-byte-offset nth update-nth))))))

(defthm fn-pic-digest-next-preserves-full-virtual-trajectory
  (implies (fn-pic-digest-trajectoryp limit c incoming pgs-digest-state)
    (fn-pic-digest-trajectoryp limit
      (mv-nth 1 (fn-pic-digest-next c fuel pgs-digest-state)) incoming
      (mv-nth 3 (fn-pic-digest-next c fuel pgs-digest-state))))
  :rule-classes nil
  :hints (("Goal" :cases ((natp fuel))
    :use fn-pic-digest-next-preserves-full-virtual-trajectory-natural-fuel
    :in-theory (e/d (fn-pic-digest-next fn-pic-digest-effect)
      (fn-pic-digest-trajectoryp fn-pic-feed-funded fn-pic-at fn-pic-span-length
       fn-pic-digest-scalar-guardp pgs-dcb-begin pgs-dcb-step pgs-dcb-result-octets
       pgs-dcb-next-byte-offset pgs-dcb-read-demand fn-pic-digest-block)))))

(local (defthm fn-pic-product-read-nth-octet
  (implies (and (fn-b3-octet-listp msg) (natp i) (< i (len msg)))
    (unsigned-byte-p 8 (nth i msg)))
  :hints (("Goal" :induct (nth i msg) :in-theory (enable fn-b3-octet-listp nth)))))
(local (defthm fn-pic-product-read-scalar-observation-valid
  (implies
    (and (fn-pic-block-prefixp c fn-octets)
         (fn-b3-octet-listp (fn-pic-span-value (fn-pic-get digest-desc c) fn-octets))
         (< (fn-pic-get pos c) (fn-pic-get block-count c)))
    (let ((offset (fn-pic-span-offset (fn-pic-get digest-desc c)
                   (+ (fn-pic-get block-start c) (fn-pic-get pos c)))))
      (and (natp offset) (< offset (fn-octets-len fn-octets))
           (unsigned-byte-p 8 (fn-octets-get offset fn-octets)))))
  :hints (("Goal"
    :use ((:instance fn-pic-span-offset-is-within-source
            (d (fn-pic-get digest-desc c)) (n (len fn-octets))
            (i (+ (fn-pic-get block-start c) (fn-pic-get pos c))))
          (:instance fn-pic-span-byte-is-denoted-byte
            (d (fn-pic-get digest-desc c)) (xs fn-octets)
            (i (+ (fn-pic-get block-start c) (fn-pic-get pos c))))
          (:instance fn-pic-product-read-nth-octet
            (msg (fn-pic-span-value (fn-pic-get digest-desc c) fn-octets))
            (i (+ (fn-pic-get block-start c) (fn-pic-get pos c)))))
    :in-theory (e/d (fn-pic-block-prefixp fn-octets-get fn-octets-len)
      (fn-pic-at fn-pic-spanp fn-pic-span-offset fn-pic-span-length fn-pic-span-value
       fn-b3-octet-listp nth nthcdr take revappend fn-pic-product-read-nth-octet
       fn-pic-span-offset-is-within-source fn-pic-span-byte-is-denoted-byte))))))
(local (defthm fn-pic-product-read-prefix-bounds
  (implies (fn-pic-block-prefixp c incoming)
    (and (natp (fn-pic-get pos c)) (natp (fn-pic-get block-start c))
         (natp (fn-pic-get block-count c))
         (<= (fn-pic-get pos c) (fn-pic-get block-count c))))
  :hints (("Goal" :in-theory (e/d (fn-pic-block-prefixp)
    (fn-pic-at fn-pic-spanp fn-pic-span-value fn-pic-span-length nth take nthcdr revappend))))))
(defthm fn-pic-next-preserves-full-virtual-trajectory
  (implies (fn-pic-digest-trajectoryp limit c fn-octets pgs-digest-state)
    (fn-pic-digest-trajectoryp limit
      (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets pgs-digest-state))
  :rule-classes nil
  :hints (("Goal"
    :cases ((equal (fn-pic-get phase c) :digest-read)
            (equal (fn-pic-get phase c) :groups)
            (equal (fn-pic-get phase c) :digest-compare))
    :use ((:instance fn-pic-product-read-prefix-bounds (incoming fn-octets))
          fn-pic-next-preserves-exact-collector-prefix
          fn-pic-product-read-scalar-observation-valid)
    :in-theory (e/d (fn-pic-digest-trajectoryp fn-pic-next fn-pic-feed-funded
          fn-pic-feed fn-pic-finish fn-pic-demand fn-pic-observation-okp
          fn-pic-groups-start fn-pic-block-add fn-octets-len)
      (fn-pic-product-read-prefix-bounds fn-pic-block-prefixp fn-pic-product-read-scalar-observation-valid
       fn-pic-next-preserves-exact-collector-prefix
       pgs-dcs-invariantp pgs-dc-mode pgs-dc-capture pgs-dc-lease
       pgs-dcb-read-demand pgs-dcb-next-byte-offset pgs-dcb-word-count
       fn-pic-at fn-pic-spanp fn-pic-span-offset fn-pic-span-length fn-pic-span-value
       fn-blake3 fn-b3-octet-listp fn-pic-groups-step fn-pic-groups-begin
       nth update-nth fn-octets-get)))))
