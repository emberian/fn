; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only join: one supported incoming domain covers either actual hash choice.
(in-package "ACL2")
(include-book "post-identity-captured-hash-choice")
(include-book "post-identity-captured-hash-entry")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-pic-hd-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-hd-octets-tail
 (implies (and (fn-b3-octet-listp x) (natp n)) (fn-b3-octet-listp (nthcdr n x)))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr fn-b3-octet-listp)))))
(local (defthm fn-pic-hd-octets-take
 (implies (and (fn-b3-octet-listp x) (natp n) (<= n (len x))) (fn-b3-octet-listp (take n x)))
 :hints (("Goal" :induct (take n x) :in-theory (enable take fn-b3-octet-listp len)))))
(local (defthm fn-pic-hd-octets-append
 (implies (and (fn-b3-octet-listp x) (fn-b3-octet-listp y)) (fn-b3-octet-listp (append x y)))
 :hints (("Goal" :induct (append x y) :in-theory (enable binary-append fn-b3-octet-listp)))))
(local (defthm fn-pic-hd-len-tail
 (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-pic-hd-span-octets
 (implies (and (fn-b3-octet-listp incoming) (fn-pic-spanp d (len incoming)))
  (fn-b3-octet-listp (fn-pic-span-value d incoming)))
 :hints (("Goal" :in-theory (e/d (fn-pic-spanp fn-pic-span-value)
  (fn-pic-at nth take nthcdr binary-append fn-b3-octet-listp))))))
(local (defthm fn-pic-hd-span-within-whole
 (implies (fn-pic-spanp d (len incoming))
  (and (natp (fn-pic-span-length d (len incoming)))
       (<= (fn-pic-span-length d (len incoming)) (len incoming))))
 :hints (("Goal" :in-theory (enable fn-pic-spanp fn-pic-span-length)))))
(local (defthm fn-pic-hd-word-count-monotone
 (implies (and (natp x) (natp y) (<= x y))
  (<= (pgs-dcb-word-count x) (pgs-dcb-word-count y)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (pgs-dcb-word-count) (ceiling))))))
(local (defthm fn-pic-hd-supported-whole-implies-virtual
 (implies (and (fn-pic-spanp d (len incoming))
               (<= (pgs-dcb-word-count (len incoming)) capacity))
  (<= (pgs-dcb-word-count (fn-pic-span-length d (len incoming))) capacity))
 :hints (("Goal" :use (:instance fn-pic-hd-word-count-monotone
  (x (fn-pic-span-length d (len incoming))) (y (len incoming)))
 :in-theory (disable fn-pic-spanp fn-pic-span-length pgs-dcb-word-count)))))
(local (defthm fn-pic-hd-context-establishes-entry-domain
 (implies (and (fn-pic-choice-contextp c incoming held)
               (implies (member-eq (fn-pic-get phase c) '(:tomb-agent-held :tomb-agent-incoming))
                        (fn-pic-get incoming-desc c))
               (fn-b3-octet-listp incoming) (natp limit) (<= limit 63)
               (<= (pgs-dcb-word-count (len incoming)) (* 128 (expt 2 limit))))
  (fn-pic-hash-entryp limit c incoming))
 :hints (("Goal" :in-theory (e/d (fn-pic-choice-contextp fn-pic-hash-entryp)
  (fn-pic-at fn-pic-spanp fn-pic-span-value fn-pic-span-length fn-b3-octet-listp pgs-dcb-word-count))))) )
(local (defthm fn-pic-hd-b3-octets-are-concrete-octets
 (implies (fn-b3-octet-listp incoming) (fn-cbor-octet-listp incoming))
 :hints (("Goal" :induct (fn-b3-octet-listp incoming)
  :in-theory (enable fn-b3-octet-listp fn-cbor-octet-listp fn-cbor-octetp unsigned-byte-p)))))
; Flag entry or an already-established paid comparison, sharing one whole extent.
(defthm fn-pic-feed-funded-establishes-chosen-hash-semantics
 (implies (and (or (and (fn-pic-choice-contextp c incoming held)
                       (equal (fn-pic-get phase c) :tomb-flag))
                  (fn-pic-choice-productp c incoming held))
               (fn-pic-choice-observationp c observation incoming held)
               (fn-b3-octet-listp incoming) (natp limit) (<= limit 63)
               (<= (pgs-dcb-word-count (len incoming)) (* 128 (expt 2 limit))))
  (let ((next (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
   (implies (equal (fn-pic-get phase next) :digest-begin)
    (and (fn-pic-choice-outcomep next incoming held)
         (fn-pic-digest-trajectoryp limit next incoming pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-feed-funded-establishes-exact-tombstone-hash-choice
   fn-pic-feed-funded-preserves-exact-tombstone-hash-choice
   fn-pic-feed-funded-establishes-hash-entry-trajectory
   fn-pic-hd-context-establishes-entry-domain)
 :in-theory (e/d (fn-pic-choice-productp)
  (fn-pic-choice-contextp fn-pic-hash-entryp fn-pic-choice-observationp fn-pic-choice-outcomep
   fn-pic-feed-funded fn-pic-digest-trajectoryp fn-pic-retained-agent fn-rcl-tomb-agent
   fn-b3-octet-listp fn-pic-at pgs-dcb-word-count fn-pic-spanp nth take nthcdr)))))
(defthm fn-pic-next-establishes-chosen-hash-semantics
 (implies (and (fn-pic-choice-productp c fn-octets held)
               (fn-b3-octet-listp fn-octets) (natp limit) (<= limit 63)
               (<= (pgs-dcb-word-count (len fn-octets)) (* 128 (expt 2 limit))))
  (let ((next (mv-nth 1 (fn-pic-next c fuel fn-octets))))
   (implies (equal (fn-pic-get phase next) :digest-begin)
    (and (fn-pic-choice-outcomep next fn-octets held)
         (fn-pic-digest-trajectoryp limit next fn-octets pgs-digest-state)))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-next-preserves-exact-tombstone-hash-choice
   fn-pic-next-establishes-hash-entry-trajectory
   (:instance fn-pic-hd-context-establishes-entry-domain (incoming fn-octets)))
 :in-theory (e/d (fn-pic-choice-productp)
  (fn-pic-choice-contextp fn-pic-hash-entryp fn-pic-choice-outcomep fn-pic-next fn-pic-digest-trajectoryp
   fn-pic-retained-agent fn-rcl-tomb-agent fn-b3-octet-listp fn-pic-at pgs-dcb-word-count
   fn-pic-spanp nth take nthcdr)))))
