; Proof-only actual tombstone feedback/incoming entry join.
(in-package "ACL2")
(include-book "post-identity-captured-refinement")
; Carried ghost obligations for either hash choice before tombstone feedback.
(defun-nx fn-pic-hash-entryp (limit c incoming)
  (let ((d (fn-pic-get incoming-desc c)))
    (and (equal (fn-pic-get incoming-n c) (len incoming))
         (natp limit) (<= limit 63)
         (fn-b3-octet-listp incoming)
         (implies (member-eq (fn-pic-get phase c) '(:tomb-agent-held :tomb-agent-incoming)) d)
         (<= (pgs-dcb-word-count (len incoming)) (* 128 (expt 2 limit)))
         (implies d
           (and (fn-pic-spanp d (len incoming))
                (fn-b3-octet-listp (fn-pic-span-value d incoming))
                (<= (pgs-dcb-word-count (fn-pic-span-length d (len incoming)))
                    (* 128 (expt 2 limit))))))))
(local (defthm fn-pic-entry-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-entry-whole-value
 (equal (fn-pic-span-value '(0 0 0) incoming) incoming)
 :hints (("Goal" :in-theory (enable fn-pic-span-value fn-pic-at take nthcdr)))))
(local (defthm fn-pic-entry-hash-start-establishes-product
 (implies (and (fn-pic-hash-entryp limit c incoming)
               (implies sourcep (fn-pic-get incoming-desc c)))
  (fn-pic-digest-trajectoryp limit (fn-pic-hash-start sourcep c) incoming pgs-digest-state))
 :hints (("Goal" :in-theory (e/d (fn-pic-hash-entryp fn-pic-hash-start
  fn-pic-digest-trajectoryp fn-pic-spanp fn-pic-span-length)
  (fn-pic-at nth update-nth fn-pic-span-value fn-b3-octet-listp pgs-dcb-word-count))))))
(defthm fn-pic-feed-funded-establishes-hash-entry-trajectory
 (implies (and (fn-pic-hash-entryp limit c incoming)
               (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming)))
   (let ((next (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
    (implies (equal (fn-pic-get phase next) :digest-begin)
      (fn-pic-digest-trajectoryp limit next incoming pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-entry-hash-start-establishes-product (sourcep t))
 (:instance fn-pic-entry-hash-start-establishes-product (sourcep nil)))
 :in-theory (e/d (fn-pic-feed-funded fn-pic-feed fn-pic-finish
                      fn-pic-demand fn-pic-hash-entryp)
 (fn-pic-at fn-pic-entry-hash-start-establishes-product fn-pic-digest-trajectoryp fn-pic-hash-start
  fn-pic-observation-okp fn-pic-observed-byte fn-pic-start-parser
  fn-pic-span-length fn-pic-span-offset nth update-nth)))))
(defthm fn-pic-next-establishes-hash-entry-trajectory
 (implies (and (fn-pic-hash-entryp limit c fn-octets)
               (member-eq (fn-pic-get phase c) '(:tomb-flag :tomb-agent-held :tomb-agent-incoming)))
   (let ((next (mv-nth 1 (fn-pic-next c fuel fn-octets))))
    (implies (equal (fn-pic-get phase next) :digest-begin)
      (fn-pic-digest-trajectoryp limit next fn-octets pgs-digest-state))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-feed-funded-establishes-hash-entry-trajectory (incoming fn-octets))
 (:instance fn-pic-feed-funded-establishes-hash-entry-trajectory (incoming fn-octets)
  (observation :control))
 (:instance fn-pic-feed-funded-establishes-hash-entry-trajectory (incoming fn-octets)
  (observation (list :incoming-byte (fn-pic-get incoming-token c) (fn-pic-at 1 (fn-pic-demand c))
                  (fn-octets-get (fn-pic-at 1 (fn-pic-demand c)) fn-octets))) (fuel (- fuel 1))))
 :in-theory (e/d (fn-pic-next fn-pic-finish)
 (fn-pic-at fn-pic-hash-entryp fn-pic-digest-trajectoryp fn-pic-feed-funded
  fn-pic-demand fn-octets-get nth update-nth)))))
