; Proof-only source carry for this job's frozen private stage. These predicates
; are never whole-source validation on a served turn.
(in-package "ACL2")
(include-book "bp-node-checkpoint-digest")
(set-verify-guards-eagerness 0)

(defun-nx fn-bpck-ready-sourcep (job)
  (and (equal (fn-bpn-nth 6 job) :digest-finish)
       (posp (fn-bpn-nth 8 job))
       (<= (fn-bpn-nth 8 job) *fn-bpc-max-uint*)
       (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job)))
       (equal (fn-bpn-nth 11 job) :private)
       (fn-b3-octet-listp (fn-bpck-frame-prefix job))
       (equal (len (fn-bpck-frame-prefix job)) (+ 14 (fn-bpn-nth 8 job)))))

(local
 (defthm fn-bpck-profile-count-fits-digest-tree
   (implies (and (posp count) (<= count *fn-bpc-max-uint*))
            (<= (pgs-dcb-word-count (+ 14 count)) (* 128 (expt 2 63))))
   :hints (("Goal" :use ((:instance rational-implies2 (x (/ (+ 14 count) 8))))
                   :in-theory (e/d (pgs-dcb-word-count) (rational-implies2))))))

(defthm fn-bpck-digest-start-establishes-exact-source-invariant
  (implies (fn-bpck-ready-sourcep job)
    (and (equal (mv-nth 0 (fn-bpck-digest-start job pgs-digest-state)) :started)
         (fn-bpck-frame-digest-invariantp job
           (mv-nth 1 (fn-bpck-digest-start job pgs-digest-state)))))
  :hints (("Goal"
    :use ((:instance fn-bpck-profile-count-fits-digest-tree
                     (count (fn-bpn-nth 8 job)))
          (:instance pgs-dcs-begin-establishes-invariant
                     (limit 63) (byte-total (+ 14 (fn-bpn-nth 8 job)))
                     (msg (fn-bpck-frame-prefix job)) (sel 0) (base 0)
                     (capture (list :bp-checkpoint-stage (fn-bpn-nth 1 job)
                                    (fn-bpn-nth 3 job)))
                     (lease (fn-bpn-nth 1 job))))
    :in-theory (e/d (fn-bpck-ready-sourcep fn-bpck-digest-start
                      fn-bpck-frame-digest-invariantp pgs-dcb-begin pgs-dc-begin)
                     (pgs-dcs-invariantp fn-bpck-frame-prefix
                      pgs-dcs-begin-establishes-invariant nth update-nth))
    :do-not-induct t))
  :rule-classes nil)

; BLOCKP names the exact bytes of the frozen prefix at this cursor's range.
; Native pread must refine that observation; short/refused observations leave
; the source cursor unchanged and remain UNCERTAIN rather than padding data.
(defthm fn-bpck-digest-step-preserves-exact-source-invariant
  (implies (and (fn-bpck-frame-digest-invariantp job pgs-digest-state)
                (pgs-dcs-blockp (fn-b3-words 16 octets)
                                 (fn-bpck-frame-prefix job) pgs-digest-state))
           (fn-bpck-frame-digest-invariantp job
             (mv-nth 1 (fn-bpck-digest-step job octets pgs-digest-state))))
  :hints (("Goal"
    :use ((:instance pgs-dcs-byte-step-preserves-invariant
                     (limit 63) (byte-total (+ 14 (fn-bpn-nth 8 job)))
                     (msg (fn-bpck-frame-prefix job))
                     (block (fn-b3-words 16 octets)))
          (:instance pgs-dcb-step-preserves-capture-and-lease
                     (byte-total (+ 14 (fn-bpn-nth 8 job)))
                     (block (fn-b3-words 16 octets))))
    :in-theory (e/d (fn-bpck-digest-step fn-bpck-digest-action
                      fn-bpck-frame-digest-invariantp)
                     (fn-bpck-frame-prefix pgs-dcs-invariantp pgs-dcs-blockp
                      pgs-dcb-step fn-b3-words
                      pgs-dcs-byte-step-preserves-invariant
                      pgs-dcb-step-preserves-capture-and-lease))
    :do-not-induct t))
  :rule-classes nil)

(local
 (defthm fn-bpck-cbor-octets-are-b3-octets
   (implies (fn-cbor-octet-listp octets) (fn-b3-octet-listp octets))
   :hints (("Goal" :induct (len octets)
                   :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                                      fn-b3-octet-listp)))))
(local
 (defthm fn-bpck-frozen-prefix-is-octets
   (fn-b3-octet-listp (fn-bpck-frame-prefix job))
   :hints (("Goal" :use ((:instance fn-bpnr-enc-octets
                                     (x (fn-bpn-nth 5 job)) (d (fn-bpn-nth 4 job)))
                         (:instance fn-bpc-u64-bytes-are-octets
                                     (n (nfix (fn-bpn-nth 8 job)))))
     :in-theory (e/d (fn-bpck-frame-prefix fn-bpcke-prefix fn-bpck-prefix)
                      (fn-bpnr-enc fn-bpc-u64-bytes))
     :cases ((fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job)))))))
(local
 (defthm fn-bpck-frozen-prefix-length
   (equal (len (fn-bpck-frame-prefix job))
          (+ 14 (len (fn-bpnr-enc (fn-bpn-nth 5 job) (fn-bpn-nth 4 job)))))
   :hints (("Goal" :use ((:instance fn-bpc-u64-bytes-have-eight-octets
                                     (n (nfix (fn-bpn-nth 8 job)))))
     :in-theory (e/d (fn-bpck-frame-prefix fn-bpcke-prefix fn-bpck-prefix)
                      (fn-bpnr-enc fn-bpc-u64-bytes))))))

(defthm fn-bpck-exact-write-history-establishes-ready-source
  (implies (and (fn-bpcke-invariantp job emitted)
                (equal (fn-bpn-nth 6 job) :digest-finish)
                (equal (fn-bpn-nth 11 job) :private)
                (posp (fn-bpn-nth 8 job))
                (<= (fn-bpn-nth 8 job) *fn-bpc-max-uint*)
                (equal (fn-bpn-nth 10 job) (+ 14 (fn-bpn-nth 8 job))))
           (fn-bpck-ready-sourcep job))
  :hints (("Goal" :in-theory (e/d (fn-bpcke-invariantp fn-bpck-ready-sourcep)
                                   (fn-bpck-frame-prefix fn-bpnr-enc
                                    fn-bpnrc-tasks-validp fn-bpnrc-residual))))
  :rule-classes nil)
