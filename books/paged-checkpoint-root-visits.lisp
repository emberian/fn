; Root-fold invocation visits. Semantic leaf work is explicitly unaccounted;
; this measures traversals, not total CPU or heap allocation.
(in-package "ACL2")
(include-book "paged-checkpoint-root-carried")
(include-book "def-fold-visits")
(local (include-book "arithmetic/top" :dir :system))

(defmacro pck-derive-fold-visits (fn &key hints)
  `(make-event
    (mv-let (cost leaves)
      (fn-fv-term (getpropc ',fn 'unnormalized-body nil (w state)) ',fn (w state))
      (declare (ignore cost))
      (value (list 'def-fold-visits ',fn :leaves leaves :hints ',hints)))))

(pck-derive-fold-visits fn-pck-config-tail)
(pck-derive-fold-visits fn-sfi-cpr-prefix-carried
  :hints (("Goal" :in-theory (enable fn-cpr-config-firstp))))
(pck-derive-fold-visits fn-pck-cpr-resume-from)
(pck-derive-fold-visits fn-replay-identity-loop)
(pck-derive-fold-visits fn-cpe-projection-replay)
(pck-derive-fold-visits fn-sco-consumer-resume)
(pck-derive-fold-visits fn-th-prefix-loop)
(pck-derive-fold-visits fn-pck-root-extend-carried)

(defthm pck-tail-fold-visits
  (equal (fn-pck-config-tail-fold-visits n rest) (+ 1 (nfix n)))
  :hints (("Goal" :induct (fn-pck-config-tail-fold-visits n rest))))

(defthm pck-identity-fold-visits
  (<= (fn-replay-identity-loop-fold-visits records ctx) (+ 1 (len records)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-replay-identity-loop-fold-visits records ctx)
           :in-theory (disable fn-store-event-p fn-replay-identity-step fn-stxk-fault))))

(defthm pck-consumer-fold-visits
  (<= (fn-cpe-projection-replay-fold-visits s records expected) (+ 1 (len records)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-cpe-projection-replay-fold-visits s records expected)
           :in-theory (disable fn-cpe-projection-step fn-cp-nth))))

(defthm pck-consumer-resume-fold-visits
  (<= (fn-sco-consumer-resume-fold-visits consumer events expected) (+ 2 (len events)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-cpe-projection-replay-fold-visits fn-cp-nth))))

(defthm pck-topic-fold-visits
  (equal (fn-th-prefix-loop-fold-visits projection records) (+ 1 (len records)))
  :hints (("Goal" :induct (fn-th-prefix-loop-fold-visits projection records)
           :in-theory (disable fn-th-prefix-step fn-th-at fn-th-prefix-state))))

(defthm pck-cpr-fold-visits-by-steps
  (<= (fn-sfi-cpr-prefix-carried-fold-visits cn configs events cs es ix)
      (+ 1 (fn-sfi-cpr-prefix-carried-steps cn configs events cs es ix)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sfi-cpr-prefix-carried cn configs events cs es ix)
           :in-theory
           (e/d (fn-sfi-cpr-prefix-carried fn-sfi-cpr-prefix-carried-steps
                 fn-sfi-cpr-prefix-carried-fold-visits)
                (fn-cnode-statep fn-node-statep fn-cpr-config-firstp
                 fn-rii-cpr-apply-event fn-cpr-apply-event fn-cnode-apply-config
                 fn-cnode-record-acceptablep fn-cnode-carried-acceptablep
                 fn-cfg-recordp fn-store-event-p fn-replay-apply-record
                 fn-replay-advance-okp fn-replay-advance-txid
                 fn-rii-ix-next fn-rii-okp fn-sfi-cpr-prefix-carried-car)))))

(defthm pck-cursor-fold-visits-bounded
  (let ((out (fn-pck-cpr-resume-from r rest events ix)))
    (implies (fn-sco-pausedp (car out))
             (<= (fn-pck-cpr-resume-from-fold-visits r rest events ix)
                 (+ 3 (len events)
                    (* 2 (fn-pck-configs-consumed r (car out)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pck-cpr-fold-visits-by-steps
                            (cn (fn-sco-at 1 r)) (configs rest)
                            (cs (fn-sco-at 2 r)) (es (fn-sco-at 3 r)))
                 (:instance fn-pck-cpr-resume-from-steps-bounded))
           :in-theory
           (e/d (fn-pck-cpr-resume-from-fold-visits fn-pck-cpr-resume-from
                 fn-pck-configs-consumed fn-pck-cpr-resume-from-steps)
                (fn-sco-at fn-sco-pausedp fn-sfi-cpr-prefix-carried
                 fn-sfi-cpr-prefix-carried-car fn-sfi-cpr-prefix-carried-steps
                 fn-sfi-cpr-prefix-carried-fold-visits)))))

; KEYSTONE: no S or record-prefix term. K is amortized by
; fn-pck-publications-consume-at-most-the-configs. This count excludes the
; semantic leaves listed in the fn-fold-visits table; it is not their tariff.
(defthm fn-pck-root-extend-carried-fold-visits-bounded
  (let* ((out (fn-pck-root-extend-carried roots ix rest s delta f plen))
         (r (fn-sco-at 0 roots))
         (next (car (car out))))
    (implies (fn-sco-pausedp next)
             (<= (fn-pck-root-extend-carried-fold-visits roots ix rest s delta f plen)
                 (+ 8 (* 4 (len delta))
                    (* 2 (fn-pck-configs-consumed r next))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pck-cursor-fold-visits-bounded
                            (r (fn-sco-at 0 roots)) (events delta)))
           :in-theory
           (e/d (fn-pck-root-extend-carried fn-pck-root-extend-carried-fold-visits)
                (fn-sco-at fn-sco-pausedp fn-pck-cpr-resume-from
                 fn-pck-cpr-resume-from-fold-visits fn-pck-configs-consumed
                 fn-replay-identity-loop-fold-visits
                 fn-sco-consumer-resume-fold-visits fn-th-prefix-loop-fold-visits
                 fn-replay-identity-loop fn-sco-consumer-resume fn-th-prefix-loop)))))

(def-fold-visits-check fn-pck-config-tail)
(def-fold-visits-check fn-sfi-cpr-prefix-carried)
(def-fold-visits-check fn-pck-cpr-resume-from)
(def-fold-visits-check fn-replay-identity-loop)
(def-fold-visits-check fn-cpe-projection-replay)
(def-fold-visits-check fn-sco-consumer-resume)
(def-fold-visits-check fn-th-prefix-loop)
(def-fold-visits-check fn-pck-root-extend-carried)
