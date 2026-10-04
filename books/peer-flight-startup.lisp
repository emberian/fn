; Composition of independent peer authority with the real DEFAULT pool.
(in-package "ACL2")
(include-book "page-read-startup")
(include-book "peer-flight-reservation")

(defun fn-prstartup-protected-with-peer (profile core nursery output max-connections peer observed)
 (declare (xargs :guard t))
 (+ (fn-prstartup-protected profile core nursery output max-connections observed)
    (if (fn-pfr-policy-p peer) (nfix (fn-pfr-at 0 peer)) 0)))
(defun fn-prstartup-default-plan-with-peer
 (dynamic occupied profile core nursery cold output max-connections root workers cache-limit fd-limit peer
  observed)
 (declare (xargs :guard t))
 (cond ((not peer) (fn-prstartup-default-plan dynamic occupied profile core nursery cold output
                      max-connections root workers cache-limit fd-limit observed))
       ((not (fn-pfr-policy-p peer)) (list :refused :invalid-peer-flight-profile))
       (cold (list :refused :unpriced-complete-cold-profile))
       ((not (or (not output) (fn-orv-policy-p output)))
        (list :refused :invalid-output-resource-profile))
       (t (fn-prstartup-plan dynamic occupied
              (fn-prstartup-protected-with-peer profile core nursery output max-connections peer observed)
              root workers (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*
              cache-limit fd-limit))))

; Pool budget includes native bytes already reserved outside the heap.
; Its remaining heap allowance is exclusive of the peer heap slice.
(defun fn-prstartup-peer-protected (profile core nursery output max-connections plan observed)
 (declare (xargs :guard t))
 (+ (fn-prstartup-protected profile core nursery output max-connections observed)
    (nfix (- (nfix (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)))
             (* (fn-prstartup-decoded-workers plan)
                (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))))
(defun fn-pfr-operation-observes-p (action)
 (declare (xargs :guard t)) (eq action :run))
(defun fn-pfr-extend-operation-reservation (base action peer core observations)
 (declare (xargs :guard t))
 (if (fn-pfr-operation-observes-p action) (fn-pfr-extend-reservation base peer core observations) base))
(defun fn-prstartup-peer-grant (dynamic profile core nursery output max-connections plan peer observed)
 (declare (xargs :guard t))
 (if (not (fn-prstartup-planp plan)) (list :refused :default-pool-not-held)
   (fn-pfr-startup-grant dynamic
     (fn-prstartup-peer-protected profile core nursery output max-connections plan observed) peer)))

; Carry this exact parent capture until the retained service publishes its bank.
(defun fn-prstartup-peer-native-capture
 (dynamic profile core nursery output max-connections plan peer observed)
 (declare (xargs :guard t))
 (if (not (eq (fn-pfr-at 0 (fn-prstartup-peer-grant dynamic profile core nursery
                              output max-connections plan peer observed)) :hold)) nil
   (list dynamic
         (fn-prstartup-peer-protected profile core nursery output max-connections plan observed)
         peer (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*)))

; Revalidate the current file capture against the whole native reservation.
; A file changed after launch cannot obtain extra unfunded worker authority.
(defun fn-prstartup-peer-native-grant
 (dynamic profile core nursery output max-connections plan peer observations observed)
 (declare (xargs :guard t))
 (let ((grant (fn-prstartup-peer-grant dynamic profile core nursery output
                                        max-connections plan peer observed)))
  (if (not (eq (fn-pfr-at 0 grant) :hold)) grant
    (if (< (fn-heap-machine-octets observations)
           (fn-heap-reservation-octets (fn-heap-mb-of dynamic) core
             (fn-heap-stack-kib profile)
             (+ (fn-heap-thread-count max-connections) (nfix (fn-pfr-at 3 peer)))))
        (list :refused :peer-native-reservation-not-held)
      (list :hold (fn-prstartup-peer-native-capture dynamic profile core nursery output
                                                  max-connections plan peer observed))))))

(defun fn-prstartup-peer-native-refusal-line (grant)
 (declare (xargs :guard t))
 (case (fn-pfr-at 1 grant)
  (:peer-native-reservation-not-held "Peer flight startup refused: native worker reservation is not held.")
  (:peer-flight-pool-not-held "Peer flight startup refused: independent pool is not held.")
  (:invalid-peer-flight-profile "Peer flight startup refused: invalid resource profile.")
  (:default-pool-not-held "Peer flight startup refused: parent DEFAULT pool is not held.")
  (otherwise "Peer flight startup refused: unsupported resource allowance.")))

; The peer composition of fn-prstartup-launch-admits-owner-protected
; (cold-start, 2026-10-04; w-peer cls2/cls3 on 6107ceb56: a peer-funded
; store refused at its launcher figure).  The peer extension grows the served
; run by the peer heap over the DEFAULT figure's backing; the owner's
; protected runtime with that heap fits the grown figure.
(defthm fn-prstartup-peer-backing-holds-owner
 (implies (and (natp d1)
               (<= (fn-prstartup-launch-floor profile core observed) d1)
               (equal (fn-heap-core-file owner-core) (fn-heap-core-file core)))
          (<= (fn-heap-store-base-octets profile owner-core observed)
              (nfix (- d1 (* 2 (fn-heap-nursery-trigger
                                d1 (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-protected fn-heap-runtime-protected-octets)
                                 (fn-heap-nursery-trigger fn-heap-store-base-octets
                                  fn-prstartup-launch-floor))
          :use ((:instance fn-prstartup-launch-floor-holds-owner (dyn d1))))))

(defthm fn-prstartup-grow-holds-base
 (implies (and (natp d1) (natp b) (natp dd)
               (<= b (nfix (- d1 (* 2 (fn-heap-nursery-trigger d1 cap)))))
               (<= (fn-heap-grow-runtime-dynamic d1 extra cap) dd))
          (<= (+ b (nfix extra) (* 2 (fn-heap-nursery-trigger dd cap))) dd))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-heap-grow-runtime-dynamic)
                                 (fn-heap-with-nursery fn-heap-nursery-trigger))
          :use ((:instance fn-heap-with-nursery-monotone
                 (b1 (+ b (nfix extra)))
                 (b2 (+ (nfix (- d1 (* 2 (fn-heap-nursery-trigger d1 cap)))) (nfix extra)))
                 (nursery cap))
                (:instance fn-heap-with-nursery-holds-the-trigger
                 (d dd) (base (+ b (nfix extra))) (nursery cap))))))

; The peer extension reads the DEFAULT figure through fn-pfr-at, the DEFAULT
; lemmas speak fn-prstartup-nth: the same accessor.
(local
 (defthm fn-pfr-at-is-fn-prstartup-nth
  (equal (fn-pfr-at n x) (fn-prstartup-nth n x))
  :hints (("Goal" :in-theory (enable fn-pfr-at fn-prstartup-nth) :induct (fn-pfr-at n x))))
)

(defthm fn-prstartup-extended-figure-natp
 (implies (equal (fn-prstartup-nth 0 (fn-prstartup-extend-default-reservation
                                      base nil root workers cache-limit core observations profile observed))
                 :heap)
          (natp (fn-prstartup-nth 1 (fn-prstartup-extend-default-reservation
                                     base nil root workers cache-limit core observations profile observed))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-prstartup-extend-default-reservation)
                                 (fn-prstartup-launch-floor fn-heap-grow-runtime-dynamic
                                  fn-prstartup-required-heap fn-heap-reservation-octets
                                  fn-heap-machine-octets fn-crl-table-supportedp fn-heap-mb-of)))))

; A :heap peer extension holds a valid policy over a :heap base and grows
; the base figure by the peer heap (fn-heap-grow-runtime-dynamic).
(defthm fn-pfr-extend-reservation-heap-covers-growth
 (let ((d (fn-pfr-extend-reservation base policy core observations)))
  (implies (and policy (equal (fn-pfr-at 0 d) :heap))
           (and (equal (fn-pfr-at 0 base) :heap)
                (fn-pfr-policy-p policy)
                (natp (fn-pfr-at 1 d))
                (<= (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (fn-pfr-at 1 base)))
                                                  (fn-pfr-at 0 policy)
                                                  (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
                    (* *fn-heap-mib* (fn-pfr-at 1 d))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pfr-extend-reservation)
                                 (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-heap-reservation-octets
                                  fn-heap-machine-octets fn-pfr-policy-p))
          :use ((:instance fn-heap-mb-of-covers
                 (octets (fn-heap-grow-runtime-dynamic
                          (* *fn-heap-mib* (nfix (fn-pfr-at 1 base)))
                          (fn-pfr-at 0 policy)
                          (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))))))

; KEYSTONE: with a peer flight profile, the served-run figure the launcher
; answers (DEFAULT extension, then the peer extension) admits the launched
; owner's protected runtime plus the peer heap (fn-prstartup-protected-with-peer),
; over any image observation of the same core file, at the trigger the owner
; sets in that heap.  Scope: absent explicit cold and output policies.
(defthm fn-prstartup-peer-launch-admits-owner-protected
 (let* ((d1 (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                      core observations profile observed))
        (d2 (fn-pfr-extend-reservation d1 peer core observations))
        (dyn (* *fn-heap-mib* (fn-pfr-at 1 d2))))
  (implies (and peer
                (equal (fn-pfr-at 0 d2) :heap)
                (equal (fn-heap-core-file owner-core) (fn-heap-core-file core)))
           (<= (fn-prstartup-protected-with-peer
                profile owner-core
                (fn-heap-nursery-trigger dyn (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
                nil max-connections peer observed)
               dyn)))
 :rule-classes nil
 :hints (("Goal"
          :in-theory (e/d (fn-prstartup-protected-with-peer fn-prstartup-protected
                           fn-heap-runtime-protected-octets)
                          (fn-pfr-extend-reservation fn-prstartup-extend-default-reservation
                           fn-heap-with-nursery fn-heap-grow-runtime-dynamic
                           fn-heap-nursery-trigger fn-heap-store-base-octets fn-heap-mb-of
                           fn-prstartup-launch-floor fn-heap-reservation-octets
                           fn-heap-machine-octets fn-pfr-policy-p))
          :use ((:instance fn-prstartup-extended-figure-natp)
                (:instance fn-prstartup-extended-covers-launch-floor)
                (:instance fn-pfr-extend-reservation-heap-covers-growth
                 (base (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                                core observations profile observed))
                 (policy peer))
                (:instance fn-prstartup-peer-backing-holds-owner
                 (d1 (* *fn-heap-mib* (fn-prstartup-nth 1
                       (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                                core observations profile observed)))))
                (:instance fn-prstartup-grow-holds-base
                 (d1 (* *fn-heap-mib* (fn-prstartup-nth 1
                       (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                                core observations profile observed))))
                 (b (fn-heap-store-base-octets profile owner-core observed))
                 (extra (fn-pfr-at 0 peer))
                 (cap (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))
                 (dd (* *fn-heap-mib* (fn-pfr-at 1 (fn-pfr-extend-reservation
                       (fn-prstartup-extend-default-reservation base nil root workers cache-limit
                                                                core observations profile observed)
                       peer core observations)))))))))
