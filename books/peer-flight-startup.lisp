; Composition of independent peer authority with the real DEFAULT pool.
(in-package "ACL2")
(include-book "page-read-startup")
(include-book "peer-flight-reservation")

(defun fn-prstartup-protected-with-peer (profile core nursery output max-connections peer)
 (declare (xargs :guard t))
 (+ (fn-prstartup-protected profile core nursery output max-connections)
    (if (fn-pfr-policy-p peer) (nfix (fn-pfr-at 0 peer)) 0)))
(defun fn-prstartup-default-plan-with-peer
 (dynamic occupied profile core nursery cold output max-connections root workers cache-limit fd-limit peer)
 (declare (xargs :guard t))
 (cond ((not peer) (fn-prstartup-default-plan dynamic occupied profile core nursery cold output
                      max-connections root workers cache-limit fd-limit))
       ((not (fn-pfr-policy-p peer)) (list :refused :invalid-peer-flight-profile))
       (cold (list :refused :unpriced-complete-cold-profile))
       ((not (or (not output) (fn-orv-policy-p output)))
        (list :refused :invalid-output-resource-profile))
       (t (fn-prstartup-plan dynamic occupied
              (fn-prstartup-protected-with-peer profile core nursery output max-connections peer)
              root workers (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*
              cache-limit fd-limit))))

; Pool budget includes native bytes already reserved outside the heap.
; Its remaining heap allowance is exclusive of the peer heap slice.
(defun fn-prstartup-peer-protected (profile core nursery output max-connections plan)
 (declare (xargs :guard t))
 (+ (fn-prstartup-protected profile core nursery output max-connections)
    (nfix (- (nfix (fn-prstartup-nth 0 (fn-prstartup-nth 1 plan)))
             (* (fn-prstartup-decoded-workers plan)
                (+ (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*))))))
(defun fn-pfr-operation-observes-p (action)
 (declare (xargs :guard t)) (eq action :run))
(defun fn-pfr-extend-operation-reservation (base action peer core observations)
 (declare (xargs :guard t))
 (if (fn-pfr-operation-observes-p action) (fn-pfr-extend-reservation base peer core observations) base))
(defun fn-prstartup-peer-grant (dynamic profile core nursery output max-connections plan peer)
 (declare (xargs :guard t))
 (if (not (fn-prstartup-planp plan)) (list :refused :default-pool-not-held)
   (fn-pfr-startup-grant dynamic
     (fn-prstartup-peer-protected profile core nursery output max-connections plan) peer)))

; Carry this exact parent capture until the retained service publishes its bank.
(defun fn-prstartup-peer-native-capture
 (dynamic profile core nursery output max-connections plan peer)
 (declare (xargs :guard t))
 (if (not (eq (fn-pfr-at 0 (fn-prstartup-peer-grant dynamic profile core nursery
                              output max-connections plan peer)) :hold)) nil
   (list dynamic
         (fn-prstartup-peer-protected profile core nursery output max-connections plan)
         peer (fn-heap-stack-octets profile) *fn-heap-thread-runtime-octets*)))

; Revalidate the current file capture against the whole native reservation.
; A file changed after launch cannot obtain extra unfunded worker authority.
(defun fn-prstartup-peer-native-grant
 (dynamic profile core nursery output max-connections plan peer observations)
 (declare (xargs :guard t))
 (let ((grant (fn-prstartup-peer-grant dynamic profile core nursery output
                                        max-connections plan peer)))
  (if (not (eq (fn-pfr-at 0 grant) :hold)) grant
    (if (< (fn-heap-machine-octets observations)
           (fn-heap-reservation-octets (fn-heap-mb-of dynamic) core
             (fn-heap-stack-kib profile)
             (+ (fn-heap-thread-count max-connections) (nfix (fn-pfr-at 3 peer)))))
        (list :refused :peer-native-reservation-not-held)
      (list :hold (fn-prstartup-peer-native-capture dynamic profile core nursery output
                                                  max-connections plan peer))))))

(defun fn-prstartup-peer-native-refusal-line (grant)
 (declare (xargs :guard t))
 (case (fn-pfr-at 1 grant)
  (:peer-native-reservation-not-held "Peer flight startup refused: native worker reservation is not held.")
  (:peer-flight-pool-not-held "Peer flight startup refused: independent pool is not held.")
  (:invalid-peer-flight-profile "Peer flight startup refused: invalid resource profile.")
  (:default-pool-not-held "Peer flight startup refused: parent DEFAULT pool is not held.")
  (otherwise "Peer flight startup refused: unsupported resource allowance.")))
