; The ordered received-FNBS replay composes (spec bp-node-machine 3.6, N16):
; replaying a prefix, then a suffix from the prefix's accumulator, is
; replaying their concatenation.  This is what lets a checkpoint of the
; accumulator stand for the rows it replaces (books/bp-node-rotation.lisp).
; First one row (the only proof that opens the fold's body), the empty
; list, then any prefix by an induction that carries the accumulator.
(in-package "ACL2")
(include-book "bp-fnbs-family-replay")
(set-verify-guards-eagerness 0)

(defthm fn-bpnr-family-replay-aux-cons
  (implies (syntaxp (not (equal rest ''nil)))
           (equal (fn-bpnf-family-replay-rows-aux
                   (cons row rest) base held handoffs prior next-arrival)
                  (let ((r (fn-bpnf-family-replay-rows-aux
                            (list row) base held handoffs prior next-arrival)))
                    (if (equal (car r) :ready)
                        (fn-bpnf-family-replay-rows-aux
                         rest base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                         (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                      r))))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize fertilize eliminate-destructors)
           :expand ((fn-bpnf-family-replay-rows-aux
                     (cons row rest) base held handoffs prior next-arrival)
                    (fn-bpnf-family-replay-rows-aux
                     (list row) base held handoffs prior next-arrival)
                    (:free (h ho p na)
                           (fn-bpnf-family-replay-rows-aux nil base h ho p na)))
           :in-theory (disable fn-bpnf-family-replay-rows-aux
                               fn-bpnf-family-replay-row-record
                               fn-bpnf-stored-record-name
                               fn-bpnf-replay-pair-afterp
                               fn-bpnf-receive-decision
                               fn-bpah-apply-delivery fn-bpnf-family-apply-at
                               fn-bpn-report-apply-delete fn-bpnp-dispatch-apply
                               fn-bpnp-attempt-apply fn-bpnp-forward-result-apply
                               fn-bpnf-conflict-apply fn-bpnp-deferral-apply
                               fn-bpnf-state
                               fn-bpnf-held-octets fn-bpn-machine-state-max-jobs
                               fn-bpn-machine-state-max-octets
                               fn-bpnf-held-bundle))))

(defthm fn-bpnr-family-replay-aux-nil
  (equal (fn-bpnf-family-replay-rows-aux nil base held handoffs prior next-arrival)
         (list :ready held handoffs prior next-arrival))
  :hints (("Goal" :expand ((fn-bpnf-family-replay-rows-aux
                            nil base held handoffs prior next-arrival))
           :in-theory (disable fn-bpnf-family-replay-rows-aux))))

(local
 (defun fn-bpnr-append-induct (prefix base held handoffs prior next-arrival)
   (if (atom prefix) (list base held handoffs prior next-arrival)
     (let ((r (fn-bpnf-family-replay-rows-aux
               (list (car prefix)) base held handoffs prior next-arrival)))
       (fn-bpnr-append-induct (cdr prefix) base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                              (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))))))

(defthm fn-bpnr-family-replay-aux-append
  (implies (true-listp prefix)
           (equal (fn-bpnf-family-replay-rows-aux
                   (append prefix suffix) base held handoffs prior next-arrival)
                  (let ((r (fn-bpnf-family-replay-rows-aux
                            prefix base held handoffs prior next-arrival)))
                    (if (equal (car r) :ready)
                        (fn-bpnf-family-replay-rows-aux
                         suffix base (fn-bpn-nth 1 r) (fn-bpn-nth 2 r)
                         (fn-bpn-nth 3 r) (fn-bpn-nth 4 r))
                      r))))
  :hints (("Goal" :induct (fn-bpnr-append-induct
                           prefix base held handoffs prior next-arrival)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (union-theories '(binary-append true-listp car-cons cdr-cons cons-car-cdr
                                        (:e fn-bpn-nth) (:e equal) (:e car)
                                        (:induction fn-bpnr-append-induct))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2"
           :use ((:instance fn-bpnr-family-replay-aux-cons
                            (row (car prefix)) (rest (cdr prefix)))
                 (:instance fn-bpnr-family-replay-aux-cons
                            (row (car prefix))
                            (rest (append (cdr prefix) suffix)))))
          ("Subgoal *1/1"
           :in-theory (union-theories '(binary-append true-listp
                                        fn-bpnr-family-replay-aux-nil
                                        (:e fn-bpn-nth) (:e equal) (:e car)
                                        car-cons cdr-cons fn-bpn-nth fn-cbor-ag-car (:e consp)
                                        (:e zp) (:e natp) (:e not))
                                      (theory 'minimal-theory)))))
