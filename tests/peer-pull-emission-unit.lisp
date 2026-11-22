; Run the same core emitter as the served callback, using the assembled
; operation faces. A missing phase or observation must fail this gate even
; when the remaining declarations generate valid functions.
(in-package "ACL2")
(include-book "../books/peer-pull-operations")

(defcost-faces fn2-peer-pull)
(make-event
 (mv-let (err events) (fn2-arms-events 'fn2-peer-pull :core (w state))
   (if err (er soft 'fn2-peer-pull-emission "~@0" err)
     (let* ((contract (cadr (cadddr (cadr events))))
            (runs (strip-cars (fn2-decl-get :continuations contract)))
            (obs (strip-cars (fn2-decl-get :observes contract)))
            (states (fn2-machine-declared 'fn2-peer-pull :states (w state)))
            (observations (strip-cars (fn2-machine-declared 'fn2-peer-pull :observes (w state)))))
       (if (and (consp states) (consp observations)
                (no-duplicatesp-eq runs) (no-duplicatesp-eq obs)
                (subsetp-eq states runs) (subsetp-eq runs states)
                (subsetp-eq observations obs) (subsetp-eq obs observations))
           (value '(value-triple :all-peer-pull-arms-emitted))
         (er soft 'fn2-peer-pull-emission
             "Expected states ~x0 and observations ~x1. Emitted ~x2 and ~x3."
             states observations runs obs))))))
