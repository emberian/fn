; Connect recovery's receipt comparison to the witnesses carried by the
; log model. A crash starts a new set of presentations.
(in-package "ACL2")
(include-book "recovery-decision-proof")
(fn2-book-layer :b)

(local (defthmd fn2-rec-witnesses-nth
 (equal (fn2-lm-state-witnesses s) (nth 8 s))))

(local (defthm fn2-rec-witnesses-of-step
 (equal (fn2-lm-state-witnesses (fn2-lm-step e s))
        (cond ((not (and (fn2-lm-state-valid s) (fn2-lm-event-allowedp e s)))
               (fn2-lm-state-witnesses s))
              ((eq (fn2-lm-event-tag e) :crash) nil)
              ((eq (fn2-lm-event-tag e) :present-frontier)
               (cons (cons (fn2-lm-event-argument e) (fn2-lm-event-extra e))
                     (fn2-lm-state-witnesses s)))
              (t (fn2-lm-state-witnesses s))))
 :hints (("Goal" :in-theory (e/d (fn2-lm-step fn2-rec-witnesses-nth)
                                 (fn2-lm-state-witnesses fn2-lm-event-allowedp
                                  fn2-lm-state-valid fn2-lm-event-tag
                                  fn2-lm-event-argument fn2-lm-event-extra))))))

(local (defthm fn2-rec-frontier-has-name
 (implies (and (eq (fn2-lm-event-tag e) :present-frontier)
               (fn2-lm-event-allowedp e s))
          (fn2-lm-event-argument e))
 :hints (("Goal" :in-theory (e/d (fn2-lm-event-allowedp)
                                 (fn2-lm-event-tag fn2-lm-event-argument))))))

(local (defthm fn2-rec-witnesses-of-update-valid
 (equal (fn2-lm-state-witnesses (update-nth 10 v s)) (fn2-lm-state-witnesses s))
 :hints (("Goal" :in-theory (e/d (fn2-rec-witnesses-nth) (fn2-lm-state-witnesses))))))

(local (in-theory (disable fn2-lm-step fn2-lm-event-allowedp fn2-lm-state-witnesses
                           fn2-lm-state-valid fn2-lm-event-tag fn2-lm-event-argument
                           fn2-lm-event-extra)))

(local (defthm fn2-rec-run-witnesses-have-names
 (implies (not (member-equal nil (strip-cars (fn2-lm-state-witnesses s))))
          (not (member-equal nil (strip-cars (fn2-lm-state-witnesses (fn2-lm-run trace s))))))
 :hints (("Goal" :induct (fn2-lm-run trace s)))))

(defthm fn2-rec-trace-witnesses-have-names
 (not (member-equal nil (strip-cars (fn2-lm-state-witnesses (fn2-lm-trace-state trace)))))
 :hints (("Goal" :use ((:instance fn2-rec-run-witnesses-have-names (s (fn2-lm-initial))))
                 :in-theory (e/d (fn2-lm-trace-state) (fn2-lm-run fn2-rec-run-witnesses-have-names)))))

(defthm fn2-rec-trace-receipt-supports-detection
 (let ((witnesses (fn2-lm-state-witnesses (fn2-lm-trace-state trace))))
  (implies (and (member-equal (cons :receipt witness) witnesses)
                (eq (nth (fn2-rec-witness-outcome assume witness (len recovered) matches)
                         *fn2-rec-witness-outcomes*) :rollback-detected))
           (and (fn2-rec-assumep assume *fn2-rec-assume-frontier*)
                (fn2-lm-conflicting-witness witnesses recovered))))
 :rule-classes nil
 :hints (("Goal" :in-theory nil
                 :use (fn2-rec-trace-witnesses-have-names
                       (:instance fn2-rec-detection-has-conflicting-receipt
                                  (witnesses (fn2-lm-state-witnesses (fn2-lm-trace-state trace))))))))

(local (defthm fn2-rec-witness-survives-suffix
 (implies (and (member-equal receipt (fn2-lm-state-witnesses s))
               (not (member-eq :crash (strip-cars suffix))))
          (member-equal receipt (fn2-lm-state-witnesses (fn2-lm-run suffix s))))
 :hints (("Goal" :induct (fn2-lm-run suffix s)
                 :in-theory (enable fn2-lm-event-tag)))))

(defthm fn2-rec-presented-receipt-survives-until-crash
 (let ((event (list :present-frontier :receipt frontier)))
  (implies (and (fn2-lm-state-valid s) (fn2-lm-event-allowedp event s)
                (not (member-eq :crash (strip-cars suffix))))
           (member-equal (cons :receipt frontier)
                         (fn2-lm-state-witnesses (fn2-lm-run (cons event suffix) s)))))
 :hints (("Goal" :expand ((fn2-lm-run (cons (list :present-frontier :receipt frontier) suffix) s))
                 :in-theory (enable fn2-lm-event-tag fn2-lm-event-argument fn2-lm-event-extra)
                 :use ((:instance fn2-rec-witness-survives-suffix
                                  (receipt (cons :receipt frontier))
                                  (s (fn2-lm-step (list :present-frontier :receipt frontier) s)))))))
