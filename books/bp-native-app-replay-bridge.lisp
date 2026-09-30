; PKT-413: the receiver projection of the actual FNRJ install replay.
(in-package "ACL2")
(include-book "bp-native-app")
(local (include-book "bp-receiver-state-invariants"))

; This describes the context-first journal sublanguage.  It is a proof
; hypothesis, never a new scan on the served path.  Transit intent/context
; records have different semantics and are deliberately excluded.
(defun fn-bpaj-receiver-only-recordsp (records)
  (declare (xargs :guard t :measure (acl2-count records)))
  (if (consp records)
      (and (not (equal (if (consp (car records)) (caar records) nil)
                       :request-transit-intent))
           (not (equal (if (consp (car records)) (caar records) nil)
                       :request-transit-context))
           (fn-bpaj-receiver-only-recordsp (cdr records)))
    t))

; The host fn-bprj-install tests the result flag and installs the receiver
; of the result's joined state.  Preserve BOTH observations, including the
; last state on refusal; projecting the outer result as a state is wrong.
(defun fn-bpaj-receiver-result (answer)
  (declare (xargs :guard t))
  (let ((joined (if (and (consp answer) (consp (cdr answer)))
                    (cadr answer) nil)))
    (list (if (consp answer) (car answer) nil)
          (if (consp joined) (car joined) nil))))
(verify-guards fn-bpaj-receiver-only-recordsp)
(verify-guards fn-bpaj-receiver-result)

(local
 (defthm fn-bpaj-context-first-statep
   (equal (fn-bpaj-statep (fn-bpaj-make-state st nil nil nil))
          (fn-bpr-statep st))
   :hints (("Goal" :in-theory (enable fn-bpaj-statep
                                    fn-bpaj-intent-listp
                                    fn-bpaj-fact-listp)))))

(local
 (defthm fn-bpaj-context-first-apply-by-definition
   (implies
    (and (fn-bpr-statep st)
         (not (equal (fn-bpaj-nth 0 r) :request-transit-intent))
         (not (equal (fn-bpaj-nth 0 r) :request-transit-context)))
    (equal
     (fn-bpaj-apply-record (fn-bpaj-make-state st nil nil nil) store r fn-arena)
     (list (car (fn-bprr-apply-record st store r fn-arena))
           (fn-bpaj-make-state
            (fn-bprr-nth 1 (fn-bprr-apply-record st store r fn-arena))
            nil nil nil))))
   :hints (("Goal"
            :use ((:instance fn-bpaj-context-first-statep))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn-bpaj-apply-record fn-bprr-apply-record
               fn-bpaj-make-state fn-bpaj-receiver fn-bpaj-intents
               fn-bpaj-facts fn-bpaj-strictp fn-bpaj-nth fn-bprr-nth
               car-cons cdr-cons (:executable-counterpart zp)))))))

(local
 (defthm fn-bpaj-context-first-replay-rest
   (implies (and (fn-bpr-statep st)
                 (fn-bpaj-receiver-only-recordsp records))
            (equal
             (fn-bpaj-replay-rest
              (fn-bpaj-make-state st nil nil nil) store records fn-arena)
             (list (car (fn-bprr-replay-rest st store records fn-arena))
                   (fn-bpaj-make-state
                    (fn-bprr-nth 1
                                 (fn-bprr-replay-rest st store records fn-arena))
                    nil nil nil))))
   :hints (("Goal"
            :induct (fn-bprr-replay-rest st store records fn-arena)
            :expand ((fn-bpaj-replay-rest
                      (fn-bpaj-make-state st nil nil nil) store records fn-arena))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(fn-bpaj-replay-rest fn-bprr-replay-rest
               fn-bpaj-receiver-only-recordsp
               fn-bpaj-context-first-apply-by-definition
               fn-bprr-apply-record-preserves-statep
               fn-bpaj-nth fn-bprr-result-state
               car-cons cdr-cons default-car default-cdr endp (:executable-counterpart zp))))
           ("Subgoal *1/3" :use ((:instance fn-bpaj-context-first-apply-by-definition
                                           (r (car records)))))
           ("Subgoal *1/2" :use ((:instance fn-bpaj-context-first-apply-by-definition
                                           (r (car records))))))))

(local
 (defthm fn-bpaj-receiver-replay-result-pair
   (equal (list (car (fn-bprr-replay-rest st store records fn-arena))
                (fn-bprr-nth 1 (fn-bprr-replay-rest st store records fn-arena)))
          (fn-bprr-replay-rest st store records fn-arena))
   :hints (("Goal" :induct (fn-bprr-replay-rest st store records fn-arena)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-bprr-replay-rest fn-bprr-result-state
                           car-cons cdr-cons))))))

(defthm fn-bpaj-replay-receiver-is-receiver-replay
  (implies (fn-bpaj-receiver-only-recordsp records)
           (equal (fn-bpaj-receiver-result
                   (fn-bpaj-replay store records fn-arena))
                  (fn-bprr-replay store records fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-bpaj-context-first-replay-rest
                            (st (fn-bpr-initial-state (fn-bprr-config (car records))))
                            (records (cdr records))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-bpaj-replay fn-bprr-replay fn-bpaj-receiver-result
              fn-bpaj-receiver-only-recordsp fn-bpaj-make-state
              fn-bpaj-receiver-replay-result-pair fn-bprr-result-state
              car-cons cdr-cons default-car default-cdr endp)))))

(local
 (defthm fn-bpaj-invalid-receiver-apply-by-definition
   (implies (not (fn-bpr-statep st))
            (equal (fn-bprr-apply-record st store r fn-arena) (list nil st)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-bprr-apply-record fn-bpr-accept-request
               fn-bpr-prepare-receipt fn-bpr-commit-receipt
               car-cons cdr-cons))))))

(local
 (defthm fn-bpaj-invalid-receiver-replay-by-definition
   (implies (not (fn-bpr-statep st))
            (equal (fn-bprr-replay-rest st store records fn-arena)
                   (list (if (consp records) nil t) st)))
   :hints (("Goal" :expand ((fn-bprr-replay-rest st store records fn-arena))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-bpaj-invalid-receiver-apply-by-definition
                           endp car-cons cdr-cons))))))

(local
 (defthm fn-bpaj-invalid-context-first-replay-by-definition
   (implies (not (fn-bpr-statep st))
            (equal (fn-bpaj-replay-rest
                    (fn-bpaj-make-state st nil nil nil) store records fn-arena)
                   (list (if (consp records) nil t)
                         (fn-bpaj-make-state st nil nil nil))))
   :hints (("Goal"
            :expand ((fn-bpaj-replay-rest
                      (fn-bpaj-make-state st nil nil nil) store records fn-arena))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-bpaj-context-first-statep fn-bpaj-apply-record
                           endp car-cons cdr-cons))))))

; A joined state in the context-first phase, including malformed receiver
; states (both interpreters refuse them). This finite-prefix proof domain
; is not checked by the host. Real transit intent switches out of it.
(defun fn-bpaj-context-firstp (joined)
  (declare (xargs :guard t))
  (equal joined (list (if (consp joined) (car joined) nil) nil nil nil)))
(verify-guards fn-bpaj-context-firstp)

(defthm fn-bpaj-replay-rest-receiver-is-receiver-replay-rest
  (implies (and (fn-bpaj-context-firstp joined)
                (fn-bpaj-receiver-only-recordsp records))
           (equal (fn-bpaj-receiver-result
                   (fn-bpaj-replay-rest joined store records fn-arena))
                  (fn-bprr-replay-rest (fn-bpaj-receiver joined)
                                       store records fn-arena)))
  :hints (("Goal"
           :cases ((fn-bpr-statep (fn-bpaj-receiver joined)))
           :use ((:instance fn-bpaj-context-first-replay-rest
                            (st (fn-bpaj-receiver joined)))
                 (:instance fn-bpaj-invalid-receiver-replay-by-definition
                            (st (fn-bpaj-receiver joined)))
                 (:instance fn-bpaj-invalid-context-first-replay-by-definition
                            (st (fn-bpaj-receiver joined))))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-bpaj-context-firstp fn-bpaj-make-state
              fn-bpaj-receiver-result fn-bpaj-receiver fn-bpaj-nth
              fn-bpaj-receiver-replay-result-pair fn-bprr-result-state
              car-cons cdr-cons default-car default-cdr
              (:executable-counterpart zp))))))
(in-theory (disable fn-bpaj-context-firstp))

(in-theory (disable fn-bpaj-receiver-only-recordsp fn-bpaj-receiver-result))
