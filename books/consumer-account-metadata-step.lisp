; Whole actual authority interpreter boundary. Proof-only state relations
; below describe maintained inputs; serving never executes their scans.
(in-package "ACL2")
(include-book "consumer-account-metadata-planner")

(local
 (defthm fn-cams-octet-predicates-agree
   (equal (fn-scc-octet-listp xs) (fn-cbor-octet-listp xs))
   :hints (("Goal" :induct (fn-scc-octet-listp xs)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-cams-row-plan-cursor-carry-unfolds
  (let* ((old (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
         (plan (fn-caa-row-plan a event op)))
   (implies (equal (car plan) :stage)
    (equal (fn-cp-nth 3 plan) (if (fn-cp-nth 4 plan) (cdr old) old))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-row-plan fn-cp-nth)
                (fn-caa-row-credential fn-auth-credp fn-caa-row-descriptor
                 fn-cp-account-creation fn-cp-creation-coordinate fn-caa-name-lessp))))))
(local
 (defthm fn-cams-tombstone-plan-cursor-carry-unfolds
  (let* ((old (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
         (plan (fn-caa-tombstone-plan a event op)))
   (implies (equal (car plan) :stage)
    (equal (fn-cp-nth 3 plan) (if (fn-cp-nth 4 plan) (cdr old) old))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-tombstone-plan fn-cp-nth)
                (fn-cp-creation-coordinate fn-caa-name-lessp))))))
(local
 (defthm fn-cams-begin-codec-size-domain
   (implies (and (fn-cac-operationp op) (equal (fn-cp-nth 0 op) :authority-begin))
            (and (fn-scc-octet-listp (fn-cp-nth 1 op))
                 (integerp (fn-cp-nth 4 op))))
   :hints (("Goal" :in-theory
            (enable fn-cac-operationp fn-cac-kinds fn-cac-fields-validp
                    fn-cac-fieldp fn-cp-nth fn-cac-u64p fn-scc-octet-listp
                    fn-scc-octetp fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-cams-finish-first-result-is-decision-by-definition
   (equal (mv-nth 0 (fn-caac-finish one metadata am pm root-carry)) one)
   :hints (("Goal" :in-theory
            (e/d (fn-caac-finish fn-cp-nth) (fn-caac-metadata))))))

(local
 (defthm fn-cams-row-plan-never-ok-by-definition
   (not (equal (car (fn-caa-row-plan a event op)) :ok))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-row-plan fn-cp-nth)
                 (fn-caa-row-credential fn-auth-credp fn-caa-row-descriptor
                  fn-cp-account-creation fn-cp-creation-coordinate
                  fn-caa-name-lessp nfix))))))
(local
 (defthm fn-cams-tombstone-plan-never-ok-by-definition
   (not (equal (car (fn-caa-tombstone-plan a event op)) :ok))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-tombstone-plan fn-cp-nth)
                 (fn-caa-row-credential fn-auth-credp fn-caa-row-descriptor
                  fn-cp-account-creation fn-cp-creation-coordinate
                  fn-caa-name-lessp nfix))))))
(local
 (defthm fn-cams-present-size-pending-is-consp
   (implies (and (fn-caam-authority-sizep a) (fn-cp-nth 5 a))
            (consp (fn-cp-nth 5 a)))
   :hints (("Goal" :in-theory
            (e/d (fn-caam-authority-sizep fn-caam-pending-sizep)
                 (fn-cp-nth fn-caam-preparation-sizep))))))

(local
 (defthm fn-cams-present-size-pending-has-namespace
   (implies (and (fn-caam-authority-sizep a) (consp (fn-cp-nth 5 a)))
            (fn-cp-authority-namespacep
             (fn-cp-nth 6 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
   :hints (("Goal" :in-theory
            (e/d (fn-caam-authority-sizep fn-caam-pending-sizep
                  fn-caam-preparation-sizep fn-cp-authority-namespacep)
                 (fn-cp-nth))))))

(local
 (defthm fn-cams-begin-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))

                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-begin)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-caam-begin-maintains-full-metadata (op (fn-cp-nth 4 event)))
 (:instance fn-cams-begin-codec-size-domain (op (fn-cp-nth 4 event))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-row-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))
                 (fn-caps-merge-relp p installed)
 (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))

                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-row)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-campl-actual-row-plan-establishes-stage-carries (op (fn-cp-nth 4 event)))
 (:instance fn-cams-row-plan-cursor-carry-unfolds (op (fn-cp-nth 4 event)))
 (:instance fn-caam-selected-stage-maintains-full-metadata
  (row (fn-cp-nth 1 (fn-caa-row-plan a event (fn-cp-nth 4 event)))) (credential (fn-cp-nth 2 (fn-caa-row-plan a event (fn-cp-nth 4 event))))
  (old-rest (fn-cp-nth 3 (fn-caa-row-plan a event (fn-cp-nth 4 event)))) (old-advancedp (fn-cp-nth 4 (fn-caa-row-plan a event (fn-cp-nth 4 event))))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-tombstone-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))
                 (fn-caps-merge-relp p installed)
 (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))
                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-tombstone)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-campl-actual-tombstone-plan-establishes-stage-carries (op (fn-cp-nth 4 event)))
 (:instance fn-cams-tombstone-plan-cursor-carry-unfolds (op (fn-cp-nth 4 event)))
 (:instance fn-caam-selected-stage-maintains-full-metadata
  (row (fn-cp-nth 1 (fn-caa-tombstone-plan a event (fn-cp-nth 4 event)))) (credential (fn-cp-nth 2 (fn-caa-tombstone-plan a event (fn-cp-nth 4 event))))
  (old-rest (fn-cp-nth 3 (fn-caa-tombstone-plan a event (fn-cp-nth 4 event)))) (old-advancedp (fn-cp-nth 4 (fn-caa-tombstone-plan a event (fn-cp-nth 4 event))))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-seal-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))

                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-seal)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-caam-seal-maintains-full-metadata (op (fn-cp-nth 4 event))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-prepare-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))
                 (fn-caar-preparation-relp prep)
                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-prepare)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-caam-prepare-maintains-full-metadata)
 (:instance fn-campl-actual-prepare-establishes-credential-carry (s (fn-cp-state-carry history incarnation frontier next-epoch entries a))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-fence-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))

                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-fence)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-caam-fence-maintains-full-metadata-and-root (op (fn-cp-nth 4 event))))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-discard-case-full-metadata
  (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
         (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
   (implies (and (fn-caam-authority-sizep a)
                 (equal metadata (fn-caam-annotation s))

                 (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-discard)
                 (equal (car one) :ok))
            (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-caam-discard-maintains-full-metadata))
           :in-theory
           (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp
                 fn-caa-matching-pendingp)
                (fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
 fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
 fn-caar-preparation-relp fn-caac-stage-selected fn-caac-finish
 fn-caa-row-plan fn-caa-tombstone-plan fn-caa-begin fn-caa-seal
 fn-caa-fence fn-caa-prepare fn-caa-success fn-caa-authority-pending
 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
 fn-caac-row-carry fn-caac-credential-carry fn-caac-spine
 fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary fn-cac-operationp
 fn-cams-begin-codec-size-domain fn-cams-row-plan-cursor-carry-unfolds
 fn-cams-tombstone-plan-cursor-carry-unfolds
 fn-campl-actual-row-plan-establishes-stage-carries
 fn-campl-actual-tombstone-plan-establishes-stage-carries
 fn-campl-actual-prepare-establishes-credential-carry
 nfix fn-cp-uintp))))))

(local
 (defthm fn-cams-success-has-supported-operation
  (implies (equal (car (mv-nth 0 (fn-caac-step s event metadata))) :ok)
           (member-equal (fn-cp-nth 0 (fn-cp-nth 4 event))
             '(:authority-begin :authority-row :authority-tombstone :authority-seal
               :authority-prepare :authority-fence :authority-discard)))
  :hints (("Goal" :in-theory
           (e/d (fn-caac-step fn-cp-nth member-equal)
                (fn-caac-step-is-logical-authority-step fn-cac-eventp fn-cp-uintp fn-caa-matching-pendingp
                 fn-caac-finish fn-caac-stage-selected fn-caa-row-plan
                 fn-caa-tombstone-plan fn-caa-begin fn-caa-seal fn-caa-prepare
                 fn-caa-fence fn-caa-success fn-caa-authority-pending
                 fn-caac-root-carry fn-caac-list-cons fn-caac-credential-value-carry
                 fn-caac-atom fn-cait-size fn-scs-cons nfix))))))

(defthm fn-cams-actual-authority-step-maintains-full-metadata
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (op (fn-cp-nth 4 event)) (kind (fn-cp-nth 0 op))
        (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
  (implies
   (and (fn-caam-authority-sizep a)
        (equal metadata (fn-caam-annotation s))
        (implies (member-eq kind '(:authority-row :authority-tombstone))
          (and (fn-caps-merge-relp p installed)
               (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))))
        (implies (equal kind :authority-prepare) (fn-caar-preparation-relp prep))
        (equal (car one) :ok))
   (fn-caam-correspondsp (fn-cp-nth 1 one) (mv-nth 1 result))))
 :hints (("Goal"
  :use ((:instance fn-cams-begin-case-full-metadata) (:instance fn-cams-row-case-full-metadata) (:instance fn-cams-tombstone-case-full-metadata) (:instance fn-cams-seal-case-full-metadata) (:instance fn-cams-prepare-case-full-metadata) (:instance fn-cams-fence-case-full-metadata) (:instance fn-cams-discard-case-full-metadata)
        (:instance fn-cams-success-has-supported-operation
         (s (fn-cp-state-carry history incarnation frontier next-epoch entries a))))
  :in-theory
  (e/d (member-equal fn-cp-state-carry fn-cp-nth)
       (fn-caac-step fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
        fn-caps-merge-relp fn-cais-triep fn-cp-authority-namespacep
        fn-caar-preparation-relp fn-cams-success-has-supported-operation)))))

(defthm fn-cams-actual-fence-publishes-exact-root-carry
 (let* ((s (fn-cp-state-carry history incarnation frontier next-epoch entries a))
        (result (fn-caac-step s event metadata)) (one (mv-nth 0 result)))
  (implies (and (fn-caam-authority-sizep a)
                (equal metadata (fn-caam-annotation s))
                (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-fence)
                (equal (car one) :ok))
           (equal (mv-nth 2 result) (fn-scs-summary (fn-cp-nth 2 one)))))
 :hints (("Goal"
  :use ((:instance fn-caam-fence-maintains-full-metadata-and-root (op (fn-cp-nth 4 event))))
  :in-theory
  (e/d (fn-caac-step fn-cp-state-carry fn-cp-nth fn-cac-eventp fn-caa-matching-pendingp
        fn-caac-finish)
       (fn-caac-step-is-logical-authority-step fn-caac-metadata
        fn-caam-correspondsp fn-caam-annotation fn-caam-authority-sizep
        fn-caac-stage-selected fn-caa-row-plan fn-caa-tombstone-plan
        fn-caa-begin fn-caa-seal fn-caa-fence fn-caa-prepare fn-caa-success
        fn-caa-authority-pending fn-caac-root-carry fn-caac-list-cons
        fn-caac-credential-value-carry fn-caac-row-carry fn-caac-credential-carry
        fn-caac-spine fn-caac-atom fn-cait-size fn-scs-cons fn-scs-summary
        fn-cac-operationp nfix fn-cp-uintp)))))
