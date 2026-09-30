; Proof-only complete fixed5 relation. No serving lookup or publication scans.
(in-package "ACL2")
(include-book "consumer-progress-carried")
(include-book "consumer-account-metadata-step")
(include-book "consumer-config-metadata")

(defun fn-cpmm-annotation (cp)
 (declare (xargs :guard t :verify-guards nil))
 (fn-cpm-metadata5 (fn-caam-annotation cp)
                    (fn-caam-list-annotation (fn-cp-nth 5 cp))))

(local
 (defthm fn-cpmm-account-annotation-is-fixed-four
  (equal (list (fn-cp-nth 0 (fn-caam-annotation cp))
               (fn-cp-nth 1 (fn-caam-annotation cp))
               (fn-cp-nth 2 (fn-caam-annotation cp))
               (fn-cp-nth 3 (fn-caam-annotation cp)))
         (fn-caam-annotation cp))
  :hints (("Goal" :in-theory
    (e/d (fn-caam-annotation fn-cp-nth)
         (fn-caam-field-annotation fn-caam-list-annotation
          fn-caam-preparation-annotation))))))

(local
 (defthm fn-cpmm-packed-annotation-is-fixed-five
  (fn-cpm-metadatap (fn-cpm-metadata5 (fn-caam-annotation cp) entry-metadata))
  :hints (("Goal" :in-theory
    (e/d (fn-cpm-metadatap fn-cpm-metadata5 fn-caam-annotation fn-cp-nth)
         (fn-caam-field-annotation fn-caam-list-annotation
          fn-caam-preparation-annotation))))))

(local
 (defthm fn-cpmm-projected-account-annotation
  (equal (fn-cpm-account4 (fn-cpmm-annotation cp)) (fn-caam-annotation cp))
  :hints (("Goal" :in-theory
    (e/d (fn-cpm-account4 fn-cpm-metadata5 fn-cpmm-annotation
          fn-caam-annotation fn-cp-nth)
         (fn-caam-field-annotation fn-caam-list-annotation
          fn-caam-preparation-annotation))))))

(local
 (defthm fn-cpmm-annotation-is-fixed-five
  (fn-cpm-metadatap (fn-cpmm-annotation cp))
  :hints (("Goal" :in-theory
    (e/d (fn-cpm-metadatap fn-cpmm-annotation fn-cpm-metadata5
          fn-caam-annotation fn-cp-nth)
         (fn-caam-field-annotation fn-caam-list-annotation
          fn-caam-preparation-annotation))))))

(local
 (defthm fn-cpmm-row-plan-never-ok-by-definition
   (not (equal (car (fn-caa-row-plan a event op)) :ok))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-row-plan fn-cp-nth)
                 (fn-caa-row-credential fn-auth-credp fn-caa-row-descriptor
                  fn-cp-account-creation fn-cp-creation-coordinate
                  fn-caa-name-lessp nfix))))))
(local
 (defthm fn-cpmm-tombstone-plan-never-ok-by-definition
   (not (equal (car (fn-caa-tombstone-plan a event op)) :ok))
   :hints (("Goal" :in-theory
            (e/d (fn-caa-tombstone-plan fn-cp-nth)
                 (fn-caa-row-credential fn-auth-credp fn-caa-row-descriptor
                  fn-cp-account-creation fn-cp-creation-coordinate
                  fn-caa-name-lessp nfix))))))

(local
 (defthm fn-cpmm-authority-success-preserves-entries
  (implies (equal (car (fn-caa-step cp event)) :ok)
           (equal (fn-cp-nth 5 (fn-cp-nth 1 (fn-caa-step cp event)))
                  (fn-cp-nth 5 cp)))
  :hints (("Goal" :in-theory
    (e/d (fn-caa-step fn-caa-begin fn-caa-row fn-caa-tombstone
          fn-caa-seal fn-caa-prepare fn-caa-fence fn-caa-stage-selected
          fn-caa-stage-indexed fn-caa-success fn-cp-state-carry fn-cp-nth)
         (fn-caa-row-plan fn-caa-tombstone-plan fn-caa-matching-pendingp
          fn-caa-namespace fn-caa-authority-pending fn-caa-count-digest-matchp
          fn-caa-preparation fn-caa-root fn-caa-pending fn-cac-eventp
          fn-cp-uintp fn-cp-authority-namespacep fn-cai-get-octets fn-cai-put-octets
          fn-sha256 fn-cac-encode))))))

(defthm fn-cpmm-initial-establishes-fixed-five-metadata
 (implies (and (fn-scc-octet-listp history) (equal hn (len history))
               (fn-scc-octet-listp incarnation) (equal in (len incarnation))
               (integerp frontier))
  (equal (mv-nth 1 (fn-cpm-initial history incarnation frontier hn in))
         (fn-cpmm-annotation
          (mv-nth 0 (fn-cpm-initial history incarnation frontier hn in)))))
 :hints (("Goal"
  :use ((:instance fn-caam-initial-establishes-full-metadata))
  :in-theory (e/d (fn-cpm-initial fn-cpmm-annotation fn-caam-correspondsp
                   fn-cp-initial fn-cp-state fn-cp-state-carry fn-cp-nth)
                  (fn-caac-initial fn-caam-annotation fn-cpm-metadata5
                   fn-caam-initial-establishes-full-metadata)))))

(defthm fn-cpmm-actual-authority-step-maintains-fixed-five-metadata
 (let* ((cp (fn-cp-state-carry h i frontier next entries a))
        (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (kind (fn-cp-nth 0 (fn-cp-nth 4 event)))
        (one (mv-nth 0 (fn-cpm-authority-step cp event metadata))))
  (implies
   (and (fn-caam-authority-sizep a)
        (equal metadata (fn-cpmm-annotation cp))
        (implies (member-eq kind '(:authority-row :authority-tombstone))
         (and (fn-caps-merge-relp p installed)
              (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))))
        (implies (equal kind :authority-prepare) (fn-caar-preparation-relp prep))
        (equal (car one) :ok))
   (equal (mv-nth 1 (fn-cpm-authority-step cp event metadata))
          (fn-cpmm-annotation (fn-cp-nth 1 one)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-cams-actual-authority-step-maintains-full-metadata
           (history h) (incarnation i) (next-epoch next)
           (metadata (fn-cpm-account4 metadata)))
        (:instance fn-cpmm-authority-success-preserves-entries
           (cp (fn-cp-state-carry h i frontier next entries a)))
        (:instance fn-cpmm-account-annotation-is-fixed-four
           (cp (fn-cp-state-carry h i frontier next entries a))))
  :in-theory
   (e/d (fn-cpm-authority-step fn-cpmm-annotation fn-cpm-metadata5
         fn-cpm-account4 fn-cp-state-carry fn-cp-nth fn-caam-correspondsp)
        (fn-caac-step fn-caa-step fn-cpm-metadatap
         fn-caam-annotation fn-caam-authority-sizep fn-caam-list-annotation
         fn-caps-merge-relp fn-cais-triep fn-caar-preparation-relp
         fn-cpmm-account-annotation-is-fixed-four)))))

(defthm fn-cpmm-config-preflight-maintains-fixed-five-metadata
 (let* ((cp (fn-cp-state-carry h i frontier next entries a))
        (approved (fn-cpm-config-preflight cp metadata)))
  (implies (and (integerp frontier) (fn-caam-authority-sizep a)
                (equal metadata (fn-cpmm-annotation cp))
                (equal (car approved) :ok))
   (equal (fn-cp-nth 2 approved)
          (fn-cpmm-annotation (fn-cp-nth 1 approved)))))
 :hints (("Goal"
  :use ((:instance fn-ccam-actual-config-preflight-maintains-full-metadata
                  (metadata (fn-cpm-account4 metadata)))
        (:instance fn-cpmm-account-annotation-is-fixed-four
                  (cp (fn-cp-state-carry h i frontier next entries a))))
  :in-theory
   (e/d (fn-cpm-config-preflight fn-cpmm-annotation fn-cpm-metadata5
         fn-cpm-account4 fn-cca-preflight fn-carv-semantic-step
         fn-carv-revision-state fn-carv-state-with-authority
         fn-cp-state-carry fn-cp-nth fn-caam-correspondsp)
        (fn-caam-annotation fn-caam-field-annotation fn-caam-list-annotation
         fn-caam-preparation-annotation fn-cpm-metadatap fn-caac-metadata
         fn-caam-authority-sizep fn-cp-uintp
         fn-cpmm-account-annotation-is-fixed-four)))))

(in-theory (disable fn-cpmm-annotation))
