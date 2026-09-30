; Join actual bounded account selection to the same-pass size producer.
; Proof-only relation projections are never called on served paths.
(in-package "ACL2")
(include-book "consumer-account-metadata-transition")
(include-book "consumer-account-planner-stage-relation")

(local
 (defthm fn-campl-octet-predicates-agree
   (equal (fn-scc-octet-listp xs) (fn-cbor-octet-listp xs))
   :hints (("Goal" :induct (fn-scc-octet-listp xs)
            :in-theory (enable fn-scc-octet-listp fn-scc-octetp
                               fn-cbor-octet-listp fn-cbor-octetp)))))
(local
 (defthm fn-campl-proper-empty-by-length
   (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
   :hints (("Goal" :induct (len x)))
   :rule-classes nil))
(local
 (defthm fn-campl-five-field-reconstruction
   (implies (and (true-listp x) (equal (len x) 5))
            (equal (list (car x) (cadr x) (caddr x) (cadddr x) (car (cddddr x))) x))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-campl-proper-empty-by-length (x (cdr (cddddr x)))))
            :in-theory (enable len true-listp)))))
(local
 (defthm fn-campl-credential-descriptor-fields-valid
   (implies (fn-auth-credp credential)
     (fn-cac-fields-validp
      (list (fn-auth-cred-principal credential)
            (fn-authsec-ver-salt (fn-auth-cred-secret credential))
            (fn-authsec-ver-digest (fn-auth-cred-secret credential))
            (fn-authsec-ver-stored-key (fn-auth-cred-secret credential))
            (fn-authsec-ver-server-key (fn-auth-cred-secret credential))
            (if (fn-auth-cred-postingp credential) 1 0))
      '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag)))
   :hints (("Goal" :in-theory
            (e/d (fn-auth-credp fn-auth-cred-shapep fn-prin-idp fn-digest-octetsp
                  fn-authsec-verifierp fn-authsec-saltp fn-authsec-32p
                  fn-cac-fields-validp fn-cac-fieldp
                  fn-auth-cred-principal fn-auth-cred-secret fn-auth-cred-postingp
                  fn-authsec-ver-salt fn-authsec-ver-digest
                  fn-authsec-ver-stored-key fn-authsec-ver-server-key
                  fn-inj-nth fn-inj-car fn-inj-cdr)
                 (fn-cbor-octet-listp))))))
(local
 (defthm fn-campl-credential-descriptor-size
   (implies (fn-auth-credp credential)
            (and (fn-scc-octet-listp (fn-caar-credential-descriptor credential))
                 (equal (len (fn-caar-credential-descriptor credential)) 145)))
   :hints (("Goal"
            :use ((:instance fn-campl-credential-descriptor-fields-valid)
                  (:instance fn-cac-fields-encoded-are-octets
                   (values (list (fn-auth-cred-principal credential)
                            (fn-authsec-ver-salt (fn-auth-cred-secret credential))
                            (fn-authsec-ver-digest (fn-auth-cred-secret credential))
                            (fn-authsec-ver-stored-key (fn-auth-cred-secret credential))
                            (fn-authsec-ver-server-key (fn-auth-cred-secret credential))
                            (if (fn-auth-cred-postingp credential) 1 0)))
                   (kinds '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag)))
                  (:instance fn-cac-fields-charge-is-encoded-length
                   (values (list (fn-auth-cred-principal credential)
                            (fn-authsec-ver-salt (fn-auth-cred-secret credential))
                            (fn-authsec-ver-digest (fn-auth-cred-secret credential))
                            (fn-authsec-ver-stored-key (fn-auth-cred-secret credential))
                            (fn-authsec-ver-server-key (fn-auth-cred-secret credential))
                            (if (fn-auth-cred-postingp credential) 1 0)))
                   (kinds '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag))))
            :in-theory
            (e/d (fn-caar-credential-descriptor fn-cac-fields-charge fn-cac-field-width)
                 (fn-campl-credential-descriptor-fields-valid fn-cac-fields-validp
                  fn-cac-fields-encode fn-cac-fields-charge-is-encoded-length
                  fn-cac-fields-encoded-are-octets fn-cbor-octet-listp))))))

(defthm fn-campl-binding-establishes-exact-row-carry
  (implies (fn-caar-bindingp row (list :account-binding row credential) watermark)
           (equal (fn-caac-row-carry row) (fn-scs-summary row)))
  :hints (("Goal"
           :use ((:instance fn-campl-five-field-reconstruction (x row))
                 (:instance fn-campl-credential-descriptor-size)
                 (:instance fn-caac-row-constructor-carry-is-exact
                  (name (fn-cp-nth 1 row)) (token (fn-cp-nth 2 row))
                  (live (fn-cp-nth 3 row)) (descriptor (fn-cp-nth 4 row))))
           :in-theory
           (e/d (fn-caar-bindingp fn-cp-authority-rowp fn-cp-account-creationp fn-cp-nth)
                (fn-caac-row-carry fn-scs-summary fn-caar-credential-descriptor
                 fn-campl-credential-descriptor-size
                 fn-scc-octet-listp fn-cbor-octet-listp
                 fn-auth-credp fn-cai-namep fn-cp-creation-coordinate)))))

(local
 (defthm fn-campl-operation-credential-carry-agrees
   (equal (fn-caac-credential-carry op)
          (fn-caac-credential-value-carry (fn-caa-row-credential op)))
   :hints (("Goal" :in-theory
            (e/d (fn-caac-credential-carry fn-caac-credential-value-carry
                  fn-caa-row-credential fn-auth-make-cred fn-cp-nth)
                 (fn-caac-spine fn-caac-atom fn-scs-octets fn-authsec-verifier))))))

(defthm fn-campl-successful-row-plan-establishes-credential-carry
  (let ((plan (fn-caa-row-plan a event op)))
    (implies (equal (car plan) :stage)
             (equal (fn-caac-credential-carry op)
                    (fn-scs-summary (fn-cp-nth 2 plan)))))
  :hints (("Goal"
           :use ((:instance fn-caac-credential-carry-is-exact
                            (credential (fn-caa-row-credential op))))
           :in-theory
           (e/d (fn-caa-row-plan fn-cp-nth)
                (fn-caac-credential-value-carry fn-caa-row-credential
                 fn-auth-credp fn-caa-row-descriptor fn-cp-account-creation
                 fn-caa-name-lessp fn-scs-summary)))))

(local
 (defthm fn-campl-old-cursor-head-domain
   (implies (and (fn-caps-old-rowsp rows watermark) (consp rows))
            (and (fn-cp-account-creationp (fn-cp-nth 2 (car rows)) watermark)
                 (fn-cai-namep (fn-cp-nth 1 (car rows)) *fn-auth-max-name-octets*)))
   :hints (("Goal" :in-theory
            (e/d (fn-caps-old-rowsp fn-cp-authority-rowp)
                 (fn-cp-account-creationp fn-cai-namep fn-cp-nth))))))

(defthm fn-campl-actual-row-plan-establishes-stage-carries
  (let* ((p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
         (plan (fn-caa-row-plan a event op)) (row (fn-cp-nth 1 plan)))
   (implies (and (fn-caps-merge-relp p installed)
                 (fn-cac-operationp op)
                 (fn-cp-authority-namespacep (fn-cp-nth 6 prep))
                 (fn-cp-uintp (fn-cp-nth 2 event))
                 (equal (car plan) :stage))
            (and (fn-scc-octet-listp (fn-cp-nth 1 row))
                 (equal (fn-caac-row-carry row) (fn-scs-summary row))
                 (equal (fn-caac-credential-carry op)
                        (fn-scs-summary (fn-cp-nth 2 plan))))))
  :hints (("Goal"
           :use ((:instance fn-campl-successful-row-plan-establishes-credential-carry)
                 (:instance fn-campl-old-cursor-head-domain
                  (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                  (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                 (:instance fn-caarr-row-plan-establishes-binding)
                 (:instance fn-campl-binding-establishes-exact-row-carry
                  (row (fn-cp-nth 1 (fn-caa-row-plan a event op)))
                  (credential (fn-cp-nth 2 (fn-caa-row-plan a event op)))
                  (watermark (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                  (1+ (nfix (fn-cp-nth 2 event)))))))
           :in-theory
           (e/d (fn-caps-merge-relp fn-caar-bindingp fn-cp-authority-rowp)
                (max nfix fn-campl-old-cursor-head-domain fn-caps-old-rowsp fn-caps-suffixp
                 fn-caas-merge-relp fn-cp-nth fn-caa-row-plan fn-cac-operationp
                 fn-cp-authority-namespacep fn-cp-uintp fn-cp-account-creationp
                 fn-cai-namep fn-auth-credp fn-caar-credential-descriptor
                 fn-caac-row-carry fn-caac-credential-carry fn-caac-credential-value-carry fn-scs-summary
                 fn-campl-operation-credential-carry-agrees
                 fn-campl-successful-row-plan-establishes-credential-carry
                 fn-caa-name-lessp fn-caarr-row-plan-establishes-binding)))))

(defthm fn-campl-actual-tombstone-plan-establishes-stage-carries
  (let* ((p (fn-cp-nth 5 a)) (plan (fn-caa-tombstone-plan a event op))
         (row (fn-cp-nth 1 plan)))
   (implies (and (fn-caps-merge-relp p installed) (equal (car plan) :stage))
            (and (fn-scc-octet-listp (fn-cp-nth 1 row))
                 (equal (fn-caac-row-carry row) (fn-scs-summary row))
                 (not (fn-cp-nth 2 plan)))))
  :hints (("Goal"
           :use ((:instance fn-campl-old-cursor-head-domain
                  (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                  (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                 (:instance fn-caarr-tombstone-plan-establishes-binding)
                 (:instance fn-campl-binding-establishes-exact-row-carry
                  (row (fn-cp-nth 1 (fn-caa-tombstone-plan a event op)))
                  (credential (fn-cp-nth 2 (fn-caa-tombstone-plan a event op)))
                  (watermark (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                  (1+ (nfix (fn-cp-nth 2 event)))))))
           :in-theory
           (e/d (fn-caps-merge-relp fn-caar-bindingp fn-cp-authority-rowp
                 fn-caa-tombstone-plan fn-cp-nth)
                (fn-campl-old-cursor-head-domain fn-caps-old-rowsp fn-caps-suffixp
                 fn-caas-merge-relp fn-cp-account-creationp fn-cai-namep
                 fn-auth-credp fn-caar-credential-descriptor
                 fn-caac-row-carry fn-scs-summary fn-caa-name-lessp
                 fn-caarr-tombstone-plan-establishes-binding)))))

(local
 (defthm fn-campl-row-member-has-binding
   (implies (and (fn-caar-rowsp rows index watermark) (member-equal row rows))
            (fn-caar-bindingp row (fn-cai-get-octets (fn-cp-nth 1 row) index)
                              watermark))
   :hints (("Goal" :induct (fn-caar-rowsp rows index watermark)
            :in-theory (e/d (fn-caar-rowsp member-equal)
                             (fn-caar-bindingp fn-cp-nth fn-cai-get-octets
                              fn-caa-name-lessp))))))
(local
 (defthm fn-campl-forward-member-survives-revappend
   (implies (member-equal x forward)
            (member-equal x (revappend reversed forward)))
   :hints (("Goal" :induct (revappend reversed forward)
            :in-theory (e/d (revappend member-equal) (revappend-removal))))))
(local
 (defthm fn-campl-reversed-head-is-member
   (implies (consp reversed)
            (member-equal (car reversed) (revappend reversed forward)))
   :hints (("Goal"
            :expand ((revappend reversed forward))
            :use ((:instance fn-campl-forward-member-survives-revappend
                   (x (car reversed)) (reversed (cdr reversed))
                   (forward (cons (car reversed) forward))))
            :in-theory (e/d (member-equal)
                             (revappend revappend-removal
                              fn-campl-forward-member-survives-revappend))))))

(defthm fn-campl-actual-prepare-establishes-credential-carry
  (let* ((prep (fn-cp-nth 5 (fn-cp-nth 5 a)))
         (head (car (fn-cp-nth 3 prep)))
         (one (fn-caa-prepare s a event))
         (new-root (fn-cp-nth 5 (fn-cp-nth 5
                     (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 one))))))
         (credential (car (fn-cp-nth 3 new-root))))
   (implies (and (fn-caar-preparation-relp prep)
                 (equal (car one) :ok) (fn-cp-nth 3 head))
            (equal (fn-caac-credential-value-carry credential)
                   (fn-scs-summary credential))))
  :hints (("Goal"
           :use ((:instance fn-campl-reversed-head-is-member
                  (reversed (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                  (forward (fn-cp-nth 4 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                 (:instance fn-campl-row-member-has-binding
                  (rows (revappend (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a)))
                                   (fn-cp-nth 4 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (row (car (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (index (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (watermark (fn-cp-nth 7 (fn-cp-nth 5 (fn-cp-nth 5 a))))))
           :in-theory
           (e/d (fn-caar-preparation-relp fn-caar-index-relp fn-caar-bindingp
                 fn-caa-prepare fn-caa-success fn-caa-authority-pending
                 fn-caa-pending fn-caa-preparation fn-caa-root fn-cp-state-carry fn-cp-nth)
                (fn-caar-rowsp fn-caar-rebuild fn-caar-credentials fn-caar-root-shapep
                 fn-campl-row-member-has-binding fn-campl-reversed-head-is-member
                 fn-cai-get-octets fn-cp-authority-rowp fn-cai-namep
                 fn-auth-credp fn-caar-credential-descriptor
                 fn-caac-credential-value-carry fn-scs-summary revappend member-equal)))))
