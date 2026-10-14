(in-package "ACL2")
(include-book "pacc-owner-reads")

(defthm fn-pacc-successful-injection-has-valid-inputs
  (implies (fn-inj-injectedp (fn-inj-decide art icfg iclock))
           (and (fn-inj-configp icfg) (fn-clock-observationp iclock)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-inj-decide fn-inj-injectedp fn-inj-refuse
                           fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacc-successful-gated-injection-has-valid-inputs
  (implies (fn-inj-injectedp (fn-post-gated-decision art icfg iclock))
           (and (fn-inj-configp icfg) (fn-clock-observationp iclock)))
  :hints (("Goal" :use ((:instance fn-post-gated-decision-is-the-decision-or-its-envelope
                          (source art) (config icfg) (injection iclock)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-pacc-successful-injection-has-valid-inputs)))))

(defthm fn-pacc-injected-decision-is-not-peer
  (implies (fn-inj-injectedp d) (not (fn-peer-submissionp d)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                      '(fn-inj-injectedp fn-peer-submissionp fn-ag-car
                        fn-inj-decision-status fn-inj-nth fn-inj-car fn-inj-cdr nfix zp)))))

(defthm fn-pacc-successful-read-body
  (implies (and (fn-own-sub-shapep sub)
                (fn-inj-configp icfg) (fn-clock-observationp iclock)
                (equal (fn-own-sub-decision sub) (fn-post-gated-decision art icfg iclock))
                (fn-inj-injectedp (fn-own-sub-decision sub))
                (not (fn-peer-submissionp (fn-own-sub-decision sub)))
                (fn-apc-p parse-carry))
           (fn-pacc-sub-read-bodyp sub secret take-config parse-carry
                                  (fn-inj-config-header-limits icfg) art icfg iclock))
  :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
               '(fn-pacc-sub-read-bodyp fn-pacc-sub-inj fn-pacc-stored-payload
                 fn-own-sub-stored-octets fn-pctx-get nfix zp car-cons cdr-cons
                 fn-apc-cl-served-payload-is-reference)))))

(defthm fn-pacc-read-body-establishes-readp
  (implies (fn-pacc-sub-read-bodyp sub secret take-config parse-carry read-limits art icfg iclock)
           (fn-pacc-sub-readp sub secret take-config parse-carry read-limits))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pacc-sub-readp-suff))
           :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-awaiting-success-produces-gated-decision
 (implies (and (fn-post-sessionp ps) (fn-post-session-awaiting ps)
               (fn-inj-injectedp (fn-post-gated-decision (fn-post-body-octets body) icfg iclock)))
  (equal (fn-post-result-submission
           (fn-nntp-post-step ps archive icfg observation iclock (list :article body) fn-arena))
         (fn-post-gated-decision (fn-post-body-octets body) icfg iclock)))
 :hints (("Goal" :do-not-induct t
   :in-theory (union-theories (theory 'minimal-theory)
      '(fn-nntp-post-step fn-post-result-submission fn-post-make-result
        fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-completed-read-establishes-sub-readp
  (let* ((art (fn-post-body-octets body))
         (d (fn-post-gated-decision art icfg iclock))
         (r (fn-nntp-post-step ps archive icfg observation iclock
                               (list :article body) fn-arena))
         (sub (fn-own-sub-make-author
               id version nil (fn-post-result-submission r) login account
               (fn-own-served-source-context (fn-post-result-submission r)))))
    (implies (and (fn-arena-p fn-arena)                         ; E1 (a)
                  (fn-post-sessionp ps)                        ; E2 (a)
                  (fn-post-session-awaiting ps)                 ; E3 (b) tooth: ground
                  (fn-apc-p parse-carry)                        ; E4 (a)
                  (fn-inj-injectedp d))                         ; E5 (b) tooth: ground
             (and (equal (fn-post-result-submission r) d)
                  (fn-pacc-sub-readp
                   sub secret take-config parse-carry
                   (fn-inj-config-header-limits icfg)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-awaiting-success-produces-gated-decision)
 (:instance fn-pacc-successful-gated-injection-has-valid-inputs (art (fn-post-body-octets body)))
 (:instance fn-pacc-injected-decision-is-not-peer (d (fn-post-gated-decision (fn-post-body-octets body) icfg iclock)))
 (:instance fn-pacc-successful-read-body (sub (fn-own-sub-make-author id version nil
 (fn-post-result-submission (fn-nntp-post-step ps archive icfg observation iclock (list :article body) fn-arena))
 login account
 (fn-own-served-source-context (fn-post-result-submission (fn-nntp-post-step ps archive icfg observation iclock (list :article body) fn-arena))))) (art (fn-post-body-octets body)))
 (:instance fn-pacc-read-body-establishes-readp (sub (fn-own-sub-make-author id version nil
 (fn-post-result-submission (fn-nntp-post-step ps archive icfg observation iclock (list :article body) fn-arena))
 login account
 (fn-own-served-source-context (fn-post-result-submission (fn-nntp-post-step ps archive icfg observation iclock (list :article body) fn-arena))))) (art (fn-post-body-octets body)) (read-limits (fn-inj-config-header-limits icfg))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-sub-shapep-of-fn-own-sub-make-author fn-own-sub-decision-of-fn-own-sub-make-author)))))

(defthm fn-pacc-sub-readp-rebinds-take-inputs
  (implies
   (and (fn-pacc-sub-readp sub secret0 cfg0 carry0 read-limits)
        (fn-apc-p carry1))
   (fn-pacc-sub-readp sub secret1 cfg1 carry1 read-limits))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-read-body-establishes-readp (secret secret1) (take-config cfg1) (parse-carry carry1) (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits))))
       (:instance fn-pacc-successful-read-body (secret secret1) (take-config cfg1) (parse-carry carry1) (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret0 cfg0 carry0 read-limits)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-readp fn-pacc-sub-read-bodyp)))))

(defthm fn-pacc-sub-readp-of-same-decision-and-account
 (implies (and (fn-pacc-sub-readp old secret cfg carry h)
               (fn-own-sub-shapep new)
               (equal (fn-own-sub-decision new) (fn-own-sub-decision old))
               (equal (fn-own-sub-account new) (fn-own-sub-account old)))
          (fn-pacc-sub-readp new secret cfg carry h))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-read-body-establishes-readp
          (sub new) (take-config cfg) (parse-carry carry) (read-limits h)
          (art (mv-nth 0 (fn-pacc-sub-readp-witness old secret cfg carry h)))
          (icfg (mv-nth 1 (fn-pacc-sub-readp-witness old secret cfg carry h)))
          (iclock (mv-nth 2 (fn-pacc-sub-readp-witness old secret cfg carry h)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-readp fn-pacc-sub-read-bodyp fn-pacc-sub-inj fn-own-sub-stored-octets
 fn-pacc-stored-payload fn-pctx-get nfix zp car-cons cdr-cons)))))

(defthm fn-pacc-recovered-owner-has-no-connections
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (not (consp (fn-own-conns (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-ock-install fn-ocfg-owner-of-fn-ocfg-make fn-own-configure fn-own-start fn-own-refresh fn-own-conns-of-fn-own-make (:executable-counterpart consp))))))

(defthm fn-pacc-recovered-owner-has-no-local-work
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (let ((o (fn-ocfg-owner (fn-ock-install replayed opened max-conns))))
             (and (not (consp (fn-own-queue o)))
                  (null (fn-own-inflight o)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-ock-install fn-ocfg-owner-of-fn-ocfg-make fn-own-configure fn-own-start fn-own-refresh fn-own-queue-of-fn-own-make fn-own-inflight-of-fn-own-make (:executable-counterpart consp))))))

(defthm fn-pacc-osb-install-keeps-queue-and-inflight
  (and (equal (fn-own-queue (mv-nth 1 (fn-osb-install o profile))) (fn-own-queue o))
       (equal (fn-own-inflight (mv-nth 1 (fn-osb-install o profile))) (fn-own-inflight o)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-osb-install fn-own-configure fn-own-queue-of-fn-own-make fn-own-inflight-of-fn-own-make mv-nth nfix zp car-cons cdr-cons)))))

(defthm fn-pacc-take-carries-sub-readp-at-item-triple
  (let* ((o (fn-ocfg-owner oc))
         (head (fn-psub-unpack-sub (car (fn-own-queue o))))
         (next (fn-ocfg-step oc (list :take) fn-arena))
         (after (fn-ocfg-owner next))
         (sub (fn-own-inflight after))
         (cfg (fn-ocfg-config next))
         (secret (fn-own-node-secret after))
         (tk (fn-apc-take cfg sub secret)))
    (implies
     (and (fn-arena-p fn-arena)                              ; T1 (a)
          (null (fn-ocfg-staged oc))                         ; T2
          (null (fn-own-inflight o))                         ; T3
          (consp (fn-own-queue o))                           ; T4
          (null (fn-own-pending o))                          ; T5
          (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready) ; T6
          (fn-pacc-sub-readp head secret cfg (cdr tk) read-limits)) ; T7
     (and (fn-pacc-sub-readp sub secret cfg (cdr tk) read-limits)
          (fn-apc-p (cdr tk))
          (equal (car tk) (fn-own-sub-stored-octets cfg sub secret)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-successful-read-body (sub (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (secret (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (take-config (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena))) (parse-carry (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))))) (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))))
       (:instance fn-pacc-read-body-establishes-readp (sub (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (secret (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (take-config (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena))) (parse-carry (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))))) (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))) read-limits))) (read-limits read-limits)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-ocfg-step fn-ocfg-pass fn-ocfg-with-owner fn-own-step fn-own-take-submission
 fn-ocfg-owner-of-fn-ocfg-make fn-ocfg-config-of-fn-ocfg-make
 fn-own-inflight-of-fn-own-make fn-own-node-secret-of-fn-own-make
 fn-own-sub-shapep-of-fn-own-sub-make-author fn-own-sub-decision-of-fn-own-sub-make-author
 fn-own-sub-account-of-fn-own-sub-make-author fn-apc-take-stores-the-stored-octets fn-apc-p-of-take
 fn-pacc-sub-readp fn-pacc-sub-read-bodyp car-cons cdr-cons
 (:executable-counterpart consp) (:executable-counterpart car) (:executable-counterpart cdr))))))

(defthm fn-pacc-u8-by-u11
 (implies (equal (fn-pak-post-admission pcarry profile msgid length (len codes) charge key fn-cat) :ok)
          (consp codes))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pak-post-admission fn-pvc-post-boundary-carried fn-pvc-post-boundary
 len natp posp nfix zp (:executable-counterpart equal) (:executable-counterpart <))))))

(defthm fn-pacc-u9-by-u11
 (implies (not (equal (fn-pctx-get 0 (fn-ars-filing-plan groups boundary-domain fn-octets)) :file))
          (not (consp (fn-store-codes-from-groups
                        (fn-pacc-derived-names (fn-pctx-get 1 (fn-ars-filing-plan groups boundary-domain fn-octets)))
                        boundary-domain))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-ars-filing-plan fn-pctx-get fn-pacc-derived-names fn-store-codes-from-groups nfix zp car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart consp) (:executable-counterpart car) (:executable-counterpart cdr))))))

(local (defthm fn-pacc-derived-names-are-proper-l
 (true-listp (fn-pacc-derived-names xs))
 :hints (("Goal" :induct (fn-pacc-derived-names xs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-derived-names true-listp car-cons cdr-cons))))))

(local (defthm fn-pacc-derived-names-exclude-nil-l
 (not (member-equal nil (fn-pacc-derived-names xs)))
 :hints (("Goal" :induct (fn-pacc-derived-names xs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-derived-names member-equal car-cons cdr-cons (:type-prescription fn-record-octets-string)))))))

(local (defthm fn-pacc-successful-codes-keep-length-l
 (implies (not (equal (fn-store-codes-from-groups names domain) :bad))
          (equal (len (fn-store-codes-from-groups names domain)) (len names)))
 :hints (("Goal" :induct (fn-store-codes-from-groups names domain)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-store-codes-from-groups len car-cons cdr-cons (:executable-counterpart equal)))))))

(local (defthm fn-pacc-derived-codes-count-filed-groups-l
 (implies (consp (fn-store-codes-from-groups (fn-pacc-derived-names xs) domain))
  (equal (len (fn-store-groups-from-codes (fn-store-codes-from-groups (fn-pacc-derived-names xs) domain) domain))
         (len (fn-store-codes-from-groups (fn-pacc-derived-names xs) domain))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-store-codes-from-groups-inverts (names (fn-pacc-derived-names xs)) (groups domain)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-derived-names-are-proper-l fn-pacc-derived-names-exclude-nil-l
 fn-pacc-successful-codes-keep-length-l (:executable-counterpart consp)))))))

(defthm fn-pacc-unsigned-arm-concludes-profile-admitted-postp-at-item-triple
  (let* ((d (fn-own-sub-decision sub))
         (filing (fn-ars-filing-plan (fn-inj-decision-groups d)
                                     boundary-domain fn-octets))
         (names (fn-pacc-derived-names (fn-pctx-get 1 filing)))
         (codes (fn-store-codes-from-groups names boundary-domain)))
    (implies
     (and (fn-octets-p fn-octets) (fn-cat-p fn-cat) (fn-sn-statep s)    ; U1 (a)
          (fn-pvc-carryp pcarry)                                     ; U2 (a)
          (fn-apc-p parse-carry)                                     ; U3 (a)
          (fn-pacc-sub-read-bodyp sub secret take-config parse-carry
                                  read-limits art icfg iclock)       ; U4, explicit; tooth: wrong ART
          (equal (fn-octets-list fn-octets)
                 (fn-own-sub-stored-octets take-config sub secret))  ; U5 tooth: ground (BODY)
          (equal read-limits (fn-bs-profile-header-limits profile))  ; U6 tooth: ground (BODY)
          (equal boundary-domain
                 (fn-state-groups (fn-node-acceptance (fn-sn-node s)))) ; U7 tooth: ground (BODY)
          (equal (fn-ars-carrier-form fn-octets) :absent)            ; U10 tooth: ground (BODY)
          (equal (fn-pak-post-admission
                  pcarry profile (fn-inj-decision-msgid d)
                  (fn-octets-len fn-octets) (len codes)
                  (fn-charge-for-payload (fn-octets-len fn-octets)) key fn-cat)
                 :ok))                                               ; U11 tooth: ground (BODY)
     (fn-pacc-profile-admitted-postp
      s art (fn-pacc-sub-inj sub secret take-config parse-carry icfg iclock)
      profile pcarry)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-u8-by-u11
        (msgid (fn-inj-decision-msgid (fn-own-sub-decision sub)))
        (length (fn-octets-len fn-octets)) (codes (fn-store-codes-from-groups (fn-pacc-derived-names (fn-pctx-get 1 (fn-ars-filing-plan (fn-inj-decision-groups (fn-own-sub-decision sub)) boundary-domain fn-octets))) boundary-domain))
        (charge (fn-charge-for-payload (fn-octets-len fn-octets))))
       (:instance fn-pacc-u9-by-u11 (groups (fn-inj-decision-groups (fn-own-sub-decision sub)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-read-bodyp fn-pacc-profile-admitted-postp fn-pacc-derived-fields
 fn-pacc-sub-inj fn-pctx-get nfix zp car-cons cdr-cons
 fn-oct-list-is-identity fn-oct-len-is-len fn-ars-carrier-form-is-reference fn-ars-filing-plan-is-reference
 fn-apc-filing-plan-is-reference fn-pak-post-admission fn-pacc-derived-codes-count-filed-groups-l
 (:executable-counterpart consp) (:executable-counterpart equal))))))

(defthm fn-pacc-unsigned-witness-concludes-profile-admitted-postp-at-item-triple (let* ((d (fn-own-sub-decision sub)) (filing (fn-ars-filing-plan (fn-inj-decision-groups d) boundary-domain fn-octets)) (names (fn-pacc-derived-names (fn-pctx-get 1 filing))) (codes (fn-store-codes-from-groups names boundary-domain))) (implies (and (fn-octets-p fn-octets) (fn-cat-p fn-cat) (fn-sn-statep s) (fn-pvc-carryp pcarry) (fn-apc-p parse-carry) (fn-pacc-sub-readp sub secret take-config parse-carry read-limits) (equal (fn-octets-list fn-octets) (fn-own-sub-stored-octets take-config sub secret)) (equal read-limits (fn-bs-profile-header-limits profile)) (equal boundary-domain (fn-state-groups (fn-node-acceptance (fn-sn-node s)))) (equal (fn-ars-carrier-form fn-octets) :absent) (equal (fn-pak-post-admission pcarry profile (fn-inj-decision-msgid d) (fn-octets-len fn-octets) (len codes) (fn-charge-for-payload (fn-octets-len fn-octets)) key fn-cat) :ok)) (fn-pacc-profile-admitted-postp s (mv-nth 0 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)) (fn-pacc-sub-inj sub secret take-config parse-carry (mv-nth 1 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)) (mv-nth 2 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) profile pcarry)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-unsigned-arm-concludes-profile-admitted-postp-at-item-triple
 (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-sub-readp)))))

(defthm fn-pacc-effective-read-config-keeps-pin-header-limits
  (equal
   (fn-inj-config-header-limits
    (fn-auth-view-config
     as (fn-auth-moderation-config as (fn-gac-config-with-live pinned live))
     archive))
   (fn-inj-config-header-limits pinned))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-auth-view-config fn-auth-moderation-config fn-gac-config-with-live fn-gac-post-config fn-inj-make-config-full fn-inj-config-header-limits fn-inj-post-bound fn-inj-bound-header-limits fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-admitted-limit-row-keeps-profile-header-limits
  (implies
   (and (fn-bs-profile-admittedp profile)
        (fn-bs-profile-admittedp (fn-lim-apply-row profile field n)))
   (equal (fn-bs-profile-header-limits (fn-lim-apply-row profile field n))
          (fn-bs-profile-header-limits profile)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-bs-profile-admittedp fn-bs-profile-of fn-bs-profile-header-limits fn-bs-profile-field fn-bs-pf fn-lim-apply-row fn-lim-field-index fn-lim-nth-of-set-nth nfix zp (:executable-counterpart fn-bs-profile-validp))))))

(local (defthm fn-pacc-rcon-sn-io-keeps-node-l
 (equal (fn-sn-node (fn-rcon-sn-io s operation result)) (fn-sn-node s))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcon-sn-io fn-sn-update fn-sn-make-v6 fn-sn-node fn-store-event-nth nfix zp car-cons cdr-cons))))))

(local (defthm fn-pacc-refresh-keeps-store-l
 (equal (fn-own-store (fn-own-refresh o)) (fn-own-store o))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-refresh fn-own-store-of-fn-own-make))))))

(local (defthm fn-pacc-rcon-ocfg-io-keeps-node-l
 (equal (fn-sn-node (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result))))
        (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcon-ocfg-io fn-rcon-own-store-io fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
 fn-pacc-refresh-keeps-store-l fn-own-store-of-fn-own-make fn-pacc-rcon-sn-io-keeps-node-l))))))

(defthm fn-pacc-log-reserve-keeps-the-allocation-node
  (implies
   (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
   (equal (fn-sn-node (fn-own-store (fn-ocfg-owner (fn-olr-ocfg-reserve oc))))
          (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-olr-ocfg-reserve fn-pacc-rcon-ocfg-io-keeps-node-l)))))

(defun fn-pacc-decision-readp (d h)
 (declare (xargs :guard t :verify-guards nil))
 (implies (and (fn-inj-injectedp d) (not (fn-peer-submissionp d)))
  (fn-pacc-sub-readp (fn-own-sub-make-author nil nil nil d nil nil :post-d25) nil nil nil h)))

(defthm fn-pacc-gated-decision-establishes-decision-readp
 (fn-pacc-decision-readp (fn-post-gated-decision art icfg iclock) (fn-inj-config-header-limits icfg))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-successful-gated-injection-has-valid-inputs)
       (:instance fn-pacc-injected-decision-is-not-peer (d (fn-post-gated-decision art icfg iclock)))
       (:instance fn-pacc-successful-read-body
        (sub (fn-own-sub-make-author nil nil nil (fn-post-gated-decision art icfg iclock) nil nil :post-d25))
        (secret nil) (take-config nil) (parse-carry nil))
       (:instance fn-pacc-read-body-establishes-readp
        (sub (fn-own-sub-make-author nil nil nil (fn-post-gated-decision art icfg iclock) nil nil :post-d25))
        (secret nil) (take-config nil) (parse-carry nil) (read-limits (fn-inj-config-header-limits icfg))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-decision-readp fn-own-sub-shapep-of-fn-own-sub-make-author
 fn-own-sub-decision-of-fn-own-sub-make-author fn-apc-p-when-atom (:executable-counterpart consp))))))

(defthm fn-pacc-decision-readp-for-refusal-or-peer-by-definition
 (implies (or (not (fn-inj-injectedp d)) (fn-peer-submissionp d))
          (fn-pacc-decision-readp d h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-decision-readp)))))

(defthm fn-pacc-post-step-establishes-decision-readp
 (fn-pacc-decision-readp
  (fn-post-result-submission (fn-nntp-post-step ps archive config observation injection wire-event fn-arena))
  (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-post-step fn-post-result-submission fn-post-make-result
 fn-pacc-gated-decision-establishes-decision-readp
 fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp))))))

(defthm fn-pacc-auth-view-keeps-header-limits
 (equal (fn-inj-config-header-limits (fn-auth-view-config as config archive))
        (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-view-config fn-gac-post-config fn-inj-make-config-full fn-inj-config-header-limits
 fn-inj-post-bound fn-inj-bound-header-limits fn-inj-nth fn-inj-car fn-inj-cdr nfix zp
 car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-moderation-view-keeps-header-limits
 (equal (fn-inj-config-header-limits (fn-auth-moderation-config as config))
        (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-moderation-config fn-inj-make-config-full fn-inj-config-header-limits
 fn-inj-post-bound fn-inj-bound-header-limits fn-inj-nth fn-inj-car fn-inj-cdr nfix zp
 car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-peer-constructor-is-not-injected-by-definition
 (not (fn-inj-injectedp (fn-peer-make-submission peer kind msgid octets)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-inj-injectedp fn-inj-decision-status fn-inj-nth fn-inj-car fn-inj-cdr
 fn-peer-make-submission nfix zp car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pacc-nntp-post-step-pinned-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-nntp-post-step-pinned ps archive index verdicts config observation injection wire-event fn-arena)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-post-step-pinned fn-pacc-post-step-establishes-decision-readp  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-nntp-post-step-pinned-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-nntp-post-step-pinned ps archive index verdicts config observation injection wire-event fn-arena)) h))
 :hints (("Goal" :use ((:instance fn-pacc-nntp-post-step-pinned-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-post-step-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-post-step ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-post-step fn-pacc-post-step-establishes-decision-readp  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-post-step-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-post-step ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-post-step-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-peer-delegate-pinned-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-peer-delegate-pinned ps archive index verdicts config observation injection wire-event fn-arena)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-peer-delegate-pinned fn-pacc-nntp-post-step-pinned-read-origin fn-pacc-nntp-post-step-pinned-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-peer-delegate-pinned-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-peer-delegate-pinned ps archive index verdicts config observation injection wire-event fn-arena)) h))
 :hints (("Goal" :use ((:instance fn-pacc-peer-delegate-pinned-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-peer-delegate-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-delegate ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-delegate fn-pacc-av-scr-post-step-read-origin fn-pacc-av-scr-post-step-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-peer-delegate-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-delegate ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-peer-delegate-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-pgc-peer-command-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-pgc-peer-command ps keyword args arts)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-peer-command   fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-scr-peer-command-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-scr-peer-command ps keyword args lver arts fn-arena fn-cat)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scr-peer-command fn-pacc-pgc-peer-command-read-origin  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-pgc-transfer-step-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-pgc-transfer-step ps wire-event)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-transfer-step fn-pacc-peer-constructor-is-not-injected-by-definition  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-pgc-peer-arm-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-pgc-peer-arm ps arts archive index verdicts config observation injection wire-event fn-arena)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-peer-arm fn-pacc-peer-delegate-pinned-read-origin fn-pacc-pgc-peer-command-read-origin fn-pacc-pgc-transfer-step-read-origin fn-pacc-peer-delegate-pinned-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-pgc-peer-arm-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-pgc-peer-arm ps arts archive index verdicts config observation injection wire-event fn-arena)) h))
 :hints (("Goal" :use ((:instance fn-pacc-pgc-peer-arm-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-peer-arm-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-arm ps lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-arm fn-pacc-av-scr-peer-delegate-read-origin fn-pacc-scr-peer-command-read-origin fn-pacc-pgc-transfer-step-read-origin fn-pacc-av-scr-peer-delegate-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-peer-arm-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-arm ps lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-peer-arm-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-peer-step-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-step ps live lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-step fn-pacc-av-scr-peer-delegate-read-origin fn-pacc-av-scr-peer-arm-read-origin fn-pacc-av-scr-peer-delegate-read-origin-at-header-limits fn-pacc-av-scr-peer-arm-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-peer-step-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-peer-step ps live lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-peer-step-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-scar-peer-step-pinned-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-scar-peer-step-pinned ps live arts archive index verdicts config observation injection wire-event fn-arena)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-peer-step-pinned fn-pacc-peer-delegate-pinned-read-origin fn-pacc-pgc-peer-arm-read-origin fn-pacc-peer-delegate-pinned-read-origin-at-header-limits fn-pacc-pgc-peer-arm-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-scar-peer-step-pinned-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-scar-peer-step-pinned ps live arts archive index verdicts config observation injection wire-event fn-arena)) h))
 :hints (("Goal" :use ((:instance fn-pacc-scar-peer-step-pinned-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-scar-auth-delegate-pinned-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-scar-auth-delegate-pinned as live arts archive index verdicts config observation injection wire-event fn-arena)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-auth-delegate-pinned fn-pacc-scar-peer-step-pinned-read-origin fn-pacc-auth-view-keeps-header-limits fn-pacc-moderation-view-keeps-header-limits fn-pacc-scar-peer-step-pinned-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-scar-auth-delegate-pinned-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-scar-auth-delegate-pinned as live arts archive index verdicts config observation injection wire-event fn-arena)) h))
 :hints (("Goal" :use ((:instance fn-pacc-scar-auth-delegate-pinned-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-auth-delegate-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-auth-delegate as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-auth-delegate fn-pacc-scar-peer-step-pinned-read-origin fn-pacc-scar-auth-delegate-pinned-read-origin fn-pacc-av-scr-peer-step-read-origin fn-pacc-auth-view-keeps-header-limits fn-pacc-moderation-view-keeps-header-limits fn-pacc-scar-peer-step-pinned-read-origin-at-header-limits fn-pacc-scar-auth-delegate-pinned-read-origin-at-header-limits fn-pacc-av-scr-peer-step-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-auth-delegate-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-auth-delegate as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-auth-delegate-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-auth-tls-established-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-tls-established as)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-tls-established   fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-auth-redeem-outcome-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-redeem-outcome as wire-event)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-redeem-outcome   fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-auth-install-context-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-install-context as wire-event)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-install-context fn-auth-install-context-has-no-submission  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-auth-sasl-continue-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-sasl-continue as line)) h)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-continue fn-auth-sasl-continue-has-no-submission  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-auth-command-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-command as config keyword args)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-command fn-auth-authinfo-carries-no-submission fn-auth-starttls fn-auth-xredeem fn-auth-compress  fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-auth-command-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-auth-command as config keyword args)) h))
 :hints (("Goal" :use ((:instance fn-pacc-auth-command-read-origin)) :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-scr-auth-step-read-origin
 (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-auth-step as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)) (fn-inj-config-header-limits config))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-auth-step fn-pacc-av-scr-auth-delegate-read-origin fn-pacc-av-scr-auth-delegate-read-origin-at-header-limits fn-pacc-auth-tls-established-read-origin fn-pacc-auth-redeem-outcome-read-origin fn-pacc-auth-install-context-read-origin fn-pacc-auth-sasl-continue-read-origin fn-pacc-auth-command-read-origin fn-pacc-av-scr-auth-delegate-read-origin-at-header-limits fn-pacc-auth-command-read-origin-at-header-limits fn-post-result-submission-of-fn-post-make-result fn-inj-nth fn-inj-car fn-inj-cdr nfix zp car-cons cdr-cons
 fn-pacc-decision-readp-for-refusal-or-peer-by-definition (:executable-counterpart fn-inj-injectedp) (:executable-counterpart fn-post-result-submission))))))

(defthm fn-pacc-av-scr-auth-step-read-origin-at-header-limits
 (implies (equal (fn-inj-config-header-limits config) h)
          (fn-pacc-decision-readp (fn-post-result-submission (fn-av-scr-auth-step as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-scr-auth-step-read-origin)) :in-theory (theory 'minimal-theory))))

(defun fn-pacc-non-submit-effectsp (effects)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp effects)
     (and (not (equal (car (car effects)) :submit))
          (fn-pacc-non-submit-effectsp (cdr effects))) t))

(defun fn-pacc-effects-readp (effects h)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp effects)
  (and (implies (equal (car (car effects)) :submit)
                (fn-pacc-decision-readp (car (cdr (car effects))) h))
       (fn-pacc-effects-readp (cdr effects) h)) t))

(defthm fn-pacc-non-submit-effectsp-append
 (equal (fn-pacc-non-submit-effectsp (append a b))
        (and (fn-pacc-non-submit-effectsp a) (fn-pacc-non-submit-effectsp b)))
 :hints (("Goal" :induct (fn-pacc-non-submit-effectsp a)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-non-submit-effectsp binary-append endp car-cons cdr-cons (:type-prescription fn-pacc-non-submit-effectsp))))))

(defthm fn-pacc-effects-readp-append
 (equal (fn-pacc-effects-readp (append a b) h)
        (and (fn-pacc-effects-readp a h) (fn-pacc-effects-readp b h)))
 :hints (("Goal" :induct (binary-append a b)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-effects-readp binary-append endp car-cons cdr-cons (:type-prescription fn-pacc-effects-readp) (:type-prescription fn-pacc-decision-readp))))))

(defthm fn-pacc-non-submit-effects-have-readp-by-definition
 (implies (fn-pacc-non-submit-effectsp effects) (fn-pacc-effects-readp effects h))
 :hints (("Goal" :induct (fn-pacc-non-submit-effectsp effects)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-non-submit-effectsp fn-pacc-effects-readp)))))

(defthm fn-pacc-selected-submission-has-readp
 (implies (fn-pacc-effects-readp effects h)
          (fn-pacc-decision-readp (fn-served-submission effects) h))
 :hints (("Goal" :induct (fn-served-submission effects)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-effects-readp fn-served-submission fn-pacc-decision-readp-for-refusal-or-peer-by-definition
 (:executable-counterpart fn-inj-injectedp))))))

(defthm fn-pacc-one-submit-has-readp-by-definition
 (implies (fn-pacc-decision-readp decision h)
          (fn-pacc-effects-readp (list (fn-served-submit-effect decision login account)) h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-served-submit-effect fn-pacc-effects-readp car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pacc-empty-effects-have-readp-by-definition
 (fn-pacc-effects-readp nil h)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-effects-readp (:executable-counterpart consp))))))

(defthm fn-pacc-nntp-result-effects-of-make-by-definition
 (equal (fn-nntp-result-effects (fn-nntp-make-result session effects)) effects)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-result-effects fn-nntp-make-result cdr-cons)))))

(local (defthm fn-pacc-auth-tls-established-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-tls-established as)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-tls-established  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-single-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-single session text)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-single  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-single-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-auth-single as text))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-single fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-redeem-outcome-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-redeem-outcome as wire-event)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-redeem-outcome fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-install-context-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-install-context as wire-event)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-install-context  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-sasl-refuse-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-sasl-refuse as text)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-refuse fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-sasl-effects-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-auth-sasl-effects code payload))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-effects  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-failed-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-failed as)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-failed fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-sasl-finish-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-sasl-finish as st response)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-finish fn-pacc-auth-sasl-effects-effects-exclude-submit fn-pacc-auth-single-effects-exclude-submit fn-pacc-auth-failed-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-sasl-continue-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-sasl-continue as line)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-continue fn-pacc-auth-sasl-refuse-effects-exclude-submit fn-pacc-auth-sasl-finish-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-compress-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-compress as args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-compress fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-sasl-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-sasl-command as margs)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-sasl-command fn-pacc-auth-sasl-refuse-effects-exclude-submit fn-pacc-auth-sasl-effects-effects-exclude-submit fn-pacc-auth-sasl-finish-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-authinfo-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-authinfo as args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-authinfo fn-pacc-auth-single-effects-exclude-submit fn-pacc-auth-failed-effects-exclude-submit fn-pacc-auth-sasl-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-xredeem-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-xredeem as args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-xredeem fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-starttls-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-starttls as args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-starttls fn-pacc-auth-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-multi-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-multi session initial lines)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-multi  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-auth-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-auth-command as config keyword args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-auth-command fn-pacc-auth-single-effects-exclude-submit fn-pacc-auth-compress-effects-exclude-submit fn-pacc-auth-authinfo-effects-exclude-submit fn-pacc-auth-xredeem-effects-exclude-submit fn-pacc-auth-starttls-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-post-single-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-single ps text))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-post-single fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-capabilities-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-capabilities session postingp)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-capabilities fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-help-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-help session)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-help fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-post-offer-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-post-offer session)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-post-offer  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-mode-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-mode-response session env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-mode-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-date-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-date-response session env)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-date-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-session-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-session-command session env keyword args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-session-command fn-pacc-nntp-capabilities-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-help-effects-exclude-submit fn-pacc-nntp-post-offer-effects-exclude-submit fn-pacc-nntp-mode-response-effects-exclude-submit fn-pacc-nntp-date-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-group-result-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-group-result session archive group)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-group-result fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-multi-octets-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-multi-octets session initial lines)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-multi-octets  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-listgroup-result-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-listgroup-result session archive group range)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-listgroup-result fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-listgroup-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-listgroup-command session archive args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-listgroup-command fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-listgroup-result-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-active-times-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-active-times session env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-active-times fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-counts-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-counts session archive groups closed)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-counts fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-counts-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-counts-command session archive closed args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-counts-command fn-pacc-nntp-list-counts-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-newsgroups-described-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-newsgroups-described session archive descs args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-newsgroups-described fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-motd-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-motd session env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-motd fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-active-status-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-active-status session archive groups closed)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-active-status fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-active-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-active session archive groups)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-active fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-newsgroups-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-newsgroups session groups)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-newsgroups fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-filtered-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-filtered-response session archive kind wildmat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-filtered-response fn-pacc-nntp-list-active-effects-exclude-submit fn-pacc-nntp-list-newsgroups-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-active-or-newsgroups-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-active-or-newsgroups session archive kind args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-active-or-newsgroups fn-pacc-nntp-list-active-effects-exclude-submit fn-pacc-nntp-list-newsgroups-effects-exclude-submit fn-pacc-nntp-list-filtered-response-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-overview-fmt-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-overview-fmt session)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-overview-fmt fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-headers-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-headers session)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-headers fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-unmaintained-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-unmaintained-response session keyword args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-unmaintained-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-list-overview-fmt-effects-exclude-submit fn-pacc-nntp-list-headers-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-response session archive args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-response fn-pacc-nntp-list-active-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-list-active-or-newsgroups-effects-exclude-submit fn-pacc-nntp-list-unmaintained-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-status-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-status-response session archive closed args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-status-response fn-pacc-nntp-list-active-status-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-list-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-command session archive env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-command fn-pacc-nntp-list-active-times-effects-exclude-submit fn-pacc-nntp-list-counts-command-effects-exclude-submit fn-pacc-nntp-list-newsgroups-described-effects-exclude-submit fn-pacc-nntp-list-motd-effects-exclude-submit fn-pacc-nntp-list-status-response-effects-exclude-submit fn-pacc-nntp-list-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-article-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-article-response session article number kind updatep group fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-article-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-next-or-last-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-next-or-last session archive direction fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-next-or-last fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-current-retrieval-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-current-retrieval session archive kind fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-current-retrieval fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-number-retrieval-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-number-retrieval session archive kind token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-number-retrieval fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-msgid-retrieval-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-msgid-retrieval session archive kind token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-msgid-retrieval fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-retrieval-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-retrieval session archive kind args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-retrieval fn-pacc-nntp-current-retrieval-effects-exclude-submit fn-pacc-nntp-number-retrieval-effects-exclude-submit fn-pacc-nntp-msgid-retrieval-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-current-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-current session archive fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-current fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-range-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-range session archive token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-range fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-msgid-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-msgid session archive token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-msgid fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-response session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-response fn-pacc-nntp-over-current-effects-exclude-submit fn-pacc-nntp-over-range-effects-exclude-submit fn-pacc-nntp-over-msgid-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xover-range-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xover-range session archive token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xover-range fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xover-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xover-response session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xover-response fn-pacc-nntp-over-current-effects-exclude-submit fn-pacc-nntp-xover-range-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-current-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-current session archive field legacyp fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-current fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-range-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-range session archive field token legacyp fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-range fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-msgid-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-msgid session archive field token legacyp fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-msgid fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-command session archive args legacyp fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-command fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-hdr-current-effects-exclude-submit fn-pacc-nntp-hdr-range-effects-exclude-submit fn-pacc-nntp-hdr-msgid-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-response session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-response fn-pacc-nntp-hdr-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xhdr-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xhdr-response session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xhdr-response fn-pacc-nntp-hdr-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xpat-range-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xpat-range session archive field patterns token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xpat-range fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xpat-msgid-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xpat-msgid session archive field patterns token fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xpat-msgid fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xpat-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xpat-response session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xpat-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-xpat-range-effects-exclude-submit fn-pacc-nntp-xpat-msgid-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-newgroups-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-newgroups-response session archive env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-newgroups-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-newnews-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-newnews-response session archive env args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-newnews-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-archive-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-archive-command session archive env keyword args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-archive-command fn-pacc-nntp-group-result-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-listgroup-command-effects-exclude-submit fn-pacc-nntp-list-command-effects-exclude-submit fn-pacc-nntp-next-or-last-effects-exclude-submit fn-pacc-nntp-retrieval-effects-exclude-submit fn-pacc-nntp-over-response-effects-exclude-submit fn-pacc-nntp-xover-response-effects-exclude-submit fn-pacc-nntp-hdr-response-effects-exclude-submit fn-pacc-nntp-xhdr-response-effects-exclude-submit fn-pacc-nntp-xpat-response-effects-exclude-submit fn-pacc-nntp-newgroups-response-effects-exclude-submit fn-pacc-nntp-newnews-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-command session archive env tokens fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-command fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-session-command-effects-exclude-submit fn-pacc-nntp-archive-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-step session archive env wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-step fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-post-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-nntp-post-step ps archive config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-post-step fn-pacc-post-single-effects-exclude-submit fn-pacc-nntp-step-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-cu-serve-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-cu-serve-reply session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-cu-serve-reply fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-withdrawn-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-withdrawn-reply session msgidp)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-withdrawn-reply fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-zar-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-zar-command session archive args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-zar-command fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-nntp-msgid-retrieval-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-list-overview-fmt-served-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-list-overview-fmt-served session)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-list-overview-fmt-served fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-range-served-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-range-served session buckets arts token legacyp server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-range-served fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-current-served-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-current-served session archive server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-current-served fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-msgid-served-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-msgid-served session archive token server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-msgid-served fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xref-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xref-reply session archive index env keyword args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xref-reply fn-pacc-nntp-list-overview-fmt-served-effects-exclude-submit fn-pacc-nntp-over-range-served-effects-exclude-submit fn-pacc-nntp-over-current-served-effects-exclude-submit fn-pacc-nntp-over-msgid-served-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-gidx-list-counts-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-gidx-list-counts-command session archive buckets closed args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-gidx-list-counts-command fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-newgroups-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-newgroups session archive env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-newgroups fn-pacc-nntp-newgroups-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-active-times-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-active-times session archive env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-active-times fn-pacc-nntp-list-active-times-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-subscriptions-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-subscriptions session archive env args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-subscriptions fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-article-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-article-reply session article number kind updatep group server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-article-reply fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-retrieval-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-retrieval session archive arts kind args server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-retrieval fn-pacc-nntp-single-effects-exclude-submit fn-pacc-rcompat-article-reply-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-hdr-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-hdr session archive arts args legacyp server fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-hdr fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-reply session archive index env keyword args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-reply fn-pacc-rcompat-newgroups-effects-exclude-submit fn-pacc-rcompat-active-times-effects-exclude-submit fn-pacc-rcompat-subscriptions-effects-exclude-submit fn-pacc-rcompat-retrieval-effects-exclude-submit fn-pacc-rcompat-hdr-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-gidx-listgroup-result-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-gidx-listgroup-result session archive buckets group range)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-gidx-listgroup-result fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-gidx-listgroup-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-gidx-listgroup-command session archive buckets args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-gidx-listgroup-command fn-pacc-nntp-single-effects-exclude-submit fn-pacc-gidx-listgroup-result-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-range-indexed-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-range-indexed session buckets arts token legacyp fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-range-indexed fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-current-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-current session archive verdicts)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-current fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-range-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-range session archive verdicts token)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-range fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-msgid-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-msgid session archive verdicts token)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-msgid fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-response session archive verdicts args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-verdict-hdr-current-effects-exclude-submit fn-pacc-nntp-verdict-hdr-range-effects-exclude-submit fn-pacc-nntp-verdict-hdr-msgid-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-control-hdr-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-control-hdr-response session archive index verdicts args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-control-hdr-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-enrollment-hdr-response-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-enrollment-hdr-response session archive index verdicts args)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-enrollment-hdr-response fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-archive-command-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-archive-command-pinned session archive index verdicts env keyword args fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-archive-command-pinned fn-pacc-nntp-xref-reply-effects-exclude-submit fn-pacc-gidx-list-counts-command-effects-exclude-submit fn-pacc-nntp-withdrawn-reply-effects-exclude-submit fn-pacc-rcompat-reply-effects-exclude-submit fn-pacc-nntp-msgid-retrieval-effects-exclude-submit fn-pacc-gidx-listgroup-command-effects-exclude-submit fn-pacc-nntp-over-range-indexed-effects-exclude-submit fn-pacc-nntp-verdict-hdr-response-effects-exclude-submit fn-pacc-nntp-control-hdr-response-effects-exclude-submit fn-pacc-nntp-enrollment-hdr-response-effects-exclude-submit fn-pacc-nntp-archive-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-command-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-command-pinned session archive index verdicts env tokens fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-command-pinned fn-pacc-nntp-single-effects-exclude-submit fn-pacc-cu-serve-reply-effects-exclude-submit fn-pacc-nntp-withdrawn-reply-effects-exclude-submit fn-pacc-zar-command-effects-exclude-submit fn-pacc-nntp-session-command-effects-exclude-submit fn-pacc-nntp-archive-command-pinned-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-step-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-step-pinned session archive index verdicts env wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-step-pinned fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-command-pinned-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-post-step-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-nntp-post-step-pinned ps archive index verdicts config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-post-step-pinned fn-pacc-nntp-post-step-effects-exclude-submit fn-pacc-nntp-step-pinned-effects-exclude-submit fn-pacc-post-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-peer-delegate-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-peer-delegate-pinned ps archive index verdicts config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-peer-delegate-pinned fn-pacc-nntp-post-step-pinned-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-peer-echo-reply-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-peer-echo-reply code-text msgid))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-peer-echo-reply  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-peer-single-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-peer-single ps text))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-peer-single fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-peer-transfer-unreceived-effects-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-peer-transfer-unreceived-effects ps transfer wire-event))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-peer-transfer-unreceived-effects fn-pacc-peer-single-effects-exclude-submit fn-pacc-peer-echo-reply-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-pgc-transfer-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-pgc-transfer-step ps wire-event)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-transfer-step fn-pacc-peer-echo-reply-effects-exclude-submit fn-pacc-peer-transfer-unreceived-effects-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-pgc-peer-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-pgc-peer-command ps keyword args arts)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-peer-command fn-pacc-peer-single-effects-exclude-submit fn-pacc-peer-echo-reply-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-pgc-peer-arm-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-pgc-peer-arm ps arts archive index verdicts config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pgc-peer-arm fn-pacc-peer-delegate-pinned-effects-exclude-submit fn-pacc-pgc-transfer-step-effects-exclude-submit fn-pacc-pgc-peer-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-scar-peer-step-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-scar-peer-step-pinned ps live arts archive index verdicts config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-peer-step-pinned fn-pacc-peer-delegate-pinned-effects-exclude-submit fn-pacc-pgc-peer-arm-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-scar-auth-delegate-pinned-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-scar-auth-delegate-pinned as live arts archive index verdicts config observation injection wire-event fn-arena)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-auth-delegate-pinned fn-pacc-scar-peer-step-pinned-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-nntp-group-result-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-av-nntp-group-result-cat session archive group v fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-nntp-group-result-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-nntp-listgroup-result-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-av-nntp-listgroup-result-cat session archive group range v fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-nntp-listgroup-result-cat fn-pacc-nntp-multi-octets-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-nntp-listgroup-command-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-av-nntp-listgroup-command-cat session archive args v fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-nntp-listgroup-command-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-av-nntp-listgroup-result-cat-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-nntp-next-or-last-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-av-nntp-next-or-last-cat session archive direction v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-nntp-next-or-last-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-next-or-last-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-retrieval-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-retrieval-cat session archive arts kind args server v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-retrieval-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-rcompat-article-reply-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-range-ovw-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-range-ovw session v token src fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-range-ovw  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-hdr-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-hdr-cat session archive arts args legacyp server v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-hdr-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-hdr-range-ovw-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-rcompat-reply-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-rcompat-reply-cat session archive index env keyword args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rcompat-reply-cat fn-pacc-rcompat-retrieval-cat-effects-exclude-submit fn-pacc-rcompat-hdr-cat-effects-exclude-submit fn-pacc-rcompat-reply-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-msgid-retrieval-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-msgid-retrieval-cat session v kind token fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-msgid-retrieval-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-number-retrieval-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-number-retrieval-cat session v kind token fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-number-retrieval-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-current-retrieval-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-current-retrieval-cat session kind v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-current-retrieval-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-article-response-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-range-ovw-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-range-ovw session v token legacyp server fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-range-ovw  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-current-served-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-current-served-cat session server v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-current-served-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-over-msgid-served-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-over-msgid-served-cat session token server v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-over-msgid-served-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xref-reply-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xref-reply-cat session archive index env keyword args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xref-reply-cat fn-pacc-nntp-list-overview-fmt-served-effects-exclude-submit fn-pacc-nntp-over-range-ovw-effects-exclude-submit fn-pacc-nntp-over-current-served-cat-effects-exclude-submit fn-pacc-nntp-over-msgid-served-cat-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-current-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-current-cat session verdicts v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-current-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-range-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-range-cat session verdicts token v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-range-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-msgid-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-msgid-cat session verdicts token v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-msgid-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-verdict-hdr-response-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-verdict-hdr-response-cat session verdicts args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-verdict-hdr-response-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-verdict-hdr-current-cat-effects-exclude-submit fn-pacc-nntp-verdict-hdr-range-cat-effects-exclude-submit fn-pacc-nntp-verdict-hdr-msgid-cat-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-control-hdr-response-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-control-hdr-response-cat session archive index verdicts args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-control-hdr-response-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-enrollment-hdr-response-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-enrollment-hdr-response-cat session index verdicts args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-enrollment-hdr-response-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-hdr-command-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-hdr-command-cat session args v legacyp fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-hdr-command-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-nntp-hdr-range-ovw-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-xpat-response-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-xpat-response-cat session args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-xpat-response-cat fn-pacc-nntp-single-effects-exclude-submit fn-pacc-nntp-hdr-range-ovw-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-lst-result-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-lst-result session archive closed statusp countsp patterns filteredp v)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lst-result  fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-lst-counts-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-lst-counts-command session archive closed args v fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lst-counts-command fn-pacc-lst-result-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-lst-active-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-lst-active-command session archive closed args v fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lst-active-command fn-pacc-lst-result-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-nntp-newnews-response-stream-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-nntp-newnews-response-stream fn-pacc-nntp-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-proto-archive-command-available-cat-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-proto-archive-command-available-cat session archive index verdicts env keyword args v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-proto-archive-command-available-cat fn-pacc-av-nntp-group-result-cat-effects-exclude-submit fn-pacc-nntp-single-effects-exclude-submit fn-pacc-av-nntp-listgroup-command-cat-effects-exclude-submit fn-pacc-nntp-archive-command-effects-exclude-submit fn-pacc-av-nntp-next-or-last-cat-effects-exclude-submit fn-pacc-nntp-withdrawn-reply-effects-exclude-submit fn-pacc-rcompat-reply-cat-effects-exclude-submit fn-pacc-nntp-msgid-retrieval-cat-effects-exclude-submit fn-pacc-nntp-number-retrieval-cat-effects-exclude-submit fn-pacc-nntp-current-retrieval-cat-effects-exclude-submit fn-pacc-nntp-xref-reply-cat-effects-exclude-submit fn-pacc-nntp-over-range-ovw-effects-exclude-submit fn-pacc-nntp-verdict-hdr-response-cat-effects-exclude-submit fn-pacc-nntp-control-hdr-response-cat-effects-exclude-submit fn-pacc-nntp-enrollment-hdr-response-cat-effects-exclude-submit fn-pacc-nntp-hdr-command-cat-effects-exclude-submit fn-pacc-nntp-xpat-response-cat-effects-exclude-submit fn-pacc-lst-counts-command-effects-exclude-submit fn-pacc-lst-active-command-effects-exclude-submit fn-pacc-nntp-newnews-response-stream-effects-exclude-submit fn-pacc-nntp-archive-command-pinned-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-scr-command-available-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-scr-command-available session archive index verdicts env tokens v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scr-command-available fn-pacc-nntp-single-effects-exclude-submit fn-pacc-cu-serve-reply-effects-exclude-submit fn-pacc-nntp-withdrawn-reply-effects-exclude-submit fn-pacc-zar-command-effects-exclude-submit fn-pacc-nntp-session-command-effects-exclude-submit fn-pacc-proto-archive-command-available-cat-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-nntp-result-effects (fn-av-scr-step session archive index verdicts env wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-step fn-pacc-nntp-single-effects-exclude-submit fn-pacc-scr-command-available-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-post-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-post-step ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-post-step fn-pacc-nntp-post-step-effects-exclude-submit fn-pacc-av-scr-step-effects-exclude-submit fn-pacc-post-single-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-peer-delegate-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-peer-delegate ps archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-delegate fn-pacc-av-scr-post-step-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-scr-peer-command-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-scr-peer-command ps keyword args lver arts fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scr-peer-command fn-pacc-peer-single-effects-exclude-submit fn-pacc-peer-echo-reply-effects-exclude-submit fn-pacc-nntp-multi-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-peer-arm-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-peer-arm ps lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-arm fn-pacc-av-scr-peer-delegate-effects-exclude-submit fn-pacc-pgc-transfer-step-effects-exclude-submit fn-pacc-scr-peer-command-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-peer-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-peer-step ps live lver arts archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-peer-step fn-pacc-av-scr-peer-delegate-effects-exclude-submit fn-pacc-av-scr-peer-arm-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-auth-delegate-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-auth-delegate as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-auth-delegate fn-pacc-scar-peer-step-pinned-effects-exclude-submit fn-pacc-scar-auth-delegate-pinned-effects-exclude-submit fn-pacc-av-scr-peer-step-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(local (defthm fn-pacc-av-scr-auth-step-effects-exclude-submit
 (fn-pacc-non-submit-effectsp (fn-post-result-effects (fn-av-scr-auth-step as live lver arts cache archive index verdicts config observation injection wire-event v fn-arena fn-cat)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-auth-step fn-pacc-auth-tls-established-effects-exclude-submit fn-pacc-auth-redeem-outcome-effects-exclude-submit fn-pacc-auth-install-context-effects-exclude-submit fn-pacc-auth-sasl-continue-effects-exclude-submit fn-pacc-auth-command-effects-exclude-submit fn-pacc-av-scr-auth-delegate-effects-exclude-submit fn-pacc-non-submit-effectsp fn-pacc-non-submit-effectsp-append
 fn-pacc-nntp-result-effects-of-make-by-definition fn-post-result-effects-of-fn-post-make-result
 fn-lst-effect fn-ovw-cursor-effect fn-nntp-reply-effect fn-nntp-close-effect fn-nntp-begin-article-effect fn-auth-starttls-effect
 fn-ag-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart consp)
 (:executable-counterpart car) (:executable-counterpart cdr) (:executable-counterpart fn-pacc-non-submit-effectsp) (:executable-counterpart fn-post-result-effects) (:executable-counterpart fn-nntp-result-effects) fn-auth-starttls-effect fn-lst-effect fn-nntp-begin-article-effect fn-nntp-close-effect fn-nntp-reply-effect fn-nnw-meta-effect fn-ovw-cursor-effect))))))

(defthm fn-pacc-av-dispatch-core-carries-read-effects-and-headers
 (let ((r (fn-av-scr-dispatch-core conn event live lver arts cache fn-arena fn-cat)))
  (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
       (fn-pacc-effects-readp (fn-served-result-effects r)
                             (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-dispatch-core fn-served-result-conn-of-fn-served-make-result
 fn-served-result-effects-of-fn-served-make-result fn-served-conn-fields-of-make-conn-live
 fn-pacc-effects-readp-append fn-pacc-non-submit-effects-have-readp-by-definition
 fn-pacc-av-scr-auth-step-effects-exclude-submit fn-pacc-av-scr-auth-step-read-origin
 fn-pacc-one-submit-has-readp-by-definition fn-pacc-empty-effects-have-readp-by-definition)))))

(defthm fn-pacc-av-dispatch-core-read-effects-at-header-limits
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
          (fn-pacc-effects-readp
           (fn-served-result-effects (fn-av-scr-dispatch-core conn event live lver arts cache fn-arena fn-cat)) h))
 :hints (("Goal" :use ((:instance fn-pacc-av-dispatch-core-carries-read-effects-and-headers))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-scr-repin-keeps-config
 (equal (fn-served-conn-config (fn-scr-repin conn fn-cat)) (fn-served-conn-config conn))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scr-repin fn-served-conn-fields-of-make-conn-live)))))

(defthm fn-pacc-av-dispatch-carries-read-effects-and-headers
 (let ((r (fn-av-scr-dispatch conn event live lver arts cache fn-arena fn-cat)))
  (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
       (fn-pacc-effects-readp (fn-served-result-effects r)
                             (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-dispatch fn-pacc-av-dispatch-core-read-effects-at-header-limits fn-pacc-av-dispatch-core-carries-read-effects-and-headers
 fn-pacc-scr-repin-keeps-config fn-served-conn-fields-of-with-wire
 fn-served-result-conn-of-fn-served-make-result fn-served-result-effects-of-fn-served-make-result)))))

(defthm fn-pacc-av-dispatch-read-effects-at-header-limits
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let ((r (fn-av-scr-dispatch conn event live lver arts cache fn-arena fn-cat)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :use ((:instance fn-pacc-av-dispatch-carries-read-effects-and-headers))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-dispatch-events-carries-read-effects-and-headers
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let ((r (fn-av-scr-dispatch-events conn events live lver arts cache fn-arena fn-cat)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :induct (fn-av-scr-dispatch-events conn events live lver arts cache fn-arena fn-cat)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-dispatch-events fn-pacc-av-dispatch-read-effects-at-header-limits
 fn-pacc-av-dispatch-carries-read-effects-and-headers fn-pacc-effects-readp-append
 fn-pacc-empty-effects-have-readp-by-definition
 fn-served-result-conn-of-fn-served-make-result fn-served-result-effects-of-fn-served-make-result)))))

(defthm fn-pacc-av-dispatch-events-keeps-config
 (equal (fn-served-conn-config (fn-served-result-conn
         (fn-av-scr-dispatch-events conn events live lver arts cache fn-arena fn-cat)))
        (fn-served-conn-config conn))
 :hints (("Goal" :use ((:instance fn-pacc-av-dispatch-events-carries-read-effects-and-headers
                      (h (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-feed-byte-carries-read-effects-and-headers
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let ((r (fn-av-scr-feed-byte conn byte live lver arts cache fn-arena fn-cat)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-feed-byte fn-pacc-av-dispatch-events-keeps-config fn-pacc-av-dispatch-events-carries-read-effects-and-headers
 fn-served-conn-fields-of-with-wire)))))

(local (defthm fn-pacc-counted-result-of-make-by-definition
 (equal (fn-served-counted-result (fn-served-counted-make consumed result)) result)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-served-counted-result fn-served-counted-make fn-ag-car fn-ag-cdr car-cons cdr-cons
 (:executable-counterpart consp)))))))

(defthm fn-pacc-av-feed-byte-keeps-config
 (equal (fn-served-conn-config (fn-served-result-conn
         (fn-av-scr-feed-byte conn byte live lver arts cache fn-arena fn-cat)))
        (fn-served-conn-config conn))
 :hints (("Goal" :use ((:instance fn-pacc-av-feed-byte-carries-read-effects-and-headers
                      (h (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-feed-span-carries-read-effects-and-headers
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let* ((counted (fn-av-scr-feed-span conn i end live lver arts cache fn-octets fn-arena fn-cat))
         (r (fn-served-counted-result counted)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :induct (fn-av-scr-feed-span conn i end live lver arts cache fn-octets fn-arena fn-cat)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-feed-span fn-pacc-av-feed-byte-carries-read-effects-and-headers
 fn-pacc-effects-readp-append fn-pacc-empty-effects-have-readp-by-definition
 fn-pacc-counted-result-of-make-by-definition fn-pacc-av-feed-byte-keeps-config
 fn-served-result-conn-of-fn-served-make-result fn-served-result-effects-of-fn-served-make-result
 car-cons cdr-cons (:executable-counterpart consp))))))

(defthm fn-pacc-av-feed-span-keeps-config
 (equal (fn-served-conn-config (fn-served-result-conn (fn-served-counted-result
         (fn-av-scr-feed-span conn i end live lver arts cache fn-octets fn-arena fn-cat))))
        (fn-served-conn-config conn))
 :hints (("Goal" :use ((:instance fn-pacc-av-feed-span-carries-read-effects-and-headers
                      (h (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-step-core-carries-read-effects-and-headers
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let* ((counted (fn-av-scr-step-span-core conn i end live lver arts cache fn-octets fn-arena fn-cat))
         (r (fn-served-counted-result counted)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-step-span-core fn-pacc-av-feed-span-carries-read-effects-and-headers
 fn-pacc-av-feed-span-keeps-config fn-pacc-counted-result-of-make-by-definition
 fn-served-result-conn-of-fn-served-make-result fn-served-result-effects-of-fn-served-make-result
 fn-pacc-effects-readp-append fn-pacc-non-submit-effects-have-readp-by-definition
 fn-nntp-close-effect (:executable-counterpart fn-pacc-non-submit-effectsp))))))

(defthm fn-pacc-av-step-core-keeps-config
 (equal (fn-served-conn-config (fn-served-result-conn (fn-served-counted-result
         (fn-av-scr-step-span-core conn i end live lver arts cache fn-octets fn-arena fn-cat))))
        (fn-served-conn-config conn))
 :hints (("Goal" :use ((:instance fn-pacc-av-step-core-carries-read-effects-and-headers
                      (h (fn-inj-config-header-limits (fn-served-conn-config conn)))))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-av-step-fast-carries-read-effects-and-headers
 (implies (equal (fn-inj-config-header-limits (fn-served-conn-config conn)) h)
  (let* ((counted (fn-av-scr-step-span-fast conn i end live lver arts cache fn-octets fn-arena fn-cat))
         (r (fn-served-counted-result counted)))
   (and (equal (fn-served-conn-config (fn-served-result-conn r)) (fn-served-conn-config conn))
        (fn-pacc-effects-readp (fn-served-result-effects r) h))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-step-span-fast fn-pacc-av-step-core-carries-read-effects-and-headers
 fn-pacc-av-step-core-keeps-config fn-pacc-counted-result-of-make-by-definition
 fn-served-result-conn-of-fn-served-make-result fn-served-result-effects-of-fn-served-make-result
 fn-pacc-empty-effects-have-readp-by-definition)))))

(defthm fn-pacc-own-tls-served-conn-keeps-header-limits
 (equal (fn-inj-config-header-limits (fn-served-conn-config (fn-own-tls-served-conn o conn)))
        (fn-inj-config-header-limits (fn-own-conn-config conn)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-tls-served-conn fn-own-served-conn fn-served-conn-fields-of-make-conn-live
 fn-gac-config-with-live-fields)))))

(defthm fn-pacc-sub-readp-rebinds-take-inputs-at-item-triple (implies (and (fn-pacc-sub-readp sub secret0 cfg0 carry0 read-limits) (fn-apc-p carry1)) (fn-pacc-sub-readp sub secret1 cfg1 carry1 read-limits))
 :hints (("Goal" :use fn-pacc-sub-readp-rebinds-take-inputs :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-every-connection-reads-own-headers
 (fn-pacc-conn-reads-own-headersp o c)
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'minimal-theory)
 '(fn-pacc-conn-reads-own-headersp fn-own-served-conn
 fn-served-conn-fields-of-make-conn-live
 fn-pacc-effective-read-config-keeps-pin-header-limits)))))

(defthm fn-pacc-every-connection-list-reads-own-headers
 (fn-pacc-conns-read-own-headersp o conns)
 :hints (("Goal" :induct (len conns) :in-theory
 (union-theories (theory 'minimal-theory)
 '(fn-pacc-conns-read-own-headersp fn-pacc-every-connection-reads-own-headers len)))))

(defthm fn-pacc-every-owner-pin-reads-own-headers
 (fn-pacc-pins-read-own-headersp o)
 :hints (("Goal" :in-theory (enable fn-pacc-pins-read-own-headersp))))

(defthm fn-pacc-open-pins-current-owner-header-triple (implies (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o))) (let ((pin (fn-own-conn-config (car (fn-own-conns (cdr (fn-own-open o acfg))))))) (and (equal pin (fn-own-config o)) (equal (fn-inj-config-header-limits pin) (fn-inj-config-header-limits (fn-own-config o))))))
 :hints (("Goal" :in-theory (enable fn-own-open fn-own-conns fn-own-make fn-own-conn-config fn-own-conn-make-group-indexed))))

(defthm fn-pacc-live-apply-installs-new-headers-and-frames-connections (mv-let (verdict next) (fn-osb-install o profile) (implies (equal verdict :installed) (and (equal (fn-inj-config-header-limits (fn-own-config next)) (fn-bs-profile-header-limits profile)) (equal (fn-own-conns next) (fn-own-conns o)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-osb-install fn-own-configure fn-own-conns-of-fn-own-make fn-own-config-of-fn-own-make fn-osb-config fn-inj-config-header-limits fn-inj-make-config-full fn-inj-post-bound fn-inj-bound-header-limits fn-inj-nth fn-inj-car fn-inj-cdr fn-osb-install-serves-the-profile-header-limits mv-nth nfix zp car-cons cdr-cons)))))

(local (defthm fn-pacc-distinct-triples-within-list
 (<= (len (fn-pacc-pinned-header-triples conns)) (len conns))
 :hints (("Goal" :induct (len conns) :in-theory (enable fn-pacc-pinned-header-triples)))))

(defthm fn-pacc-distinct-pinned-header-triples-bounded-by-connections (<= (len (fn-pacc-pinned-header-triples (fn-own-conns o))) (len (fn-own-conns o)))
 :hints (("Goal" :in-theory (enable fn-pacc-distinct-triples-within-list))))

(defthm fn-pacc-distinct-pinned-header-triples-bounded-by-cap (implies (<= (len (fn-own-conns o)) (nfix (fn-own-max-conns o))) (<= (len (fn-pacc-pinned-header-triples (fn-own-conns o))) (nfix (fn-own-max-conns o))))
 :hints (("Goal" :use fn-pacc-distinct-pinned-header-triples-bounded-by-connections
 :in-theory (union-theories (theory 'minimal-theory)
 '((:type-prescription len) nfix)))))

(defthm fn-pacc-own-make-carries-profile-headers (implies (fn-pacc-conns-read-own-headersp (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused) conns) (fn-pacc-pins-read-own-headersp (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-asto-with-conn-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc)) (fn-pacc-conn-reads-own-headersp (fn-ocfg-owner oc) conn)) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-asto-with-conn oc conn))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-crf-with-store-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-crf-with-store o s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oclc-publish-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (mv-nth 1 (fn-oclc-publish oc generation (fn-inj-post-bound (fn-sbud-payload-bound profile) (fn-bs-profile-header-limits profile)))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ocl-owner-with-store-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-ocl-owner-with-store o st)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ocl-publish-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (mv-nth 1 (fn-ocl-publish oc generation (fn-inj-post-bound (fn-sbud-payload-bound profile) (fn-bs-profile-header-limits profile)))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ccp-owner-with-approved-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ccp-owner-with-approved oc approved))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-irc-rix-own-complete-enabled-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-irc-rix-own-complete-enabled o fn-hist carry)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-irc-ocfg-prepare-identity-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-irc-ocfg-prepare-identity oc event carry))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-acar-own-advance-result-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-acar-own-advance-result o id))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-acar-own-outcome-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-acar-own-outcome o id word))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oas-owner-closed-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-oas-owner-closed oc id))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ocln-owner-at-line-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ocln-owner-at-line oc id))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ccar-own-complete-enabled-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-ccar-own-complete-enabled o)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ccar-ocfg-prepare-identity-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-ccar-ocfg-prepare-identity oc event))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ocar-own-open-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-ocar-own-open o acfg))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ocar-own-reader-context-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-ocar-own-reader-context o id cfg)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oct-outcome-next-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-oct-outcome-next o id sub completion icar carry feeds)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oct-transit-next-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-oct-transit-next o id conn sub completion kind reason feeds)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oop-outcome-next-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-oop-outcome-next o id sub completion icar carry)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oop-transit-next-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-oop-transit-next o id conn sub completion kind reason)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-pcar-opc-owner-prepare-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-pcar-opc-owner-prepare o record)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-opc-owner-prepare-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-opc-owner-prepare o record)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-psrv-prepare-topic-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-psrv-prepare-topic oc event))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-with-view-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-with-view o v)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-orcp-swap-base-keeps-profile-headers (fn-pacc-pins-read-own-headersp (fn-orcp-swap-base live rebuilt))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-orcp-swapped-owner-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp live)) (fn-pacc-pins-read-own-headersp (fn-orcp-swapped-owner live rebuilt)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-refresh-ix-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-refresh-ix o fn-hist)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-rix-own-complete-enabled-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-rix-own-complete-enabled o fn-hist)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-osb-install-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (mv-nth 1 (fn-osb-install o profile))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-scar-finish-read-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o) (fn-pacc-conn-reads-own-headersp o conn)) (fn-pacc-pins-read-own-headersp (cdr (fn-scar-finish-read o conn result live))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-scar-own-read-step-full-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cadr (fn-scar-own-read-step-full o id event fn-arena))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-otm-owner-with-allow-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-otm-owner-with-allow oc id allow))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-otm-ocfg-with-refused-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (fn-otm-ocfg-with-refused oc mem))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-refresh-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-refresh o)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-set-conns-keeps-profile-headers (implies (fn-pacc-conns-read-own-headersp o conns) (fn-pacc-pins-read-own-headersp (fn-own-set-conns o conns)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-reader-context-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-reader-context o id cfg)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-open-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-open o acfg))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-open-peer-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-open-peer o peer cfg acfg))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-enqueue-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-enqueue o sub)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-finish-read-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o) (fn-pacc-conn-reads-own-headersp o conn)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-finish-read o conn result))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-read-step-full-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cadr (fn-own-read-step-full o id event fn-arena))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-advance-result-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-advance-result o id))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-close-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-close o id)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-begin-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-begin o id)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-store-step-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-store-step o event)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-complete-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-complete o)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-reopen-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-reopen o frontier records)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-observe-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-observe o obs)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-declare-group-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-declare-group o name)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-with-feeds-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-with-feeds o feeds)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-configure-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (fn-own-configure o config)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-with-node-secret-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-with-node-secret o secret)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-take-submission-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-take-submission o)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-outcome-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-outcome o id word))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-control-outcome-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-own-control-outcome o word)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-transit-outcome-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-own-transit-outcome o id kind reason word))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-own-step-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (fn-own-step o event fn-arena)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-pidx-opc-owner-prepare-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-pidx-opc-owner-prepare o record)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ppc-opc-owner-prepare-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-ppc-opc-owner-prepare o record dup carry)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-prc-opc-owner-prepare-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-prc-opc-owner-prepare o record carry)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-rcon-own-store-io-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (fn-rcon-own-store-io o operation result)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-ordinary-configure-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (fn-own-configure o (fn-oag-post-config cfg (fn-inj-post-bound (fn-sbud-payload-bound profile) (fn-bs-profile-header-limits profile))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-posting-configure-logical-core-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (fn-own-configure o (fn-inj-make-config-full allow (fn-inj-config-agent (fn-own-config o)) (fn-inj-config-groups (fn-own-config o)) (fn-inj-post-bound (fn-sbud-payload-bound profile) (fn-bs-profile-header-limits profile)) (fn-inj-config-listing (fn-own-config o)) (fn-inj-config-closed (fn-own-config o))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-live-limit-logical-core-keeps-profile-headers (implies (fn-pacc-pins-read-own-headersp o) (fn-pacc-pins-read-own-headersp (mv-nth 1 (fn-osb-install o (fn-lim-apply-row profile field n)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-host-open-core-keeps-profile-headers (implies (and (fn-pacc-pins-read-own-headersp (fn-ocfg-owner oc))) (fn-pacc-pins-read-own-headersp (fn-ocfg-owner (cdr (fn-ocar-ocfg-open oc acfg)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-oct-control-keeps-profile-headers-owner-projection (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (car (fn-oct-control o word pending))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-apc-own-outcome-keeps-profile-headers-owner-projection (implies (and (fn-pacc-pins-read-own-headersp o)) (fn-pacc-pins-read-own-headersp (cdr (fn-apc-own-outcome o id word icar carry))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

(defthm fn-pacc-profile-install-core-establishes-pins-when-unconnected (implies (and (fn-bs-profile-admittedp profile) (not (consp (fn-own-conns o)))) (fn-pacc-pins-read-own-headersp (mv-nth 1 (fn-osb-install o profile))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-every-owner-pin-reads-own-headers)))))

; Approved v4 composition.
(defthm fn-pacc-profile-witness-establishes-item-read
 (implies (fn-pacc-sub-read-at-profilep sub secret cfg carry profile)
 (fn-pacc-item-sub-readp sub secret cfg carry))
 :hints (("Goal" :use ((:instance fn-pacc-item-sub-readp-suff (take-config cfg) (parse-carry carry) (item-profile profile)))
 :in-theory (theory 'minimal-theory))))

(defthm fn-pacc-enqueue-from-pin-establishes-item-read (implies (fn-pacc-pin3-enqueue-read-premisep sub secret take-config parse-carry pin c art icfg iclock) (and (fn-pacc-sub-readp sub secret take-config parse-carry (fn-bs-profile-header-limits pin)) (fn-pacc-sub-read-at-profilep sub secret take-config parse-carry pin) (fn-pacc-item-sub-readp sub secret take-config parse-carry)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-read-body-establishes-readp (read-limits (fn-bs-profile-header-limits pin))) (:instance fn-pacc-profile-witness-establishes-item-read (profile pin) (cfg take-config) (carry parse-carry))) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-pin3-enqueue-read-premisep fn-pacc-sub-read-at-profilep)))))

(local (defthm fn-pacc-install-owner-work-frame
 (and (equal (fn-own-conns (mv-nth 1 (fn-osb-install o profile))) (fn-own-conns o))
      (equal (fn-own-queue (mv-nth 1 (fn-osb-install o profile))) (fn-own-queue o))
      (equal (fn-own-inflight (mv-nth 1 (fn-osb-install o profile))) (fn-own-inflight o)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-osb-install fn-own-configure fn-own-conns-of-fn-own-make
 fn-own-queue-of-fn-own-make fn-own-inflight-of-fn-own-make mv-nth car-cons cdr-cons))))))

(defthm fn-pacc-live-apply-frames-local-items (mv-let (verdict next) (fn-osb-install o profile) (declare (ignore verdict)) (and (equal (fn-own-queue next) (fn-own-queue o)) (equal (fn-own-inflight next) (fn-own-inflight o)) (equal (fn-pacc-queue-readp (fn-own-queue next) secret take-config parse-carry) (fn-pacc-queue-readp (fn-own-queue o) secret take-config parse-carry)) (equal (fn-pacc-inflight-readp (fn-own-inflight next) secret take-config parse-carry) (fn-pacc-inflight-readp (fn-own-inflight o) secret take-config parse-carry))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-install-owner-work-frame)))))

(local (defthm fn-pacc-item-queue-append
 (equal (fn-pacc-queue-readp (append q (list packed)) secret cfg carry)
 (and (fn-pacc-queue-readp q secret cfg carry)
      (fn-pacc-local-sub-readp (fn-psub-unpack-sub packed) secret cfg carry)))
 :hints (("Goal" :induct (fn-pacc-queue-readp q secret cfg carry)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-queue-readp binary-append car-cons cdr-cons
 (:type-prescription fn-pacc-local-sub-readp) (:type-prescription fn-pacc-queue-readp)))))))

(defthm fn-pacc-enqueue-carries-sub-readp (implies (and (fn-pacc-item-sub-readp sub secret take-config parse-carry) (fn-pacc-queue-readp (fn-own-queue o) secret take-config parse-carry)) (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue o sub)) secret take-config parse-carry))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-own-enqueue fn-own-queue fn-own-make fn-ag-append fn-pacc-item-queue-append fn-pacc-local-sub-readp fn-psub-unpack-of-pack-sub car-cons cdr-cons)))))

(defthm fn-pacc-item-sub-readp-rebinds-take-inputs (implies (and (fn-pacc-item-sub-readp sub secret0 cfg0 carry0) (fn-apc-p carry1)) (fn-pacc-item-sub-readp sub secret1 cfg1 carry1))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-sub-readp-rebinds-take-inputs (read-limits (fn-bs-profile-header-limits (fn-pacc-item-sub-readp-witness sub secret0 cfg0 carry0)))) (:instance fn-pacc-profile-witness-establishes-item-read (secret secret1) (cfg cfg1) (carry carry1) (profile (fn-pacc-item-sub-readp-witness sub secret0 cfg0 carry0)))) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-item-sub-readp fn-pacc-sub-read-at-profilep)))))

(defthm fn-pacc-take-carries-sub-readp (let* ((o (fn-ocfg-owner oc)) (head (fn-psub-unpack-sub (car (fn-own-queue o)))) (next (fn-ocfg-step oc (list :take) fn-arena)) (after (fn-ocfg-owner next)) (sub (fn-own-inflight after)) (cfg (fn-ocfg-config next)) (secret (fn-own-node-secret after)) (tk (fn-apc-take cfg sub secret))) (implies (and (fn-arena-p fn-arena) (null (fn-ocfg-staged oc)) (null (fn-own-inflight o)) (consp (fn-own-queue o)) (null (fn-own-pending o)) (equal (fn-sf-phase (fn-sn-files (fn-own-store o))) :ready) (fn-pacc-item-sub-readp head secret cfg (cdr tk))) (and (fn-pacc-item-sub-readp sub secret cfg (cdr tk)) (fn-apc-p (cdr tk)) (equal (car tk) (fn-own-sub-stored-octets cfg sub secret)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-take-carries-sub-readp-at-item-triple (read-limits (fn-bs-profile-header-limits (fn-pacc-item-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))))))) (:instance fn-pacc-profile-witness-establishes-item-read (sub (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (secret (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))) (cfg (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena))) (carry (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena)))))) (profile (fn-pacc-item-sub-readp-witness (fn-psub-unpack-sub (car (fn-own-queue (fn-ocfg-owner oc)))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (cdr (fn-apc-take (fn-ocfg-config (fn-ocfg-step oc (list :take) fn-arena)) (fn-own-inflight (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))) (fn-own-node-secret (fn-ocfg-owner (fn-ocfg-step oc (list :take) fn-arena))))))))) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-item-sub-readp fn-pacc-sub-read-at-profilep)))))

(defthm fn-pacc-keyed-post-ok-implies-admitted-profile
 (implies (and (fn-pvc-carryp carry)
 (equal (fn-pak-post-admission carry profile msgid pl gc ch key fn-cat) :ok))
 (fn-bs-profile-admittedp profile))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pak-post-admission fn-pvc-post-boundary-carried fn-pvc-post-boundary fn-pvc-admittedp-is-the-verdict fn-pvc-pf fn-bs-profile-field fn-bs-profile-of fn-bs-pf fn-bs-meta-nth fn-pvc-post-boundary fn-pvc-admittedp posp natp)))))

(defthm fn-pacc-unsigned-arm-concludes-profile-admitted-postp (let* ((d (fn-own-sub-decision sub)) (filing (fn-ars-filing-plan (fn-inj-decision-groups d) boundary-domain fn-octets)) (names (fn-pacc-derived-names (fn-pctx-get 1 filing))) (codes (fn-store-codes-from-groups names boundary-domain))) (implies (and (fn-octets-p fn-octets) (fn-cat-p fn-cat) (fn-sn-statep s) (fn-pvc-carryp pcarry) (fn-apc-p parse-carry) (fn-pacc-sub-read-bodyp sub secret take-config parse-carry read-limits art icfg iclock) (equal (fn-octets-list fn-octets) (fn-own-sub-stored-octets take-config sub secret)) (equal read-limits (fn-bs-profile-header-limits profile)) (equal boundary-domain (fn-state-groups (fn-node-acceptance (fn-sn-node s)))) (equal (fn-ars-carrier-form fn-octets) :absent) (equal (fn-pak-post-admission pcarry profile (fn-inj-decision-msgid d) (fn-octets-len fn-octets) (len codes) (fn-charge-for-payload (fn-octets-len fn-octets)) key fn-cat) :ok)) (and (fn-pacc-profile-admitted-postp s art (fn-pacc-sub-inj sub secret take-config parse-carry icfg iclock) profile pcarry) (fn-pacc-item-sub-readp sub secret take-config parse-carry))))
 :hints (("Goal" :do-not-induct t :use (fn-pacc-unsigned-arm-concludes-profile-admitted-postp-at-item-triple (:instance fn-pacc-read-body-establishes-readp) (:instance fn-pacc-profile-witness-establishes-item-read (cfg take-config) (carry parse-carry)) (:instance fn-pacc-keyed-post-ok-implies-admitted-profile (carry pcarry) (msgid (fn-inj-decision-msgid (fn-own-sub-decision sub))) (pl (fn-octets-len fn-octets)) (gc (len (fn-store-codes-from-groups (fn-pacc-derived-names (fn-pctx-get 1 (fn-ars-filing-plan (fn-inj-decision-groups (fn-own-sub-decision sub)) boundary-domain fn-octets))) boundary-domain))) (ch (fn-charge-for-payload (fn-octets-len fn-octets))))) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-sub-read-at-profilep)))))

(defthm fn-pacc-unsigned-witness-concludes-profile-admitted-postp (let* ((d (fn-own-sub-decision sub)) (filing (fn-ars-filing-plan (fn-inj-decision-groups d) boundary-domain fn-octets)) (names (fn-pacc-derived-names (fn-pctx-get 1 filing))) (codes (fn-store-codes-from-groups names boundary-domain))) (implies (and (fn-octets-p fn-octets) (fn-cat-p fn-cat) (fn-sn-statep s) (fn-pvc-carryp pcarry) (fn-apc-p parse-carry) (fn-pacc-sub-readp sub secret take-config parse-carry read-limits) (equal (fn-octets-list fn-octets) (fn-own-sub-stored-octets take-config sub secret)) (equal read-limits (fn-bs-profile-header-limits profile)) (equal boundary-domain (fn-state-groups (fn-node-acceptance (fn-sn-node s)))) (equal (fn-ars-carrier-form fn-octets) :absent) (equal (fn-pak-post-admission pcarry profile (fn-inj-decision-msgid d) (fn-octets-len fn-octets) (len codes) (fn-charge-for-payload (fn-octets-len fn-octets)) key fn-cat) :ok)) (and (fn-pacc-profile-admitted-postp s (mv-nth 0 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)) (fn-pacc-sub-inj sub secret take-config parse-carry (mv-nth 1 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits)) (mv-nth 2 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) profile pcarry) (fn-pacc-item-sub-readp sub secret take-config parse-carry))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-unsigned-arm-concludes-profile-admitted-postp (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))) (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret take-config parse-carry read-limits))))) :in-theory (union-theories (theory 'minimal-theory) '(fn-pacc-sub-readp)))))

; Heterogeneous ER proof support: landing-er-normalize.lisp
(defconst *fn-pacc-wide-read-profile*
 (fn-lim-set-nth *fn-bs-pf-max-header-fields* *fn-article-max-octets*
  (fn-lim-set-nth *fn-bs-pf-max-header-lines* *fn-article-max-octets*
   (fn-lim-set-nth *fn-bs-pf-max-header-octets* *fn-article-max-octets* *fn-bs-profile-development*))))

(defthm fn-pacc-wide-read-profile-is-admitted
 (and (fn-bs-profile-admittedp *fn-pacc-wide-read-profile*)
      (equal (fn-bs-profile-header-limits *fn-pacc-wide-read-profile*) *fn-article-ceiling-limits*))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '((:executable-counterpart fn-bs-profile-admittedp) (:executable-counterpart fn-bs-profile-header-limits))))))

(defun fn-pacc-wide-read-config (cfg)
 (declare (xargs :guard t :verify-guards nil))
 (fn-inj-make-config-full (fn-inj-config-allow cfg) (fn-inj-config-agent cfg)
 (fn-inj-config-groups cfg) (fn-inj-post-bound (fn-inj-config-max-octets cfg) *fn-article-ceiling-limits*)
 (fn-inj-config-listing cfg) (fn-inj-config-closed cfg)))

(defthm fn-pacc-wide-read-config-fields
 (and (equal (fn-inj-config-allow (fn-pacc-wide-read-config cfg)) (fn-inj-config-allow cfg))
 (equal (fn-inj-config-agent (fn-pacc-wide-read-config cfg)) (fn-inj-config-agent cfg))
 (equal (fn-inj-config-groups (fn-pacc-wide-read-config cfg)) (fn-inj-config-groups cfg))
 (equal (fn-inj-config-max-octets (fn-pacc-wide-read-config cfg)) (fn-inj-config-max-octets cfg))
 (equal (fn-inj-config-listing (fn-pacc-wide-read-config cfg)) (fn-inj-config-listing cfg))
 (equal (fn-inj-config-closed (fn-pacc-wide-read-config cfg)) (fn-inj-config-closed cfg))
 (equal (fn-inj-config-header-limits (fn-pacc-wide-read-config cfg)) *fn-article-ceiling-limits*)
 (equal (fn-inj-configp (fn-pacc-wide-read-config cfg))
        (and (booleanp (fn-inj-config-allow cfg))
             (fn-cbor-octet-listp (fn-inj-config-agent cfg))
             (consp (fn-inj-config-agent cfg))
             (<= (len (fn-inj-config-agent cfg)) *fn-inj-max-agent-octets*)
             (fn-af-dot-atom-textp (fn-inj-config-agent cfg))
             (fn-inj-group-namesp (fn-inj-config-groups cfg))
             (posp (fn-inj-config-max-octets cfg))
             (<= (fn-inj-config-max-octets cfg) *fn-article-max-octets*))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-wide-read-config fn-inj-configp fn-inj-config-shapep fn-inj-make-config-full
 fn-inj-config-allow fn-inj-config-agent fn-inj-config-groups fn-inj-config-max-octets
 fn-inj-config-listing fn-inj-config-closed fn-inj-config-header-limits fn-inj-post-bound
 fn-inj-bound-octets fn-inj-bound-header-limits fn-inj-nth fn-inj-car fn-inj-cdr
 nfix zp len car-cons cdr-cons (:executable-counterpart consp) (:executable-counterpart true-listp))))))

(defthm fn-pacc-wide-read-config-keeps-validity
 (implies (fn-inj-configp cfg) (fn-inj-configp (fn-pacc-wide-read-config cfg)))
 :hints (("Goal" :in-theory (e/d (fn-inj-configp fn-pacc-wide-read-config-fields)
 (fn-pacc-wide-read-config fn-inj-config-allow fn-inj-config-agent fn-inj-config-groups fn-inj-config-max-octets)))))

(defthm fn-pacc-injection-has-readable-source-and-census
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
 (and (fn-article-result-okp (fn-article-parse source))
 (not (fn-article-census-refusal (fn-article-header-census source) (fn-inj-config-header-limits config)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-inj-decide fn-inj-injectedp fn-inj-refuse fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacc-readable-source-passes-wide-census
 (implies (fn-article-result-okp (fn-article-parse source))
 (not (fn-article-census-refusal (fn-article-header-census source) *fn-article-ceiling-limits*)))
 :hints (("Goal" :use ((:instance fn-article-census-refusal-is-the-parse
 (octets source) (limits *fn-article-ceiling-limits*)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-article-parse)))))

(defthm fn-pacc-injection-keeps-decision-at-wide-headers
 (implies (fn-inj-injectedp (fn-inj-decide source config obs))
 (equal (fn-inj-decide source (fn-pacc-wide-read-config config) obs) (fn-inj-decide source config obs)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-successful-injection-has-valid-inputs (art source) (icfg config) (iclock obs))
 (:instance fn-pacc-injection-has-readable-source-and-census)
 (:instance fn-pacc-readable-source-passes-wide-census))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-inj-decide fn-pacc-wide-read-config-fields fn-pacc-wide-read-config-keeps-validity
 fn-inj-generated-message-id fn-inj-refuse fn-inj-injectedp fn-inj-decision-status-of-fn-inj-make-decision)))))

; Heterogeneous ER proof support: landing-er-gated.lisp
(defthm fn-pacc-wide-read-config-keeps-group-gate
 (implies (fn-inj-configp cfg)
 (and (equal (fn-gst-post-gate source (fn-pacc-wide-read-config cfg)) (fn-gst-post-gate source cfg))
      (equal (fn-mod-facts source (fn-pacc-wide-read-config cfg)) (fn-mod-facts source cfg))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-gst-post-gate fn-mod-facts fn-pacc-wide-read-config-fields fn-pacc-wide-read-config-keeps-validity)))))

(defthm fn-pacc-wide-read-config-keeps-successful-forward
 (implies (fn-inj-injectedp (fn-mod-forward source config obs decision facts entry))
 (equal (fn-mod-forward source (fn-pacc-wide-read-config config) obs decision facts entry)
        (fn-mod-forward source config obs decision facts entry)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-mod-forward fn-pacc-wide-read-config-fields fn-pacc-injection-keeps-decision-at-wide-headers
 fn-inj-injectedp fn-inj-refuse fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacc-wide-read-config-keeps-successful-moderation
 (implies (and (fn-inj-configp config) (fn-inj-injectedp (fn-mod-gate source config obs decision)))
 (equal (fn-mod-gate source (fn-pacc-wide-read-config config) obs decision)
        (fn-mod-gate source config obs decision)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-mod-gate fn-pacc-wide-read-config-keeps-group-gate fn-pacc-wide-read-config-fields
 fn-pacc-wide-read-config-keeps-successful-forward fn-inj-injectedp fn-inj-refuse
 fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacc-gated-injection-keeps-decision-at-wide-headers
 (implies (fn-inj-injectedp (fn-post-gated-decision source config obs))
 (equal (fn-post-gated-decision source (fn-pacc-wide-read-config config) obs)
        (fn-post-gated-decision source config obs)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-post-gated-decision-is-the-decision-or-its-envelope (injection obs))
 (:instance fn-pacc-successful-gated-injection-has-valid-inputs (art source) (icfg config) (iclock obs)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-post-gated-decision fn-pacc-injection-keeps-decision-at-wide-headers
 fn-pacc-wide-read-config-keeps-group-gate fn-pacc-wide-read-config-keeps-successful-moderation
 fn-inj-injectedp fn-inj-refuse fn-inj-decision-status-of-fn-inj-make-decision)))))

(defthm fn-pacc-read-body-has-wide-profile-witness
 (implies (fn-pacc-sub-read-bodyp sub secret cfg carry h art icfg iclock)
 (fn-pacc-sub-read-bodyp sub secret cfg carry *fn-article-ceiling-limits*
 art (fn-pacc-wide-read-config icfg) iclock))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-read-bodyp fn-pacc-sub-inj fn-pacc-stored-payload fn-pctx-get
 fn-pacc-wide-read-config-fields fn-pacc-wide-read-config-keeps-validity
 fn-pacc-gated-injection-keeps-decision-at-wide-headers nfix zp car-cons cdr-cons)))))

(defthm fn-pacc-sub-readp-has-admitted-item-profile
 (implies (fn-pacc-sub-readp sub secret cfg carry h)
 (fn-pacc-item-sub-readp sub secret cfg carry))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-read-body-has-wide-profile-witness
 (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret cfg carry h)))
 (icfg (mv-nth 1 (fn-pacc-sub-readp-witness sub secret cfg carry h)))
 (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret cfg carry h))))
 (:instance fn-pacc-read-body-establishes-readp (take-config cfg) (parse-carry carry) (read-limits *fn-article-ceiling-limits*)
 (art (mv-nth 0 (fn-pacc-sub-readp-witness sub secret cfg carry h)))
 (icfg (fn-pacc-wide-read-config (mv-nth 1 (fn-pacc-sub-readp-witness sub secret cfg carry h))))
 (iclock (mv-nth 2 (fn-pacc-sub-readp-witness sub secret cfg carry h))))
 (:instance fn-pacc-profile-witness-establishes-item-read (profile *fn-pacc-wide-read-profile*)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-sub-readp fn-pacc-sub-read-at-profilep fn-pacc-wide-read-profile-is-admitted)))))

; Heterogeneous ER proof support: landing-er-compose.lisp
(defthm fn-pacc-local-item-readp-from-decision-readp
 (implies (and (fn-pacc-decision-readp (fn-own-sub-decision sub) h)
               (fn-own-sub-shapep sub) (fn-apc-p carry))
          (fn-pacc-local-sub-readp sub secret cfg carry))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-sub-readp-has-admitted-item-profile) (:instance fn-pacc-successful-read-body (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (take-config cfg) (parse-carry carry))
       (:instance fn-pacc-read-body-establishes-readp (art (mv-nth 0 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (icfg (mv-nth 1 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (iclock (mv-nth 2 (fn-pacc-sub-readp-witness (fn-own-sub-make-author nil nil nil (fn-own-sub-decision sub) nil nil :post-d25) nil nil nil h)))
        (take-config cfg) (parse-carry carry) (read-limits h)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-decision-readp fn-pacc-local-sub-readp fn-pacc-sub-readp fn-pacc-sub-read-bodyp
 fn-own-sub-decision-of-fn-own-sub-make-author)))))

(defthm fn-pacc-enqueue-carries-local-item-readp
 (implies (and (fn-pacc-local-sub-readp sub secret cfg carry)
               (fn-pacc-queue-readp (fn-own-queue o) secret cfg carry))
          (fn-pacc-queue-readp (fn-own-queue (fn-own-enqueue o sub)) secret cfg carry))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-own-enqueue fn-own-queue fn-own-make fn-ag-append fn-pacc-item-queue-append
 fn-psub-unpack-of-pack-sub car-cons cdr-cons)))))

(defthm fn-pacc-scar-finish-read-carries-item-queue-readp
 (implies (and (fn-pacc-queue-readp (fn-own-queue o) secret cfg carry)
               (fn-pacc-effects-readp (fn-served-result-effects result) h)
               (fn-apc-p carry))
          (fn-pacc-queue-readp (fn-own-queue (cdr (fn-scar-finish-read o conn result live))) secret cfg carry))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-pacc-local-item-readp-from-decision-readp (sub (fn-own-sub-make-author (fn-own-conn-id conn) (fn-own-conn-version conn) nil (fn-served-submission (fn-served-result-effects result)) (fn-served-submission-login (fn-served-result-effects result)) (fn-served-submission-account (fn-served-result-effects result)) (fn-own-served-source-context (fn-served-submission (fn-served-result-effects result))))))) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-scar-finish-read fn-own-set-conns fn-own-queue-of-fn-own-make
 fn-pacc-selected-submission-has-readp fn-pacc-local-item-readp-from-decision-readp
 fn-own-sub-shapep-of-fn-own-sub-make-author fn-own-sub-decision-of-fn-own-sub-make-author
 fn-pacc-enqueue-carries-local-item-readp cdr-cons)))))

(encapsulate ()
 (set-ignore-ok t)
 (defthm fn-pacc-available-read-carries-queue-readp (let* ((conn (fn-own-find-conn id (fn-own-conns o))) (r (fn-av-scr-own-read-span o id i end cache fn-octets fn-arena fn-cat))) (implies (and (fn-octets-p fn-octets) (fn-arena-p fn-arena) (fn-cat-p fn-cat) (natp i) (natp end) (fn-apc-p parse-carry) (fn-pacc-queue-readp (fn-own-queue o) secret take-config parse-carry)) (fn-pacc-queue-readp (fn-own-queue (fn-own-tls-result-owner r)) secret take-config parse-carry)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pacc-scar-finish-read-carries-item-queue-readp
 (cfg take-config) (carry parse-carry)
 (conn (fn-own-find-conn id (fn-own-conns o)))
 (result (fn-served-counted-result
 (fn-av-scr-step-span-fast (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))) i end
 (fn-sn-node (fn-own-store o)) (fn-own-view-version (fn-own-view o))
 (fn-state-articles (fn-own-view-archive (fn-own-view o))) cache fn-octets fn-arena fn-cat)))
 (live (fn-sn-node (fn-own-store o)))
 (h (fn-inj-config-header-limits (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o)))))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-av-scr-own-read-span fn-own-tls-result-owner fn-own-tls-make-result
 fn-pacc-scar-finish-read-carries-item-queue-readp fn-pacc-av-step-fast-carries-read-effects-and-headers
 fn-pacc-own-tls-served-conn-keeps-header-limits fn-ag-car fn-ag-cdr car-cons cdr-cons (:executable-counterpart consp))))))
)

(defthm fn-pacc-startup-install-establishes-item-owner-reads
 (let* ((oc (fn-ock-install replayed opened max-conns))
 (next (mv-nth 1 (fn-osb-install (fn-ocfg-owner oc) profile))))
 (implies (and (not (equal oc :fault)) (fn-bs-profile-admittedp profile))
 (fn-pacc-owner-value-readsp next)))
 :hints (("Goal" :do-not-induct t :use (fn-pacc-recovered-owner-has-no-local-work)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-pacc-owner-value-readsp fn-pacc-every-owner-pin-reads-own-headers
 fn-pacc-install-owner-work-frame fn-pacc-queue-readp fn-pacc-inflight-readp fn-pacc-local-sub-readp
 fn-own-sub-decision fn-own-sub-source-context fn-inj-injectedp fn-inj-decision-status
 fn-inj-nth fn-inj-car fn-inj-cdr fn-ag-car fn-ag-cdr nfix zp
 (:executable-counterpart consp) (:executable-counterpart equal))))))
