; Actual prepared commit -> reserved/registered builder typed-row attachment.
; PRF-1168 extension. These relations are proof-only and never scan hot rows.
(in-package "ACL2")
(include-book "index-backing-row-carry")
(include-book "catalog-prepare")
(include-book "index-backing-assignment")

(defthm fn-iprc-prepare-establishes-row-domain
 (implies (and (not pending) (fn-ab-p (fn-row-binding wire)))
  (mv-let (pc fn-arena)
   (fn-cat-prepare wire plan reservation fn-octets keyring generation pending fn-arena fn-cat)
   (fn-ibrc-row-domainp (fn-pc-held pc) (fn-arena-count fn-arena))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ibrc-buffer-intern-establishes-row-domain))
  :in-theory (e/d (fn-cat-prepare fn-pc-internals)
                  (fn-cat-intern fn-ibrc-row-domainp fn-arena-count fn-row-binding fn-ab-p)))))

; PC is the actual prepare result; PREFIX is that result's SAME arena prefix.
; Arena incarnation retention/publication is an additional source obligation.
(defun fn-iprc-builder-prepared-carryp (builder pc prefix)
 (declare (xargs :guard t))
 (and (equal (fn-omk-at 6 (fn-omk-at 19 builder)) pc)
      (equal (fn-omk-at 6 builder) (fn-pc-expected pc))
      (equal (fn-omk-at 7 builder) (fn-pc-token pc))
      (fn-ibrc-row-domainp (fn-pc-held pc) prefix)))

(local
 (defthm fn-iprc-omk-at-is-nth
  (implies (natp i) (equal (fn-omk-at i xs) (nth i xs)))
  :hints (("Goal" :induct (fn-omk-at i xs)
                  :in-theory (enable fn-omk-at nth)))))

(local
 (defthm fn-iprc-prs-never-reserved
  (not (equal (car (fn-prs-issue budget used rescue charged next limit demand)) :reserved))
  :hints (("Goal" :in-theory (e/d (fn-prs-issue)
    (fn-prs-vectorp fn-prs-below fn-prs-fundedp fn-prs-plus))))))
(local
 (defthm fn-iprc-candidate-never-reserved
  (not (equal (car (fn-igr-candidate fn-index-backing)) :reserved))
  :hints (("Goal" :in-theory (enable fn-igr-candidate)))))

(defthm fn-iprc-reserve-attaches-actual-prepared-row
 (implies
  (and (fn-ibrc-row-domainp (fn-pc-held pc) prefix)
       (eq (mv-nth 0 (fn-igr-reserve pc demand fn-index-backing fn-page-read-pool)) :reserved))
  (fn-iprc-builder-prepared-carryp
   (fn-ibp-builder (mv-nth 2 (fn-igr-reserve pc demand fn-index-backing fn-page-read-pool)))
   pc prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-igr-reserve fn-iprc-builder-prepared-carryp fn-omk-at)
    (fn-ibrc-row-domainp fn-pc-held fn-pc-expected fn-pc-token fn-igr-candidate
     fn-prs-issue fn-owner-page-read-keep-ledger fn-owner-page-read-ledger)))))

(defthm fn-iprc-register-preserves-prepared-row
 (implies (fn-iprc-builder-prepared-carryp (fn-ibp-builder fn-index-backing) pc prefix)
  (fn-iprc-builder-prepared-carryp
   (fn-ibp-builder (mv-nth 2 (fn-igr-register fuel fn-index-backing))) pc prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-igr-register fn-iprc-builder-prepared-carryp fn-omk-at)
    (fn-igr-node-register fn-ibrc-row-domainp fn-pc-held fn-pc-expected fn-pc-token
     fn-ibp-nodep fn-ibp-node-children-put)))))

(defthm fn-iprc-assignment-begin-attaches-prepared-row
 (implies
  (and (fn-iprc-builder-prepared-carryp (fn-ibp-builder fn-index-backing) pc prefix)
       (eq (mv-nth 0 (fn-ibp-writer-assignment-begin fuel fn-index-backing)) :assigning))
  (fn-ibrc-assignment-carryp
   (fn-omk-at 18 (fn-ibp-builder
     (mv-nth 2 (fn-ibp-writer-assignment-begin fuel fn-index-backing)))) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-writer-assignment-begin fn-iprc-builder-prepared-carryp)
   (fn-omk-at fn-ibrc-assignment-carryp fn-ibrc-row-domainp fn-gns-pending-begin
    fn-ipub-shapep fn-pc-held fn-pc-token fn-pc-expected)))))

(defthm fn-iprc-assignment-one-publishes-typed-assigned
 (implies
  (and (fn-ibrc-assignment-carryp (fn-omk-at 18 (fn-ibp-builder fn-index-backing)) prefix)
       (eq (mv-nth 0 (fn-ibp-writer-assignment-one fuel fn-index-backing)) :numbers))
  (fn-ibrc-row-domainp
   (fn-omk-at 5 (fn-omk-at 8 (fn-ibp-builder
      (mv-nth 2 (fn-ibp-writer-assignment-one fuel fn-index-backing))))) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibp-writer-assignment-one fn-ibrc-assignment-carryp fn-gns-pending-result)
   (fn-omk-at fn-gns-assign-step fn-held-with-numbers fn-gns-stage-begin
    fn-ibrc-row-domainp fn-gns-assign-cursorp)))))

; Logical carry over the actual selected registry path. This reuses PRF-1168's
; prefix relation on the reached child. It is never called by a served read.
(defun-nx fn-iprc-node-prefixp (slot depth count prefix node)
 (declare (xargs :measure (nfix depth)))
 (if (zp depth)
  (and (fn-ibp-node-children-boundp 'fn-ibp-row-page node)
       (fn-ibrc-prefixp
        (nth 0 (fn-ibp-node-children-get 'fn-ibp-row-page node (create-fn-ibp-row-page)))
        count prefix))
  (let ((key (if (equal (mod slot 2) 0) 'fn-ibp-node-left 'fn-ibp-node-right)))
   (and (fn-ibp-node-children-boundp key node)
        (fn-iprc-node-prefixp (floor slot 2) (- depth 1) count prefix
          (fn-ibp-node-children-get key node (create-fn-ibp-node)))))))

(defthm fn-iprc-actual-node-read-row-domain
 (implies
  (and (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
       (< (nfix (mod ordinal 256)) (nfix count))
       (eq (mv-nth 0 (fn-ibp-node-row-read ordinal fuel slot depth id incarnation fn-ibp-node)) :row))
  (fn-ibrc-row-domainp
   (mv-nth 1 (fn-ibp-node-row-read ordinal fuel slot depth id incarnation fn-ibp-node)) prefix))
 :hints (("Goal"
  :induct (fn-ibp-node-row-read ordinal fuel slot depth id incarnation fn-ibp-node)
  :do-not '(generalize eliminate-destructors)
  :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
  :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-row-read)
   (fn-ibp-row nth fn-ibrc-prefixp fn-ibrc-row-domainp fn-ibp-node-children-boundp
    fn-ibp-node-children-get mod floor mod-=-0 floor-=-x/y mod-type)))))

; Re-decide and policy events replace context, not payload/NOV/binding.
; The actual delta producer still owns which ordinal/context may be applied.
(defthm fn-iprc-context-update-preserves-row-domain
 (implies (fn-ibrc-row-domainp row prefix)
  (fn-ibrc-row-domainp (fn-held-with-context row context) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-held-with-context fn-ibrc-row-domainp
                    fn-held-internals fn-record-internals)
                  (fn-ab-p fn-hnov-p fn-hf-nov fn-held-withdrawnp)))))
