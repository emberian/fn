; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5)
; Actual prepared commit -> reserved/registered builder typed-row attachment.
; PRF-1168 extension. These relations are proof-only and never scan hot rows.
(in-package "ACL2")
(include-book "index-backing-row-carry")
(include-book "catalog-prepare")
(include-book "index-backing-assignment")
(include-book "index-backing-row-copy")

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

; Actual recursive destination mutation, carried from the existing filled
; prefix and actual assigned/copied row. A stamp never establishes the row.
(local
 (defthm fn-iprc-row-set-preserves-prefix
  (implies (and (fn-ibrc-prefixp (nth 0 fn-ibp-row-page) count prefix)
                (fn-ibrc-row-domainp row prefix))
   (fn-ibrc-prefixp (nth 0 (fn-ibp-row-set ordinal row fn-ibp-row-page)) count prefix))
  :hints (("Goal"
   :use ((:instance fn-ibrc-prefix-replace (rows (nth 0 fn-ibp-row-page)) (slot ordinal)))
   :in-theory (e/d (fn-ibp-row-set update-fn-ibp-row-cellsi)
    (fn-ibrc-prefixp fn-ibrc-row-domainp fn-ibrc-prefix-replace update-nth nfix))))))

(defthm fn-iprc-node-row-write-preserves-prefix
 (implies
  (and (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
       (or sealp (fn-ibrc-row-domainp row prefix)))
  (fn-iprc-node-prefixp slot depth count prefix
   (mv-nth 2 (fn-ibp-node-row-write ordinal row sealp slot depth id incarnation fuel fn-ibp-node))))
 :hints (("Goal"
  :induct (fn-ibp-node-row-write ordinal row sealp slot depth id incarnation fuel fn-ibp-node)
  :do-not '(generalize eliminate-destructors)
  :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
  :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-row-write)
   (fn-ibp-row-set fn-ibp-row-seal nth fn-ibrc-prefixp fn-ibrc-row-domainp
    mod floor mod-=-0 floor-=-x/y mod-type)))))

(defthm fn-iprc-node-row-write-extends-prefix
 (implies
  (and (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
       (fn-ibrc-row-domainp row prefix)
       (equal (mod ordinal 256) (nfix count))
       (eq (mv-nth 0 (fn-ibp-node-row-write ordinal row nil slot depth id incarnation fuel fn-ibp-node)) :written))
  (fn-iprc-node-prefixp slot depth (+ 1 (nfix count)) prefix
   (mv-nth 2 (fn-ibp-node-row-write ordinal row nil slot depth id incarnation fuel fn-ibp-node))))
 :hints (("Goal"
  :induct (fn-ibp-node-row-write ordinal row nil slot depth id incarnation fuel fn-ibp-node)
  :do-not '(generalize eliminate-destructors)
  :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
  :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-row-write)
   (fn-ibp-row-set fn-ibp-row-seal nfix nth fn-ibrc-prefixp fn-ibrc-row-domainp
    mod floor mod-=-0 floor-=-x/y mod-type)))))

; Owner lifecycle metadata is in a distinct child from row cells. Actual
; CURRENT read/retain/seal and copy progress preserve every selected row path.
(encapsulate ()
 (local (defun-nx fn-iprc-owner-path-induct (slot address depth fuel node)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth) (list slot fuel node)
   (fn-iprc-owner-path-induct (floor slot 2) (floor address 2) (- depth 1) (- fuel 1)
    (fn-ibp-node-children-get
     (if (evenp address) 'fn-ibp-node-left 'fn-ibp-node-right)
     node (create-fn-ibp-node))))))

 (defthm fn-iprc-page-owner-action-preserves-row-prefix
  (equal
   (fn-iprc-node-prefixp slot depth count prefix
    (mv-nth 4 (fn-ibp-node-page-owner-action token operation kind physical receipt builder
                 fuel address depth fn-ibp-node)))
   (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
  :hints (("Goal"
   :induct (fn-iprc-owner-path-induct slot address depth fuel fn-ibp-node)
   :do-not '(generalize eliminate-destructors)
   :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
            (fn-ibp-node-page-owner-action token operation kind physical receipt builder fuel address depth fn-ibp-node))
   :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-page-owner-action)
    (fn-ibp-page-owner-row fn-ibp-page-owner-finish-retirement
     fn-ibp-page-owner-reserve fn-ibp-page-owner-built fn-ibp-page-owner-sealed
     fn-ibp-page-owner-reference fn-ibp-page-owner-retire
     fn-ibp-page-owner-tokenp fn-omk-at nth fn-ibrc-prefixp fn-ibrc-row-domainp
     mod floor mod-=-0 floor-=-x/y mod-type floor-type-2 floor-type-3 floor-type-4)))))

 (defthm fn-iprc-owner-filled-preserves-row-prefix
  (equal
   (fn-iprc-node-prefixp slot depth count prefix
    (mv-nth 2 (fn-ibp-node-row-owner-filled token expected fuel address depth fn-ibp-node)))
   (fn-iprc-node-prefixp slot depth count prefix fn-ibp-node))
  :hints (("Goal"
   :induct (fn-iprc-owner-path-induct slot address depth fuel fn-ibp-node)
   :do-not '(generalize eliminate-destructors)
   :expand ((fn-iprc-node-prefixp slot depth count prefix fn-ibp-node)
            (fn-ibp-node-row-owner-filled token expected fuel address depth fn-ibp-node))
   :in-theory (e/d (fn-iprc-node-prefixp fn-ibp-node-row-owner-filled)
    (fn-ibp-row-owner-filled nth fn-ibrc-prefixp fn-ibrc-row-domainp
     mod floor mod-=-0 floor-=-x/y mod-type floor-type-2 floor-type-3 floor-type-4)))))
)

(defthm fn-iprc-copy-cell-preserves-destination-prefix
 (implies
  (and (natp count)
       (fn-iprc-node-prefixp physical depth filled prefix fn-ibp-node)
       (fn-ibrc-row-domainp assigned prefix)
       (fn-iprc-node-prefixp (nth 1 old-descriptor) depth (mod count 256) prefix fn-ibp-node))
  (fn-iprc-node-prefixp physical depth filled prefix
   (mv-nth 2 (fn-ibp-row-copy-cell token assigned count old-descriptor physical nonce fuel depth fn-ibp-node))))
 :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors)
  :use ((:instance fn-iprc-actual-node-read-row-domain
          (ordinal (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))
          (fuel (+ 1 depth)) (slot (nth 1 old-descriptor))
          (count (mod count 256)) (id (nth 2 old-descriptor))
          (incarnation (nth 3 old-descriptor)) (fn-ibp-node (mv-nth 4 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))))
  :in-theory (e/d (fn-ibp-row-copy-cell)
   (fn-iprc-actual-node-read-row-domain fn-iprc-node-prefixp fn-ibrc-row-domainp fn-ibp-node-page-owner-action
    fn-ibp-node-row-read fn-ibp-node-row-write fn-ibp-node-row-owner-filled
    fn-ibp-chunk-descriptorp fn-omk-at mod floor mod-=-0 floor-=-x/y mod-type)))))

(defthm fn-iprc-copy-cell-extends-owned-prefix
 (let ((position (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))))
  (implies
   (and (natp count)
        (fn-iprc-node-prefixp physical depth position prefix fn-ibp-node)
        (fn-ibrc-row-domainp assigned prefix)
        (fn-iprc-node-prefixp (nth 1 old-descriptor) depth (mod count 256) prefix fn-ibp-node)
        (member-eq (mv-nth 0 (fn-ibp-row-copy-cell token assigned count old-descriptor physical nonce fuel depth fn-ibp-node))
                   '(:copied :appended)))
   (fn-iprc-node-prefixp physical depth (+ 1 (nfix position)) prefix
    (mv-nth 2 (fn-ibp-row-copy-cell token assigned count old-descriptor physical nonce fuel depth fn-ibp-node)))))
 :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors)
  :use ((:instance fn-iprc-node-row-write-extends-prefix
 (ordinal (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))) (row assigned) (slot physical) (count (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))
 (id nonce) (incarnation nonce) (fuel (+ 1 depth)) (fn-ibp-node (mv-nth 4 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))
(:instance fn-iprc-node-row-write-extends-prefix
 (ordinal (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))) (row (mv-nth 1 (fn-ibp-node-row-read (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))) (+ 1 depth) (nth 1 old-descriptor) depth (nth 2 old-descriptor) (nth 3 old-descriptor) (mv-nth 4 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))) (slot physical) (count (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))
 (id nonce) (incarnation nonce) (fuel (+ 1 depth)) (fn-ibp-node (mv-nth 4 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node))))
(:instance fn-iprc-actual-node-read-row-domain
          (ordinal (fn-omk-at 10 (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))) (fuel (+ 1 depth)) (slot (nth 1 old-descriptor))
          (count (mod count 256)) (id (nth 2 old-descriptor)) (incarnation (nth 3 old-descriptor))
          (fn-ibp-node (mv-nth 4 (fn-ibp-node-page-owner-action token :read nil nil nil nil (+ 1 depth) (floor physical 64) depth fn-ibp-node)))))
  :in-theory (e/d (fn-ibp-row-copy-cell)
   (fn-iprc-node-row-write-extends-prefix fn-iprc-actual-node-read-row-domain fn-iprc-node-prefixp fn-ibrc-row-domainp
    fn-ibp-node-page-owner-action fn-ibp-node-row-read fn-ibp-node-row-write
    fn-ibp-node-row-owner-filled fn-ibp-chunk-descriptorp fn-omk-at
    mod floor mod-=-0 floor-=-x/y mod-type)))))

; Actual caller derives the copied row and descriptors from its retained builder.
(encapsulate ()
(defun-nx fn-iprc-copy-layout-domainp (prefix backing)
 (let* ((builder (fn-ibp-builder backing)) (receipt (fn-ibp-page-pending backing))
        (count (fn-omk-at 6 builder)) (physical (fn-omk-at 3 receipt))
        (nonce (fn-omk-at 2 receipt)) (depth (fn-ibp-slot-depth backing))
        (descriptor (fn-omk-at 9 receipt)) (node (fn-ibp-registry backing))
        (token (list :index-page nonce (+ 1 (floor physical 64)) (mod physical 64)))
        (owner (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil
                           (+ 1 depth) (floor physical 64) depth node))))
  (and (natp count)
       (fn-ibrc-row-domainp (fn-omk-at 5 (fn-omk-at 8 builder)) prefix)
       (fn-iprc-node-prefixp (nth 1 descriptor) depth (mod count 256) prefix node)
       (fn-iprc-node-prefixp physical depth
         (if (eq (fn-omk-at 10 receipt) :copied) (+ 1 (mod count 256))
           (fn-omk-at 10 owner)) prefix node))))

(local
 (defthm fn-iprc-copy-appended-position
  (implies
   (eq (mv-nth 0 (fn-ibp-row-copy-cell token assigned count old-descriptor physical nonce fuel depth fn-ibp-node)) :appended)
   (equal (fn-omk-at 10
           (mv-nth 1 (fn-ibp-node-page-owner-action token :read nil nil nil nil
                        (+ 1 depth) (floor physical 64) depth fn-ibp-node)))
          (mod count 256)))
  :hints (("Goal" :do-not-induct t
   :in-theory (e/d (fn-ibp-row-copy-cell)
    (fn-ibp-node-page-owner-action fn-ibp-node-row-read fn-ibp-node-row-write
     fn-ibp-node-row-owner-filled fn-ibp-chunk-descriptorp fn-omk-at
     mod floor mod-=-0 floor-=-x/y mod-type))))))

(local (defthm fn-iprc-count-remainder-natp
 (implies (natp count) (natp (mod count 256)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (enable mod)))))

(defthm fn-iprc-copy-one-appended-domain
 (implies
  (and (fn-iprc-copy-layout-domainp prefix fn-index-backing)
       (eq (mv-nth 0 (fn-ipa-row-copy-one fuel fn-index-backing)) :appended))
  (fn-iprc-node-prefixp
   (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing))
   (fn-ibp-slot-depth fn-index-backing)
   (+ 1 (mod (fn-omk-at 6 (fn-ibp-builder fn-index-backing)) 256)) prefix
   (fn-ibp-registry (mv-nth 2 (fn-ipa-row-copy-one fuel fn-index-backing)))))
 :hints (("Goal" :do-not-induct t :do-not '(generalize eliminate-destructors)
  :use ((:instance fn-iprc-copy-cell-extends-owned-prefix (token (list :index-page (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing)) (+ 1 (floor (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing)) 64)) (mod (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing)) 64)))
 (assigned (fn-omk-at 5 (fn-omk-at 8 (fn-ibp-builder fn-index-backing)))) (count (fn-omk-at 6 (fn-ibp-builder fn-index-backing)))
 (old-descriptor (fn-omk-at 9 (fn-ibp-page-pending fn-index-backing))) (physical (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing))) (nonce (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing)))
 (depth (fn-ibp-slot-depth fn-index-backing)) (fn-ibp-node (fn-ibp-registry fn-index-backing)))
        (:instance fn-iprc-copy-appended-position (token (list :index-page (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing)) (+ 1 (floor (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing)) 64)) (mod (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing)) 64)))
 (assigned (fn-omk-at 5 (fn-omk-at 8 (fn-ibp-builder fn-index-backing)))) (count (fn-omk-at 6 (fn-ibp-builder fn-index-backing)))
 (old-descriptor (fn-omk-at 9 (fn-ibp-page-pending fn-index-backing))) (physical (fn-omk-at 3 (fn-ibp-page-pending fn-index-backing))) (nonce (fn-omk-at 2 (fn-ibp-page-pending fn-index-backing)))
 (depth (fn-ibp-slot-depth fn-index-backing)) (fn-ibp-node (fn-ibp-registry fn-index-backing))))
  :in-theory (e/d (fn-ipa-row-copy-one fn-iprc-copy-layout-domainp)
   (fn-iprc-copy-cell-extends-owned-prefix fn-iprc-copy-appended-position nth update-nth
    fn-ibp-row-copy-cell fn-ibp-node-page-owner-action fn-ibrc-row-domainp
    fn-iprc-node-prefixp fn-omk-at mod floor mod-=-0 floor-=-x/y mod-type)))))

)
