; Typed row establishment and physical-prefix preservation, PRF-1168.
; These are proof relations, not validators on the served path. Header seals
; and row counts never establish a row's types or its source arena identity.
(in-package "ACL2")
(include-book "catalog-record")
(include-book "catalog-number-assignment")
(include-book "group-number-source-pending")
(include-book "index-backing-chunks")

; The exact current held16 boundary, including its real binding field.
; PREFIX belongs to the captured source arena; a current larger count alone
; does not prove that a handle denotes the same payload after reconstruction.
(defun fn-ibrc-row-domainp (row prefix)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 16)
       (fn-ab-p (fn-held-binding row))
       (fn-held-withdrawnp (fn-held-withdrawn row))
       (natp (fn-record-payload row)) (natp prefix)
       (< (fn-record-payload row) prefix)
       (or (not (fn-hf-nov (fn-held-facts row)))
           (fn-hnov-p (fn-hf-nov (fn-held-facts row))))))

(defun fn-ibrc-prefixp (rows count prefix)
  (declare (xargs :guard t :measure (nfix count)))
  (if (zp (nfix count)) t
    (and (consp rows)
         (fn-ibrc-row-domainp (car rows) prefix)
         (fn-ibrc-prefixp (cdr rows) (- (nfix count) 1) prefix))))

(defthm fn-ibrc-intern-establishes-row-domain
  (implies (fn-ab-p (fn-row-binding wire))
    (mv-let (row fn-arena)
      (fn-cat-intern-list wire keyring generation fn-arena)
      (fn-ibrc-row-domainp row (fn-arena-count fn-arena))))
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-ibrc-row-domainp fn-cat-intern-list
                      fn-held-internals fn-record-internals fn-held-withdrawnp)
                     (fn-held-facts-of fn-held-context-of fn-row-binding
                      fn-ab-p fn-hnov-of fn-arena-count fn-arena-seal-list)))))

(defthm fn-ibrc-buffer-intern-establishes-row-domain
  (implies (fn-ab-p (fn-row-binding wire))
    (mv-let (row fn-arena)
      (fn-cat-intern wire fn-octets keyring generation fn-arena)
      (fn-ibrc-row-domainp row (fn-arena-count fn-arena))))
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-ibrc-row-domainp fn-cat-intern
                      fn-held-internals fn-record-internals fn-held-withdrawnp)
                     (fn-cat-intern-is-intern-list fn-arena-seal-buffer fn-held-facts-of
                      fn-held-context-of fn-row-binding fn-ab-p fn-hnov-of
                      fn-arena-count fn-arena-seal-list)))))

(defthm fn-ibrc-assignment-preserves-row-domain
  (implies (fn-ibrc-row-domainp row prefix)
           (fn-ibrc-row-domainp (fn-cat-assign row catalog) prefix))
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-cat-assign fn-held-with-numbers fn-ibrc-row-domainp
                      fn-held-internals fn-record-internals)
                     (fn-cat-assign-numbers fn-ab-p fn-hnov-p fn-hf-nov)))))

(defthm fn-ibrc-number-field-update-preserves-row-domain
  (implies (fn-ibrc-row-domainp row prefix)
           (fn-ibrc-row-domainp (fn-held-with-numbers row numbers) prefix))
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-held-with-numbers fn-ibrc-row-domainp
                      fn-held-internals fn-record-internals)
                     (fn-ab-p fn-hnov-p fn-hf-nov)))))

; These are the actual bounded assignment cursor and actual assigned8 field5
; consumed by FnIPARowCopyOne. No row is reconstructed by a parallel model.
(defun fn-ibrc-assignment-carryp (cursor prefix)
  (declare (xargs :guard t))
  (and (fn-gns-assign-cursorp cursor)
       (fn-ibrc-row-domainp (fn-gns-at 7 cursor) prefix)))

(defthm fn-ibrc-pending-begin-establishes-carry
  (implies (fn-ibrc-row-domainp (fn-pc-held pending) prefix)
    (fn-ibrc-assignment-carryp
      (fn-gns-pending-begin pending root root-id) prefix))
  :hints (("Goal"
    :use ((:instance fn-gns-assign-begin-cursorp
                     (groups (fn-record-groups (fn-pc-held pending)))
                     (held (fn-pc-held pending)) (token (fn-pc-token pending))
                     (count (fn-pc-expected pending))))
    :in-theory
    (e/d (fn-ibrc-assignment-carryp fn-gns-pending-begin fn-gns-assign-begin fn-gns-at)
         (fn-ibrc-row-domainp fn-gns-assign-cursorp
          fn-gns-assign-begin-cursorp)))))

(defthm fn-ibrc-assignment-step-preserves-carry
  (implies (fn-ibrc-assignment-carryp cursor prefix)
    (fn-ibrc-assignment-carryp (fn-gns-assign-step cursor) prefix))
  :hints (("Goal"
    :use ((:instance fn-gns-assign-step-retains-pending-binding (c cursor))
          (:instance fn-gns-assign-step-cursorp (c cursor)))
    :in-theory (e/d (fn-ibrc-assignment-carryp)
                    (fn-gns-assign-step fn-gns-assign-cursorp fn-gns-at
                     fn-ibrc-row-domainp fn-gns-assign-step-retains-pending-binding
                     fn-gns-assign-step-cursorp)))))

(defthm fn-ibrc-actual-assigned-row-domain
  (implies (and (equal (fn-gns-at 0 cursor) :done)
                (fn-ibrc-row-domainp (fn-gns-at 7 cursor) prefix))
    (fn-ibrc-row-domainp (fn-gns-at 5 (fn-gns-pending-result cursor)) prefix))
  :hints (("Goal" :in-theory
    (e/d (fn-gns-pending-result fn-gns-at)
         (fn-ibrc-row-domainp fn-held-with-numbers)))))

(defthm fn-ibrc-withdrawal-preserves-row-domain
  (implies (and (fn-ibrc-row-domainp row prefix)
                (fn-held-withdrawnp withdrawn))
           (fn-ibrc-row-domainp (fn-held-with-withdrawn row withdrawn) prefix))
  :hints (("Goal" :do-not-induct t
    :in-theory (e/d (fn-held-with-withdrawn fn-ibrc-row-domainp
                      fn-held-internals fn-record-internals)
                     (fn-held-withdrawnp fn-ab-p fn-hnov-p fn-hf-nov)))))

(local (defun fn-ibrc-prefix-slot-induct (slot count rows)
  (declare (xargs :measure (nfix slot) :guard t))
  (if (or (zp (nfix slot)) (zp (nfix count)) (atom rows)) nil
    (fn-ibrc-prefix-slot-induct (- (nfix slot) 1) (- (nfix count) 1) (cdr rows)))))

(defthm fn-ibrc-prefix-read-domain
  (implies (and (fn-ibrc-prefixp rows count prefix)
                (< (nfix slot) (nfix count)))
           (fn-ibrc-row-domainp (nth slot rows) prefix))
  :hints (("Goal" :induct (fn-ibrc-prefix-slot-induct slot count rows)
                  :in-theory (disable fn-ibrc-row-domainp))))

(defthm fn-ibrc-prefix-append-one
  (implies (and (fn-ibrc-prefixp rows count prefix)
                (fn-ibrc-row-domainp row prefix))
           (fn-ibrc-prefixp (update-nth (nfix count) row rows)
                             (+ 1 (nfix count)) prefix))
  :hints (("Goal" :induct (fn-ibrc-prefixp rows count prefix)
                  :in-theory (disable fn-ibrc-row-domainp))))

(defthm fn-ibrc-prefix-replace
  (implies (and (fn-ibrc-prefixp rows count prefix)
                (fn-ibrc-row-domainp row prefix))
           (fn-ibrc-prefixp (update-nth slot row rows) count prefix))
  :hints (("Goal" :induct (fn-ibrc-prefix-slot-induct slot count rows)
                  :in-theory (disable fn-ibrc-row-domainp))))

; Actual mutators and actual selector. The proof relation is carried from
; producer inputs; neither ROW-SET nor ROW-SEAL silently validates it.
(defthm fn-ibrc-row-set-appends-domain
  (implies (and (fn-ibrc-prefixp (nth 0 fn-ibp-row-page) count prefix)
                (fn-ibrc-row-domainp row prefix))
    (fn-ibrc-prefixp
      (nth 0 (fn-ibp-row-set (nfix count) row fn-ibp-row-page))
      (+ 1 (nfix count)) prefix))
  :hints (("Goal"
    :use ((:instance fn-ibrc-prefix-append-one (rows (nth 0 fn-ibp-row-page))))
    :in-theory (e/d (fn-ibp-row-set update-fn-ibp-row-cellsi)
                    (fn-ibrc-prefixp fn-ibrc-row-domainp
                     fn-ibrc-prefix-append-one update-nth nfix)))))

(defthm fn-ibrc-row-seal-preserves-domain
  (implies (fn-ibrc-prefixp (nth 0 fn-ibp-row-page) count prefix)
    (fn-ibrc-prefixp
      (nth 0 (mv-nth 1 (fn-ibp-row-seal id incarnation fn-ibp-row-page)))
      count prefix))
  :hints (("Goal" :in-theory (e/d (fn-ibp-row-seal update-fn-ibp-row-sealed)
                            (fn-ibrc-prefixp fn-ibrc-row-domainp)))))

(defthm fn-ibrc-physical-row-read-domain
  (implies (and (fn-ibrc-prefixp (nth 0 fn-ibp-row-page) count prefix)
                (< (nfix slot) (nfix count)))
           (fn-ibrc-row-domainp (fn-ibp-row slot fn-ibp-row-page) prefix))
  :hints (("Goal"
    :use ((:instance fn-ibrc-prefix-read-domain (rows (nth 0 fn-ibp-row-page))))
    :in-theory (e/d (fn-ibp-row fn-ibp-row-cellsi)
                    (fn-ibrc-prefixp fn-ibrc-row-domainp
                     fn-ibrc-prefix-read-domain nfix nth)))))

(local (defthm fn-ibrc-copy-append
  (implies (and (natp start) (posp count)
                (fn-ibrc-prefixp rows (+ start count) prefix)
                (fn-ibrc-prefixp dest start prefix))
    (fn-ibrc-prefixp (update-nth start (nth start rows) dest)
                      (+ 1 start) prefix))
  :hints (("Goal"
    :use ((:instance fn-ibrc-prefix-read-domain (slot start) (count (+ start count)))
          (:instance fn-ibrc-prefix-append-one (rows dest) (count start)
                                               (row (nth start rows))))
    :in-theory (disable fn-ibrc-prefixp fn-ibrc-row-domainp nth update-nth
                         fn-ibrc-prefix-read-domain fn-ibrc-prefix-append-one)))))

(defthm fn-ibrc-row-copy-span-extends-domain
  (implies (and (natp start) (natp count)
                (fn-ibrc-prefixp (nth 0 fn-ibp-row-page)
                                  (+ start count) prefix)
                (fn-ibrc-prefixp (nth 0 fn-ibp-row-page2) start prefix))
    (fn-ibrc-prefixp
      (nth 0 (fn-ibp-row-copy-span start count fn-ibp-row-page fn-ibp-row-page2))
      (+ start count) prefix))
  :hints (("Goal" :induct (fn-ibp-row-copy-span start count
                              fn-ibp-row-page fn-ibp-row-page2)
    :in-theory (e/d (fn-ibp-row-copy-span fn-ibp-row fn-ibp-row-cellsi
                      update-fn-ibp-row-cellsi)
                     (fn-ibrc-prefixp fn-ibrc-row-domainp nth update-nth)))))

; Normalized internal arithmetic inputs avoid redundant natural-number
; hypotheses; guarded callers already carry naturals. Only the two producer
; prefix hypotheses supply the row domain, neither header nor count does.
(defthm fn-ibrc-row-copy-owned-prefix
  (implies (and (fn-ibrc-prefixp (nth 0 fn-ibp-row-page)
                                 (+ (nfix start) (nfix count)) prefix)
                (fn-ibrc-prefixp (nth 0 fn-ibp-row-page2) (nfix start) prefix))
    (fn-ibrc-prefixp
      (nth 0 (fn-ibp-row-copy-span (nfix start) (nfix count)
                                   fn-ibp-row-page fn-ibp-row-page2))
      (+ (nfix start) (nfix count)) prefix))
  :hints (("Goal"
    :use ((:instance fn-ibrc-row-copy-span-extends-domain
                      (start (nfix start)) (count (nfix count))))
    :in-theory (disable fn-ibrc-row-copy-span-extends-domain
                         fn-ibrc-prefixp fn-ibrc-row-domainp fn-ibp-row-copy-span))))

(in-theory (disable fn-ibrc-row-domainp fn-ibrc-prefixp))
