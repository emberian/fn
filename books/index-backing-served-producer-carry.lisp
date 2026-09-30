; Actual staged held16 and single-seal producer -> registered builder carry.
; No new runtime source hook, installer or supplied allowance boundary.
(in-package "ACL2")
(include-book "index-backing-publication-row-carry")
(include-book "store-intern-row")
(include-book "catalog-prepare-sealed")

(encapsulate ()
(defthm fn-ipsp-staged-row-domain
 (implies (and (fn-ab-p (fn-row-binding wire)) (natp h) (natp prefix) (< h prefix))
  (fn-ibrc-row-domainp (fn-intern-row-at wire keyring generation h) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-ibrc-row-domainp fn-intern-row-at fn-held-internals fn-record-internals fn-held-withdrawnp)
   (fn-held-facts-of fn-held-context-of fn-row-binding fn-ab-p fn-hnov-of)))))
(defthm fn-ipsp-sealed-prepare-establishes-domain
 (implies (fn-ab-p (fn-row-binding wire))
  (let* ((row (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena)))
         (sealed (fn-arena-seal-buffer fn-octets fn-arena))
         (pc (fn-cat-prepare-sealed wire row plan reservation nil sealed fn-cat)))
   (fn-ibrc-row-domainp (fn-pc-held pc) (fn-arena-count sealed))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-cat-prepare-sealed fn-intern-row-at fn-pc-internals
                   fn-ibrc-row-domainp fn-held-internals fn-record-internals fn-held-withdrawnp fn-arena-count)
   (fn-held-facts-of fn-held-context-of fn-row-binding fn-ab-p fn-hnov-of
    fn-arena-seal-buffer fn-arena-seal-buffer-is-append)))))
(defthm fn-ipsp-sealed-is-actual-buffer-prepare
 (implies (equal (fn-octets-list fn-octets) (fn-record-payload wire))
  (let* ((row (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena)))
         (sealed (fn-arena-seal-buffer fn-octets fn-arena)))
   (and
    (equal (fn-cat-prepare-sealed wire row plan reservation pending sealed fn-cat)
           (mv-nth 0 (fn-cat-prepare wire plan reservation fn-octets keyring generation pending fn-arena fn-cat)))
    (implies (not pending)
     (equal sealed (mv-nth 1 (fn-cat-prepare wire plan reservation fn-octets keyring generation pending fn-arena fn-cat)))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-cat-prepare-sealed fn-cat-prepare fn-cat-intern fn-intern-row-at
                   fn-held-internals fn-record-internals fn-arena-count)
   (fn-cat-intern-is-intern-list fn-held-facts-of fn-held-context-of fn-row-binding fn-pc-make
    fn-arena-seal-buffer fn-arena-seal-buffer-is-append)))))
)

(encapsulate ()
(defthm fn-ipsp-sealed-reserve-register-retains-actual-row
 (let* ((row (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena)))
        (sealed (fn-arena-seal-buffer fn-octets fn-arena))
        (pc (fn-cat-prepare-sealed wire row plan reservation nil sealed fn-cat))
        (reserved (mv-nth 2 (fn-igr-reserve pc demand fn-index-backing fn-page-read-pool))))
  (implies
   (and (fn-ab-p (fn-row-binding wire))
        (eq (mv-nth 0 (fn-igr-reserve pc demand fn-index-backing fn-page-read-pool)) :reserved))
   (fn-iprc-builder-prepared-carryp
    (fn-ibp-builder (mv-nth 2 (fn-igr-register fuel reserved))) pc (fn-arena-count sealed))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ipsp-sealed-prepare-establishes-domain)
        (:instance fn-iprc-reserve-attaches-actual-prepared-row
         (pc (fn-cat-prepare-sealed wire
              (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena))
              plan reservation nil (fn-arena-seal-buffer fn-octets fn-arena) fn-cat))
         (prefix (fn-arena-count (fn-arena-seal-buffer fn-octets fn-arena))))
        (:instance fn-iprc-register-preserves-prepared-row
         (pc (fn-cat-prepare-sealed wire
              (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena))
              plan reservation nil (fn-arena-seal-buffer fn-octets fn-arena) fn-cat))
         (prefix (fn-arena-count (fn-arena-seal-buffer fn-octets fn-arena)))
         (fn-index-backing
          (mv-nth 2 (fn-igr-reserve
           (fn-cat-prepare-sealed wire
            (fn-intern-row-at wire keyring generation (fn-arena-count fn-arena))
            plan reservation nil (fn-arena-seal-buffer fn-octets fn-arena) fn-cat)
           demand fn-index-backing fn-page-read-pool)))))
  :in-theory (disable fn-ipsp-sealed-prepare-establishes-domain
   fn-iprc-reserve-attaches-actual-prepared-row fn-iprc-register-preserves-prepared-row
   fn-iprc-builder-prepared-carryp fn-ibrc-row-domainp fn-ab-p fn-row-binding
   fn-cat-prepare-sealed fn-intern-row-at fn-arena-count fn-arena-seal-buffer
   fn-igr-reserve fn-igr-register fn-ibp-builder))))
)

; Actual event mutators retain the domain over the complete resulting catalog.
(encapsulate ()
(defthm fn-ipsp-actual-withdraw-preserves-row-domain
 (implies (and (fn-ibrc-prefixp fn-cat (fn-cat-count fn-cat) prefix)
               (natp by))
  (fn-ibrc-prefixp (fn-cat-withdraw (nfix target) by fn-cat)
                   (fn-cat-count fn-cat) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-cat-withdraw-is-mark fn-cat-mark-withdrawn
                   fn-cat-count-is-len fn-held-withdrawnp)
   (fn-cat-withdraw fn-cat-count fn-ibrc-prefixp fn-ibrc-row-domainp
    fn-held-with-withdrawn fn-held-withdrawn nth update-nth)))))
(defthm fn-ipsp-actual-redecide-preserves-row-domain
 (implies (and (fn-ibrc-prefixp fn-cat (fn-cat-count fn-cat) prefix)
               (< (nfix seq) (fn-cat-count fn-cat)))
  (fn-ibrc-prefixp (fn-cat-redecide (nfix seq) context fn-cat)
                   (fn-cat-count fn-cat) prefix))
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-cat-redecide-is-update-nth fn-cat-count-is-len)
   (fn-cat-redecide fn-cat-count fn-ibrc-prefixp fn-ibrc-row-domainp
    fn-held-with-context nth update-nth)))))
)
(encapsulate ()
(defthm fn-ipsp-actual-withdraw-preserves-full-domain
 (implies (and (fn-ibrc-prefixp fn-cat (fn-cat-count fn-cat) prefix)
               (natp by))
  (let ((result (fn-cat-withdraw (nfix target) by fn-cat)))
   (fn-ibrc-prefixp result (fn-cat-count result) prefix)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ipsp-actual-withdraw-preserves-row-domain))
  :in-theory (e/d (fn-cat-withdraw-is-mark fn-cat-mark-withdrawn fn-cat-count-is-len)
   (fn-cat-withdraw fn-cat-count fn-ibrc-prefixp fn-ibrc-row-domainp
    fn-held-with-withdrawn fn-held-withdrawn nth update-nth)))))
(defthm fn-ipsp-actual-redecide-preserves-full-domain
 (implies (and (fn-ibrc-prefixp fn-cat (fn-cat-count fn-cat) prefix)
               (< (nfix seq) (fn-cat-count fn-cat)))
  (let ((result (fn-cat-redecide (nfix seq) context fn-cat)))
   (fn-ibrc-prefixp result (fn-cat-count result) prefix)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ipsp-actual-redecide-preserves-row-domain))
  :in-theory (e/d (fn-cat-redecide-is-update-nth fn-cat-count-is-len)
   (fn-cat-redecide fn-cat-count fn-ibrc-prefixp fn-ibrc-row-domainp
    fn-held-with-context nth update-nth)))))
)
