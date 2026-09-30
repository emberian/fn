; Caller carry for the actual full-plan byte entry; proof vocabulary only.
; The served wrapper must carry this result, never evaluate the catalog relation.
(in-package "ACL2")
(include-book "served-plan-byte-cursor")
(include-book "over-byte-invariants")

(local
 (defthm fn-spcarry-at-is-nth
  (equal (fn-lpc-at i x) (nth (nfix i) x))
  :hints (("Goal" :in-theory (enable fn-lpc-at fn-ag-car fn-ag-cdr nth)))))

(local
 (defthm fn-spcarry-put-status
  (equal (fn-spbc-status (fn-spbc-put p (fn-spbc-effect :byte-quantum q)))
         (if (and (nth 0 q) (posp (nth 1 q))) :continue :ready))
  :hints (("Goal" :in-theory
   (e/d (fn-spbc-status fn-spbc-put fn-spbc-head fn-spbc-payload fn-spbc-effect
         fn-spbc-cur fn-spbc-rest fn-spbc-with-rest fn-splan-cursor-effectp
         fn-spp-save-active fn-spp-make fn-spp-holderp fn-splan-cur fn-splan-rest)
        (fn-spbc-tail fn-spp-prefix fn-spp-origin fn-spp-resource))))))

(local
 (defthm fn-spcarry-put-ready
  (equal (fn-spbc-ready-p (fn-spbc-put p (fn-spbc-effect :byte-quantum q)) fn-arena fn-cat)
         (and (true-listp q) (natp (nth 1 q)) (true-listp (nth 2 q)) (natp (nth 3 q))
              (or (null (nth 0 q))
                  (and (fn-obc-statep (nth 0 q) fn-arena)
                       (fn-obc-source-ready-p (nth 0 q) fn-arena fn-cat)))))
  :hints (("Goal" :in-theory
   (e/d (fn-spbc-ready-p)
        (fn-spbc-put fn-spbc-effect fn-spbc-status fn-spbc-quantum
         fn-obc-statep fn-obc-source-ready-p))))))

(defthm fn-spbc-one-preserves-carried-ready
 (implies (and (fn-spbc-ready-p p fn-arena fn-cat)
               (fn-cat-p fn-cat)
               (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat))
          (fn-spbc-ready-p (fn-spbc-one p fn-arena fn-cat) fn-arena fn-cat))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-obc-one-keeps-shape-under-carried-catalog-by-definition
          (s (nth 0 (fn-spbc-quantum p))))
        (:instance fn-obc-source-ready-from-carried-handles
          (s (mv-nth 1 (fn-obc-one (nth 0 (fn-spbc-quantum p)) fn-arena fn-cat))))
        (:instance fn-obc-one-output-true-list (s (nth 0 (fn-spbc-quantum p)))))
  :in-theory
   (e/d (fn-spbc-one fn-spbc-ready-p fn-obc-quantum-one fn-obc-quantum-status)
        (fn-spbc-status fn-spbc-put fn-spbc-effect fn-spbc-quantum fn-obc-one
         fn-obc-statep fn-obc-source-ready-p fn-cat-p fn-cat-handles-inp
         fn-cat-count fn-scol-okp nth)))))
