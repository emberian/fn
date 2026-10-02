; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Actual pooled incoming authority for the captured readonly entry.
; No supplied row snapshot and no native symbol whitelist. The owner retains
; producer/backing identity, funded lifetime and mutable-dispatch obligations.
(in-package "ACL2")
(include-book "post-identity-captured")
(include-book "incoming-buffer-carrier-shape")
(include-book "page-read-pool-state")

(defun fn-pic-held-next (c fuel fn-octets fn-page-read-pool)
  (declare (xargs :stobjs (fn-octets fn-page-read-pool)
                  :guard (and (true-listp c) (natp fuel))))
  (let* ((row (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool)))
         (word (fn-ioh-access row (fn-pic-get incoming-token c) :read)))
    (if (equal word :holder-readonly)
        (fn-pic-next c fuel fn-octets)
      (mv word c fuel))))

(defthm fn-pic-held-next-authorized-output-unfolds
  (implies (equal (fn-ioh-access
                   (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                   (fn-pic-get incoming-token c) :read) :holder-readonly)
    (equal (mv-list 3 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))
           (mv-list 3 (fn-pic-next c fuel fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-pic-held-next)
                       (fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-pic-at)))))
(defthm fn-pic-held-next-refused-output-unfolds
  (implies (not (equal (fn-ioh-access
                         (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                         (fn-pic-get incoming-token c) :read) :holder-readonly))
    (equal (mv-list 3 (fn-pic-held-next c fuel fn-octets fn-page-read-pool))
           (list (fn-ioh-access
                   (fn-ibc-carrier-row (fn-prp-incoming-slot fn-page-read-pool))
                   (fn-pic-get incoming-token c) :read) c fuel)))
  :hints (("Goal" :in-theory (e/d (fn-pic-held-next)
                       (fn-pic-next fn-ioh-access fn-ibc-carrier-row fn-pic-at)))))

; Explicit logical frame for the actual readonly signature. This ghost is
; never served; both original stobjs occur verbatim as its effect outputs.
; This equation is intentionally by-definition, not a source-authority
; keystone. Funded installation and mutable dispatch live with the owner.
(defun-nx fn-pic-held-next-input-frame (c fuel fn-octets fn-page-read-pool)
  (declare (xargs :stobjs (fn-octets fn-page-read-pool) :verify-guards nil))
  (mv-let (word next left)
    (fn-pic-held-next c fuel fn-octets fn-page-read-pool)
    (mv word next left fn-octets fn-page-read-pool)))
(defthm fn-pic-held-next-input-frame-by-definition
  (let ((framed (mv-list 5 (fn-pic-held-next-input-frame c fuel fn-octets fn-page-read-pool))))
    (and (equal (nth 3 framed) fn-octets)
         (equal (nth 4 framed) fn-page-read-pool)
         (equal (nth 0 framed) (mv-nth 0 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
         (equal (nth 1 framed) (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
         (equal (nth 2 framed) (mv-nth 2 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))))
  :hints (("Goal" :in-theory (e/d (fn-pic-held-next-input-frame)
                                 (fn-pic-held-next fn-pic-next)))))
(defthm fn-pic-held-next-preserves-captured-row-and-input
  (equal (fn-pic-captured-context
           (mv-nth 1 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
         (fn-pic-captured-context c))
  :hints (("Goal" :in-theory (e/d (fn-pic-held-next)
                       (fn-pic-next fn-pic-captured-context fn-ioh-access fn-ibc-carrier-row)))))
(defthm fn-pic-held-next-fuel-bounded
  (implies (natp fuel)
    (and (natp (mv-nth 2 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)))
         (<= (mv-nth 2 (fn-pic-held-next c fuel fn-octets fn-page-read-pool)) fuel)))
  :hints (("Goal" :in-theory (e/d (fn-pic-held-next)
                       (fn-pic-next fn-ioh-access fn-ibc-carrier-row)))))
