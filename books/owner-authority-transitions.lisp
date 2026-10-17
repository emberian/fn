; Exact publication composition, before owner/state installation.
; Props: an unexpected published root refuses without any installation;
; otherwise preserve the existing readiness test, adopted-root aliases and
; canonical invalidation. No absence is interpreted as ready authority.
(in-package "ACL2")
(include-book "owner-authority-state")
(include-book "owner-config")

(defun fn-oauth-publication (r full4 epoch)
  (declare (xargs :guard t))
  (let* ((word (fn-cp-nth 0 full4))
         (next (fn-cp-nth 1 full4))
         (metadata (fn-cp-nth 2 full4))
         (published-root (fn-cp-nth 3 full4))
         (old-sidecar (fn-oauth-root r))
         (old-canonical (fn-oauth-canonical r)))
    (if published-root
        (mv nil :recovery-required nil r)
      (let* ((cp (fn-sn-consumer (fn-own-store (fn-ocfg-owner next))))
             (authority (fn-cp-nth 6 cp))
             (sidecar
               (and old-sidecar
                    (if (and (equal word :durable) metadata
                             (equal (fn-cp-nth 0 old-sidecar) :ready)
                             (equal epoch (fn-cp-nth 1 old-sidecar))
                             (equal (fn-cp-nth 3 authority) (fn-cp-nth 2 old-sidecar)))
                        (list :ready epoch (fn-cp-nth 3 authority)
                              (fn-cp-nth 1 authority) (fn-cp-nth 4 old-sidecar)
                              (fn-cp-nth 5 old-sidecar))
                      (cons :unavailable (fn-ag-cdr old-sidecar))))))
        (mv t word next
            (fn-oauth-make metadata sidecar
                          (and old-canonical (cons :unavailable (fn-ag-cdr old-canonical)))))))))

(defthm fn-oauth-publication-preserves-shape
  (implies (fn-oauth-shapep r)
           (fn-oauth-shapep (mv-nth 3 (fn-oauth-publication r full4 epoch))))
  :hints (("Goal" :in-theory (disable fn-cp-nth fn-sn-consumer fn-own-store fn-ocfg-owner))))

(defthm fn-oauth-publication-rejects-published-root
  (implies (fn-cp-nth 3 full4)
           (and (not (mv-nth 0 (fn-oauth-publication r full4 epoch)))
                (equal (mv-nth 1 (fn-oauth-publication r full4 epoch)) :recovery-required)
                (equal (mv-nth 3 (fn-oauth-publication r full4 epoch)) r))))

(defthm fn-oauth-publication-does-not-invent-root
  (implies (not (fn-oauth-root r))
           (not (fn-oauth-root (mv-nth 3 (fn-oauth-publication r full4 epoch)))))
  :hints (("Goal" :in-theory (disable fn-cp-nth fn-sn-consumer fn-own-store fn-ocfg-owner))))

; Independent equations for the old output word, owner install and three
; global writes. The equation uses the tuple constructor, never PUT.
(defthm fn-oauth-publication-composition-by-definition
  (let* ((word (fn-cp-nth 0 full4))
         (next (fn-cp-nth 1 full4))
         (metadata (fn-cp-nth 2 full4))
         (published-root (fn-cp-nth 3 full4))
         (old-sidecar (fn-oauth-root r))
         (old-canonical (fn-oauth-canonical r))
         (authority (fn-cp-nth 6 (fn-sn-consumer (fn-own-store (fn-ocfg-owner next)))))
         (sidecar
          (and old-sidecar
               (if (and (equal word :durable) metadata
                        (equal (fn-cp-nth 0 old-sidecar) :ready)
                        (equal epoch (fn-cp-nth 1 old-sidecar))
                        (equal (fn-cp-nth 3 authority) (fn-cp-nth 2 old-sidecar)))
                   (list :ready epoch (fn-cp-nth 3 authority)
                         (fn-cp-nth 1 authority) (fn-cp-nth 4 old-sidecar)
                         (fn-cp-nth 5 old-sidecar))
                 (cons :unavailable (cdr old-sidecar)))))
         (result (fn-oauth-publication r full4 epoch)))
    (and (equal (mv-nth 0 result) (not published-root))
         (equal (mv-nth 1 result) (if published-root :recovery-required word))
         (equal (mv-nth 2 result) (if published-root nil next))
         (equal (mv-nth 3 result)
                (if published-root r
                  (fn-oauth-make metadata sidecar
                                (and old-canonical (cons :unavailable (cdr old-canonical))))))))
  :hints (("Goal" :in-theory (disable fn-cp-nth fn-sn-consumer fn-own-store fn-ocfg-owner))))

(in-theory (disable fn-oauth-publication))
