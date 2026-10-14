; STATE supporting corollaries through the production host bridge.
(in-package "ACL2")
(include-book "../../host/owner-host")

; Supporting STATE corollaries, redundant after the host include. Their
; book declarations make the supporting citations visible to the book ledger;
; their proofs remain the host bridge instances, with no new arithmetic proof.
(defthm fn-owner-memory-gate-charges-every-pinned-connection
  (implies (and (boundp-global 'fn-owner state)
                (member-equal c (fn-own-conns (fn-owner-core state))))
           (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                  *fn-cbud-reply-status-octets*)
               (fn-mm-large-reply profile
                                  (fn-adm-priced-cfg (fn-owner-memory-run-cfg r v cfg state) held cap)))))

(defthm fn-owner-live-apply-keeps-every-pin-charged
  (implies (and (boundp-global 'fn-owner state)
                (member-equal c (fn-own-conns (fn-owner-core state))))
           (let ((state2 (mv-nth 2 (fn-owner-apply-limit-profile values state))))
             (<= (+ (* 2 (nfix (fn-inj-config-max-octets (fn-own-conn-config c))))
                    *fn-cbud-reply-status-octets*)
                 (fn-mm-large-reply (fn-owner-store-profile state2)
                                    (fn-adm-priced-cfg (fn-owner-memory-run-cfg r v cfg state2) held cap))))))

(defthm fn-owner-memory-gate-charge-falls-to-the-current-profile
  (implies (and (boundp-global 'fn-owner state)
                (<= (fn-adm-pin-octets (fn-own-conns (fn-owner-core state)))
                    (nfix (fn-bs-profile-max-article-octets profile)))
                (<= (fn-owner-memory-stored-most state)
                    (nfix (fn-bs-profile-max-article-octets profile))))
           (equal (fn-mm-served-article-octets
                   profile (fn-adm-priced-cfg (fn-owner-memory-run-cfg r v cfg state) held cap))
                  (nfix (fn-bs-profile-max-article-octets profile)))))
