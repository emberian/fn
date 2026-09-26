;; fn: the hybrid-store constructors that route a portable carrier through
;; the injecting agent.
;
; Split out of books/hybrid-store.lisp (planning/audit-2026-09-25-twins-fanin.md
; packet 1): these three definitions are the only forms of the hybrid store
; that call fn-inj-decide, and nothing else in the hybrid store calls them, so
; the 400-odd books above books/hybrid-store.lisp no longer recertify when the
; injection decision changes.  The host calls two of them by name:
; fn-hsig-injected-carrier-octets from host/native/hybrid-control.lisp and
; fn-hsig-authorized-injected-carried-submission-event from
; host/native/signatures.lisp; host/native/build.lisp and build-dtn.lisp
; include this book.  The definitions are unchanged, and each is disabled at
; the end of the book as it was in books/hybrid-store.lisp.

(in-package "ACL2")
(include-book "hybrid-store")
(include-book "injection")
(local (include-book "injection-invariants"))

; The portable carrier is not yet a locally injected news article.  Route it
; through the same ACL2 injecting agent used by POST and operator post, so
; Path, Injection-Date and Injection-Info are the node's trace projection and
; the exact signed source remains a suffix of the stored received bytes.
(defun fn-hsig-injected-carrier-plan
    (source principal keys signatures config observation)
  (declare (xargs :guard t))
  (let ((carrier (fn-hc-render-at-most *fn-article-max-octets*
                                      source principal keys signatures)))
    (cond ((not carrier) (fn-inj-refuse :carrier))
          ; D32 accepts a supplied Path on a served POST and prefixes it in
          ; place.  This route keeps refusing one, as every route did before:
          ; its received bytes carry the exact signed source as a suffix
          ; (books/hybrid-store-invariants.lisp), which a prefixed Path would
          ; not be.
          ((fn-inj-supplies-pathp carrier) (fn-inj-refuse :path-present))
          (t (fn-inj-decide carrier config observation)))))

(defun fn-hsig-injected-carrier-octets
    (source principal keys signatures config observation)
  (declare (xargs :guard t))
  (let ((plan (fn-hsig-injected-carrier-plan
               source principal keys signatures config observation)))
    (if (fn-inj-injectedp plan) (fn-inj-decision-octets plan) nil)))

; This is the native hybrid-author event constructor.  It binds the durable
; received payload to the exact ACL2 injection result, rather than trusting a
; host-supplied Path or a second host implementation of header rendering.
(defun fn-hsig-authorized-injected-carried-submission-event
    (sequence txid generation keyring-generation enrolled-snapshot
              msgid source received groups obligation-id content-subject
              release-evidence charge principal keys signatures observed-ml-key
              ed25519-observation ml-dsa-65-observation config observation)
  (declare (xargs :guard t))
  (let ((plan (fn-hsig-injected-carrier-plan
               source principal keys signatures config observation)))
    (fn-hsig-authorized-carried-submission-event-base
     sequence txid generation keyring-generation enrolled-snapshot
     msgid source received groups obligation-id content-subject
     release-evidence charge principal keys signatures observed-ml-key
     ed25519-observation ml-dsa-65-observation observation
     (and (fn-inj-injectedp plan)
          (equal received (fn-inj-decision-octets plan))))))

;; ---------------------------------------------------------------------------
;; PKT-147 (control-across-peers, PRF-170): the carrier's refusal names its
;; reason.  host/native/hybrid-control.lisp `fnn-hybrid-control-author' calls
;; `fn-hsig-injected-carrier-octets' and, when it answers nil, this function
;; for the word it reports (through books/native-hybrid-control.lisp
;; `fn-nhc-author-refusal'), instead of a bare refusal.  The reason is the
;; plan's own: `:carrier', `:path-present', or the injection decision's.
(defun fn-hsig-injected-carrier-reason
    (source principal keys signatures config observation)
  (declare (xargs :guard t))
  (let ((plan (fn-hsig-injected-carrier-plan
               source principal keys signatures config observation)))
    (if (fn-inj-injectedp plan) nil (fn-inj-decision-reason plan))))

(local (in-theory (disable fn-article-parse fn-af-proto-article-check
                           fn-article-result-okp fn-article-result-article
                           fn-article-syntax-p fn-article-get-headers
                           fn-clock-observationp fn-clock-has-wall
                           fn-clock-wall fn-clock-monotonic
                           fn-inj-proto-reason fn-inj-mandatory-reason
                           fn-inj-path-reason fn-inj-other-reason
                           fn-inj-absentp fn-inj-prefix fn-inj-block
                           fn-inj-splice fn-inj-append fn-inj-date-octets
                           fn-inj-instant-of fn-inj-generated-message-id
                           fn-inj-path-offset fn-inj-path-insert
                           fn-cbor-at-mostp fn-inj-groups-admissiblep
                           fn-inj-group-namesp fn-inj-nth
                           fn-hc-render-at-most fn-inj-supplies-pathp)))

;; The generated Message-ID reads the agent and the clock, not the groups.
(defthm fn-inj-generated-message-id-ignores-the-served-groups
  (equal (fn-inj-generated-message-id observation
                                      (fn-inj-make-config allow agent g2 max))
         (fn-inj-generated-message-id observation
                                      (fn-inj-make-config allow agent g1 max)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-inj-generated-message-id))))

;; The served set only chooses.  A source the injecting agent admits under
;; one served group list G1 is, under the node's list G2 (same agent, same
;; bound, same clock), either the identical decision -- when every group the
;; decision names is in G2 -- or the refusal :unknown-group.  Nothing else
;; in the decision reads the served list.
(defthm fn-inj-decide-served-groups-choose-only-unknown-group
  (implies (and (fn-inj-injectedp
                 (fn-inj-decide source (fn-inj-make-config allow agent g1 max)
                                observation))
                (fn-inj-group-namesp g2))
           (equal (fn-inj-decide source (fn-inj-make-config allow agent g2 max)
                                 observation)
                  (if (fn-inj-groups-admissiblep
                       (fn-inj-decision-groups
                        (fn-inj-decide source (fn-inj-make-config allow agent g1 max)
                                       observation))
                       g2)
                      (fn-inj-decide source (fn-inj-make-config allow agent g1 max)
                                     observation)
                    (fn-inj-refuse :unknown-group))))
  :hints (("Goal" :in-theory (enable fn-inj-decide fn-inj-configp fn-inj-refuse
                                   fn-inj-injectedp)
           :use fn-inj-generated-message-id-ignores-the-served-groups)))

;; KEYSTONE (PKT-147).  The host-called pair over one signed source: the
;; carrier a node would admit under some served list is, under this node's
;; list, refused by the name :unknown-group exactly when a group it names is
;; not served, and otherwise proceeds with the same octets and no reason.
(defthm fn-hsig-injected-carrier-unserved-group-is-refused-by-name
  (let ((served (fn-hsig-injected-carrier-plan
                 source principal keys signatures
                 (fn-inj-make-config allow agent g1 max) observation)))
    (implies (and (fn-hsig-injected-carrier-octets
                   source principal keys signatures
                   (fn-inj-make-config allow agent g1 max) observation)
                  (fn-inj-group-namesp g2))
             (if (fn-inj-groups-admissiblep (fn-inj-decision-groups served) g2)
                 (and (equal (fn-hsig-injected-carrier-octets
                              source principal keys signatures
                              (fn-inj-make-config allow agent g2 max) observation)
                             (fn-hsig-injected-carrier-octets
                              source principal keys signatures
                              (fn-inj-make-config allow agent g1 max) observation))
                      (equal (fn-hsig-injected-carrier-reason
                              source principal keys signatures
                              (fn-inj-make-config allow agent g2 max) observation)
                             nil))
               (and (equal (fn-hsig-injected-carrier-octets
                            source principal keys signatures
                            (fn-inj-make-config allow agent g2 max) observation)
                           nil)
                    (equal (fn-hsig-injected-carrier-reason
                            source principal keys signatures
                            (fn-inj-make-config allow agent g2 max) observation)
                           :unknown-group)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hsig-injected-carrier-plan
                                   fn-hsig-injected-carrier-octets
                                   fn-hsig-injected-carrier-reason)
                                  (fn-inj-decide)))))

(in-theory (disable (:d fn-hsig-injected-carrier-plan)
                    (:d fn-hsig-injected-carrier-octets)
                    (:d fn-hsig-authorized-injected-carried-submission-event)))
(in-theory (disable (:d fn-hsig-injected-carrier-reason)))
