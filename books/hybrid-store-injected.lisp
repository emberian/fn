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

(in-theory (disable (:d fn-hsig-injected-carrier-plan)
                    (:d fn-hsig-injected-carrier-octets)
                    (:d fn-hsig-authorized-injected-carried-submission-event)))
