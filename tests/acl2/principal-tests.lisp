; Witnesses and teeth for books/principal.lisp.
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/principal-invariants")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals
                          fn-stmt-invariants-vocabulary
                          fn-prin-internals
                          fn-prin-invariants-vocabulary)))

(defconst *fn-t-seed-alice* (make-list 32 :initial-element 1))
(defconst *fn-t-seed-alice-2* (make-list 32 :initial-element 3))
(defconst *fn-t-seed-mallory* (make-list 32 :initial-element 9))
(defconst *fn-t-token-default* (fn-record-string-octets "default"))
(defconst *fn-t-token-other* (fn-record-string-octets "other"))

(defun fn-t-alice-key () (fn-sig-public-key *fn-t-seed-alice*))
(defun fn-t-alice-key-2 () (fn-sig-public-key *fn-t-seed-alice-2*))
(defun fn-t-mallory-key () (fn-sig-public-key *fn-t-seed-mallory*))
(defun fn-t-alice-id () (fn-prin-id (fn-t-alice-key) *fn-t-token-default*))

; -----------------------------------------------------------------------------
; Identity derivation

(assert-event (fn-prin-idp (fn-t-alice-id)))
(assert-event (fn-prin-genesis-bindsp (fn-t-alice-id) (fn-t-alice-key)
                                      *fn-t-token-default*))
; teeth: another token, another key, another tag do not bind
(assert-event (not (fn-prin-genesis-bindsp (fn-t-alice-id) (fn-t-alice-key)
                                           *fn-t-token-other*)))
(assert-event (not (fn-prin-genesis-bindsp (fn-t-alice-id) (fn-t-mallory-key)
                                           *fn-t-token-default*)))
(assert-event (not (equal (fn-t-alice-id)
                          (fn-digest-tagged *fn-stmt-id-tag*
                                            (fn-prin-preimage
                                             (fn-t-alice-key)
                                             *fn-t-token-default*)))))
; The preimage separates key and token (proved generally); executable check:
(assert-event (equal (fn-stmt-decode-items
                      2 (fn-prin-preimage (fn-t-alice-key) *fn-t-token-default*))
                     (fn-stmt-ok (list (cons :bytes (fn-t-alice-key))
                                       (cons :bytes *fn-t-token-default*)))))
; tooth for fn-prin-preimage-injective: without the public-key shape
; hypothesis two different non-keys share a preimage.
(assert-event
 (with-guard-checking :none
  (equal (fn-prin-preimage '(300) '(1))
         (fn-prin-preimage '(301) '(1)))))
; The separating pair: the seed shape IS a public key and `(300)` is not,
; so the line below refutes the shape and not the recogniser.
(assert-event (fn-sig-public-key-p *fn-t-seed-alice*))
(assert-event (not (fn-sig-public-key-p '(300))))

; A-CRYPTO made visible: under a colliding digest two keys share an id.
(defattach fn-digest fn-toy-length-digest)
(assert-event (equal (fn-prin-id (fn-t-alice-key) *fn-t-token-default*)
                     (fn-prin-id (fn-t-mallory-key) *fn-t-token-default*)))
(assert-event (not (equal (fn-t-alice-key) (fn-t-mallory-key))))
(defattach fn-digest fn-toy-mix-digest)
(assert-event (not (equal (fn-prin-id (fn-t-alice-key) *fn-t-token-default*)
                          (fn-prin-id (fn-t-mallory-key) *fn-t-token-default*))))

; -----------------------------------------------------------------------------
; Key succession

(defun fn-t-alice-genesis ()
  (fn-prin-genesis-state (fn-t-alice-key) *fn-t-token-default* 1))
(assert-event (fn-prin-statep (fn-t-alice-genesis)))
(assert-event (equal (fn-prin-state-key (fn-t-alice-genesis)) (fn-t-alice-key)))
(assert-event (equal (fn-prin-state-next (fn-t-alice-genesis)) 1))

; The holder of the current key rotates to a new key.
(defun fn-t-succession-1 ()
  (fn-prin-sign-succession *fn-t-seed-alice* (fn-t-alice-genesis)
                           (fn-t-alice-key-2)))
(assert-event (fn-stmt-p (fn-t-succession-1)))
(assert-event (equal (fn-stmt-kind (fn-t-succession-1)) :succession))
(assert-event (equal (fn-prin-succession-key (fn-t-succession-1))
                     (fn-t-alice-key-2)))
(assert-event (fn-prin-succession-acceptablep (fn-t-alice-genesis)
                                              (fn-t-succession-1)))
(defun fn-t-alice-after-1 ()
  (fn-prin-apply-succession (fn-t-alice-genesis) (fn-t-succession-1)))
(assert-event (equal (fn-prin-state-key (fn-t-alice-after-1)) (fn-t-alice-key-2)))
(assert-event (equal (fn-prin-state-id (fn-t-alice-after-1)) (fn-t-alice-id)))
(assert-event (equal (fn-prin-state-next (fn-t-alice-after-1)) 2))

; Teeth, one per acceptance clause.
; not the holder: mallory signs a succession naming herself for alice's id
(defun fn-t-succession-forged ()
  (fn-prin-sign-succession *fn-t-seed-mallory* (fn-t-alice-genesis)
                           (fn-t-mallory-key)))
(assert-event (not (fn-prin-succession-acceptablep (fn-t-alice-genesis)
                                                   (fn-t-succession-forged))))
(assert-event (equal (fn-prin-apply-succession (fn-t-alice-genesis)
                                               (fn-t-succession-forged))
                     (fn-t-alice-genesis)))
; replay: the first succession again, after it was applied (sequence 1 != 2)
(assert-event (not (fn-prin-succession-acceptablep (fn-t-alice-after-1)
                                                   (fn-t-succession-1))))
; the old key after rotation cannot sign the next succession
(defun fn-t-succession-old-key ()
  (fn-prin-sign-succession *fn-t-seed-alice* (fn-t-alice-after-1)
                           (fn-t-mallory-key)))
(assert-event (not (fn-prin-succession-acceptablep (fn-t-alice-after-1)
                                                   (fn-t-succession-old-key))))
; the new key can
(defun fn-t-succession-2 ()
  (fn-prin-sign-succession *fn-t-seed-alice-2* (fn-t-alice-after-1)
                           (fn-t-alice-key)))
(assert-event (fn-prin-succession-acceptablep (fn-t-alice-after-1)
                                              (fn-t-succession-2)))
; wrong incarnation
(assert-event (not (fn-prin-succession-acceptablep
                    (fn-prin-make-state (fn-t-alice-id) (fn-t-alice-key) 2 1)
                    (fn-t-succession-1))))
; wrong principal id
(assert-event (not (fn-prin-succession-acceptablep
                    (fn-prin-make-state (make-list 32 :initial-element 7)
                                        (fn-t-alice-key) 1 1)
                    (fn-t-succession-1))))
; wrong kind
(assert-event (not (fn-prin-succession-acceptablep
                    (fn-t-alice-genesis)
                    (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice-id) 1 1 nil
                                  :article
                                  (fn-prin-succession-payload (fn-t-alice-key-2))))))
; payload that is not a key
(assert-event (not (fn-prin-succession-acceptablep
                    (fn-t-alice-genesis)
                    (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice-id) 1 1 nil
                                  :succession '(1 2 3)))))
; sequence exhausted
(assert-event (not (fn-prin-succession-acceptablep
                    (fn-prin-make-state (fn-t-alice-id) (fn-t-alice-key) 1
                                        *fn-cbor-max-uint*)
                    (fn-prin-sign-succession
                     *fn-t-seed-alice*
                     (fn-prin-make-state (fn-t-alice-id) (fn-t-alice-key) 1
                                         *fn-cbor-max-uint*)
                     (fn-t-alice-key-2)))))

; Resolution over a mixed list: foreign and replayed statements are skipped,
; the trail is exactly the accepted chain, and the key ends where the last
; accepted succession put it.
(defun fn-t-mixed ()
  (list (fn-t-succession-forged) (fn-t-succession-1) (fn-t-succession-1)
        (fn-t-succession-old-key) (fn-t-succession-2)))
(assert-event (equal (fn-prin-state-key
                      (fn-prin-resolve (fn-t-alice-genesis) (fn-t-mixed)))
                     (fn-t-alice-key)))
(assert-event (equal (fn-prin-state-next
                      (fn-prin-resolve (fn-t-alice-genesis) (fn-t-mixed)))
                     3))
(assert-event (equal (fn-prin-trail (fn-t-alice-genesis) (fn-t-mixed))
                     (list (fn-t-succession-1) (fn-t-succession-2))))
(assert-event (fn-prin-chain-validp (fn-t-alice-genesis)
                                    (fn-prin-trail (fn-t-alice-genesis)
                                                   (fn-t-mixed))))
(assert-event (equal (fn-prin-first-accepted (fn-t-alice-genesis) (fn-t-mixed))
                     (fn-t-succession-1)))
; teeth: a list with no holder-signed succession never moves the key
(assert-event (equal (fn-prin-resolve (fn-t-alice-genesis)
                                      (list (fn-t-succession-forged)
                                            (fn-t-succession-old-key)))
                     (fn-t-alice-genesis)))

; -----------------------------------------------------------------------------
; Keyrings

(defun fn-t-keyring ()
  (fn-prin-keyring-of-states (list (fn-t-alice-after-1))))
(assert-event (fn-prin-keyringp (fn-t-keyring)))
(assert-event (equal (fn-prin-key-for (fn-t-alice-id) (fn-t-keyring))
                     (fn-t-alice-key-2)))
(assert-event (fn-prin-verifiedp
               (fn-stmt-sign *fn-t-seed-alice-2* (fn-t-alice-id) 1 2 nil
                             :article '(1))
               (fn-t-keyring)))
; teeth: old key, unknown creator, garbage statement
(assert-event (not (fn-prin-verifiedp
                    (fn-stmt-sign *fn-t-seed-alice* (fn-t-alice-id) 1 2 nil
                                  :article '(1))
                    (fn-t-keyring))))
(assert-event (not (fn-prin-verifiedp
                    (fn-stmt-sign *fn-t-seed-alice-2*
                                  (make-list 32 :initial-element 8) 1 2 nil
                                  :article '(1))
                    (fn-t-keyring))))
(assert-event (not (fn-prin-verifiedp '(1 2 3) (fn-t-keyring))))
