; fn: the store-identity request and reply as exported wire grammars (Mini
; M4 and M5; planning/design/wire-grammar-2026-10-04.md section 5).
;
; One control request, FNCT kind 24 with an empty payload, asks the running
; owner who this store is; the owner answers FNCT kind 25:
;
;   accepted (tag 0):  format word, genesis node identity (32), schema digest
;                      (32), profile digest (32), the consumer state -- named
;                      `unbootstrapped' before its first bootstrap, else
;                      `bootstrapped' with its history id and incarnation
;                      (1..64 octets each: an identity field is never empty,
;                      and absence is an arm, not an empty field) -- the
;                      creating image's revision, the running image's
;                      revision, and the digest of the exported grammar file
;                      the running image renders (32);
;   refused  (tag 1):  a named reason: `no-genesis' (the open read no genesis
;                      record) or `consumer-state' (the consumer state's ids
;                      are not ids; never for a state fn-cp-statep accepts).
;
; These are new codecs: the interpreter at these constants IS the codec
; (books/store-identity.lisp calls fn-wg-encode and fn-wg-decode here), so
; there is no hand-written encoder to agree with.

(in-package "ACL2")
(include-book "wire-grammar")

(defconst *fn-wf-identity-request-kind* 24)
(defconst *fn-wf-identity-reply-kind* 25)

(defconst *fn-wf-identity-request-grammar*
  '(:frame (70 78 67 84) 1 24 0 (:seq)))

(defconst *fn-wf-identity-refusals* '(:no-genesis :consumer-state))

; The consumer state's identity: an arm, so that no identity field is empty.
(defconst *fn-wf-identity-consumer-grammar*
  '(:tag 1
    (0 :unbootstrapped (:seq))
    (1 :bootstrapped (:seq (:bytes 1 1 64 :any)      ; history id
                           (:bytes 1 1 64 :any)))))  ; incarnation

(defconst *fn-wf-identity-reply-grammar*
  `(:frame (70 78 67 84) 1 25 2048
    (:tag 1
     (0 :accepted (:seq (:bytes 2 1 512 :utf8)     ; format word
                        (:bytes 1 32 32 :any)      ; genesis node identity
                        (:bytes 1 32 32 :any)      ; schema digest
                        (:bytes 1 32 32 :any)      ; profile digest
                        ,*fn-wf-identity-consumer-grammar*
                        (:bytes 2 1 512 :utf8)     ; creating image's revision
                        (:bytes 2 1 512 :utf8)     ; running image's revision
                        (:bytes 1 32 32 :any)))    ; exported grammar digest
     (1 :refused (:enum 1 1 ,*fn-wf-identity-refusals*)))))

(defthm fn-wf-identity-grammars-are-grammars
  (and (fn-wg-grammarp *fn-wf-identity-request-grammar*)
       (fn-wg-grammarp *fn-wf-identity-reply-grammar*)
       (fn-wg-delimitedp *fn-wf-identity-request-grammar*)
       (fn-wg-delimitedp *fn-wf-identity-reply-grammar*)))
