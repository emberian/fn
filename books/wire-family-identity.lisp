; fn: the store-identity request and reply as exported wire grammars (Mini
; M4 and M5; planning/design/wire-grammar-2026-10-04.md section 5).
;
; One control request, FNCT kind 24 with an empty payload, asks the running
; owner who this store is; the owner answers FNCT kind 25:
;
;   accepted (tag 0):  format word, genesis node identity (32), schema digest
;                      (32), profile digest (32), history id and incarnation
;                      (0..64 each: empty while the consumer state has no
;                      bootstrap), the creating image's revision, the running
;                      image's revision, and the digest of the exported
;                      grammar file the running image renders (32);
;   refused  (tag 1):  a named reason.
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

(defconst *fn-wf-identity-refusals* '(:no-genesis))

(defconst *fn-wf-identity-reply-grammar*
  '(:frame (70 78 67 84) 1 25 2048
    (:tag 1
     (0 :accepted (:seq (:bytes 2 1 512 :utf8)     ; format word
                        (:bytes 1 32 32 :any)      ; genesis node identity
                        (:bytes 1 32 32 :any)      ; schema digest
                        (:bytes 1 32 32 :any)      ; profile digest
                        (:bytes 1 0 64 :any)       ; history id
                        (:bytes 1 0 64 :any)       ; incarnation
                        (:bytes 2 1 512 :utf8)     ; creating image's revision
                        (:bytes 2 1 512 :utf8)     ; running image's revision
                        (:bytes 1 32 32 :any)))    ; exported grammar digest
     (1 :refused (:enum 1 1 (:no-genesis))))))

(defthm fn-wf-identity-grammars-are-grammars
  (and (fn-wg-grammarp *fn-wf-identity-request-grammar*)
       (fn-wg-grammarp *fn-wf-identity-reply-grammar*)
       (fn-wg-delimitedp *fn-wf-identity-request-grammar*)
       (fn-wg-delimitedp *fn-wf-identity-reply-grammar*)))
