; fn: host wrappers for the external freshness anchor.  Program mode, outside
; the proof boundary.  These marshal octets and decide nothing that
; books/anchor.lisp does not already decide.
;
; `fn-anchor-sig-verify' and `fn-anchor-leaf-digest' are constrained functions
; and cannot be executed, so each one's value arrives as an argument, exactly
; as the integrity trailer does in host/store-host.lisp.  There are two, one
; per seam: `verdict' is `fn-anchor-signatures-okp' (the two Ed25519 checks)
; and `one-nonce' is `fn-anchor-one-nonce-p' (this response covers one nonce
; and it is ours).  The delegation window is ACL2's and is applied inside
; these entries.  The octets the verdict is about are produced here by
; `fn-anchor-signed-from-root', not by the host:
; `fn-anchor-restore-observed-is-restore',
; `fn-anchor-node-accept-observed-is-node-accept' and
; `fn-anchor-node-advance-observed-is-node-advance' in
; books/anchor-invariants.lisp equate these entries with the functions the
; keystones are about, under that one hypothesis.

(in-package "ACL2")
(include-book "../books/anchor-invariants")

(set-state-ok t)
(program)

; An anchor reaches the bridge as its ten fields, or NIL for "none".  The
; tenth is ROOT, off the wire: `books/anchor.lisp' reads the signed octets
; from it rather than recomputing them, so a batched response reaches the
; model as what it is and is reported `:uncertain :unmodelled-tree' there.
(defun fn-anchor-host-fields (fields)
  (if (and (true-listp fields) (equal (len fields) 10))
      (fn-anchor (nth 0 fields) (nth 1 fields) (nth 2 fields) (nth 3 fields)
                 (nth 4 fields) (nth 5 fields) (nth 6 fields) (nth 7 fields)
                 (nth 8 fields) (nth 9 fields))
    nil))

(defun fn-anchor-host-wellformedp (fields)
  (if (fn-anchor-p (fn-anchor-host-fields fields)) 1 0))

; The octets the server signed, rebuilt by ACL2 for the host to verify.
(defun fn-anchor-host-signed-octets (radius midpoint root)
  (fn-anchor-signed-from-root radius midpoint root))

; The delegation octets the pinned long-term key signed, for the host to check.
(defun fn-anchor-host-delegation-octets (fields)
  (let ((a (fn-anchor-host-fields fields)))
    (if (not (fn-anchor-p a)) :bad (fn-anchor-delegation-signed-octets a))))

; The durable FNAN record: the incarnation and the anchor it stands under.
; ACL2 returns the octets the integrity trailer covers; the host appends
; SHA-256 of exactly those octets and nothing else, as it does for FNST.
(defun fn-anchor-host-protected (incarnation fields)
  (let ((values (cons incarnation fields)))
    (if (not (fn-anchor-record-okp :incarnation values))
        :bad
      (fn-frame-protected *fn-anchor-magic* *fn-frame-version*
                          (fn-frame-enum-index :incarnation *fn-anchor-kinds*)
                          (fn-frame-fields-octets
                           (fn-frame-spec-for :incarnation *fn-anchor-specs*)
                           values)))))

(defun fn-anchor-host-decode (octets digest)
  (let ((result (fn-anchor-decode octets digest)))
    (if (or (not (fn-frame-result-okp result))
            (not (equal (fn-frame-result-kind result) :incarnation)))
        :bad
      (fn-frame-result-payload result))))

; Accepting one observation into the node's durable anchor state.
(defun fn-anchor-host-accept (pinned latest-fields incarnation fields verdict
                              one-nonce)
  (let ((outcome (fn-anchor-node-accept-observed
                  (fn-anchor-node pinned (fn-anchor-host-fields latest-fields)
                                  incarnation)
                  (fn-anchor-host-fields fields) verdict one-nonce)))
    (list (fn-anchor-status outcome) (fn-anchor-reason outcome))))

; Advancing this node's incarnation under one observation.  OBJ-006: the new
; incarnation is opened only under an anchor strictly newer than the one the
; node holds, which `fn-anchor-incarnation-advances-only-under-a-newer-anchor'
; is about.
(defun fn-anchor-host-advance (pinned latest-fields incarnation fields verdict
                               one-nonce)
  (let ((outcome (fn-anchor-node-advance-observed
                  (fn-anchor-node pinned (fn-anchor-host-fields latest-fields)
                                  incarnation)
                  (fn-anchor-host-fields fields) verdict one-nonce)))
    (list (fn-anchor-status outcome)
          (fn-anchor-reason outcome)
          (if (equal (fn-anchor-status outcome) :accepted)
              (fn-anchor-node-incarnation (fn-anchor-payload outcome))
            incarnation))))

; The restore decision over an image the host read off disk.
(defun fn-anchor-host-restore (pinned image-incarnation image-fields
                               presented-fields verdict one-nonce)
  (let ((outcome (fn-anchor-restore-observed
                  (fn-anchor-node pinned nil 0)
                  (fn-anchor-image image-incarnation
                                   (fn-anchor-host-fields image-fields))
                  (fn-anchor-host-fields presented-fields) verdict one-nonce)))
    (list (fn-anchor-status outcome)
          (fn-anchor-reason outcome)
          (if (equal (fn-anchor-status outcome) :accepted)
              (fn-anchor-node-incarnation (fn-anchor-payload outcome))
            image-incarnation))))

; Two images of one origin: fork, the same image, or distinct incarnations.
(defun fn-anchor-host-pair (left-incarnation left-fields
                            right-incarnation right-fields)
  (let ((outcome (fn-anchor-pair-admit
                  (fn-anchor-image left-incarnation
                                   (fn-anchor-host-fields left-fields))
                  (fn-anchor-image right-incarnation
                                   (fn-anchor-host-fields right-fields)))))
    (list (fn-anchor-status outcome) (fn-anchor-reason outcome))))

;; Restore the logic-mode default: the store bridge waits for the
;; "ACL2 !>" prompt, and a host file that leaves the session in program
;; mode ("ACL2 p!>") makes every bridge call time out.
(logic)
