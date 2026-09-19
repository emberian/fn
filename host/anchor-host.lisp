; fn: host wrappers for the external freshness anchor.  Program mode, outside
; the proof boundary.  These marshal octets and decide nothing that
; books/anchor.lisp does not already decide.
;
; `fn-anchor-sig-verify' is a constrained function and cannot be executed, so
; the Ed25519 verdict arrives as an argument, exactly as the integrity trailer
; does in host/store-host.lisp.  The octets that verdict is about are produced
; here by `fn-anchor-signed-from-root', not by the host:
; `fn-anchor-restore-observed-is-restore' and
; `fn-anchor-node-accept-observed-is-node-accept' in
; books/anchor-invariants.lisp equate these entries with the functions the
; keystones are about, under that one hypothesis.

(in-package "ACL2")
(include-book "books/anchor-invariants")

(set-state-ok t)
(program)

; An anchor reaches the bridge as its five fields, or NIL for "none".
(defun fn-anchor-host-fields (fields)
  (if (and (true-listp fields) (equal (len fields) 9))
      (fn-anchor (nth 0 fields) (nth 1 fields) (nth 2 fields) (nth 3 fields)
                 (nth 4 fields) (nth 5 fields) (nth 6 fields) (nth 7 fields)
                 (nth 8 fields))
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
(defun fn-anchor-host-accept (pinned latest-fields incarnation fields verdict)
  (let ((outcome (fn-anchor-node-accept-observed
                  (fn-anchor-node pinned (fn-anchor-host-fields latest-fields)
                                  incarnation)
                  (fn-anchor-host-fields fields) verdict)))
    (list (fn-anchor-status outcome) (fn-anchor-reason outcome))))

; The restore decision over an image the host read off disk.
(defun fn-anchor-host-restore (pinned image-incarnation image-fields
                               presented-fields verdict)
  (let ((outcome (fn-anchor-restore-observed
                  (fn-anchor-node pinned nil 0)
                  (fn-anchor-image image-incarnation
                                   (fn-anchor-host-fields image-fields))
                  (fn-anchor-host-fields presented-fields) verdict)))
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
