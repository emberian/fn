; The identity prepare the host calls, after both batch AW lanes that
; changed it (2026-09-27): signed-post interns the wire composite into the
; arena's row first (books/owner-identity-intern.lisp; the flipped Store
; stages rows only), and prepare-served makes the configured owner refuse a
; composite whose groups the live configuration does not serve
; (books/owner-prepare-served.lisp).  This is the two composed: the served
; test over the ROW the intern makes (a wire composite is not held, so the
; test over the wire value would always pass).
;
; host/owner-host.lisp fn-owner-prepare-identity calls
; fn-oiis-prepare-identity.
(in-package "ACL2")
(include-book "owner-identity-intern")
(include-book "owner-prepare-served-ocl")

(defun fn-oiis-prepare-identity (oc w h)
  (declare (xargs :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (natp h))
                  :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-psrv-prepare-identity
     oc (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h))))

; The entry is signed-post's prepare when the row's groups are served, and
; the owner unchanged otherwise.
(defthm fn-oiis-prepare-identity-unfolds
  (equal (fn-oiis-prepare-identity oc w h)
         (let ((s (fn-own-store (fn-ocfg-owner oc))))
           (if (fn-psrv-event-servedp
                (fn-ocfg-config oc)
                (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) h))
               (fn-oii-ocfg-prepare-identity oc w h)
             oc)))
  :hints (("Goal" :in-theory '(fn-oiis-prepare-identity fn-psrv-prepare-identity
                               fn-oii-ocfg-prepare-identity))))

; KEYSTONE: the carried format-9 owner invariant survives the entry the host
; calls, for every wire value and handle (prepare-served's keystone at the
; interned row).
(defthm fn-oiis-prepare-identity-preserves-invariant
  (implies (fn-lgoc-invariantp oc)
           (fn-lgoc-invariantp (fn-oiis-prepare-identity oc w h)))
  :hints (("Goal" :in-theory '(fn-oiis-prepare-identity)
           :use ((:instance fn-psrv-prepare-identity-preserves-invariant
                  (e (fn-oii-identity-row
                      w (fn-sn-keyring (fn-own-store (fn-ocfg-owner oc)))
                      (fn-sn-keyring-generation (fn-own-store (fn-ocfg-owner oc)))
                      h)))))))
