; K3 and K4: the byte-level crash keystones that stand on K2.
;
; specs/crash-model-v2.md section 3.3.  K1 and K2 live in
; books/byte-store-scan.lisp, whose include-closure is the byte model and
; the file kernel.  K3 needs nothing more, but K4 is a statement about the
; HOST's reopen entry (fn-sn-open-observed, which host/store-node-host.lisp
; calls at every process start), so it needs books/store-observed and the
; store-node closure under it.  That is the seam this book exists at: no
; theorem here reasons about bytes, each is one kernel theorem applied to
; K2's conclusion.
;
; Every proof below runs in (theory 'minimal-theory) with each fact cited.
; That is not a shortcut around a fan: the terms here are the scan of an
; image, and in the ambient theory the rewriter descends them one cons at a
; time to its call-depth limit of 1000 -- no loop, no useful rule, no
; checkpoint.  books/byte-store-scan.lisp records the same measurement at
; three of its own forms.

(in-package "ACL2")
(include-book "byte-store-scan")
(include-book "store-observed")

; -----------------------------------------------------------------------------
; K3.  The constructor as a corollary: fn-sf-image-crash, applied to the
; image the scan reads, reproduces it exactly, and lands the kernel in
; :replaying -- which is the phase host/store-node-host.lisp:39 builds.
; fn-sf-recovery-crash-realizes-every-admissible-image is the work and
; covers all four arms (D14-b, D14-c); K3 is that theorem at K2's image.
(defthm fn-bs-store-recovery-is-a-kernel-crash
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (let* ((scan (fn-bs-scan-store image))
                  (crashed (fn-sf-image-crash ks (fn-bs-scan-frontier scan)
                                              (fn-bs-scan-records scan))))
             (and (equal (fn-sf-frontier crashed) (fn-bs-scan-frontier scan))
                  (equal (fn-sf-records crashed) (fn-bs-scan-records scan))
                  (equal (fn-sf-phase crashed) :replaying))))
  :hints (("Goal"
           :use (fn-bs-store-crash-image-is-kernel-admissible
                 (:instance fn-sf-recovery-crash-realizes-every-admissible-image
                            (s ks)
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; K4, first half, and the one with no vacuous instance: the host's reopen
; entry SUCCEEDS on every byte-level crash image of a related state, in both
; windows and whatever the pending entry operation did.  This is the half
; the wider predicate made new (fn-sn-recovery-admissible-image-reopens,
; lane w11/bytestore-k2); over fn-sf-crash-imagep it could not be stated at
; all in the recovery window.
(defthm fn-bs-crash-image-reopens
  (implies (and (fn-snt-relation s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image))
           (fn-sn-open-okp
            (fn-sn-open-observed
             (fn-sn-groups s) (fn-sn-capacity s)
             (fn-bs-scan-frontier (fn-bs-scan-store image))
             (fn-bs-scan-records (fn-bs-scan-store image)))))
  :hints (("Goal"
           :use ((:instance fn-bs-store-crash-image-is-kernel-admissible
                            (ks (fn-sn-files s)))
                 (:instance fn-sn-recovery-admissible-image-reopens
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))

; K4.  Acknowledged retention across a BYTE crash: an outcome this store
; acknowledged before the crash names a record of the state the host reopens
; on.  The record half is clause 5 of fn-sf-recovery-admissible-image-facts
; carried through fn-sn-open-observed-success-exact-history, which says the
; reopened file state holds exactly the observed records.
;
; HONEST SCOPE.  Its recovery-window instances are vacuous and its publish
; window instances are not: fn-bs-replay-matches-scan carries (equal
; (fn-sf-successes ks) nil), so a state with an acknowledged outcome is
; outside the window and this theorem is a statement about the publish
; window alone.  That is not a defect of the statement but the physical
; fact D14-b records -- a process that is still recovering has acknowledged
; nothing of its own.  What covers the recovery window is
; fn-bs-crash-image-reopens above, which carries no success hypothesis.
; The kernel lane's judgement stands and is not reopened here: the
; acknowledged-record half is NOT restated over fn-sf-recovery-crash-imagep
; at the kernel, because there both rollback arms would be vacuous with
; nothing left; here the premise is the byte relation and the publish window
; is a live, non-degenerate instance.
(defthm fn-bs-acknowledged-record-survives-byte-crash
  (implies (and (fn-snt-relation s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (let ((opened (fn-sn-open-observed
                          (fn-sn-groups s) (fn-sn-capacity s)
                          (fn-bs-scan-frontier (fn-bs-scan-store image))
                          (fn-bs-scan-records (fn-bs-scan-store image)))))
             (and (fn-sn-open-okp opened)
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-sn-open-state opened)))))))
  :hints (("Goal"
           :use (fn-bs-crash-image-reopens
                 (:instance fn-bs-store-crash-image-is-kernel-admissible
                            (ks (fn-sn-files s)))
                 (:instance fn-sf-recovery-admissible-image-facts
                            (s (fn-sn-files s))
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image))))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))
