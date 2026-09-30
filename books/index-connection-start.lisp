; INTERNAL operation composition. DEMAND and FUEL are the installed operation
; evaluator's outputs, never native request inputs. The public host entry uses
; a once-only prepaid operation ticket; this leaf establishes no installation.
(in-package "ACL2")
(include-book "index-connection-issuer")

(defun fn-ics-reserve-register
 (id demand fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
                 :guard (natp fuel)))
 ; One registration traversal plus the existing open preflight's seven.
 ; Division avoids constructing an out-of-domain product on refusal.
 (if (< (floor fuel 8) (+ 1 (fn-ibp-slot-depth fn-index-backing)))
     (mv :yield nil fuel fn-index-backing fn-page-read-pool)
   (mv-let (reserved token fn-index-backing fn-page-read-pool)
    (fn-icr-reserve id demand fn-index-backing fn-page-read-pool)
    (if (not (eq reserved :reserved))
        (mv reserved token fuel fn-index-backing fn-page-read-pool)
      (mv-let (registered left fn-index-backing)
       (fn-icr-register token fuel fn-index-backing)
       (cond
        ((and (eq registered :registered)
              (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
               (and (eq (fn-omk-at 0 receipt) :connection-reservation)
                    (equal (fn-omk-at 1 receipt) token)
                    (eq (fn-omk-at 6 receipt) :registered))))
         (mv :reserved token left fn-index-backing fn-page-read-pool))
        ; Only named definite, nonmutating registration outcomes permit abort.
        ; A malformed/stale registry or retained intent fences with its token.
        ((member-eq registered '(:unavailable :refused :yield))
         (mv-let (aborted remaining fn-index-backing fn-page-read-pool)
          (fn-icr-abort token (nfix left) fn-index-backing fn-page-read-pool)
          (if (eq aborted :released)
              (mv :refused nil remaining fn-index-backing fn-page-read-pool)
            (mv :recovery-required token remaining fn-index-backing fn-page-read-pool))))
        (t (mv :recovery-required token left fn-index-backing fn-page-read-pool))))))))

(defun fn-mio-connection-reserve-register
 (id demand fuel fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word token left fn-index-backing fn-page-read-pool)
  (fn-ics-reserve-register id demand fuel fn-index-backing fn-page-read-pool)
  (mv word token left fn-mio$c fn-page-read-pool)))

(defthm fn-ics-reserved-has-registered-receipt
 (implies (eq (mv-nth 0 (fn-ics-reserve-register id demand fuel backing pool)) :reserved)
  (let ((receipt (fn-ibp-connection-pending
                  (mv-nth 3 (fn-ics-reserve-register id demand fuel backing pool)))))
   (and (equal (fn-omk-at 1 receipt)
               (mv-nth 1 (fn-ics-reserve-register id demand fuel backing pool)))
        (eq (fn-omk-at 0 receipt) :connection-reservation)
        (eq (fn-omk-at 6 receipt) :registered))))
 :hints (("Goal" :in-theory
          (disable fn-icr-reserve fn-icr-register fn-icr-abort floor)))
 :rule-classes nil)
