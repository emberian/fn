; The association is produced only by the actual accepted-open composition.
; These fixed-record functions do not make a supplied observation authority.
; The holder token carries its issued identity, segment and physical slot;
; the RX identity comes from the SAME installed provider/turn/pool readout.
(in-package "ACL2")
(include-book "index-connection-holder")

(defun fn-crx-originp (origin)
 (declare (xargs :guard t))
 (and (fn-omk-widthp origin 5)
      (eq (fn-omk-at 0 origin) :connection-rx-origin)
      (natp (fn-omk-at 1 origin))
      (fn-ich-tokenp (fn-omk-at 2 origin))
      (fn-omk-at 3 origin)
      (natp (fn-omk-at 4 origin))))

; RESULT is the returned actual FnOwnerIndexOpen result, never a native
; reconstruction. The composed caller passes no ERP here: any ERP fences first.
(defun fn-crx-open-origin (result capacity instance)
 (declare (xargs :guard t))
 (if (and (fn-omk-widthp result 3)
          (eq (fn-omk-at 0 result) :opened)
          (natp (fn-omk-at 1 result))
          (fn-ich-tokenp (fn-omk-at 2 result))
          capacity (natp instance))
     (list :connection-rx-origin (fn-omk-at 1 result)
           (fn-omk-at 2 result) capacity instance)
   nil))

(defun fn-crx-origin-currentp (origin id holder capacity instance)
 (declare (xargs :guard t))
 (and (fn-crx-originp origin)
      (equal id (fn-omk-at 1 origin))
      (equal holder (fn-omk-at 2 origin))
      (equal capacity (fn-omk-at 3 origin))
      (equal instance (fn-omk-at 4 origin))))

; Fixed3, retaining the SAME origin instead of creating a second copy. The
; only composed producer runs after actual turn issuance, before any copy.
(defun fn-crx-issued (origin word ticket)
 (declare (xargs :guard t))
 (if (and (fn-crx-originp origin) (eq word :admitted)
          (fn-omk-widthp ticket 2)
          (eq (fn-omk-at 0 ticket) :receiver-turn)
          (natp (fn-omk-at 1 ticket)))
     (list :connection-rx-turn origin ticket)
   nil))

(defun fn-crx-turn-currentp (issued id holder ticket capacity instance)
 (declare (xargs :guard t))
 (and (fn-omk-widthp issued 3)
      (eq (fn-omk-at 0 issued) :connection-rx-turn)
      (equal ticket (fn-omk-at 2 issued))
      (fn-crx-origin-currentp (fn-omk-at 1 issued)
                             id holder capacity instance)))

; Closing revokes only acquisition authority. The actual parser/response
; lifetime remains retained by its own controller until its terminal receipt.
(defun fn-crx-revoke (issued id holder)
 (declare (xargs :guard t))
 (let ((origin (fn-omk-at 1 issued)))
  (if (and (fn-crx-originp origin)
           (equal id (fn-omk-at 1 origin))
           (equal holder (fn-omk-at 2 origin))) nil issued)))

; Bounded segment storage. A recycled physical slot never lends an earlier
; holder's RX origin to its new issued token. No caller performs first-use bind.
(defun fn-ich-rx-origin (id holder fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let ((row (fn-ich-row holder fn-ibp-connection-segment)))
  (if (not (and (fn-ich-tokenp holder)
                (eq (fn-omk-at 4 row) :live)
                (equal id (fn-omk-at 2 row))))
      (mv :stale nil)
   (let ((origin (fn-ich-rx-originsi (fn-omk-at 3 holder)
                                    fn-ibp-connection-segment)))
    (if (and (fn-crx-originp origin)
             (equal id (fn-omk-at 1 origin))
             (equal holder (fn-omk-at 2 origin)))
        (mv :current origin) (mv :receiver-unavailable nil))))))

(defun fn-ich-rx-bind (id holder origin fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let ((row (fn-ich-row holder fn-ibp-connection-segment)))
  (if (not (and (fn-ich-tokenp holder)
                (eq (fn-omk-at 4 row) :live)
                (equal id (fn-omk-at 2 row))
                (fn-crx-originp origin)
                (equal id (fn-omk-at 1 origin))
                (equal holder (fn-omk-at 2 origin))))
      (mv :stale fn-ibp-connection-segment)
   (let ((old (fn-ich-rx-originsi (fn-omk-at 3 holder)
                                 fn-ibp-connection-segment)))
    (cond ((equal old origin) (mv :associated fn-ibp-connection-segment))
          ((and (fn-crx-originp old)
                (equal holder (fn-omk-at 2 old)))
           (mv :recovery-required fn-ibp-connection-segment))
          (t (let ((fn-ibp-connection-segment
                    (update-fn-ich-rx-originsi (fn-omk-at 3 holder) origin
                                              fn-ibp-connection-segment)))
               (mv :associated fn-ibp-connection-segment))))))))

; Revoke future turn issuance before the actual close/fault. A separate issued
; receipt can still retain its immutable origin for terminal custody handling.
(defun fn-ich-rx-revoke (id holder fn-ibp-connection-segment)
 (declare (xargs :stobjs fn-ibp-connection-segment :guard t))
 (let ((row (fn-ich-row holder fn-ibp-connection-segment)))
  (if (not (and (fn-ich-tokenp holder)
                (equal id (fn-omk-at 2 row))
                (member-eq (fn-omk-at 4 row) '(:live :closing))))
      (mv :stale fn-ibp-connection-segment)
   (let ((fn-ibp-connection-segment
          (update-fn-ich-rx-originsi (fn-omk-at 3 holder) nil
                                    fn-ibp-connection-segment)))
    (mv :revoked fn-ibp-connection-segment)))))
