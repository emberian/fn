; Actual open completion -> bounded holder origin -> actual turn issuance.
; Native cannot install the binding from its own CID observation. The genuine
; runtime readout and accepted core result are consumed within this composition.
(in-package "ACL2")
(include-book "index-connection-owner-host")
(include-book "receiver-source-gate-host")

(defun fn-mio-connection-rx-path (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (path) (+ 1 (fn-ibp-slot-depth fn-index-backing)) path))

(defun fn-owner-index-rx-open
 (kind family address peer holder fuel fn-mio$c fn-rx-provider fn-receiver-turn
  fn-rx-capacity-current fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-rx-provider fn-receiver-turn
                          fn-rx-capacity-current fn-page-read-pool state)
                 :mode :program))
 (let ((path (fn-mio-connection-rx-path fn-mio$c)))
  ; Original open owns at most seven traversals, association owns one. Do not
  ; spend the same fuel twice or start an accepted open without its suffix.
  (if (< (nfix fuel) (* 8 path))
      (mv nil (list :yield nil holder) fn-mio$c fn-page-read-pool state)
   (mv-let (runtime capacity instance)
    (fn-owner-runtime-receiver-source fn-rx-provider fn-receiver-turn
                                      fn-rx-capacity-current fn-page-read-pool state)
    (if (not (eq runtime :current))
        (mv-let (released left fn-mio$c fn-page-read-pool)
         (fn-mio-connection-abort holder (nfix fuel) fn-mio$c fn-page-read-pool)
         (declare (ignore left))
         (mv nil (if (eq released :released) (list :unavailable nil nil)
                   (list :recovery-required nil holder))
             fn-mio$c fn-page-read-pool state))
     (mv-let (erp result fn-mio$c fn-page-read-pool state)
      (fn-owner-index-open kind family address peer holder (- (nfix fuel) path)
                            fn-mio$c fn-page-read-pool state)
      (if (or erp (not (eq (fn-omk-at 0 result) :opened)))
          (mv erp result fn-mio$c fn-page-read-pool state)
       (mv-let (current capacity1 instance1)
        (fn-owner-runtime-receiver-source fn-rx-provider fn-receiver-turn
                                          fn-rx-capacity-current fn-page-read-pool state)
        (let ((origin (fn-crx-open-origin result capacity1 instance1)))
         (if (not (and (eq current :current) origin
                        (equal capacity capacity1) (equal instance instance1)))
             (mv nil (list :recovery-required (fn-omk-at 1 result)
                           (fn-omk-at 2 result)) fn-mio$c fn-page-read-pool state)
          (mv-let (bound payload left fn-mio$c)
           (fn-mio-connection-event (fn-omk-at 2 result) :rx-bind
                                     (fn-omk-at 1 result) origin path fn-mio$c)
           (declare (ignore payload left))
           (mv nil (if (eq bound :associated) result
                     (list :recovery-required (fn-omk-at 1 result)
                           (fn-omk-at 2 result)))
               fn-mio$c fn-page-read-pool state)))))))))))
)

; INTERNAL scheduler composition: DEMAND is still an operation producer
; obligation. Neither this argument nor an origin is a runtime allowance.
; The installed runtime readout currently refuses until qualification exists.
(defun fn-owner-rx-connection-turn-start
 (id holder fuel demand fn-mio$c fn-rx-provider fn-receiver-turn
  fn-rx-capacity-current fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-rx-provider fn-receiver-turn
                          fn-rx-capacity-current fn-page-read-pool state)
                 :mode :program))
 (mv-let (runtime capacity instance)
  (fn-owner-runtime-receiver-source fn-rx-provider fn-receiver-turn
                                    fn-rx-capacity-current fn-page-read-pool state)
  (if (not (eq runtime :current))
      (mv :receiver-unavailable nil fn-mio$c fn-receiver-turn fn-page-read-pool state)
   (mv-let (word origin left fn-mio$c)
    (fn-mio-connection-event holder :rx-origin id nil (nfix fuel) fn-mio$c)
    (declare (ignore left))
    (if (not (and (eq word :current)
                  (fn-crx-origin-currentp origin id holder capacity instance)))
        (mv (if (eq word :yield) :yield :receiver-unavailable) nil
            fn-mio$c fn-receiver-turn fn-page-read-pool state)
     (mv-let (started ticket fn-receiver-turn fn-page-read-pool)
      (fn-owner-rx-turn-start capacity demand fn-rx-provider
                              fn-receiver-turn fn-page-read-pool)
      (if (not (eq started :admitted))
          (mv started nil fn-mio$c fn-receiver-turn fn-page-read-pool state)
       (let* ((issued (fn-crx-issued origin started ticket))
              (state (f-put-global 'fn-owner-rx-connection-issued issued state)))
        (mv (if issued :admitted :recovery-required) ticket
            fn-mio$c fn-receiver-turn fn-page-read-pool state))))))))
)

(defun fn-owner-index-rx-close
 (id holder faultp fuel fn-mio$c fn-page-read-pool fn-arena state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool fn-arena state) :mode :program))
 (let ((path (fn-mio-connection-rx-path fn-mio$c)))
  (if (< (nfix fuel) (* 6 path))
      (mv nil (list :yield id holder) fn-mio$c fn-page-read-pool state)
   (mv-let (revoked payload left fn-mio$c)
    (fn-mio-connection-event holder :rx-revoke id nil path fn-mio$c)
    (declare (ignore payload left))
    (if (not (eq revoked :revoked))
        (mv nil (list :recovery-required id holder) fn-mio$c fn-page-read-pool state)
     (let ((state (fn-owner-rx-connection-revoke id holder state)))
      (fn-owner-index-close id holder faultp (- (nfix fuel) path)
                             fn-mio$c fn-page-read-pool fn-arena state)))))))
