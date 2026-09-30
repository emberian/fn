; Accepted-owner joins for registered connection reservations. No supplied
; demand, constructor or installed-runtime Boolean enters this interface.
; Native activation requires the actual admitted issuer and full runtime
; contract; until then these are INTERNAL source composition entry points.
(in-package "ACL2")
(include-book "owner-host")
(include-book "index-connection-pins-host")

(defun fn-mio-connection-open-preflight (id token fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word)
  (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
   (cond ((not (and (natp id) (fn-ich-tokenp token)
                    (fn-omk-widthp receipt 8)
                    (eq (fn-omk-at 0 receipt) :connection-reservation)
                    (equal (fn-omk-at 1 receipt) token)
                    (equal (fn-omk-at 2 receipt) id))) :stale)
         ((not (eq (fn-omk-at 6 receipt) :registered)) :recovery-required)
         ; Capture traverses twice; a definite refused open can require five
         ; further traversals for close/settlement. Nothing yields mid-open.
         ((< fuel (* 7 (+ 1 (fn-ibp-slot-depth fn-index-backing)))) :yield)
         (t :ready)))
  word))

(defun fn-mio-connection-finish-open (id token fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing)
  (fn-icr-finish-open id token fuel fn-index-backing)
  (mv word left fn-mio$c)))

(defun fn-mio-connection-abort (token fuel fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing fn-page-read-pool)
  (fn-icr-abort token fuel fn-index-backing fn-page-read-pool)
  (mv word left fn-mio$c fn-page-read-pool)))

(defun fn-mio-connection-settle (token fuel fn-mio$c fn-page-read-pool)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool) :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing fn-page-read-pool)
  (fn-icr-settle token fuel fn-index-backing fn-page-read-pool)
  (mv word left fn-mio$c fn-page-read-pool)))

; Result3 = (word actual-id retained-token). Error/uncertainty retains TOKEN;
; definite refusal that actually settles it returns NIL in that position.
; The caller owns the mutex across this entire operation, including the
; actual owner call. A raw escape is a service fault, never a retry signal.
(defun fn-owner-index-open
 (kind family address peer-octets token fuel fn-mio$c fn-page-read-pool state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool state) :mode :program))
 (let* ((id (fn-own-next-id (fn-owner-core state)))
        (ready (fn-mio-connection-open-preflight id token (nfix fuel) fn-mio$c)))
  (cond
   ((not (member-eq kind '(:reader :exposure :peer)))
    (mv nil (list :invalid nil token) fn-mio$c fn-page-read-pool state))
   ((not (eq ready :ready))
    (mv nil (list ready nil token) fn-mio$c fn-page-read-pool state))
   (t
    (mv-let (captured pin left fn-mio$c)
     (if (eq kind :reader)
         (fn-owner-index-connection-capture token (nfix fuel) fn-mio$c state)
       (fn-owner-index-working-connection-capture token (nfix fuel) fn-mio$c))
     (declare (ignore pin))
     (cond
      ((eq captured :captured)
       (mv-let (erp opened state)
        (case kind
         (:reader (fn-owner-open state))
         (:exposure (fn-owner-exposure-open family address peer-octets state))
         (otherwise (fn-owner-open-peer peer-octets state)))
        (cond
         ; An error is not evidence that the owner refused without effects.
         (erp (mv erp (list :recovery-required opened token) fn-mio$c fn-page-read-pool state))
         ((equal opened id)
          (mv-let (finished remaining fn-mio$c)
           (fn-mio-connection-finish-open id token (nfix left) fn-mio$c)
           (declare (ignore remaining))
           (mv nil (list (if (eq finished :opened) :opened :recovery-required) id token)
               fn-mio$c fn-page-read-pool state)))
         ((not opened)
          (mv-let (released remaining fn-mio$c fn-page-read-pool)
           (fn-mio-connection-abort token (nfix left) fn-mio$c fn-page-read-pool)
           (declare (ignore remaining))
           (mv nil (if (eq released :released) (list :refused nil nil)
                     (list :recovery-required nil token)) fn-mio$c fn-page-read-pool state)))
         (t (mv nil (list :recovery-required opened token) fn-mio$c fn-page-read-pool state)))))
      ; These words are definite no-retain outcomes from the registered phase.
      ((member-eq captured '(:unavailable :stale))
       (mv-let (released remaining fn-mio$c fn-page-read-pool)
        (fn-mio-connection-abort token (nfix left) fn-mio$c fn-page-read-pool)
        (declare (ignore remaining))
        (mv nil (if (eq released :released) (list captured nil nil)
                  (list :recovery-required nil token)) fn-mio$c fn-page-read-pool state)))
      ; Preflight already funds the whole transition, so unexpected yield or
      ; any other return after capture began is fenced, not an owner retry.
      (t (mv nil (list :recovery-required nil token) fn-mio$c fn-page-read-pool state))))))))

(defun fn-mio-connection-close-preflight (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (ready)
  (<= (* 5 (+ 1 (fn-ibp-slot-depth fn-index-backing))) fuel)
  ready))

; Revoke new aliases BEFORE the actual logical close/fault. Existing aliases
; keep the publication and grant until their separate registered return. A
; fault in the owner call cannot make those obligations disappear.
(defun fn-owner-index-close
 (id token faultp fuel fn-mio$c fn-page-read-pool fn-arena state)
 (declare (xargs :stobjs (fn-mio$c fn-page-read-pool fn-arena state) :mode :program))
 (if (not (fn-mio-connection-close-preflight (nfix fuel) fn-mio$c))
     (mv nil (list :yield id token) fn-mio$c fn-page-read-pool state)
   (mv-let (closing payload left fn-mio$c)
    (fn-mio-connection-event token :close id nil (nfix fuel) fn-mio$c)
    (declare (ignore payload))
    (if (not (eq closing :closing))
        (mv nil (list closing id token) fn-mio$c fn-page-read-pool state)
      (mv-let (erp outcome state)
       (if faultp (fn-owner-fault id state) (fn-owner-close id fn-arena state))
       (declare (ignore outcome))
       (if erp
           (mv erp (list :recovery-required id token) fn-mio$c fn-page-read-pool state)
         (mv-let (settled remaining fn-mio$c fn-page-read-pool)
          (fn-mio-connection-settle token (nfix left) fn-mio$c fn-page-read-pool)
          (declare (ignore remaining))
          (mv nil (case settled
                    (:released (list :closed id nil))
                    ((:held :busy) (list :closed-held id token))
                    (otherwise (list :recovery-required id token)))
              fn-mio$c fn-page-read-pool state))))))))
