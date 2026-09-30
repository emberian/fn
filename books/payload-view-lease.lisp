; PRF-1133: fixed logical incarnation lease for the exclusive snapshot slot.
; The caller supplies an already issued capture ticket and admitted maintenance
; lease. This book does not infer funding or captured-row authorization.
(in-package "ACL2")
(include-book "snapshot-source-token")
(defun fn-pvl-tokenp (x)
  (declare (xargs :guard t))
  (and (fn-omk-widthp x 4) (eq (fn-omk-at 0 x) :payload-view)
       (natp (fn-omk-at 1 x)) (natp (fn-omk-at 2 x))
       (natp (fn-omk-at 3 x))))
(defun fn-pvl-token-matchp (a b)
  (declare (xargs :guard t))
  (and (fn-pvl-tokenp a) (fn-pvl-tokenp b)
       (equal (fn-omk-at 1 a) (fn-omk-at 1 b))
       (equal (fn-omk-at 2 a) (fn-omk-at 2 b))
       (equal (fn-omk-at 3 a) (fn-omk-at 3 b))))
; Incarnation, spent-ticket high water, active (token resource-lease) or NIL.
; High water borrows the actual capture identity; it is not another issuer.
(defun fn-pvl-seed () (declare (xargs :guard t)) (list 0 nil nil))
(defun fn-pvl-ledgerp (s)
  (declare (xargs :guard t))
  (let ((inc (fn-omk-at 0 s)) (last (fn-omk-at 1 s))
        (active (fn-omk-at 2 s)))
    (and (fn-omk-widthp s 3) (natp inc) (or (null last) (natp last))
         (or (null active)
             (and (fn-omk-widthp active 2)
                  (fn-pvl-tokenp (fn-omk-at 0 active))
                  (equal (fn-omk-at 1 (fn-omk-at 0 active)) inc)
                  (equal (fn-omk-at 3 (fn-omk-at 0 active)) last))))))
(defun fn-pvl-livep (token s)
  (declare (xargs :guard t))
  (and (fn-pvl-ledgerp s)
       (fn-pvl-token-matchp token (fn-omk-at 0 (fn-omk-at 2 s)))))
(defun fn-pvl-acquire (s prefix capture-ticket resource-lease)
  (declare (xargs :guard t))
  (cond ((not (and (fn-pvl-ledgerp s) (natp prefix)
                   (natp capture-ticket) resource-lease))
         (list :refused :payload-view-domain s))
        ((fn-omk-at 2 s) (list :refused :payload-view-busy s))
        ((and (natp (fn-omk-at 1 s))
              (<= capture-ticket (fn-omk-at 1 s)))
         (list :refused :payload-view-spent-ticket s))
        (t (let ((token (list :payload-view (fn-omk-at 0 s)
                             prefix capture-ticket)))
             (list :acquired token
                   (list (fn-omk-at 0 s) capture-ticket
                         (list token resource-lease)))))))
(defun fn-pvl-release (s token settlement)
  (declare (xargs :guard t))
  (cond ((not (fn-pvl-livep token s)) (list :refused :payload-view-stale s))
        ((not (eq settlement :joined)) (list :retained :cleanup-pending s))
        (t (list :released token
                 (list (fn-omk-at 0 s) (fn-omk-at 1 s) nil)))))
(defun fn-pvl-reset (s)
  (declare (xargs :guard t))
  (cond ((not (fn-pvl-ledgerp s)) (list :refused :payload-view-domain s))
        ((fn-omk-at 2 s) (list :refused :payload-view-live s))
        (t (list :reset nil
                 (list (+ 1 (fn-omk-at 0 s)) (fn-omk-at 1 s) nil)))))
(defthm fn-pvl-acquire-establishes-live-incarnation
  (implies (equal (car (fn-pvl-acquire s prefix ticket resource)) :acquired)
           (let ((next (fn-omk-at 2 (fn-pvl-acquire s prefix ticket resource)))
                 (token (fn-omk-at 1 (fn-pvl-acquire s prefix ticket resource))))
             (and (fn-pvl-ledgerp next) (fn-pvl-livep token next)
                  (equal (fn-omk-at 1 token) (fn-omk-at 0 s))
                  (equal (fn-omk-at 2 token) prefix)
                  (equal (fn-omk-at 3 token) ticket))))
  :hints (("Goal" :in-theory (enable fn-pvl-acquire fn-pvl-ledgerp fn-pvl-livep
                                   fn-pvl-tokenp fn-pvl-token-matchp
                                   fn-omk-at fn-omk-widthp))))
(defthm fn-pvl-refused-acquisition-keeps-ownership
  (implies (not (equal (car (fn-pvl-acquire s prefix ticket resource)) :acquired))
           (equal (fn-omk-at 2 (fn-pvl-acquire s prefix ticket resource)) s))
  :hints (("Goal" :in-theory (enable fn-omk-at))))
(defthm fn-pvl-unjoined-release-keeps-live-ownership
  (implies (and (fn-pvl-livep token s) (not (eq settlement :joined)))
           (and (equal (car (fn-pvl-release s token settlement)) :retained)
                (equal (fn-omk-at 2 (fn-pvl-release s token settlement)) s)))
  :hints (("Goal" :in-theory (enable fn-omk-at))))
(defthm fn-pvl-release-requires-exact-live-token-and-joined-cleanup
  (iff (equal (car (fn-pvl-release s token settlement)) :released)
       (and (fn-pvl-livep token s) (eq settlement :joined))))
(defthm fn-pvl-reset-refuses-a-live-view
  (implies (fn-omk-at 2 s)
           (and (equal (car (fn-pvl-reset s)) :refused)
                (equal (fn-omk-at 2 (fn-pvl-reset s)) s)))
  :hints (("Goal" :in-theory (enable fn-omk-at))))
(defthm fn-pvl-reset-advances-incarnation-without-reusing-a-ticket
  (implies (equal (car (fn-pvl-reset s)) :reset)
           (let ((next (fn-omk-at 2 (fn-pvl-reset s))))
             (and (fn-pvl-ledgerp next)
                  (equal (fn-omk-at 0 next) (+ 1 (fn-omk-at 0 s)))
                  (equal (fn-omk-at 1 next) (fn-omk-at 1 s))
                  (not (fn-omk-at 2 next)))))
  :hints (("Goal" :in-theory (enable fn-pvl-reset fn-pvl-ledgerp
                                   fn-omk-at fn-omk-widthp))))
; State-free runtime lifecycle decision. The native exclusion observes these
; phases while holding the actual arena lifecycle mutex. JOINED is evidence
; of completed shutdown, not a timeout; OWNED is the carried logical lease.
(defun fn-pvl-runtime-step (phase event owned joined)
  (declare (xargs :guard t))
  (cond ((not (member-equal phase '(:quiescent :serving :draining)))
         (list :refused phase))
        ((eq event :reset)
         (if (eq phase :quiescent) (list :allowed phase) (list :refused phase)))
        ((eq event :start)
         (if (and (eq phase :quiescent) (not owned))
             (list :allowed :serving) (list :refused phase)))
        ((eq event :capture)
         (if (eq phase :serving) (list :allowed phase) (list :refused phase)))
        ((eq event :borrow)
         (if (member-equal phase '(:serving :draining))
             (list :allowed phase) (list :refused phase)))
        ((eq event :drain) (list :allowed :draining))
        ((eq event :joined)
         (if (and (eq phase :draining) joined (not owned))
             (list :allowed :quiescent) (list :refused phase)))
        (t (list :refused phase))))
(defthm fn-pvl-runtime-reset-requires-quiescence
  (iff (equal (car (fn-pvl-runtime-step phase :reset owned joined)) :allowed)
       (equal phase :quiescent)))
(defthm fn-pvl-runtime-unjoined-or-owned-cannot-retire
  (implies (or (not joined) owned)
           (equal (fn-pvl-runtime-step phase :joined owned joined)
                  (list :refused phase))))
(defthm fn-pvl-runtime-start-excludes-reset
  (implies (equal (car (fn-pvl-runtime-step phase :start owned joined)) :allowed)
           (equal (fn-pvl-runtime-step
                   (cadr (fn-pvl-runtime-step phase :start owned joined))
                   :reset nil nil)
                  (list :refused :serving))))
(defthm fn-pvl-runtime-refused-keeps-phase
  (implies (equal (car (fn-pvl-runtime-step phase event owned joined)) :refused)
           (equal (cadr (fn-pvl-runtime-step phase event owned joined)) phase)))
(in-theory (disable fn-pvl-runtime-step))
(in-theory (disable fn-pvl-tokenp fn-pvl-token-matchp fn-pvl-seed
                    fn-pvl-ledgerp fn-pvl-livep fn-pvl-acquire
                    fn-pvl-release fn-pvl-reset))
