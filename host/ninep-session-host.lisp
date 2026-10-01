(in-package "ACL2")
(include-book "../books/ninep-dispatch")
(include-book "../books/definterface")

; The actual host receives actions/reply bytes from the concrete core. It
; performs neither path selection nor tag/fid lookup itself.
(defun fn-ninep-session-step (server-msize dispatch fn-octets fn-ninep-session state)
 (declare (xargs :stobjs (fn-octets fn-ninep-session state) :guard t))
 (mv-let (answer next fn-ninep-session)
  (fn-9p-dispatch-step server-msize dispatch fn-octets fn-ninep-session)
  (mv answer next fn-ninep-session state)))

(defun fn-ninep-session-quiesce (fn-ninep-session state)
 (declare (xargs :stobjs (fn-ninep-session state) :guard t))
 (mv-let (word fn-ninep-session) (fn-9ps-quiesce-step fn-ninep-session)
  (mv word fn-ninep-session state)))

(defun fn-ninep-session-disconnect (fn-ninep-session state)
 (declare (xargs :stobjs (fn-ninep-session state) :guard t))
 (let ((fn-ninep-session (fn-9ps-drain-begin fn-ninep-session)))
  (mv :draining fn-ninep-session state)))

(defthm fn-ninep-session-step-complete-correspondence
 (equal (fn-ninep-session-step server dispatch fn-octets fn-ninep-session state)
        (list (mv-nth 0 (fn-9p-dispatch-step server dispatch fn-octets fn-ninep-session))
              (mv-nth 1 (fn-9p-dispatch-step server dispatch fn-octets fn-ninep-session))
              (mv-nth 2 (fn-9p-dispatch-step server dispatch fn-octets fn-ninep-session)) state))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-session-step) (fn-9p-dispatch-step)))))

(defthm fn-ninep-session-step-preserves-state
 (equal (mv-nth 3 (fn-ninep-session-step server dispatch fn-octets fn-ninep-session state)) state)
 :hints (("Goal" :in-theory (e/d (fn-ninep-session-step) (fn-9p-dispatch-step)))))
(defthm fn-ninep-session-quiesce-preserves-state
 (equal (mv-nth 2 (fn-ninep-session-quiesce fn-ninep-session state)) state)
 :hints (("Goal" :in-theory (e/d (fn-ninep-session-quiesce) (fn-9ps-quiesce-step)))))
(defthm fn-ninep-session-disconnect-preserves-state
 (equal (mv-nth 2 (fn-ninep-session-disconnect fn-ninep-session state)) state))

; These guard-T boundaries skip no carry predicate. Do not invent a
; :raw-with declaration or a cosmetic guard merely to select hot dispatch.
; The actual installed native executor/operation carry remains to compose.
(definterface fn-ninep-session-step :class :common-lisp-compliant)
(definterface fn-ninep-session-quiesce :class :common-lisp-compliant)
(definterface fn-ninep-session-disconnect :class :common-lisp-compliant)
