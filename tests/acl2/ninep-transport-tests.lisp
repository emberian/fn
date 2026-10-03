(in-package "ACL2")
(include-book "../../host/ninep-transport-host")

; INTERNAL metadata/codec fixture: no installed family, mount or grant.
(defun-nx ninep-transport-run (fuel transport buffer session)
 (declare (xargs :measure (nfix fuel)))
 (if (zp fuel) (list '(:budget-exhausted) transport session)
  (let* ((result (fn-9pt-current-step transport buffer session))
         (action (mv-nth 0 result)) (next (mv-nth 1 result)) (s (mv-nth 2 result)))
   (if (eq (car action) :yield)
       (ninep-transport-run (1- fuel) next buffer s)
     (list action next s)))))

(defun-nx ninep-transport-fixture ()
 (mv-nth 1 (fn-9pt-provision-internal 64 16 (create-fn-ninep-transport))))

(defconst *ninep-transport-version-wire*
 '(19 0 0 0 100 255 255 64 0 0 0 6 0 57 80 50 48 48 48))
(defconst *ninep-transport-version-reply*
 '(19 0 0 0 101 255 255 64 0 0 0 6 0 57 80 50 48 48 48))

(defthm ninep-transport-header-body-complete-positive
 (let* ((transport (ninep-transport-fixture))
        (session (create-fn-ninep-session))
        (buffer (fn-octets-from-list '(23 0 0 0 116 9 0) (create-fn-octets)))
        (result (ninep-transport-run 4 transport buffer session)))
  (and (fn-ninep-transportp transport) (fn-ninep-sessionp session) (fn-octets-p buffer)
       (equal (car result) '(:receive 16))
       (equal (mv-nth 0 (fn-9pt-current-step (cadr result) buffer session)) '(:receive 16))
       (equal (mv-nth 1 (fn-9pt-current-step (cadr result) buffer session)) (cadr result))
       (equal (mv-nth 2 (fn-9pt-current-step (cadr result) buffer session)) session)
       (equal (fn-octets-list buffer) '(23 0 0 0 116 9 0))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

(defthm ninep-transport-version-complete-positive
 (let* ((transport (ninep-transport-fixture)) (session (create-fn-ninep-session))
        (buffer (fn-octets-from-list *ninep-transport-version-wire* (create-fn-octets)))
        (result (ninep-transport-run 32 transport buffer session))
        (next (cadr result)) (s (caddr result)))
  (and (equal (car result) (list :send *ninep-transport-version-reply*))
       (equal (fn-9ps-phase s) :base) (equal (fn-9ps-msize s) 64)
       (equal (fn-9ps-mount-token s) nil) (equal (fn-9ps-mount-source s) nil)
       (equal (fn-ninep-transport-step next buffer s nil)
              (list (car result) next s nil))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

(defthm ninep-transport-reply-return-and-duplicate-complete-positive
 (let* ((buffer (fn-octets-from-list *ninep-transport-version-wire* (create-fn-octets)))
        (result (ninep-transport-run 32 (ninep-transport-fixture) buffer (create-fn-ninep-session)))
        (transport (cadr result)) (session (caddr result))
        (returned (fn-9pt-current-reply-returned transport buffer session))
        (next (mv-nth 1 returned)) (empty (mv-nth 2 returned)))
  (and (equal (mv-nth 0 returned) :returned)
       (equal (fn-octets-list empty) nil)
       (equal (mv-nth 3 returned) session)
       (equal (fn-9pt-owned-cursor next) (fn-9pt-begin 64))
       (equal (fn-9pt-current-reply-returned next empty session)
              (list :stale next empty session))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

(defthm ninep-transport-repeat-version-produces-real-drain
 (let* ((buffer (fn-octets-from-list *ninep-transport-version-wire* (create-fn-octets)))
        (first (ninep-transport-run 32 (ninep-transport-fixture) buffer (create-fn-ninep-session)))
        (session (caddr first))
        (again (ninep-transport-run 48 (ninep-transport-fixture) buffer session)))
  (and (equal (car again) (list :send *ninep-transport-version-reply*))
       (equal (caddr again) (update-fn-9ps-drain-index 1 session))
       (equal (fn-9ps-phase (caddr again)) :base)
       (equal (fn-9ps-pending-version (caddr again)) nil)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

(defthm ninep-transport-held-mount-no-shaped-return
 (let* ((buffer (fn-octets-from-list *ninep-transport-version-wire* (create-fn-octets)))
        (base (update-fn-9ps-phase :base (create-fn-ninep-session)))
        (base (update-fn-9ps-msize 64 base))
        (base (update-fn-9ps-mount-phase :held base))
        (base (update-fn-9ps-mount-token '(:internal-mount 0) base))
        (base (update-fn-9ps-mount-source '(:internal-source 19) base))
        (result (ninep-transport-run 48 (ninep-transport-fixture) buffer base))
        (next (caddr result)))
  (and (equal (car result) '(:await-mount-return))
       (equal (fn-9ps-phase next) :mount-return-ready)
       (equal (fn-9ps-mount-token next) (fn-9ps-mount-token base))
       (equal (fn-9ps-mount-source next) (fn-9ps-mount-source base))
       (equal (fn-9pt-version-after-quiescence next)
              (list :await-mount-return nil next))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

; The allocator's definite refusal has no issued token or retained source.
; The complete parsed Tversion still executes the real bounded drain.
(defthm ninep-transport-refused-mount-version-resets
 (let* ((buffer (fn-octets-from-list *ninep-transport-version-wire* (create-fn-octets)))
        (base (update-fn-9ps-phase :base (create-fn-ninep-session)))
        (base (update-fn-9ps-msize 64 base))
        (base (update-fn-9ps-mount-phase :refused base))
        (result (ninep-transport-run 48 (ninep-transport-fixture) buffer base))
        (next (caddr result)))
  (and (equal (car result) (list :send *ninep-transport-version-reply*))
       (equal (fn-9ps-phase next) :base)
       (equal (fn-9ps-mount-phase next) :empty)
       (equal (fn-9ps-mount-token next) nil)
       (equal (fn-9ps-mount-source next) nil)
       (equal (fn-9ps-mount-intent next) nil)
       (equal (fn-9ps-pending-version next) nil)))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))

(defthm ninep-transport-uncertain-mount-cannot-reset
 (implies (member-eq (fn-9ps-mount-phase session)
                    '(:issue-intent :reserved :pin-intent :return-intent :fenced))
  (equal (fn-9pt-version-after-quiescence session)
         (list :await-mount-return nil session)))
 :rule-classes nil)

; Mutation witness: treating header observation as body observation accepts
; this absent body. Every real subject guard/state antecedent still holds.
(defthm ninep-transport-header-is-not-body-mutation-refuted
 (let* ((transport (ninep-transport-fixture)) (s (create-fn-ninep-session))
        (buffer (fn-octets-from-list '(23 0 0 0 116 9 0) (create-fn-octets)))
        (result (ninep-transport-run 4 transport buffer s)))
  (and (fn-ninep-transportp transport) (fn-ninep-sessionp s) (fn-octets-p buffer)
       (equal (car result) '(:receive 16))
       (not (equal (car result) '(:send (11 0 0 0 117 9 0 0 0 0 0))))))
 :rule-classes nil
 :hints (("Goal" :expand ((:free (fuel transport buffer session)
                                      (ninep-transport-run fuel transport buffer session)))
           :in-theory (enable ninep-transport-run fn-oct-word-at fn-octets-p fn-octets-len fn-octets-list
                                    fn-octets-get fn-octets-get-word))))
