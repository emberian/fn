; The bounded semantic revision step. It becomes authoritative only as part
; of the same actual durable publication that changes visibility/config.
; A pending adoption is discarded by that publication, never adopted merely
; because its previous base revision stopped matching. No shared table is
; recognized or rebuilt here. The first authority fence owns namespace birth.
(in-package "ACL2")
(include-book "consumer-position")

(defun fn-carv-state-with-authority (s authority)
  (declare (xargs :guard t))
  (fn-cp-state-carry (fn-cp-nth 1 s) (fn-cp-nth 2 s) (fn-cp-nth 3 s)
                     (fn-cp-nth 4 s) (fn-cp-nth 5 s) authority))

(defun fn-carv-revision-state (s revision)
  (declare (xargs :guard t))
  (let ((a (fn-cp-nth 6 s)))
    (fn-carv-state-with-authority
     s (list :authority revision (fn-cp-nth 2 a) (fn-cp-nth 3 a)
             (fn-cp-nth 4 a) nil))))

; This gate must also be consumed before a visibility-changing publication
; allocates its frontier. Completion/replay use the identical scalar step;
; exhaustion after ambiguous persistence is a recovery event, not rollback.
(defun fn-carv-semantic-step (s)
  (declare (xargs :guard t))
  (let* ((a (fn-cp-nth 6 s)) (revision (fn-cp-nth 1 a)))
    (cond ((null s) (list :ok nil))
          ((not (fn-cp-nth 3 a))
           ; No usable remote authority namespace yet. Discard provisional
           ; adoption against the former config/visibility, retaining the
           ; pre-bootstrap comparison value instead of counting old events.
           (list :ok (fn-carv-revision-state s revision)))
          ((or (not (fn-cp-uintp revision))
               (equal revision *fn-cbor-max-uint*))
           (list :refused :authority-revision-exhausted))
          (t (list :ok (fn-carv-revision-state s (1+ revision)))))))

(defthm fn-carv-semantic-step-fences-current-authority
  (let* ((a (fn-cp-nth 6 s)) (revision (fn-cp-nth 1 a))
         (next (fn-cp-nth 1 (fn-carv-semantic-step s))))
    (implies (and (fn-cp-nth 3 a) (fn-cp-uintp revision)
                  (< revision *fn-cbor-max-uint*))
             (and (eq (car (fn-carv-semantic-step s)) :ok)
                  (equal (fn-cp-nth 1 (fn-cp-nth 6 next)) (1+ revision))
                  (not (fn-cp-nth 5 (fn-cp-nth 6 next)))
                  (equal (fn-cp-nth 2 (fn-cp-nth 6 next)) (fn-cp-nth 2 a))
                  (equal (fn-cp-nth 3 (fn-cp-nth 6 next)) (fn-cp-nth 3 a))
                  (equal (fn-cp-nth 4 (fn-cp-nth 6 next)) (fn-cp-nth 4 a)))))
  :hints (("Goal" :in-theory
           (enable fn-carv-semantic-step fn-carv-revision-state
                   fn-carv-state-with-authority fn-cp-state-carry fn-cp-nth))))

(defthm fn-carv-semantic-step-preserves-statep
  (implies (and (fn-cp-statep s)
                (eq (car (fn-carv-semantic-step s)) :ok))
           (fn-cp-statep (fn-cp-nth 1 (fn-carv-semantic-step s))))
  :hints (("Goal" :in-theory
           (e/d (fn-carv-semantic-step fn-carv-revision-state
                  fn-carv-state-with-authority fn-cp-state-carry fn-cp-statep
                  fn-cp-authorityp fn-cp-nth fn-cp-uintp)
                (fn-cp-idp fn-cp-entriesp fn-cp-authority-rowsp
                 fn-cp-adoptionp)))))

(in-theory (disable fn-carv-state-with-authority fn-carv-revision-state
                    fn-carv-semantic-step))
