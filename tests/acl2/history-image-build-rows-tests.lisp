; PRF-1265 teeth: literal antecedents/conclusions and discrimination between
; appended all-event rows, corrupted logical history, and malformed custody.
(in-package "ACL2")
(include-book "../../books/history-image-build-rows")

(local (in-theory (enable fn-hrs-img-ok fn-hp-vhold-is-x)))
(defconst *hibr-empty*
  '( (nil nil nil nil nil nil) nil 0 0 0
     (0 0 0 0 0) (1 1 1 1 1) 0 0 nil 0 0))
(defconst *hibr-event* '(:other 7 nil))

; Reachable positive: actual beginning followed by the host-called row step.
(defthm hibr-row-positive
  (let* ((c (fn-his-build-begin 0 *hibr-empty*))
         (n (mv-nth 1 (fn-his-build-row *hibr-event* c))))
    (and (fn-hrc-wfp c) (fn-hrs-rel nil c)
         (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
         (fn-hrc-wfp n) (fn-hrs-rel (list *hibr-event*) n)))
  :hints (("Goal" :use ((:instance fn-his-build-begin-establishes
                                   (salt 0) (fn-hrecs$c *hibr-empty*))
                        (:instance fn-his-build-row-refines-history-append
                                   (ev *hibr-event*) (h nil)
                                   (c (fn-his-build-begin 0 *hibr-empty*))))
           :in-theory (disable fn-his-build-begin fn-his-build-row
                               fn-hrc-wfp fn-hrs-rel)))
  :rule-classes nil)

(defun hibr-live-row (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :verify-guards nil))
  (let ((fn-hrecs$c (fn-his-build-begin 0 fn-hrecs$c)))
    (mv-let (v fn-hrecs$c) (fn-his-build-row *hibr-event* fn-hrecs$c)
      (mv (list v (fn-hrc-lo fn-hrecs$c) (fn-hrc-hi fn-hrecs$c)
                (fn-hrc-sfxi 0 fn-hrecs$c) (fn-hrc-sfx-length fn-hrecs$c)
                (fn-hrc-count fn-hrecs$c)) fn-hrecs$c))))
(assert-event
 (mv-let (result fn-hrecs$c) (hibr-live-row fn-hrecs$c)
   (mv (equal result '(:ok 0 0 nil 16 1)) fn-hrecs$c))
 :stobjs-out '(nil fn-hrecs$c))

; A pending suffix refuses before any append and keeps exact state.
(defconst *hibr-pending* (update-nth 11 1 (update-nth 9 (list *hibr-event*) *hibr-empty*)))
(defthm hibr-pending-positive
  (let* ((c *hibr-pending*) (n (mv-nth 1 (fn-his-build-row :later c))))
    (and (fn-hrc-wfp c) (fn-hrs-rel (list *hibr-event*) c)
         (not (and (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)))
         (equal (mv-nth 0 (fn-his-build-row :later c)) '(:refused :pending-suffix))
         (fn-hrc-wfp n) (equal n c)))
  :rule-classes nil)

; Hypothesis removal: actual beginning is well formed but the claimed
; logical history contains a ghost row. The literal append conclusion fails.
(defthm hibr-row-rel-removal
  (let* ((c (update-nth 2 1 (update-nth 4 1 *hibr-empty*)))
         (n (mv-nth 1 (fn-his-build-row *hibr-event* c))))
    (and (fn-hrc-wfp c) (not (fn-hrs-rel nil c))
         (equal (fn-hrc-lo c) 0) (equal (fn-hrc-hi c) 0)
         (not (fn-hrs-rel (list *hibr-event*) n))))
  :hints (("Goal" :in-theory (enable fn-hrc-fields fn-hrc-updaters)))
  :rule-classes nil)

; Hypothesis removal: retained relation is true (empty suffix), but the
; suffix window is backwards. Refusal keeps the corrupted shape, so the
; literal theorem's shape conclusion fails.
(defthm hibr-row-wfp-removal
  (let ((c (update-nth 10 3 *hibr-empty*)))
    (and (not (fn-hrc-wfp c)) (fn-hrs-rel nil c)
         (not (fn-hrc-wfp (mv-nth 1 (fn-his-build-row :later c))))))
  :rule-classes nil)

; The physical suffix bound: the producer beginning has no slots and every
; row step preserves the 16-slot envelope, independently of row byte size.
(defthm hibr-suffix-bound-positive
  (let ((c (fn-his-build-begin 0 *hibr-empty*)))
    (and (<= (fn-hrc-sfx-length c) 16)
         (<= (fn-hrc-sfx-length (mv-nth 1 (fn-his-build-row *hibr-event* c))) 16)))
  :hints (("Goal" :use ((:instance fn-his-build-begin-establishes
                                   (salt 0) (fn-hrecs$c *hibr-empty*)))
           :in-theory (disable fn-his-build-begin fn-his-build-row)))
  :rule-classes nil)
(defthm hibr-suffix-bound-removal
  (let ((c (update-nth 9 (make-list 32 :initial-element nil) *hibr-pending*)))
    (and (not (<= (fn-hrc-sfx-length c) 16))
         (not (<= (fn-hrc-sfx-length (mv-nth 1 (fn-his-build-row :later c))) 16))))
  :rule-classes nil)
