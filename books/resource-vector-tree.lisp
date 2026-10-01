; fn: a node's accounting as one state -- the root bank and its sub-banks
; (lane resource-ledger / deputy-1, 2026-10-01; Codex review r06 F2: a
; sub-bank that is a value of its own cannot be revoked by its parent's
; destroy).  KeyKOS space banks are a tree: a sub-bank lives in its parent,
; and destroying the parent's slot destroys the sub-bank with everything it
; held (build/coordinator/scholar-literature-2026-10-01.md section E.3).
;
; THE TREE.  (ROOT SUBS): ROOT a bank (books/resource-vector.lisp) and
; SUBS a list by slot, the sub-bank at every slot whose root row is phase 2
; and NIL elsewhere.  Sub-banks partition their parent (the whole sub-bank
; budget is drawn on the root at open), so a step inside a sub-bank never
; touches the root, and the root's row for a sub-bank carries its budget.
; One level: a sub-bank holds draws, never sub-banks of its own (an :open,
; :grow or :destroy addressed inside one is refused :no-nested-sub-banks).
; This is the shape of the typed ledger: one table, a row's owner a slot.
;
; AN OP is (OWNER . STEP): OWNER :root, or the sub-bank's token (SLOT . GEN)
; -- the root row's slot and generation as fn-rv-open answered them -- and
; STEP a bank op (books/resource-vector.lisp fn-rv-step).  A root :open
; names the sub-bank's slot count, (:open SLOT BUDGET NSLOTS); a root
; :destroy is (:destroy SLOT GEN): what the sub-bank spent is read from the
; sub-bank itself, never supplied.  A step answers (WORD TREE' [TOKEN]), a
; refused one the tree itself.
;
; FN-RT-OKP: the root okp; SUBS as long as the root has slots; at every
; slot a sub-bank exactly when the row is phase 2, okp, with the row's
; demand as its budget.
;
; KEYSTONES:
;   fn-rt-step-keeps-okp           every step keeps the invariant
;   fn-rt-step-refused-keeps-the-tree
;   fn-rt-sub-bank-steps-keep-the-root   a step inside a sub-bank leaves the
;                                  root bank (the partition)
;   fn-rt-destroy-revokes-the-sub-bank   after a destroy every step addressed
;                                  to the sub-bank's token is :stale and
;                                  leaves the tree, however the slot is used
;                                  afterwards (the root's generation never
;                                  falls: fn-rv-run-never-lowers-a-gen)
;
; No served path calls this book (MODE 2026-10-01 section 3).

(in-package "ACL2")
(include-book "resource-vector")

(defun fn-rt-make (root subs)
  (declare (xargs :guard t))
  (list root subs))

(defun fn-rt-root (tree) (declare (xargs :guard t)) (nth 0 (true-list-fix tree)))
(defun fn-rt-subs (tree) (declare (xargs :guard t)) (nth 1 (true-list-fix tree)))

(defun fn-rt-sub (slot tree)
  (declare (xargs :guard (natp slot)))
  (nth slot (true-list-fix (fn-rt-subs tree))))

; -----------------------------------------------------------------------------
; The invariant.

(defun fn-rt-slot-okp (j root subs)
  (declare (xargs :guard (and (natp j) (fn-rv-bankp root) (true-listp subs))))
  (if (eql (fn-rv-phase j root) 2)
      (and (fn-rv-okp (nth j subs))
           (equal (fn-rv-budget (nth j subs)) (fn-rv-demand j root)))
    (null (nth j subs))))

(defun fn-rt-slots-okp (n root subs)
  (declare (xargs :guard (and (natp n) (fn-rv-bankp root) (true-listp subs))))
  (if (zp n)
      t
    (and (fn-rt-slot-okp (- n 1) root subs)
         (fn-rt-slots-okp (- n 1) root subs))))

(defun fn-rt-okp (tree)
  (declare (xargs :guard t))
  (and (fn-rv-okp (fn-rt-root tree))
       (true-listp (fn-rt-subs tree))
       (equal (len (fn-rt-subs tree)) (fn-rv-slot-count (fn-rt-root tree)))
       (fn-rt-slots-okp (fn-rv-slot-count (fn-rt-root tree))
                        (fn-rt-root tree) (fn-rt-subs tree))))

; -----------------------------------------------------------------------------
; The steps.

; A fresh sub-bank: its budget, nothing drawn, N idle slots.
(defun fn-rt-fresh (budget n)
  (declare (xargs :guard (natp n)))
  (fn-rv-make budget *fn-rv-zero* (fn-rv-idle-rows n)))

; What the sub-bank at SLOT is after an admitted root step: a fresh one on
; :open, the same with its budget grown on :grow, none otherwise (the row
; is not a sub-bank after a :draw, :settle, :refund or :destroy).
(defun fn-rt-sub-after (kind slot root2 sub nslots)
  (declare (xargs :guard (and (natp slot) (fn-rv-bankp root2) (natp nslots))))
  (case kind
    (:open (fn-rt-fresh (fn-rv-demand slot root2) nslots))
    (:grow (fn-rv-make (fn-rv-demand slot root2) (fn-rv-drawn sub) (fn-rv-slots sub)))
    (otherwise nil)))

(defun fn-rt-root-step (tree step)
  (declare (xargs :guard (and (true-listp step) (fn-rv-bankp (fn-rt-root tree))
                              (true-listp (fn-rt-subs tree)))
                  :verify-guards nil))
  (let* ((root (fn-rt-root tree))
         (subs (fn-rt-subs tree))
         (kind (car step))
         (slot (nfix (nth 1 step)))
         (step (if (eq kind :destroy)
                   (list :destroy slot (nth 2 step)
                         (fn-rv-spent (fn-rv-drawn (fn-rt-sub slot tree))))
                 step))
         (r (fn-rv-step root step))
         (word (car r)))
    (if (not (fn-rv-admittedp word))
        (list word tree)
      (list word
            (fn-rt-make (cadr r)
                        (update-nth slot
                                    (fn-rt-sub-after kind slot (cadr r) (fn-rt-sub slot tree)
                                                     (nfix (nth 3 step)))
                                    subs))
            (caddr r)))))

(defun fn-rt-sub-step (tree slot gen step)
  (declare (xargs :guard (and (natp slot) (true-listp step) (fn-rv-bankp (fn-rt-root tree))
                              (true-listp (fn-rt-subs tree)))
                  :verify-guards nil))
  (let ((root (fn-rt-root tree)))
    (cond ((not (and (fn-rv-slotp slot root) (fn-rv-sub-bankp slot gen root)))
           (list :stale tree))
          ((not (member-eq (car step) '(:draw :settle :refund)))
           (list :no-nested-sub-banks tree))
          (t (let ((r (fn-rv-step (fn-rt-sub slot tree) step)))
               (if (not (fn-rv-admittedp (car r)))
                   (list (car r) tree)
                 (list (car r)
                       (fn-rt-make root (update-nth slot (cadr r) (fn-rt-subs tree)))
                       (caddr r))))))))

(defun fn-rt-step (tree op)
  (declare (xargs :guard (and (true-listp op) (fn-rv-bankp (fn-rt-root tree))
                              (true-listp (fn-rt-subs tree)))
                  :verify-guards nil))
  (let ((owner (car op)))
    (cond ((eq owner :root) (fn-rt-root-step tree (cdr op)))
          ((consp owner) (fn-rt-sub-step tree (nfix (car owner)) (cdr owner) (cdr op)))
          (t (list :unknown-owner tree)))))

(defun fn-rt-run (tree ops)
  (declare (xargs :guard (and (true-list-listp ops) (fn-rv-bankp (fn-rt-root tree))
                              (true-listp (fn-rt-subs tree)))
                  :verify-guards nil))
  (if (consp ops)
      (let* ((one (fn-rt-step tree (car ops)))
             (rest (fn-rt-run (cadr one) (cdr ops))))
        (list (cons (car one) (car rest)) (cadr rest)))
    (list nil tree)))

; The root as a tree: the installed bank with no sub-bank but the reserve.
(defun fn-rt-install (budget baseline reserve nslots reserve-slots)
  (declare (xargs :guard (and (true-listp budget) (true-listp baseline)
                              (true-listp reserve) (natp nslots) (natp reserve-slots))
                  :verify-guards nil))
  (let ((r (fn-rv-install budget baseline reserve nslots)))
    (if (not (eq (car r) :installed))
        (list (car r) nil)
      (list :installed
            (fn-rt-make (cadr r)
                        (update-nth 1 (fn-rt-fresh reserve reserve-slots)
                                    (make-list nslots :initial-element nil)))))))

; -----------------------------------------------------------------------------
; Facts.

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-rt-nfix-nfix (equal (nfix (nfix x)) (nfix x))))

(defthm fn-rt-accessors-of-make
  (and (equal (fn-rt-root (fn-rt-make r s)) r)
       (equal (fn-rt-subs (fn-rt-make r s)) s)))

(defthm fn-rt-okp-forward
  (implies (fn-rt-okp tree)
           (and (fn-rv-okp (fn-rt-root tree))
                (true-listp (fn-rt-subs tree))
                (equal (len (fn-rt-subs tree)) (fn-rv-slot-count (fn-rt-root tree)))
                (fn-rt-slots-okp (fn-rv-slot-count (fn-rt-root tree))
                                 (fn-rt-root tree) (fn-rt-subs tree))))
  :rule-classes :forward-chaining)

(defthm fn-rt-sub-of-true-list
  (implies (true-listp (fn-rt-subs tree))
           (equal (fn-rt-sub slot tree) (nth slot (fn-rt-subs tree)))))

(defthm fn-rt-zero-below-every-vector
  (implies (fn-rv-vectorp v) (fn-rv-below *fn-rv-zero* v))
  :hints (("Goal" :use ((:instance fn-rv-below-drop-self
                                   (v (fn-rv-keep v *fn-rv-reusable-mask*)) (m *fn-rv-reusable-mask*))
                        (:instance fn-rv-below-keep-self (m *fn-rv-reusable-mask*))
                        (:instance fn-rv-below-transitive
                                   (a (fn-rv-zeros (len v)))
                                   (b (fn-rv-keep v *fn-rv-reusable-mask*)) (c v))))))

(defthm fn-rt-fresh-is-okp
  (implies (fn-rv-vectorp budget)
           (and (fn-rv-okp (fn-rt-fresh budget n))
                (equal (fn-rv-budget (fn-rt-fresh budget n)) budget)))
  :hints (("Goal" :in-theory (enable fn-rv-okp fn-rv-bankp fn-rv-make fn-rv-budget
                                     fn-rv-drawn fn-rv-slots))))

; A bank with its budget grown stays okp.
(defthm fn-rt-grown-is-okp
  (implies (and (fn-rv-okp sub) (fn-rv-vectorp x))
           (fn-rv-okp (fn-rv-make (fn-rv-plus (fn-rv-budget sub) x)
                                  (fn-rv-drawn sub) (fn-rv-slots sub))))
  :hints (("Goal" :in-theory (e/d (fn-rv-okp fn-rv-bankp) (fn-rv-budget fn-rv-drawn fn-rv-slots))
           :use (:instance fn-rv-below-transitive
                           (a (fn-rv-drawn sub)) (b (fn-rv-budget sub))
                           (c (fn-rv-plus (fn-rv-budget sub) x))))))

; Pointwise: the slots stay okp when every other slot is as it was (a
; root step at SLOT, fn-rv-step-keeps-the-other-slots) and SLOT itself is.
(defthm fn-rt-slot-okp-depends-on-the-row
  (implies (and (equal (fn-rv-row j root2) (fn-rv-row j root)) (natp j))
           (equal (fn-rt-slot-okp j root2 subs) (fn-rt-slot-okp j root subs)))
  :hints (("Goal" :in-theory (enable fn-rv-phase fn-rv-demand)))
  :rule-classes nil)

(defthm fn-rt-slot-okp-of-update-nth-other
  (implies (and (natp j) (natp slot) (not (equal j slot)))
           (equal (fn-rt-slot-okp j root (update-nth slot x subs))
                  (fn-rt-slot-okp j root subs)))
  :hints (("Goal" :in-theory (enable fn-rt-slot-okp))))

(defthm fn-rt-slots-okp-after-a-root-step
  (implies (and (fn-rt-slots-okp n root subs)
                (natp slot) (equal slot (nfix (nth 1 op)))
                (fn-rt-slot-okp slot (cadr (fn-rv-step root op)) (update-nth slot x subs)))
           (fn-rt-slots-okp n (cadr (fn-rv-step root op)) (update-nth slot x subs)))
  :hints (("Goal" :induct (fn-rt-slots-okp n root subs)
           :in-theory (disable fn-rt-slot-okp fn-rv-step update-nth nfix
                               fn-rv-step-keeps-the-other-slots))
          ("Subgoal *1/2" :cases ((equal (- n 1) slot))
           :use ((:instance fn-rt-slot-okp-depends-on-the-row
                            (j (- n 1)) (root2 (cadr (fn-rv-step root op)))
                            (subs (update-nth slot x subs)))
                 (:instance fn-rv-step-keeps-the-other-slots
                            (j (- n 1)) (bank root))))))

(defthm fn-rt-slots-okp-after-a-sub-step
  (implies (and (fn-rt-slots-okp n root subs) (natp slot)
                (fn-rt-slot-okp slot root (update-nth slot x subs)))
           (fn-rt-slots-okp n root (update-nth slot x subs)))
  :hints (("Goal" :induct (fn-rt-slots-okp n root subs)
           :in-theory (disable fn-rt-slot-okp update-nth))
          ("Subgoal *1/2" :cases ((equal (- n 1) slot)))))

(defthm fn-rt-slots-okp-at
  (implies (and (fn-rt-slots-okp n root subs) (natp j) (< j (nfix n)))
           (fn-rt-slot-okp j root subs))
  :hints (("Goal" :in-theory (disable fn-rt-slot-okp))))

; -----------------------------------------------------------------------------
; The keystones.

; The sub-bank's slot after each admitted root step.
(local
 (defthm fn-rt-grow-names-a-live-sub-bank
   (implies (equal (car (fn-rv-grow bank slot gen x)) :grown)
            (and (equal (fn-rv-phase slot bank) 2)
                 (natp slot)
                 (< slot (fn-rv-slot-count bank))))
   :hints (("Goal" :in-theory (e/d (fn-rv-grow fn-rv-sub-bankp fn-rv-slotp)
                                   (nth update-nth fn-rv-make fn-rv-slot-count))))))

; An admitted transition answers its own word.
(local
 (defthm fn-rt-admitted-words
   (and (equal (fn-rv-admittedp (car (fn-rv-draw bank slot d)))
               (equal (car (fn-rv-draw bank slot d)) :drawn))
        (equal (fn-rv-admittedp (car (fn-rv-open bank slot d)))
               (equal (car (fn-rv-open bank slot d)) :opened))
        (equal (fn-rv-admittedp (car (fn-rv-settle bank slot gen)))
               (equal (car (fn-rv-settle bank slot gen)) :settled))
        (equal (fn-rv-admittedp (car (fn-rv-refund bank slot gen x)))
               (equal (car (fn-rv-refund bank slot gen x)) :refunded))
        (equal (fn-rv-admittedp (car (fn-rv-grow bank slot gen x)))
               (equal (car (fn-rv-grow bank slot gen x)) :grown))
        (equal (fn-rv-admittedp (car (fn-rv-destroy bank slot gen x)))
               (equal (car (fn-rv-destroy bank slot gen x)) :destroyed)))
   :hints (("Goal" :in-theory (e/d (fn-rv-draw fn-rv-open fn-rv-charge fn-rv-settle fn-rv-refund
                                    fn-rv-grow fn-rv-destroy fn-rv-admittedp)
                                   (nth update-nth fn-rv-make))))))

(local
 (defthm fn-rt-settle-and-refund-name-a-draw
   (and (implies (equal (car (fn-rv-settle bank slot gen)) :settled)
                 (and (natp slot) (< slot (fn-rv-slot-count bank))
                      (equal (fn-rv-phase slot bank) 1)))
        (implies (equal (car (fn-rv-refund bank slot gen x)) :refunded)
                 (and (natp slot) (< slot (fn-rv-slot-count bank))
                      (equal (fn-rv-phase slot bank) 1))))
   :hints (("Goal" :in-theory (e/d (fn-rv-settle fn-rv-refund fn-rv-drawnp fn-rv-slotp)
                                   (nth update-nth fn-rv-make fn-rv-slot-count))))))

; The slot after each admitted root transition, one lemma a kind.
(local
 (defthm fn-rt-slot-okp-after-a-draw
   (implies (equal (car (fn-rv-draw root slot d)) :drawn)
            (fn-rt-slot-okp slot (cadr (fn-rv-draw root slot d)) (update-nth slot nil subs)))
   :hints (("Goal" :in-theory (disable fn-rv-draw fn-rv-phase fn-rv-demand update-nth)))))

(local
 (defthm fn-rt-slot-okp-after-an-open
   (implies (equal (car (fn-rv-open root slot b)) :opened)
            (fn-rt-slot-okp slot (cadr (fn-rv-open root slot b))
                            (update-nth slot (fn-rt-fresh (fn-rv-demand slot (cadr (fn-rv-open root slot b))) n)
                                        subs)))
   :hints (("Goal" :in-theory (disable fn-rv-open fn-rv-phase fn-rv-demand update-nth fn-rt-fresh
                                       fn-rv-okp fn-rv-budget)))))

(local
 (defthm fn-rt-slot-okp-after-a-settle
   (implies (equal (car (fn-rv-settle root slot gen)) :settled)
            (fn-rt-slot-okp slot (cadr (fn-rv-settle root slot gen)) (update-nth slot nil subs)))
   :hints (("Goal" :in-theory (disable fn-rv-settle fn-rv-phase fn-rv-demand update-nth)))))

(local
 (defthm fn-rt-slot-okp-after-a-refund
   (implies (equal (car (fn-rv-refund root slot gen x)) :refunded)
            (fn-rt-slot-okp slot (cadr (fn-rv-refund root slot gen x)) (update-nth slot nil subs)))
   :hints (("Goal" :in-theory (disable fn-rv-refund fn-rv-phase fn-rv-demand update-nth)))))

(local
 (defthm fn-rt-slot-okp-after-a-grow
   (implies (and (fn-rt-slots-okp (fn-rv-slot-count root) root subs)
                 (equal (car (fn-rv-grow root slot gen x)) :grown))
            (fn-rt-slot-okp slot (cadr (fn-rv-grow root slot gen x))
                            (update-nth slot
                                        (fn-rv-make (fn-rv-demand slot (cadr (fn-rv-grow root slot gen x)))
                                                    (fn-rv-drawn (nth slot subs))
                                                    (fn-rv-slots (nth slot subs)))
                                        subs)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-rv-grow fn-rv-okp fn-rv-bankp fn-rt-slots-okp fn-rv-make
                                fn-rv-budget fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen
                                fn-rv-demand fn-rv-row fn-rv-slot-count fn-rt-grown-is-okp
                                fn-rt-slots-okp-at update-nth nth)
            :use ((:instance fn-rt-slots-okp-at (n (fn-rv-slot-count root)) (j slot))
                  (:instance fn-rt-grown-is-okp (sub (nth slot subs)))
                  (:instance fn-rt-grow-names-a-live-sub-bank (bank root)))))))

(local
 (defthm fn-rt-slot-okp-after-a-destroy
   (implies (and (fn-rt-okp tree)
                 (equal (car (fn-rv-destroy (fn-rt-root tree) slot gen spent)) :destroyed))
            (fn-rt-slot-okp slot (cadr (fn-rv-destroy (fn-rt-root tree) slot gen spent))
                            (update-nth slot nil (fn-rt-subs tree))))
   :hints (("Goal" :in-theory (disable fn-rv-destroy fn-rv-okp fn-rv-bankp fn-rt-slots-okp
                                       fn-rv-phase fn-rv-demand fn-rv-row update-nth fn-rt-okp)))))

; fn-rv-step by kind (the dispatch, as rewrites under the kind).
(local
 (defthm fn-rt-step-dispatch
   (and (implies (equal (car step) :draw)
                 (equal (fn-rv-step root step)
                        (fn-rv-draw root (nfix (nth 1 step)) (true-list-fix (nth 2 step)))))
        (implies (equal (car step) :open)
                 (equal (fn-rv-step root step)
                        (fn-rv-open root (nfix (nth 1 step)) (true-list-fix (nth 2 step)))))
        (implies (equal (car step) :settle)
                 (equal (fn-rv-step root step)
                        (fn-rv-settle root (nfix (nth 1 step)) (nth 2 step))))
        (implies (equal (car step) :refund)
                 (equal (fn-rv-step root step)
                        (fn-rv-refund root (nfix (nth 1 step)) (nth 2 step) (true-list-fix (nth 3 step)))))
        (implies (equal (car step) :grow)
                 (equal (fn-rv-step root step)
                        (fn-rv-grow root (nfix (nth 1 step)) (nth 2 step) (true-list-fix (nth 3 step)))))
        (implies (equal (car step) :destroy)
                 (equal (fn-rv-step root step)
                        (fn-rv-destroy root (nfix (nth 1 step)) (nth 2 step) (true-list-fix (nth 3 step)))))
        (implies (not (member-eq (car step) '(:draw :open :settle :refund :grow :destroy)))
                 (equal (fn-rv-step root step) (list :unknown-step root))))
   :hints (("Goal" :in-theory (enable fn-rv-step)))))

; A root step whose own slot is okp afterwards keeps the tree okp: the
; root by fn-rv-step-keeps-okp, every other slot by the pointwise lemma.
(local
 (defthm fn-rt-root-step-okp-when-the-slot-is
   (implies (and (fn-rt-okp tree)
                 (fn-rv-admittedp (car (fn-rv-step (fn-rt-root tree) op)))
                 (fn-rt-slot-okp (nfix (nth 1 op)) (cadr (fn-rv-step (fn-rt-root tree) op))
                                 (update-nth (nfix (nth 1 op)) x (fn-rt-subs tree))))
            (fn-rt-okp (fn-rt-make (cadr (fn-rv-step (fn-rt-root tree) op))
                                   (update-nth (nfix (nth 1 op)) x (fn-rt-subs tree)))))
   :hints (("Goal" :in-theory (e/d (fn-rt-okp fn-rv-slotp)
                                   (fn-rv-step fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp fn-rv-bankp
                                    fn-rv-slot-count fn-rv-admittedp fn-rt-slots-okp-after-a-root-step
                                    update-nth fn-rt-root fn-rt-subs fn-rt-make fn-rt-accessors-of-make))
            :use ((:instance fn-rt-slots-okp-after-a-root-step
                             (n (fn-rv-slot-count (fn-rt-root tree))) (root (fn-rt-root tree))
                             (subs (fn-rt-subs tree)) (slot (nfix (nth 1 op))))
                  (:instance fn-rv-admitted-step-names-a-slot (bank (fn-rt-root tree)))
                  (:instance fn-rv-step-keeps-okp (bank (fn-rt-root tree)))
                  (:instance fn-rv-step-keeps-the-budget-and-the-slot-count (bank (fn-rt-root tree)))
                  (:instance fn-rt-accessors-of-make
                             (r (cadr (fn-rv-step (fn-rt-root tree) op)))
                             (s (update-nth (nfix (nth 1 op)) x (fn-rt-subs tree)))))))))

(defthm fn-rt-true-listp-of-drop
  (true-listp (fn-rv-drop v m))
  :hints (("Goal" :use (:instance fn-rv-nats-p-forward-to-true-listp (v (fn-rv-drop v m))))))

; The root step keeps the tree okp, one lemma a kind, then by cases.
(local
 (defthm fn-rt-root-step-keeps-okp-draw
   (implies (and (fn-rt-okp tree) (equal (car step) :draw))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is (op step) (x nil))
                  (:instance fn-rt-slot-okp-after-a-draw (root (fn-rt-root tree)) (slot (nfix (nth 1 step)))
                             (d (true-list-fix (nth 2 step))) (subs (fn-rt-subs tree))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-open
   (implies (and (fn-rt-okp tree) (equal (car step) :open))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is (op step)
                             (x (fn-rt-fresh (fn-rv-demand (nfix (nth 1 step))
                                                           (cadr (fn-rv-step (fn-rt-root tree) step)))
                                             (nfix (nth 3 step)))))
                  (:instance fn-rt-slot-okp-after-an-open (root (fn-rt-root tree)) (slot (nfix (nth 1 step)))
                             (b (true-list-fix (nth 2 step))) (n (nfix (nth 3 step))) (subs (fn-rt-subs tree))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-settle
   (implies (and (fn-rt-okp tree) (equal (car step) :settle))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is (op step) (x nil))
                  (:instance fn-rt-slot-okp-after-a-settle (root (fn-rt-root tree)) (slot (nfix (nth 1 step)))
                             (gen (nth 2 step)) (subs (fn-rt-subs tree))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-refund
   (implies (and (fn-rt-okp tree) (equal (car step) :refund))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is (op step) (x nil))
                  (:instance fn-rt-slot-okp-after-a-refund (root (fn-rt-root tree)) (slot (nfix (nth 1 step)))
                             (gen (nth 2 step)) (x (true-list-fix (nth 3 step))) (subs (fn-rt-subs tree))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-grow
   (implies (and (fn-rt-okp tree) (equal (car step) :grow))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is (op step)
                             (x (fn-rv-make (fn-rv-demand (nfix (nth 1 step))
                                                          (cadr (fn-rv-step (fn-rt-root tree) step)))
                                            (fn-rv-drawn (nth (nfix (nth 1 step)) (fn-rt-subs tree)))
                                            (fn-rv-slots (nth (nfix (nth 1 step)) (fn-rt-subs tree))))))
                  (:instance fn-rt-slot-okp-after-a-grow (root (fn-rt-root tree)) (slot (nfix (nth 1 step))) (subs (fn-rt-subs tree))
                             (gen (nth 2 step)) (x (true-list-fix (nth 3 step)))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-destroy
   (implies (and (fn-rt-okp tree) (equal (car step) :destroy))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))
            :use ((:instance fn-rt-root-step-okp-when-the-slot-is
                             (op (list :destroy (nfix (nth 1 step)) (nth 2 step)
                                       (fn-rv-spent (fn-rv-drawn (nth (nfix (nth 1 step)) (fn-rt-subs tree))))))
                             (x nil))
                  (:instance fn-rt-slot-okp-after-a-destroy (slot (nfix (nth 1 step))) (gen (nth 2 step))
                             (spent (fn-rv-spent (fn-rv-drawn (nth (nfix (nth 1 step)) (fn-rt-subs tree)))))))))))

(local
 (defthm fn-rt-root-step-keeps-okp-otherwise
   (implies (and (fn-rt-okp tree)
                 (not (member-eq (car step) '(:draw :open :settle :refund :grow :destroy))))
            (fn-rt-okp (cadr (fn-rt-root-step tree step))))
   :hints (("Goal" :in-theory (e/d (fn-rt-root-step fn-rt-sub-after)
                                   (fn-rv-step fn-rt-okp fn-rt-slot-okp fn-rt-slots-okp fn-rv-okp
                                   fn-rv-bankp fn-rv-admittedp fn-rt-fresh fn-rv-make fn-rv-budget
                                   fn-rv-drawn fn-rv-slots fn-rv-phase fn-rv-gen fn-rv-demand fn-rv-row
                                   fn-rv-slot-count fn-rv-slotp update-nth nfix fn-rt-sub fn-rv-spent
                                   fn-rv-draw fn-rv-open fn-rv-settle fn-rv-refund fn-rv-grow fn-rv-destroy
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-root-step-okp-when-the-slot-is))))))

(defthm fn-rt-root-step-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-root-step tree step))))
  :hints (("Goal" :in-theory (disable fn-rt-root-step fn-rt-okp)
           :cases ((equal (car step) :draw) (equal (car step) :open) (equal (car step) :settle)
                   (equal (car step) :refund) (equal (car step) :grow) (equal (car step) :destroy)))))

(defthm fn-rt-okp-of-make
  (equal (fn-rt-okp (fn-rt-make r s))
         (and (fn-rv-okp r) (true-listp s) (equal (len s) (fn-rv-slot-count r))
              (fn-rt-slots-okp (fn-rv-slot-count r) r s)))
  :hints (("Goal" :in-theory (enable fn-rt-okp))))

(defthm fn-rt-sub-step-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-sub-step tree slot gen step))))
  :hints (("Goal" :in-theory (e/d (fn-rt-sub-step fn-rv-slotp)
                                  (fn-rv-step fn-rv-okp fn-rv-bankp fn-rt-slots-okp fn-rt-okp
                                   fn-rv-admittedp fn-rv-slot-count fn-rv-phase fn-rv-gen
                                   fn-rv-demand fn-rv-sub-bankp update-nth fn-rt-sub
                                   fn-rt-root fn-rt-subs fn-rt-make fn-rt-slots-okp-after-a-sub-step
                                   fn-rt-slots-okp-at fn-rv-step-keeps-okp
                                   fn-rv-step-keeps-the-budget-and-the-slot-count))
           :use ((:instance fn-rt-slots-okp-at (n (fn-rv-slot-count (fn-rt-root tree)))
                            (root (fn-rt-root tree)) (subs (fn-rt-subs tree)) (j slot))
                 (:instance fn-rt-slots-okp-after-a-sub-step
                            (n (fn-rv-slot-count (fn-rt-root tree))) (root (fn-rt-root tree))
                            (subs (fn-rt-subs tree))
                            (x (cadr (fn-rv-step (nth slot (fn-rt-subs tree)) step))))
                 (:instance fn-rv-step-keeps-okp (bank (nth slot (fn-rt-subs tree))) (op step))
                 (:instance fn-rv-step-keeps-the-budget-and-the-slot-count
                            (bank (nth slot (fn-rt-subs tree))) (op step))))
          ("Goal'" :in-theory (e/d (fn-rt-slot-okp fn-rv-sub-bankp fn-rv-slotp)
                                   (fn-rv-step fn-rv-okp fn-rv-bankp fn-rt-slots-okp fn-rt-okp
                                    fn-rv-admittedp fn-rv-slot-count fn-rv-phase fn-rv-gen
                                    fn-rv-demand update-nth fn-rt-sub fn-rt-root fn-rt-subs fn-rt-make
                                    fn-rt-slots-okp-after-a-sub-step fn-rt-slots-okp-at
                                    fn-rv-step-keeps-okp fn-rv-step-keeps-the-budget-and-the-slot-count)))))

; KEYSTONE.  Every step keeps the invariant.
(defthm fn-rt-step-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-step tree op))))
  :hints (("Goal" :in-theory (disable fn-rt-okp fn-rt-root-step fn-rt-sub-step))))

(defthm fn-rt-run-keeps-okp
  (implies (fn-rt-okp tree)
           (fn-rt-okp (cadr (fn-rt-run tree ops))))
  :hints (("Goal" :in-theory (disable fn-rt-okp fn-rt-step))))

; KEYSTONE.  A refused step returns the tree itself.
(defthm fn-rt-step-refused-keeps-the-tree
  (implies (not (fn-rv-admittedp (car (fn-rt-step tree op))))
           (equal (cadr (fn-rt-step tree op)) tree))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rt-sub-after fn-rv-admittedp))))

; KEYSTONE.  A step inside a sub-bank leaves the root bank: sub-banks
; partition their parent.
(defthm fn-rt-sub-bank-steps-keep-the-root
  (equal (fn-rt-root (cadr (fn-rt-step tree (cons (cons slot gen) step))))
         (fn-rt-root tree))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-admittedp fn-rv-slotp fn-rv-sub-bankp))))

; A root step is the bank's step on the root (with a destroy's SPENT read
; from the sub-bank).
(defthm fn-rt-root-of-root-step
  (equal (fn-rt-root (cadr (fn-rt-root-step tree step)))
         (let ((r (fn-rv-step (fn-rt-root tree)
                              (if (eq (car step) :destroy)
                                  (list :destroy (nfix (nth 1 step)) (nth 2 step)
                                        (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix (nth 1 step)) tree))))
                                step))))
           (if (fn-rv-admittedp (car r)) (cadr r) (fn-rt-root tree))))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-admittedp fn-rt-sub-after))))

; The root's generations never fall under tree steps.
(defthm fn-rt-step-never-lowers-a-root-gen
  (implies (natp j)
           (<= (fn-rv-gen j (fn-rt-root tree))
               (fn-rv-gen j (fn-rt-root (cadr (fn-rt-step tree op))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-admittedp fn-rt-sub-after fn-rv-gen
                                      fn-rv-slotp fn-rv-sub-bankp fn-rt-root-step)
           :use ((:instance fn-rv-step-never-lowers-a-gen (bank (fn-rt-root tree))
                            (op (if (eq (cadr op) :destroy)
                                    (list :destroy (nfix (nth 2 op)) (nth 3 op)
                                          (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix (nth 2 op)) tree))))
                                  (cdr op))))
                 (:instance fn-rt-root-of-root-step (step (cdr op)))))))

(defthm fn-rt-run-never-lowers-a-root-gen
  (implies (natp j)
           (<= (fn-rv-gen j (fn-rt-root tree))
               (fn-rv-gen j (fn-rt-root (cadr (fn-rt-run tree ops))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-rt-step fn-rv-gen fn-rt-root))))

; A retired token of the root stays retired under tree steps and runs.
(defthm fn-rt-step-keeps-a-retired-token
  (implies (and (natp j) (fn-rv-token-retiredp j g (fn-rt-root tree)))
           (fn-rv-token-retiredp j g (fn-rt-root (cadr (fn-rt-step tree op)))))
  :hints (("Goal" :in-theory (disable fn-rv-step fn-rv-admittedp fn-rt-sub-after fn-rv-gen
                                      fn-rv-token-retiredp fn-rv-slotp fn-rv-sub-bankp
                                      fn-rt-root-step fn-rt-root fn-rt-subs fn-rt-make)
           :use ((:instance fn-rv-step-keeps-a-retired-token (bank (fn-rt-root tree))
                            (op (if (eq (car (cdr op)) :destroy)
                                    (list :destroy (nfix (nth 1 (cdr op))) (nth 2 (cdr op))
                                          (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix (nth 1 (cdr op))) tree))))
                                  (cdr op))))
                 (:instance fn-rt-root-of-root-step (step (cdr op)))))))

(defthm fn-rt-run-keeps-a-retired-token
  (implies (and (natp j) (fn-rv-token-retiredp j g (fn-rt-root tree)))
           (fn-rv-token-retiredp j g (fn-rt-root (cadr (fn-rt-run tree ops)))))
  :hints (("Goal" :in-theory (disable fn-rt-step fn-rv-token-retiredp fn-rt-root))))

; KEYSTONE (Codex review r06 F2).  Destroying a sub-bank revokes it: after
; the destroy, any run, and whatever the slot holds then, every step
; addressed to the destroyed sub-bank's token is :stale and leaves the tree.
(defthm fn-rt-destroy-revokes-the-sub-bank
  (implies (equal (car (fn-rt-step tree (list :root :destroy slot gen))) :destroyed)
           (let ((later (cadr (fn-rt-run (cadr (fn-rt-step tree (list :root :destroy slot gen)))
                                         ops))))
             (and (equal (car (fn-rt-step later (cons (cons slot gen) step))) :stale)
                  (equal (cadr (fn-rt-step later (cons (cons slot gen) step))) later))))
  :hints (("Goal"
           :in-theory (e/d (fn-rt-step fn-rt-sub-step fn-rt-root-step fn-rv-step fn-rv-admittedp
                            fn-rt-sub-after)
                           (fn-rv-destroy fn-rt-run fn-rv-gen fn-rv-phase
                            fn-rv-slotp fn-rv-row fn-rt-root fn-rt-subs fn-rt-sub fn-rv-sub-bankp
                            fn-rv-token-retiredp fn-rt-accessors-of-make
                            fn-rt-run-keeps-a-retired-token fn-rv-destroy-retires-the-token
                            fn-rv-retired-token-names-no-sub-bank))
           :use ((:instance fn-rv-destroy-retires-the-token (bank (fn-rt-root tree)) (slot (nfix slot))
                            (spent (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix slot) tree)))))
                 (:instance fn-rt-accessors-of-make
                            (r (cadr (fn-rv-destroy (fn-rt-root tree) (nfix slot) gen
                                                    (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix slot) tree))))))
                            (s (update-nth (nfix slot) nil (fn-rt-subs tree))))
                 (:instance fn-rt-run-keeps-a-retired-token (j (nfix slot)) (g gen)
                            (tree (fn-rt-make
                                   (cadr (fn-rv-destroy (fn-rt-root tree) (nfix slot) gen
                                                        (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix slot) tree)))))
                                   (update-nth (nfix slot) nil (fn-rt-subs tree)))))
                 (:instance fn-rv-retired-token-names-no-sub-bank (j (nfix slot)) (g gen)
                            (bank (fn-rt-root (cadr (fn-rt-run
                                                     (fn-rt-make
                                                      (cadr (fn-rv-destroy (fn-rt-root tree) (nfix slot) gen
                                                                           (fn-rv-spent (fn-rv-drawn (fn-rt-sub (nfix slot) tree)))))
                                                      (update-nth (nfix slot) nil (fn-rt-subs tree)))
                                                     ops)))))))))

(in-theory (disable fn-rt-make fn-rt-root fn-rt-subs fn-rt-sub fn-rt-slot-okp fn-rt-slots-okp
                    fn-rt-okp fn-rt-fresh fn-rt-sub-after fn-rt-root-step fn-rt-sub-step
                    fn-rt-step fn-rt-run fn-rt-install))
