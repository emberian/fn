; THE STORED OWNERS. Three tables keep, per row, the owner kind their writes
; go out as: the cursor's conn-kind (its connection's reply), a read scan's
; qk (copied from that conn-kind) and an overlay's okind (its arena). The
; invariant FN2-DH-OWNERS-OK K: no row of those columns holds K. With K the
; commit kind, a write naming such a stored owner is never the commit
; kind's, so the cursor's run keeps the rows the commit kind holds
; (machines.lisp fn2-dispatch-held-claims). It holds after init (every
; column starts at 0) and every function the dispatch's chains reach keeps
; it (dispatch-held.lisp: one lemma per function, the writers of the
; columns asked that the value stored is not K). Below the commit hooks
; (assembly-callbacks-b), whose constraints and attachments keep it.
(in-package "ACL2")
(include-book "dispatch-held")
(include-book "assembly-init")

;; (stobj owner-column core-accessor)
(defconst *fn2-dispatch-held-owner-tables*
  '((fn2-cursor conn-kind fn2-cursor-table) (fn2-overlays okind fn2-core-overlays) (fn2-reads qk fn2-core-reads)))
(make-event
 (value (cons 'progn (fn2-dh-owner-events-all *fn2-dispatch-held-owner-tables* (w state)))))
(make-event (value (fn2-dh-owners-ok-form (w state))))
(make-event (value (cons 'progn (fn2-dh-owners-rules-forms (w state)))))
(in-theory (disable fn2-dh-owners-ok))

;; INIT: FN2-DH-OWNERS-OK at the commit kind holds of fn2-core-init's result,
;; for every profile and every prior core. Each owner stobj's -INIT resizes
;; every column to 0 and then to N rows of its :initially (not the commit
;; kind); each core child's init leaves the other owner tables; an owner
;; table's init (its -INIT-FOR or prepare) is that -INIT and then owner-chain
;; functions (fn2-cursor-initialize-rows stores conn-kind 0).
(defun fn2-dh-owner-init-forms (owners world)
  (declare (xargs :mode :program))
  (if (atom owners) nil
    (let* ((e (car owners)) (init (fn2-columns-sym (car e) "-INIT")))
      (cons `(defthm ,(fn2-columns-sym init "-OWNERS")
               (fn2-dh-col-ok *fn2-commit-kind* ',(nth 1 e) (,init n ,(car e)))
               :hints (("Goal" :in-theory '(,init ,@(all-fnnames (getpropc init 'unnormalized-body nil world))
                                            fn2-dh-col-ok-of-update-nth fn2-dh-avoids-resize-list fn2-dh-resize-list-0
                                            nth-update-nth (:e fn2-dh-avoids) (:e nfix) (:e equal)))))
            (fn2-dh-owner-init-forms (cdr owners) world)))))
(make-event (value (cons 'progn (fn2-dh-owner-init-forms (fn2-dh-owners (w state)) (w state)))))

(defun fn2-dh-init-frame-forms1 (init acc owner-accs)
  (declare (xargs :mode :program))
  (cond ((atom owner-accs) nil)
        ((eq acc (car owner-accs)) (fn2-dh-init-frame-forms1 init acc (cdr owner-accs)))
        (t (cons `(defthm ,(fn2-columns-sym (car owner-accs) (concatenate 'string "-OF-" (symbol-name init)))
                    (equal (,(car owner-accs) (,init profile fn2-core)) (,(car owner-accs) fn2-core))
                    :hints (("Goal" :in-theory '(,init ,(fn2-columns-sym (car owner-accs) (concatenate 'string "-OF-UPDATE-" (symbol-name acc)))))))
                 (fn2-dh-init-frame-forms1 init acc (cdr owner-accs))))))
(defun fn2-dh-init-frame-forms (accs owner-accs)
  ; each core child's init leaves every other owner table
  (declare (xargs :mode :program))
  (if (atom accs) nil
    (append (fn2-dh-init-frame-forms1 (fn2-columns-pre "INIT-" (car accs)) (car accs) owner-accs)
            (fn2-dh-init-frame-forms (cdr accs) owner-accs))))
(make-event (value (cons 'progn (fn2-dh-init-frame-forms (strip-cars *fn2-core-children*) (fn2-dh-owner-accs (fn2-dh-owners (w state)))))))

(defun fn2-dh-stobj-callees (fns s world)
  ; the functions of FNS taking stobj S
  (declare (xargs :mode :program))
  (cond ((atom fns) nil)
        ((member-eq s (formals (car fns) world)) (cons (car fns) (fn2-dh-stobj-callees (cdr fns) s world)))
        (t (fn2-dh-stobj-callees (cdr fns) s world))))
(defun fn2-dh-init-leaf-runes (fns s)
  ; S-INIT by its -OWNERS lemma; every other leaf by its owner chain lemma
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons (if (eq (car fns) (fn2-columns-sym s "-INIT"))
              (fn2-columns-sym s "-INIT-OWNERS")
            (fn2-columns-sym 'fn2-dh-owners-of (concatenate 'string "-" (symbol-name (car fns)))))
          (fn2-dh-init-leaf-runes (cdr fns) s))))
(defun fn2-dh-init-chain-leaves (fns s)
  (declare (xargs :mode :program))
  (cond ((atom fns) nil)
        ((eq (car fns) (fn2-columns-sym s "-INIT")) (fn2-dh-init-chain-leaves (cdr fns) s))
        (t (cons (car fns) (fn2-dh-init-chain-leaves (cdr fns) s)))))
(defun fn2-dh-bodies (fns world)
  (declare (xargs :mode :program))
  (if (atom fns) nil (cons (getpropc (car fns) 'unnormalized-body nil world) (fn2-dh-bodies (cdr fns) world))))
(defun fn2-dh-owner-child-init-forms (owners world)
  ; each owner table's core init: its column avoids the commit kind
  (declare (xargs :mode :program))
  (if (atom owners) nil
    (let* ((e (car owners)) (s (car e)) (acc (nth 3 e)) (init (fn2-columns-pre "INIT-" acc))
           (mids (remove1-eq (fn2-columns-pre "UPDATE-" acc)
                             (fn2-dh-stobj-callees (all-fnnames (getpropc init 'unnormalized-body nil world)) s world)))
           (leaves (fn2-dh-stobj-callees (all-fnnames-lst (fn2-dh-bodies mids world)) s world))
           (chains (fn2-dh-init-chain-leaves leaves s)))
      (append
       (and chains `((make-event (value (cons 'progn (fn2-dh-chain-forms-m (fn2-dh-postorder-m ',chains :owners (w state)) nil :owners))))))
       `((defthm ,(fn2-columns-sym init "-OWNERS")
           (fn2-dh-col-ok *fn2-commit-kind* ',(nth 1 e) (,acc (,init profile fn2-core)))
           :hints (("Goal" :in-theory '(,init ,(fn2-columns-sym acc (concatenate 'string "-OF-UPDATE-" (symbol-name acc)))
                                        ,@mids ,@(fn2-dh-init-leaf-runes leaves s) (:e equal))))))
       (fn2-dh-owner-child-init-forms (cdr owners) world)))))
(make-event (value (cons 'progn (fn2-dh-owner-child-init-forms (fn2-dh-owners (w state)) (w state)))))

(defun fn2-dh-init-frame-names1 (init acc owner-accs)
  (declare (xargs :mode :program))
  (cond ((atom owner-accs) nil)
        ((eq acc (car owner-accs)) (cons (fn2-columns-sym init "-OWNERS") (fn2-dh-init-frame-names1 init acc (cdr owner-accs))))
        (t (cons (fn2-columns-sym (car owner-accs) (concatenate 'string "-OF-" (symbol-name init)))
                 (fn2-dh-init-frame-names1 init acc (cdr owner-accs))))))
(defun fn2-dh-init-frame-names (accs owner-accs)
  (declare (xargs :mode :program))
  (if (atom accs) nil
    (append (fn2-dh-init-frame-names1 (fn2-columns-pre "INIT-" (car accs)) (car accs) owner-accs)
            (fn2-dh-init-frame-names (cdr accs) owner-accs))))
(make-event
 `(defthm fn2-dh-owners-ok-init
    (fn2-dh-owners-ok *fn2-commit-kind* (fn2-core-init profile fn2-core))
    :hints (("Goal" :in-theory '(fn2-dh-owners-ok fn2-core-init
                                 ,@(fn2-dh-init-frame-names (strip-cars *fn2-core-children*)
                                                            (fn2-dh-owner-accs (fn2-dh-owners (w state)))))))))
