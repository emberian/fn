; Bounded predecessor of the actual FnPWXReturn transition.
(in-package "ACL2")
(include-book "page-window-executor")

; Cursor11: tag/token/original-worker/revision/original-rows/remaining/
; reversed-prefix/rebuilt/first-binding/phase/actual-source-reference.
(defun fn-pwrt-make (token worker revision original remaining prefix rebuilt found phase source)
 (declare (xargs :guard t))
 (list :window-return token worker revision original remaining prefix rebuilt found phase source))
(defun fn-pwrt-start (token worker revision rows source)
 (declare (xargs :guard t))
 (fn-pwrt-make token worker revision rows rows nil nil nil :scan source))
(defun fn-pwrt-one (cursor)
 (declare (xargs :guard t))
 (let* ((token (fn-prl-nth 1 cursor)) (worker (fn-prl-nth 2 cursor))
        (revision (fn-prl-nth 3 cursor)) (original (fn-prl-nth 4 cursor))
        (remaining (fn-prl-nth 5 cursor)) (prefix (fn-prl-nth 6 cursor))
        (rebuilt (fn-prl-nth 7 cursor)) (found (fn-prl-nth 8 cursor))
        (phase (fn-prl-nth 9 cursor)) (source (fn-prl-nth 10 cursor)))
  (case phase
   (:scan
    (if (consp remaining)
     (let* ((row (car remaining))
            (match (and (consp row) (equal token (car row)))))
      (fn-pwrt-make token worker revision original (cdr remaining)
       (if match prefix (cons row prefix)) rebuilt
       (if (and match (not found)) row found) :scan source))
     (fn-pwrt-make token worker revision original remaining prefix remaining found :rebuild source)))
   (:rebuild
    (if (consp prefix)
     (fn-pwrt-make token worker revision original remaining (cdr prefix)
                   (cons (car prefix) rebuilt) found :rebuild source)
     (fn-pwrt-make token worker revision original remaining prefix rebuilt found :ready source)))
   (otherwise cursor))))
(defun fn-pwrt-run (cursor fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (not (member-eq (fn-prl-nth 9 cursor) '(:scan :rebuild))))
  (mv cursor fuel)
  (fn-pwrt-run (fn-pwrt-one cursor) (- fuel 1))))

; Exactly the original return decision and complete ledger effects, using the
; once-resolved first binding and reconstructed remove result. No lookup here.
(defun fn-pwrt-resolved-return (ledger worker token binding removed)
 (declare (xargs :guard t :verify-guards nil))
 (let ((row (if (consp binding) (cdr binding) nil)))
  (if (not (and (fn-pwx-rowp worker) (fn-pwx-tokenp token)
                (member-eq (fn-prl-nth 2 worker) '(:running :cancelled-running))
                (equal (fn-prl-nth 3 worker) token)
                (eq (fn-prl-nth 1 row) :window)
                (eq (fn-prl-nth 2 row) :running)
                (equal (fn-prl-nth 3 row) (fn-prl-nth 0 worker))))
   (mv :stale-job worker ledger)
   (mv :returned
       (list (fn-prl-nth 0 worker) (fn-prl-nth 1 worker)
             (if (eq (fn-prl-nth 2 worker) :cancelled-running) :cancelled-returned :returned) token)
       (fn-prl-build (fn-prl-nth 0 ledger) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
        (cons (cons token (list (fn-prl-nth 0 row) :window :returned (fn-prl-nth 0 worker))) removed)
        (fn-prl-nth 4 ledger))))))

(local
 (defthm fn-pwrt-token-kind
  (implies (fn-pwx-tokenp token)
           (member-eq (fn-prl-nth 0 token) '(:window :decoded-window)))
  :hints (("Goal" :in-theory (e/d (fn-pwx-tokenp fn-pwz-tokenp fn-prl-nth nth)
                                 (fn-prw-descriptorp fn-pwz-descriptorp))))))

(defthm fn-pwrt-resolved-return-refines-pwx-return
 (implies
  (and (equal binding (fn-prl-binding token (fn-prl-nth 3 ledger)))
       (equal removed (fn-prl-remove token (fn-prl-nth 3 ledger))))
  (equal (fn-pwrt-resolved-return ledger worker token binding removed)
         (fn-pwx-return ledger worker token)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pwrt-resolved-return fn-pwx-return fn-pwx-boundp fn-prw-phase))))

; Ghost carry, never a served validator. It connects every resumed scan phase
; to the original ledger semantics, including an improper tail in the model.
(defun fn-pwrt-carryp (cursor)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((token (fn-prl-nth 1 cursor)) (original (fn-prl-nth 4 cursor))
        (remaining (fn-prl-nth 5 cursor)) (prefix (fn-prl-nth 6 cursor))
        (rebuilt (fn-prl-nth 7 cursor)) (found (fn-prl-nth 8 cursor))
        (phase (fn-prl-nth 9 cursor)))
  (and (true-listp prefix)
   (if (eq phase :scan)
    (and (equal (fn-prl-binding token original) (or found (fn-prl-binding token remaining)))
         (equal (fn-prl-remove token original) (revappend prefix (fn-prl-remove token remaining))))
    (and (member-eq phase '(:rebuild :ready))
         (equal found (fn-prl-binding token original))
         (equal (fn-prl-remove token original) (revappend prefix rebuilt))
         (implies (eq phase :ready) (null prefix)))))))

(local
 (defun fn-pwrt-model-remove (token rows)
  (declare (xargs :guard t))
  (if (consp rows)
   (if (and (consp (car rows)) (equal token (caar rows)))
    (fn-pwrt-model-remove token (cdr rows))
    (cons (car rows) (fn-pwrt-model-remove token (cdr rows)))) rows)))
(local
 (defthm fn-pwrt-remove-aux-model
  (implies (true-listp rev)
   (equal (fn-prl-remove-aux token rows rev)
          (revappend rev (fn-pwrt-model-remove token rows))))
  :hints (("Goal" :induct (fn-prl-remove-aux token rows rev)
                   :in-theory (enable fn-prl-remove-aux fn-pwrt-model-remove revappend)))))
(local
 (defthm fn-pwrt-remove-model
  (equal (fn-prl-remove token rows) (fn-pwrt-model-remove token rows))
  :hints (("Goal" :in-theory (enable fn-prl-remove)))))
(local
 (defthm fn-pwrt-remove-one
  (equal (fn-prl-remove token rows)
   (if (consp rows)
    (if (and (consp (car rows)) (equal token (caar rows)))
     (fn-prl-remove token (cdr rows))
     (cons (car rows) (fn-prl-remove token (cdr rows)))) rows))
  :hints (("Goal" :in-theory (enable fn-pwrt-model-remove)))
  :rule-classes nil))

(defthm fn-pwrt-start-establishes-carry-by-definition
 (fn-pwrt-carryp (fn-pwrt-start token worker revision rows source))
 :hints (("Goal" :in-theory (enable fn-pwrt-start fn-pwrt-make fn-pwrt-carryp fn-prl-nth))))

(local
 (defthm fn-pwrt-binding-one
  (equal (fn-prl-binding token rows)
   (if (consp rows)
    (if (and (consp (car rows)) (equal token (caar rows)))
     (car rows) (fn-prl-binding token (cdr rows))) nil))
  :hints (("Goal" :in-theory (enable fn-prl-binding)))
  :rule-classes nil))

(defthm fn-pwrt-one-preserves-carry
 (implies (fn-pwrt-carryp cursor) (fn-pwrt-carryp (fn-pwrt-one cursor)))
 :hints (("Goal" :in-theory (e/d (fn-pwrt-carryp fn-pwrt-one fn-pwrt-make
                                      fn-prl-nth revappend)
                                     (fn-prl-binding fn-prl-remove fn-prl-remove-aux
                                      fn-pwrt-model-remove fn-pwrt-remove-model))
                  :use ((:instance fn-pwrt-remove-one
                          (token (fn-prl-nth 1 cursor)) (rows (fn-prl-nth 5 cursor)))
                        (:instance fn-pwrt-binding-one
                          (token (fn-prl-nth 1 cursor)) (rows (fn-prl-nth 5 cursor)))))))

(defthm fn-pwrt-run-preserves-carry
 (implies (and (natp fuel) (fn-pwrt-carryp cursor))
          (fn-pwrt-carryp (mv-nth 0 (fn-pwrt-run cursor fuel))))
 :hints (("Goal" :induct (fn-pwrt-run cursor fuel)
                  :in-theory (e/d (fn-pwrt-run) (fn-pwrt-carryp fn-pwrt-one fn-prl-nth)))))

(defthm fn-pwrt-ready-has-original-binding-and-removal
 (implies (and (fn-pwrt-carryp cursor) (eq (fn-prl-nth 9 cursor) :ready))
  (and (equal (fn-prl-nth 8 cursor)
              (fn-prl-binding (fn-prl-nth 1 cursor) (fn-prl-nth 4 cursor)))
       (equal (fn-prl-nth 7 cursor)
              (fn-prl-remove (fn-prl-nth 1 cursor) (fn-prl-nth 4 cursor)))))
 :hints (("Goal" :in-theory (enable fn-pwrt-carryp revappend))))

(defthm fn-pwrt-one-retains-source-worker-and-root
 (let ((next (fn-pwrt-one cursor)))
  (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 cursor))
       (equal (fn-prl-nth 2 next) (fn-prl-nth 2 cursor))
       (equal (fn-prl-nth 3 next) (fn-prl-nth 3 cursor))
       (equal (fn-prl-nth 4 next) (fn-prl-nth 4 cursor))
       (equal (fn-prl-nth 10 next) (fn-prl-nth 10 cursor))))
 :hints (("Goal" :in-theory (enable fn-pwrt-one fn-pwrt-make fn-prl-nth))))

(verify-guards fn-pwrt-resolved-return)
(verify-guards fn-pwrt-carryp)

; The endpoint is the complete original function result, not just phase or C.
(defthm fn-pwrt-ready-refines-complete-return
 (implies (and (fn-pwrt-carryp cursor)
               (eq (fn-prl-nth 9 cursor) :ready)
               (equal (fn-prl-nth 4 cursor) (fn-prl-nth 3 ledger)))
  (equal (fn-pwrt-resolved-return ledger (fn-prl-nth 2 cursor) (fn-prl-nth 1 cursor)
                                (fn-prl-nth 8 cursor) (fn-prl-nth 7 cursor))
         (fn-pwx-return ledger (fn-prl-nth 2 cursor) (fn-prl-nth 1 cursor))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pwrt-ready-has-original-binding-and-removal
                      (:instance fn-pwrt-resolved-return-refines-pwx-return
                       (worker (fn-prl-nth 2 cursor)) (token (fn-prl-nth 1 cursor))
                       (binding (fn-prl-nth 8 cursor)) (removed (fn-prl-nth 7 cursor))))
                  :in-theory (disable fn-pwrt-carryp fn-pwrt-resolved-return fn-pwx-return))))
