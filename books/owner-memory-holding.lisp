; The owner carries the union of logical readers and physical disposal debt.
; Gates read COUNT without walking the connections or another actor's roster.
(in-package "ACL2")
(include-book "public-exposure")
(include-book "acceptance-alloc")
(include-book "defrecord")
(include-book "state-globals")

(def-loop fn-adm-hh-drop (id rows)
 :shape :map :over rows :elt row
 :stop (and (consp row) (equal (car row) id))
 :stop-value (cdr rows) :body row)
(defun fn-adm-hh-put (id logical physical rows)
 (declare (xargs :guard t))
 (cons (list id logical physical) (fn-adm-hh-drop id rows)))

(def-loop fn-adm-hh-row-errors (rows)
 :shape :sum :over rows :elt row
 :body (if (and (true-listp row) (equal (len row) 3) (natp (car row))) 0 1))

(fn-defrecord fn-adm-hh
 :constructor (fn-adm-hh-make count rows)
 :fields ((fn-adm-hh-count natp) (fn-adm-hh-rows true-listp))
 :extra ((equal (fn-adm-hh-row-errors (fn-adm-hh-rows x)) 0)
         (equal (fn-adm-hh-count x) (len (fn-adm-hh-rows x)))))

(defun fn-adm-hh-initial ()
 (declare (xargs :guard t))
 (fn-adm-hh-make 0 nil))

; The three-cell rows use the generated exposure map operations: identity,
; logical presence, physical presence. Updates run only at lifecycle edges.
(defun fn-adm-hh-update (bank id logical physical)
 (declare (xargs :guard t))
 (if (not (natp id)) bank
  (let* ((rows (fn-adm-hh-rows bank))
         (old (fn-exp-lookup id rows))
         (alive (or logical physical))
         (count (nfix (fn-adm-hh-count bank))))
   (fn-adm-hh-make
    (cond ((and old (not alive)) (nfix (1- count)))
          ((and (not old) alive) (1+ count))
          (t count))
    (if alive (fn-adm-hh-put id (and logical t) (and physical t) rows)
      (fn-adm-hh-drop id rows))))))

(defun fn-adm-hh-open (bank id physical)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id t
  (or physical (fn-exp-at 2 (fn-exp-lookup id (fn-adm-hh-rows bank))))))

(defun fn-adm-hh-close (bank id)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id nil
  (fn-exp-at 2 (fn-exp-lookup id (fn-adm-hh-rows bank)))))

(defun fn-adm-hh-return (bank id)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id
  (fn-exp-at 1 (fn-exp-lookup id (fn-adm-hh-rows bank))) nil))

; A persistent HTTP transport transfers its physical identity to its next
; logical reader only after the preceding reader ended, under the owner.
(defun fn-adm-hh-rearm (bank old-id new-id)
 (declare (xargs :guard t))
 (let ((old (fn-exp-lookup old-id (fn-adm-hh-rows bank)))
       (new (fn-exp-lookup new-id (fn-adm-hh-rows bank))))
  (if (and (not (equal old-id new-id))
           (not (fn-exp-at 1 old)) (fn-exp-at 2 old) (fn-exp-at 1 new))
   (fn-adm-hh-open (fn-adm-hh-return bank old-id) new-id t)
   bank)))

(defun fn-owner-memory-held-bank (state)
 (declare (xargs :stobjs state :guard t))
 (if (boundp-global 'fn-owner-memory-held-bank state)
  (f-get-global 'fn-owner-memory-held-bank state)
  (fn-adm-hh-initial)))

(defun fn-owner-memory-held (state)
 (declare (xargs :stobjs state :guard t))
 (nfix (fn-adm-hh-count (fn-owner-memory-held-bank state))))

(defun fn-owner-memory-held-open (id physical state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-open (fn-owner-memory-held-bank state) id physical) state))

(defun fn-owner-memory-held-close (id state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-close (fn-owner-memory-held-bank state) id) state))

(defun fn-owner-memory-held-return (id state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-return (fn-owner-memory-held-bank state) id) state))

(defun fn-owner-memory-held-rearm (old-id new-id state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-rearm (fn-owner-memory-held-bank state) old-id new-id) state))

(local (defthm m22-lookup-implies-consp-by-definition
 (implies (fn-exp-lookup id rows) (< 0 (len rows)))
 :hints (("Goal" :induct (fn-exp-lookup id rows) :in-theory (enable fn-exp-lookup)))))

(local (defthm m22-drop-count-by-definition
 (implies (equal (fn-adm-hh-row-errors rows) 0)
  (equal (len (fn-adm-hh-drop id rows))
        (if (fn-exp-lookup id rows) (1- (len rows)) (len rows))))
 :hints (("Goal" :induct (fn-exp-lookup id rows)
          :in-theory (enable fn-adm-hh-drop fn-exp-lookup fn-adm-hh-row-errors)))))

(local (defthm m22-drop-is-true-list-by-definition
 (implies (true-listp rows) (true-listp (fn-adm-hh-drop id rows)))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows) :in-theory (enable fn-adm-hh-drop true-listp)))))

(local (defthm m22-drop-preserves-rows-by-definition
 (implies (equal (fn-adm-hh-row-errors rows) 0)
          (equal (fn-adm-hh-row-errors (fn-adm-hh-drop id rows)) 0))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-row-errors)))))

(local (defthm m22-put-preserves-rows-by-definition
 (implies (and (natp id) (equal (fn-adm-hh-row-errors rows) 0))
          (equal (fn-adm-hh-row-errors (fn-adm-hh-put id logical physical rows)) 0))
 :hints (("Goal" :in-theory (enable fn-adm-hh-put fn-adm-hh-row-errors)))))

(local (defthm m22-initial-bank-is-valid-by-definition
 (fn-adm-hhp (fn-adm-hh-initial))
 :hints (("Goal" :in-theory (enable fn-adm-hh-initial fn-adm-hhp)))))

(defthm fn-adm-hh-update-preserves-validity
 (implies (fn-adm-hhp bank) (fn-adm-hhp (fn-adm-hh-update bank id logical physical)))
 :hints (("Goal" :use ((:instance m22-lookup-implies-consp-by-definition (rows (fn-adm-hh-rows bank)))) :in-theory (e/d (fn-adm-hhp fn-adm-hh-update fn-adm-hh-put)
   (fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup fn-adm-hh-drop)))))

; Cached cardinality refines the union of logical and physical custody.
(def-loop fn-adm-hh-ids (rows)
 :shape :map :over rows :elt row :body (fn-exp-at 0 row))
(def-loop fn-adm-hh-dead (rows)
 :shape :sum :over rows :elt row :body (if (or (fn-exp-at 1 row) (fn-exp-at 2 row)) 0 1))
(defun fn-adm-hh-representsp (bank)
 (declare (xargs :guard t))
 (and (fn-adm-hhp bank)
      (no-duplicatesp-equal (fn-adm-hh-ids (fn-adm-hh-rows bank)))
      (equal (fn-adm-hh-dead (fn-adm-hh-rows bank)) 0)))
(local (defthm m22-drop-ids-subset
 (implies (not (member-equal key (fn-adm-hh-ids rows)))
          (not (member-equal key (fn-adm-hh-ids (fn-adm-hh-drop id rows)))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids)))))
(local (defthm m22-drop-preserves-unique-ids
 (implies (no-duplicatesp-equal (fn-adm-hh-ids rows))
          (no-duplicatesp-equal (fn-adm-hh-ids (fn-adm-hh-drop id rows))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids)))))
(local (defthm m22-drop-removes-id
 (implies (and (no-duplicatesp-equal (fn-adm-hh-ids rows))
               (equal (fn-adm-hh-row-errors rows) 0))
          (not (member-equal id (fn-adm-hh-ids (fn-adm-hh-drop id rows)))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids fn-adm-hh-row-errors)))))
(local (defthm m22-drop-preserves-live-rows
 (implies (equal (fn-adm-hh-dead rows) 0)
          (equal (fn-adm-hh-dead (fn-adm-hh-drop id rows)) 0))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-dead)))))
(defthm fn-adm-hh-initial-represents-the-empty-union
 (fn-adm-hh-representsp (fn-adm-hh-initial))
 :hints (("Goal" :in-theory (enable fn-adm-hh-representsp fn-adm-hh-initial fn-adm-hhp))))
(defthm fn-adm-hh-update-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
          (fn-adm-hh-representsp (fn-adm-hh-update bank id logical physical)))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-hh-representsp fn-adm-hhp fn-adm-hh-update fn-adm-hh-put fn-adm-hh-ids fn-adm-hh-dead)
 (fn-adm-hh-drop fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup))
 :use (fn-adm-hh-update-preserves-validity))))

(def-loop fn-adm-hh-present-ids (rows)
 :shape :map :over rows :elt row
 :keep (or (fn-exp-at 1 row) (fn-exp-at 2 row)) :body (fn-exp-at 0 row))
(local (defthm m22-ids-length-by-definition
 (equal (len (fn-adm-hh-ids rows)) (len rows))
 :hints (("Goal" :induct (fn-adm-hh-ids rows) :in-theory (enable fn-adm-hh-ids)))))
(local (defthm m22-live-union-is-all-ids
 (implies (equal (fn-adm-hh-dead rows) 0)
          (equal (fn-adm-hh-present-ids rows) (fn-adm-hh-ids rows)))
 :hints (("Goal" :induct (fn-adm-hh-dead rows)
          :in-theory (enable fn-adm-hh-dead fn-adm-hh-present-ids fn-adm-hh-ids)))))
(defthm fn-adm-hh-cached-count-is-the-union-cardinality
 (implies (fn-adm-hh-representsp bank)
  (and (no-duplicatesp-equal (fn-adm-hh-present-ids (fn-adm-hh-rows bank)))
       (equal (fn-adm-hh-count bank) (len (fn-adm-hh-present-ids (fn-adm-hh-rows bank))))))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-representsp fn-adm-hhp)
                               (fn-adm-hh-rows fn-adm-hh-count fn-adm-hh-present-ids fn-adm-hh-ids)))))
(defthm fn-adm-hh-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-open bank id physical)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-open) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-close-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-close bank id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-close) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-return-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-return bank id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-return) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-rearm-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-rearm bank old-id new-id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-rearm) (fn-adm-hh-open fn-adm-hh-return fn-adm-hh-update fn-adm-hh-representsp)))))
