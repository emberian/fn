; PRF-1081: actual held payload-slot update, with the complete tail borrowed.
; Isolated from Store recovery so this concrete boundary has a narrow gate.
(in-package "ACL2")
(include-book "held-record-shape")
(defun fn-orm-tail (n row)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) row
    (fn-orm-tail (1- n) (if (consp row) (cdr row) nil))))
(local
 (defthm fn-orm-tail-is-nthcdr-by-definition
   (implies (natp n) (equal (fn-orm-tail n row) (nthcdr n row)))
   :hints (("Goal" :induct (fn-orm-tail n row)
            :in-theory (enable fn-orm-tail nthcdr)))))
(defun fn-orm-held (row handle)
  (declare (xargs :guard t))
  ; Five fixed prefix conses; every remaining field stays borrowed.
  (list* (fn-held-sequence row) (fn-held-txid row)
         (fn-held-generation row) (fn-held-msgid row) handle
         (fn-orm-tail 5 row)))
(defthm fn-orm-held-is-the-actual-payload-slot-update
  (equal (fn-orm-held row handle) (update-nth 4 handle row))
  :rule-classes nil
  :hints (("Goal"
           :expand ((update-nth 4 handle row)
                    (update-nth 3 handle (cdr row))
                    (update-nth 2 handle (cddr row))
                    (update-nth 1 handle (cdddr row))
                    (update-nth 0 handle (cddddr row)))
           :in-theory (e/d (fn-orm-held fn-held-internals fn-record-internals nthcdr)
                           (fn-orm-tail)))))
(defthm fn-orm-held-borrows-the-entire-metadata-tail
  (equal (fn-orm-tail 5 (fn-orm-held row handle)) (fn-orm-tail 5 row))
  :hints (("Goal" :in-theory (enable fn-orm-held fn-orm-tail nthcdr))))
(defthm fn-orm-held-keeps-every-retained-field-except-the-handle
  (let ((new (fn-orm-held row handle)))
    (and (equal (fn-held-sequence new) (fn-held-sequence row))
         (equal (fn-held-txid new) (fn-held-txid row))
         (equal (fn-held-generation new) (fn-held-generation row))
         (equal (fn-held-msgid new) (fn-held-msgid row))
         (equal (fn-held-payload new) handle)
         (equal (fn-held-groups new) (fn-held-groups row))
         (equal (fn-held-obligation-id new) (fn-held-obligation-id row))
         (equal (fn-held-content-subject new) (fn-held-content-subject row))
         (equal (fn-held-release-evidence new) (fn-held-release-evidence row))
         (equal (fn-held-charge new) (fn-held-charge row))
         (equal (fn-held-stamp new) (fn-held-stamp row))
         (equal (fn-held-facts new) (fn-held-facts row))
         (equal (fn-held-context new) (fn-held-context row))
         (equal (fn-held-numbers new) (fn-held-numbers row))
         (equal (fn-held-withdrawn new) (fn-held-withdrawn row))
         (equal (fn-held-binding new) (fn-held-binding row))))
  :hints (("Goal" :in-theory (enable fn-orm-held fn-held-internals fn-record-internals))))
(defthm fn-orm-held-preserves-the-held-shape
  (implies (and (fn-held-p row) (natp handle))
           (fn-held-p (fn-orm-held row handle)))
  :hints (("Goal" :in-theory (enable fn-orm-held fn-held-p fn-held-internals fn-record-internals))))
(local
 (defthm fn-orm-nonempty-tail-carries-the-original-spine
  (implies (and (natp n) (consp (fn-orm-tail n row)))
           (and (equal (true-listp row) (true-listp (fn-orm-tail n row)))
                (equal (len row) (+ n (len (fn-orm-tail n row))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-orm-tail n row)
           :in-theory (e/d (fn-orm-tail true-listp len)
                           (fn-orm-tail-is-nthcdr-by-definition))))))
(defthm fn-orm-held-has-the-same-wire-projection-at-the-same-bytes
  (equal (fn-held-wire (fn-orm-held row handle) bytes)
         (fn-held-wire row bytes))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-orm-nonempty-tail-carries-the-original-spine (n 5)))
           :cases ((consp row) (consp (cdr row)) (consp (cddr row))
                   (consp (cdddr row)) (consp (cddddr row)))
           :in-theory (enable fn-orm-held fn-orm-tail fn-held-wire fn-row-binding
                              fn-held-shapep fn-record-shapep
                              fn-held-internals fn-record-internals))))
(defun fn-orm-metadata (row)
  (declare (xargs :guard t))
  ; Only the payload slot is removed. The complete retained tail is shared.
  (list* (fn-held-sequence row) (fn-held-txid row) (fn-held-generation row)
         (fn-held-msgid row) (fn-orm-tail 5 row)))
(defthm fn-orm-metadata-keeps-the-complete-tail-after-payload-remap
  (equal (fn-orm-metadata (fn-orm-held row handle)) (fn-orm-metadata row))
  :hints (("Goal" :in-theory (enable fn-orm-metadata fn-orm-held
                                     fn-orm-tail nthcdr
                                     fn-held-internals fn-record-internals))))
(in-theory (disable fn-orm-tail fn-orm-held fn-orm-metadata))
