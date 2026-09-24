; Bounded retirement of superseded lossless pack generations.  A selected
; pack remains the only authority for exact prefix replay; neither article
; retention nor Store event history is pruned by this namespace operation.
(in-package "ACL2")
(include-book "checkpoint-publish")

(defun fn-cprt-generations-after-p (generations previous)
  (declare (xargs :guard t))
  (if (consp generations)
      (and (natp (car generations))
           (< (ifix previous) (car generations))
           (< (car generations) *fn-cpp-max-generations*)
           (fn-cprt-generations-after-p (cdr generations) (car generations)))
    (null generations)))

(defun fn-cprt-generationsp (generations)
  (declare (xargs :guard t))
  (and (<= (len generations) *fn-cpp-max-generations*)
       (fn-cprt-generations-after-p generations -1)))

; Pack generations may have gaps left by retirement.  The selected generation
; is never retired, so the maximum remains a durable high-water mark.  The
; ordinary checkpoint allocator keeps its separate gap-free contract.
(defun fn-cprt-next-from (generations previous)
  (declare (xargs :guard t))
  (if (consp generations)
      (fn-cprt-next-from (cdr generations) (car generations))
    (if (< (ifix previous) (1- *fn-cpp-max-generations*))
        (1+ (ifix previous))
      :exhausted)))

(defun fn-cprt-next-generation (generations)
  (declare (xargs :guard t))
  (if (fn-cprt-generationsp generations)
      (fn-cprt-next-from generations -1)
    :invalid))

(defun fn-cprt-older-prefix (generations selected)
  (declare (xargs :guard t))
  (if (consp generations)
      (if (< (nfix (car generations)) (nfix selected))
          (cons (car generations)
                (fn-cprt-older-prefix (cdr generations) selected))
        nil)
    nil))

(defun fn-cprt-retire-plan (generations selected)
  (declare (xargs :guard t))
  (if (and (fn-cprt-generationsp generations)
           (natp selected)
           (member-equal selected generations))
      (fn-cprt-older-prefix generations selected)
    :invalid))

; Every successful unlink has its own process-death cut.  Until the directory
; barrier, any issued unlink may survive or disappear on reopen; the selected
; generation and every newer candidate remain outside the plan.
(defun fn-cprt-retire-steps (generations)
  (declare (xargs :guard t))
  (if (consp generations)
      (cons (list :unlink :packs (car generations))
            (cons (list :cut "pack-retire-unlink")
                  (fn-cprt-retire-steps (cdr generations))))
    (list (list :fsync-dir :packs)
          (list :cut "pack-retire-directory"))))

(defun fn-cprt-retire-program (generations selected)
  (declare (xargs :guard t))
  (let ((plan (fn-cprt-retire-plan generations selected)))
    (if (equal plan :invalid) nil
      (fn-cprt-retire-steps plan))))

; ISSUED is the prefix of the plan whose unlink calls have returned.  RETAINED
; chooses which issued names survive a crash before the closing directory
; barrier.  This represents the same per-entry uncertainty as the byte store's
; :del-entry transition without weakening the selected authority.
(defun fn-cprt-crash-survivors (generations issued retained)
  (declare (xargs :guard (and (true-listp issued) (true-listp retained))))
  (if (consp generations)
      (if (and (member-equal (car generations) issued)
               (not (member-equal (car generations) retained)))
          (fn-cprt-crash-survivors (cdr generations) issued retained)
        (cons (car generations)
              (fn-cprt-crash-survivors (cdr generations) issued retained)))
    nil))

(defun fn-cprt-prefixp (prefix whole)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp whole) (equal (car prefix) (car whole))
           (fn-cprt-prefixp (cdr prefix) (cdr whole)))
    (null prefix)))

(defthm fn-cprt-older-prefix-excludes-selected
  (not (member-equal selected
                     (fn-cprt-older-prefix generations selected)))
  :hints (("Goal" :induct (fn-cprt-older-prefix generations selected)
           :in-theory (enable fn-cprt-older-prefix))))

(defthm fn-cprt-plan-excludes-selected
  (implies (not (equal (fn-cprt-retire-plan generations selected) :invalid))
           (not (member-equal selected
                              (fn-cprt-retire-plan generations selected))))
  :hints (("Goal" :in-theory (enable fn-cprt-retire-plan))))

(defthm fn-cprt-unissued-generation-survives-crash
  (implies (and (member-equal generation generations)
                (not (member-equal generation issued)))
           (member-equal generation
                         (fn-cprt-crash-survivors generations issued retained)))
  :hints (("Goal" :induct (fn-cprt-crash-survivors generations issued retained)
           :in-theory (enable fn-cprt-crash-survivors))))

(defthm fn-cprt-prefix-member
  (implies (and (fn-cprt-prefixp prefix whole)
                (member-equal value prefix))
           (member-equal value whole))
  :hints (("Goal" :induct (fn-cprt-prefixp prefix whole)
           :in-theory (enable fn-cprt-prefixp))))

(defthm fn-cprt-selected-survives-retirement-cut
  (let ((plan (fn-cprt-retire-plan generations selected)))
    (implies (and (member-equal selected generations)
                  (fn-cprt-prefixp issued plan))
             (member-equal selected
                           (fn-cprt-crash-survivors generations issued retained))))
  :hints (("Goal" :use ((:instance fn-cprt-plan-excludes-selected)
                         (:instance fn-cprt-prefix-member
                          (prefix issued)
                          (whole (fn-cprt-retire-plan generations selected))
                          (value selected))
                         (:instance fn-cprt-unissued-generation-survives-crash
                          (generation selected)))
           :in-theory (enable fn-cprt-prefixp))))

(defthm fn-cprt-next-from-above-previous
  (implies (and (integerp previous)
                (fn-cprt-generations-after-p generations previous)
                (not (equal (fn-cprt-next-from generations previous)
                            :exhausted)))
           (< previous (fn-cprt-next-from generations previous)))
  :hints (("Goal" :induct (fn-cprt-next-from generations previous)
           :in-theory (enable fn-cprt-generations-after-p fn-cprt-next-from))))

(defthm fn-cprt-member-below-next-from
  (implies (and (integerp previous)
                (fn-cprt-generations-after-p generations previous)
                (member-equal selected generations)
                (not (equal (fn-cprt-next-from generations previous)
                            :exhausted)))
           (< selected (fn-cprt-next-from generations previous)))
  :hints (("Goal" :induct (fn-cprt-next-from generations previous)
           :in-theory (enable fn-cprt-generations-after-p fn-cprt-next-from))))

(defthm fn-cprt-next-after-retirement-is-above-selected
  (implies (and (fn-cprt-generationsp generations)
                (member-equal selected generations)
                (not (equal (fn-cprt-next-generation generations) :exhausted)))
           (< selected (fn-cprt-next-generation generations)))
  :hints (("Goal" :use ((:instance fn-cprt-member-below-next-from
                          (previous -1)))
           :in-theory (enable fn-cprt-next-generation fn-cprt-generationsp))))

(deftheory fn-checkpoint-pack-retire-vocabulary
  '(fn-cprt-generations-after-p fn-cprt-generationsp fn-cprt-next-from
    fn-cprt-next-generation fn-cprt-older-prefix fn-cprt-retire-plan
    fn-cprt-retire-steps fn-cprt-retire-program fn-cprt-crash-survivors
    fn-cprt-prefixp))
(in-theory (disable fn-checkpoint-pack-retire-vocabulary))
