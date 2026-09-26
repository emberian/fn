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
           (fn-record-uint32p (car generations))
           (fn-cprt-generations-after-p (cdr generations) (car generations)))
    (null generations)))

; D27, PRF-171: a pack generation is a uint32 (the name codec's width); how
; many the directory retains is the profile's capacity, checked by the
; allocator (`fn-cprt-next-generation'), not by the shape of the list.
(defun fn-cprt-generationsp (generations)
  (declare (xargs :guard t))
  (fn-cprt-generations-after-p generations -1))

; Pack generations may have gaps left by retirement.  The selected generation
; is never retired, so the maximum remains a durable high-water mark.  The
; ordinary checkpoint allocator keeps its separate gap-free contract.
(defun fn-cprt-next-from (generations previous)
  (declare (xargs :guard t))
  (if (consp generations)
      (fn-cprt-next-from (cdr generations) (car generations))
    (if (< (ifix previous) *fn-cbor-max-uint*)
        (1+ (ifix previous))
      :exhausted)))

(defun fn-cprt-next-generation (generations capacity)
  (declare (xargs :guard t))
  (cond ((not (fn-cprt-generationsp generations)) :invalid)
        ((<= (nfix capacity) (len generations)) :exhausted)
        (t (fn-cprt-next-from generations -1))))

; Publication of a replacement pack must use the same gap-aware namespace
; contract as its allocator.  Ordinary node checkpoints retain the separate
; gap-free fn-cpp-publication-initial policy.
(defun fn-cprt-publication-initial
  (generations proposed-generation exclusivep final-absentp capacity)
  (declare (xargs :guard t))
  (let ((next (fn-cprt-next-generation generations capacity)))
    (cond ((equal next :invalid) '(:error :namespace))
          ((equal next :exhausted) '(:error :exhausted))
          ((not (equal proposed-generation next)) '(:error :generation))
          ((not (equal exclusivep t)) '(:error :authority))
          ((not (equal final-absentp t)) '(:error :occupied))
          (t (list :ok next (fn-jpub-initial t))))))

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
    (if (or (equal plan :invalid) (null plan)) nil
      (fn-cprt-retire-steps plan))))

; ISSUED is a prefix of unlink attempts, including the most recent attempt if
; it returned an ambiguous OS error.  RETAINED chooses which issued names
; survive a crash before the closing directory barrier.  This represents the
; same per-entry uncertainty as the byte store's :del-entry transition without
; weakening the selected authority.
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

(defthm fn-cprt-retirement-never-increases-namespace-count
  (<= (len (fn-cprt-crash-survivors generations issued retained))
      (len generations))
  :hints (("Goal" :induct (fn-cprt-crash-survivors generations issued retained)
           :in-theory (enable fn-cprt-crash-survivors))))

(defthm fn-cprt-issued-unretained-name-frees-one-slot
  (implies (and (member-equal generation generations)
                (member-equal generation issued)
                (not (member-equal generation retained)))
           (< (len (fn-cprt-crash-survivors generations issued retained))
              (len generations)))
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
                (not (equal (fn-cprt-next-generation generations capacity)
                            :exhausted)))
           (< selected (fn-cprt-next-generation generations capacity)))
  :hints (("Goal" :use ((:instance fn-cprt-member-below-next-from
                          (previous -1)))
           :in-theory (enable fn-cprt-next-generation fn-cprt-generationsp))))

;; The pack allocator's two bounds (D27, PRF-171).  The retained names are
;; the profile's capacity; the numbers run to the uint32 width of the name
;; codec, and nothing else stops them.

(defun fn-cprt-last (generations)
  (declare (xargs :guard t))
  (if (consp generations)
      (if (consp (cdr generations)) (fn-cprt-last (cdr generations))
        (car generations))
    -1))

(local
 (defthm fn-cprt-next-from-is-after-the-last
   (implies (and (integerp previous)
                 (fn-cprt-generations-after-p generations previous))
            (equal (fn-cprt-next-from generations previous)
                   (let ((last (if (consp generations)
                                   (fn-cprt-last generations)
                                 previous)))
                     (if (< last *fn-cbor-max-uint*) (+ 1 last) :exhausted))))
   :hints (("Goal" :induct (fn-cprt-next-from generations previous)
            :in-theory (enable fn-cprt-next-from fn-cprt-generations-after-p
                               fn-cprt-last fn-record-uint32p)))))

; KEYSTONE (the pack allocator refuses exactly at the operator's capacity or
; the codec width).  On a valid namespace the next pack generation is
; :exhausted exactly when CAPACITY names are already retained or the
; highest retained number is the uint32 maximum; otherwise it is the number
; after the highest.  Host: host/native/checkpoint.lisp
; `fnn-pack-publish-generation' through host/checkpoint-host.lisp
; `fn-store-checkpoint-pack-next-generation' and
; `fn-store-checkpoint-pack-publication-initial'.
(defthm fn-cprt-next-generation-refuses-exactly-at-the-profile-capacity
  (implies (fn-cprt-generationsp generations)
           (equal (fn-cprt-next-generation generations capacity)
                  (cond ((<= (nfix capacity) (len generations)) :exhausted)
                        ((<= *fn-cbor-max-uint* (fn-cprt-last generations))
                         :exhausted)
                        (t (+ 1 (fn-cprt-last generations))))))
  :hints (("Goal" :in-theory (enable fn-cprt-next-generation
                                     fn-cprt-generationsp fn-cprt-last))))

(deftheory fn-checkpoint-pack-retire-vocabulary
  '(fn-cprt-generations-after-p fn-cprt-generationsp fn-cprt-next-from
    fn-cprt-next-generation fn-cprt-publication-initial
    fn-cprt-older-prefix fn-cprt-retire-plan
    fn-cprt-retire-steps fn-cprt-retire-program fn-cprt-crash-survivors
    fn-cprt-prefixp fn-cprt-last))
(in-theory (disable fn-checkpoint-pack-retire-vocabulary))
