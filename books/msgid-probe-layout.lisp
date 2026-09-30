; Exact operational layout model for the full circular P2 probe.
; This is the abstraction of backing words, not a rows-derived reconstruction.
(in-package "ACL2")
(include-book "msgid-probe-cursor")

(defun fn-mpl-tag-at (page slot words)
  (declare (xargs :guard (and (natp page) (natp slot) (true-listp words))))
  (nfix (nth (fn-mpxt-slot page slot) words)))

(defun fn-mpl-seq-at (page slot words)
  (declare (xargs :guard (and (natp page) (natp slot) (true-listp words))))
  (nfix (nth (+ *fn-mpxt-page-slots* (fn-mpxt-slot page slot)) words)))

(defun fn-mpl-next (tag cursor fuel pages words)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (natp tag) (true-listp words)
                              (fn-mpr-cursorp cursor pages)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :done cursor nil fuel))
        ((zp fuel) (mv :yield cursor nil 0))
        (t
         (let* ((page (nth 0 cursor)) (slot (nth 2 cursor))
                (found-tag (fn-mpl-tag-at page slot words))
                (next (fn-mpr-advance cursor pages)))
           (cond ((equal found-tag 0) (mv :done cursor nil (- fuel 1)))
                 ((equal found-tag tag)
                  (let ((encoded-seq (fn-mpl-seq-at page slot words)))
                    (if (zp encoded-seq)
                        (mv :recovery-required cursor nil (- fuel 1))
                      (mv :candidate next (- encoded-seq 1) (- fuel 1)))))
                 (t (fn-mpl-next tag next (- fuel 1) pages words)))))))

(verify-guards fn-mpl-next
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

; The result includes the physical candidate/yield schedule and exact residual
; fuel. Final semantic selection is a separate query invariant over captured rows.
(defthm fn-mpr-next-is-operational-layout-step
  (implies (and (natp tag) (fn-mpxt-wfp fn-mpxt)
                (fn-mpr-cursorp cursor (fn-mpxt-pages fn-mpxt))
                (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
           (equal (fn-mpr-next tag cursor fuel fn-mpxt)
                  (fn-mpl-next tag cursor fuel (fn-mpxt-pages fn-mpxt)
                               (nth 0 fn-mpxt))))
  :hints (("Goal" :induct (fn-mpr-next tag cursor fuel fn-mpxt)
           :in-theory (enable fn-mpr-next fn-mpl-next fn-mpl-tag-at fn-mpl-seq-at
                              fn-mpxt-tag-at fn-mpxt-seq-at fn-mpxt-wi
                              fn-mpxt-pages))))

(defun fn-mpl-write-slot (page slot tag seq words)
  (declare (xargs :guard (and (natp page) (natp slot) (natp tag) (natp seq)
                              (true-listp words))))
  (update-nth (+ *fn-mpxt-page-slots* (fn-mpxt-slot page slot)) (+ 1 seq)
              (update-nth (fn-mpxt-slot page slot) tag words)))

(defun fn-mpl-place (tag seq cursor fuel pages words)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (posp tag) (natp seq) (true-listp words)
                              (fn-mpr-cursorp cursor pages)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :full cursor fuel words))
        ((zp fuel) (mv :yield cursor 0 words))
        (t
         (let* ((page (nth 0 cursor)) (slot (nth 2 cursor))
                (next (fn-mpr-advance cursor pages)))
           (if (equal (fn-mpl-tag-at page slot words) 0)
               (mv :placed next (- fuel 1)
                   (fn-mpl-write-slot page slot tag seq words))
             (fn-mpl-place tag seq next (- fuel 1) pages words))))))

(verify-guards fn-mpl-place
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

(defthm fn-mpr-place-is-operational-layout-step
  (implies (and (posp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*)
                (fn-mpxt-wfp fn-mpxt)
                (fn-mpr-cursorp cursor (fn-mpxt-pages fn-mpxt))
                (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
           (let ((physical (fn-mpr-place tag seq cursor fuel fn-mpxt))
                 (logical (fn-mpl-place tag seq cursor fuel
                                        (fn-mpxt-pages fn-mpxt) (nth 0 fn-mpxt))))
             (and (equal (nth 0 physical) (nth 0 logical))
                  (equal (nth 1 physical) (nth 1 logical))
                  (equal (nth 2 physical) (nth 2 logical))
                  (equal (nth 0 (nth 3 physical)) (nth 3 logical)))))
  :hints (("Goal" :induct (fn-mpr-place tag seq cursor fuel fn-mpxt)
           :in-theory (enable fn-mpr-place fn-mpl-place fn-mpl-write-slot
                              fn-mpl-tag-at fn-mpxt-write-slot
                              fn-mpxt-tag-at fn-mpxt-wi fn-mpxt-pages
                              update-fn-mpxt-wi))))

(defun fn-mpl-remaining (cursor)
  (declare (xargs :guard (and (true-listp cursor) (equal (len cursor) 3)
                              (natp (nth 1 cursor)) (natp (nth 2 cursor)))))
  (if (zp (nth 1 cursor)) 0
    (+ (* (- (nth 1 cursor) 1) *fn-mpxt-page-slots*)
       (- *fn-mpxt-page-slots* (nth 2 cursor)))))

(defthm fn-mpl-remaining-of-advance
  (implies (and (fn-mpr-cursorp cursor pages) (posp (nth 1 cursor)))
           (equal (fn-mpl-remaining (fn-mpr-advance cursor pages))
                  (- (fn-mpl-remaining cursor) 1)))
  :hints (("Goal" :in-theory (enable fn-mpl-remaining fn-mpr-advance fn-mpr-cursorp))))

(defun fn-mpl-reachable (tag seq cursor pages words)
  (declare (xargs :measure (nfix (fn-mpl-remaining cursor))
                  :hints (("Goal" :in-theory (e/d (fn-mpr-cursorp fn-mpl-remaining)
                                                   (fn-mpr-advance fn-mpl-tag-at fn-mpl-seq-at))))
                  :guard (and (posp tag) (natp seq) (true-listp words)
                              (fn-mpr-cursorp cursor pages))
                  :verify-guards nil))
  (if (or (not (fn-mpr-cursorp cursor pages))
          (zp (nth 1 cursor))
          (zp (fn-mpl-tag-at (nth 0 cursor) (nth 2 cursor) words)))
      nil
    (or (and (equal tag (fn-mpl-tag-at (nth 0 cursor) (nth 2 cursor) words))
             (equal (+ 1 seq) (fn-mpl-seq-at (nth 0 cursor) (nth 2 cursor) words)))
        (fn-mpl-reachable tag seq (fn-mpr-advance cursor pages) pages words))))

(verify-guards fn-mpl-reachable
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

(defthm fn-mpl-tag-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (equal (fn-mpl-tag-at q i (fn-mpl-write-slot p j tag seq words))
                  (if (and (equal q p) (equal i j)) (nfix tag)
                    (fn-mpl-tag-at q i words))))
  :hints (("Goal" :in-theory (enable fn-mpl-tag-at fn-mpl-write-slot)
           :use ((:instance fn-mpxt-slot-equal)
                 (:instance fn-mpxt-slot-is-not-a-seq-word)))))

(defthm fn-mpl-seq-at-of-write-slot
  (implies (and (natp q) (natp i) (< i *fn-mpxt-page-slots*)
                (natp p) (natp j) (< j *fn-mpxt-page-slots*))
           (equal (fn-mpl-seq-at q i (fn-mpl-write-slot p j tag seq words))
                  (if (and (equal q p) (equal i j)) (nfix (+ 1 seq))
                    (fn-mpl-seq-at q i words))))
  :hints (("Goal" :in-theory (enable fn-mpl-seq-at fn-mpl-write-slot fn-mpxt-slot)
           :use ((:instance fn-mpxt-slot-equal)
                 (:instance fn-mpxt-slot-is-not-a-seq-word
                             (q p) (i j) (p q) (j i))))))

(defthm fn-mpl-write-empty-preserves-reachable
  (implies (and (fn-mpr-cursorp cursor pages)
                (natp p) (< p pages) (natp j) (< j *fn-mpxt-page-slots*)
                (equal (fn-mpl-tag-at p j words) 0)
                (posp newtag)
                (fn-mpl-reachable tag seq cursor pages words))
           (fn-mpl-reachable tag seq cursor pages
                             (fn-mpl-write-slot p j newtag newseq words)))
  :hints (("Goal" :induct (fn-mpl-reachable tag seq cursor pages words)
           :expand ((:free (tag seq) (fn-mpl-reachable tag seq cursor pages
                                     (fn-mpl-write-slot p j newtag newseq words))))
           :in-theory (e/d (fn-mpl-reachable fn-mpr-cursorp)
                            (fn-mpl-tag-at fn-mpl-seq-at fn-mpl-write-slot
                             fn-mpr-advance fn-mpl-remaining)))))

(defthm fn-mpl-cursor-field-bounds
  (implies (fn-mpr-cursorp cursor pages)
           (and (consp cursor) (natp (car cursor)) (< (car cursor) pages)
                (natp (nth 0 cursor)) (< (nth 0 cursor) pages)
                (natp (nth 1 cursor))
                (natp (nth 2 cursor)) (< (nth 2 cursor) *fn-mpxt-page-slots*)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

(defthm fn-mpl-place-preserves-existing-reachable
  (implies (and (fn-mpr-cursorp cursor pages)
                (fn-mpr-cursorp search pages) (posp tag)
                (fn-mpl-reachable oldtag oldseq search pages words))
           (fn-mpl-reachable oldtag oldseq search pages
                             (mv-nth 3 (fn-mpl-place tag seq cursor fuel pages words))))
  :hints (("Goal" :induct (fn-mpl-place tag seq cursor fuel pages words)
           :in-theory (e/d (fn-mpl-place)
                            (fn-mpl-reachable fn-mpl-write-slot fn-mpl-tag-at fn-mpr-cursorp
                             fn-mpl-seq-at fn-mpr-advance fn-mpl-remaining)))))

(defthm fn-mpl-place-keeps-occupied-tag
  (implies (and (fn-mpr-cursorp cursor pages)
                (natp p) (< p pages) (natp j) (< j *fn-mpxt-page-slots*)
                (not (equal (fn-mpl-tag-at p j words) 0)))
           (equal (fn-mpl-tag-at p j (mv-nth 3 (fn-mpl-place tag seq cursor fuel pages words)))
                  (fn-mpl-tag-at p j words)))
  :hints (("Goal" :induct (fn-mpl-place tag seq cursor fuel pages words)
           :in-theory (e/d (fn-mpl-place)
                            (fn-mpl-tag-at fn-mpl-seq-at fn-mpl-write-slot fn-mpr-cursorp
                             fn-mpr-advance fn-mpl-remaining)))))

(defthm fn-mpl-placed-entry-is-reachable
  (implies (and (fn-mpr-cursorp cursor pages) (posp tag) (natp seq)
                (equal (mv-nth 0 (fn-mpl-place tag seq cursor fuel pages words)) :placed))
           (fn-mpl-reachable tag seq cursor pages
                             (mv-nth 3 (fn-mpl-place tag seq cursor fuel pages words))))
  :hints (("Goal" :induct (fn-mpl-place tag seq cursor fuel pages words)
           :expand ((:free (w) (fn-mpl-reachable tag seq cursor pages w)))
           :in-theory (e/d (fn-mpl-place)
                            (fn-mpl-reachable fn-mpl-write-slot fn-mpl-tag-at fn-mpr-cursorp
                             fn-mpl-seq-at fn-mpr-advance fn-mpl-remaining)))))

(defthm fn-mpl-next-done-has-no-reachable-candidate
  (implies (and (fn-mpr-cursorp cursor pages)
                (equal (mv-nth 0 (fn-mpl-next tag cursor fuel pages words)) :done))
           (not (fn-mpl-reachable tag seq cursor pages words)))
  :hints (("Goal" :induct (fn-mpl-next tag cursor fuel pages words)
           :expand ((:free (tag seq) (fn-mpl-reachable tag seq cursor pages words)))
           :in-theory (e/d (fn-mpl-next)
                            (fn-mpl-reachable fn-mpl-tag-at fn-mpl-seq-at fn-mpr-cursorp
                             fn-mpr-advance fn-mpl-remaining)))))

(defthm fn-mpl-next-retains-or-delivers-reachable-candidate
  (implies (and (fn-mpr-cursorp cursor pages) (natp seq)
                (fn-mpl-reachable tag seq cursor pages words)
                (member-equal (mv-nth 0 (fn-mpl-next tag cursor fuel pages words))
                              '(:yield :candidate)))
           (or (and (equal (mv-nth 0 (fn-mpl-next tag cursor fuel pages words)) :candidate)
                    (equal (mv-nth 2 (fn-mpl-next tag cursor fuel pages words)) seq))
               (fn-mpl-reachable tag seq
                 (mv-nth 1 (fn-mpl-next tag cursor fuel pages words)) pages words)))
  :hints (("Goal" :induct (fn-mpl-next tag cursor fuel pages words)
           :expand ((:free (tag seq) (fn-mpl-reachable tag seq cursor pages words)))
           :in-theory (e/d (fn-mpl-next)
                            (fn-mpl-reachable fn-mpl-tag-at fn-mpl-seq-at fn-mpr-cursorp
                             fn-mpr-advance fn-mpl-remaining)))))

(in-theory (disable fn-mpl-tag-at fn-mpl-seq-at fn-mpl-next fn-mpl-write-slot
                    fn-mpl-place fn-mpl-remaining fn-mpl-reachable))
