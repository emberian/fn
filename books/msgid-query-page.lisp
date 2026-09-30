; One borrowed immutable page tick of the operational Message-ID iterator.
; Page transition returns to the provider's bounded directory continuation.
(in-package "ACL2")
(include-book "msgid-probe-layout")

(defun fn-mpl-page-next (tag cursor fuel pages page-index page-words)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (natp tag) (fn-mpr-cursorp cursor pages)
                              (natp page-index) (< page-index pages)
                              (true-listp page-words)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :done cursor nil fuel))
        ((zp fuel) (mv :yield cursor nil 0))
        ((not (equal (nth 0 cursor) page-index))
         (mv :next-page cursor nil fuel))
        (t
         (let* ((slot (nth 2 cursor))
                (found-tag (fn-mpl-tag-at 0 slot page-words))
                (next (fn-mpr-advance cursor pages)))
           (cond ((equal found-tag 0) (mv :done cursor nil (- fuel 1)))
                 ((equal found-tag tag)
                  (let ((encoded-seq (fn-mpl-seq-at 0 slot page-words)))
                    (if (zp encoded-seq)
                        (mv :recovery-required cursor nil (- fuel 1))
                      (mv :candidate next (- encoded-seq 1) (- fuel 1)))))
                 (t (fn-mpl-page-next tag next (- fuel 1) pages page-index page-words)))))))

(verify-guards fn-mpl-page-next
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

(in-theory (disable fn-mpl-page-next))

; The provider establishes this once for a borrowed chunk and carries it
; through ticks. It is a logical relation, never a served-page revalidation.
(defun fn-mpl-page-match-from (slot page-index page-words words)
  (declare (xargs :guard (and (natp page-index) (true-listp page-words) (true-listp words))
                  :measure (nfix (- *fn-mpxt-page-slots* (nfix slot)))
                  :verify-guards nil))
  (if (or (not (natp slot)) (>= slot *fn-mpxt-page-slots*)) t
    (and (equal (fn-mpl-tag-at 0 slot page-words)
                (fn-mpl-tag-at page-index slot words))
         (equal (fn-mpl-seq-at 0 slot page-words)
                (fn-mpl-seq-at page-index slot words))
         (fn-mpl-page-match-from (+ 1 slot) page-index page-words words))))

(defthm fn-mpl-page-match-from-slot
  (implies (and (natp from) (natp slot) (<= from slot)
                (< slot *fn-mpxt-page-slots*)
                (fn-mpl-page-match-from from page-index page-words words))
           (and (equal (fn-mpl-tag-at 0 slot page-words)
                       (fn-mpl-tag-at page-index slot words))
                (equal (fn-mpl-seq-at 0 slot page-words)
                       (fn-mpl-seq-at page-index slot words))))
  :hints (("Goal" :induct (fn-mpl-page-match-from from page-index page-words words)
           :in-theory (enable fn-mpl-page-match-from))))

(defthm fn-mpl-page-match-at-cursor
  (implies (and (fn-mpr-cursorp cursor pages)
                (equal (nth 0 cursor) page-index)
                (fn-mpl-page-match-from 0 page-index page-words words))
           (and (equal (fn-mpl-tag-at 0 (nth 2 cursor) page-words)
                       (fn-mpl-tag-at (nth 0 cursor) (nth 2 cursor) words))
                (equal (fn-mpl-seq-at 0 (nth 2 cursor) page-words)
                       (fn-mpl-seq-at (nth 0 cursor) (nth 2 cursor) words))))
  :hints (("Goal" :use ((:instance fn-mpl-page-match-from-slot
                                   (from 0) (slot (nth 2 cursor))))
           :in-theory (e/d (fn-mpr-cursorp)
                            (fn-mpl-page-match-from fn-mpl-tag-at fn-mpl-seq-at)))))

(defthm fn-mpl-page-step-refines-operational-layout
  (implies (and (fn-mpr-cursorp cursor pages)
                (fn-mpl-page-match-from 0 page-index page-words words)
                (not (equal (mv-nth 0 (fn-mpl-page-next tag cursor fuel pages
                                                      page-index page-words)) :next-page)))
           (equal (fn-mpl-page-next tag cursor fuel pages page-index page-words)
                  (fn-mpl-next tag cursor fuel pages words)))
  :hints (("Goal" :induct (fn-mpl-page-next tag cursor fuel pages page-index page-words)
           :expand ((:free (tag) (fn-mpl-next tag cursor fuel pages words))
                    (:free (tag page-index) (fn-mpl-page-next tag cursor fuel pages page-index page-words)))
           :in-theory (e/d ((:induction fn-mpl-page-next))
                            ((:definition fn-mpl-page-next) (:definition fn-mpl-next) fn-mpr-cursorp fn-mpl-tag-at fn-mpl-seq-at
                             fn-mpr-advance fn-mpl-page-match-from)))
          ("Subgoal *1/1" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/2" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/3" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/4" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/5" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/6" :use ((:instance fn-mpl-page-match-at-cursor)))
          ("Subgoal *1/7" :use ((:instance fn-mpl-page-match-at-cursor)))
))

(verify-guards fn-mpl-page-match-from)
(in-theory (disable fn-mpl-page-match-from))

; The writer shares the query's exact circular cursor, and mutates only this
; unpublished local page. Crossing its boundary returns to directory/COW work.
(defun fn-mpl-page-place (tag seq cursor fuel pages page-index page-words)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (posp tag) (natp seq) (fn-mpr-cursorp cursor pages)
                              (natp page-index) (< page-index pages)
                              (true-listp page-words)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :full cursor fuel page-words))
        ((zp fuel) (mv :yield cursor 0 page-words))
        ((not (equal (nth 0 cursor) page-index)) (mv :next-page cursor fuel page-words))
        (t
         (let* ((slot (nth 2 cursor)) (next (fn-mpr-advance cursor pages)))
           (if (equal (fn-mpl-tag-at 0 slot page-words) 0)
               (mv :placed next (- fuel 1) (fn-mpl-write-slot 0 slot tag seq page-words))
             (fn-mpl-page-place tag seq next (- fuel 1) pages page-index page-words))))))

(verify-guards fn-mpl-page-place
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))
(in-theory (disable fn-mpl-page-place))
