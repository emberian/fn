; LC allocation consumers of the landed v2 predicate.
(in-package "ACL2")
(include-book "log-checkpoint-values")
(include-book "defkeystone")
(verify-guards fn-lc-header-next-id)
(verify-guards fn-lc-header-exhaustedp)
(defun fn-lc-header-ids-coverp (header segs keys)
 (declare (xargs :guard t))
 (fn-lc-segment-ids-below-next (fn-lc-header-next-id header)
                              (fn-lc-header-exhaustedp header) segs keys))
(assert-event
 (let* ((next-id 22) (exhaustedp nil) (segs nil) (keys nil)
        (out (mv-list 4 (fn-lc-allocate-segment next-id exhaustedp))))
  (and (fn-lc-segment-ids-below-next next-id exhaustedp segs keys)
       (equal (car out) :ok)
       (not (fn-lc-id-allocatedp (nth 1 out) next-id exhaustedp))
       (fn-lc-segment-ids-below-next (nth 2 out) (nth 3 out)
                                    (cons (list (nth 1 out) nil nil) segs) keys)
       (not (fn-lc-id-allocatedp (nth 1 out) next-id exhaustedp)))))
(with-guard-checking-event :none
 (assert-event
  (let* ((next-id -1) (exhaustedp nil) (segs nil) (keys nil)
         (out (mv-list 4 (fn-lc-allocate-segment next-id exhaustedp))))
   (and (not (fn-lc-segment-ids-below-next next-id exhaustedp segs keys))
        (equal (car out) :ok)
        (not (and (not (fn-lc-id-allocatedp (nth 1 out) next-id exhaustedp))
                   (fn-lc-segment-ids-below-next (nth 2 out) (nth 3 out)
                     (cons (list (nth 1 out) nil nil) segs) keys)))))))
(local (defthm b1-allocated-monotone
 (implies (and (natp next-id) (fn-lc-id-allocatedp id next-id nil))
          (fn-lc-id-allocatedp id (+ 1 next-id) nil))))
(local (defthm b1-segs-monotone
 (implies (and (natp next-id) (fn-lc-seg-ids-allocatedp segs next-id nil))
          (fn-lc-seg-ids-allocatedp segs (+ 1 next-id) nil))
 :hints (("Goal" :induct (fn-lc-seg-ids-allocatedp segs next-id nil)))))
(local (defthm b1-keys-monotone
 (implies (and (natp next-id) (fn-lc-key-ids-allocatedp keys next-id nil))
          (fn-lc-key-ids-allocatedp keys (+ 1 next-id) nil))
 :hints (("Goal" :induct (fn-lc-key-ids-allocatedp keys next-id nil)))))
(local (defthm b1-segs-exhausted
 (implies (fn-lc-seg-ids-allocatedp segs next-id nil)
          (fn-lc-seg-ids-allocatedp segs next-id t))
 :hints (("Goal" :induct (fn-lc-seg-ids-allocatedp segs next-id nil)))))
(local (defthm b1-keys-exhausted
 (implies (fn-lc-key-ids-allocatedp keys next-id nil)
          (fn-lc-key-ids-allocatedp keys next-id t))
 :hints (("Goal" :induct (fn-lc-key-ids-allocatedp keys next-id nil)))))
(local (defthm b1-segs-cons
 (equal (fn-lc-seg-ids-allocatedp (cons entry segs) next exhausted)
        (and (consp entry) (fn-lc-id-allocatedp (car entry) next exhausted)
             (fn-lc-seg-ids-allocatedp segs next exhausted)))
 :hints (("Goal" :expand ((fn-lc-seg-ids-allocatedp (cons entry segs) next exhausted))))))
(defthm fn-lc-allocate-keeps-segment-ids-below-next
 (implies (fn-lc-segment-ids-below-next next-id exhaustedp segs keys)
           (mv-let (answer id new-next new-exhaustedp)
             (fn-lc-allocate-segment next-id exhaustedp)
             (implies (equal answer :ok)
                      (and (not (fn-lc-id-allocatedp id next-id exhaustedp))
                           (fn-lc-segment-ids-below-next new-next new-exhaustedp
                                                         (cons (list id nil nil) segs) keys)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-lc-seg-ids-allocatedp fn-lc-key-ids-allocatedp))))
(with-guard-checking-event :none
 (assert-event
  (let* ((header '(:lc-header (0 0 0 0 nil) 22 nil nil nil))
         (segs nil) (keys nil)
         (out (mv-list 3 (fn-lc-roll-segment header segs))))
   (and (fn-lc-header-ids-coverp header segs keys)
        (equal (car out) :ok)
        (fn-lc-header-ids-coverp (nth 1 out) (nth 2 out) keys)
        (not (member-equal (caar (nth 2 out)) (fn-lc-seg-ids segs)))
        (equal (cdr (nth 2 out)) segs)
        (not (fn-lc-header-ids-coverp header (nth 2 out) keys))))))
(with-guard-checking-event :none
 (assert-event
  (let* ((header '(:lc-header (0 0 0 0 nil) 22 nil nil nil))
         (segs '((100 nil nil))) (keys nil)
         (out (mv-list 3 (fn-lc-roll-segment header segs))))
   (and (not (fn-lc-header-ids-coverp header segs keys))
        (equal (car out) :ok)
        (not (and (fn-lc-header-ids-coverp (nth 1 out) (nth 2 out) keys)
                   (not (member-equal (caar (nth 2 out)) (fn-lc-seg-ids segs)))
                   (equal (cdr (nth 2 out)) segs)))))))
(with-guard-checking-event :none
 (assert-event
  (let* ((header '(:lc-header (0 0 0 0 nil) 22 t nil nil))
         (segs '((1 nil nil))) (keys nil)
         (out (mv-list 3 (fn-lc-roll-segment header segs))))
   (and (fn-lc-header-ids-coverp header segs keys)
        (not (equal (car out) :ok))
        (not (and (fn-lc-header-ids-coverp (nth 1 out) (nth 2 out) keys)
                   (not (member-equal (caar (nth 2 out)) (fn-lc-seg-ids segs)))
                   (equal (cdr (nth 2 out)) segs)))))))
(defthm fn-lc-roll-keeps-segment-ids-below-next
 (let ((out (fn-lc-roll-segment header segs)))
    (implies (and (fn-lc-header-ids-coverp header segs keys)
                  (equal (mv-nth 0 out) :ok))
             (and (fn-lc-header-ids-coverp (mv-nth 1 out) (mv-nth 2 out) keys)
                  (not (member-equal (car (car (mv-nth 2 out))) (fn-lc-seg-ids segs)))
                  (equal (cdr (mv-nth 2 out)) segs))))
 :rule-classes nil
 :hints (("Goal" :in-theory (disable fn-lc-seg-ids-allocatedp fn-lc-key-ids-allocatedp fn-lc-seg-ids))))

(defteeth fn-lc-allocate-keeps-segment-ids-below-next
 :claim (((cover (fn-lc-segment-ids-below-next next-id exhaustedp segs keys)))
           (mv-let (answer id new-next new-exhaustedp)
             (fn-lc-allocate-segment next-id exhaustedp)
             (implies (equal answer :ok)
                      (and (not (fn-lc-id-allocatedp id next-id exhaustedp))
                           (fn-lc-segment-ids-below-next new-next new-exhaustedp
                                                         (cons (list id nil nil) segs) keys)))))
 :subject fn-lc-allocate-segment
 :witness ((next-id 22) (exhaustedp nil) (segs nil) (keys nil))
 :breaks ((cover ((next-id -1)) :logical "negative allocator input outside its omitted type guard"))
 :mutations ((reuses-id
  (:conclusion
           (mv-let (answer id new-next new-exhaustedp)
             (fn-lc-allocate-segment next-id exhaustedp)
             (implies (equal answer :ok)
                      (and (fn-lc-id-allocatedp id next-id exhaustedp)
                           (fn-lc-segment-ids-below-next new-next new-exhaustedp
                                                         (cons (list id nil nil) segs) keys)))))
  ((next-id 22) (exhaustedp nil) (segs nil) (keys nil))
  :fault "allocator reports an already allocated id as fresh")))

(defteeth fn-lc-roll-keeps-segment-ids-below-next
 :claim (let ((out (fn-lc-roll-segment header segs)))
  (((cover (fn-lc-header-ids-coverp header segs keys))
    (accepted (equal (mv-nth 0 out) :ok)))
   (and (fn-lc-header-ids-coverp (mv-nth 1 out) (mv-nth 2 out) keys)
        (not (member-equal (car (car (mv-nth 2 out))) (fn-lc-seg-ids segs)))
        (equal (cdr (mv-nth 2 out)) segs))))
 :subject fn-lc-roll-segment
 :witness ((header '(:lc-header (0 0 0 0 nil) 22 nil nil nil)) (segs nil) (keys nil))
 :breaks ((cover ((segs '((100 nil nil)))))
          (accepted ((header '(:lc-header (0 0 0 0 nil) 22 t nil nil))
                     (segs '((1 nil nil))))))
 :mutations ((omits-advance
  (:conclusion (and (fn-lc-header-ids-coverp header (mv-nth 2 out) keys)
                   (not (member-equal (car (car (mv-nth 2 out))) (fn-lc-seg-ids segs)))
                   (equal (cdr (mv-nth 2 out)) segs)))
  ((header '(:lc-header (0 0 0 0 nil) 22 nil nil nil)) (segs nil) (keys nil))
  :fault "rollover returns the old allocation header without advancing next-id")))
(defteeth-check (fn-lc-allocate-keeps-segment-ids-below-next
                fn-lc-roll-keeps-segment-ids-below-next))
