; A probe reads the first entry in the upper half of the search interval.
(in-package "ACL2")
(include-book "range-seek-scan-proof")

(defun fn2-range-natural-keysp (es)
 (if (atom es) t
   (and (natp (caar es)) (natp (cadar es))
        (fn2-range-natural-keysp (cdr es)))))
(defun-nx fn2-overview-probe-window (es group mid hi)
 (fn2-range-window-spec *fn2-overview-range-key* es (list group mid) (list group (1- hi)) nil 0))

(local
 (defun-nx fn2-overview-probe-side (entry group mid hi)
  (cond ((eq (fn2-run-key-order-spec *fn2-overview-range-key* entry (list group mid)) :lt) :before)
        ((eq (fn2-run-key-order-spec *fn2-overview-range-key* entry (list group (1- hi))) :gt) :after)
        (t :inside))))

(local
 (defthm fn2-overview-probe-window-step
  (equal (fn2-overview-probe-window es group mid hi)
         (cond ((atom es) nil)
               ((eq (fn2-overview-probe-side (car es) group mid hi) :before)
                (fn2-overview-probe-window (cdr es) group mid hi))
               ((eq (fn2-overview-probe-side (car es) group mid hi) :after) nil)
               (t (cons (car es) (fn2-overview-probe-window (cdr es) group mid hi)))))
  :rule-classes ((:definition :controller-alist ((fn2-overview-probe-window t nil nil nil))))
  :hints (("Goal" :expand ((:free (lo top) (fn2-range-window-spec *fn2-overview-range-key* es lo top nil 0)))
           :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthm fn2-overview-probe-side-values
  (implies (and (natp group) (natp mid) (integerp hi) (< mid hi)
                (natp (car e)) (natp (cadr e)))
           (equal (fn2-overview-probe-side e group mid hi)
                  (cond ((< (car e) group) :before)
                        ((< group (car e)) :after)
                        ((< (cadr e) mid) :before)
                        ((<= hi (cadr e)) :after)
                        (t :inside))))
  :hints (("Goal" :cases ((< (cadr e) hi))))))

(local
 (defthm fn2-range-sorted-tail
  (implies (fn2-run-sorted-spec key es)
           (fn2-run-sorted-spec key (cdr es)))
  :hints (("Goal" :expand ((fn2-run-sorted-spec key es))))))

(local
 (defthm fn2-range-probe-past-both
  (implies (and (consp es) (natp (caar es)) (natp (cadar es)) (natp group)
                (natp mid) (integerp hi) (< mid hi)
                (fn2-run-sorted-spec *fn2-overview-range-key* es)
                (eq (fn2-overview-probe-side (car es) group mid hi) :after))
           (and (equal (fn2-range-seek-scan es (list group) 2 p hi 3 acc) acc)
                (equal (fn2-range-seek-scan es (list group) 2 p mid 3 acc) acc)))
  :rule-classes nil
  :hints (("Goal" :use (fn2-range-seek-scan-above-hi (:instance fn2-range-seek-scan-above-hi (hi mid)))
           :in-theory (disable fn2-range-seek-scan-above-hi fn2-range-seek-scan
                               fn2-run-sorted-spec fn2-overview-probe-side)))))

(local
 (defthm fn2-range-probe-over-position
  (implies (and (consp es) (natp (caar es)) (natp (cadar es)) (natp group)
                (natp mid) (integerp hi) (< mid hi)
                (fn2-range-monotone-scan es (list group) 3 last)
                (eq (fn2-overview-probe-side (car es) group mid hi) :inside)
                (< p (nfix (nth 3 (car es)))))
           (equal (fn2-range-seek-scan es (list group) 2 p bound 3 acc) acc))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-range-seek-scan-after-position (es (cdr es)) (prefix (list group))
                                     (last (nfix (nth 3 (car es)))) (hi bound)))
           :expand ((fn2-range-seek-scan es (list group) 2 p bound 3 acc)
                    (fn2-range-monotone-scan es (list group) 3 last))
           :in-theory (disable fn2-range-seek-scan-after-position fn2-range-seek-scan
                               fn2-range-monotone-scan fn2-overview-probe-side)))))

(local
 (defthm fn2-range-probe-at-position
  (implies (and (consp es) (natp (caar es)) (natp (cadar es)) (natp group)
                (natp mid) (integerp hi) (< mid hi)
                (fn2-run-sorted-spec *fn2-overview-range-key* es)
                (eq (fn2-overview-probe-side (car es) group mid hi) :inside)
                (<= (nfix (nth 3 (car es))) p))
           (< (cadar es) (fn2-range-seek-scan es (list group) 2 p hi 3 acc)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-range-seek-scan-preserves-floor (es (cdr es))
                                   (n (cadar es)) (acc (+ 1 (cadar es)))))
           :expand ((:free (prefix) (fn2-range-seek-scan es prefix 2 p hi 3 acc))
                    (fn2-run-sorted-spec *fn2-overview-range-key* es))
           :in-theory (disable fn2-range-seek-scan fn2-run-sorted-spec fn2-overview-probe-side)))))

(local
 (defun-nx fn2-overview-probe-prefix-induction (es group mid hi p last acc)
  (cond ((atom es) (list last acc))
        ((not (eq (fn2-overview-probe-side (car es) group mid hi) :before)) (list last acc))
        ((not (fn2-range-prefixp (list group) (car es)))
         (fn2-overview-probe-prefix-induction (cdr es) group mid hi p last acc))
        ((<= (nfix (nth 3 (car es))) p)
         (fn2-overview-probe-prefix-induction (cdr es) group mid hi p (nfix (nth 3 (car es))) (+ 1 (nfix (cadar es)))))
        (t (fn2-overview-probe-prefix-induction (cdr es) group mid hi p (nfix (nth 3 (car es))) acc)))))

; An empty window or an over-limit first row lets the scan discard [MID, HI).
(defthm fn2-range-seek-upper-probe
 (implies (and (natp group) (natp mid) (integerp hi) (< mid hi)
               (fn2-range-natural-keysp es)
               (fn2-run-sorted-spec *fn2-overview-range-key* es)
               (fn2-range-monotone-scan es (list group) 3 last)
               (let ((window (fn2-overview-probe-window es group mid hi)))
                 (or (atom window) (< p (nfix (nth 3 (car window)))))))
          (equal (fn2-range-seek-scan es (list group) 2 p hi 3 acc)
                 (fn2-range-seek-scan es (list group) 2 p mid 3 acc)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-overview-probe-prefix-induction es group mid hi p last acc)
          :in-theory (disable fn2-run-sorted-spec fn2-overview-probe-window fn2-overview-probe-side
                              fn2-range-seek-scan)
          :expand ((:free (prefix bound) (fn2-range-seek-scan es prefix 2 p bound 3 acc))
                   (:with fn2-overview-probe-window-step (fn2-overview-probe-window es group mid hi))))
         ("Subgoal *1/2" :cases ((eq (fn2-overview-probe-side (car es) group mid hi) :after)))
         ("Subgoal *1/2.1" :use (fn2-range-probe-past-both))
         ("Subgoal *1/2.2" :use ((:instance fn2-range-probe-over-position (bound hi))
                                 (:instance fn2-range-probe-over-position (bound mid))
                                 (:instance fn2-overview-probe-side-values (e (car es)))))))

; A qualifying first entry advances the lower bound past its number.
(defthm fn2-range-seek-lower-probe
 (implies (and (natp group) (natp mid) (integerp hi) (< mid hi)
               (fn2-range-natural-keysp es)
               (fn2-run-sorted-spec *fn2-overview-range-key* es)
               (let ((window (fn2-overview-probe-window es group mid hi)))
                 (and (consp window) (<= (nfix (nth 3 (car window))) p))))
          (< (cadr (car (fn2-overview-probe-window es group mid hi)))
             (fn2-range-seek-scan es (list group) 2 p hi 3 acc)))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-overview-probe-prefix-induction es group mid hi p last acc)
          :in-theory (disable fn2-run-sorted-spec fn2-overview-probe-window fn2-overview-probe-side
                              fn2-range-seek-scan)
          :expand ((:free (prefix bound) (fn2-range-seek-scan es prefix 2 p bound 3 acc))
                   (:with fn2-overview-probe-window-step (fn2-overview-probe-window es group mid hi))))
         ("Subgoal *1/2" :use (fn2-range-probe-at-position))))

(defthm fn2-overview-probe-first-key
 (implies (and (natp group) (natp mid) (integerp hi) (< mid hi)
               (fn2-range-natural-keysp es)
               (consp (fn2-overview-probe-window es group mid hi)))
          (let ((entry (car (fn2-overview-probe-window es group mid hi))))
            (and (equal (car entry) group) (natp (cadr entry))
                 (<= mid (cadr entry)) (< (cadr entry) hi))))
 :rule-classes nil
 :hints (("Goal" :induct (len es)
          :expand ((:with fn2-overview-probe-window-step (fn2-overview-probe-window es group mid hi)))
          :in-theory (disable fn2-overview-probe-side fn2-overview-probe-window))))
