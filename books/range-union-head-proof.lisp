; The first qualifying row of the union can be selected one source at a time.
(in-package "ACL2")
(include-book "range-union-proof")

; A singleton keeps the row distinct from the absence of a candidate.
(defun-nx fn2-overview-source-head (rows lo)
  (cond ((atom rows) nil)
        ((eq (fn2-run-key-order-spec *fn2-overview-range-key* (car rows) lo) :lt)
         (fn2-overview-source-head (cdr rows) lo))
        (t (list (car rows)))))

(defun-nx fn2-overview-earlier-head (older newer)
  (cond ((atom newer) older)
        ((atom older) newer)
        ((eq (fn2-run-key-order-spec *fn2-overview-range-key* (car older) (car newer)) :lt) older)
        (t newer)))

(local
 (defthm fn2-overview-head-of-insert
   (equal (fn2-overview-source-head (fn2-range-put-spec *fn2-overview-range-key* e acc) lo)
          (fn2-overview-earlier-head (fn2-overview-source-head acc lo)
                                     (fn2-overview-source-head (list e) lo)))
   :hints (("Goal" :induct (fn2-range-put-spec *fn2-overview-range-key* e acc)
            :in-theory (disable nfix)))))

(local
 (defthm fn2-overview-earlier-head-associative
   (equal (fn2-overview-earlier-head (fn2-overview-earlier-head a b) c)
          (fn2-overview-earlier-head a (fn2-overview-earlier-head b c)))
   :hints (("Goal" :in-theory (disable nfix)))))

(local
 (defthm fn2-overview-head-precedes-sorted-tail
   (implies (and (fn2-run-sorted-spec *fn2-overview-range-key* (cons a rows))
                 (not (eq (fn2-run-key-order-spec *fn2-overview-range-key* a lo) :lt)))
            (equal (fn2-overview-earlier-head (list a) (fn2-overview-source-head rows lo))
                   (list a)))
   :hints (("Goal" :expand ((fn2-overview-source-head rows lo))
            :in-theory (disable nfix)))))

(local
 (defthm fn2-overview-no-older-head
   (equal (fn2-overview-earlier-head nil (fn2-overview-source-head rows lo)) (fn2-overview-source-head rows lo))
   :hints (("Goal" :in-theory (disable fn2-run-key-order-spec)))))

(local
 (defthm fn2-overview-source-head-as-selection
   (implies (and (consp rows) (fn2-run-sorted-spec *fn2-overview-range-key* rows))
            (equal (fn2-overview-earlier-head (fn2-overview-source-head (list (car rows)) lo)
                                              (fn2-overview-source-head (cdr rows) lo))
                   (fn2-overview-source-head rows lo)))
   :hints (("Goal" :do-not-induct t :use ((:instance fn2-overview-head-precedes-sorted-tail
                                    (a (car rows)) (rows (cdr rows))))
            :expand ((fn2-overview-source-head nil lo) (fn2-overview-source-head rows lo)
                     (fn2-overview-source-head (list (car rows)) lo))
            :in-theory (disable fn2-run-key-order-spec fn2-overview-earlier-head fn2-overview-source-head fn2-run-sorted-spec
                                fn2-overview-head-precedes-sorted-tail)))))

(local
 (defthm fn2-overview-head-of-inserts
   (implies (fn2-run-sorted-spec *fn2-overview-range-key* es)
            (equal (fn2-overview-source-head (fn2-range-puts-spec *fn2-overview-range-key* es acc) lo)
                   (fn2-overview-earlier-head (fn2-overview-source-head acc lo)
                                              (fn2-overview-source-head es lo))))
   :hints (("Goal" :induct (fn2-range-puts-spec *fn2-overview-range-key* es acc)
            :in-theory (disable fn2-range-put-spec fn2-run-key-order-spec fn2-overview-earlier-head
                                fn2-overview-source-head))
           ("Subgoal *1/1" :in-theory (enable fn2-overview-source-head fn2-overview-earlier-head)))))

(defun-nx fn2-overview-select-source-heads (sources lo best)
  (if (atom sources) best
    (fn2-overview-select-source-heads (cdr sources) lo
      (fn2-overview-earlier-head best (fn2-overview-source-head (car sources) lo)))))

(defthmd fn2-overview-union-head-from-sources
  (implies (fn2-range-listsp layout *fn2-overview-range-key* sources)
           (equal (fn2-overview-source-head (fn2-range-union-spec *fn2-overview-range-key* sources acc) lo)
                  (fn2-overview-select-source-heads sources lo (fn2-overview-source-head acc lo))))
  :hints (("Goal" :induct (fn2-range-union-spec *fn2-overview-range-key* sources acc)
           :expand ((:free (best) (fn2-overview-select-source-heads sources lo best)))
           :in-theory (disable fn2-run-sorted-spec fn2-run-entries-layoutp fn2-range-puts-spec
                               fn2-overview-earlier-head fn2-overview-source-head))))

(local
 (defthm fn2-overview-lower-bound-not-before-start
   (implies (natp start)
            (let ((i (cadr (fn2-run-lower-bound-spec key rows lo start))))
              (and (integerp i) (<= start i))))
   :rule-classes (:rewrite (:linear :corollary (implies (natp start) (<= start (cadr (fn2-run-lower-bound-spec key rows lo start))))))
   :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows lo start)
            :in-theory (disable fn2-run-key-order-spec)))))

(defthmd fn2-overview-source-head-at-lower-bound
  (let* ((bound (fn2-run-lower-bound-spec *fn2-overview-range-key* rows lo start))
         (offset (- (cadr bound) start)))
    (implies (natp start)
             (equal (fn2-overview-source-head rows lo)
                    (if (< offset (len rows)) (list (nth offset rows)) nil))))
  :hints (("Goal" :induct (fn2-run-lower-bound-spec *fn2-overview-range-key* rows lo start)
           :expand ((fn2-overview-source-head rows lo))
           :in-theory (disable fn2-run-key-order-spec))))

(local
 (defthm fn2-overview-window-head-from-lower-bound
   (let* ((key *fn2-overview-range-key*) (head (fn2-overview-source-head rows lo))
          (row (car head)) (window (fn2-range-window-spec key rows lo hi pidx plimit)))
     (equal (if (consp window) (list (car window)) nil)
            (if (or (atom head) (eq (fn2-run-key-order-spec key row hi) :gt)
                    (and (natp pidx) (< (nfix plimit) (nfix (nth pidx row)))))
                nil head)))
   :hints (("Goal" :induct (fn2-overview-source-head rows lo)
            :in-theory (disable fn2-run-key-order-spec)))))

(defthmd fn2-overview-window-head-from-sources
  (let* ((key *fn2-overview-range-key*) (head (fn2-overview-select-source-heads sources lo nil))
         (row (car head)) (window (fn2-range-spec key sources lo hi pidx plimit)))
    (implies (fn2-range-listsp layout key sources)
             (equal (if (consp window) (list (car window)) nil)
                    (if (or (atom head) (eq (fn2-run-key-order-spec key row hi) :gt)
                            (and (natp pidx) (< (nfix plimit) (nfix (nth pidx row)))))
                        nil head))))
  :hints (("Goal" :use ((:instance fn2-overview-window-head-from-lower-bound
                          (rows (fn2-range-union-spec *fn2-overview-range-key* sources nil)))
                        (:instance fn2-overview-union-head-from-sources (acc nil)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-range-spec fn2-overview-source-head (:e consp) (:e car) eq)))))
