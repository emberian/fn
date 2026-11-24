; The resident merge computes the same selection as the logical source lists.
(in-package "ACL2")
(include-book "range-head-pick-proof")
(include-book "range-union-head-proof")

(defun-nx fn2-overview-resident-head (s sources f pool)
  (and (fn2-overview-active-headp s sources)
       (list (fn2-run-unload-values *fn2-overview-entry* (fn2-overview-head-base s sources) f pool))))

; Every remaining active source is newer than a candidate already visited.
(defun-nx fn2-overview-newer-heads-p (n base prior sources)
  (if (zp n) t
    (let ((s (+ base (1- n))))
      (and (implies (and (natp prior) (fn2-overview-active-headp s sources))
                    (fn2-range-newer s prior sources))
           (fn2-overview-newer-heads-p (1- n) base prior sources)))))

; Enumeration visits streams from oldest to newest while counting down
; physical slots. Each head is the row at its own source's lower bound.
(defun-nx fn2-overview-supplied-source-heads-p (streams lo n base sources f pool)
  (if (zp n) (atom streams)
    (let ((s (+ base (1- n))))
      (and (consp streams)
           (equal (fn2-overview-source-head (car streams) lo)
                  (fn2-overview-resident-head s sources f pool))
           (fn2-overview-newer-heads-p (1- n) base s sources)
           (fn2-overview-supplied-source-heads-p (cdr streams) lo (1- n) base sources f pool)))))

(local
 (defthm fn2-overview-earlier-resident-head
   (let ((newer (fn2-overview-resident-head s sources f pool))
         (older (fn2-overview-resident-head best sources f pool)))
     (implies (and (or (not best) (fn2-overview-active-headp best sources))
                   (implies (and best (fn2-overview-active-headp s sources)) (fn2-range-newer s best sources)))
              (equal (fn2-overview-earlier-head older newer)
                     (fn2-overview-resident-head
                       (if (and (fn2-overview-active-headp s sources)
                                (or (not (natp best)) (fn2-overview-head-precedes s best sources f)))
                           s best)
                       sources f pool))))
   :hints (("Goal" :in-theory (disable nfix fn2-range-newer fn2-range-sources-rows
                             fn2-range-sources-state fn2-overview-head-base fn2-fields-value fn2-fields-ref-len
                             fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-slot fn2-run-read-bytes)))))

(local
 (defthm fn2-overview-supplied-index-natural
   (implies (fn2-overview-active-headp s sources) (natp s))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defun-nx fn2-overview-select-induct (streams lo n base best sources f pool)
   (declare (ignorable lo pool))
   (if (zp n) (list streams best)
     (let ((s (+ base (1- n))))
       (fn2-overview-select-induct (cdr streams) lo (1- n) base
         (if (and (fn2-overview-active-headp s sources)
                  (or (not (natp best)) (fn2-overview-head-precedes s best sources f)))
             s best)
         sources f pool)))))

(defthmd fn2-overview-resident-selection-matches-sources
  (implies (and (natp n) (natp base)
                (or (not best) (fn2-overview-active-headp best sources))
                (fn2-overview-newer-heads-p n base best sources)
                (fn2-overview-supplied-source-heads-p streams lo n base sources f pool))
           (equal (fn2-overview-resident-head (fn2-overview-best-head n base best sources f) sources f pool)
                  (fn2-overview-select-source-heads streams lo (fn2-overview-resident-head best sources f pool))))
  :hints (("Goal" :induct (fn2-overview-select-induct streams lo n base best sources f pool)
           :do-not '(preprocess)
           :expand ((fn2-overview-newer-heads-p n base best sources)
                    (fn2-overview-supplied-source-heads-p streams lo n base sources f pool)
                    (:free (b) (fn2-overview-select-source-heads streams lo b))
                    (:free (b) (fn2-overview-best-head n base b sources f)))
           :in-theory (disable fn2-overview-earlier-resident-head fn2-overview-earlier-head fn2-overview-source-head
                               fn2-overview-head-precedes fn2-range-newer fn2-overview-active-headp
                               fn2-overview-resident-head fn2-overview-best-head fn2-overview-select-source-heads))
          ("Subgoal *1/2" :use ((:instance fn2-overview-earlier-resident-head (s (+ base (1- n))))))))

(local
 (defthm fn2-overview-no-prior-to-compare
   (fn2-overview-newer-heads-p n base nil sources)
   :hints (("Goal" :induct (fn2-overview-newer-heads-p n base nil sources)))))

(local
 (defthm fn2-overview-no-prior-resident-head
   (equal (fn2-overview-resident-head nil sources f pool) nil)))

(defthmd fn2-overview-winning-row-from-sources
  (implies (and (natp n) (natp base)
                (fn2-overview-supplied-source-heads-p streams lo n base sources f pool))
           (equal (fn2-overview-resident-head (fn2-overview-best-head n base nil sources f) sources f pool)
                  (fn2-overview-select-source-heads streams lo nil)))
  :hints (("Goal" :use ((:instance fn2-overview-resident-selection-matches-sources (best nil)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn2-overview-no-prior-to-compare fn2-overview-no-prior-resident-head)))))
