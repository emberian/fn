; Before a seal the active overlay has a source slot even when empty.
; Afterwards only nonempty runs have slots. Both enumerate the same union.
(in-package "ACL2")
(include-book "range")

(defun fn2-range-visible-streams (streams active-overlay)
  (declare (xargs :guard t))
  (cond ((atom streams) nil)
        ((or (consp (car streams)) (and active-overlay (atom (cdr streams))))
         (cons (car streams) (fn2-range-visible-streams (cdr streams) active-overlay)))
        (t (fn2-range-visible-streams (cdr streams) active-overlay))))

(defthm fn2-range-visible-streams-union
  (equal (fn2-range-union-spec key (fn2-range-visible-streams streams active-overlay) acc)
         (fn2-range-union-spec key streams acc))
  :hints (("Goal" :induct (fn2-range-union-spec key streams acc)
           :expand ((fn2-range-visible-streams streams active-overlay))
           :in-theory (disable fn2-range-put-spec))))

(defthm fn2-range-visible-streams-admitted
  (implies (fn2-range-listsp layout key streams)
           (fn2-range-listsp layout key (fn2-range-visible-streams streams active-overlay)))
  :hints (("Goal" :induct (fn2-range-visible-streams streams active-overlay)
           :in-theory (disable fn2-run-sorted-spec fn2-run-entries-layoutp))))

(defthm fn2-range-visible-streams-window
  (equal (fn2-range-spec key (fn2-range-visible-streams streams active-overlay) lo hi pidx limit)
         (fn2-range-spec key streams lo hi pidx limit))
  :hints (("Goal" :in-theory (e/d (fn2-range-spec) (fn2-range-union-spec fn2-range-window-spec)))))

(defthm fn2-range-visible-streams-seek
  (equal (fn2-range-seek-spec key (fn2-range-visible-streams streams active-overlay) prefix p hi pidx)
         (fn2-range-seek-spec key streams prefix p hi pidx))
  :hints (("Goal" :in-theory (e/d (fn2-range-seek-spec) (fn2-range-union-spec fn2-range-seek-scan)))))
