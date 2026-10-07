(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-lzr-intern-events-loop (ws zs ps dicts keyring generation acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-lzr-dictsp dicts) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-lzr-intern-event)))))
  (if (atom ws)
      (mv (fn-ag-rev-onto acc nil) fn-arena)
    (let* ((z (and (consp zs) (car zs)))
           (p (and (consp ps) (consp (car ps)) (car ps)))
           (file (nfix (and (consp p) (car p))))
           (position (and (consp p) (cdr p))))
      (mv-let (row fn-arena)
        (fn-lzr-intern-event (car ws) z position file dicts keyring generation fn-arena)
        (if (eq row :bad)
            (mv :bad fn-arena)
          (fn-lzr-intern-events-loop (cdr ws) (and (consp zs) (cdr zs)) (and (consp ps) (cdr ps))
                                     dicts keyring generation (cons row acc) fn-arena))))))

(defun fn-lzr-intern-events (ws zs ps dicts keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-lzr-dictsp dicts) (fn-prin-keyringp keyring) (natp generation))
                  :verify-guards nil))
  (mbe :logic
  (if (atom ws)
      (mv nil fn-arena)
    (let* ((z (and (consp zs) (car zs)))
           (p (and (consp ps) (consp (car ps)) (car ps)))
           (file (nfix (and (consp p) (car p))))
           (position (and (consp p) (cdr p))))
      (mv-let (row fn-arena)
        (fn-lzr-intern-event (car ws) z position file dicts keyring generation fn-arena)
        (if (eq row :bad)
            (mv :bad fn-arena)
          (mv-let (rest fn-arena)
            (fn-lzr-intern-events (cdr ws) (and (consp zs) (cdr zs)) (and (consp ps) (cdr ps))
                                  dicts keyring generation fn-arena)
            (if (eq rest :bad)
                (mv :bad fn-arena)
              (mv (cons row rest) fn-arena)))))))
  :exec (fn-lzr-intern-events-loop ws zs ps dicts keyring generation nil fn-arena)))

(defthm fn-lzr-intern-events-loop-is-rev-onto
  (equal (fn-lzr-intern-events-loop ws zs ps dicts keyring generation acc fn-arena)
         (mv-let (r a) (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           (mv (if (eq r :bad) :bad (fn-ag-rev-onto acc r)) a)))
  :hints (("Goal" :induct (fn-lzr-intern-events-loop ws zs ps dicts keyring generation acc
                                                     fn-arena)
                  :do-not '(generalize fertilize eliminate-destructors)
                  :in-theory (disable fn-lzr-intern-event nfix))))

(verify-guards fn-lzr-intern-events
  :hints (("Goal" :in-theory (disable fn-lzr-intern-event))))

(defthm fn-lzr-intern-events-true-listp
  (or (true-listp (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)))
      (equal (mv-nth 0 (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)) :bad))
  :rule-classes nil
  :hints (("Goal" :induct (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           :in-theory (disable fn-lzr-intern-event))))

(defun fn-lzr-intern-step (acc ws zs ps dicts fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-lzr-dictsp dicts)
                  :guard-hints (("Goal" :use ((:instance fn-lzr-intern-events-true-listp
                                                 (keyring nil) (generation 0)))
                                 :in-theory (disable fn-lzr-intern-events)))))
  (if (or (eq acc :bad) (eq ws :bad))
      (mv :bad fn-arena)
    (mv-let (rows fn-arena)
      (fn-lzr-intern-events ws zs ps dicts nil 0 fn-arena)
      (if (eq rows :bad)
          (mv :bad fn-arena)
        (mv (revappend rows acc) fn-arena)))))

(defthm fn-lzr-intern-events-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p zs ps))
           (equal (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
                  (fn-intern-events ws keyring generation fn-arena)))
  :hints (("Goal" :induct (fn-lzr-intern-events ws zs ps dicts keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-lzr-intern-event fn-intern-event fn-intern-event-arena)))))

(defthm fn-lzr-intern-step-refines
  (implies (and (fn-arena-p fn-arena)
                (fn-arx-faithful-p zs ps))
           (equal (fn-lzr-intern-step acc ws zs ps dicts fn-arena)
                  (fn-srs-intern-step acc ws fn-arena)))
  :hints (("Goal" :in-theory (disable fn-lzr-intern-events fn-intern-events))))
