(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-fps-other-slot-rows-loop (rows row acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-fps-other-slot-rows-loop
       (cdr rows) row
       (if (and (fn-fps-slot-rowp (car rows)) (not (equal (car rows) row)))
           (cons (car rows) acc)
         acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-fps-other-slot-rows (rows row)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (if (and (fn-fps-slot-rowp (car rows)) (not (equal (car rows) row)))
                      (cons (car rows) (fn-fps-other-slot-rows (cdr rows) row))
                    (fn-fps-other-slot-rows (cdr rows) row))
                nil)
       :exec (fn-fps-other-slot-rows-loop rows row nil)))

(defthm fn-fps-other-slot-rows-loop-is-rev-onto
  (equal (fn-fps-other-slot-rows-loop rows row acc)
         (fn-ag-rev-onto acc (fn-fps-other-slot-rows rows row)))
  :hints (("Goal" :induct (fn-fps-other-slot-rows-loop rows row acc)
                  :in-theory (union-theories
                              '(fn-fps-other-slot-rows-loop fn-fps-other-slot-rows
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-fps-other-slot-rows
  :hints (("Goal" :in-theory (union-theories
                              '(fn-fps-other-slot-rows fn-ag-rev-onto
                                fn-fps-other-slot-rows-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-fps-live-names-loop (names peers acc)
  (declare (xargs :guard t))
  (if (consp names)
      (fn-fps-live-names-loop
       (cdr names) peers
       (if (fn-fps-pausedp (car names) peers) acc (cons (car names) acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-fps-live-names (names peers)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp names)
                  (if (fn-fps-pausedp (car names) peers)
                      (fn-fps-live-names (cdr names) peers)
                    (cons (car names) (fn-fps-live-names (cdr names) peers)))
                nil)
       :exec (fn-fps-live-names-loop names peers nil)))

(defthm fn-fps-live-names-loop-is-rev-onto
  (equal (fn-fps-live-names-loop names peers acc)
         (fn-ag-rev-onto acc (fn-fps-live-names names peers)))
  :hints (("Goal" :induct (fn-fps-live-names-loop names peers acc)
                  :in-theory (union-theories
                              '(fn-fps-live-names-loop fn-fps-live-names
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-fps-live-names
  :hints (("Goal" :in-theory (union-theories
                              '(fn-fps-live-names fn-ag-rev-onto
                                fn-fps-live-names-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

