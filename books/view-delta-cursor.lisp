; Resumable persistent-trie aggregate delta. PRF-1192 / SCN-1072.
; Each step reads one sibling or rebuilds one cell, never a whole key/path.
(in-package "ACL2")
(include-book "view-delta")

(defun fn-vcu-car (x)
 (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-vcu-cdr (x)
 (declare (xargs :guard t)) (if (consp x) (cdr x) nil))

(defun fn-vcu-at (n x)
 (declare (xargs :guard (natp n)))
 (if (zp n) (fn-vcu-car x) (fn-vcu-at (1- n) (fn-vcu-cdr x))))

; phase, borrowed string, offset, sibling tail, reversed sibling prefix,
; parent frames, rebuilt result, retained weight, release flag.
(defun fn-vcu-c (phase key offset tail prefix parents result weight release)
 (declare (xargs :guard t))
 (list phase key offset tail prefix parents result weight release))

(defun fn-vcu-pair (old weight release)
 (declare (xargs :guard t))
 (let* ((old (if (fn-vd-pairp old) old *fn-vd-zero*))
        (count (nfix (fn-vcu-car old))) (sum (nfix (fn-vcu-cdr old))))
  (if release
   (if (<= count 1) *fn-vd-zero*
    (cons (1- count) (nfix (- sum (nfix weight)))))
   (cons (+ 1 count) (+ sum (nfix weight))))))

(defun fn-vcu-begin (key weight release trie)
 (declare (xargs :guard t))
 (fn-vcu-c (if (stringp key) :scan :done) key 0 trie nil nil trie
           (nfix weight) (if release t nil)))

(defun fn-vcu-step (c)
 (declare (xargs :guard t))
 (let* ((phase (fn-vcu-at 0 c)) (key (fn-vcu-at 1 c))
        (i (nfix (fn-vcu-at 2 c))) (tail (fn-vcu-at 3 c))
        (prefix (fn-vcu-at 4 c)) (parents (fn-vcu-at 5 c))
        (result (fn-vcu-at 6 c)) (weight (fn-vcu-at 7 c))
        (release (fn-vcu-at 8 c)))
  (cond
   ((eq phase :scan)
    (if (not (stringp key)) c
     (let* ((down (< i (length key)))
            (wanted (if down (char key i) :fn-midx-value))
            (entry (fn-vcu-car tail))
            (found (and (consp tail) (equal wanted (fn-vcu-car entry)))))
      (if (and (consp tail) (not found))
       (fn-vcu-c :scan key i (cdr tail) (cons entry prefix) parents result weight release)
       (let ((suffix (if found (fn-vcu-cdr tail) nil))
             (old (if found (fn-vcu-cdr entry) nil)))
        (if down
         (fn-vcu-c :scan key (+ 1 i) old nil
                    (cons (list wanted prefix suffix) parents) result weight release)
         (fn-vcu-c :rebuild key i nil prefix parents
                    (cons (cons wanted (fn-vcu-pair old weight release)) suffix)
                    weight release)))))))
   ((eq phase :rebuild)
    (cond ((consp prefix)
           (fn-vcu-c :rebuild key i nil (cdr prefix) parents
                      (cons (car prefix) result) weight release))
          ((consp parents)
           (let ((frame (car parents)))
            (fn-vcu-c :rebuild key i nil (fn-vcu-at 1 frame) (cdr parents)
                       (cons (cons (fn-vcu-at 0 frame) result) (fn-vcu-at 2 frame))
                       weight release)))
          (t (fn-vcu-c :done key i nil nil nil result weight release))))
   (t c))))

(defun fn-vcu-drive (c fuel)
 (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
 (if (or (zp fuel) (eq (fn-vcu-at 0 c) :done)) (mv c 0)
  (mv-let (next used) (fn-vcu-drive (fn-vcu-step c) (1- fuel))
   (mv next (+ 1 (nfix used))))))

(defun fn-vcu-result (c)
 (declare (xargs :guard t))
 (if (eq (fn-vcu-at 0 c) :done) (list :done (fn-vcu-at 6 c)) nil))

(defthm fn-vcu-drive-work-bound
 (<= (mv-nth 1 (fn-vcu-drive c fuel)) (nfix fuel))
 :hints (("Goal" :induct (fn-vcu-drive c fuel)
          :in-theory (disable fn-vcu-step fn-vcu-at))))

(defthm fn-vcu-done-stable
 (implies (eq (fn-vcu-at 0 c) :done)
  (and (equal (mv-nth 0 (fn-vcu-drive c fuel)) c)
       (equal (mv-nth 1 (fn-vcu-drive c fuel)) 0))))
