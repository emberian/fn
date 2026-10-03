; Captured-view group summary, one numbered metadata probe per accepted step.
; No group-sized number list or changing live-summary read in execution.
; Snapshot/column stability and integer/metadata lookup tariffs are separate.
(in-package "ACL2")
(include-book "catalog-available-readers")
(include-book "def-cursor")

(local (in-theory (disable (tau-system) fn-scv-keptp)))

(defun fn-gsc-at (n cur)
  (declare (xargs :guard (natp n)))
  (fn-cur-at n cur))

; Fields: tag group scan-high captured-next captured-v next-number count low last.
(defun fn-gsc-start (group high next v)
  (declare (xargs :guard t))
  (list :group-summary group (nfix high) (nfix next) (nfix v) 1 0 0 0))

(defun fn-gsc-remaining (cur)
  (declare (xargs :guard t))
  (nfix (- (+ 1 (nfix (fn-gsc-at 2 cur))) (nfix (fn-gsc-at 5 cur)))))

(defun fn-gsc-one (cur fn-cat)
  (declare (xargs :stobjs fn-cat :guard t))
  (let ((high (nfix (fn-gsc-at 2 cur)))
        (k (nfix (fn-gsc-at 5 cur)))
        (v (nfix (fn-gsc-at 4 cur)))
        (count (nfix (fn-gsc-at 6 cur)))
        (low (nfix (fn-gsc-at 7 cur)))
        (last (nfix (fn-gsc-at 8 cur))))
    (if (< high k) cur
      (let ((kept (fn-scv-keptp (fn-gsc-at 1 cur) k v fn-cat)))
        (list :group-summary (fn-gsc-at 1 cur) high (nfix (fn-gsc-at 3 cur)) v
              (+ 1 k) (if kept (+ 1 count) count)
              (if (and kept (zp low)) k low) (if kept k last))))))

(defun fn-gsc-summary (cur)
  (declare (xargs :guard t))
  (let ((count (nfix (fn-gsc-at 6 cur)))
        (next (nfix (fn-gsc-at 3 cur))))
    (if (posp count)
        (list count (nfix (fn-gsc-at 7 cur)) (nfix (fn-gsc-at 8 cur)))
      (list 0 next (if (posp next) (- next 1) 0)))))

; Disabled logical reference: completing the remaining number sequence adds
; its count and endpoints to the already retained scalar summary. Never served.
(defun-nx fn-gsc-fold-reference (group high next v k count low last fn-cat)
  (let* ((numbers (fn-scat-available-numbers group k high v fn-cat))
         (total (+ count (len numbers)))
         (first (if (posp low) low (if (consp numbers) (car numbers) 0)))
         (final (if (consp numbers) (fn-scat-available-last numbers) last)))
    (if (posp total) (list total first final)
      (list 0 next (if (posp next) (- next 1) 0)))))

(defun-nx fn-gsc-reference (cur fn-cat)
  (fn-gsc-fold-reference
   (fn-gsc-at 1 cur) (nfix (fn-gsc-at 2 cur)) (nfix (fn-gsc-at 3 cur))
   (nfix (fn-gsc-at 4 cur)) (nfix (fn-gsc-at 5 cur))
   (nfix (fn-gsc-at 6 cur)) (nfix (fn-gsc-at 7 cur))
   (nfix (fn-gsc-at 8 cur)) fn-cat))

(defun fn-gsc-statep (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (equal (len cur) 9)
       (equal (fn-gsc-at 0 cur) :group-summary)
       (natp (fn-gsc-at 2 cur)) (natp (fn-gsc-at 3 cur))
       (natp (fn-gsc-at 4 cur)) (posp (fn-gsc-at 5 cur))
       (natp (fn-gsc-at 6 cur)) (natp (fn-gsc-at 7 cur))
       (natp (fn-gsc-at 8 cur))))

(local (in-theory (enable fn-gsc-at fn-cur-at)))

(defthm fn-gsc-start-statep
  (fn-gsc-statep (fn-gsc-start group high next v)))

(defthm fn-gsc-one-keeps-statep
  (implies (fn-gsc-statep cur) (fn-gsc-statep (fn-gsc-one cur fn-cat))))

(defthm fn-gsc-one-progress
  (implies (posp (fn-gsc-remaining cur))
           (equal (fn-gsc-remaining (fn-gsc-one cur fn-cat))
                  (- (fn-gsc-remaining cur) 1))))

(defthm fn-gsc-done-is-unchanged
  (implies (zp (fn-gsc-remaining cur))
           (equal (fn-gsc-one cur fn-cat) cur)))

(defthm fn-gsc-start-remaining
  (equal (fn-gsc-remaining (fn-gsc-start group high next v)) (nfix high)))

; Shape bounds retained state/new constructor cells; this is not a heap tariff.
(defthm fn-gsc-one-fixed-envelope
  (implies (fn-gsc-statep cur)
           (equal (len (fn-gsc-one cur fn-cat)) 9)))

(local
 (defthm fn-gsc-kept-is-positive
   (implies (fn-scv-keptp group k v fn-cat) (posp k))
   :hints (("Goal" :in-theory '(fn-scv-keptp)))))

(local
 (defthm fn-gsc-numbers-proper
   (true-listp (fn-scat-available-numbers group k high v fn-cat))
   :hints (("Goal" :induct (fn-scat-available-numbers group k high v fn-cat)
            :in-theory (e/d (fn-scat-available-numbers) (fn-scv-keptp))))))

(local
 (defthm fn-gsc-fold-one
   (implies (and (natp high) (natp next) (natp v) (natp k)
                 (natp count) (natp low) (natp last) (<= k high))
    (equal
     (fn-gsc-fold-reference group high next v (+ 1 k)
       (if (fn-scv-keptp group k v fn-cat) (+ 1 count) count)
       (if (and (fn-scv-keptp group k v fn-cat) (zp low)) k low)
       (if (fn-scv-keptp group k v fn-cat) k last) fn-cat)
     (fn-gsc-fold-reference group high next v k count low last fn-cat)))
   :hints (("Goal" :in-theory
            (e/d (fn-gsc-fold-reference fn-scat-available-last)
                 (fn-scv-keptp fn-scat-available-numbers
                  fn-scat-available-numbers-count fn-scat-available-numbers-first
                  fn-scat-available-numbers-last))
            :expand ((fn-scat-available-numbers group k high v fn-cat))))))

(local (defthm fn-gsc-nfix-twice
         (equal (nfix (nfix x)) (nfix x))
         :hints (("Goal" :in-theory '(nfix)))))
(local (defthm fn-gsc-nfix-successor
         (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x)))
         :hints (("Goal" :in-theory '(nfix)))))

(defthm fn-gsc-one-preserves-reference
  (equal (fn-gsc-reference (fn-gsc-one cur fn-cat) fn-cat)
         (fn-gsc-reference cur fn-cat))
  :hints (("Goal" :in-theory
           (e/d (fn-gsc-reference fn-gsc-one fn-gsc-at fn-cur-at)
                (fn-scv-keptp fn-gsc-fold-reference nfix))
           :use ((:instance fn-gsc-fold-one
                    (group (fn-gsc-at 1 cur)) (high (nfix (fn-gsc-at 2 cur)))
                    (next (nfix (fn-gsc-at 3 cur))) (v (nfix (fn-gsc-at 4 cur)))
                    (k (nfix (fn-gsc-at 5 cur))) (count (nfix (fn-gsc-at 6 cur)))
                    (low (nfix (fn-gsc-at 7 cur))) (last (nfix (fn-gsc-at 8 cur))))))))

(local (defthm fn-gsc-numbers-after-high
   (implies (< high k)
            (equal (fn-scat-available-numbers group k high v fn-cat) nil))
   :hints (("Goal" :in-theory (union-theories '(fn-scat-available-numbers)
                                             (theory 'minimal-theory))))))

(defthm fn-gsc-terminal-reference
  (implies (zp (fn-gsc-remaining cur))
           (equal (fn-gsc-reference cur fn-cat) (fn-gsc-summary cur)))
  :hints (("Goal" :in-theory
           (e/d (fn-gsc-reference fn-gsc-fold-reference fn-gsc-remaining fn-gsc-summary
                 fn-gsc-at fn-cur-at fn-scat-available-numbers)
                (fn-scv-keptp fn-scat-available-numbers-count
                 fn-scat-available-numbers-first fn-scat-available-numbers-last)))))

(in-theory (disable fn-gsc-reference fn-gsc-fold-reference fn-gsc-statep fn-gsc-start fn-gsc-one
                    fn-gsc-summary fn-gsc-remaining fn-gsc-at))
