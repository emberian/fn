; Digest microbenchmark: 32 KiB through the list model and the stobj, and the
; string entry, in one ACL2 session over the certified books.  Each figure is
; time$'s wall and bytes allocated for 200 digests; the per-digest numbers are
; the quotients.  Run on hbox only, under a memory cap (bench.sh).
(include-book "/tank/fn/scratch/rep-sha256/after-tree/books/sha256-stobj")
(include-book "/tank/fn/scratch/rep-sha256/after-tree/books/crypto-attach")
(defun bench-repeat (n x) (declare (xargs :guard t :measure (nfix n))) (let ((n (nfix n))) (if (zp n) nil (cons x (bench-repeat (- n 1) x)))))
(defconst *m32k* (bench-repeat 32768 97))
(defconst *s32k* (coerce (make-list 32768 :initial-element #\a) 'string))
; Each loop tests the digest it computed, so the message is a relevant formal.
(defun bench-list-model (n m) (declare (xargs :guard t :measure (nfix n))) (let ((n (nfix n))) (if (zp n) nil (if (fn-sha256 m) (bench-list-model (- n 1) m) :no))))
(defun bench-stobj (n m) (declare (xargs :guard t :measure (nfix n))) (let ((n (nfix n))) (if (zp n) nil (if (fn-sha256-stobj m) (bench-stobj (- n 1) m) :no))))
(defun bench-string (n s) (declare (xargs :guard (stringp s) :measure (nfix n))) (let ((n (nfix n))) (if (zp n) nil (if (fn-sha256-of-string s) (bench-string (- n 1) s) :no))))
(defun bench-attached (n m) (declare (xargs :guard t :measure (nfix n))) (let ((n (nfix n))) (if (zp n) nil (if (fn-digest m) (bench-attached (- n 1) m) :no))))
; agreement first
(assert-event (equal (fn-sha256 *m32k*) (fn-sha256-stobj *m32k*)))
(assert-event (equal (fn-sha256 *m32k*) (fn-sha256-of-string *s32k*)))
(assert-event (equal (fn-sha256 *m32k*) (fn-digest *m32k*)))
; warm
(bench-stobj 5 *m32k*)
(bench-list-model 5 *m32k*)
(cw "~%BENCH list-model 200 x 32KiB~%")
(time$ (bench-list-model 200 *m32k*) :msg "list-model: ~st s real, ~sc s cpu, ~sa bytes~%")
(cw "~%BENCH stobj 200 x 32KiB~%")
(time$ (bench-stobj 200 *m32k*) :msg "stobj: ~st s real, ~sc s cpu, ~sa bytes~%")
(cw "~%BENCH string 200 x 32KiB~%")
(time$ (bench-string 200 *s32k*) :msg "string: ~st s real, ~sc s cpu, ~sa bytes~%")
(cw "~%BENCH attached fn-digest 200 x 32KiB~%")
(time$ (bench-attached 200 *m32k*) :msg "attached: ~st s real, ~sc s cpu, ~sa bytes~%")
; and again, to see variance
(time$ (bench-list-model 200 *m32k*) :msg "list-model: ~st s real, ~sc s cpu, ~sa bytes~%")
(time$ (bench-stobj 200 *m32k*) :msg "stobj: ~st s real, ~sc s cpu, ~sa bytes~%")
(time$ (bench-string 200 *s32k*) :msg "string: ~st s real, ~sc s cpu, ~sa bytes~%")
(cw "~%BENCH-DONE~%")
