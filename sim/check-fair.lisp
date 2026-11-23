; FAIR checker (EXECUTION-MODEL.md rules 4 & 10): live scheduler calendar
; starvation bound (L visits), intrusive per-principal FIFO integrity (pop-head
; readiness), timer-readiness non-starvation, bounded-readiness trace checking,
; and PV resource deadlock checking (check-deadlock.lisp).
(in-package "ACL2")
(include-book "../books/sched")
(include-book "check-deadlock")

(defun fn2-fair-resultp (res)
  (declare (xargs :guard t))
  (or (eq res :pass)
      (and (consp res) (eq (car res) :fail) (consp (cdr res)))))
(defthm fn2-fair-resultp-pass (fn2-fair-resultp :pass))
(defthm fn2-fair-resultp-fail (implies (consp rest) (fn2-fair-resultp (cons :fail rest))))
(in-theory (disable fn2-fair-resultp))

;; 1. Calendar weight recovery and validity over fn2-sched (guard-verified).

(defun fn2-fair-ones (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 1 (fn2-fair-ones (- n 1)))))
(local (defthm fn2-fair-ones-len
         (implies (natp n) (equal (len (fn2-fair-ones n)) n))))

(defun fn2-fair-calendar-count (i len slot fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix len) (nfix i)))
                  :guard (and (natp i) (natp len)
                              (<= len (fn2-sched-calendar-length fn2-sched)) (natp slot))))
  (if (or (not (natp i)) (not (natp len)) (>= i len)) 0
    (+ (if (equal (fn2-sched-calendari i fn2-sched) slot) 1 0)
       (fn2-fair-calendar-count (+ 1 i) len slot fn2-sched))))

(defun fn2-fair-calendar-weights-aux (slot p len fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix p) (nfix slot)))
                  :guard (and (natp slot) (natp p) (natp len)
                              (<= len (fn2-sched-calendar-length fn2-sched)))))
  (if (or (not (natp slot)) (not (natp p)) (>= slot p)) nil
    (cons (fn2-fair-calendar-count 0 len slot fn2-sched)
          (fn2-fair-calendar-weights-aux (+ 1 slot) p len fn2-sched))))
(local (defthm fn2-fair-calendar-weights-aux-len
         (implies (and (natp slot) (natp p) (<= slot p))
                  (equal (len (fn2-fair-calendar-weights-aux slot p len fn2-sched)) (- p slot)))))

(defun fn2-fair-sched-weights (fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (let ((p (fn2-sched-nprincipals fn2-sched))
        (len (fn2-sched-calendar-length fn2-sched)))
    (if (<= len *fn2-sched-weighted-calendar-max*)
        (fn2-fair-calendar-weights-aux 0 p len fn2-sched)
      (fn2-fair-ones p))))
(defthm fn2-fair-sched-weights-len
  (implies (fn2-schedp fn2-sched)
           (equal (len (fn2-fair-sched-weights fn2-sched)) (fn2-sched-nprincipals fn2-sched))))

(defun fn2-fair-calendar-matchp (codes i fn2-sched)
  (declare (xargs :stobjs fn2-sched
                  :guard (and (true-listp codes) (natp i)
                              (<= (+ i (len codes)) (fn2-sched-calendar-length fn2-sched)))))
  (if (atom codes) t
    (and (< i (fn2-sched-calendar-length fn2-sched))
         (equal (fn2-sched-calendari i fn2-sched) (car codes))
         (fn2-fair-calendar-matchp (cdr codes) (+ i 1) fn2-sched))))
(defthm fn2-fair-calendar-matchp-implies-sched
  (implies (and (fn2-fair-calendar-matchp codes i fn2-sched) (natp i))
           (fn2-sched-calendar-matchp codes i fn2-sched)))

(defun fn2-fair-calendar-validp (weights fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (true-listp weights)))
  (let ((codes (fn2-sched-calendar-list weights)))
    (and (fn2-sched-weightsp weights)
         (equal (len weights) (fn2-sched-nprincipals fn2-sched))
         (equal (fn2-sched-calendar-length fn2-sched) (len codes))
         (fn2-fair-calendar-matchp codes 0 fn2-sched))))
(defthm fn2-fair-calendar-validp-implies-sched
  (implies (fn2-fair-calendar-validp weights fn2-sched)
           (fn2-sched-calendar-validp weights fn2-sched)))

;; 2. Intrusive FIFO & timer-readiness integrity (guard-verified).

(defun fn2-fair-fifo-walk (cur prev left tail p rows fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix left)
                  :guard (and (fn2-sched-wfp fn2-sched) (natp cur) (natp prev)
                              (posp left) (natp tail) (natp p)
                              (equal rows (fn2-sched-rows fn2-sched)))))
  (and (posp left) (natp cur) (natp rows) (< cur rows)
       (= (fn2-sched-in-queue cur fn2-sched) 1)
       (= (fn2-sched-principal cur fn2-sched) p)
       (= (fn2-sched-prev cur fn2-sched) prev)
       (if (= left 1)
           (and (= cur tail) (= (fn2-sched-next cur fn2-sched) *fn2-none*))
         (fn2-fair-fifo-walk (fn2-sched-next cur fn2-sched) cur (- left 1) tail p rows fn2-sched))))

(defun fn2-fair-fifos-validp (slot p rows fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix p) (nfix slot)))
                  :guard (and (fn2-sched-wfp fn2-sched) (natp slot) (natp p)
                              (<= p (fn2-sched-heads-length fn2-sched))
                              (<= p (fn2-sched-tails-length fn2-sched))
                              (<= p (fn2-sched-counts-length fn2-sched))
                              (equal rows (fn2-sched-rows fn2-sched)))))
  (if (or (not (natp slot)) (not (natp p)) (>= slot p)) t
    (let ((head (fn2-sched-headsi slot fn2-sched))
          (tail (fn2-sched-tailsi slot fn2-sched))
          (cnt (fn2-sched-countsi slot fn2-sched)))
      (and (if (zp cnt)
               (and (= cnt 0) (= head *fn2-none*) (= tail *fn2-none*))
             (fn2-fair-fifo-walk head *fn2-none* cnt tail slot rows fn2-sched))
           (fn2-fair-fifos-validp (+ 1 slot) p rows fn2-sched)))))

(defun fn2-fair-sum-counts (slot p fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix p) (nfix slot)))
                  :guard (and (natp slot) (natp p) (<= p (fn2-sched-counts-length fn2-sched)))))
  (if (or (not (natp slot)) (not (natp p)) (>= slot p)) 0
    (+ (nfix (fn2-sched-countsi slot fn2-sched))
       (fn2-fair-sum-counts (+ 1 slot) p fn2-sched))))

(defun fn2-fair-count-in-queue (i rows fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix rows) (nfix i)))
                  :guard (and (fn2-sched-wfp fn2-sched) (natp i) (equal rows (fn2-sched-rows fn2-sched)))))
  (if (or (not (natp i)) (not (natp rows)) (>= i rows)) 0
    (+ (if (= (fn2-sched-in-queue i fn2-sched) 1) 1 0)
       (fn2-fair-count-in-queue (+ 1 i) rows fn2-sched))))

(defun fn2-fair-fifos-okp (fn2-sched)
  (declare (xargs :stobjs fn2-sched
                  :guard (and (fn2-sched-wfp fn2-sched)
                              (<= (fn2-sched-nprincipals fn2-sched) (fn2-sched-heads-length fn2-sched))
                              (<= (fn2-sched-nprincipals fn2-sched) (fn2-sched-tails-length fn2-sched))
                              (<= (fn2-sched-nprincipals fn2-sched) (fn2-sched-counts-length fn2-sched)))))
  (let ((p (fn2-sched-nprincipals fn2-sched))
        (rows (fn2-sched-rows fn2-sched))
        (queued (fn2-sched-queued fn2-sched)))
    (and (fn2-fair-fifos-validp 0 p rows fn2-sched)
         (equal (fn2-fair-sum-counts 0 p fn2-sched) queued)
         (equal (fn2-fair-count-in-queue 0 rows fn2-sched) queued))))

(defun fn2-fair-count-armed (i rows fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix rows) (nfix i)))
                  :guard (and (fn2-sched-wfp fn2-sched) (natp i) (equal rows (fn2-sched-rows fn2-sched)))))
  (if (or (not (natp i)) (not (natp rows)) (>= i rows)) 0
    (+ (if (< (fn2-sched-deadline i fn2-sched) *fn2-no-deadline*) 1 0)
       (fn2-fair-count-armed (+ 1 i) rows fn2-sched))))

(defun fn2-fair-timers-min-okp (i rows earliest fn2-sched)
  (declare (xargs :stobjs fn2-sched :measure (nfix (- (nfix rows) (nfix i)))
                  :guard (and (fn2-sched-wfp fn2-sched) (natp i) (natp earliest)
                              (equal rows (fn2-sched-rows fn2-sched)))))
  (if (or (not (natp i)) (not (natp rows)) (>= i rows)) t
    (let ((dl (fn2-sched-deadline i fn2-sched)))
      (and (or (>= dl *fn2-no-deadline*) (<= earliest dl))
           (fn2-fair-timers-min-okp (+ 1 i) rows earliest fn2-sched)))))

(defun fn2-fair-timers-okp (fn2-sched)
  (declare (xargs :stobjs fn2-sched :guard (fn2-sched-wfp fn2-sched)))
  (let ((rows (fn2-sched-rows fn2-sched)))
    (and (equal (fn2-fair-count-armed 0 rows fn2-sched)
                (fn2-sched-armed-timers fn2-sched))
         (or (fn2-sched-service-ready *fn2-timer-service-slot* fn2-sched)
             (fn2-fair-timers-min-okp 0 rows (fn2-sched-earliest-deadline fn2-sched) fn2-sched)))))

(defun fn2-check-fair-sched (fn2-sched)
  (declare (xargs :stobjs fn2-sched))
  (let ((p (fn2-sched-nprincipals fn2-sched))
        (len (fn2-sched-calendar-length fn2-sched))
        (cursor (fn2-sched-cursor fn2-sched)))
    (cond ((not (fn2-sched-wfp fn2-sched)) '(:fail :fair-sched-wfp))
          ((or (not (natp p)) (= p 0) (> p 65536)
               (< (fn2-sched-heads-length fn2-sched) p)
               (< (fn2-sched-tails-length fn2-sched) p)
               (< (fn2-sched-counts-length fn2-sched) p))
           '(:fail :fair-principals))
          ((or (not (natp len)) (= len 0) (not (unsigned-byte-p 32 len))
               (not (natp cursor)) (>= cursor len))
           '(:fail :fair-calendar-bounds))
          ((not (fn2-fair-calendar-validp (fn2-fair-sched-weights fn2-sched) fn2-sched))
           '(:fail :fair-calendar))
          ((not (fn2-fair-fifos-okp fn2-sched)) '(:fail :fair-fifo))
          ((not (fn2-fair-timers-okp fn2-sched)) '(:fail :fair-timers))
          (t :pass))))
(defthm fn2-check-fair-sched-result-shape
  (fn2-fair-resultp (fn2-check-fair-sched fn2-sched))
  :hints (("Goal" :in-theory (disable fn2-sched-wfp fn2-fair-calendar-validp
                                      fn2-fair-sched-weights fn2-fair-fifos-okp
                                      fn2-fair-timers-okp))))

;; 3. Live scheduler soundness: L-visit starvation bound + FIFO pop-head.

(defthm fn2-check-fair-sched-implies-starvation-hyps
  (implies (and (fn2-schedp fn2-sched)
                (equal (fn2-check-fair-sched fn2-sched) :pass)
                (fn2-sched-principalp principal fn2-sched)
                (< 0 (fn2-sched-countsi principal fn2-sched)))
           (fn2-sched-starvation-hyps principal (fn2-fair-sched-weights fn2-sched) fn2-sched))
  :hints (("Goal" :in-theory (disable fn2-schedp fn2-sched-wfp
                                      fn2-fair-sched-weights fn2-fair-calendar-validp
                                      fn2-fair-fifos-okp fn2-fair-timers-okp
                                      fn2-sched-calendar-validp fn2-sched-calendar-list fn2-sched-weightsp)
           :use ((:instance fn2-fair-calendar-validp-implies-sched
                            (weights (fn2-fair-sched-weights fn2-sched)))))))

(local (defun fn2-fair-find-code (i len code fn2-sched)
         (declare (xargs :stobjs fn2-sched :verify-guards nil :measure (nfix (- (nfix len) (nfix i)))))
         (cond ((or (not (natp i)) (not (natp len)) (>= i len)) nil)
               ((equal (fn2-sched-calendari i fn2-sched) code) i)
               (t (fn2-fair-find-code (+ 1 i) len code fn2-sched)))))
(local (defun fn2-fair-pass-induct (weights slot principal)
         (if (or (atom weights) (zp principal)) slot
           (fn2-fair-pass-induct (cdr weights) (+ 1 slot) (- principal 1)))))
(local (defthm fn2-fair-pass-0-has-all-slots
         (implies (and (fn2-sched-weightsp weights) (natp slot) (natp principal) (< principal (len weights)))
                  (member-equal (+ slot principal) (fn2-sched-pass weights 0 slot)))
         :hints (("Goal" :induct (fn2-fair-pass-induct weights slot principal)))))
(local (defthm fn2-fair-weights-max-posp
         (implies (and (fn2-sched-weightsp weights) (consp weights))
                  (<= 1 (fn2-sched-weights-max weights)))
         :rule-classes :linear))
(local (defthm fn2-fair-principal-sequence-has-pass-0
         (implies (and (natp top) (<= 1 top) (member-equal x (fn2-sched-pass weights 0 0)))
                  (member-equal x (fn2-sched-principal-sequence weights 0 top)))
         :hints (("Goal" :expand ((fn2-sched-principal-sequence weights 0 top))))))
(local (defthm fn2-fair-calendar-entries-preserves-member
         (implies (member-equal x seq)
                  (member-equal x (fn2-sched-calendar-entries seq p in-block)))))
(local (defthm fn2-fair-calendar-list-contains-every-principal
         (implies (and (fn2-sched-weightsp weights) (natp principal) (< principal (len weights)))
                  (member-equal principal (fn2-sched-calendar-list weights)))
         :hints (("Goal" :in-theory (disable fn2-sched-pass fn2-sched-principal-sequence
                                             fn2-sched-calendar-entries fn2-sched-weights-max)
                  :use ((:instance fn2-fair-pass-0-has-all-slots (slot 0))
                        (:instance fn2-fair-weights-max-posp)
                        (:instance fn2-fair-principal-sequence-has-pass-0
                                   (x principal) (top (fn2-sched-weights-max weights))))))))
(local (defthm fn2-fair-calendar-matchp-finds-code
         (implies (and (fn2-fair-calendar-matchp codes i fn2-sched)
                       (natp i) (natp len) (<= (+ i (len codes)) len)
                       (<= len (fn2-sched-calendar-length fn2-sched))
                       (member-equal code codes))
                  (let ((idx (fn2-fair-find-code i len code fn2-sched)))
                    (and (natp idx) (< idx len) (equal (fn2-sched-calendari idx fn2-sched) code))))
         :hints (("Goal" :induct (fn2-fair-calendar-matchp codes i fn2-sched)))))
(local (defun fn2-fair-dist (cur idx len)
         (if (<= (nfix cur) (nfix idx)) (- (nfix idx) (nfix cur))
           (+ (- (nfix len) (nfix cur)) (nfix idx)))))
(local (defthm fn2-fair-dist-props
         (implies (and (natp cur) (natp len) (< cur len))
                  (and (natp (fn2-fair-dist cur idx len))
                       (implies (and (natp idx) (< idx len)) (< (fn2-fair-dist cur idx len) len))))
         :rule-classes (:rewrite
                        (:linear :corollary
                                 (implies (and (natp cur) (natp len) (< cur len))
                                          (and (<= 0 (fn2-fair-dist cur idx len))
                                               (implies (and (natp idx) (< idx len))
                                                        (< (fn2-fair-dist cur idx len) len))))))))
(local (defthm fn2-fair-visit-step
         (implies (and (natp (fn2-sched-cursor fn2-sched))
                       (natp (fn2-sched-calendar-length fn2-sched))
                       (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
                       (unsigned-byte-p 32 (fn2-sched-calendar-length fn2-sched))
                       (natp idx) (< idx (fn2-sched-calendar-length fn2-sched))
                       (natp principal) (< principal (fn2-sched-nprincipals fn2-sched))
                       (equal (fn2-sched-calendari idx fn2-sched) principal))
                  (mv-let (kind slot pos s2) (fn2-sched-visit fn2-sched)
                    (declare (ignore pos))
                    (and (equal (fn2-sched-calendar-length s2) (fn2-sched-calendar-length fn2-sched))
                         (equal (fn2-sched-nprincipals s2) (fn2-sched-nprincipals fn2-sched))
                         (equal (fn2-sched-calendari idx s2) principal)
                         (natp (fn2-sched-cursor s2))
                         (< (fn2-sched-cursor s2) (fn2-sched-calendar-length s2))
                         (if (equal (fn2-sched-cursor fn2-sched) idx)
                             (and (= kind 0) (equal slot principal))
                           (< (fn2-fair-dist (fn2-sched-cursor s2) idx (fn2-sched-calendar-length s2))
                              (fn2-fair-dist (fn2-sched-cursor fn2-sched) idx (fn2-sched-calendar-length fn2-sched)))))))
         :hints (("Goal" :in-theory (enable fn2-sched-visit fn2-sched-calendar-length fn2-sched-calendari)))))
(local (defthm fn2-fair-visits-principal-reaches-idx
         (implies (and (natp (fn2-sched-cursor fn2-sched))
                       (natp (fn2-sched-calendar-length fn2-sched))
                       (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
                       (unsigned-byte-p 32 (fn2-sched-calendar-length fn2-sched))
                       (natp idx) (< idx (fn2-sched-calendar-length fn2-sched))
                       (natp principal) (< principal (fn2-sched-nprincipals fn2-sched))
                       (equal (fn2-sched-calendari idx fn2-sched) principal)
                       (natp left)
                       (<= (+ 1 (fn2-fair-dist (fn2-sched-cursor fn2-sched) idx (fn2-sched-calendar-length fn2-sched))) left))
                  (mv-nth 0 (fn2-sched-visits-principal left principal fn2-sched)))
         :rule-classes nil
         :hints (("Goal" :induct (fn2-sched-visits-principal left principal fn2-sched)
                  :in-theory (disable fn2-sched-visit fn2-fair-dist fn2-sched-calendari
                                      fn2-sched-cursor fn2-sched-calendar-length fn2-sched-nprincipals))
                 ("Subgoal *1/3" :use (fn2-fair-visit-step
                                       (:instance fn2-fair-dist-props
                                                  (cur (fn2-sched-cursor (mv-nth 3 (fn2-sched-visit fn2-sched))))
                                                  (len (fn2-sched-calendar-length fn2-sched)))))
                 ("Subgoal *1/2" :use (fn2-fair-visit-step
                                       (:instance fn2-fair-dist-props
                                                  (cur (fn2-sched-cursor fn2-sched))
                                                  (len (fn2-sched-calendar-length fn2-sched)))))
                 ("Subgoal *1/1" :use (fn2-fair-visit-step
                                       (:instance fn2-fair-dist-props
                                                  (cur (fn2-sched-cursor fn2-sched))
                                                  (len (fn2-sched-calendar-length fn2-sched))))))))

(defthm fn2-check-fair-sched-guarantees-visit-within-l
  (implies (and (fn2-schedp fn2-sched)
                (equal (fn2-check-fair-sched fn2-sched) :pass)
                (fn2-sched-principalp principal fn2-sched))
           (mv-nth 0 (fn2-sched-visits-principal
                      (fn2-sched-calendar-length fn2-sched) principal fn2-sched)))
  :hints (("Goal"
           :in-theory (disable fn2-schedp fn2-sched-wfp
                               fn2-sched-visits-principal fn2-sched-visit
                               fn2-fair-fifos-okp fn2-fair-timers-okp fn2-sched-calendar-list
                               fn2-fair-sched-weights fn2-fair-dist fn2-fair-find-code
                               fn2-sched-calendari fn2-sched-cursor fn2-sched-calendar-length
                               fn2-sched-nprincipals fn2-fair-calendar-list-contains-every-principal
                               fn2-fair-calendar-matchp-finds-code)
           :use ((:instance fn2-fair-calendar-list-contains-every-principal
                            (weights (fn2-fair-sched-weights fn2-sched)))
                 (:instance fn2-fair-calendar-matchp-finds-code
                            (codes (fn2-sched-calendar-list (fn2-fair-sched-weights fn2-sched)))
                            (i 0) (len (fn2-sched-calendar-length fn2-sched)) (code principal))
                 (:instance fn2-fair-visits-principal-reaches-idx
                            (idx (fn2-fair-find-code 0 (fn2-sched-calendar-length fn2-sched) principal fn2-sched))
                            (left (fn2-sched-calendar-length fn2-sched)))))))

(local (defthm fn2-fair-fifos-validp-extract
         (implies (and (fn2-fair-fifos-validp slot p rows fn2-sched)
                       (natp slot) (natp principal) (natp p) (<= slot principal) (< principal p)
                       (posp (fn2-sched-countsi principal fn2-sched)))
                  (fn2-fair-fifo-walk (fn2-sched-headsi principal fn2-sched) *fn2-none*
                                      (fn2-sched-countsi principal fn2-sched)
                                      (fn2-sched-tailsi principal fn2-sched) principal rows fn2-sched))
         :hints (("Goal" :induct (fn2-fair-fifos-validp slot p rows fn2-sched)
                  :in-theory (disable fn2-fair-fifo-walk)))))
(local (defthm fn2-fair-fifo-walk-head-props
         (implies (and (fn2-fair-fifo-walk head prev count tail principal rows fn2-sched) (posp count))
                  (and (< head rows)
                       (= (fn2-sched-in-queue head fn2-sched) 1)
                       (= (fn2-sched-principal head fn2-sched) principal)
                       (implies (< 1 count) (< (fn2-sched-next head fn2-sched) rows))))
         :hints (("Goal" :in-theory (disable fn2-fair-fifo-walk fn2-sched-in-queue
                                             fn2-sched-principal fn2-sched-prev fn2-sched-next)
                  :expand ((fn2-fair-fifo-walk head prev count tail principal rows fn2-sched)
                           (fn2-fair-fifo-walk (fn2-sched-next head fn2-sched) head
                                               (+ -1 count) tail principal rows fn2-sched))))))
(local (defthm fn2-fair-sum-counts-ge-slot
         (implies (and (natp slot) (natp principal) (natp p) (<= slot principal) (< principal p))
                  (<= (nfix (fn2-sched-countsi principal fn2-sched))
                      (fn2-fair-sum-counts slot p fn2-sched)))
         :rule-classes :linear))
(local (defthm fn2-fair-countsi-natp
         (implies (and (fn2-schedp fn2-sched) (natp principal)
                       (< principal (fn2-sched-counts-length fn2-sched)))
                  (and (integerp (fn2-sched-countsi principal fn2-sched))
                       (<= 0 (fn2-sched-countsi principal fn2-sched))))
         :rule-classes nil))

(defthm fn2-check-fair-sched-pop-head-ok
  (implies (and (fn2-schedp fn2-sched)
                (equal (fn2-check-fair-sched fn2-sched) :pass)
                (fn2-sched-principalp principal fn2-sched)
                (< 0 (fn2-sched-countsi principal fn2-sched)))
           (let ((head (fn2-sched-headsi principal fn2-sched)))
             (and (equal (mv-nth 0 (fn2-sched-pop-head principal fn2-sched)) :ok)
                  (equal (mv-nth 1 (fn2-sched-pop-head principal fn2-sched)) head)
                  (< head (fn2-sched-rows fn2-sched))
                  (= (fn2-sched-in-queue head fn2-sched) 1)
                  (= (fn2-sched-principal head fn2-sched) principal))))
  :hints (("Goal" :in-theory (e/d (fn2-sched-pop-head)
                                  (fn2-schedp fn2-sched-wfp
                                   fn2-sched-in-queue fn2-sched-principal fn2-sched-prev fn2-sched-next
                                   fn2-sched-headsi fn2-sched-tailsi fn2-sched-countsi
                                   fn2-sched-queued fn2-sched-rows
                                   fn2-sched-set-in-queue fn2-sched-set-prev fn2-sched-set-next
                                   update-fn2-sched-headsi update-fn2-sched-tailsi
                                   update-fn2-sched-countsi update-fn2-sched-queued
                                   fn2-fair-calendar-validp fn2-fair-sched-weights
                                   fn2-fair-timers-okp fn2-fair-count-in-queue
                                   fn2-fair-fifo-walk fn2-fair-fifos-validp fn2-fair-sum-counts))
           :use (fn2-fair-countsi-natp
                 (:instance fn2-fair-fifos-validp-extract
                            (slot 0) (p (fn2-sched-nprincipals fn2-sched)) (rows (fn2-sched-rows fn2-sched)))
                 (:instance fn2-fair-fifo-walk-head-props
                            (head (fn2-sched-headsi principal fn2-sched)) (prev *fn2-none*)
                            (count (fn2-sched-countsi principal fn2-sched))
                            (tail (fn2-sched-tailsi principal fn2-sched)) (rows (fn2-sched-rows fn2-sched)))
                 (:instance fn2-fair-sum-counts-ge-slot
                            (slot 0) (p (fn2-sched-nprincipals fn2-sched)))))))

;; 4. Bounded-readiness / non-starvation trace checker (guard-verified).
;; Continuously eligible ids must be visited within BOUND visits (< BOUND age);
;; repeated (:wake id) on an already-waiting id preserves its accumulated age.

(defun fn2-fair-wait-add (id waiting)
  (declare (xargs :guard (alistp waiting)))
  (if (assoc-equal id waiting) waiting (cons (cons id 0) waiting)))
(defun fn2-fair-wait-remove (id waiting)
  (declare (xargs :guard (alistp waiting)))
  (cond ((atom waiting) nil)
        ((equal (caar waiting) id) (fn2-fair-wait-remove id (cdr waiting)))
        (t (cons (car waiting) (fn2-fair-wait-remove id (cdr waiting))))))
(defun fn2-fair-wait-age (waiting)
  (declare (xargs :guard (alistp waiting)))
  (if (atom waiting) nil
    (cons (cons (caar waiting) (+ 1 (nfix (cdar waiting)))) (fn2-fair-wait-age (cdr waiting)))))
(defun fn2-fair-wait-exceeded (waiting bound)
  (declare (xargs :guard (and (alistp waiting) (posp bound))))
  (cond ((atom waiting) nil)
        ((>= (nfix (cdar waiting)) bound) (car waiting))
        (t (fn2-fair-wait-exceeded (cdr waiting) bound))))
(local (defthm fn2-fair-wait-alistp
         (implies (alistp waiting)
                  (and (alistp (fn2-fair-wait-add id waiting))
                       (alistp (fn2-fair-wait-remove id waiting))
                       (alistp (fn2-fair-wait-age waiting))))))

(defun fn2-fair-trace-step (e waiting bound)
  (declare (xargs :guard (and (alistp waiting) (posp bound))))
  (if (not (and (true-listp e) (consp e)))
      (mv (list :fail :fair-malformed-event e) waiting)
    (case (car e)
      ((:eligible :wake)
       (if (= (len e) 2) (mv nil (fn2-fair-wait-add (cadr e) waiting))
         (mv (list :fail :fair-malformed-event e) waiting)))
      (:visit
       (if (= (len e) 2)
           (let* ((w1 (fn2-fair-wait-age (fn2-fair-wait-remove (cadr e) waiting)))
                  (bad (fn2-fair-wait-exceeded w1 bound)))
             (if bad (mv (list :fail :fair-starvation (car bad) (cdr bad) bound) w1) (mv nil w1)))
         (mv (list :fail :fair-malformed-event e) waiting)))
      (:tick
       (if (= (len e) 1)
           (let* ((w1 (fn2-fair-wait-age waiting))
                  (bad (fn2-fair-wait-exceeded w1 bound)))
             (if bad (mv (list :fail :fair-starvation (car bad) (cdr bad) bound) w1) (mv nil w1)))
         (mv (list :fail :fair-malformed-event e) waiting)))
      ((:retire :done)
       (if (= (len e) 2) (mv nil (fn2-fair-wait-remove (cadr e) waiting))
         (mv (list :fail :fair-malformed-event e) waiting)))
      (otherwise (mv (list :fail :fair-unknown-event e) waiting)))))

(local (defthm fn2-fair-trace-step-props
         (and (implies (alistp waiting) (alistp (mv-nth 1 (fn2-fair-trace-step e waiting bound))))
              (implies (mv-nth 0 (fn2-fair-trace-step e waiting bound))
                       (fn2-fair-resultp (mv-nth 0 (fn2-fair-trace-step e waiting bound))))
              (implies (car (fn2-fair-trace-step e waiting bound))
                       (fn2-fair-resultp (car (fn2-fair-trace-step e waiting bound)))))))

(defun fn2-fair-trace-loop (events waiting bound drainp)
  (declare (xargs :guard (and (alistp waiting) (posp bound))))
  (if (atom events)
      (cond ((not (null events)) '(:fail :fair-malformed-trace))
            ((and drainp (consp waiting)) (list :fail :fair-unserved waiting))
            (t :pass))
    (mv-let (err next) (fn2-fair-trace-step (car events) waiting bound)
      (if err err (fn2-fair-trace-loop (cdr events) next bound drainp)))))

(defun fn2-fair-trace-check (events bound drainp)
  (declare (xargs :guard t))
  (if (not (posp bound)) '(:fail :fair-bad-bound)
    (fn2-fair-trace-loop events nil bound drainp)))
(local (defthm fn2-fair-trace-loop-result-shape
         (fn2-fair-resultp (fn2-fair-trace-loop events waiting bound drainp))
         :hints (("Goal" :induct (fn2-fair-trace-loop events waiting bound drainp)
                  :in-theory (disable fn2-fair-trace-step)))))
(defthm fn2-fair-trace-check-result-shape
  (fn2-fair-resultp (fn2-fair-trace-check events bound drainp))
  :hints (("Goal" :in-theory (disable fn2-fair-trace-loop))))

(defun fn2-fair-wait-max-age-okp (waiting bound)
  (declare (xargs :guard (and (alistp waiting) (posp bound))))
  (null (fn2-fair-wait-exceeded waiting bound)))
(defun fn2-fair-trace-bounded-p (events waiting bound drainp)
  (declare (xargs :guard (and (alistp waiting) (posp bound))))
  (if (atom events)
      (and (null events) (or (not drainp) (atom waiting)))
    (mv-let (err next) (fn2-fair-trace-step (car events) waiting bound)
      (and (not err) (fn2-fair-wait-max-age-okp next bound)
           (fn2-fair-trace-bounded-p (cdr events) next bound drainp)))))

(local (defthm fn2-fair-wait-exceeded-remove-add
         (implies (and (posp bound) (not (fn2-fair-wait-exceeded waiting bound)))
                  (and (not (fn2-fair-wait-exceeded (fn2-fair-wait-remove id waiting) bound))
                       (not (fn2-fair-wait-exceeded (fn2-fair-wait-add id waiting) bound))))))
(local (defthm fn2-fair-trace-step-nil-implies-age-ok
         (implies (and (posp bound)
                       (not (mv-nth 0 (fn2-fair-trace-step e waiting bound)))
                       (fn2-fair-wait-max-age-okp waiting bound))
                  (fn2-fair-wait-max-age-okp (mv-nth 1 (fn2-fair-trace-step e waiting bound)) bound))))
(local (defthm fn2-fair-trace-loop-sound
         (implies (and (posp bound) (fn2-fair-wait-max-age-okp waiting bound)
                       (equal (fn2-fair-trace-loop events waiting bound drainp) :pass))
                  (fn2-fair-trace-bounded-p events waiting bound drainp))))
(defthm fn2-fair-trace-check-sound
  (implies (equal (fn2-fair-trace-check events bound drainp) :pass)
           (and (posp bound) (fn2-fair-trace-bounded-p events nil bound drainp))))

;; 5. PV deadlock checker & evidence-aware fairness dispatcher.

(defun fn2-fair-deadlock-check (threads capacities retained)
  (declare (xargs :verify-guards nil))
  (let* ((res (fn2-pv-check-retained threads capacities retained))
         (status (cdr (assoc-eq :status res)))
         (deadlocks (cdr (assoc-eq :deadlocks res)))
         (witnesses (cdr (assoc-eq :witnesses res))))
    (cond ((not (eq status :ok)) (list :fail :fair-invalid-pv-program status))
          ((not (equal deadlocks 0)) (list :fail :fair-deadlock (or witnesses res)))
          (t :pass))))
(defthm fn2-fair-deadlock-check-result-shape
  (fn2-fair-resultp (fn2-fair-deadlock-check threads capacities retained)))
(defthm fn2-fair-deadlock-check-sound
  (iff (equal (fn2-fair-deadlock-check threads capacities retained) :pass)
       (let ((res (fn2-pv-check-retained threads capacities retained)))
         (and (eq (cdr (assoc-eq :status res)) :ok)
              (equal (cdr (assoc-eq :deadlocks res)) 0)))))

(defun fn2-check-fair-item (evidence fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (cond ((or (null evidence) (eq evidence :core)) (fn2-check-fair-sched fn2-sched))
        ((not (true-listp evidence)) '(:fail :fair-bad-evidence))
        ((and (eq (car evidence) :profile) (= (len evidence) 2))
         (let ((core-res (fn2-check-fair-sched fn2-sched)))
           (if (not (eq core-res :pass)) core-res
             (if (equal (fn2-fair-sched-weights fn2-sched) (fn2-profile-weights (nth 1 evidence)))
                 :pass '(:fail :fair-profile-weights)))))
        ((member-eq (car evidence) '(:trace :bounded-readiness))
         (cond ((= (len evidence) 3) (fn2-fair-trace-check (nth 1 evidence) (nth 2 evidence) nil))
               ((= (len evidence) 4) (fn2-fair-trace-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)))
               (t '(:fail :fair-bad-evidence))))
        ((eq (car evidence) :deadlock)
         (cond ((= (len evidence) 3)
                (fn2-fair-deadlock-check (nth 1 evidence) (nth 2 evidence)
                                         (make-list (len (nth 1 evidence)) :initial-element nil)))
               ((= (len evidence) 4)
                (fn2-fair-deadlock-check (nth 1 evidence) (nth 2 evidence) (nth 3 evidence)))
               (t '(:fail :fair-bad-evidence))))
        (t '(:fail :fair-bad-evidence))))

(defun fn2-check-fair-all (items fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (if (atom items)
      (if (null items) :pass '(:fail :fair-bad-evidence))
    (let ((r (fn2-check-fair-item (car items) fn2-sched)))
      (if (eq r :pass) (fn2-check-fair-all (cdr items) fn2-sched) r))))

(defun fn2-check-fair-sched-with-evidence (evidence fn2-sched)
  (declare (xargs :stobjs fn2-sched :verify-guards nil))
  (if (and (true-listp evidence) (eq (car evidence) :all))
      (fn2-check-fair-all (cdr evidence) fn2-sched)
    (fn2-check-fair-item evidence fn2-sched)))

(local (defthm fn2-check-fair-item-result-shape
         (fn2-fair-resultp (fn2-check-fair-item evidence fn2-sched))
         :hints (("Goal" :in-theory (disable fn2-check-fair-sched fn2-fair-trace-check
                                             fn2-fair-deadlock-check)))))
(local (defthm fn2-check-fair-all-result-shape
         (fn2-fair-resultp (fn2-check-fair-all items fn2-sched))
         :hints (("Goal" :induct (fn2-check-fair-all items fn2-sched)
                  :in-theory (disable fn2-check-fair-item)))))
(defthm fn2-check-fair-sched-with-evidence-result-shape
  (fn2-fair-resultp (fn2-check-fair-sched-with-evidence evidence fn2-sched))
  :hints (("Goal" :in-theory (disable fn2-check-fair-item fn2-check-fair-all))))
(defthm fn2-check-fair-all-sound
  (implies (and (equal (fn2-check-fair-all items fn2-sched) :pass)
                (member-equal item items))
           (equal (fn2-check-fair-item item fn2-sched) :pass))
  :hints (("Goal" :induct (fn2-check-fair-all items fn2-sched)
           :in-theory (disable fn2-check-fair-item))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-fair-resultp fn2-fair-ones fn2-fair-calendar-count fn2-fair-calendar-weights-aux
    fn2-fair-sched-weights fn2-fair-calendar-matchp fn2-fair-calendar-validp
    fn2-fair-fifo-walk fn2-fair-fifos-validp fn2-fair-sum-counts
    fn2-fair-count-in-queue fn2-fair-fifos-okp fn2-fair-count-armed
    fn2-fair-timers-min-okp fn2-fair-timers-okp fn2-check-fair-sched
    fn2-fair-wait-add fn2-fair-wait-remove fn2-fair-wait-age
    fn2-fair-wait-exceeded fn2-fair-trace-step fn2-fair-trace-loop
    fn2-fair-trace-check fn2-fair-wait-max-age-okp fn2-fair-trace-bounded-p)
  (w state)))

(assert-event
 (and (equal (fn2-fair-trace-check '((:eligible 0) (:eligible 1) (:visit 1) (:visit 0)) 2 t) :pass)
      (equal (car (fn2-fair-trace-check '((:eligible 0) (:eligible 1) (:visit 1) (:visit 1)) 2 nil)) :fail)
      (equal (car (fn2-fair-trace-check '((:eligible 0) (:visit 1) (:wake 0) (:visit 1)) 2 nil)) :fail)
      (equal (car (fn2-fair-trace-check '((:eligible 0) (:tick) (:tick)) 2 nil)) :fail)
      (equal (fn2-fair-deadlock-check '(((:p :a) (:v :a)) ((:p :a) (:v :a))) '((:a . 1)) '(nil nil)) :pass)
      (equal (car (fn2-fair-deadlock-check '(((:p :a) (:p :b) (:v :b) (:v :a))
                                             ((:p :b) (:p :a) (:v :a) (:v :b)))
                                           '((:a . 1) (:b . 1)) '(nil nil))) :fail)))
