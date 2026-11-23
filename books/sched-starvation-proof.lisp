; Discharges fn2-sched-starvation (books/sched.lisp): from any cursor inside a valid weighted
; calendar, L = (fn2-sched-calendar-length fn2-sched) calls of fn2-sched-visit include a
; principal visit of PRINCIPAL.  The witness is PRINCIPAL's pass-0 entry: every weight is at
; least 1, so pass 0 lists every slot in order and slot q sits at calendar position
; q + 4*floor(q/16) (ss-pos).  fn2-sched-principalp bounds q below 65536, so that position is
; below 2^32 and stays on the visited cycle even where fn2-sched-visit resets a non-u32 cursor.
(in-package "ACL2")
(include-book "sched")
(include-book "owed-discharge")

; Position of sequence element Q in (fn2-sched-calendar-entries seq p b): one slot per
; principal entry, four more after each sixteenth.
(local
 (defun ss-pos (q b)
   (if (zp q) 0
     (if (>= b 15) (+ 5 (ss-pos (- q 1) 0)) (+ 1 (ss-pos (- q 1) (+ 1 b)))))))
(local
 (defthm ss-pos-bound
   (and (natp (ss-pos q b)) (<= (ss-pos q b) (* 5 (nfix q))))
   :rule-classes ((:linear :corollary (<= (ss-pos q b) (* 5 (nfix q))))
                  (:type-prescription :corollary (natp (ss-pos q b))))))
(local
 (defun ss-entries-ind (q seq b)
   (if (or (zp q) (atom seq)) (list q seq b)
     (if (or (atom (cdr seq)) (>= b 15)) (ss-entries-ind (- q 1) (cdr seq) 0)
       (ss-entries-ind (- q 1) (cdr seq) (+ 1 b))))))
(local
 (defthm ss-nth-plus-cons
   (implies (and (syntaxp (quotep k)) (posp k) (natp x))
            (equal (nth (+ k x) (cons a l)) (nth (+ (- k 1) x) l)))))
(local
 (defthm ss-entries-nth
   (implies (and (natp q) (< q (len seq)))
            (and (< (ss-pos q b) (len (fn2-sched-calendar-entries seq p b)))
                 (equal (nth (ss-pos q b) (fn2-sched-calendar-entries seq p b))
                        (nth q seq))))
   :hints (("Goal" :induct (ss-entries-ind q seq b)))))

; Pass 0 of a valid weight list is the slots in order.
(local
 (defthm ss-pass-len
   (implies (fn2-sched-weightsp weights)
            (equal (len (fn2-sched-pass weights 0 slot)) (len weights)))))
(local
 (defun ss-pass-ind (weights q slot)
   (if (or (atom weights) (zp q)) (list weights q slot)
     (ss-pass-ind (cdr weights) (- q 1) (+ 1 slot)))))
(local
 (defthm ss-pass-nth
   (implies (and (fn2-sched-weightsp weights) (natp q) (< q (len weights)) (acl2-numberp slot))
            (equal (nth q (fn2-sched-pass weights 0 slot)) (+ slot q)))
   :hints (("Goal" :induct (ss-pass-ind weights q slot)
            :expand ((fn2-sched-pass weights 0 slot))))))
(local
 (defthm ss-nth-append
   (implies (and (natp q) (< q (len a)))
            (and (equal (nth q (append a b)) (nth q a))
                 (< q (len (append a b)))))))
(local
 (defthm ss-max-pos
   (implies (and (fn2-sched-weightsp weights) (consp weights))
            (< 0 (fn2-sched-weights-max weights)))
   :rule-classes :linear))
(local
 (defthm ss-sequence-nth
   (implies (and (fn2-sched-weightsp weights) (natp q) (< q (len weights)))
            (and (< q (len (fn2-sched-principal-sequence weights 0 (fn2-sched-weights-max weights))))
                 (equal (nth q (fn2-sched-principal-sequence weights 0 (fn2-sched-weights-max weights))) q)))
   :hints (("Goal" :expand ((fn2-sched-principal-sequence weights 0 (fn2-sched-weights-max weights)))
            :cases ((consp weights))
            :use ((:instance ss-pass-nth (slot 0))
                  (:instance ss-nth-append (a (fn2-sched-pass weights 0 0))
                             (b (fn2-sched-principal-sequence weights 1 (fn2-sched-weights-max weights)))))
            :in-theory (disable ss-pass-nth ss-nth-append fn2-sched-pass)))))

; Slot Q's pass-0 entry sits at (ss-pos q 0) of the weighted calendar.
(local
 (defthm ss-calendar-list-nth
   (implies (and (fn2-sched-weightsp weights) (natp q) (< q (len weights)))
            (and (< (ss-pos q 0) (len (fn2-sched-calendar-list weights)))
                 (equal (nth (ss-pos q 0) (fn2-sched-calendar-list weights)) q)))
   :hints (("Goal" :in-theory (disable ss-entries-nth fn2-sched-principal-sequence fn2-sched-calendar-entries)
            :use ((:instance ss-sequence-nth)
                  (:instance ss-entries-nth (b 0) (p (len weights))
                             (seq (fn2-sched-principal-sequence weights 0 (fn2-sched-weights-max weights)))))))))
(local
 (defun ss-match-ind (codes i j)
   (if (or (atom codes) (zp j)) (list codes i j) (ss-match-ind (cdr codes) (+ 1 i) (- j 1)))))
(local
 (defthm ss-matchp-nth
   (implies (and (fn2-sched-calendar-matchp codes i fn2-sched) (natp j) (< j (len codes)))
            (equal (fn2-sched-calendari (+ i j) fn2-sched) (nth j codes)))
   :hints (("Goal" :induct (ss-match-ind codes i j)
            :in-theory (disable fn2-sched-calendari fn2-sched-calendar-length)))))

; A visit writes only the cursor.
(local
 (defthm ss-visit-frame
   (and (equal (fn2-sched-calendar-length (mv-nth 3 (fn2-sched-visit fn2-sched)))
               (fn2-sched-calendar-length fn2-sched))
        (equal (fn2-sched-calendari i (mv-nth 3 (fn2-sched-visit fn2-sched)))
               (fn2-sched-calendari i fn2-sched))
        (equal (fn2-sched-nprincipals (mv-nth 3 (fn2-sched-visit fn2-sched)))
               (fn2-sched-nprincipals fn2-sched)))
   :hints (("Goal" :in-theory (enable fn2-sched-visit)))))
(local
 (defthm ss-visit-cursor
   (implies (natp (fn2-sched-cursor fn2-sched))
            (equal (fn2-sched-cursor (mv-nth 3 (fn2-sched-visit fn2-sched)))
                   (let ((c (fn2-sched-cursor fn2-sched))
                         (l (fn2-sched-calendar-length fn2-sched)))
                     (if (< c l)
                         (if (and (< (+ 1 c) l) (< (+ 1 c) 4294967296)) (+ 1 c) 0)
                       c))))
   :hints (("Goal" :in-theory (enable fn2-sched-visit)))))
(local
 (defthm ss-visit-hit
   (implies (and (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
                 (< (fn2-sched-calendari (fn2-sched-cursor fn2-sched) fn2-sched)
                    (fn2-sched-nprincipals fn2-sched)))
            (and (equal (mv-nth 0 (fn2-sched-visit fn2-sched)) 0)
                 (equal (mv-nth 1 (fn2-sched-visit fn2-sched))
                        (fn2-sched-calendari (fn2-sched-cursor fn2-sched) fn2-sched))))
   :hints (("Goal" :in-theory (enable fn2-sched-visit)))))

; Visits from cursor C to position TT, the cursor wrapping to 0 after position M-1.
(local (defun ss-dist (c tt m) (if (<= c tt) (- tt c) (+ (- m c) tt))))
(local
 (defthm ss-visits-reach
   (implies (and (natp tt) (< tt (fn2-sched-calendar-length fn2-sched)) (< tt 4294967296)
                 (natp (fn2-sched-cursor fn2-sched))
                 (< (fn2-sched-cursor fn2-sched) (fn2-sched-calendar-length fn2-sched))
                 (< (fn2-sched-cursor fn2-sched) 4294967296)
                 (equal (fn2-sched-calendari tt fn2-sched) principal)
                 (< principal (fn2-sched-nprincipals fn2-sched))
                 (integerp n)
                 (< (ss-dist (fn2-sched-cursor fn2-sched) tt
                             (min (fn2-sched-calendar-length fn2-sched) 4294967296))
                    n))
            (mv-nth 0 (fn2-sched-visits-principal n principal fn2-sched)))
   :hints (("Goal" :induct (fn2-sched-visits-principal n principal fn2-sched)
            :expand ((fn2-sched-visits-principal n principal fn2-sched))
            :in-theory (disable fn2-sched-cursor fn2-sched-calendari fn2-sched-calendar-length
                                fn2-sched-nprincipals))
           ("Subgoal *1/3" :cases ((equal (fn2-sched-cursor fn2-sched) tt))))))
(local
 (defthm ss-pos-u32
   (implies (and (natp q) (< q 65536)) (< (ss-pos q 0) 4294967296))
   :hints (("Goal" :use ((:instance ss-pos-bound (b 0))) :in-theory (disable ss-pos-bound)))
   :rule-classes :linear))

(defthm fn2-sched-starvation-proved
  (fn2-sched-starvation$owed principal weights fn2-sched)
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn2-sched-starvation$owed)
                           (fn2-sched-cursor fn2-sched-calendari fn2-sched-calendar-length
                            fn2-sched-nprincipals fn2-sched-calendar-list ss-visits-reach
                            ss-matchp-nth ss-calendar-list-nth fn2-sched-wfp fn2-sched-countsi))
           :use ((:instance ss-visits-reach (tt (ss-pos principal 0))
                            (n (fn2-sched-calendar-length fn2-sched)))
                 (:instance ss-matchp-nth (i 0) (j (ss-pos principal 0))
                            (codes (fn2-sched-calendar-list weights)))
                 (:instance ss-calendar-list-nth (q principal))))))
(fn2-owed-discharge fn2-sched-starvation fn2-sched-starvation-proved)
