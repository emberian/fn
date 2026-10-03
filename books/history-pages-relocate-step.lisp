; A publisher-owned relocation continuation. Every STEP checks one page,
; copies/zeros one page, changes the thirteen header words, or marks one page.
; GROW-IMAGE is deliberately separate: the current flat backing resizes the
; whole image. No bound on that allocation or on event encoding is claimed.
; Keep the cursor and scratch store together until :done or abandon both;
; a need verdict preserves the cursor and changes no words. Partial relocation
; is private: its placement is published only after :done.
(in-package "ACL2")
(include-book "history-pages-relocate")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-hpr-cursorp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 8)
       (member-eq (nth 0 x) '(:header-ready :ready :grow-image :copy :zero :header :mark :done))
       (natp (nth 1 x)) (< (nth 1 x) 5)
       (natp (nth 2 x)) (natp (nth 3 x))
       (nat-listp (nth 4 x)) (equal (len (nth 4 x)) 5)
       (nat-listp (nth 5 x)) (equal (len (nth 5 x)) 5)
       (natp (nth 6 x)) (natp (nth 7 x))))

(defun fn-hpr-cursor (phase r c n lens starts np k)
  (declare (xargs :guard t))
  (list phase r c n lens starts np k))

(defun fn-hpr-phase (phase k cursor)
  (declare (xargs :guard (fn-hpr-cursorp cursor)))
  (fn-hpr-cursor phase (nth 1 cursor) (nth 2 cursor) (nth 3 cursor)
                 (nth 4 cursor) (nth 5 cursor) (nth 6 cursor) k))

(defun fn-hpr-imagep (np pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (natp np)))
  (and (equal (pgs-v-length pgs-mem) np)
       (equal (pgs-d-length pgs-mem) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np))))

(defun fn-hpr-begin (r c n lens starts np pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp r) (< r 5) (natp c) (natp n)
                              (nat-listp lens) (equal (len lens) 5)
                              (nat-listp starts) (equal (len starts) 5) (natp np))
                  :verify-guards nil))
  (let ((hdr (fn-hp-hdr-m n lens (update-nth r np starts) (+ np c))))
    (cond ((not (fn-hpr-imagep np pgs-mem))
           (mv (list :refused :image) nil pgs-mem))
          ((not (and (< 0 c) (<= (adt-cap (nth r lens)) c)))
           (mv (list :refused :capacity) nil pgs-mem))
          ((not (adt-placement-ok starts lens np))
           (mv (list :refused :placement) nil pgs-mem))
          ((not (fn-hp-u64-listp hdr))
           (mv (list :refused :out-of-range) nil pgs-mem))
          (t (mv :yield (fn-hpr-cursor :header-ready r c n lens starts np 0) pgs-mem)))))

(defun fn-hpr-step (cursor pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (fn-hpr-cursorp cursor)
                  :verify-guards nil))
  (let* ((phase (nth 0 cursor)) (r (nth 1 cursor)) (c (nth 2 cursor))
         (n (nth 3 cursor)) (lens (nth 4 cursor)) (starts (nth 5 cursor))
         (np (nth 6 cursor)) (k (nth 7 cursor))
         (old (nth r starts)) (cap (adt-cap (nth r lens)))
         (npn (+ np c)) (hdr (fn-hp-hdr-m n lens (update-nth r np starts) npn))
         (before-grow (member-eq phase '(:header-ready :ready :grow-image))))
    (cond
     ((not (and (< 0 c) (<= cap c) (adt-placement-ok starts lens np)
                (fn-hp-u64-listp hdr)
                (fn-hpr-imagep (if before-grow np npn) pgs-mem)))
      (mv (list :refused :continuation-state) cursor pgs-mem))
     ((eq phase :header-ready)
      (let ((v (fn-hp-x-ready 0 pgs-mem)))
        (if (eq v :ok) (mv :yield (fn-hpr-phase :ready 0 cursor) pgs-mem)
          (mv v cursor pgs-mem))))
     ((eq phase :ready)
      (if (< k cap)
          (let ((v (fn-hp-x-ready (+ old k) pgs-mem)))
            (if (eq v :ok) (mv :yield (fn-hpr-phase :ready (+ 1 k) cursor) pgs-mem)
              (mv v cursor pgs-mem)))
        (mv :yield (fn-hpr-phase :grow-image 0 cursor) pgs-mem)))
     ((eq phase :grow-image)
      (mv (list :grow-image npn) cursor pgs-mem))
     ((eq phase :copy)
      (if (< k cap)
          (let ((pgs-mem (fn-hp-x-copy (* 2048 (+ old k)) (* 2048 (+ np k)) 2048 pgs-mem)))
            (mv :yield (fn-hpr-phase :copy (+ 1 k) cursor) pgs-mem))
        (mv :yield (fn-hpr-phase :zero 0 cursor) pgs-mem)))
     ((eq phase :zero)
      (if (< k cap)
          (let ((pgs-mem (fn-hp-x-zero (* 2048 (+ old k)) 2048 pgs-mem)))
            (mv :yield (fn-hpr-phase :zero (+ 1 k) cursor) pgs-mem))
        (mv :yield (fn-hpr-phase :header 0 cursor) pgs-mem)))
     ((eq phase :header)
      (let ((pgs-mem (fn-hp-x-put 6 hdr pgs-mem)))
        (mv :yield (fn-hpr-phase :mark 0 cursor) pgs-mem)))
     ((eq phase :mark)
      (if (< k c)
          (let ((pgs-mem (update-pgs-di (+ np k) 1 pgs-mem)))
            (mv :yield (fn-hpr-phase :mark (+ 1 k) cursor) pgs-mem))
        (mv :done (fn-hpr-phase :done 0 cursor) pgs-mem)))
     (t (mv :done cursor pgs-mem)))))

(defun fn-hpr-grow-image (cursor pgs-mem)
  ; Explicit prepaid capacity operation. It is not a bounded STEP.
  (declare (xargs :stobjs pgs-mem :guard (fn-hpr-cursorp cursor)
                  :verify-guards nil))
  (let ((np (nth 6 cursor)) (c (nth 2 cursor)))
    (if (not (and (eq (nth 0 cursor) :grow-image)
                  (fn-hpr-imagep np pgs-mem)))
        (mv (list :refused :continuation-state) cursor pgs-mem)
      (let ((pgs-mem (pgs-x-grow-image (+ np c) pgs-mem)))
        (mv :yield (fn-hpr-phase :copy 0 cursor) pgs-mem)))))

(defun fn-hpr-placement (cursor)
  ; Only :done exposes the replacement placement to the append retry.
  (declare (xargs :guard (fn-hpr-cursorp cursor)))
  (and (eq (nth 0 cursor) :done)
       (list (update-nth (nth 1 cursor) (nth 6 cursor) (nth 5 cursor))
             (+ (nth 6 cursor) (nth 2 cursor)))))

(local
 (defthm fn-hpr-natp-nth
   (implies (and (nat-listp x) (natp k) (< k (len x))) (natp (nth k x)))
   :hints (("Goal" :in-theory (enable nth)))))
(local
 (defthm fn-hpr-page-offset-natp
   (implies (and (natp a) (natp b)) (natp (+ (* 2048 a) (* 2048 b))))
   :hints (("Goal" :in-theory (enable natp)))))
(local
 (defthm fn-hpr-sum-natp
   (implies (and (natp a) (natp b)) (natp (+ a b)))
   :hints (("Goal" :in-theory (enable natp)))))

(verify-guards fn-hpr-begin
 :hints (("Goal" :in-theory (disable adt-cap adt-placement-ok fn-hp-hdr-m fn-hp-u64-listp))))
(verify-guards fn-hpr-grow-image
 :hints (("Goal" :in-theory (enable fn-hpr-cursorp))))
(verify-guards fn-hpr-step
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hpr-natp-nth (k (nth 1 cursor)) (x (nth 5 cursor)))
                (:instance fn-hpr-natp-nth (k (nth 1 cursor)) (x (nth 4 cursor)))
                (:instance fn-hp-placement-natp-start
                           (r (nth 1 cursor)) (starts (nth 5 cursor))
                           (lens (nth 4 cursor)) (np (nth 6 cursor))))
          :in-theory (e/d (fn-hpr-cursorp)
                          (nth adt-nth-0 adt-nth-1+ adt-cap adt-placement-ok
                           fn-hp-hdr-m fn-hp-u64-listp fn-hp-x-copy fn-hp-x-zero
                           fn-hp-x-put fn-hp-x-ready fn-hpr-phase)))))

; Whole-state equality, including dirty flags: splitting the existing loops
; changes neither the copied words nor any side effect.
(defthm fn-hpr-copy-split
  (implies (and (natp src) (natp dst) (natp a) (natp b))
           (equal (fn-hp-x-copy (+ src a) (+ dst a) b
                                 (fn-hp-x-copy src dst a pgs-mem))
                  (fn-hp-x-copy src dst (+ a b) pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-copy src dst a pgs-mem)
           :in-theory (enable fn-hp-x-copy))))

(defthm fn-hpr-zero-split
  (implies (and (natp at) (natp a) (natp b))
           (equal (fn-hp-x-zero (+ at a) b (fn-hp-x-zero at a pgs-mem))
                  (fn-hp-x-zero at (+ a b) pgs-mem)))
  :hints (("Goal" :induct (fn-hp-x-zero at a pgs-mem)
           :in-theory (enable fn-hp-x-zero))))

(defthm fn-hpr-copy-page
 (implies (and (natp old) (natp np) (natp k) (natp cap) (< k cap))
  (equal (fn-hp-x-copy (* 2048 (+ old k 1)) (* 2048 (+ np k 1)) (* 2048 (- cap (+ k 1)))
                        (fn-hp-x-copy (* 2048 (+ old k)) (* 2048 (+ np k)) 2048 pgs-mem))
         (fn-hp-x-copy (* 2048 (+ old k)) (* 2048 (+ np k)) (* 2048 (- cap k)) pgs-mem)))
 :hints (("Goal" :use ((:instance fn-hpr-copy-split (src (* 2048 (+ old k)))
                                (dst (* 2048 (+ np k))) (a 2048) (b (* 2048 (- cap (+ k 1))))))
          :in-theory (disable fn-hp-x-copy fn-hpr-copy-split))))
(defthm fn-hpr-zero-page
 (implies (and (natp old) (natp k) (natp cap) (< k cap))
  (equal (fn-hp-x-zero (* 2048 (+ old k 1)) (* 2048 (- cap (+ k 1)))
                        (fn-hp-x-zero (* 2048 (+ old k)) 2048 pgs-mem))
         (fn-hp-x-zero (* 2048 (+ old k)) (* 2048 (- cap k)) pgs-mem)))
 :hints (("Goal" :use ((:instance fn-hpr-zero-split (at (* 2048 (+ old k)))
                                (a 2048) (b (* 2048 (- cap (+ k 1))))))
          :in-theory (disable fn-hp-x-zero fn-hpr-zero-split))))

(defthm fn-hpr-mark-one
 (implies (and (natp at) (natp end) (< at end))
  (equal (fn-hp-x-mark (+ 1 at) end (update-pgs-di at 1 pgs-mem))
         (fn-hp-x-mark at end pgs-mem)))
 :hints (("Goal" :expand ((fn-hp-x-mark at end pgs-mem)))))
(defun-nx fn-hpr-remaining (cursor pgs-mem)
  ; Completion potential after growth. A successful tick preserves this
  ; entire final concrete, not just its words or returned placement.
  (let* ((phase (nth 0 cursor)) (r (nth 1 cursor)) (c (nth 2 cursor))
         (n (nth 3 cursor)) (lens (nth 4 cursor)) (starts (nth 5 cursor))
         (np (nth 6 cursor)) (k (nth 7 cursor))
         (old (nfix (nth r starts))) (cap (adt-cap (nfix (nth r lens))))
         (npn (+ (nfix np) (nfix c)))
         (hdr (fn-hp-hdr-m n lens (update-nth r np starts) npn)))
    (case phase
      (:copy (fn-hp-x-mark np npn
               (fn-hp-x-put 6 hdr
                 (fn-hp-x-zero (* 2048 old) (* 2048 cap)
                   (fn-hp-x-copy (* 2048 (+ old (nfix k)))
                                  (* 2048 (+ (nfix np) (nfix k)))
                                  (* 2048 (nfix (- cap (nfix k)))) pgs-mem)))))
      (:zero (fn-hp-x-mark np npn
               (fn-hp-x-put 6 hdr
                 (fn-hp-x-zero (* 2048 (+ old (nfix k)))
                                (* 2048 (nfix (- cap (nfix k)))) pgs-mem))))
      (:header (fn-hp-x-mark np npn (fn-hp-x-put 6 hdr pgs-mem)))
      (:mark (fn-hp-x-mark (+ (nfix np) (nfix k)) npn pgs-mem))
      (otherwise pgs-mem))))

(defthm fn-hpr-copy-zero (equal (fn-hp-x-copy src dst 0 pgs-mem) pgs-mem))
(defthm fn-hpr-zero-zero (equal (fn-hp-x-zero at 0 pgs-mem) pgs-mem))
(defthm fn-hpr-mark-end
 (implies (and (natp at) (natp end) (<= end at))
          (equal (fn-hp-x-mark at end pgs-mem) pgs-mem)))
(defthm fn-hpr-step-preserves-completion
 (implies (and (fn-hpr-cursorp cursor)
               (member-eq (nth 0 cursor) '(:copy :zero :header :mark :done)))
  (equal (fn-hpr-remaining (mv-nth 1 (fn-hpr-step cursor pgs-mem))
                            (mv-nth 2 (fn-hpr-step cursor pgs-mem)))
         (fn-hpr-remaining cursor pgs-mem)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hpr-copy-page (old (nth (nth 1 cursor) (nth 5 cursor)))
                           (np (nth 6 cursor)) (k (nth 7 cursor))
                           (cap (adt-cap (nth (nth 1 cursor) (nth 4 cursor)))))
                (:instance fn-hpr-zero-page (old (nth (nth 1 cursor) (nth 5 cursor)))
                           (k (nth 7 cursor)) (cap (adt-cap (nth (nth 1 cursor) (nth 4 cursor))))))
          :in-theory (e/d (fn-hpr-step fn-hpr-remaining fn-hpr-phase fn-hpr-cursor fn-hpr-cursorp)
                          (nth adt-nth-0 adt-nth-1+ adt-cap adt-placement-ok
                           fn-hp-hdr-m fn-hp-u64-listp fn-hp-x-copy fn-hp-x-zero
                           fn-hp-x-put fn-hp-x-mark fn-hp-x-ready)))))

(defthm fn-hpr-wait-keeps-concrete
 (implies (member-eq (nth 0 cursor) '(:header-ready :ready :grow-image :done))
          (equal (mv-nth 2 (fn-hpr-step cursor pgs-mem)) pgs-mem))
 :hints (("Goal" :in-theory (disable fn-hp-x-ready fn-hp-x-copy fn-hp-x-zero fn-hp-x-put))))
(defthm fn-hpr-begin-keeps-concrete
 (equal (mv-nth 2 (fn-hpr-begin r c n lens starts np pgs-mem)) pgs-mem))
(defthm fn-hpr-grow-starts-old-relocation
 (implies (and (natp r) (< r 5) (natp c) (natp n) (natp np)
               (nat-listp lens) (equal (len lens) 5)
               (nat-listp starts) (equal (len starts) 5)
               (equal (mv-nth 0 (fn-hp-x-relocate r c n lens starts np pgs-mem)) :ok))
  (equal (fn-hpr-remaining (fn-hpr-cursor :copy r c n lens starts np 0)
                            (pgs-x-grow-image (+ np c) pgs-mem))
         (mv-nth 3 (fn-hp-x-relocate r c n lens starts np pgs-mem))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-x-relocate-ok-unfolds))
          :in-theory (e/d (fn-hpr-remaining fn-hpr-cursor)
                          (fn-hp-x-relocate fn-hp-x-copy fn-hp-x-zero fn-hp-x-put
                           fn-hp-x-mark fn-hp-hdr-m adt-cap pgs-x-grow-image
                           fn-hp-x-relocate-ok-unfolds)))))
(defthm fn-hpr-done-is-complete
 (implies (equal (nth 0 cursor) :done)
          (equal (fn-hpr-remaining cursor pgs-mem) pgs-mem)))

(defthm fn-hpr-step-keeps-cursor
 (implies (fn-hpr-cursorp cursor)
          (fn-hpr-cursorp (mv-nth 1 (fn-hpr-step cursor pgs-mem))))
 :hints (("Goal" :in-theory
   (e/d (fn-hpr-cursorp fn-hpr-step fn-hpr-phase fn-hpr-cursor)
        (fn-hp-x-ready fn-hp-x-copy fn-hp-x-zero fn-hp-x-put fn-hp-x-mark
         adt-cap adt-placement-ok fn-hp-hdr-m fn-hp-u64-listp
         nth adt-nth-0 adt-nth-1+)))))

(local (defthm fn-hpr-ready-not-yield
  (not (equal (fn-hp-x-ready p pgs-mem) :yield))
  :hints (("Goal" :in-theory (enable fn-hp-x-ready)))))
(defun fn-hpr-rank (cursor)
 (declare (xargs :guard (fn-hpr-cursorp cursor)))
 (let* ((cap (adt-cap (nfix (nth (nth 1 cursor) (nth 4 cursor)))))
        (c (nfix (nth 2 cursor))) (k (nfix (nth 7 cursor))))
  (case (nth 0 cursor)
   (:header-ready (+ (* 3 cap) c 7))
   (:ready (+ (* 2 cap) (nfix (- cap k)) c 6))
   (:grow-image (+ (* 2 cap) c 5))
   (:copy (+ cap (nfix (- cap k)) c 4))
   (:zero (+ (nfix (- cap k)) c 3))
   (:header (+ c 2))
   (:mark (+ (nfix (- c k)) 1))
   (otherwise 0))))
(defthm fn-hpr-yield-progresses
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-step cursor pgs-mem)) :yield))
          (< (fn-hpr-rank (mv-nth 1 (fn-hpr-step cursor pgs-mem)))
             (fn-hpr-rank cursor)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-hpr-step fn-hpr-rank fn-hpr-phase fn-hpr-cursor fn-hpr-cursorp)
                          (nth adt-nth-0 adt-nth-1+ adt-cap adt-placement-ok
                           fn-hp-hdr-m fn-hp-u64-listp fn-hp-x-copy fn-hp-x-zero
                           fn-hp-x-put fn-hp-x-mark fn-hp-x-ready)))))
(defthm fn-hpr-grow-progresses
 (implies (and (fn-hpr-cursorp cursor)
               (equal (mv-nth 0 (fn-hpr-grow-image cursor pgs-mem)) :yield))
          (< (fn-hpr-rank (mv-nth 1 (fn-hpr-grow-image cursor pgs-mem)))
             (fn-hpr-rank cursor)))
 :hints (("Goal" :in-theory (e/d (fn-hpr-rank fn-hpr-phase fn-hpr-cursor fn-hpr-cursorp)
                                (nth adt-nth-0 adt-nth-1+ adt-cap pgs-x-grow-image)))))
