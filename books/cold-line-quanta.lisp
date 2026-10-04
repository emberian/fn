; cold-line-quanta.lisp -- why a served line must run in quanta that fit the
; realizer's cache, and that such quanta always finish (lane cold-line,
; 2026-10-04; ledger sl-cold-line-quanta, sl-cold-line-deadline).
;
; The host (host/native/extent.lisp fnn-extent-entry, host/native/owner.lisp
; fnn-owner-cursor-step) runs a served quantum with the extent realizer in
; its no-I/O mode: a payload already in the realizer's cache is a hit (moved
; to the front); the first payload that is not aborts the run, is read off
; the owner mutex and stored at the front (the cache keeps
; fn-arx-read-cache-entries, the oldest falls off), and the quantum runs
; again from its unchanged continuation.  This book is that loop as a model:
;   fn-clq-run (demand cache)        one no-I/O run of a quantum that reads
;                                    the payload handles DEMAND in order
;   fn-clq-resume (demand cache c n) at most N runs, each miss stored
; KEYSTONE fn-clq-resume-finishes: a quantum whose demand has at most C
; reads finishes within (len demand) + 1 runs from ANY cache of capacity C.
; TEETH fn-clq-nine-reads-never-finish: nine distinct reads at C = 8 (the
; 45e05c7fd defect: a whole HDR Newsgroups line over 40 articles is one
; quantum of 40 reads) never finish, whatever the number of runs tried:
; each miss evicts the read the next run needs first.
; LINE fn-clq-line-finishes: a line run as quanta each of at most C reads
; finishes, in at most (total reads) + (number of quanta) runs.
; The served cursors meet the premise with Q = fn-clq-payload-quantum reads
; per quantum (books/over-window.lisp fn-ovw-step-payloads-fit), half the
; cache, so a second line's quantum interleaved between a miss and its
; rerun cannot evict the first's reads either.
(in-package "ACL2")

(defun fn-clq-touch (h cache)
  (declare (xargs :guard (true-listp cache)))
  (cons h (remove-equal h cache)))

(defun fn-clq-insert (h cache c)
  (declare (xargs :guard (and (true-listp cache) (natp c))))
  (take (min (nfix c) (+ 1 (len cache))) (cons h cache)))

; (mv missp handle cache'): NIL when every read hit, else the first read
; that missed and the cache as the aborted run left it.
(defun fn-clq-run (demand cache)
  (declare (xargs :guard (and (true-listp demand) (true-listp cache))))
  (if (atom demand)
      (mv nil nil cache)
    (if (member-equal (car demand) cache)
        (fn-clq-run (cdr demand) (fn-clq-touch (car demand) cache))
      (mv t (car demand) cache))))

(defthm fn-clq-run-keeps-true-listp
  (implies (true-listp cache)
           (true-listp (mv-nth 2 (fn-clq-run demand cache))))
  :hints (("Goal" :in-theory (enable fn-clq-touch))))

; (mv runs donep cache')
(defun fn-clq-resume (demand cache c n)
  (declare (xargs :guard (and (true-listp demand) (true-listp cache) (natp c) (natp n))
                  :measure (nfix n) :verify-guards nil))
  (if (zp n)
      (mv 0 nil cache)
    (mv-let (missp h cache2) (fn-clq-run demand cache)
      (if (not missp)
          (mv 1 t cache2)
        (mv-let (runs donep cache3)
          (fn-clq-resume demand (fn-clq-insert h cache2 c) c (- n 1))
          (mv (+ 1 runs) donep cache3))))))

(defthm fn-clq-insert-true-listp
  (true-listp (fn-clq-insert h cache c)))

(defthm fn-clq-resume-runs-natp
  (natp (car (fn-clq-resume demand cache c n)))
  :rule-classes (:rewrite :type-prescription))

(verify-guards fn-clq-resume
  :hints (("Goal" :in-theory (disable fn-clq-insert fn-clq-run))))

; The realizer's own number (books/payload-extent.lisp
; fn-arx-read-cache-entries is 8; restated so this book stays below it --
; tests/acl2/cold-line-quanta-tests.lisp checks the two agree).
(defconst *fn-clq-cache-entries* 8)

; Reads a served quantum may need: half the cache.
(defun fn-clq-payload-quantum ()
  (declare (xargs :guard t))
  (floor *fn-clq-cache-entries* 2))

(defthm fn-clq-payload-quantum-fits
  (and (posp (fn-clq-payload-quantum))
       (< (fn-clq-payload-quantum) *fn-clq-cache-entries*))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Membership facts of the two cache moves

(defthm fn-clq-member-touch
  (iff (member-equal x (fn-clq-touch h cache))
       (or (equal x h) (member-equal x cache))))

(in-theory (disable fn-clq-touch))

; The longest prefix of DEMAND every read of which is in CACHE.
(defun fn-clq-held (demand cache)
  (declare (xargs :guard (and (true-listp demand) (true-listp cache))))
  (if (and (consp demand) (member-equal (car demand) cache))
      (+ 1 (fn-clq-held (cdr demand) cache))
    0))

(local
 (defun fn-clq-take-ind (n l)
   (if (or (zp n) (atom l)) (list n l) (fn-clq-take-ind (- n 1) (cdr l)))))

(defthm fn-clq-member-take-mono
  (implies (and (member-equal x (take m l)) (natp m) (natp n) (<= m n))
           (member-equal x (take n l)))
  :hints (("Goal" :induct (list (fn-clq-take-ind m l) (fn-clq-take-ind n l)))))

(defthm fn-clq-member-take-remove
  (implies (and (member-equal x (take n l)) (not (equal x y)) (natp n))
           (member-equal x (take n (remove-equal y l))))
  :hints (("Goal" :induct (fn-clq-take-ind n l))
          ("Subgoal *1/2" :use ((:instance fn-clq-member-take-mono
                                 (m (- n 1)) (l (remove-equal y (cdr l))))))))

(defthm fn-clq-member-take-touch
  (implies (and (member-equal x (take n cache)) (natp n))
           (member-equal x (take (+ 1 n) (fn-clq-touch y cache))))
  :hints (("Goal" :in-theory (enable fn-clq-touch)
           :cases ((equal x y)))))

(defthm fn-clq-held-of-touch
  (implies (member-equal a cache)
           (equal (fn-clq-held d (fn-clq-touch a cache))
                  (fn-clq-held d cache))))


(local
 (defun fn-clq-run-ind (demand cache n)
   (if (atom demand)
       (list cache n)
     (if (member-equal (car demand) cache)
         (fn-clq-run-ind (cdr demand) (fn-clq-touch (car demand) cache) (+ 1 n))
       (list cache n)))))

(defthm fn-clq-run-take-shift
  (implies (and (member-equal x (take n cache)) (natp n))
           (member-equal x (take (+ n (fn-clq-held demand cache))
                                 (mv-nth 2 (fn-clq-run demand cache)))))
  :hints (("Goal" :induct (fn-clq-run-ind demand cache n) :in-theory (disable take)) ("Subgoal *1/2" :use ((:instance fn-clq-member-take-touch (y (car demand)))))))

(defthm fn-clq-run-missp
  (iff (mv-nth 0 (fn-clq-run demand cache))
       (< (fn-clq-held demand cache) (len demand)))
  :hints (("Goal" :induct (fn-clq-run demand cache))))

(defthm fn-clq-run-missed
  (implies (mv-nth 0 (fn-clq-run demand cache))
           (equal (mv-nth 1 (fn-clq-run demand cache))
                  (nth (fn-clq-held demand cache) demand)))
  :hints (("Goal" :induct (fn-clq-run demand cache))))

(defthm fn-clq-member-of-held-prefix
  (implies (member-equal x (take (fn-clq-held demand cache) demand))
           (member-equal x cache))
  :hints (("Goal" :induct (fn-clq-held demand cache))))

(defthm fn-clq-run-keeps-members
  (implies (member-equal x cache)
           (member-equal x (mv-nth 2 (fn-clq-run demand cache))))
  :hints (("Goal" :induct (fn-clq-run demand cache))))

(defthm fn-clq-member-take-1+
  (implies (and (member-equal x (take k l)) (natp k))
           (member-equal x (take (+ 1 k) l)))
  :hints (("Goal" :use ((:instance fn-clq-member-take-mono (m k) (n (+ 1 k)))))))

(defthm fn-clq-touched-front
  (member-equal a (take (+ 1 (fn-clq-held d (fn-clq-touch a cache)))
                        (mv-nth 2 (fn-clq-run d (fn-clq-touch a cache)))))
  :hints (("Goal" :in-theory (disable fn-clq-run-take-shift)
           :use ((:instance fn-clq-run-take-shift (x a) (n 1) (demand d)
                            (cache (fn-clq-touch a cache))))
           :expand ((fn-clq-touch a cache)))))

(defthm fn-clq-take-0
  (equal (take 0 x) nil))

(defthm fn-clq-touched-front-held
  (implies (member-equal a cache)
           (member-equal a (take (+ 1 (fn-clq-held d cache))
                                 (mv-nth 2 (fn-clq-run d (fn-clq-touch a cache))))))
  :hints (("Goal" :in-theory (disable fn-clq-touched-front)
           :use fn-clq-touched-front)))

(defthm fn-clq-run-holds-prefix
  (implies (member-equal x (take (fn-clq-held demand cache) demand))
           (member-equal x (take (fn-clq-held demand cache)
                                 (mv-nth 2 (fn-clq-run demand cache)))))
  :hints (("Goal" :induct (fn-clq-run demand cache)
           :in-theory (disable take fn-clq-run-take-shift fn-clq-member-take-mono fn-clq-touched-front))
          ("Subgoal *1/2" :expand ((take (+ 1 (fn-clq-held (cdr demand) cache)) demand)))))

(defthm fn-clq-member-take-own-len
  (implies (member-equal x l) (member-equal x (take (len l) l))))

(defthm fn-clq-member-insert
  (implies (and (member-equal x (take k l)) (member-equal x l)
                (natp k) (natp c) (< k c))
           (member-equal x (fn-clq-insert h l c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-clq-insert) (take fn-clq-member-take-mono fn-clq-member-take-1+))
           :expand ((take (min c (+ 1 (len l))) (cons h l)) (take (+ 1 (len l)) (cons h l)) (take c (cons h l)))
           :cases ((<= k (len l))))
          ("Subgoal 2" :use ((:instance fn-clq-member-take-mono (m (len l)) (n (+ -1 (min c (+ 1 (len l))))))))
          ("Subgoal 1" :use ((:instance fn-clq-member-take-mono (m k) (n (+ -1 (min c (+ 1 (len l))))))))))

(defthm fn-clq-member-insert-self
  (implies (posp c) (member-equal h (fn-clq-insert h l c))))

(local
 (defun fn-clq-bad (xs l)
   (if (atom xs) nil
     (if (member-equal (car xs) l) (fn-clq-bad (cdr xs) l) (car xs)))))

(local
 (defthm fn-clq-bad-witness
   (implies (not (subsetp-equal xs l))
            (and (member-equal (fn-clq-bad xs l) xs)
                 (not (member-equal (fn-clq-bad xs l) l))))))

(defthm fn-clq-held-at-least
  (implies (and (subsetp-equal (take k demand) l) (natp k) (<= k (len demand)))
           (<= k (fn-clq-held demand l)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-clq-take-ind k demand))))

(defthm fn-clq-member-take-split
  (implies (and (member-equal x (take (+ 1 k) l)) (natp k)
                (not (member-equal x (take k l))))
           (equal (nth k l) x))
  :rule-classes nil
  :hints (("Goal" :induct (fn-clq-take-ind k l))))

(defthm fn-clq-miss-stores-prefix
  (implies (and (mv-nth 0 (fn-clq-run demand cache))
                (posp c) (<= (len demand) c)
                (member-equal x (take (+ 1 (fn-clq-held demand cache)) demand)))
           (member-equal x (fn-clq-insert (mv-nth 1 (fn-clq-run demand cache))
                                          (mv-nth 2 (fn-clq-run demand cache)) c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-clq-insert take)
           :cases ((member-equal x (take (fn-clq-held demand cache) demand))))
          ("Subgoal 2" :use ((:instance fn-clq-member-take-split
                              (k (fn-clq-held demand cache)) (l demand))))
          ("Subgoal 1" :use ((:instance fn-clq-member-insert
                              (k (fn-clq-held demand cache))
                              (l (mv-nth 2 (fn-clq-run demand cache)))
                              (h (mv-nth 1 (fn-clq-run demand cache))))))))

(defthm fn-clq-miss-progresses
  (implies (and (mv-nth 0 (fn-clq-run demand cache))
                (posp c) (<= (len demand) c))
           (< (fn-clq-held demand cache)
              (fn-clq-held demand (fn-clq-insert (mv-nth 1 (fn-clq-run demand cache))
                                                 (mv-nth 2 (fn-clq-run demand cache)) c))))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-clq-insert take fn-clq-run-missed)
           :use ((:instance fn-clq-held-at-least
                  (k (+ 1 (fn-clq-held demand cache)))
                  (l (fn-clq-insert (mv-nth 1 (fn-clq-run demand cache))
                                    (mv-nth 2 (fn-clq-run demand cache)) c)))
                 (:instance fn-clq-bad-witness
                  (xs (take (+ 1 (fn-clq-held demand cache)) demand))
                  (l (fn-clq-insert (mv-nth 1 (fn-clq-run demand cache))
                                    (mv-nth 2 (fn-clq-run demand cache)) c)))
                 (:instance fn-clq-miss-stores-prefix
                  (x (fn-clq-bad (take (+ 1 (fn-clq-held demand cache)) demand)
                                 (fn-clq-insert (mv-nth 1 (fn-clq-run demand cache))
                                                (mv-nth 2 (fn-clq-run demand cache)) c))))))))

(defthm fn-clq-held-bound
  (<= (fn-clq-held demand cache) (len demand))
  :rule-classes :linear)

(defthm fn-clq-run-missp-car
  (iff (car (fn-clq-run demand cache))
       (< (fn-clq-held demand cache) (len demand)))
  :hints (("Goal" :use fn-clq-run-missp :in-theory (disable fn-clq-run-missp))))

(defthm fn-clq-resume-finishes-from
  (implies (and (posp c) (<= (len demand) c) (natp n)
                (< (- (len demand) (fn-clq-held demand cache)) n))
           (and (mv-nth 1 (fn-clq-resume demand cache c n))
                (<= (mv-nth 0 (fn-clq-resume demand cache c n))
                    (+ 1 (- (len demand) (fn-clq-held demand cache))))))
  :hints (("Goal" :induct (fn-clq-resume demand cache c n)
           :in-theory (disable fn-clq-insert fn-clq-run-missed))))

; KEYSTONE.

(defthm fn-clq-resume-finishes
  (implies (and (posp c) (<= (len demand) c))
           (and (mv-nth 1 (fn-clq-resume demand cache c (+ 1 (len demand))))
                (<= (mv-nth 0 (fn-clq-resume demand cache c (+ 1 (len demand))))
                    (+ 1 (len demand)))))
  :hints (("Goal" :use ((:instance fn-clq-resume-finishes-from (n (+ 1 (len demand)))))
           :in-theory (disable fn-clq-resume-finishes-from))))

(defun fn-clq-next (demand cache c)
  (declare (xargs :guard (and (true-listp demand) (true-listp cache) (natp c))))
  (mv-let (missp h cache2) (fn-clq-run demand cache)
    (if missp (fn-clq-insert h cache2 c) cache2)))

(defthm fn-clq-resume-of-miss
  (implies (and (not (zp n)) (mv-nth 0 (fn-clq-run demand cache)))
           (equal (mv-nth 1 (fn-clq-resume demand cache c n))
                  (mv-nth 1 (fn-clq-resume demand (fn-clq-next demand cache c) c (- n 1))))))

(defconst *fn-clq-nine* '(1 2 3 4 5 6 7 8 9))

; A set of caches closed under the loop, every one of which misses: no run

; from any of them ever finishes.

(defun fn-clq-trap-from (todo states demand c)
  (declare (xargs :guard (and (true-listp todo) (true-listp states) (true-listp demand) (natp c))))
  (if (atom todo)
      t
    (mv-let (missp h cache2) (fn-clq-run demand (true-list-fix (car todo)))
      (declare (ignore h cache2))
      (and (true-listp (car todo))
           missp
           (member-equal (fn-clq-next demand (true-list-fix (car todo)) c) states)
           (fn-clq-trap-from (cdr todo) states demand c)))))

(defun fn-clq-trapp (states demand c)
  (declare (xargs :guard (and (true-listp states) (true-listp demand) (natp c))))
  (fn-clq-trap-from states states demand c))

(defthm fn-clq-true-list-fix-id
  (implies (true-listp x) (equal (true-list-fix x) x)))

(defthm fn-clq-trap-from-member
  (implies (and (fn-clq-trap-from todo states demand c) (member-equal s todo))
           (and (true-listp s)
                (mv-nth 0 (fn-clq-run demand s))
                (member-equal (fn-clq-next demand s c) states)))
  :hints (("Goal" :in-theory (disable fn-clq-run fn-clq-next fn-clq-run-missp fn-clq-run-missp-car))))

(local
 (defun fn-clq-orbit-ind (cache n demand c)
   (declare (xargs :measure (nfix n)))
   (if (zp n) (list cache demand c)
     (fn-clq-orbit-ind (fn-clq-next demand cache c) (- n 1) demand c))))

(defthm fn-clq-trapped-never-finishes
  (implies (and (fn-clq-trapp states demand c) (member-equal cache states))
           (not (mv-nth 1 (fn-clq-resume demand cache c n))))
  :hints (("Goal" :induct (fn-clq-orbit-ind cache n demand c)
           :in-theory (disable fn-clq-next fn-clq-resume fn-clq-run-missp fn-clq-run-missp-car
                               fn-clq-trap-from-member))
          ("Subgoal *1/2" :use ((:instance fn-clq-trap-from-member (todo states) (s cache))))
          ("Subgoal *1/1" :expand ((fn-clq-resume demand cache c n)))))

; The orbit of an empty cache under nine distinct reads at C = 8.

(defconst *fn-clq-nine-orbit*
  '(nil (1) (2 1) (3 2 1) (4 3 2 1) (5 4 3 2 1) (6 5 4 3 2 1) (7 6 5 4 3 2 1)
    (8 7 6 5 4 3 2 1) (9 8 7 6 5 4 3 2) (1 9 8 7 6 5 4 3) (2 1 9 8 7 6 5 4)
    (3 2 1 9 8 7 6 5) (4 3 2 1 9 8 7 6) (5 4 3 2 1 9 8 7) (6 5 4 3 2 1 9 8)
    (7 6 5 4 3 2 1 9)))

; TEETH (the 45e05c7fd defect in the model): nine reads, one more than the

; cache keeps, never finish from an empty cache, whatever N.

(defthm fn-clq-nine-reads-never-finish
  (not (mv-nth 1 (fn-clq-resume *fn-clq-nine* nil *fn-clq-cache-entries* n)))
  :hints (("Goal" :use ((:instance fn-clq-trapped-never-finishes
                         (states *fn-clq-nine-orbit*) (demand *fn-clq-nine*)
                         (c *fn-clq-cache-entries*) (cache nil)))
           :in-theory (disable fn-clq-trapped-never-finishes fn-clq-resume))))

; and the same nine reads as quanta of the served size do finish.

(defthm fn-clq-nine-reads-in-quanta-finish
  (and (mv-nth 1 (fn-clq-resume '(1 2 3 4) nil *fn-clq-cache-entries* 5))
       (mv-nth 1 (fn-clq-resume '(5 6 7 8) '(4 3 2 1) *fn-clq-cache-entries* 5))
       (mv-nth 1 (fn-clq-resume '(9) '(8 7 6 5 4 3 2 1) *fn-clq-cache-entries* 2))))

; A line: its quanta in order, each resumed until it finishes (the host

; gives a quantum as many runs as it takes; here (len q) + 1, the keystone's).

(defun fn-clq-line (quanta cache c)
  (declare (xargs :guard (and (true-list-listp quanta) (true-listp cache) (natp c))
                  :verify-guards nil))
  (if (atom quanta)
      (mv 0 t cache)
    (mv-let (runs donep cache2)
      (fn-clq-resume (car quanta) cache c (+ 1 (len (car quanta))))
      (if (not donep)
          (mv runs nil cache2)
        (mv-let (more donep2 cache3) (fn-clq-line (cdr quanta) cache2 c)
          (mv (+ runs more) donep2 cache3))))))

(defun fn-clq-fit (quanta c)
  (declare (xargs :guard (and (true-list-listp quanta) (natp c))))
  (if (atom quanta) t
    (and (<= (len (car quanta)) (nfix c)) (fn-clq-fit (cdr quanta) c))))

(defun fn-clq-line-reads (quanta)
  (declare (xargs :guard (true-list-listp quanta)))
  (if (atom quanta) 0 (+ (len (car quanta)) (fn-clq-line-reads (cdr quanta)))))

; LINE: a line whose every quantum fits the cache finishes, in at most its

; reads plus its quanta runs.

(defthm fn-clq-line-finishes
  (implies (and (posp c) (fn-clq-fit quanta c))
           (and (mv-nth 1 (fn-clq-line quanta cache c))
                (<= (mv-nth 0 (fn-clq-line quanta cache c))
                    (+ (fn-clq-line-reads quanta) (len quanta)))))
  :hints (("Goal" :induct (fn-clq-line quanta cache c)
           :in-theory (disable fn-clq-resume))
          ("Subgoal *1/3" :use ((:instance fn-clq-resume-finishes (demand (car quanta)))))
          ("Subgoal *1/2" :use ((:instance fn-clq-resume-finishes (demand (car quanta)))))))


; -----------------------------------------------------------------------------
; Lines cut into quanta

(local (include-book "arithmetic-5/top" :dir :system))

; A line's reads cut into quanta of Q: what the served cursors do.

(defun fn-clq-chunks (demand q)
  (declare (xargs :guard (and (true-listp demand) (posp q))
                  :measure (len demand)))
  (if (or (atom demand) (zp q))
      nil
    (cons (take (min q (len demand)) demand)
          (fn-clq-chunks (nthcdr (min q (len demand)) demand) q))))

(defthm fn-clq-len-take
  (equal (len (take n l)) (nfix n)))

(defthm fn-clq-nthcdr-nil
  (equal (nthcdr n nil) nil))

(defthm fn-clq-len-nthcdr
  (equal (len (nthcdr n l)) (nfix (- (len l) (nfix n))))
  :hints (("Goal" :induct (fn-clq-take-ind n l))))

(defthm fn-clq-chunks-fit
  (implies (and (natp q) (natp c) (<= q c))
           (fn-clq-fit (fn-clq-chunks demand q) c))
  :hints (("Goal" :induct (fn-clq-chunks demand q) :in-theory (disable take nthcdr))))

(defthm fn-clq-chunks-reads
  (implies (posp q)
           (equal (fn-clq-line-reads (fn-clq-chunks demand q)) (len demand)))
  :hints (("Goal" :induct (fn-clq-chunks demand q) :in-theory (disable take nthcdr))))

(defthm fn-clq-ceiling-small
  (implies (and (posp q) (posp n) (<= n q))
           (equal (ceiling n q) 1))
  :hints (("Goal" :nonlinearp t)))

(defthm fn-clq-ceiling-step
  (implies (and (posp q) (natp n) (< q n))
           (equal (ceiling n q) (+ 1 (ceiling (- n q) q)))))

(defun fn-clq-ceil (n q)
  (declare (xargs :guard (and (natp n) (posp q)) :measure (nfix n)))
  (if (or (zp n) (zp q)) 0
    (if (<= n q) 1 (+ 1 (fn-clq-ceil (- n q) q)))))

(defthm fn-clq-ceil-one
  (implies (and (posp n) (posp q) (<= n q))
           (equal (fn-clq-ceil n q) 1)))

(defthm fn-clq-ceil-step
  (implies (and (natp n) (posp q) (< q n))
           (equal (fn-clq-ceil n q) (+ 1 (fn-clq-ceil (- n q) q)))))

(defthm fn-clq-ceil-is-ceiling
  (implies (and (natp n) (posp q))
           (equal (fn-clq-ceil n q) (ceiling n q)))
  :hints (("Goal" :induct (fn-clq-ceil n q) :in-theory (disable ceiling))
          ("Subgoal *1/2" :use ((:instance fn-clq-ceiling-step)))
          ("Subgoal *1/1" :use ((:instance fn-clq-ceiling-small)))))

(defthm fn-clq-chunks-count
  (implies (posp q)
           (equal (len (fn-clq-chunks demand q)) (fn-clq-ceil (len demand) q)))
  :hints (("Goal" :induct (fn-clq-chunks demand q) :in-theory (disable take nthcdr fn-clq-ceil-is-ceiling))))

; KEYSTONE (the cold-line contract): a line that needs the N payload reads

; DEMAND, run as quanta of at most Q <= C reads, finishes from any cache, in

; ceiling(N/Q) quanta and at most N + ceiling(N/Q) runs.

(defthm fn-clq-quantized-line-finishes
  (implies (and (posp q) (natp c) (<= q c))
           (and (mv-nth 1 (fn-clq-line (fn-clq-chunks demand q) cache c))
                (equal (len (fn-clq-chunks demand q)) (ceiling (len demand) q))
                (<= (mv-nth 0 (fn-clq-line (fn-clq-chunks demand q) cache c))
                    (+ (len demand) (ceiling (len demand) q)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-clq-line fn-clq-chunks ceiling fn-clq-line-finishes)
           :use ((:instance fn-clq-line-finishes (quanta (fn-clq-chunks demand q)))))))

