; fn: the page store's keystones (lanes proto-pagestore and arena-store, 2026-09-27).
;
; Over the model of books/proto/pagestore.lisp (the two-level page table):
;   pgs-open-after-commit   commit-then-open denotes the committed state:
;                           after the complete commit of DIRTY on root R,
;                           R opens on the next transaction and the state
;                           with each dirty page replaced (or appended).
;   pgs-open-after-crash    a crash anywhere in that commit (any subset of
;                           its page, table-page and directory writes
;                           reached the disk; the record old, torn or new)
;                           opens on the committed state or on the previous
;                           one, and on the previous one whenever the record
;                           did not land.
;   pgs-crash-isolates-other-roots, pgs-fork-denotes
;                           fork isolation: a commit (complete or crashed)
;                           on R leaves every other root's open unchanged,
;                           and a fork opens on its source's state.
;   pgs-alloc-fresh         allocation is complete and fresh: over an
;                           allocator state whose free list avoids every
;                           kept address (`pgs-alloc-inv'), it always
;                           answers, with distinct addresses no valid record
;                           of any root keeps.
; The keystones' only hypotheses about the commit are that R opens, the
; dirty pages are in order (`pgs-lpages-ok'), and the allocator invariant.
; The torn-write keystone also takes `pgs-writes-faithful' (a stale page
; whose digest equals the intended page's IS that page: A-CRYPTO's collision
; resistance, instantiated) and a torn record that fails its check; the test
; book shows both are needed.
(in-package "ACL2")
(include-book "pagestore")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; Table pages: cutting a flat table and joining it again.

(defthm pgs-take-of-append-exact
  (implies (and (true-listp a) (equal (len a) n))
           (equal (take n (append a b)) a)))

(defthm pgs-nthcdr-of-append-exact
  (implies (equal (len a) n)
           (equal (nthcdr n (append a b)) b))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n a))))

(defthm pgs-append-take-nthcdr
  (implies (<= (nfix n) (len x))
           (equal (append (take n x) (nthcdr n x)) x))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

(defthm pgs-len-of-take
  (equal (len (take n x)) (nfix n)))

(defthm pgs-take-when-len
  (implies (and (true-listp x) (equal (len x) n)) (equal (take n x) x)))

(defthm pgs-nthcdr-too-far
  (implies (and (true-listp x) (<= (len x) (nfix n)))
           (equal (nthcdr n x) nil))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

(defthm pgs-flatten-of-chunk
  (implies (true-listp x)
           (equal (pgs-flatten (pgs-chunk x)) x))
  :hints (("Goal" :induct (pgs-chunk x))))

(defthm pgs-len-of-chunk
  (equal (len (pgs-chunk x)) (pgs-ntables (len x)))
  :hints (("Goal" :induct (pgs-chunk x) :expand ((pgs-ntables (len x))))))

(defthm pgs-ptab-p-of-take
  (implies (and (pgs-ptab-p x) (<= (nfix n) (len x)))
           (pgs-ptab-p (take n x))))

(defthm pgs-txids-ok-of-take
  (implies (and (pgs-ptab-txids-ok x txid) (<= (nfix n) (len x)))
           (pgs-ptab-txids-ok (take n x) txid)))

(defthm pgs-ptab-p-of-nthcdr
  (implies (pgs-ptab-p x) (pgs-ptab-p (nthcdr n x)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

(defthm pgs-txids-ok-of-nthcdr
  (implies (pgs-ptab-txids-ok x txid) (pgs-ptab-txids-ok (nthcdr n x) txid))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

; A well-formed flat table cuts into well-formed table pages.
(defun pgs-chunk-ind (p rem i)
  (declare (xargs :measure (len p)))
  (if (atom p) (list rem i) (pgs-chunk-ind (nthcdr *pgs-tab-entries* p) (- (nfix rem) *pgs-tab-entries*) (+ 1 i))))

(defthm pgs-tables-verdict-of-chunk-gen
  (implies (and (pgs-ptab-p p) (pgs-ptab-txids-ok p txid) (equal (nfix rem) (len p)))
           (equal (pgs-tables-verdict (pgs-chunk p) rem txid i) nil))
  :hints (("Goal" :induct (pgs-chunk-ind p rem i))))

(defthm pgs-tables-verdict-of-chunk
  (implies (and (pgs-ptab-p p) (pgs-ptab-txids-ok p txid))
           (equal (pgs-tables-verdict (pgs-chunk p) (len p) txid i) nil)))

; The converse: well-formed table pages join into a well-formed flat table
; that cuts back into the same table pages.
(defthm pgs-ntables-of-small
  (implies (and (integerp n) (< 0 n) (<= n *pgs-tab-entries*))
           (equal (pgs-ntables n) 1))
  :hints (("Goal" :expand ((pgs-ntables n) (pgs-ntables (- n 341))))))

(defthm pgs-ntables-zero
  (implies (zp n) (equal (pgs-ntables n) 0))
  :hints (("Goal" :expand ((pgs-ntables n)))))

(defthm pgs-ntables-step
  (implies (and (integerp n) (< *pgs-tab-entries* n))
           (equal (pgs-ntables n) (+ 1 (pgs-ntables (- n *pgs-tab-entries*)))))
  :hints (("Goal" :expand ((pgs-ntables n)))))

(defthm pgs-ptab-p-of-true-list-fix
  (implies (pgs-ptab-p x) (equal (true-list-fix x) x)))

(defthm pgs-txids-ok-of-append
  (equal (pgs-ptab-txids-ok (append a b) txid)
         (and (pgs-ptab-txids-ok a txid) (pgs-ptab-txids-ok b txid))))

(defthm pgs-len-of-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm pgs-consp-of-append
  (equal (consp (append a b)) (or (consp a) (consp b))))

(defthm pgs-len-zero-atom
  (equal (equal (len x) 0) (atom x)))

(defthm pgs-tables-ok-join
  (implies (and (not (pgs-tables-verdict cs rem txid i))
                (equal (len cs) (pgs-ntables (nfix rem))))
           (and (equal (pgs-chunk (pgs-flatten cs)) (true-list-fix cs))
                (equal (len (pgs-flatten cs)) (nfix rem))
                (pgs-ptab-txids-ok (pgs-flatten cs) txid)))
  :hints (("Goal" :induct (pgs-tables-verdict cs rem txid i)
                  :expand ((pgs-ntables (nfix rem))))))

; -----------------------------------------------------------------------------
; Table-page arithmetic: logical page L lies in table page floor(L / E).

(defun pgs-nt-ind (tp n)
  (declare (xargs :measure (nfix tp)))
  (if (or (zp tp) (zp n)) (list tp n) (pgs-nt-ind (1- tp) (nfix (- n *pgs-tab-entries*)))))

(defthm pgs-ntables-bound
  ; T is a table page of a table of N entries exactly when T*E < N.
  (implies (and (natp tp) (natp n))
           (iff (< tp (pgs-ntables n)) (< (* *pgs-tab-entries* tp) n)))
  :hints (("Goal" :induct (pgs-nt-ind tp n)
                  :in-theory (disable pgs-ntables-step)
                  :expand ((pgs-ntables n)))))

(defun pgs-nt-ind2 (a b)
  (declare (xargs :measure (nfix a)))
  (if (or (zp a) (zp b)) (list a b)
    (pgs-nt-ind2 (nfix (- a *pgs-tab-entries*)) (nfix (- b *pgs-tab-entries*)))))

(defthm pgs-ntables-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (pgs-ntables a) (pgs-ntables b)))
  :rule-classes :linear
  :hints (("Goal" :induct (pgs-nt-ind2 a b)
                  :in-theory (disable pgs-ntables-step)
                  :expand ((pgs-ntables a) (pgs-ntables b)))))

(defthm pgs-floor-bounds-raw
  (implies (natp l)
           (and (integerp (floor l 341)) (<= 0 (floor l 341))
                (<= (* 341 (floor l 341)) l)
                (< l (+ 341 (* 341 (floor l 341))))))
  :hints (("Goal" :in-theory (disable floor)
                  :use ((:instance floor-bounded-by-/ (x l) (y 341)))))
  :rule-classes nil)

(defthm pgs-floor-bounds
  (implies (natp l)
           (and (natp (floor l *pgs-tab-entries*))
                (<= (* *pgs-tab-entries* (floor l *pgs-tab-entries*)) l)
                (< l (+ *pgs-tab-entries* (* *pgs-tab-entries* (floor l *pgs-tab-entries*))))))
  :hints (("Goal" :use pgs-floor-bounds-raw :in-theory (disable floor)))
  :rule-classes ((:linear :corollary
                  (implies (natp l)
                           (and (<= (* *pgs-tab-entries* (floor l *pgs-tab-entries*)) l)
                                (< l (+ *pgs-tab-entries* (* *pgs-tab-entries* (floor l *pgs-tab-entries*)))))))
                 (:type-prescription :corollary
                  (implies (natp l) (natp (floor l *pgs-tab-entries*))))))

(defthm pgs-floor-unique
  (implies (and (natp l) (natp tp)
                (<= (* *pgs-tab-entries* tp) l)
                (< l (+ *pgs-tab-entries* (* *pgs-tab-entries* tp))))
           (equal (floor l *pgs-tab-entries*) tp))
  :hints (("Goal" :use pgs-floor-bounds-raw :in-theory (disable floor pgs-floor-bounds))))

(defthm pgs-floor-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (floor a *pgs-tab-entries*) (floor b *pgs-tab-entries*)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance pgs-floor-bounds-raw (l a)) (:instance pgs-floor-bounds-raw (l b)))
                  :in-theory (disable floor pgs-floor-bounds))))

(in-theory (disable floor))

; -----------------------------------------------------------------------------
; A table page is a window of the flat table; an update outside it keeps it.

(defun pgs-window (tp p)
  (take (min *pgs-tab-entries* (nfix (- (len p) (* *pgs-tab-entries* (nfix tp)))))
        (nthcdr (* *pgs-tab-entries* (nfix tp)) p)))

(defthm pgs-nthcdr-nthcdr
  (equal (nthcdr a (nthcdr b x)) (nthcdr (+ (nfix a) (nfix b)) x))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr b x))))

(defun pgs-win-ind (tp p)
  (declare (xargs :measure (len p)))
  (if (or (zp tp) (atom p)) (list tp p) (pgs-win-ind (1- tp) (nthcdr *pgs-tab-entries* p))))

(defthm pgs-nth-of-chunk
  (implies (and (natp tp) (< tp (len (pgs-chunk p))))
           (equal (nth tp (pgs-chunk p)) (pgs-window tp p)))
  :hints (("Goal" :induct (pgs-win-ind tp p) :expand ((pgs-chunk p))
                  :in-theory (disable pgs-len-of-chunk))))

(defthm pgs-nthcdr-of-update-nth-below
  (implies (and (natp l) (natp k) (< l k))
           (equal (nthcdr k (update-nth l e p)) (nthcdr k p)))
  :hints (("Goal" :in-theory (enable nthcdr update-nth) :induct (list (nthcdr k p) (update-nth l e p)))))

(defthm pgs-nthcdr-of-update-nth-above
  (implies (and (natp l) (natp k) (<= k l) (< l (len p)))
           (equal (nthcdr k (update-nth l e p)) (update-nth (- l k) e (nthcdr k p))))
  :hints (("Goal" :in-theory (enable nthcdr update-nth) :induct (list (nthcdr k p) (update-nth l e p)))))

(defthm pgs-take-of-update-nth-beyond
  (implies (and (natp j) (natp n) (<= n j))
           (equal (take n (update-nth j e x)) (take n x)))
  :hints (("Goal" :in-theory (enable update-nth) :induct (list (take n x) (update-nth j e x)))))

(defthm pgs-nthcdr-of-append-short
  (implies (<= (nfix k) (len p))
           (equal (nthcdr k (append p q)) (append (nthcdr k p) q)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr k p))))

(defthm pgs-take-of-append-short
  (implies (<= (nfix n) (len a))
           (equal (take n (append a b)) (take n a))))

(defthm pgs-len-of-update-nth-inside
  (implies (< (nfix l) (len p))
           (equal (len (update-nth l e p)) (len p))))

(defthm pgs-window-of-update-entry-nat
  (implies (and (natp l) (natp tp)
                (< (* *pgs-tab-entries* tp) (len p))
                (not (and (<= (* *pgs-tab-entries* tp) l)
                          (< l (+ *pgs-tab-entries* (* *pgs-tab-entries* tp))))))
           (equal (pgs-window tp (pgs-update-entry l e p)) (pgs-window tp p)))
  :rule-classes nil)

(defthm pgs-window-of-update-entry-before
  (implies (and (natp tp)
                (< (* *pgs-tab-entries* tp) (len p))
                (< (nfix l) (* *pgs-tab-entries* tp)))
           (equal (pgs-window tp (pgs-update-entry l e p)) (pgs-window tp p)))
  :hints (("Goal" :use ((:instance pgs-window-of-update-entry-nat (l (nfix l))))
                  :in-theory (disable pgs-window))))

(defthm pgs-window-of-update-entry-after
  (implies (and (natp tp)
                (< (* *pgs-tab-entries* tp) (len p))
                (<= (+ *pgs-tab-entries* (* *pgs-tab-entries* tp)) (nfix l)))
           (equal (pgs-window tp (pgs-update-entry l e p)) (pgs-window tp p)))
  :hints (("Goal" :use ((:instance pgs-window-of-update-entry-nat (l (nfix l))))
                  :in-theory (disable pgs-window))))

(defun pgs-avoids-window (ls tp)
  (if (atom ls)
      t
    (and (not (and (<= (* *pgs-tab-entries* tp) (nfix (car ls)))
                   (< (nfix (car ls)) (+ *pgs-tab-entries* (* *pgs-tab-entries* tp)))))
         (pgs-avoids-window (cdr ls) tp))))

(defthm pgs-len-of-update-entry-grows
  (<= (len p) (len (pgs-update-entry l e p)))
  :rule-classes :linear)

(defthm pgs-window-of-plan-ptab
  (implies (and (natp tp) (< (* *pgs-tab-entries* tp) (len p))
                (pgs-avoids-window lpages tp))
           (equal (pgs-window tp (pgs-plan-ptab p lpages fresh digests txid))
                  (pgs-window tp p)))
  :hints (("Goal" :induct (pgs-plan-ptab p lpages fresh digests txid)
                  :in-theory (disable pgs-window pgs-update-entry nfix))))

; -----------------------------------------------------------------------------
; The touched table pages.

(defthm pgs-touched-covers
  ; Every dirty page's table page is touched (or is PREV).
  (implies (member-equal l ls)
           (or (equal (floor (nfix l) *pgs-tab-entries*) prev)
               (member-equal (floor (nfix l) *pgs-tab-entries*) (pgs-touched ls prev))))
  :rule-classes nil)

(defthm pgs-member-touched-of-floor
  (implies (member-equal l ls)
           (member-equal (floor (nfix l) *pgs-tab-entries*) (pgs-touched ls nil)))
  :hints (("Goal" :use ((:instance pgs-touched-covers (prev nil))))))

(defthm pgs-avoids-window-of-untouched-gen
  (implies (and (natp tp) (nat-listp ls) (not (equal tp prev))
                (not (member-equal tp (pgs-touched ls prev))))
           (pgs-avoids-window ls tp))
  :hints (("Goal" :induct (pgs-touched ls prev))
          ("Subgoal *1/3" :use ((:instance pgs-floor-unique (l (car ls)))))
          ("Subgoal *1/2" :use ((:instance pgs-floor-unique (l (car ls)))))))

(defthm pgs-avoids-window-of-untouched
  (implies (and (natp tp) (nat-listp ls)
                (not (member-equal tp (pgs-touched ls nil))))
           (pgs-avoids-window ls tp)))

(defun pgs-asc-above (s prev)
  ; S strictly ascending naturals, each above PREV (nil: no bound).
  (if (atom s)
      (null s)
    (and (natp (car s))
         (or (null prev) (and (natp prev) (< prev (car s))))
         (pgs-asc-above (cdr s) (car s)))))

(defthm pgs-lpages-ok-nat-listp
  (implies (pgs-lpages-ok ls n lo) (nat-listp ls)))

(defthm pgs-touched-ascending
  (implies (and (pgs-lpages-ok ls n lo) (natp lo)
                (or (null prev)
                    (and (natp prev) (<= prev (floor lo *pgs-tab-entries*)))))
           (pgs-asc-above (pgs-touched ls prev) prev))
  :hints (("Goal" :induct (list (pgs-lpages-ok ls n lo) (pgs-touched ls prev)))))

(defthm pgs-lpages-below-grown
  (implies (and (pgs-lpages-ok ls n lo) (member-equal l ls))
           (< l (pgs-grown-len ls n)))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-lpages-ok ls n lo))))

(defun pgs-all-below (s bound)
  (if (atom s) t (and (< (car s) bound) (pgs-all-below (cdr s) bound))))

(defthm pgs-grown-len-monotone
  (<= (nfix n) (pgs-grown-len ls n))
  :rule-classes :linear)

(defthm pgs-touched-below-gen
  (implies (and (pgs-lpages-ok ls n lo)
                (natp m) (<= (pgs-grown-len ls n) m))
           (pgs-all-below (pgs-touched ls prev) (pgs-ntables m)))
  :hints (("Goal" :induct (list (pgs-lpages-ok ls n lo) (pgs-touched ls prev)))
          ("Subgoal *1/2" :use ((:instance pgs-lpages-below-grown (l (car ls)))
                                (:instance pgs-ntables-bound (tp (floor (car ls) *pgs-tab-entries*)) (n m))))))

(defthm pgs-touched-below
  (implies (pgs-lpages-ok ls n lo)
           (pgs-all-below (pgs-touched ls prev) (pgs-ntables (pgs-grown-len ls n)))))

; -----------------------------------------------------------------------------
; Growth: the table's length after the commit, and the new pages are dirty.

(defthm pgs-len-of-update-entry
  (equal (len (pgs-update-entry i e ptab))
         (if (equal (nfix i) (len ptab)) (+ 1 (len ptab)) (len ptab))))

(defthm pgs-len-of-plan-ptab
  (equal (len (pgs-plan-ptab ptab lpages fresh digests txid))
         (pgs-grown-len lpages (len ptab)))
  :hints (("Goal" :induct (pgs-plan-ptab ptab lpages fresh digests txid)
                  :in-theory (disable pgs-update-entry))))

(defthm pgs-lpages-cover-growth
  (implies (and (pgs-lpages-ok ls n lo) (natp x) (<= (nfix n) x) (< x (pgs-grown-len ls n)))
           (member-equal x ls))
  :hints (("Goal" :induct (pgs-lpages-ok ls n lo))))

; -----------------------------------------------------------------------------
; Rewriting only the touched table pages rebuilds the table pages of the new
; flat table: if C agrees with C2 everywhere outside S, and S (ascending)
; covers every table page C2 adds, replacing (or appending) each table page
; in S by C2's gives C2.

(defun pgs-agree (c c2 s i)
  ; Position I+J of C equals C2's, or is in S, for every J below |C|.
  (if (atom c)
      t
    (and (or (member-equal i s) (and (consp c2) (equal (car c) (car c2))))
         (pgs-agree (cdr c) (if (consp c2) (cdr c2) nil) s (+ 1 i)))))

(defun pgs-covers (s lo hi)
  (declare (xargs :measure (nfix (- (nfix hi) (nfix lo)))))
  (if (and (natp lo) (natp hi) (< lo hi))
      (and (member-equal lo s) (pgs-covers s (+ 1 lo) hi))
    t))

(defthm pgs-agree-ext
  (implies (and (true-listp a) (true-listp b) (equal (len a) (len b))
                (pgs-agree a b nil i))
           (equal a b))
  :rule-classes nil)

(defthm pgs-agree-of-update-nth
  (implies (and (pgs-agree c c2 (cons s0 rest) i) (natp i) (natp s0) (<= i s0)
                (< s0 (+ i (len c))) (< s0 (+ i (len c2))))
           (pgs-agree (update-nth (- s0 i) (nth (- s0 i) c2) c) c2 rest i))
  :hints (("Goal" :induct (pgs-agree c c2 (cons s0 rest) i)
                  :in-theory (enable update-nth))))

(defthm pgs-agree-of-append-next
  (implies (and (pgs-agree c c2 (cons s0 rest) i) (natp i)
                (equal s0 (+ i (len c))) (< s0 (+ i (len c2))))
           (pgs-agree (append c (list (nth (- s0 i) c2))) c2 rest i))
  :hints (("Goal" :induct (pgs-agree c c2 (cons s0 rest) i))))

(defthm pgs-covers-step
  (implies (and (natp lo) (pgs-covers s lo hi)) (pgs-covers s (+ 1 lo) hi)))

(defthm pgs-covers-drop
  (implies (and (pgs-covers (cons s0 rest) lo hi) (natp lo) (natp s0) (< s0 lo))
           (pgs-covers rest lo hi)))

(defthm pgs-asc-above-member
  (implies (and (pgs-asc-above s prev) (member-equal x s) prev)
           (< prev x))
  :rule-classes nil)

(defthm pgs-asc-above-member-nil
  (implies (and (pgs-asc-above s nil) (consp s) (member-equal x (cdr s)))
           (< (car s) x))
  :hints (("Goal" :use ((:instance pgs-asc-above-member (s (cdr s)) (prev (car s)))))))

(defthm pgs-agree-of-update-nth-0
  (implies (and (pgs-agree c c2 (cons s0 rest) 0) (natp s0)
                (< s0 (len c)) (< s0 (len c2)))
           (pgs-agree (update-nth s0 (nth s0 c2) c) c2 rest 0))
  :hints (("Goal" :use ((:instance pgs-agree-of-update-nth (i 0))))))

(defthm pgs-agree-of-append-next-0
  (implies (and (pgs-agree c c2 (cons s0 rest) 0)
                (equal s0 (len c)) (< s0 (len c2)))
           (pgs-agree (append c (list (nth s0 c2))) c2 rest 0))
  :hints (("Goal" :use ((:instance pgs-agree-of-append-next (i 0))))))

(defthm pgs-covers-first
  (implies (and (pgs-asc-above s nil) (consp s) (pgs-covers s lo hi)
                (natp lo) (natp hi) (< lo hi))
           (<= (car s) lo))
  :rule-classes nil
  :hints (("Goal" :expand ((pgs-covers s lo hi))
                  :use ((:instance pgs-asc-above-member-nil (x lo))))))

(defun pgs-rl-ind (s c c2)
  (if (atom s)
      (list c c2)
    (pgs-rl-ind (cdr s)
                (let ((i (nfix (car s))))
                  (cond ((< i (len c)) (update-nth i (nth i c2) c))
                        ((equal i (len c)) (append c (list (nth i c2))))
                        (t c)))
                c2)))

(defthm pgs-asc-above-weaken
  (implies (and (pgs-asc-above s prev) prev) (pgs-asc-above s nil)))

(defthm pgs-rebuild-tables
  (implies (and (true-listp c) (true-listp c2)
                (pgs-asc-above s nil) (pgs-all-below s (len c2))
                (<= (len c) (len c2))
                (pgs-covers s (len c) (len c2))
                (pgs-agree c c2 s 0))
           (equal (pgs-apply-dirty c (pgs-table-dirty s c2)) c2))
  :hints (("Goal" :induct (pgs-rl-ind s c c2))
          ("Subgoal *1/2" :use ((:instance pgs-covers-first (lo (len c)) (hi (len c2)))))
          ("Subgoal *1/1" :use ((:instance pgs-agree-ext (a c) (b c2) (i 0))))))

; The commit's instance: the table pages after the commit are the old ones
; with the touched ones replaced.

(defun pgs-agree-at (c c2 s i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (and (or (member-equal i s) (equal (nth i c) (nth i c2)))
           (pgs-agree-at c c2 s (+ 1 i) n))
    t))

(defthm pgs-car-nthcdr
  (equal (car (nthcdr i x)) (nth i x))
  :hints (("Goal" :in-theory (enable nthcdr nth))))

(defthm pgs-cdr-nthcdr
  (equal (cdr (nthcdr i x)) (nthcdr (+ 1 (nfix i)) x))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthmd pgs-consp-iff-len
  (equal (consp y) (< 0 (len y))))

(defthm pgs-consp-nthcdr
  (equal (consp (nthcdr i x)) (< (nfix i) (len x)))
  :hints (("Goal" :use ((:instance pgs-len-of-nthcdr (n i))
                        (:instance pgs-consp-iff-len (y (nthcdr i x))))
                  :in-theory (disable nthcdr pgs-len-of-nthcdr))))

(defun pgs-ag-ind (i c)
  (declare (xargs :measure (nfix (- (len c) (nfix i)))))
  (if (and (natp i) (< i (len c))) (pgs-ag-ind (+ 1 i) c) i))

(defthm pgs-agree-from-agree-at-gen
  (implies (and (natp i) (<= (len c) (len c2)) (pgs-agree-at c c2 s i (len c)))
           (pgs-agree (nthcdr i c) (nthcdr i c2) s i))
  :hints (("Goal" :induct (pgs-ag-ind i c)
                  :in-theory (disable pgs-agree-at pgs-agree nthcdr nth pgs-len-of-nthcdr)
                  :expand ((pgs-agree-at c c2 s i (len c))
                           (pgs-agree (nthcdr i c) (nthcdr i c2) s i)))))

(defthm pgs-agree-from-agree-at
  (implies (and (<= (len c) (len c2)) (pgs-agree-at c c2 s 0 (len c)))
           (pgs-agree c c2 s 0))
  :hints (("Goal" :use ((:instance pgs-agree-from-agree-at-gen (i 0))))))

(defthm pgs-true-listp-of-chunk
  (true-listp (pgs-chunk x)))

(defthm pgs-nth-chunk-untouched
  (implies (and (pgs-lpages-ok ls (len p) 0)
                (natp tp) (< tp (len (pgs-chunk p)))
                (not (member-equal tp (pgs-touched ls nil))))
           (equal (nth tp (pgs-chunk (pgs-plan-ptab p ls fresh digests txid)))
                  (nth tp (pgs-chunk p))))
  :hints (("Goal" :in-theory (union-theories '(pgs-len-of-chunk pgs-len-of-plan-ptab)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-ntables-bound (n (len p)))
                        (:instance pgs-ntables-monotone (a (len p)) (b (pgs-grown-len ls (len p))))
                        (:instance pgs-grown-len-monotone (n (len p)))
                        (:instance pgs-nth-of-chunk (p p))
                        (:instance pgs-nth-of-chunk (p (pgs-plan-ptab p ls fresh digests txid)))
                        (:instance pgs-window-of-plan-ptab (lpages ls))
                        (:instance pgs-lpages-ok-nat-listp (n (len p)) (lo 0))
                        (:instance pgs-avoids-window-of-untouched)))
          (and stable-under-simplificationp
               '(:in-theory (enable natp nfix)))))

(defthm pgs-agree-at-chunks
  (implies (and (pgs-lpages-ok ls (len p) 0) (natp i))
           (pgs-agree-at (pgs-chunk p) (pgs-chunk (pgs-plan-ptab p ls fresh digests txid))
                         (pgs-touched ls nil) i (len (pgs-chunk p))))
  :hints (("Goal" :induct (pgs-agree-at (pgs-chunk p) (pgs-chunk (pgs-plan-ptab p ls fresh digests txid))
                                        (pgs-touched ls nil) i (len (pgs-chunk p)))
                  :in-theory (disable pgs-len-of-chunk pgs-plan-ptab pgs-chunk pgs-touched
                                      pgs-lpages-ok pgs-nth-of-chunk))))

(defthm pgs-touched-growth-member
  (implies (and (pgs-lpages-ok ls n 0) (natp n) (natp lo)
                (<= (pgs-ntables n) lo) (< lo (pgs-ntables (pgs-grown-len ls n))))
           (member-equal lo (pgs-touched ls nil)))
  :hints (("Goal" :in-theory (union-theories '(nfix natp) (theory 'minimal-theory))
                  :use ((:instance pgs-ntables-bound (tp lo) (n n))
                        (:instance pgs-ntables-bound (tp lo) (n (pgs-grown-len ls n)))
                        (:instance pgs-lpages-cover-growth (lo 0) (x (* *pgs-tab-entries* lo)))
                        (:instance pgs-member-touched-of-floor (l (* *pgs-tab-entries* lo)))
                        (:instance pgs-floor-unique (l (* *pgs-tab-entries* lo)) (tp lo))))
          (and stable-under-simplificationp
               '(:in-theory (enable natp nfix)))))

(defthm pgs-covers-growth
  (implies (and (pgs-lpages-ok ls n 0) (natp n) (natp lo) (<= (pgs-ntables n) lo))
           (pgs-covers (pgs-touched ls nil) lo (pgs-ntables (pgs-grown-len ls n))))
  :hints (("Goal" :induct (pgs-covers (pgs-touched ls nil) lo (pgs-ntables (pgs-grown-len ls n)))
                  :in-theory (disable pgs-touched pgs-lpages-ok pgs-grown-len pgs-ntables))))

(defthm pgs-tables-after-plan
  (implies (and (pgs-ptab-p p) (pgs-lpages-ok ls (len p) 0))
           (equal (pgs-apply-dirty (pgs-chunk p)
                                   (pgs-table-dirty (pgs-touched ls nil)
                                                    (pgs-chunk (pgs-plan-ptab p ls fresh digests txid))))
                  (pgs-chunk (pgs-plan-ptab p ls fresh digests txid))))
  :hints (("Goal" :in-theory (disable pgs-plan-ptab pgs-touched pgs-chunk pgs-apply-dirty
                                      pgs-table-dirty pgs-rebuild-tables)
                  :use ((:instance pgs-rebuild-tables
                                   (c (pgs-chunk p))
                                   (c2 (pgs-chunk (pgs-plan-ptab p ls fresh digests txid)))
                                   (s (pgs-touched ls nil)))
                        (:instance pgs-touched-ascending (n (len p)) (lo 0) (prev nil))
                        (:instance pgs-touched-below (n (len p)) (lo 0) (prev nil))
                        (:instance pgs-ntables-monotone (a (len p)) (b (pgs-grown-len ls (len p))))
                        (:instance pgs-covers-growth (n (len p)) (lo (pgs-ntables (len p))))
                        (:instance pgs-agree-from-agree-at
                                   (c (pgs-chunk p))
                                   (c2 (pgs-chunk (pgs-plan-ptab p ls fresh digests txid)))
                                   (s (pgs-touched ls nil)))
                        (:instance pgs-agree-at-chunks (i 0))))))
