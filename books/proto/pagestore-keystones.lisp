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

(defthm pgs-grown-len-monotone
  (<= (nfix n) (pgs-grown-len ls n))
  :rule-classes :linear)

(defthm pgs-lpages-below-grown
  (implies (and (pgs-lpages-ok ls n lo) (member-equal l ls))
           (< l (pgs-grown-len ls n)))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-lpages-ok ls n lo))
          ("Subgoal *1/2" :use ((:instance pgs-grown-len-monotone
                                           (ls (cdr ls))
                                           (n (if (equal (car ls) (nfix n)) (+ 1 (nfix n)) n)))))))

(defun pgs-all-below (s bound)
  (if (atom s) t (and (< (car s) bound) (pgs-all-below (cdr s) bound))))

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
  (implies (and (natp lo) (pgs-covers s lo hi)) (pgs-covers s (+ 1 lo) hi))
  :hints (("Goal" :expand ((pgs-covers s (+ 1 lo) hi) (pgs-covers s lo hi)))))

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

; -----------------------------------------------------------------------------
; Writes and the addresses they touch.

(defun pgs-write-addrs (writes)
  (if (atom writes)
      nil
    (if (consp (car writes))
        (cons (caar writes) (pgs-write-addrs (cdr writes)))
      (pgs-write-addrs (cdr writes)))))

(defun pgs-avoids (xs ys)
  ; No element of XS is in YS.
  (if (atom xs) t (and (not (member-equal (car xs) ys)) (pgs-avoids (cdr xs) ys))))

(defthm pgs-lookup-of-apply-pages-outside
  (implies (not (member-equal a (pgs-write-addrs writes)))
           (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                  (pgs-lookup a pages))))

(defthm pgs-lookup-of-cons
  (equal (pgs-lookup a (cons (cons b c) pages))
         (if (equal a b) c (pgs-lookup a pages))))

(in-theory (disable pgs-lookup))

; -----------------------------------------------------------------------------
; Locality: a record's try reads only the addresses it keeps.

(defthm pgs-check-pages-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-check-pages ptab txid mode (pgs-apply-pages writes keep pages) i tag)
                  (pgs-check-pages ptab txid mode pages i tag))))

(defthm pgs-contents-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-contents ptab (pgs-apply-pages writes keep pages))
                  (pgs-contents ptab pages)))
  :hints (("Goal" :induct (pgs-ptab-physes ptab))))

(defthm pgs-avoids-append
  (equal (pgs-avoids (append xs ys) zs)
         (and (pgs-avoids xs zs) (pgs-avoids ys zs))))

(defthm pgs-run-first
  (implies (not (zp m)) (member-equal a (pgs-run a m))))

(defthm pgs-avoids-member
  (implies (and (pgs-avoids xs ys) (member-equal a xs))
           (not (member-equal a ys))))

(defthm pgs-ptab-run-pages-posp
  (and (integerp (pgs-ptab-run-pages n)) (< 0 (pgs-ptab-run-pages n)))
  :rule-classes ((:type-prescription :corollary (integerp (pgs-ptab-run-pages n)))
                 (:linear :corollary (< 0 (pgs-ptab-run-pages n)))))

(defthm pgs-rec-keeps-avoids-addr
  (implies (pgs-avoids (pgs-rec-keeps rec dir tables) w)
           (not (member-equal (pgs-rec-dir-addr rec) w)))
  :hints (("Goal" :in-theory (disable pgs-run-first pgs-avoids-member pgs-rec-dir-addr)
                  :use ((:instance pgs-run-first
                                   (a (pgs-rec-dir-addr rec))
                                   (m (pgs-dir-run-pages (pgs-rec-npages rec))))
                        (:instance pgs-avoids-member
                                   (a (pgs-rec-dir-addr rec)) (ys w)
                                   (xs (pgs-run (pgs-rec-dir-addr rec)
                                                (pgs-dir-run-pages (pgs-rec-npages rec)))))))))

(defthm pgs-rec-keeps-avoids-dir
  (implies (and (pgs-ptab-p dir) (pgs-avoids (pgs-rec-keeps rec dir tables) w))
           (pgs-avoids (pgs-ptab-physes dir) w)))

(defthm pgs-rec-keeps-avoids-table
  (implies (and (pgs-ptab-p dir) (pgs-ptab-p (pgs-flatten tables))
                (pgs-avoids (pgs-rec-keeps rec dir tables) w))
           (pgs-avoids (pgs-ptab-physes (pgs-flatten tables)) w)))

(in-theory (disable pgs-rec-keeps))

(defthm pgs-dir-verdict-when-not-ptab-p
  (implies (not (pgs-ptab-p dir))
           (pgs-dir-verdict rec dir observed)))

(defthm pgs-try-of-apply-pages
  (implies (pgs-avoids (pgs-rec-keeps-in rec pages) (pgs-write-addrs writes))
           (equal (pgs-try rec (pgs-apply-pages writes keep pages) mode)
                  (pgs-try rec pages mode)))
  :hints (("Goal" :in-theory (disable pgs-check-pages pgs-contents pgs-dir-verdict pgs-tables-verdict
                                      pgs-ptab-p pgs-apply-pages pgs-flatten
                                      pgs-rec-dir-addr pgs-rec-txid pgs-rec-npages
                                      pgs-rec-dir-digest pgs-rec-keeps-avoids-addr)
                  :cases ((pgs-ptab-p (pgs-lookup (pgs-rec-dir-addr rec) pages)))
                  :use ((:instance pgs-rec-keeps-avoids-addr
                                   (dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
                                   (tables (if (pgs-ptab-p (pgs-lookup (pgs-rec-dir-addr rec) pages))
                                               (pgs-contents (pgs-lookup (pgs-rec-dir-addr rec) pages) pages)
                                             nil))
                                   (w (pgs-write-addrs writes)))))))

(defun pgs-order-valid (order slots)
  (if (atom order)
      t
    (and (member-equal (car order) '(0 1))
         (pgs-rec-valid (pgs-slot (car order) slots))
         (pgs-order-valid (cdr order) slots))))

(defthm pgs-order-valid-of-open-order
  (pgs-order-valid (pgs-open-order (pgs-slot 0 slots) (pgs-rec-valid (pgs-slot 0 slots))
                                   (pgs-slot 1 slots) (pgs-rec-valid (pgs-slot 1 slots)))
                   slots))

(defthm pgs-slot-keeps-avoid
  (implies (and (pgs-avoids (pgs-slots-keeps slots pages) w)
                (member-equal k '(0 1))
                (pgs-rec-valid (pgs-slot k slots)))
           (pgs-avoids (pgs-rec-keeps-in (pgs-slot k slots) pages) w))
  :hints (("Goal" :in-theory (disable pgs-rec-valid pgs-slot pgs-rec-keeps-in))))

(defthm pgs-try-slot-of-apply-pages
  (implies (and (member-equal k '(0 1))
                (pgs-rec-valid (pgs-slot k slots))
                (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes)))
           (equal (pgs-try (pgs-slot k slots) (pgs-apply-pages writes keep pages) mode)
                  (pgs-try (pgs-slot k slots) pages mode)))
  :hints (("Goal" :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-rec-keeps-in pgs-apply-pages
                                      pgs-slot-keeps-avoid pgs-try-of-apply-pages)
                  :use ((:instance pgs-slot-keeps-avoid (w (pgs-write-addrs writes)))
                        (:instance pgs-try-of-apply-pages (rec (pgs-slot k slots)))))))

(defthm pgs-try-in-order-of-apply-pages
  (implies (and (pgs-order-valid order slots)
                (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes)))
           (equal (pgs-try-in-order order slots (pgs-apply-pages writes keep pages) mode refusals)
                  (pgs-try-in-order order slots pages mode refusals)))
  :hints (("Goal" :induct (pgs-try-in-order order slots pages mode refusals)
                  :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-rec-keeps-in pgs-apply-pages pgs-rec-shape-p
                                      pgs-slot-keeps-avoid pgs-try-of-apply-pages))))

(defthm pgs-open-slots-of-apply-pages
  (implies (pgs-avoids (pgs-slots-keeps slots pages) (pgs-write-addrs writes))
           (equal (pgs-open-slots slots (pgs-apply-pages writes keep pages) mode)
                  (pgs-open-slots slots pages mode)))
  :hints (("Goal" :in-theory (disable pgs-try-in-order pgs-rec-valid pgs-slot pgs-slots-keeps
                                      pgs-rec-keeps-in pgs-apply-pages pgs-open-order))))

(defthm pgs-slots-keeps-of-nil
  (equal (pgs-slots-keeps nil pages) nil))

(defthm pgs-roots-keeps-cover
  (implies (pgs-avoids (pgs-roots-keeps roots pages) w)
           (pgs-avoids (pgs-slots-keeps (cdr (hons-assoc-equal r roots)) pages) w))
  :hints (("Goal" :induct (pgs-roots-keeps roots pages)
                  :in-theory (disable pgs-slots-keeps))))

; -----------------------------------------------------------------------------
; Set facts for the commit's addresses.

(defthm pgs-avoids-cons
  (equal (pgs-avoids xs (cons y ys))
         (and (not (member-equal y xs)) (pgs-avoids xs ys))))

(defthm pgs-avoids-nil
  (pgs-avoids xs nil))

(defthm pgs-avoids-symmetric
  (equal (pgs-avoids xs ys) (pgs-avoids ys xs))
  :rule-classes nil)

(defthm pgs-write-addrs-append
  (equal (pgs-write-addrs (append a b))
         (append (pgs-write-addrs a) (pgs-write-addrs b))))

(defthm pgs-write-addrs-of-page-writes
  (implies (equal (len fresh) (len dirty))
           (equal (pgs-write-addrs (pgs-page-writes dirty fresh))
                  (true-list-fix fresh))))

(defthm pgs-member-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(defthm pgs-member-true-list-fix
  (iff (member-equal x (true-list-fix a)) (member-equal x a)))

(defthm pgs-avoids-append-right
  (equal (pgs-avoids xs (append ys zs))
         (and (pgs-avoids xs ys) (pgs-avoids xs zs))))

(defthm pgs-avoids-true-list-fix
  (equal (pgs-avoids xs (true-list-fix ys)) (pgs-avoids xs ys)))

; -----------------------------------------------------------------------------
; Where the writes land.

(defun pgs-lands (dirty fresh pages)
  ; Each dirty page's content is at its fresh address.
  (if (atom dirty)
      t
    (and (equal (pgs-lookup (car fresh) pages) (cdar dirty))
         (pgs-lands (cdr dirty) (cdr fresh) pages))))

(defun pgs-content-of (a ws)
  (if (atom ws)
      nil
    (if (and (consp (car ws)) (equal (caar ws) a))
        (cdar ws)
      (pgs-content-of a (cdr ws)))))

(defthm pgs-lookup-of-apply-pages-all
  (implies (and (no-duplicatesp-equal (pgs-write-addrs ws))
                (member-equal a (pgs-write-addrs ws)))
           (equal (pgs-lookup a (pgs-apply-pages ws nil pages))
                  (pgs-content-of a ws))))

(defthm pgs-lookup-of-apply-pages-some
  (implies (and (no-duplicatesp-equal (pgs-write-addrs ws))
                (member-equal a (pgs-write-addrs ws)))
           (or (equal (pgs-lookup a (pgs-apply-pages ws keep pages))
                      (pgs-content-of a ws))
               (equal (pgs-lookup a (pgs-apply-pages ws keep pages))
                      (pgs-lookup a pages))))
  :rule-classes nil)

; With distinct write addresses, a crash image holds at each address either
; what the complete commit holds there or what was there before.
(defthm pgs-lookup-of-apply-pages-crash
  (implies (no-duplicatesp-equal (pgs-write-addrs writes))
           (or (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                      (pgs-lookup a (pgs-apply-pages writes nil pages)))
               (equal (pgs-lookup a (pgs-apply-pages writes keep pages))
                      (pgs-lookup a pages))))
  :rule-classes nil
  :hints (("Goal" :cases ((member-equal a (pgs-write-addrs writes)))
                  :use ((:instance pgs-lookup-of-apply-pages-some (ws writes))))))

(defun pgs-lands-in (dirty fresh ws)
  ; Each dirty page's content is what WS writes at its fresh address.
  (if (atom dirty)
      t
    (and (member-equal (car fresh) (pgs-write-addrs ws))
         (equal (pgs-content-of (car fresh) ws) (cdar dirty))
         (pgs-lands-in (cdr dirty) (cdr fresh) ws))))

(defthm pgs-lands-from-lands-in
  (implies (and (no-duplicatesp-equal (pgs-write-addrs ws))
                (pgs-lands-in dirty fresh ws))
           (pgs-lands dirty fresh (pgs-apply-pages ws nil pages))))

(defthm pgs-content-of-append
  (equal (pgs-content-of a (append x y))
         (if (member-equal a (pgs-write-addrs x))
             (pgs-content-of a x)
           (pgs-content-of a y))))

(defthm pgs-lands-in-of-append-left
  (implies (and (pgs-lands-in dirty fresh x) (no-duplicatesp-equal (pgs-write-addrs (append x y))))
           (pgs-lands-in dirty fresh (append x y))))

(defthm pgs-no-dups-append
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a) (no-duplicatesp-equal b) (pgs-avoids a b))))

(defthm pgs-lands-in-of-append-right
  (implies (and (pgs-lands-in dirty fresh y) (pgs-avoids (pgs-write-addrs x) (pgs-write-addrs y)))
           (pgs-lands-in dirty fresh (append x y)))
  :hints (("Goal" :induct (pgs-lands-in dirty fresh y))))

(defthm pgs-lands-in-of-page-writes
  (implies (and (no-duplicatesp-equal (true-list-fix fresh)) (equal (len fresh) (len dirty)))
           (pgs-lands-in dirty fresh (pgs-page-writes dirty fresh)))
  :hints (("Goal" :induct (pgs-page-writes dirty fresh))))

; -----------------------------------------------------------------------------
; Table predicates, entry by entry, and what the planner keeps of them
; (each for the flat table and, the same, for the directory).

(defun pgs-entries-good (ptab txid mode pages)
  ; Every entry the mode checks verifies.
  (if (atom ptab)
      t
    (and (not (eq (pgs-entry-verdict (car ptab) txid mode
                                     (pgs-digest (pgs-lookup (first (car ptab)) pages)))
                  :damaged))
         (pgs-entries-good (cdr ptab) txid mode pages))))

(defthm pgs-check-pages-iff-good
  (iff (pgs-check-pages ptab txid mode pages i tag)
       (not (pgs-entries-good ptab txid mode pages))))

(defun pgs-entry-sound (e txid mode p1 p2)
  ; Reading entry E's page in P2 either gives what P1 holds there, or the
  ; check refuses it.
  (or (equal (pgs-lookup (first e) p2) (pgs-lookup (first e) p1))
      (and (pgs-entry-checked-p e txid mode)
           (not (equal (pgs-digest (pgs-lookup (first e) p2)) (third e))))))

(defun pgs-entries-sound (ptab txid mode p1 p2)
  (if (atom ptab)
      t
    (and (pgs-entry-sound (car ptab) txid mode p1 p2)
         (pgs-entries-sound (cdr ptab) txid mode p1 p2))))

(defthm pgs-contents-when-sound-and-good
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entries-good ptab txid mode p2))
           (equal (pgs-contents ptab p2) (pgs-contents ptab p1))))

(defthm pgs-entries-good-of-update-nth
  (implies (and (pgs-entries-good ptab txid mode pages)
                (not (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
                         :damaged))
                (< (nfix i) (len ptab)))
           (pgs-entries-good (update-nth i e ptab) txid mode pages))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-entries-sound-of-update-nth
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entry-sound e txid mode p1 p2)
                (< (nfix i) (len ptab)))
           (pgs-entries-sound (update-nth i e ptab) txid mode p1 p2))
  :hints (("Goal" :induct (update-nth i e ptab) :in-theory (disable pgs-entry-sound))))

(defthm pgs-ptab-p-of-update-nth
  (implies (and (pgs-ptab-p ptab) (pgs-entry-p e) (< (nfix i) (len ptab)))
           (pgs-ptab-p (update-nth i e ptab)))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-txids-ok-of-update-nth
  (implies (and (pgs-ptab-txids-ok ptab txid) (pgs-entry-p e) (<= (second e) (nfix txid))
                (< (nfix i) (len ptab)))
           (pgs-ptab-txids-ok (update-nth i e ptab) txid))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-entries-good-of-append
  (equal (pgs-entries-good (append a b) txid mode pages)
         (and (pgs-entries-good a txid mode pages) (pgs-entries-good b txid mode pages))))

(defthm pgs-entries-sound-of-append
  (equal (pgs-entries-sound (append a b) txid mode p1 p2)
         (and (pgs-entries-sound a txid mode p1 p2) (pgs-entries-sound b txid mode p1 p2)))
  :hints (("Goal" :in-theory (disable pgs-entry-sound))))

(defthm pgs-contents-of-update-nth
  (implies (< (nfix i) (len ptab))
           (equal (pgs-contents (update-nth i e ptab) pages)
                  (update-nth i (pgs-lookup (first e) pages) (pgs-contents ptab pages))))
  :hints (("Goal" :induct (update-nth i e ptab))))

(defthm pgs-len-of-contents
  (equal (len (pgs-contents ptab pages)) (len ptab)))

(defthm pgs-contents-of-append
  (equal (pgs-contents (append a b) pages)
         (append (pgs-contents a pages) (pgs-contents b pages))))

(defthm pgs-contents-of-update-entry
  (equal (pgs-contents (pgs-update-entry i e ptab) pages)
         (cond ((< (nfix i) (len ptab))
                (update-nth (nfix i) (pgs-lookup (first e) pages) (pgs-contents ptab pages)))
               ((equal (nfix i) (len ptab))
                (append (pgs-contents ptab pages) (list (pgs-lookup (first e) pages))))
               (t (pgs-contents ptab pages)))))

(defun pgs-plan-ind (ptab dirty fresh contents txid)
  (if (atom dirty)
      (list ptab fresh contents txid)
    (pgs-plan-ind (pgs-update-entry (nfix (caar dirty))
                                    (list (nfix (car fresh)) (nfix txid)
                                          (nfix (pgs-digest (cdar dirty))))
                                    ptab)
                  (cdr dirty) (cdr fresh)
                  (let ((i (nfix (caar dirty))))
                    (cond ((< i (len contents)) (update-nth i (cdar dirty) contents))
                          ((equal i (len contents)) (append contents (list (cdar dirty))))
                          (t contents)))
                  txid)))

; The planner over the model's dirty list: the table after the commit, read
; where the dirty pages landed, is the state with the dirty pages replaced
; (or appended).
(defthm pgs-contents-of-plan-ptab
  (implies (and (pgs-lands dirty fresh pages) (nat-listp fresh) (<= (len dirty) (len fresh)))
           (equal (pgs-contents (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                               (pgs-dirty-digests dirty) txid)
                                pages)
                  (pgs-apply-dirty (pgs-contents ptab pages) dirty)))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh (pgs-contents ptab pages) txid)
                  :in-theory (disable pgs-update-entry))))

(defthm pgs-entries-good-of-update-entry
  (implies (and (pgs-entries-good ptab txid mode pages)
                (not (eq (pgs-entry-verdict e txid mode (pgs-digest (pgs-lookup (first e) pages)))
                         :damaged)))
           (pgs-entries-good (pgs-update-entry i e ptab) txid mode pages)))

(defthm pgs-entries-sound-of-update-entry
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-entry-sound e txid mode p1 p2))
           (pgs-entries-sound (pgs-update-entry i e ptab) txid mode p1 p2))
  :hints (("Goal" :in-theory (disable pgs-entry-sound))))

(defthm pgs-ptab-p-of-update-entry
  (implies (and (pgs-ptab-p ptab) (pgs-entry-p e))
           (pgs-ptab-p (pgs-update-entry i e ptab))))

(defthm pgs-txids-ok-of-update-entry
  (implies (and (pgs-ptab-txids-ok ptab txid) (pgs-entry-p e) (<= (second e) (nfix txid)))
           (pgs-ptab-txids-ok (pgs-update-entry i e ptab) txid)))

(in-theory (disable pgs-update-entry))

(defthm pgs-entries-good-of-plan-ptab
  (implies (and (pgs-entries-good ptab txid mode pages)
                (pgs-lands dirty fresh pages) (nat-listp fresh) (<= (len dirty) (len fresh))
                (natp txid))
           (pgs-entries-good (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                            (pgs-dirty-digests dirty) txid)
                             txid mode pages))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh nil txid))))

(defthm pgs-ptab-p-of-plan-ptab
  (implies (pgs-ptab-p ptab)
           (pgs-ptab-p (pgs-plan-ptab ptab lpages fresh digests txid))))

(defthm pgs-txids-ok-of-plan-ptab
  (implies (pgs-ptab-txids-ok ptab txid)
           (pgs-ptab-txids-ok (pgs-plan-ptab ptab lpages fresh digests txid) txid)))

(defthm pgs-txids-ok-monotone
  (implies (and (pgs-ptab-txids-ok ptab t0) (<= (nfix t0) (nfix t1)))
           (pgs-ptab-txids-ok ptab t1)))

(defthm pgs-entries-good-at-later-txid
  (implies (and (pgs-entries-good ptab t0 mode pages)
                (pgs-ptab-txids-ok ptab t0)
                (natp t0) (< t0 t1))
           (pgs-entries-good ptab t1 mode pages)))

(defthm pgs-entries-good-of-apply-pages
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (equal (pgs-entries-good ptab txid mode (pgs-apply-pages writes keep pages))
                  (pgs-entries-good ptab txid mode pages)))
  :hints (("Goal" :induct (pgs-ptab-physes ptab))))

; Soundness of a crash image against the complete commit.
(defthm pgs-entries-sound-of-unwritten
  (implies (pgs-avoids (pgs-ptab-physes ptab) (pgs-write-addrs writes))
           (pgs-entries-sound ptab txid mode
                              (pgs-apply-pages writes nil pages)
                              (pgs-apply-pages writes keep pages))))

(defthm pgs-dirty-lpages-of-table-dirty
  (implies (nat-listp tl)
           (equal (pgs-dirty-lpages (pgs-table-dirty tl cs)) tl)))

(defthm pgs-len-of-table-dirty
  (equal (len (pgs-table-dirty tl cs)) (len tl)))

; -----------------------------------------------------------------------------
; What a successful try and a successful open say.

(defthm pgs-true-listp-of-contents
  (true-listp (pgs-contents ptab pages)))

(defthm pgs-try-ok-facts
  (implies (equal (car (pgs-try rec pages mode)) :ok)
           (let* ((dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
                  (cs (pgs-contents dir pages))
                  (ptab (pgs-flatten cs)))
             (and (pgs-ptab-p dir)
                  (equal (len dir) (pgs-ntables (pgs-rec-npages rec)))
                  (pgs-ptab-txids-ok dir (pgs-rec-txid rec))
                  (equal (pgs-digest dir) (pgs-rec-dir-digest rec))
                  (pgs-entries-good dir (pgs-rec-txid rec) mode pages)
                  (not (pgs-tables-verdict cs (pgs-rec-npages rec) (pgs-rec-txid rec) 0))
                  (pgs-ptab-p ptab)
                  (equal (pgs-chunk ptab) cs)
                  (equal (len ptab) (pgs-rec-npages rec))
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid rec))
                  (pgs-entries-good ptab (pgs-rec-txid rec) mode pages)
                  (equal (pgs-try rec pages mode)
                         (list :ok (pgs-rec-txid rec) (pgs-contents ptab pages))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pgs-check-pages pgs-contents pgs-tables-verdict pgs-flatten
                                      pgs-chunk pgs-ptab-p pgs-ptab-txids-ok pgs-entries-good
                                      pgs-ntables pgs-rec-txid pgs-rec-dir-addr pgs-rec-npages
                                      pgs-rec-dir-digest pgs-lookup pgs-tables-ok-join)
                  :use ((:instance pgs-tables-ok-join
                                   (cs (pgs-contents (pgs-lookup (pgs-rec-dir-addr rec) pages) pages))
                                   (rem (pgs-rec-npages rec)) (txid (pgs-rec-txid rec)) (i 0))))))

(defthm pgs-try-when-facts
  (let* ((dir (pgs-lookup (pgs-rec-dir-addr rec) pages))
         (cs (pgs-contents dir pages))
         (ptab (pgs-flatten cs)))
    (implies (and (pgs-ptab-p dir)
                  (equal (len dir) (pgs-ntables (pgs-rec-npages rec)))
                  (pgs-ptab-txids-ok dir (pgs-rec-txid rec))
                  (equal (pgs-digest dir) (pgs-rec-dir-digest rec))
                  (pgs-entries-good dir (pgs-rec-txid rec) mode pages)
                  (not (pgs-tables-verdict cs (pgs-rec-npages rec) (pgs-rec-txid rec) 0))
                  (pgs-entries-good ptab (pgs-rec-txid rec) mode pages))
             (equal (pgs-try rec pages mode)
                    (list :ok (pgs-rec-txid rec) (pgs-contents ptab pages)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable pgs-check-pages pgs-contents pgs-tables-verdict pgs-flatten
                                      pgs-chunk pgs-ptab-p pgs-ptab-txids-ok pgs-entries-good
                                      pgs-ntables pgs-rec-txid pgs-rec-dir-addr pgs-rec-npages
                                      pgs-rec-dir-digest pgs-lookup))))

(defthm pgs-try-shape
  (implies (equal (car (pgs-try rec pages mode)) :ok)
           (equal (list :ok (cadr (pgs-try rec pages mode)) (caddr (pgs-try rec pages mode)))
                  (pgs-try rec pages mode)))
  :hints (("Goal" :in-theory (disable pgs-check-pages pgs-contents pgs-tables-verdict pgs-flatten
                                      pgs-chunk pgs-ptab-p pgs-ptab-txids-ok pgs-entries-good
                                      pgs-ntables pgs-rec-txid pgs-rec-dir-addr pgs-rec-npages
                                      pgs-rec-dir-digest pgs-lookup pgs-dir-verdict
                                      pgs-check-pages-iff-good))))

(defthm pgs-try-in-order-ok
  (let ((o (pgs-try-in-order order slots pages mode refs)))
    (implies (and (equal (car o) :ok) (pgs-order-valid order slots))
             (and (member-equal (second o) '(0 1))
                  (pgs-rec-valid (pgs-slot (second o) slots))
                  (equal (pgs-try (pgs-slot (second o) slots) pages mode)
                         (list :ok (third o) (fourth o)))
                  (true-listp o))))
  :hints (("Goal" :induct (pgs-try-in-order order slots pages mode refs)
                  :in-theory (disable pgs-try pgs-rec-valid pgs-slot)))
  :rule-classes nil)

(defthm pgs-open-slots-ok
  (let ((o (pgs-open-slots slots pages mode)))
    (implies (equal (car o) :ok)
             (and (member-equal (second o) '(0 1))
                  (pgs-rec-valid (pgs-slot (second o) slots))
                  (equal (pgs-try (pgs-slot (second o) slots) pages mode)
                         (list :ok (third o) (fourth o)))
                  (true-listp o))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-rec-valid pgs-slot pgs-try-in-order
                                      pgs-open-order pgs-order-valid-of-open-order)
                  :use ((:instance pgs-order-valid-of-open-order)
                        (:instance pgs-try-in-order-ok
                                   (order (pgs-open-order (pgs-slot 0 slots)
                                                          (pgs-rec-valid (pgs-slot 0 slots))
                                                          (pgs-slot 1 slots)
                                                          (pgs-rec-valid (pgs-slot 1 slots))))
                                   (refs (pgs-slot-refusals (pgs-slot 0 slots)
                                                            (pgs-rec-valid (pgs-slot 0 slots))
                                                            (pgs-slot 1 slots)
                                                            (pgs-rec-valid (pgs-slot 1 slots))))))))
  :rule-classes nil)

; The record a commit writes.
(defthm pgs-make-rec-fields
  (implies (and (natp txid) (natp a) (natp n))
           (and (pgs-rec-valid (pgs-make-rec txid a n (pgs-digest x)))
                (equal (pgs-rec-txid (pgs-make-rec txid a n d)) txid)
                (equal (pgs-rec-dir-addr (pgs-make-rec txid a n d)) a)
                (equal (pgs-rec-npages (pgs-make-rec txid a n d)) n)
                (equal (pgs-rec-dir-digest (pgs-make-rec txid a n (pgs-digest x))) (pgs-digest x))
                (pgs-rec-shape-p (pgs-make-rec txid a n (pgs-digest x))))))

(defthm pgs-len-of-apply-dirty
  (equal (len (pgs-apply-dirty c d))
         (pgs-grown-len (pgs-dirty-lpages d) (len c)))
  :hints (("Goal" :induct (pgs-apply-dirty c d))))

; -----------------------------------------------------------------------------
; One commit step, over a root's slots (the disk-level keystones instantiate
; it).  CUR is the slot the open used; the commit writes the dirty pages to
; FRESH, the touched table pages to TFRESH, the directory DIR2 to RS and the
; record to the other slot.

(in-theory (disable pgs-rec-txid pgs-rec-dir-addr pgs-rec-npages pgs-rec-dir-digest))

(defthm pgs-rec-keeps-in-when-dir
  (implies (pgs-ptab-p (pgs-lookup (pgs-rec-dir-addr rec) pages))
           (equal (pgs-rec-keeps-in rec pages)
                  (pgs-rec-keeps rec (pgs-lookup (pgs-rec-dir-addr rec) pages)
                                 (pgs-contents (pgs-lookup (pgs-rec-dir-addr rec) pages) pages)))))

(defun pgs-step-ptab (cur pages)
  (pgs-flatten (pgs-contents (pgs-lookup (pgs-rec-dir-addr cur) pages) pages)))
(defun pgs-step-ptab2 (ptab dirty fresh txid)
  (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh (pgs-dirty-digests dirty) txid))
(defun pgs-step-tl (dirty) (pgs-touched (pgs-dirty-lpages dirty) nil))
(defun pgs-step-tdirty (dirty ptab2) (pgs-table-dirty (pgs-step-tl dirty) (pgs-chunk ptab2)))
(defun pgs-step-dir2 (dir dirty tdirty tfresh txid)
  (pgs-plan-ptab (true-list-fix dir) (pgs-step-tl dirty) tfresh (pgs-dirty-digests tdirty) txid))
(defun pgs-step-writes (dirty fresh tdirty tfresh rs dir2)
  (append (pgs-page-writes dirty fresh) (pgs-page-writes tdirty tfresh) (list (cons rs dir2))))

(defun pgs-step-hyps (cur pages mode dirty fresh tfresh rs txid)
  (and (pgs-rec-valid cur)
       (equal (car (pgs-try cur pages mode)) :ok)
       (natp txid) (< (pgs-rec-txid cur) txid)
       (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (pgs-step-ptab cur pages)) 0)
       (nat-listp fresh) (nat-listp tfresh) (natp rs)
       (equal (len fresh) (len dirty))
       (equal (len tfresh) (len (pgs-step-tl dirty)))
       (no-duplicatesp-equal (append fresh tfresh (list rs)))
       (pgs-avoids (pgs-rec-keeps-in cur pages) (append fresh tfresh (list rs)))))

(defthm pgs-step-hyps-facts
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (let* ((dir (pgs-lookup (pgs-rec-dir-addr cur) pages))
                  (cs (pgs-contents dir pages))
                  (ptab (pgs-flatten cs)))
             (and (pgs-rec-valid cur)
                  (natp txid) (< (pgs-rec-txid cur) txid)
                  (pgs-lpages-ok (pgs-dirty-lpages dirty) (len ptab) 0)
                  (nat-listp fresh) (nat-listp tfresh) (natp rs)
                  (equal (len fresh) (len dirty))
                  (equal (len tfresh) (len (pgs-step-tl dirty)))
                  (no-duplicatesp-equal fresh) (no-duplicatesp-equal tfresh)
                  (pgs-avoids fresh tfresh)
                  (not (member-equal rs fresh)) (not (member-equal rs tfresh))
                  (pgs-ptab-p dir)
                  (equal (len dir) (pgs-ntables (pgs-rec-npages cur)))
                  (pgs-ptab-txids-ok dir (pgs-rec-txid cur))
                  (pgs-entries-good dir (pgs-rec-txid cur) mode pages)
                  (pgs-ptab-p ptab)
                  (equal (pgs-chunk ptab) cs)
                  (equal (len ptab) (pgs-rec-npages cur))
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid cur))
                  (pgs-entries-good ptab (pgs-rec-txid cur) mode pages)
                  (equal (pgs-try cur pages mode)
                         (list :ok (pgs-rec-txid cur) (pgs-contents ptab pages)))
                  (pgs-avoids (pgs-ptab-physes dir) (append fresh tfresh (list rs)))
                  (pgs-avoids (pgs-ptab-physes ptab) (append fresh tfresh (list rs)))
                  (pgs-avoids (pgs-rec-keeps-in cur pages) (append fresh tfresh (list rs))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(pgs-step-hyps pgs-step-ptab pgs-no-dups-append
                                               pgs-avoids-append-right pgs-avoids-cons pgs-avoids-nil
                                               pgs-avoids-append no-duplicatesp-equal
                                               member-equal pgs-avoids car-cons cdr-cons
                                               pgs-rec-keeps-in-when-dir)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-try-ok-facts (rec cur))
                        (:instance pgs-rec-keeps-avoids-dir
                                   (rec cur) (dir (pgs-lookup (pgs-rec-dir-addr cur) pages))
                                   (tables (pgs-contents (pgs-lookup (pgs-rec-dir-addr cur) pages) pages))
                                   (w (append fresh tfresh (list rs))))
                        (:instance pgs-rec-keeps-avoids-table
                                   (rec cur) (dir (pgs-lookup (pgs-rec-dir-addr cur) pages))
                                   (tables (pgs-contents (pgs-lookup (pgs-rec-dir-addr cur) pages) pages))
                                   (w (append fresh tfresh (list rs))))))))

(defthm pgs-write-addrs-of-step-writes
  (implies (and (equal (len fresh) (len dirty)) (equal (len tfresh) (len tdirty)))
           (equal (pgs-write-addrs (pgs-step-writes dirty fresh tdirty tfresh rs dir2))
                  (append (true-list-fix fresh) (true-list-fix tfresh) (list rs)))))

(defthm pgs-no-dups-true-list-fix
  (equal (no-duplicatesp-equal (true-list-fix xs)) (no-duplicatesp-equal xs)))

(defthm pgs-avoids-true-list-fix-left
  (equal (pgs-avoids (true-list-fix xs) ys) (pgs-avoids xs ys)))

(defthm pgs-step-lands
  ; The complete commit: every write is where the plan put it.
  (implies (and (nat-listp fresh) (nat-listp tfresh)
                (equal (len fresh) (len dirty)) (equal (len tfresh) (len tdirty))
                (no-duplicatesp-equal (append fresh tfresh (list rs))))
           (let ((p1 (pgs-apply-pages (pgs-step-writes dirty fresh tdirty tfresh rs dir2) nil pages)))
             (and (pgs-lands dirty fresh p1)
                  (pgs-lands tdirty tfresh p1)
                  (equal (pgs-lookup rs p1) dir2))))
  :hints (("Goal" :in-theory (disable pgs-apply-pages pgs-lookup-of-apply-pages-all)
                  :use ((:instance pgs-lookup-of-apply-pages-all
                                   (a rs) (ws (pgs-step-writes dirty fresh tdirty tfresh rs dir2)))))))

(defthm pgs-nat-listp-of-touched
  (nat-listp (pgs-touched ls prev)))

(defthm pgs-nat-listp-true-listp
  (implies (nat-listp x) (true-listp x))
  :rule-classes :forward-chaining)

; The step's objects, named (and closed) so that each fact below is small.
(defun pgs-sd (cur pages) (pgs-lookup (pgs-rec-dir-addr cur) pages))
(defun pgs-sp (cur pages) (pgs-flatten (pgs-contents (pgs-sd cur pages) pages)))
(defun pgs-sp2 (cur pages dirty fresh txid) (pgs-step-ptab2 (pgs-sp cur pages) dirty fresh txid))
(defun pgs-std (cur pages dirty fresh txid) (pgs-step-tdirty dirty (pgs-sp2 cur pages dirty fresh txid)))
(defun pgs-sd2 (cur pages dirty fresh tfresh txid)
  (pgs-step-dir2 (pgs-sd cur pages) dirty (pgs-std cur pages dirty fresh txid) tfresh txid))
(defun pgs-swr (cur pages dirty fresh tfresh rs txid)
  (pgs-step-writes dirty fresh (pgs-std cur pages dirty fresh txid) tfresh rs
                   (pgs-sd2 cur pages dirty fresh tfresh txid)))
(defun pgs-srec (cur pages dirty fresh tfresh rs txid)
  (pgs-make-rec txid rs (len (pgs-sp2 cur pages dirty fresh txid))
                (pgs-digest (pgs-sd2 cur pages dirty fresh tfresh txid))))

(defthm pgs-s-facts
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (let ((dir (pgs-sd cur pages)) (ptab (pgs-sp cur pages)))
             (and (pgs-rec-valid cur)
                  (natp txid) (< (pgs-rec-txid cur) txid)
                  (pgs-lpages-ok (pgs-dirty-lpages dirty) (len ptab) 0)
                  (nat-listp fresh) (nat-listp tfresh) (natp rs)
                  (equal (len fresh) (len dirty))
                  (equal (len tfresh) (len (pgs-step-tl dirty)))
                  (no-duplicatesp-equal (append fresh tfresh (list rs)))
                  (pgs-ptab-p dir)
                  (pgs-ptab-txids-ok dir (pgs-rec-txid cur))
                  (pgs-entries-good dir (pgs-rec-txid cur) mode pages)
                  (pgs-ptab-p ptab)
                  (equal (pgs-chunk ptab) (pgs-contents dir pages))
                  (pgs-ptab-txids-ok ptab (pgs-rec-txid cur))
                  (pgs-entries-good ptab (pgs-rec-txid cur) mode pages)
                  (equal (pgs-try cur pages mode)
                         (list :ok (pgs-rec-txid cur) (pgs-contents ptab pages)))
                  (pgs-avoids (pgs-ptab-physes dir) (append fresh tfresh (list rs)))
                  (pgs-avoids (pgs-ptab-physes ptab) (append fresh tfresh (list rs)))
                  (pgs-avoids (pgs-rec-keeps-in cur pages) (append fresh tfresh (list rs))))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(pgs-sd pgs-sp pgs-step-hyps)
                  :use ((:instance pgs-step-hyps-facts)))))

(in-theory (disable pgs-rec-valid pgs-step-hyps pgs-sd pgs-sp pgs-sp2 pgs-std pgs-sd2 pgs-swr pgs-srec
                    pgs-step-ptab2 pgs-step-tdirty pgs-step-dir2 pgs-step-writes))

(defthm pgs-len-of-std
  (equal (len (pgs-std cur pages dirty fresh txid)) (len (pgs-step-tl dirty)))
  :hints (("Goal" :in-theory (enable pgs-std pgs-step-tdirty))))

(defthm pgs-s-lands
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (let ((p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))
             (and (pgs-lands dirty fresh p1)
                  (pgs-lands (pgs-std cur pages dirty fresh txid) tfresh p1)
                  (equal (pgs-lookup rs p1) (pgs-sd2 cur pages dirty fresh tfresh txid)))))
  :hints (("Goal" :in-theory (e/d (pgs-swr) (pgs-step-lands pgs-apply-pages pgs-lands pgs-lookup))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-step-lands
                                   (tdirty (pgs-std cur pages dirty fresh txid))
                                   (dir2 (pgs-sd2 cur pages dirty fresh tfresh txid)))))))

(defthm pgs-s-writes-avoid
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (pgs-write-addrs (pgs-swr cur pages dirty fresh tfresh rs txid))
                  (append fresh tfresh (list rs))))
  :hints (("Goal" :in-theory (e/d (pgs-swr) (pgs-write-addrs))
                  :use ((:instance pgs-s-facts)))))

(defthm pgs-s-old-in-image
  ; The old directory and table read the same, and still verify at the new
  ; txid, in any image of the commit's writes.
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (let ((p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
             (and (equal (pgs-contents (pgs-sd cur pages) p2) (pgs-contents (pgs-sd cur pages) pages))
                  (equal (pgs-contents (pgs-sp cur pages) p2) (pgs-contents (pgs-sp cur pages) pages))
                  (pgs-entries-good (pgs-sd cur pages) txid mode p2)
                  (pgs-entries-good (pgs-sp cur pages) txid mode p2))))
  :hints (("Goal" :in-theory (disable pgs-apply-pages pgs-contents pgs-entries-good pgs-avoids
                                      pgs-entries-good-at-later-txid)
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-entries-good-at-later-txid
                                   (ptab (pgs-sd cur pages)) (t0 (pgs-rec-txid cur)) (t1 txid))
                        (:instance pgs-entries-good-at-later-txid
                                   (ptab (pgs-sp cur pages)) (t0 (pgs-rec-txid cur)) (t1 txid))))))

(defthm pgs-s-dir2-contents
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (pgs-contents (pgs-sd2 cur pages dirty fresh tfresh txid)
                                (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                  (pgs-chunk (pgs-sp2 cur pages dirty fresh txid))))
  :hints (("Goal" :in-theory (e/d (pgs-sd2 pgs-step-dir2 pgs-std pgs-step-tdirty pgs-sp2 pgs-step-ptab2 pgs-step-tl)
                                  (pgs-apply-pages pgs-contents pgs-chunk pgs-plan-ptab pgs-touched
                                   pgs-table-dirty pgs-apply-dirty pgs-s-old-in-image pgs-s-lands
                                   pgs-tables-after-plan pgs-contents-of-plan-ptab))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-lands)
                        (:instance pgs-s-old-in-image (keep nil))
                        (:instance pgs-tables-after-plan
                                   (p (pgs-sp cur pages)) (ls (pgs-dirty-lpages dirty))
                                   (digests (pgs-dirty-digests dirty)))
                        (:instance pgs-contents-of-plan-ptab
                                   (ptab (pgs-sd cur pages))
                                   (dirty (pgs-std cur pages dirty fresh txid))
                                   (fresh tfresh)
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))))))

(defthm pgs-s-new-shapes
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (and (pgs-ptab-p (pgs-sd2 cur pages dirty fresh tfresh txid))
                (pgs-ptab-txids-ok (pgs-sd2 cur pages dirty fresh tfresh txid) txid)
                (pgs-ptab-p (pgs-sp2 cur pages dirty fresh txid))
                (pgs-ptab-txids-ok (pgs-sp2 cur pages dirty fresh txid) txid)))
  :hints (("Goal" :in-theory (e/d (pgs-sd2 pgs-step-dir2 pgs-sp2 pgs-step-ptab2)
                                  (pgs-plan-ptab pgs-ptab-p pgs-ptab-txids-ok))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-txids-ok-monotone (ptab (pgs-sd cur pages))
                                   (t0 (pgs-rec-txid cur)) (t1 txid))
                        (:instance pgs-txids-ok-monotone (ptab (pgs-sp cur pages))
                                   (t0 (pgs-rec-txid cur)) (t1 txid))))))

(defthm pgs-sd2-is-plan
  (equal (pgs-sd2 cur pages dirty fresh tfresh txid)
         (pgs-plan-ptab (true-list-fix (pgs-sd cur pages))
                        (pgs-dirty-lpages (pgs-std cur pages dirty fresh txid))
                        tfresh (pgs-dirty-digests (pgs-std cur pages dirty fresh txid)) txid))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(pgs-sd2 pgs-step-dir2 pgs-std pgs-step-tdirty pgs-step-tl
                                               pgs-dirty-lpages-of-table-dirty pgs-nat-listp-of-touched)
                                             (theory 'minimal-theory)))))

(defthm pgs-sp2-is-plan
  (equal (pgs-sp2 cur pages dirty fresh txid)
         (pgs-plan-ptab (pgs-sp cur pages) (pgs-dirty-lpages dirty) fresh (pgs-dirty-digests dirty) txid))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pgs-sp2 pgs-step-ptab2))))

(defthm pgs-s-new-good
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (let ((p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))
             (and (pgs-entries-good (pgs-sd2 cur pages dirty fresh tfresh txid) txid mode p1)
                  (pgs-entries-good (pgs-sp2 cur pages dirty fresh txid) txid mode p1)
                  (equal (pgs-contents (pgs-sp2 cur pages dirty fresh txid) p1)
                         (pgs-apply-dirty (pgs-contents (pgs-sp cur pages) pages) dirty)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-len-of-std pgs-step-tl pgs-ptab-p-of-true-list-fix)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-lands)
                        (:instance pgs-s-old-in-image (keep nil))
                        (:instance pgs-sd2-is-plan)
                        (:instance pgs-sp2-is-plan)
                        (:instance pgs-entries-good-of-plan-ptab
                                   (ptab (pgs-sd cur pages)) (dirty (pgs-std cur pages dirty fresh txid))
                                   (fresh tfresh)
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))
                        (:instance pgs-entries-good-of-plan-ptab
                                   (ptab (pgs-sp cur pages))
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))
                        (:instance pgs-contents-of-plan-ptab
                                   (ptab (pgs-sp cur pages))
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))))
          (and stable-under-simplificationp
               '(:in-theory (enable nat-listp natp true-listp)))))

(defthm pgs-s-dir2-len
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (len (pgs-sd2 cur pages dirty fresh tfresh txid))
                  (pgs-ntables (len (pgs-sp2 cur pages dirty fresh txid)))))
  :hints (("Goal" :in-theory (disable pgs-s-dir2-contents pgs-len-of-contents)
                  :use ((:instance pgs-s-dir2-contents)
                        (:instance pgs-len-of-contents
                                   (ptab (pgs-sd2 cur pages dirty fresh tfresh txid))
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid)
                                                           nil pages)))))))

; The complete commit's image opens, through the new record, on the next
; transaction and the state with the dirty pages replaced.
(defthm pgs-step-try-new
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (pgs-try (pgs-srec cur pages dirty fresh tfresh rs txid)
                           (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)
                           mode)
                  (list :ok txid (pgs-apply-dirty (pgs-contents (pgs-sp cur pages) pages) dirty))))
  :hints (("Goal" :in-theory (e/d (pgs-srec)
                                  (pgs-try pgs-apply-pages pgs-contents pgs-entries-good pgs-chunk
                                   pgs-flatten pgs-ptab-p pgs-ptab-txids-ok pgs-tables-verdict
                                   pgs-make-rec pgs-apply-dirty pgs-lookup))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-try-when-facts
                                   (rec (pgs-srec cur pages dirty fresh tfresh rs txid))
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid)
                                                           nil pages)))
                        (:instance pgs-tables-verdict-of-chunk
                                   (p (pgs-sp2 cur pages dirty fresh txid)) (i 0))))))

; -----------------------------------------------------------------------------
; A crash image read through the new record: what it verifies is what the
; complete commit holds.

(defun pgs-writes-faithful (writes pages)
  ; A-CRYPTO, instantiated: an address a write targets holds, before the
  ; write, either the written content or content with another digest.
  (if (atom writes)
      t
    (and (or (atom (car writes))
             (not (equal (pgs-digest (pgs-lookup (caar writes) pages))
                         (pgs-digest (cdar writes))))
             (equal (pgs-lookup (caar writes) pages) (cdar writes)))
         (pgs-writes-faithful (cdr writes) pages))))

(defthm pgs-writes-faithful-append
  (equal (pgs-writes-faithful (append a b) pages)
         (and (pgs-writes-faithful a pages) (pgs-writes-faithful b pages))))

(defun pgs-crash-local (xs p1 p2 p0)
  (if (atom xs)
      t
    (and (or (equal (pgs-lookup (car xs) p2) (pgs-lookup (car xs) p1))
             (equal (pgs-lookup (car xs) p2) (pgs-lookup (car xs) p0)))
         (pgs-crash-local (cdr xs) p1 p2 p0))))

(defthm pgs-crash-local-of-apply
  (implies (no-duplicatesp-equal (pgs-write-addrs writes))
           (pgs-crash-local xs (pgs-apply-pages writes nil pages)
                            (pgs-apply-pages writes keep pages) pages))
  :hints (("Goal" :induct (len xs))
          ("Subgoal *1/1" :use ((:instance pgs-lookup-of-apply-pages-crash (a (car xs)))))))

(defun pgs-new-sound (dirty fresh txid mode p1 p2)
  (if (atom dirty)
      t
    (and (pgs-entry-sound (list (nfix (car fresh)) (nfix txid) (nfix (pgs-digest (cdar dirty))))
                          txid mode p1 p2)
         (pgs-new-sound (cdr dirty) (cdr fresh) txid mode p1 p2))))

(defthm pgs-new-sound-from-faithful
  (implies (and (pgs-lands dirty fresh p1)
                (pgs-crash-local fresh p1 p2 p0)
                (pgs-writes-faithful (pgs-page-writes dirty fresh) p0)
                (nat-listp fresh) (natp txid)
                (<= (len dirty) (len fresh)))
           (pgs-new-sound dirty fresh txid mode p1 p2))
  :hints (("Goal" :induct (pgs-page-writes dirty fresh))))

(defthm pgs-entries-sound-of-plan-ptab
  (implies (and (pgs-entries-sound ptab txid mode p1 p2)
                (pgs-new-sound dirty fresh txid mode p1 p2))
           (pgs-entries-sound (pgs-plan-ptab ptab (pgs-dirty-lpages dirty) fresh
                                             (pgs-dirty-digests dirty) txid)
                              txid mode p1 p2))
  :hints (("Goal" :induct (pgs-plan-ind ptab dirty fresh nil txid)
                  :in-theory (disable pgs-entry-sound))))

(defthm pgs-crash-local-append
  (equal (pgs-crash-local (append a b) p1 p2 p0)
         (and (pgs-crash-local a p1 p2 p0) (pgs-crash-local b p1 p2 p0))))

(defthm pgs-s-crash-sound
  ; In any image of the commit's writes, the new directory and table read
  ; either what the complete commit holds or fail their checks.
  (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                (pgs-writes-faithful (pgs-swr cur pages dirty fresh tfresh rs txid) pages))
           (let ((p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                 (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
             (and (pgs-entries-sound (pgs-sd2 cur pages dirty fresh tfresh txid) txid mode p1 p2)
                  (pgs-entries-sound (pgs-sp2 cur pages dirty fresh txid) txid mode p1 p2))))
  :hints (("Goal" :in-theory (union-theories '(pgs-len-of-std pgs-step-tl pgs-ptab-p-of-true-list-fix
                                               pgs-writes-faithful-append pgs-crash-local-append
                                               pgs-swr pgs-step-writes pgs-s-writes-avoid)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-lands)
                        (:instance pgs-s-writes-avoid)
                        (:instance pgs-sd2-is-plan)
                        (:instance pgs-sp2-is-plan)
                        (:instance pgs-crash-local-of-apply
                                   (xs (append fresh tfresh (list rs)))
                                   (writes (pgs-swr cur pages dirty fresh tfresh rs txid)))
                        (:instance pgs-entries-sound-of-unwritten
                                   (ptab (pgs-sd cur pages))
                                   (writes (pgs-swr cur pages dirty fresh tfresh rs txid)))
                        (:instance pgs-entries-sound-of-unwritten
                                   (ptab (pgs-sp cur pages))
                                   (writes (pgs-swr cur pages dirty fresh tfresh rs txid)))
                        (:instance pgs-new-sound-from-faithful
                                   (dirty (pgs-std cur pages dirty fresh txid)) (fresh tfresh)
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages))
                                   (p0 pages))
                        (:instance pgs-new-sound-from-faithful
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages))
                                   (p0 pages))
                        (:instance pgs-entries-sound-of-plan-ptab
                                   (ptab (true-list-fix (pgs-sd cur pages)))
                                   (dirty (pgs-std cur pages dirty fresh txid)) (fresh tfresh)
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
                        (:instance pgs-entries-sound-of-plan-ptab
                                   (ptab (pgs-sp cur pages))
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))))
          (and stable-under-simplificationp
               '(:in-theory (enable nat-listp natp true-listp)))))

(defthm pgs-s-dir-in-crash
  ; The directory the new record names, read from a crash image, is the
  ; planned one or has another digest.
  (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                (pgs-writes-faithful (pgs-swr cur pages dirty fresh tfresh rs txid) pages)
                (equal (pgs-digest (pgs-lookup rs (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid)
                                                                   keep pages)))
                       (pgs-digest (pgs-sd2 cur pages dirty fresh tfresh txid))))
           (equal (pgs-lookup rs (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages))
                  (pgs-sd2 cur pages dirty fresh tfresh txid)))
  :hints (("Goal" :in-theory (e/d (pgs-swr pgs-step-writes)
                                  (pgs-apply-pages pgs-sd2 pgs-page-writes pgs-s-lands
                                   pgs-s-writes-avoid))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-lands)
                        (:instance pgs-s-writes-avoid)
                        (:instance pgs-lookup-of-apply-pages-crash
                                   (a rs) (writes (pgs-swr cur pages dirty fresh tfresh rs txid)))))))

(defthm pgs-step-try-crash
  (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                (pgs-writes-faithful (pgs-swr cur pages dirty fresh tfresh rs txid) pages)
                (equal (car (pgs-try (pgs-srec cur pages dirty fresh tfresh rs txid)
                                     (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)
                                     mode))
                       :ok))
           (equal (pgs-try (pgs-srec cur pages dirty fresh tfresh rs txid)
                           (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)
                           mode)
                  (list :ok txid (pgs-apply-dirty (pgs-contents (pgs-sp cur pages) pages) dirty))))
  :hints (("Goal" :in-theory (union-theories '(pgs-srec pgs-flatten-of-chunk
                                               pgs-true-listp-of-contents pgs-ptab-p-true-listp)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-make-rec-fields
                                   (a rs) (n (len (pgs-sp2 cur pages dirty fresh txid)))
                                   (x (pgs-sd2 cur pages dirty fresh tfresh txid))
                                   (d (pgs-digest (pgs-sd2 cur pages dirty fresh tfresh txid))))
                        (:instance pgs-s-new-shapes)
                        (:instance pgs-s-new-good)
                        (:instance pgs-s-dir2-contents)
                        (:instance pgs-s-crash-sound)
                        (:instance pgs-s-dir-in-crash)
                        (:instance pgs-try-ok-facts
                                   (rec (pgs-srec cur pages dirty fresh tfresh rs txid))
                                   (pages (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
                        (:instance pgs-contents-when-sound-and-good
                                   (ptab (pgs-sd2 cur pages dirty fresh tfresh txid))
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
                        (:instance pgs-contents-when-sound-and-good
                                   (ptab (pgs-sp2 cur pages dirty fresh txid))
                                   (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages))
                                   (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))))
          (and stable-under-simplificationp
               '(:in-theory (enable natp (:type-prescription len))))))

(defthm pgs-step-try-cur-crash
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (equal (pgs-try cur (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages) mode)
                  (list :ok (pgs-rec-txid cur) (pgs-contents (pgs-sp cur pages) pages))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-apply-pages pgs-try-of-apply-pages)
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-writes-avoid)
                        (:instance pgs-try-of-apply-pages
                                   (rec cur) (writes (pgs-swr cur pages dirty fresh tfresh rs txid)))))))

(defthm pgs-s-rec-facts
  (implies (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
           (and (pgs-rec-valid (pgs-srec cur pages dirty fresh tfresh rs txid))
                (pgs-rec-shape-p (pgs-srec cur pages dirty fresh tfresh rs txid))
                (equal (pgs-rec-txid (pgs-srec cur pages dirty fresh tfresh rs txid)) txid)))
  :hints (("Goal" :in-theory (e/d (pgs-srec) (pgs-make-rec pgs-make-rec-fields))
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-make-rec-fields
                                   (a rs) (n (len (pgs-sp2 cur pages dirty fresh txid)))
                                   (x (pgs-sd2 cur pages dirty fresh tfresh txid))
                                   (d (pgs-digest (pgs-sd2 cur pages dirty fresh tfresh txid))))))))

(defthm pgs-rec-valid-shape
  (implies (pgs-rec-valid x)
           (and (pgs-rec-shape-p x) (true-listp x) (consp x)))
  :hints (("Goal" :in-theory (enable pgs-rec-valid)))
  :rule-classes :forward-chaining)

(defthm pgs-step-open-complete
  (let ((rec (pgs-srec cur pages dirty fresh tfresh rs txid))
        (p1 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) nil pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                  (or (equal slots2 (cons cur rec)) (equal slots2 (cons rec cur))))
             (equal (pgs-view (pgs-open-slots slots2 p1 mode))
                    (list txid (pgs-apply-dirty (pgs-contents (pgs-sp cur pages) pages) dirty)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-apply-pages pgs-rec-shape-p pgs-step-try-cur-crash)
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-rec-facts)
                        (:instance pgs-step-try-new)
                        (:instance pgs-step-try-cur-crash (keep nil))))))

(defthm pgs-step-open-crash
  (let ((rec (pgs-srec cur pages dirty fresh tfresh rs txid))
        (p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                  (pgs-writes-faithful (pgs-swr cur pages dirty fresh tfresh rs txid) pages)
                  (or (equal sv rec) (not (pgs-rec-valid sv)))
                  (or (equal slots2 (cons cur sv)) (equal slots2 (cons sv cur))))
             (member-equal (pgs-view (pgs-open-slots slots2 p2 mode))
                           (list (list txid (pgs-apply-dirty (pgs-contents (pgs-sp cur pages) pages) dirty))
                                 (list (pgs-rec-txid cur) (pgs-contents (pgs-sp cur pages) pages))))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-apply-pages pgs-rec-shape-p pgs-step-try-cur-crash
                                      pgs-step-try-crash)
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-s-rec-facts)
                        (:instance pgs-step-try-crash)
                        (:instance pgs-step-try-cur-crash))
                  :cases ((equal (car (pgs-try sv (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid)
                                                                   keep pages)
                                               mode))
                                 :ok)))))

(defthm pgs-step-open-torn
  (let ((p2 (pgs-apply-pages (pgs-swr cur pages dirty fresh tfresh rs txid) keep pages)))
    (implies (and (pgs-step-hyps cur pages mode dirty fresh tfresh rs txid)
                  (not (pgs-rec-valid sv))
                  (or (equal slots2 (cons cur sv)) (equal slots2 (cons sv cur))))
             (equal (pgs-view (pgs-open-slots slots2 p2 mode))
                    (list (pgs-rec-txid cur) (pgs-contents (pgs-sp cur pages) pages)))))
  :hints (("Goal" :in-theory (disable pgs-try pgs-apply-pages pgs-rec-shape-p pgs-step-try-cur-crash)
                  :use ((:instance pgs-s-facts)
                        (:instance pgs-step-try-cur-crash)))))
