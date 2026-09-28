; fn: the page store's executable reclamation cycle (lane arena-store,
; 2026-09-27).  Prefix pgs-g-.
;
; The mark-and-sweep cycle of books/pagestore-reclaim.lisp, as the
; host runs it: over a stobj `pgs-gc' of its own (pgs-mem is untouched),
; every call bounded by a work quantum Q and resumable from the cursor it
; returns.
;
;   pgs-gm   the mark flags, one byte per physical address in [0, HWM0)
;   pgs-gf   the cycle's FREE0 flags, the same range
;   pgs-gs   scratch words: the host fills a record's directory run, then
;            each table page it names, here (its fill primitive), and the
;            cycle marks each entry's PHYS (entry J's PHYS is word 6J)
;
; The logical views are `pgs-g-marks-list' and `pgs-g-free0-list' (the
; flagged addresses, ascending).  Keystones (the host calls the subject):
;   pgs-g-mark-record-covers   marking a record's run, its directory's
;                              entries and its table pages' entries (the
;                              host's sequence of `pgs-g-mark-run' and
;                              `pgs-g-mark-words' steps, any positive
;                              quantum) marks every address below HWM0 that
;                              `pgs-rec-keeps' of the decoded record keeps
;   pgs-g-mark-record-covers-encoded
;                              the same over the model: the host fills the
;                              encodings of the record's directory and
;                              table pages (`pgs-decode-encode-run/-table')
;   pgs-g-sweep-step-is        one sweep step is `pgs-sweep' of its quantum,
;                              consed in order onto the accumulator; the
;                              cursor DESCENDS from HWM0 so that
;   pgs-g-sweep-all-is         the steps from HWM0 down to 0 accumulate
;                              exactly `pgs-sweep 0 HWM0' of the views
;   pgs-g-reclaim-sound        the keystone `pgs-reclaim-never-frees-live'
;                              for the executable cycle: marks covering the
;                              start disk's keeps and FREE0 flags covering
;                              the start free list make `pgs-g-install' of
;                              the swept list keep `pgs-alloc-inv' at the
;                              disk after any commits and forks of the cycle
(in-package "ACL2")
(include-book "pagestore-reclaim")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition pgs-entry-p)
                          (:definition pgs-ptab-p)
                          (:rewrite pgs-true-list-fix-when-true-listp)
                          (:rewrite pgs-x-nfix-when-natp))))

(defstobj pgs-gc
  (pgs-gm :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (pgs-gf :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (pgs-gs :type (array (unsigned-byte 64) (0)) :initially 0 :resizable t)
  :inline t)

; The fields as lists, for the theorems (closed after the leaf lemmas).
(defun pgs-g-m (st) (nth *pgs-gmi* st))
(defun pgs-g-f (st) (nth *pgs-gfi* st))
(defun pgs-g-s (st) (nth *pgs-gsi* st))

; Open: that the words the host's fill leaves in scratch are the pages'
; encodings is A-PGS-OBSERVE (`pgs-g-mark-record-covers-encoded' takes the
; encodings as the fill); its directory-length hypothesis is what the
; open's `pgs-dir-verdict' checks.  The per-disk marking (every valid
; record of every root) is the hypothesis of `pgs-g-reclaim-sound', not yet
; a composition of `pgs-g-mark-record'; `pgs-g-install' appends to the free
; list once per cycle (O(|FREE|)).

; =============================================================================
; 1. Flag lists: the logical view of a flag array is its flagged indices.

(defun pgs-g-flags (i l)
  (declare (xargs :guard (natp i) :verify-guards nil
                  :measure (nfix (- (len l) (nfix i)))))
  (if (< (nfix i) (len l))
      (if (equal (nth (nfix i) l) 0)
          (pgs-g-flags (+ 1 (nfix i)) l)
        (cons (nfix i) (pgs-g-flags (+ 1 (nfix i)) l)))
    nil))

(defthm pgs-g-member-flags
  (iff (member-equal x (pgs-g-flags i l))
       (and (natp x) (<= (nfix i) x) (< x (len l)) (not (equal (nth x l) 0)))))

(defthm pgs-g-flags-facts
  (and (nat-listp (pgs-g-flags i l))
       (pgs-all-below (pgs-g-flags i l) (len l))))

(in-theory (disable pgs-g-flags))

(defun pgs-g-marks-list (st) (pgs-g-flags 0 (pgs-g-m st)))
(defun pgs-g-free0-list (st) (pgs-g-flags 0 (pgs-g-f st)))

; Setting flags, and what a list of flags covers: every natural X in XS
; below the array's length has its flag set.
(defun pgs-g-set (x l)
  (if (and (natp x) (< x (len l))) (update-nth x 1 l) l))

(defun pgs-g-set-all (xs l)
  (if (atom xs) l (pgs-g-set-all (cdr xs) (pgs-g-set (car xs) l))))

(defun pgs-g-covered (xs l)
  (if (atom xs)
      t
    (and (or (not (natp (car xs))) (<= (len l) (car xs)) (not (equal (nth (car xs) l) 0)))
         (pgs-g-covered (cdr xs) l))))

(defthm pgs-g-len-set
  (equal (len (pgs-g-set x l)) (len l)))

(defthm pgs-g-len-set-all
  (equal (len (pgs-g-set-all xs l)) (len l)))

(defthm pgs-g-covered-set
  (implies (pgs-g-covered xs l) (pgs-g-covered xs (pgs-g-set x l))))

(defthm pgs-g-covered-set-here
  (pgs-g-covered (list x) (pgs-g-set x l)))

(defthm pgs-g-nth-set-nonzero
  (implies (not (equal (nth y l) 0)) (not (equal (nth y (pgs-g-set x l)) 0)))
  :hints (("Goal" :in-theory (enable pgs-g-set))))

(defthm pgs-g-nth-set-all-nonzero
  (implies (not (equal (nth y l) 0)) (not (equal (nth y (pgs-g-set-all xs l)) 0)))
  :hints (("Goal" :in-theory (disable pgs-g-set))))

(defthm pgs-g-nth-set-here
  (implies (and (natp x) (< x (len l))) (not (equal (nth x (pgs-g-set x l)) 0)))
  :hints (("Goal" :in-theory (enable pgs-g-set))))

(in-theory (disable pgs-g-set))

(defthm pgs-g-covered-set-all
  (implies (pgs-g-covered xs l) (pgs-g-covered xs (pgs-g-set-all ys l))))

(defthm pgs-g-covered-of-set-all
  (pgs-g-covered xs (pgs-g-set-all xs l))
  :hints (("Goal" :induct (pgs-g-set-all xs l))))

(defthm pgs-g-set-all-append
  (equal (pgs-g-set-all (append a b) l) (pgs-g-set-all b (pgs-g-set-all a l))))

(defthm pgs-g-covered-append
  (equal (pgs-g-covered (append a b) l) (and (pgs-g-covered a l) (pgs-g-covered b l))))

(defthm pgs-g-covered-flags
  (pgs-g-covered (pgs-g-flags i l) l)
  :hints (("Goal" :in-theory (enable pgs-g-flags))))

(defthm pgs-g-covered-subset
  ; What a flag list covers, it holds, when it is all natural and below
  ; the array's length.
  (implies (and (pgs-g-covered xs l) (nat-listp xs) (pgs-all-below xs (len l)))
           (pgs-subset xs (pgs-g-flags 0 l))))

(defthm pgs-g-flags-grow
  ; Setting flags only grows the view.
  (pgs-subset (pgs-g-flags 0 l) (pgs-g-flags 0 (pgs-g-set-all ys l)))
  :hints (("Goal" :in-theory (disable pgs-g-covered-subset pgs-g-set-all)
                  :use ((:instance pgs-g-covered-subset (xs (pgs-g-flags 0 l)) (l (pgs-g-set-all ys l)))))))

; =============================================================================
; 2. The cycle's start and the FREE0 snapshot.

(defun pgs-g-start (hwm0 pgs-gc)
  ; Both flag arrays cleared to HWM0 addresses (a resize to nothing, then to
  ; HWM0: fresh zeros), and the reserved page marked: `pgs-disk-keeps'
  ; keeps it whatever the roots hold, so the cycle keeps it too.
  (declare (xargs :stobjs pgs-gc :guard (natp hwm0)))
  (let* ((pgs-gc (resize-pgs-gm 0 pgs-gc))
         (pgs-gc (resize-pgs-gm hwm0 pgs-gc))
         (pgs-gc (resize-pgs-gf 0 pgs-gc))
         (pgs-gc (resize-pgs-gf hwm0 pgs-gc)))
    (if (< *pgs-reserved-page* (nfix hwm0))
        (update-pgs-gmi *pgs-reserved-page* 1 pgs-gc)
      pgs-gc)))

(local (defun pgs-g-down2 (i n) (if (zp n) i (pgs-g-down2 (1- (nfix i)) (1- n)))))

(defthm pgs-g-nth-of-zeros
  (implies (< (nfix i) (nfix n)) (equal (nth i (resize-list nil n 0)) 0))
  :hints (("Goal" :induct (pgs-g-down2 i n) :in-theory (enable nth resize-list))))

(defthm pgs-g-len-of-resize-list
  (equal (len (resize-list l n d)) (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

(local (defthm pgs-g-len-cdr-zeros
  (implies (posp n) (equal (len (cdr (resize-list nil n 0))) (- n 1)))
  :hints (("Goal" :expand ((resize-list nil n 0))))))

(local (defthm pgs-g-nth-of-marked-zeros
  (implies (and (natp x) (< x (nfix n)))
           (equal (nth x (cons 1 (cdr (resize-list nil n 0)))) (if (equal x 0) 1 0)))
  :hints (("Goal" :cases ((equal x 0))
                  :use ((:instance pgs-g-nth-of-zeros (i x)))
                  :expand ((resize-list nil n 0))))))

(defthm pgs-g-start-facts
  ; After the start: both arrays have HWM0 flags; the only mark is the
  ; reserved page's (when HWM0 reaches it) and no FREE0 flag is set.
  (and (equal (len (pgs-g-m (pgs-g-start hwm0 pgs-gc))) (nfix hwm0))
       (equal (len (pgs-g-f (pgs-g-start hwm0 pgs-gc))) (nfix hwm0))
       (iff (member-equal x (pgs-g-marks-list (pgs-g-start hwm0 pgs-gc)))
            (and (equal x *pgs-reserved-page*) (< *pgs-reserved-page* (nfix hwm0))))
       (not (member-equal x (pgs-g-free0-list (pgs-g-start hwm0 pgs-gc))))))

(in-theory (disable pgs-g-start))

(in-theory (disable pgs-g-m pgs-g-f pgs-g-s))

(defun pgs-g-flag-free (x pgs-gc)
  (declare (xargs :stobjs pgs-gc :guard t))
  (if (and (natp x) (< x (pgs-gf-length pgs-gc))) (update-pgs-gfi x 1 pgs-gc) pgs-gc))

(defthm pgs-g-flag-free-is
  (and (equal (pgs-g-f (pgs-g-flag-free x pgs-gc)) (pgs-g-set x (pgs-g-f pgs-gc)))
       (equal (pgs-g-m (pgs-g-flag-free x pgs-gc)) (pgs-g-m pgs-gc))
       (equal (pgs-g-s (pgs-g-flag-free x pgs-gc)) (pgs-g-s pgs-gc)))
  :hints (("Goal" :in-theory (enable pgs-g-set pgs-g-m pgs-g-f pgs-g-s))))

(in-theory (disable pgs-g-flag-free))

(defun pgs-g-load-free0 (free q pgs-gc)
  ; Flag the first Q addresses of FREE (the free list at the cycle's start);
  ; (mv REST pgs-gc), REST the addresses not yet flagged.
  (declare (xargs :stobjs pgs-gc :guard (natp q) :measure (nfix q)))
  (if (or (zp q) (atom free))
      (mv free pgs-gc)
    (let ((pgs-gc (pgs-g-flag-free (car free) pgs-gc)))
      (pgs-g-load-free0 (cdr free) (1- q) pgs-gc))))

(defun pgs-g-prefix (xs q)
  (if (or (zp q) (atom xs)) nil (cons (car xs) (pgs-g-prefix (cdr xs) (1- q)))))

(defun pgs-g-drop (xs q)
  (if (or (zp q) (atom xs)) xs (pgs-g-drop (cdr xs) (1- q))))

(defthm pgs-g-prefix-drop
  (equal (append (pgs-g-prefix xs q) (pgs-g-drop xs q)) xs))

(defthm pgs-g-len-drop
  (implies (and (posp q) (consp xs)) (< (len (pgs-g-drop xs q)) (len xs)))
  :rule-classes :linear)

(defthm pgs-g-load-free0-is
  (and (equal (mv-nth 0 (pgs-g-load-free0 free q pgs-gc)) (pgs-g-drop free q))
       (equal (pgs-g-f (mv-nth 1 (pgs-g-load-free0 free q pgs-gc)))
              (pgs-g-set-all (pgs-g-prefix free q) (pgs-g-f pgs-gc)))
       (equal (pgs-g-m (mv-nth 1 (pgs-g-load-free0 free q pgs-gc))) (pgs-g-m pgs-gc))
       (equal (pgs-g-s (mv-nth 1 (pgs-g-load-free0 free q pgs-gc))) (pgs-g-s pgs-gc))))

(defthm pgs-g-set-all-prefix-drop
  (equal (pgs-g-set-all (pgs-g-drop xs q) (pgs-g-set-all (pgs-g-prefix xs q) l))
         (pgs-g-set-all xs l))
  :hints (("Goal" :in-theory (disable pgs-g-set-all-append pgs-g-prefix-drop)
                  :use ((:instance pgs-g-set-all-append (a (pgs-g-prefix xs q)) (b (pgs-g-drop xs q)))
                        (:instance pgs-g-prefix-drop)))))

(defun pgs-g-load-free0-all (free q pgs-gc)
  ; The host's loop: `pgs-g-load-free0' until nothing is left.
  (declare (xargs :stobjs pgs-gc :guard (natp q) :measure (len free)))
  (if (or (zp q) (atom free))
      pgs-gc
    (mv-let (rest pgs-gc) (pgs-g-load-free0 free q pgs-gc)
      (pgs-g-load-free0-all rest q pgs-gc))))

(defthm pgs-g-load-free0-all-is
  (implies (posp q)
           (and (equal (pgs-g-f (pgs-g-load-free0-all free q pgs-gc))
                       (pgs-g-set-all free (pgs-g-f pgs-gc)))
                (equal (pgs-g-m (pgs-g-load-free0-all free q pgs-gc)) (pgs-g-m pgs-gc))
                (equal (pgs-g-s (pgs-g-load-free0-all free q pgs-gc)) (pgs-g-s pgs-gc))))
  :hints (("Goal" :induct (pgs-g-load-free0-all free q pgs-gc)
                  :in-theory (disable pgs-g-load-free0))))

; =============================================================================
; 3. Marking: a directory run, and the entries of the words in scratch.

(defun pgs-g-mark (x pgs-gc)
  (declare (xargs :stobjs pgs-gc :guard t))
  (if (and (natp x) (< x (pgs-gm-length pgs-gc))) (update-pgs-gmi x 1 pgs-gc) pgs-gc))

(defthm pgs-g-mark-is
  (and (equal (pgs-g-m (pgs-g-mark x pgs-gc)) (pgs-g-set x (pgs-g-m pgs-gc)))
       (equal (pgs-g-f (pgs-g-mark x pgs-gc)) (pgs-g-f pgs-gc))
       (equal (pgs-g-s (pgs-g-mark x pgs-gc)) (pgs-g-s pgs-gc)))
  :hints (("Goal" :in-theory (enable pgs-g-set pgs-g-m pgs-g-f pgs-g-s))))

(in-theory (disable pgs-g-mark))

(defun pgs-g-mark-addrs (a k pgs-gc)
  ; Mark A .. A+K-1.
  (declare (xargs :stobjs pgs-gc :guard (and (natp a) (natp k)) :measure (nfix k)))
  (if (zp k)
      pgs-gc
    (let ((pgs-gc (pgs-g-mark a pgs-gc)))
      (pgs-g-mark-addrs (+ 1 (nfix a)) (1- k) pgs-gc))))

(defthm pgs-g-mark-addrs-is
  (and (equal (pgs-g-m (pgs-g-mark-addrs a k pgs-gc))
              (pgs-g-set-all (pgs-run a k) (pgs-g-m pgs-gc)))
       (equal (pgs-g-f (pgs-g-mark-addrs a k pgs-gc)) (pgs-g-f pgs-gc))
       (equal (pgs-g-s (pgs-g-mark-addrs a k pgs-gc)) (pgs-g-s pgs-gc))))

(defun pgs-g-mark-run (a m q pgs-gc)
  ; One quantum of marking the M-page run at A: marks min(M, Q) pages;
  ; (mv A2 M2 pgs-gc), the run left to mark.
  (declare (xargs :stobjs pgs-gc :guard (and (natp a) (natp m) (natp q))))
  (let* ((k (min (nfix m) (nfix q)))
         (pgs-gc (pgs-g-mark-addrs (nfix a) k pgs-gc)))
    (mv (+ (nfix a) k) (- (nfix m) k) pgs-gc)))

(local (defun pgs-g-run-ind (a k m)
  (if (zp k) (list a m) (pgs-g-run-ind (+ 1 a) (1- k) (1- m)))))

(defthm pgs-g-run-split
  (implies (and (natp a) (natp k) (<= k (nfix m)))
           (equal (pgs-run a m) (append (pgs-run a k) (pgs-run (+ a k) (- (nfix m) k)))))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-g-run-ind a k m))))

(defun pgs-g-mark-run-all (a m q pgs-gc)
  ; The host's loop: `pgs-g-mark-run' until the run is marked.
  (declare (xargs :stobjs pgs-gc :guard (and (natp a) (natp m) (natp q)) :measure (nfix m)))
  (if (or (zp m) (zp q))
      pgs-gc
    (mv-let (a2 m2 pgs-gc) (pgs-g-mark-run a m q pgs-gc)
      (pgs-g-mark-run-all a2 m2 q pgs-gc))))

(defthm pgs-g-mark-run-all-is
  (implies (and (natp a) (posp q))
           (and (equal (pgs-g-m (pgs-g-mark-run-all a m q pgs-gc))
                       (pgs-g-set-all (pgs-run a m) (pgs-g-m pgs-gc)))
                (equal (pgs-g-f (pgs-g-mark-run-all a m q pgs-gc)) (pgs-g-f pgs-gc))
                (equal (pgs-g-s (pgs-g-mark-run-all a m q pgs-gc)) (pgs-g-s pgs-gc))))
  :hints (("Goal" :induct (pgs-g-mark-run-all a m q pgs-gc) :in-theory (disable pgs-g-mark-addrs))
          ("Subgoal *1/2" :use ((:instance pgs-g-run-split (k (min (nfix m) q)))))))

(defun pgs-g-word (a pgs-gc)
  ; Scratch word A, 0 past the end.
  (declare (xargs :stobjs pgs-gc :guard (natp a)))
  (if (< a (pgs-gs-length pgs-gc)) (nfix (pgs-gsi a pgs-gc)) 0))

(defthm pgs-g-nth-past-end
  (implies (<= (len l) (nfix a)) (equal (nth a l) nil))
  :hints (("Goal" :in-theory (enable nth))))

(defthm pgs-g-word-is
  (implies (natp a) (equal (pgs-g-word a pgs-gc) (nfix (nth a (pgs-g-s pgs-gc)))))
  :hints (("Goal" :in-theory (e/d (pgs-g-s) (nth)))))

(in-theory (disable pgs-g-word))

(defun pgs-g-mark-entries (j e pgs-gc)
  ; Mark the PHYS of scratch entries J .. E-1 (entry J's PHYS is word 6J).
  (declare (xargs :stobjs pgs-gc :guard (and (natp j) (natp e))
                  :measure (nfix (- (nfix e) (nfix j)))))
  (if (< (nfix j) (nfix e))
      (let ((pgs-gc (pgs-g-mark (pgs-g-word (* 6 (nfix j)) pgs-gc) pgs-gc)))
        (pgs-g-mark-entries (+ 1 (nfix j)) e pgs-gc))
    pgs-gc))

(defun pgs-g-word-physes (ws j e)
  ; The PHYS of entries J .. E-1 of the words WS.
  (declare (xargs :measure (nfix (- (nfix e) (nfix j)))))
  (if (< (nfix j) (nfix e))
      (cons (nfix (nth (* 6 (nfix j)) ws)) (pgs-g-word-physes ws (+ 1 (nfix j)) e))
    nil))

(defthm pgs-g-word-physes-empty
  (implies (<= (nfix e) (nfix j)) (equal (pgs-g-word-physes ws j e) nil)))

(defthm pgs-g-mark-entries-is
  (and (equal (pgs-g-m (pgs-g-mark-entries j e pgs-gc))
              (pgs-g-set-all (pgs-g-word-physes (pgs-g-s pgs-gc) j e) (pgs-g-m pgs-gc)))
       (equal (pgs-g-f (pgs-g-mark-entries j e pgs-gc)) (pgs-g-f pgs-gc))
       (equal (pgs-g-s (pgs-g-mark-entries j e pgs-gc)) (pgs-g-s pgs-gc))))

(defun pgs-g-mark-words (j n q pgs-gc)
  ; One quantum of marking the N entries in scratch: entries J .. up to
  ; J+Q-1 (below N); (mv J2 pgs-gc), J2 the next entry.
  (declare (xargs :stobjs pgs-gc :guard (and (natp j) (natp n) (natp q))))
  (let* ((e (min (nfix n) (+ (nfix j) (nfix q))))
         (pgs-gc (pgs-g-mark-entries j e pgs-gc)))
    (mv (max (nfix j) e) pgs-gc)))

(local (defun pgs-g-physes-ind (j m e)
  (declare (xargs :measure (nfix (- (nfix m) (nfix j)))))
  (if (< (nfix j) (nfix m)) (pgs-g-physes-ind (+ 1 (nfix j)) m e) (list j e))))

(defthm pgs-g-word-physes-split
  (implies (and (natp j) (natp m) (natp e) (<= j m) (<= m e))
           (equal (pgs-g-word-physes ws j e)
                  (append (pgs-g-word-physes ws j m) (pgs-g-word-physes ws m e))))
  :rule-classes nil
  :hints (("Goal" :induct (pgs-g-physes-ind j m e))))

(defun pgs-g-mark-words-all (j n q pgs-gc)
  ; The host's loop: `pgs-g-mark-words' until entry N.
  (declare (xargs :stobjs pgs-gc :guard (and (natp j) (natp n) (natp q))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (if (or (zp q) (<= (nfix n) (nfix j)))
      pgs-gc
    (mv-let (j2 pgs-gc) (pgs-g-mark-words j n q pgs-gc)
      (pgs-g-mark-words-all j2 n q pgs-gc))))

(defthm pgs-g-mark-words-all-done
  (implies (<= (nfix n) (nfix j)) (equal (pgs-g-mark-words-all j n q pgs-gc) pgs-gc)))

(defthm pgs-g-mark-words-all-is
  (implies (and (natp j) (posp q))
           (and (equal (pgs-g-m (pgs-g-mark-words-all j n q pgs-gc))
                       (pgs-g-set-all (pgs-g-word-physes (pgs-g-s pgs-gc) j n) (pgs-g-m pgs-gc)))
                (equal (pgs-g-f (pgs-g-mark-words-all j n q pgs-gc)) (pgs-g-f pgs-gc))
                (equal (pgs-g-s (pgs-g-mark-words-all j n q pgs-gc)) (pgs-g-s pgs-gc))))
  :hints (("Goal" :induct (pgs-g-mark-words-all j n q pgs-gc) :in-theory (disable pgs-g-mark-entries))
          ("Subgoal *1/2" :use ((:instance pgs-g-word-physes-split (ws (pgs-g-s pgs-gc))
                                           (m (min (nfix n) (+ j q))) (e (nfix n)))))))

; -----------------------------------------------------------------------------
; A record: the host's sequence.  `pgs-g-fill' is the logical twin of the
; host's fill primitive over the scratch array (the words it leaves are the
; page's: A-PGS-OBSERVE); TWS lists the record's table pages as
; (WORDS . ENTRY-COUNT).

(defun pgs-g-fill (ws st) (update-nth *pgs-gsi* ws st))

(defthm pgs-g-fill-is
  (and (equal (pgs-g-m (pgs-g-fill ws st)) (pgs-g-m st))
       (equal (pgs-g-f (pgs-g-fill ws st)) (pgs-g-f st))
       (equal (pgs-g-s (pgs-g-fill ws st)) ws))
  :hints (("Goal" :in-theory (enable pgs-g-m pgs-g-f pgs-g-s))))

(in-theory (disable pgs-g-fill))

(defun-nx pgs-g-mark-tables (tws q st)
  (if (atom tws)
      st
    (pgs-g-mark-tables (cdr tws) q
                       (pgs-g-mark-words-all 0 (nfix (cdar tws)) q (pgs-g-fill (caar tws) st)))))

(defun-nx pgs-g-mark-record (rec dws tws q st)
  ; Mark REC's directory run; fill scratch with its directory's words DWS
  ; and mark its entries; then each table page of TWS.
  (let* ((npages (pgs-rec-npages rec))
         (st (pgs-g-mark-run-all (pgs-rec-dir-addr rec) (pgs-dir-run-pages npages) q st))
         (st (pgs-g-mark-words-all 0 (pgs-ntables npages) q (pgs-g-fill dws st))))
    (pgs-g-mark-tables tws q st)))

(defun pgs-g-tables-physes (tws)
  (if (atom tws)
      nil
    (append (pgs-g-word-physes (caar tws) 0 (nfix (cdar tws))) (pgs-g-tables-physes (cdr tws)))))

(defthm pgs-g-mark-tables-is
  (implies (posp q)
           (equal (pgs-g-m (pgs-g-mark-tables tws q st))
                  (pgs-g-set-all (pgs-g-tables-physes tws) (pgs-g-m st))))
  :hints (("Goal" :induct (pgs-g-mark-tables tws q st)
                  :in-theory (disable pgs-g-mark-words-all))))

(defthm pgs-g-covered-of-subset
  (implies (and (pgs-subset xs ys) (pgs-g-covered ys l)) (pgs-g-covered xs l)))

(defthm pgs-g-nat-listp-run
  (implies (natp a) (nat-listp (pgs-run a m))))

(defthm pgs-g-nat-listp-physes
  (implies (pgs-ptab-p p) (nat-listp (pgs-ptab-physes p))))

(defthm pgs-g-rec-keeps-bound
  ; What a record keeps: natural, and among its run and its tables' PHYS.
  (and (nat-listp (pgs-rec-keeps rec dir tables))
       (pgs-subset (pgs-rec-keeps rec dir tables)
                   (append (pgs-run (pgs-rec-dir-addr rec) (pgs-dir-run-pages (pgs-rec-npages rec)))
                           (pgs-ptab-physes dir)
                           (pgs-ptab-physes (pgs-flatten tables)))))
  :hints (("Goal" :in-theory (e/d (pgs-rec-keeps) (pgs-dir-run-pages)))))

(defthm pgs-g-mark-record-covers
  ; The refinement: after the host's marking sequence for a record whose
  ; directory's PHYS are those of the directory words DWS and whose tables'
  ; PHYS are those of the table-page words TWS, every address below HWM0
  ; the record keeps is marked; and nothing marked before is unmarked.
  (implies (and (posp q)
                (equal (pgs-ptab-physes dir)
                       (pgs-g-word-physes dws 0 (pgs-ntables (pgs-rec-npages rec))))
                (equal (pgs-ptab-physes (pgs-flatten tables)) (pgs-g-tables-physes tws))
                (pgs-all-below (pgs-rec-keeps rec dir tables) (len (pgs-g-m st))))
           (and (pgs-subset (pgs-rec-keeps rec dir tables)
                            (pgs-g-marks-list (pgs-g-mark-record rec dws tws q st)))
                (pgs-subset (pgs-g-marks-list st)
                            (pgs-g-marks-list (pgs-g-mark-record rec dws tws q st)))))
  :hints (("Goal" :in-theory (e/d (pgs-g-mark-record)
                                  (pgs-rec-keeps pgs-g-covered-subset pgs-g-flags-grow
                                   pgs-dir-run-pages pgs-ntables pgs-ntables-as-tq pgs-g-mark-tables))
                  :use ((:instance pgs-g-covered-subset
                                   (xs (pgs-rec-keeps rec dir tables))
                                   (l (pgs-g-m (pgs-g-mark-record rec dws tws q st))))
                        (:instance pgs-g-flags-grow
                                   (l (pgs-g-m st))
                                   (ys (append (pgs-run (pgs-rec-dir-addr rec) (pgs-dir-run-pages (pgs-rec-npages rec)))
                                               (pgs-g-word-physes dws 0 (pgs-ntables (pgs-rec-npages rec)))
                                               (pgs-g-tables-physes tws))))
                        (:instance pgs-g-covered-of-subset
                                   (xs (pgs-rec-keeps rec dir tables))
                                   (ys (append (pgs-run (pgs-rec-dir-addr rec) (pgs-dir-run-pages (pgs-rec-npages rec)))
                                               (pgs-g-word-physes dws 0 (pgs-ntables (pgs-rec-npages rec)))
                                               (pgs-g-tables-physes tws)))
                                   (l (pgs-g-m (pgs-g-mark-record rec dws tws q st))))))))

;
; The words are the encodings: when the host fills scratch with the
; encoding of the record's directory D (`pgs-encode-run', the run's words)
; and of each table page T (`pgs-encode-table'), the PHYS the marking reads
; are the decoded model's (`pgs-decode-encode-run', `pgs-decode-encode-table'),
; so the marks cover `pgs-rec-keeps' of the record over D and its tables.

(local (defthm pgs-g-nth-of-nthcdr
  (equal (nth i (nthcdr n l)) (nth (+ (nfix i) (nfix n)) l))
  :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local (defun pgs-g-dec-ind (j k)
  (if (zp k) j (pgs-g-dec-ind (+ 1 j) (1- k)))))

(defthm pgs-g-physes-of-decode
  ; PHYS of the entries decoded from the words at entry J is what the
  ; marking reads (word 6I for entry I).
  (implies (natp j)
           (equal (pgs-ptab-physes (pgs-decode-table (nthcdr (* 6 j) ws) k))
                  (pgs-g-word-physes ws j (+ j (nfix k)))))
  :hints (("Goal" :induct (pgs-g-dec-ind j k)
                  :in-theory (enable pgs-decode-entry))))

(defun pgs-g-decode-tables (tws)
  (if (atom tws)
      nil
    (cons (pgs-decode-table (caar tws) (nfix (cdar tws))) (pgs-g-decode-tables (cdr tws)))))

(defthm pgs-g-physes-of-decode-tables
  (equal (pgs-ptab-physes (pgs-flatten (pgs-g-decode-tables tws))) (pgs-g-tables-physes tws))
  :hints (("Goal" :induct (pgs-g-decode-tables tws))
          ("Subgoal *1/2" :use ((:instance pgs-g-physes-of-decode (j 0) (ws (caar tws))
                                           (k (nfix (cdar tws))))))))

(defun pgs-g-encode-tables (ts)
  ; The words the host fills for table pages TS, with their entry counts.
  (declare (xargs :verify-guards nil))
  (if (atom ts) nil (cons (cons (pgs-encode-table (car ts)) (len (car ts))) (pgs-g-encode-tables (cdr ts)))))

(defun pgs-g-tables-fit (ts)
  (if (atom ts) t (and (pgs-ptab-p (car ts)) (pgs-x-entries-fit (car ts)) (pgs-g-tables-fit (cdr ts)))))

(defthm pgs-g-decode-encode-tables
  (implies (pgs-g-tables-fit ts)
           (equal (pgs-g-decode-tables (pgs-g-encode-tables ts)) (true-list-fix ts))))

(defthm pgs-g-flatten-true-list-fix
  (equal (pgs-flatten (true-list-fix ts)) (pgs-flatten ts)))

(defthm pgs-g-mark-record-covers-encoded
  ; The refinement over the model: the host fills the encoding of the
  ; record's directory DIR (whose length is the directory size the record
  ; names, as the open's `pgs-dir-verdict' checks) and of its table pages
  ; TABLES; its marking covers every address below HWM0 the record keeps.
  (implies (and (posp q)
                (pgs-ptab-p dir) (pgs-x-entries-fit dir)
                (equal (len dir) (pgs-ntables (pgs-rec-npages rec)))
                (pgs-g-tables-fit tables)
                (pgs-all-below (pgs-rec-keeps rec dir tables) (len (pgs-g-m st))))
           (pgs-subset (pgs-rec-keeps rec dir tables)
                       (pgs-g-marks-list
                        (pgs-g-mark-record rec (pgs-encode-run dir (pgs-dir-run-pages (pgs-rec-npages rec)))
                                           (pgs-g-encode-tables tables) q st))))
  :hints (("Goal" :in-theory (disable pgs-g-mark-record-covers pgs-g-physes-of-decode pgs-rec-keeps
                                      pgs-g-mark-record pgs-g-marks-list pgs-ntables pgs-ntables-as-tq pgs-dir-run-pages
                                      pgs-decode-encode-run pgs-g-physes-of-decode-tables
                                      pgs-g-decode-encode-tables pgs-g-encode-tables)
                  :use ((:instance pgs-g-mark-record-covers
                                   (dws (pgs-encode-run dir (pgs-dir-run-pages (pgs-rec-npages rec))))
                                   (tws (pgs-g-encode-tables tables)))
                        (:instance pgs-decode-encode-run (c dir) (m (pgs-dir-run-pages (pgs-rec-npages rec))))
                        (:instance pgs-g-physes-of-decode (j 0) (k (len dir))
                                   (ws (pgs-encode-run dir (pgs-dir-run-pages (pgs-rec-npages rec)))))
                        (:instance pgs-g-physes-of-decode-tables (tws (pgs-g-encode-tables tables)))
                        (:instance pgs-g-decode-encode-tables (ts tables))))))

; =============================================================================
; 4. The sweep, in quanta, the cursor descending from HWM0.

(defun pgs-g-sweep-down (a lo acc pgs-gc)
  ; Cons onto ACC, from A-1 down to LO, each address neither marked nor
  ; free at the start.
  (declare (xargs :stobjs pgs-gc
                  :guard (and (natp a) (natp lo)
                              (<= a (pgs-gm-length pgs-gc)) (<= a (pgs-gf-length pgs-gc)))
                  :measure (nfix (- (nfix a) (nfix lo)))))
  (if (<= (nfix a) (nfix lo))
      acc
    (let ((b (- (nfix a) 1)))
      (pgs-g-sweep-down b lo
                        (if (and (eql (pgs-gmi b pgs-gc) 0) (eql (pgs-gfi b pgs-gc) 0))
                            (cons b acc)
                          acc)
                        pgs-gc))))

(defthm pgs-g-gmi-gfi-is
  (and (equal (pgs-gmi i pgs-gc) (nth i (pgs-g-m pgs-gc)))
       (equal (pgs-gfi i pgs-gc) (nth i (pgs-g-f pgs-gc))))
  :hints (("Goal" :in-theory (enable pgs-g-m pgs-g-f))))

(defun pgs-g-sweep-step (hi n acc pgs-gc)
  ; One quantum: sweep [max(0, HI-N), HI) onto ACC; (mv LO ACC2), LO the
  ; next cursor (0 when the sweep is done).
  (declare (xargs :stobjs pgs-gc
                  :guard (and (natp hi) (natp n)
                              (<= hi (pgs-gm-length pgs-gc)) (<= hi (pgs-gf-length pgs-gc)))))
  (let ((lo (if (< (nfix n) (nfix hi)) (- (nfix hi) (nfix n)) 0)))
    (mv lo (pgs-g-sweep-down hi lo acc pgs-gc))))

(defthm pgs-g-sweep-empty
  (implies (<= (nfix hi) (nfix lo)) (equal (pgs-sweep lo hi marks free0) nil)))

(defthm pgs-g-sweep-last
  ; The sweep of [A-1, A) of the views, from the flags.
  (implies (and (posp a) (<= a (len (pgs-g-m st))) (<= a (len (pgs-g-f st))))
           (equal (pgs-sweep (+ -1 a) a (pgs-g-marks-list st) (pgs-g-free0-list st))
                  (if (and (equal (nth (+ -1 a) (pgs-g-m st)) 0) (equal (nth (+ -1 a) (pgs-g-f st)) 0))
                      (list (+ -1 a))
                    nil)))
  :hints (("Goal" :expand ((pgs-sweep (+ -1 a) a (pgs-g-marks-list st) (pgs-g-free0-list st))))))

(defthm pgs-g-sweep-peel
  ; The sweep of [LO, A) is that of [LO, A-1), then A-1 when it is flagged
  ; in neither array.
  (implies (and (natp lo) (natp a) (< lo a) (<= a (len (pgs-g-m st))) (<= a (len (pgs-g-f st))))
           (equal (pgs-sweep lo a (pgs-g-marks-list st) (pgs-g-free0-list st))
                  (append (pgs-sweep lo (+ -1 a) (pgs-g-marks-list st) (pgs-g-free0-list st))
                          (if (and (equal (nth (+ -1 a) (pgs-g-m st)) 0) (equal (nth (+ -1 a) (pgs-g-f st)) 0))
                              (list (+ -1 a))
                            nil))))
  :hints (("Goal" :in-theory (disable pgs-sweep pgs-g-marks-list pgs-g-free0-list)
                  :use ((:instance pgs-sweep-split (lo lo) (mid (+ -1 a)) (hi a)
                                   (marks (pgs-g-marks-list st)) (free0 (pgs-g-free0-list st)))
                        (:instance pgs-g-sweep-last)))))

(defthm pgs-g-sweep-down-is
  (implies (and (natp lo) (natp a) (<= lo a) (<= a (len (pgs-g-m st))) (<= a (len (pgs-g-f st))))
           (equal (pgs-g-sweep-down a lo acc st)
                  (append (pgs-sweep lo a (pgs-g-marks-list st) (pgs-g-free0-list st)) acc)))
  :hints (("Goal" :induct (pgs-g-sweep-down a lo acc st)
                  :in-theory (disable pgs-sweep pgs-g-marks-list pgs-g-free0-list pgs-g-sweep-last))))

(in-theory (disable pgs-g-sweep-peel pgs-g-sweep-last))

(defthm pgs-g-sweep-step-is
  ; One step is the model's sweep of its quantum, consed in order onto ACC.
  (implies (and (natp hi) (<= hi (len (pgs-g-m st))) (<= hi (len (pgs-g-f st))))
           (equal (pgs-g-sweep-step hi n acc st)
                  (let ((lo (if (< (nfix n) hi) (- hi (nfix n)) 0)))
                    (mv lo (append (pgs-sweep lo hi (pgs-g-marks-list st) (pgs-g-free0-list st)) acc)))))
  :hints (("Goal" :in-theory (disable pgs-g-sweep-down pgs-sweep pgs-g-marks-list pgs-g-free0-list))))

(in-theory (disable pgs-g-sweep-step))

(defun pgs-g-sweep-all (hi n acc pgs-gc)
  ; The host's loop: `pgs-g-sweep-step' from HI down to 0.
  (declare (xargs :stobjs pgs-gc
                  :guard (and (natp hi) (natp n)
                              (<= hi (pgs-gm-length pgs-gc)) (<= hi (pgs-gf-length pgs-gc)))
                  :measure (nfix hi)
                  :hints (("Goal" :in-theory (enable pgs-g-sweep-step)))
                  :guard-hints (("Goal" :in-theory (enable pgs-g-sweep-step)))))
  (if (or (zp hi) (zp n))
      acc
    (mv-let (lo acc) (pgs-g-sweep-step hi n acc pgs-gc)
      (pgs-g-sweep-all lo n acc pgs-gc))))

(defthm pgs-g-sweep-all-is
  ; The whole sweep from quanta: the steps from HI down to 0 accumulate
  ; the model's `pgs-sweep 0 HI' of the views, ascending.
  (implies (and (natp hi) (posp n) (<= hi (len (pgs-g-m st))) (<= hi (len (pgs-g-f st))))
           (equal (pgs-g-sweep-all hi n acc st)
                  (append (pgs-sweep 0 hi (pgs-g-marks-list st) (pgs-g-free0-list st)) acc)))
  :hints (("Goal" :induct (pgs-g-sweep-all hi n acc st)
                  :in-theory (disable pgs-sweep pgs-g-marks-list pgs-g-free0-list))
          ("Subgoal *1/2" :use ((:instance pgs-sweep-split (lo 0) (mid (if (< n hi) (- hi n) 0)) (hi hi)
                                           (marks (pgs-g-marks-list st)) (free0 (pgs-g-free0-list st)))))))

; =============================================================================
; 5. The cycle against the keystone.
;
; The free list after the sweep: the allocator's free list NOW, then the
; swept addresses; the high-water mark unchanged.  This is `pgs-reclaim'.

(defun pgs-g-install (alloc swept)
  (declare (xargs :guard (true-listp swept)))
  (list (append (true-list-fix (car (true-list-fix alloc))) swept)
        (nfix (cadr (true-list-fix alloc)))))

(defthm pgs-g-install-is-reclaim
  (equal (pgs-g-install alloc (pgs-sweep 0 hwm0 marks free0))
         (pgs-reclaim alloc marks free0 hwm0)))

; The model's reclamation step IS the install the host calls
; (host/native/proto-pagestore.lisp fnps-reclaim), over the swept list.
(defthm pgs-reclaim-is-g-install
  (implies (equal swept (pgs-sweep 0 hwm0 marks free0))
           (equal (pgs-reclaim alloc marks free0 hwm0) (pgs-g-install alloc swept)))
  :rule-classes nil)

(in-theory (disable pgs-g-install))

; What runs during the cycle: commits and forks.  OPS is a list of
; (:commit R MODE DIRTY) and (:fork R R2 MODE); a commit takes the allocator
; state its plan returns.
(defun pgs-g-cycle-run (disk alloc ops)
  ; (DISK . ALLOC) after OPS.
  (if (atom ops)
      (cons disk alloc)
    (let ((op (car ops)))
      (if (eq (car op) :fork)
          (pgs-g-cycle-run (pgs-fork disk (second op) (third op) (fourth op)) alloc (cdr ops))
        (pgs-g-cycle-run (pgs-commit disk (second op) (third op) (fourth op) alloc)
                         (fifth (pgs-plan-commit disk (second op) (third op) (fourth op) alloc))
                         (cdr ops))))))

(defun pgs-g-ops-ok (disk alloc ops)
  ; Each commit's root opens and its dirty pages are in order (the commit
  ; keystones' hypotheses).
  (if (atom ops)
      t
    (let ((op (car ops)))
      (if (eq (car op) :fork)
          (pgs-g-ops-ok (pgs-fork disk (second op) (third op) (fourth op)) alloc (cdr ops))
        (and (equal (car (pgs-open disk (second op) (third op))) :ok)
             (pgs-lpages-ok (pgs-dirty-lpages (fourth op))
                            (len (fourth (pgs-open disk (second op) (third op)))) 0)
             (pgs-g-ops-ok (pgs-commit disk (second op) (third op) (fourth op) alloc)
                           (fifth (pgs-plan-commit disk (second op) (third op) (fourth op) alloc))
                           (cdr ops)))))))

(defthm pgs-g-invariants-of-cycle-run
  (implies (and (pgs-alloc-inv alloc disk)
                (pgs-cycle-inv disk marks free0 hwm0 alloc)
                (pgs-g-ops-ok disk alloc ops))
           (and (pgs-alloc-inv (cdr (pgs-g-cycle-run disk alloc ops)) (car (pgs-g-cycle-run disk alloc ops)))
                (pgs-cycle-inv (car (pgs-g-cycle-run disk alloc ops)) marks free0 hwm0
                               (cdr (pgs-g-cycle-run disk alloc ops)))))
  :hints (("Goal" :induct (pgs-g-cycle-run disk alloc ops)
                  :in-theory (union-theories '(pgs-g-cycle-run pgs-g-ops-ok
                                               pgs-alloc-inv-after-commit pgs-cycle-inv-after-commit
                                               pgs-invariants-after-fork car-cons cdr-cons)
                                             (theory 'minimal-theory))))
  :rule-classes nil)

(defthm pgs-g-from-mono
  (implies (and (pgs-from xs a hwm) (pgs-subset a b)) (pgs-from xs b hwm)))

(defthm pgs-g-cycle-start
  ; The marking phase's postcondition establishes the cycle invariant:
  ; marks covering the start disk's keeps, FREE0 covering its free list.
  (implies (and (pgs-alloc-inv alloc disk)
                (pgs-subset (pgs-disk-keeps disk) marks)
                (pgs-subset (pgs-alloc-free alloc) free0))
           (pgs-cycle-inv disk marks free0 (pgs-alloc-hwm alloc) alloc))
  :hints (("Goal" :in-theory (disable pgs-alloc-inv pgs-disk-keeps pgs-alloc-free pgs-alloc-hwm
                                      pgs-g-from-mono pgs-cycle-inv-start)
                  :use ((:instance pgs-cycle-inv-start)
                        (:instance pgs-g-from-mono (xs (pgs-disk-keeps disk))
                                   (a (append (pgs-disk-keeps disk) (pgs-alloc-free alloc)))
                                   (b (append marks free0)) (hwm (pgs-alloc-hwm alloc))))))
  :rule-classes nil)

(defthm pgs-g-reclaim-sound
  ; The keystone for the executable cycle.  At the start (DISK0, ALLOC0) the
  ; allocator invariant holds; the marks cover what DISK0 keeps and the
  ; FREE0 flags cover ALLOC0's free list; HWM0 is ALLOC0's high-water mark
  ; and the arrays reach it.  Then after any commits and forks OPS, the
  ; free list the host installs from the sweep's quanta keeps the allocator
  ; invariant at the disk then: no swept address is kept by a valid record
  ; of any root.
  (implies (and (pgs-alloc-inv alloc0 disk0)
                (pgs-subset (pgs-disk-keeps disk0) (pgs-g-marks-list st))
                (pgs-subset (pgs-alloc-free alloc0) (pgs-g-free0-list st))
                (equal hwm0 (pgs-alloc-hwm alloc0))
                (<= hwm0 (len (pgs-g-m st))) (<= hwm0 (len (pgs-g-f st)))
                (posp n)
                (pgs-g-ops-ok disk0 alloc0 ops))
           (pgs-alloc-inv (pgs-g-install (cdr (pgs-g-cycle-run disk0 alloc0 ops))
                                         (pgs-g-sweep-all hwm0 n nil st))
                          (car (pgs-g-cycle-run disk0 alloc0 ops))))
  :hints (("Goal" :in-theory (disable pgs-alloc-inv pgs-cycle-inv pgs-reclaim pgs-disk-keeps pgs-alloc-free
                                      pgs-alloc-hwm pgs-g-cycle-run pgs-g-ops-ok pgs-g-marks-list
                                      pgs-g-free0-list pgs-sweep pgs-g-sweep-all
                                      pgs-reclaim-never-frees-live)
                  :use ((:instance pgs-g-cycle-start (alloc alloc0) (disk disk0)
                                   (marks (pgs-g-marks-list st)) (free0 (pgs-g-free0-list st)))
                        (:instance pgs-g-invariants-of-cycle-run (alloc alloc0) (disk disk0)
                                   (marks (pgs-g-marks-list st)) (free0 (pgs-g-free0-list st)))
                        (:instance pgs-g-sweep-all-is (hi hwm0) (acc nil))
                        (:instance pgs-reclaim-never-frees-live
                                   (alloc (cdr (pgs-g-cycle-run disk0 alloc0 ops)))
                                   (disk (car (pgs-g-cycle-run disk0 alloc0 ops)))
                                   (marks (pgs-g-marks-list st)) (free0 (pgs-g-free0-list st))))))
  :rule-classes nil)

; =============================================================================
; 6. Ground witnesses.

(defun pgs-g-read-flags (i n acc pgs-gc)
  ; Witness helper: the mark flags of [I, N), descending onto ACC.
  (declare (xargs :stobjs pgs-gc :guard (and (natp i) (natp n) (<= n (pgs-gm-length pgs-gc)))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (< (nfix i) (nfix n))
      (pgs-g-read-flags i (- (nfix n) 1) (cons (pgs-gmi (- (nfix n) 1) pgs-gc) acc) pgs-gc)
    acc))

(defun pgs-g-witness-cycle ()
  ; A cycle over 10 addresses on the executable: FREE0 = (2); a record whose
  ; one-page directory run is at 5, naming one table page at 7, which names
  ; one data page at 9.  Marked with quantum 1; swept in two ways: a step
  ; of 4 and then quanta of 4, and one quantum of 100.  Returns (MARK-FLAGS
  ; SWEEP-IN-QUANTA SWEEP-AT-ONCE FIRST-STEP).
  (declare (xargs :guard t :verify-guards nil))
  (with-local-stobj pgs-gc
    (mv-let (r pgs-gc)
      (let* ((pgs-gc (pgs-g-start 10 pgs-gc))
             (pgs-gc (pgs-g-load-free0-all '(2) 1 pgs-gc))
             (pgs-gc (pgs-g-mark-run-all 5 (pgs-dir-run-pages 1) 1 pgs-gc))
             (pgs-gc (resize-pgs-gs 0 pgs-gc))
             (pgs-gc (resize-pgs-gs 2048 pgs-gc))
             (pgs-gc (update-pgs-gsi 0 7 pgs-gc))
             (pgs-gc (update-pgs-gsi 1 1 pgs-gc))
             (pgs-gc (pgs-g-mark-words-all 0 (pgs-ntables 1) 1 pgs-gc))
             (pgs-gc (update-pgs-gsi 0 9 pgs-gc))
             (pgs-gc (pgs-g-mark-words-all 0 1 1 pgs-gc)))
        (mv-let (lo acc) (pgs-g-sweep-step 10 4 nil pgs-gc)
          (mv (list (pgs-g-read-flags 0 10 nil pgs-gc)
                    (pgs-g-sweep-all lo 4 acc pgs-gc)
                    (pgs-g-sweep-all 10 100 nil pgs-gc)
                    (list lo acc))
              pgs-gc)))
      r)))

(defthm pgs-g-witness-cycle-ok
  ; Marked exactly the reserved page 0 (by the start) and 5, 7, 9; two
  ; quanta equal one sweep; the first step swept [6, 10) and left the
  ; cursor at 6.
  (equal (pgs-g-witness-cycle)
         '((1 0 0 0 0 1 0 1 0 1) (1 3 4 6 8) (1 3 4 6 8) (6 (6 8)))))

; The same record on the model's disk: root :r, slot 0 a valid record
; (txid 1, directory at 5, 1 logical page); page 5 is the directory, page 7
; the table page.
(defun pgs-g-w-disk ()
  (cons (list (cons 5 '((7 1 0))) (cons 7 '((9 1 0))))
        (list (cons :r (cons (pgs-make-rec 1 5 1 0) nil)))))

(defconst *pgs-g-w-gm* '(1 0 0 0 0 1 0 1 0 1))     ; the witness's marks
(defconst *pgs-g-w-gf* '(0 0 1 0 0 0 0 0 0 0))     ; FREE0 = (2)

(defthm pgs-g-witness-keeps
  (equal (pgs-disk-keeps (pgs-g-w-disk)) '(0 5 7 9))
  :hints (("Goal" :in-theory (enable pgs-rec-keeps pgs-rec-valid pgs-rec-ok pgs-rec-body pgs-rec-shape-p
                                     pgs-rec-npages pgs-rec-dir-addr pgs-ntables))))

(defthm pgs-g-witness-reclaim
  ; `pgs-g-reclaim-sound''s complete antecedent (no commits during the
  ; cycle) and its conclusion, on the witness's arrays: the installed free
  ; list is (2 1 3 4 6 8).
  (let ((disk (pgs-g-w-disk)) (alloc '((2) 10)) (st (list *pgs-g-w-gm* *pgs-g-w-gf* nil)))
    (and (pgs-alloc-inv alloc disk)
         (pgs-subset (pgs-disk-keeps disk) (pgs-g-marks-list st))
         (pgs-subset (pgs-alloc-free alloc) (pgs-g-free0-list st))
         (equal 10 (pgs-alloc-hwm alloc))
         (<= 10 (len (pgs-g-m st))) (<= 10 (len (pgs-g-f st)))
         (pgs-g-ops-ok disk alloc nil)
         (equal (pgs-g-install (cdr (pgs-g-cycle-run disk alloc nil)) (pgs-g-sweep-all 10 4 nil st))
                '((2 1 3 4 6 8) 10))
         (pgs-alloc-inv (pgs-g-install (cdr (pgs-g-cycle-run disk alloc nil)) (pgs-g-sweep-all 10 4 nil st))
                        (car (pgs-g-cycle-run disk alloc nil)))))
  :hints (("Goal" :in-theory (e/d (pgs-g-m pgs-g-f pgs-g-flags pgs-g-install pgs-g-sweep-step)
                                  (pgs-disk-keeps pgs-g-w-disk (:e pgs-g-w-disk)))
                  :use pgs-g-witness-keeps))
  :rule-classes nil)

; Teeth (corrupted-state witnesses: the arrays are not what the host's
; marking and snapshot produce).
(defthm pgs-g-tooth-unmarked-keep
  ; A mark set missing the kept data page 9 (its table page skipped): every
  ; other hypothesis holds, the marks miss a kept address, the sweep frees
  ; 9, and the allocator invariant fails.
  (let ((disk (pgs-g-w-disk)) (alloc '((2) 10))
        (st (list '(1 0 0 0 0 1 0 1 0 0) *pgs-g-w-gf* nil)))
    (and (pgs-alloc-inv alloc disk)
         (not (pgs-subset (pgs-disk-keeps disk) (pgs-g-marks-list st)))
         (pgs-subset (pgs-alloc-free alloc) (pgs-g-free0-list st))
         (<= 10 (len (pgs-g-m st))) (<= 10 (len (pgs-g-f st)))
         (pgs-g-ops-ok disk alloc nil)
         (member-equal 9 (pgs-g-sweep-all 10 4 nil st))
         (not (pgs-alloc-inv (pgs-g-install (cdr (pgs-g-cycle-run disk alloc nil)) (pgs-g-sweep-all 10 4 nil st))
                             (car (pgs-g-cycle-run disk alloc nil))))))
  :hints (("Goal" :in-theory (e/d (pgs-g-m pgs-g-f pgs-g-flags pgs-g-install pgs-g-sweep-step)
                                  (pgs-disk-keeps pgs-g-w-disk (:e pgs-g-w-disk)))
                  :use pgs-g-witness-keeps))
  :rule-classes nil)

(defthm pgs-g-tooth-free0-unflagged
  ; FREE0 flags missing the free address 2: every other hypothesis holds,
  ; the sweep frees 2 again, and the installed free list repeats it.
  (let ((disk (pgs-g-w-disk)) (alloc '((2) 10))
        (st (list *pgs-g-w-gm* '(0 0 0 0 0 0 0 0 0 0) nil)))
    (and (pgs-alloc-inv alloc disk)
         (pgs-subset (pgs-disk-keeps disk) (pgs-g-marks-list st))
         (not (pgs-subset (pgs-alloc-free alloc) (pgs-g-free0-list st)))
         (<= 10 (len (pgs-g-m st))) (<= 10 (len (pgs-g-f st)))
         (pgs-g-ops-ok disk alloc nil)
         (member-equal 2 (pgs-g-sweep-all 10 4 nil st))
         (not (pgs-alloc-inv (pgs-g-install (cdr (pgs-g-cycle-run disk alloc nil)) (pgs-g-sweep-all 10 4 nil st))
                             (car (pgs-g-cycle-run disk alloc nil))))))
  :hints (("Goal" :in-theory (e/d (pgs-g-m pgs-g-f pgs-g-flags pgs-g-install pgs-g-sweep-step)
                                  (pgs-disk-keeps pgs-g-w-disk (:e pgs-g-w-disk)))
                  :use pgs-g-witness-keeps))
  :rule-classes nil)
