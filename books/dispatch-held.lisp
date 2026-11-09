; The rows an owner kind K holds in the operation table and the pool, as one
; observation, and what each write of another owner keeps of it. The dispatch's
; held frame (machines.lisp fn2-dh-chain-*, assembly-dispatch) is this
; observation at the commit kind, kept by every run of a kind that holds no
; batch membership.
(in-package "ACL2")
(include-book "arm-children")
(deflabel fn2-dh-start)

;; ---------------------------------------------------------------------------
;; HELD ROWS. An operation row K owns that is not free; a pool row K owns that
;; is neither free nor handed (a handed row is its target's to accept,
;; fn2-pool-accept-own). Free rows are excluded because the reserves take the
;; free head after checking only its phase or state.
(defun-nx fn2-dh-op-held (k s ops)
  (and (equal (nth s (nth *fn2-ops-owner-kind$ai* ops)) k)
       (not (equal (nth s (nth *fn2-ops-phase$ai* ops)) *fn2-op-phase-free*))))
(defun-nx fn2-dh-pool-held (k r pool)
  (and (equal (nth r (nth *fn2-pool-owner-kind$ai* pool)) k)
       (not (equal (nth r (nth *fn2-pool-state$ai* pool)) *fn2-pool-state-free*))
       (not (equal (nth r (nth *fn2-pool-state$ai* pool)) *fn2-pool-state-handed*))))

;; A row's values at the column indices COLS.
(defun-nx fn2-dh-row (cols s x)
  (if (atom cols) nil (cons (nth s (nth (car cols) x)) (fn2-dh-row (cdr cols) s x))))
(defun fn2-dh-range (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil (cons i (fn2-dh-range (+ 1 i) n))))
;; Every operation column but the free-chain link (meaningful only on a free
;; row); every pool column but the free-chain link and the extent (base, cap:
;; observed for every row, below).
(make-event
 (let* ((ops (strip-cars (fn2-view-layout 'fn2-ops (w state))))
        (pool (strip-cars (fn2-view-layout 'fn2-pool (w state)))))
   (value `(progn
             (defconst *fn2-dh-op-cols*
               ',(remove (position-eq 'next-free ops) (fn2-dh-range 0 (len ops))))
             (defconst *fn2-dh-pool-cols*
               ',(set-difference-equal (fn2-dh-range 0 (len pool))
                                       (list (position-eq 'next-free pool) (position-eq 'base pool)
                                             (position-eq 'cap pool))))))))
(assert-event (and (equal *fn2-ops-rows* (+ 1 (car (last *fn2-dh-op-cols*))))
                   (member-equal *fn2-ops-owner-kind$ai* *fn2-dh-op-cols*)
                   (member-equal *fn2-ops-phase$ai* *fn2-dh-op-cols*)
                   (member-equal *fn2-pool-owner-kind$ai* *fn2-dh-pool-cols*)
                   (member-equal *fn2-pool-state$ai* *fn2-dh-pool-cols*)
                   (not (member-equal *fn2-pool-base$ai* *fn2-dh-pool-cols*))
                   (not (member-equal *fn2-pool-cap$ai* *fn2-dh-pool-cols*))
                   (< (car (last *fn2-dh-pool-cols*)) *fn2-pool-rows*)
                   (< *fn2-pool-rows* *fn2-pool-datai*)))

;; ---------------------------------------------------------------------------
;; THE OBSERVATION. Operations: the row count and every held row's columns.
;; Pool: the row count, every row's extent, every held row's columns, and --
;; when the extents are ordered and disjoint, a fact of the extents alone --
;; the data length and every held row's octets over its whole extent.
(defun-nx fn2-dh-op-rows (k n ops)
  (if (zp n) nil
    (cons (and (fn2-dh-op-held k (1- n) ops) (fn2-dh-row *fn2-dh-op-cols* (1- n) ops))
          (fn2-dh-op-rows k (1- n) ops))))
(defun-nx fn2-dh-ops-obs (k ops)
  (cons (nth *fn2-ops-rows* ops) (fn2-dh-op-rows k (nfix (nth *fn2-ops-rows* ops)) ops)))

(defun-nx fn2-dh-extents (n pool)
  (if (zp n) nil
    (cons (cons (nth (1- n) (nth *fn2-pool-base$ai* pool)) (nth (1- n) (nth *fn2-pool-cap$ai* pool)))
          (fn2-dh-extents (1- n) pool))))
(defun-nx fn2-dh-ordered (n pool)
  ; row i's extent ends at or before row i+1's begins
  (if (zp n) t
    (and (natp (nth (1- n) (nth *fn2-pool-base$ai* pool)))
         (natp (nth (1- n) (nth *fn2-pool-cap$ai* pool)))
         (or (zp (1- n))
             (<= (+ (nth (- n 2) (nth *fn2-pool-base$ai* pool)) (nth (- n 2) (nth *fn2-pool-cap$ai* pool)))
                 (nth (1- n) (nth *fn2-pool-base$ai* pool))))
         (fn2-dh-ordered (1- n) pool))))
(defun-nx fn2-dh-pool-rows (k n pool)
  (if (zp n) nil
    (cons (and (fn2-dh-pool-held k (1- n) pool) (fn2-dh-row *fn2-dh-pool-cols* (1- n) pool))
          (fn2-dh-pool-rows k (1- n) pool))))
(defun-nx fn2-dh-octets (k n pool)
  (if (zp n) nil
    (cons (and (fn2-dh-pool-held k (1- n) pool)
               (fn2-pool-logical-octets (nth (1- n) (nth *fn2-pool-cap$ai* pool))
                                        (nth (1- n) (nth *fn2-pool-base$ai* pool)) pool))
          (fn2-dh-octets k (1- n) pool))))
(defun-nx fn2-dh-pool-obs (k pool)
  (let ((n (nfix (nth *fn2-pool-rows* pool))))
    (list (nth *fn2-pool-rows* pool) (fn2-dh-extents n pool) (fn2-dh-pool-rows k n pool)
          (and (natp (nth *fn2-pool-rows* pool)) (fn2-dh-ordered n pool)
               (cons (len (nth *fn2-pool-datai* pool)) (fn2-dh-octets k n pool))))))

;; ---------------------------------------------------------------------------
;; THE ALGEBRA, once. A write outside the observed fields keeps the
;; observation. Writes at one row S compose through the WIPE of S (every
;; observed column at S cleared, its owner made another kind's): the
;; observation of a row not held equals that of its wipe, and the wipe
;; absorbs any observed write at S, so a sequence of writes at S keeps the
;; observation when S is held before and after neither -- whatever the row
;; looks like between them (a reserve sets the state before the owner).
;; a row index is used as its natural
(defthm fn2-dh-nth-nfix (equal (nth (nfix n) l) (nth n l)))
(defthm fn2-dh-update-nth-nfix (equal (update-nth (nfix n) v l) (update-nth n v l)))
(defthm fn2-dh-op-held-nfix (equal (fn2-dh-op-held k (nfix s) ops) (fn2-dh-op-held k s ops)))
(defthm fn2-dh-pool-held-nfix (equal (fn2-dh-pool-held k (nfix s) pool) (fn2-dh-pool-held k s pool)))
(defthm fn2-dh-row-of-other
  (implies (and (nat-listp cols) (not (member-equal (nfix f) cols)))
           (equal (fn2-dh-row cols i (update-nth f v x)) (fn2-dh-row cols i x)))
  :hints (("Goal" :induct (fn2-dh-row cols i x))))
(defthm fn2-dh-op-held-of-other
  (implies (and (not (equal (nfix f) *fn2-ops-owner-kind$ai*)) (not (equal (nfix f) *fn2-ops-phase$ai*)))
           (equal (fn2-dh-op-held k i (update-nth f v ops)) (fn2-dh-op-held k i ops))))
(defthm fn2-dh-pool-held-of-other
  (implies (and (not (equal (nfix f) *fn2-pool-owner-kind$ai*)) (not (equal (nfix f) *fn2-pool-state$ai*)))
           (equal (fn2-dh-pool-held k i (update-nth f v pool)) (fn2-dh-pool-held k i pool))))
(defthm fn2-dh-op-rows-of-other
  (implies (not (member-equal (nfix f) *fn2-dh-op-cols*))
           (equal (fn2-dh-op-rows k n (update-nth f v ops)) (fn2-dh-op-rows k n ops)))
  :hints (("Goal" :induct (fn2-dh-op-rows k n ops) :in-theory (disable fn2-dh-row fn2-dh-op-held))))
(defthm fn2-dh-ops-obs-of-other
  (implies (and (not (member-equal (nfix f) *fn2-dh-op-cols*)) (not (equal (nfix f) *fn2-ops-rows*)))
           (equal (fn2-dh-ops-obs k (update-nth f v ops)) (fn2-dh-ops-obs k ops)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn2-dh-op-rows))))
(defthm fn2-dh-pool-rows-of-other
  (implies (not (member-equal (nfix f) *fn2-dh-pool-cols*))
           (equal (fn2-dh-pool-rows k n (update-nth f v pool)) (fn2-dh-pool-rows k n pool)))
  :hints (("Goal" :induct (fn2-dh-pool-rows k n pool) :in-theory (disable fn2-dh-row fn2-dh-pool-held))))
(defthm fn2-dh-extents-of-other
  (implies (and (not (equal (nfix f) *fn2-pool-base$ai*)) (not (equal (nfix f) *fn2-pool-cap$ai*)))
           (equal (fn2-dh-extents n (update-nth f v pool)) (fn2-dh-extents n pool))))
(defthm fn2-dh-ordered-of-other
  (implies (and (not (equal (nfix f) *fn2-pool-base$ai*)) (not (equal (nfix f) *fn2-pool-cap$ai*)))
           (equal (fn2-dh-ordered n (update-nth f v pool)) (fn2-dh-ordered n pool))))
(defthm fn2-dh-logical-octets-of-other
  (implies (not (equal (nfix f) *fn2-pool-datai*))
           (equal (fn2-pool-logical-octets m b (update-nth f v pool)) (fn2-pool-logical-octets m b pool))))
(defthm fn2-dh-octets-of-other
  (implies (and (not (member-equal (nfix f) *fn2-dh-pool-cols*)) (not (equal (nfix f) *fn2-pool-datai*))
                (not (equal (nfix f) *fn2-pool-base$ai*)) (not (equal (nfix f) *fn2-pool-cap$ai*)))
           (equal (fn2-dh-octets k n (update-nth f v pool)) (fn2-dh-octets k n pool)))
  :hints (("Goal" :induct (fn2-dh-octets k n pool) :in-theory (disable fn2-pool-logical-octets fn2-dh-pool-held))))
(defthm fn2-dh-pool-obs-of-other
  (implies (and (not (member-equal (nfix f) *fn2-dh-pool-cols*)) (not (equal (nfix f) *fn2-pool-rows*))
                (not (equal (nfix f) *fn2-pool-datai*))
                (not (equal (nfix f) *fn2-pool-base$ai*)) (not (equal (nfix f) *fn2-pool-cap$ai*)))
           (equal (fn2-dh-pool-obs k (update-nth f v pool)) (fn2-dh-pool-obs k pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn2-dh-pool-rows fn2-dh-octets fn2-dh-extents fn2-dh-ordered))))

;; THE WIPE of row S over the observed columns COLS (OKC the owner column).
(defun fn2-dh-other (k) (declare (xargs :guard t)) (if (equal k 0) 1 0))
(defun-nx fn2-dh-wipe (cols okc k s x)
  (if (atom cols) x
    (fn2-dh-wipe (cdr cols) okc k s
                 (update-nth (car cols) (update-nth s (if (equal (car cols) okc) (fn2-dh-other k) nil) (nth (car cols) x)) x))))
(local (defthm fn2-dh-update-nth-same
         (equal (update-nth n a (update-nth n b l)) (update-nth n a l))))
(local (defthm fn2-dh-update-nth-diff
         (implies (not (equal (nfix m) (nfix n)))
                  (equal (update-nth m a (update-nth n b l)) (update-nth n b (update-nth m a l))))
         :rule-classes ((:rewrite :loop-stopper ((m n))))))
(defthm fn2-dh-nth-of-wipe-off-row
  (implies (and (natp i) (natp s) (not (equal i s)))
           (equal (nth i (nth c (fn2-dh-wipe cols okc k s x))) (nth i (nth c x))))
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(defthm fn2-dh-nth-of-wipe-other
  (implies (and (nat-listp cols) (not (member-equal (nfix f) cols)))
           (equal (nth f (fn2-dh-wipe cols okc k s x)) (nth f x)))
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(defthm fn2-dh-nth-of-wipe-at-row
  (implies (and (natp s) (natp c) (member-equal c cols) (nat-listp cols) (no-duplicatesp-equal cols))
           (equal (nth s (nth c (fn2-dh-wipe cols okc k s x))) (if (equal c okc) (fn2-dh-other k) nil)))
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(defthm fn2-dh-wipe-absorbs
  (implies (and (natp s) (natp c) (member-equal c cols) (nat-listp cols) (no-duplicatesp-equal cols))
           (equal (fn2-dh-wipe cols okc k s (update-nth c (update-nth s v (nth c x)) x))
                  (fn2-dh-wipe cols okc k s x)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(defthm fn2-dh-wipe-commutes
  (implies (and (natp f) (nat-listp cols) (not (member-equal f cols)))
           (equal (fn2-dh-wipe cols okc k s (update-nth f v x)) (update-nth f v (fn2-dh-wipe cols okc k s x))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(defthm fn2-dh-logical-octets-of-wipe
  (implies (and (nat-listp cols) (not (member-equal *fn2-pool-datai* cols)))
           (equal (fn2-pool-logical-octets m b (fn2-dh-wipe cols okc k s x)) (fn2-pool-logical-octets m b x)))
  :hints (("Goal" :induct (fn2-pool-logical-octets m b x))))
(defthm fn2-dh-wipe-nfix
  (equal (fn2-dh-wipe cols okc k (nfix s) x) (fn2-dh-wipe cols okc k s x))
  :hints (("Goal" :induct (fn2-dh-wipe cols okc k s x))))
(in-theory (disable fn2-dh-wipe))

(defun-nx fn2-dh-op-wipe (k s ops) (fn2-dh-wipe *fn2-dh-op-cols* *fn2-ops-owner-kind$ai* k s ops))
(defun-nx fn2-dh-pool-wipe (k s pool) (fn2-dh-wipe *fn2-dh-pool-cols* *fn2-pool-owner-kind$ai* k s pool))
(defthm fn2-dh-nth-of-op-wipe-other
  (implies (not (member-equal (nfix f) *fn2-dh-op-cols*))
           (equal (nth f (fn2-dh-op-wipe k s ops)) (nth f ops))))
(defthm fn2-dh-nth-of-pool-wipe-other
  (implies (not (member-equal (nfix f) *fn2-dh-pool-cols*))
           (equal (nth f (fn2-dh-pool-wipe k s pool)) (nth f pool))))
(defthm fn2-dh-row-of-wipe
  (implies (and (natp i) (natp s) (not (equal i s)))
           (equal (fn2-dh-row cols2 i (fn2-dh-wipe cols okc k s x)) (fn2-dh-row cols2 i x)))
  :hints (("Goal" :induct (fn2-dh-row cols2 i x))))
(defthm fn2-dh-op-rows-of-wipe
  (implies (and (natp s) (not (fn2-dh-op-held k s ops)))
           (equal (fn2-dh-op-rows k n (fn2-dh-op-wipe k s ops)) (fn2-dh-op-rows k n ops)))
  :hints (("Goal" :induct (fn2-dh-op-rows k n ops) :in-theory (disable fn2-dh-row))
          ("Subgoal *1/2" :cases ((equal s (+ -1 n))))))
(defthm fn2-dh-ops-obs-of-wipe-natp
  (implies (and (natp s) (not (fn2-dh-op-held k s ops)))
           (equal (fn2-dh-ops-obs k (fn2-dh-op-wipe k s ops)) (fn2-dh-ops-obs k ops)))
  :hints (("Goal" :in-theory (disable fn2-dh-op-rows fn2-dh-op-wipe fn2-dh-op-held))))
(defthm fn2-dh-op-wipe-nfix (equal (fn2-dh-op-wipe k (nfix s) ops) (fn2-dh-op-wipe k s ops))
  :hints (("Goal" :in-theory (enable fn2-dh-op-wipe))))
(defthm fn2-dh-ops-obs-of-wipe
  (implies (not (fn2-dh-op-held k s ops))
           (equal (fn2-dh-ops-obs k (fn2-dh-op-wipe k s ops)) (fn2-dh-ops-obs k ops)))
  :hints (("Goal" :in-theory (disable fn2-dh-ops-obs fn2-dh-op-wipe fn2-dh-op-held)
           :use ((:instance fn2-dh-ops-obs-of-wipe-natp (s (nfix s)))))))
(defthm fn2-dh-op-held-of-wipe
  (not (fn2-dh-op-held k s (fn2-dh-op-wipe k s ops)))
  :hints (("Goal" :use ((:instance fn2-dh-nth-of-wipe-at-row (s (nfix s)) (c *fn2-ops-owner-kind$ai*)
                                   (cols *fn2-dh-op-cols*) (okc *fn2-ops-owner-kind$ai*) (x ops))))))
(defthm fn2-dh-pool-held-of-wipe
  (not (fn2-dh-pool-held k s (fn2-dh-pool-wipe k s pool)))
  :hints (("Goal" :use ((:instance fn2-dh-nth-of-wipe-at-row (s (nfix s)) (c *fn2-pool-owner-kind$ai*)
                                   (cols *fn2-dh-pool-cols*) (okc *fn2-pool-owner-kind$ai*) (x pool))))))
(defthm fn2-dh-pool-rows-of-wipe
  (implies (and (natp s) (not (fn2-dh-pool-held k s pool)))
           (equal (fn2-dh-pool-rows k n (fn2-dh-pool-wipe k s pool)) (fn2-dh-pool-rows k n pool)))
  :hints (("Goal" :induct (fn2-dh-pool-rows k n pool) :in-theory (disable fn2-dh-row))
          ("Subgoal *1/2" :cases ((equal s (+ -1 n))))))
(defthm fn2-dh-octets-of-wipe
  (implies (and (natp s) (not (fn2-dh-pool-held k s pool)))
           (equal (fn2-dh-octets k n (fn2-dh-pool-wipe k s pool)) (fn2-dh-octets k n pool)))
  :hints (("Goal" :induct (fn2-dh-octets k n pool) :in-theory (disable fn2-pool-logical-octets))
          ("Subgoal *1/2" :cases ((equal s (+ -1 n))))))
(defthm fn2-dh-extents-of-wipe
  (equal (fn2-dh-extents n (fn2-dh-pool-wipe k s pool)) (fn2-dh-extents n pool)))
(defthm fn2-dh-ordered-of-wipe
  (equal (fn2-dh-ordered n (fn2-dh-pool-wipe k s pool)) (fn2-dh-ordered n pool)))
(defthm fn2-dh-pool-obs-of-wipe-natp
  (implies (and (natp s) (not (fn2-dh-pool-held k s pool)))
           (equal (fn2-dh-pool-obs k (fn2-dh-pool-wipe k s pool)) (fn2-dh-pool-obs k pool)))
  :hints (("Goal" :in-theory (disable fn2-dh-pool-rows fn2-dh-octets fn2-dh-pool-wipe fn2-dh-pool-held
                                      fn2-dh-extents fn2-dh-ordered))))
(defthm fn2-dh-pool-wipe-nfix (equal (fn2-dh-pool-wipe k (nfix s) pool) (fn2-dh-pool-wipe k s pool))
  :hints (("Goal" :in-theory (enable fn2-dh-pool-wipe))))
(defthm fn2-dh-pool-obs-of-wipe
  (implies (not (fn2-dh-pool-held k s pool))
           (equal (fn2-dh-pool-obs k (fn2-dh-pool-wipe k s pool)) (fn2-dh-pool-obs k pool)))
  :hints (("Goal" :in-theory (disable fn2-dh-pool-obs fn2-dh-pool-wipe fn2-dh-pool-held)
           :use ((:instance fn2-dh-pool-obs-of-wipe-natp (s (nfix s)))))))
(in-theory (disable fn2-dh-op-wipe fn2-dh-pool-wipe))

;; ---------------------------------------------------------------------------
;; THE PER-SETTER LEMMAS (fn2-dh-setters): for every updater of the operation
;; table and the pool -- the stobj's own and the column setters -- its field
;; read back (-NTH), its observation and its wipe. An observed column's write
;; at row I is the wipe of I when I is not held after it, and the wipe of I
;; absorbs it; any other field's write keeps the observation and commutes
;; with every wipe. The row count, the extents (base, cap: only init writes
;; them) and the data get no observation lemma (the data's is
;; fn2-dh-pool-obs-of-data-write), so a writer of any of them is refused.
(defun fn2-dh-name-prefix-p (prefix sym)
  (declare (xargs :mode :program))
  (let ((n (symbol-name sym)))
    (and (<= (length prefix) (length n)) (equal (subseq n 0 (length prefix)) prefix))))
(defun fn2-dh-updaters (names stobj)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((or (fn2-dh-name-prefix-p (concatenate 'string "UPDATE-" (symbol-name stobj) "-") (car names))
             (fn2-dh-name-prefix-p (concatenate 'string "RESIZE-" (symbol-name stobj) "-") (car names)))
         (cons (car names) (fn2-dh-updaters (cdr names) stobj)))
        (t (fn2-dh-updaters (cdr names) stobj))))
;; (index inner row) of an updater's body over STOBJ: the field it writes, the
;; field's new value, and for a column's (i v STOBJ) updater the row variable
(defun fn2-dh-updater-shape (u stobj world)
  (declare (xargs :mode :program))
  (let ((b (getpropc u 'unnormalized-body nil world)) (formals (formals u world)))
    (cond ((and (consp b) (eq (car b) 'update-nth) (quotep (cadr b)) (eq (cadddr b) stobj))
           (list (unquote (cadr b)) (caddr b) nil))
          ((and (consp b) (eq (car b) 'update-nth-array) (quotep (cadr b)) (eq (car (cddddr b)) stobj))
           (list (unquote (cadr b)) `(update-nth ,(caddr b) ,(cadddr b) (nth ,(unquote (cadr b)) ,stobj))
                 (and (equal formals (list 'i 'v stobj)) 'i)))
          (t nil))))
(defun fn2-dh-sym (obs u) (declare (xargs :mode :program)) (fn2-columns-sym obs (concatenate 'string "-OF-" (symbol-name u))))
;; U's three lemmas; ENABLE opens U to the update-nth of field J (a raw
;; updater and update-nth-array, or a column setter and its raw updater,
;; whose lemmas then apply).
(defun fn2-dh-setter-lemmas (u formals j inner row stobj spec skip enable rawp)
  (declare (xargs :mode :program))
  (let* ((obs (car spec)) (held (cadr spec)) (wipe (caddr spec)) (cols (cadddr spec))
         (rows (nth 4 spec)) (okc (nth 5 spec)) (var (nth 6 spec))
         (call `(,u ,@formals))
         (wcall (subst `(,wipe k dh-s ,stobj) stobj call)))
    (append
     (and rawp
          `((defthm ,(fn2-columns-pre "FN2-DH-NTH-OF-" u)
              (equal (nth f ,call) (if (equal (nfix f) ,j) ,inner (nth f ,stobj)))
              :hints (("Goal" :in-theory (e/d ,enable (nth update-nth)))))))
     (if (member-equal j cols)
         (and row
              `((defthm ,(fn2-dh-sym obs u)
                  (implies (not (,held k ,row ,call))
                           (equal (,obs k ,call) (,obs k (,wipe k ,row ,stobj))))
                  :hints (("Goal" :in-theory ,(if rawp `(e/d (,wipe ,@enable) (,obs ,held nth update-nth)) `(e/d ,enable (,obs ,held ,wipe nth update-nth)))
                           ,@(and rawp
                                  `(:use ((:instance ,(fn2-columns-sym obs "-OF-WIPE") (s ,row) (,var ,call))
                                          (:instance fn2-dh-wipe-absorbs (cols ',cols) (okc ,okc) (s (nfix ,row)) (c ,j)
                                                     (v ,(caddr inner)) (x ,stobj))))))))
                (defthm ,(fn2-dh-sym wipe u)
                  (equal (,wipe k ,row ,call) (,wipe k ,row ,stobj))
                  :hints (("Goal" :in-theory ,(if rawp `(e/d (,wipe ,@enable) (nth update-nth)) `(e/d ,enable (,wipe nth update-nth)))
                           ,@(and rawp
                                  `(:use ((:instance fn2-dh-wipe-absorbs (cols ',cols) (okc ,okc) (s (nfix ,row)) (c ,j)
                                                     (v ,(caddr inner)) (x ,stobj))))))))))
       (append
        (and (not (equal j rows)) (not (member-equal j skip))
             `((defthm ,(fn2-dh-sym obs u) (equal (,obs k ,call) (,obs k ,stobj))
                 :hints (("Goal" :in-theory ,(if rawp `(e/d ,enable (,obs nth update-nth)) `(e/d ,enable (,obs nth update-nth)))
                          ,@(and rawp `(:use ((:instance ,(fn2-columns-sym obs "-OF-OTHER") (f ,j) (v ,inner)
                                                          (,var ,stobj))))))))))
        (and (not (member-equal j (nth 7 spec)))
        `((defthm ,(fn2-dh-sym wipe u) (equal (,wipe k dh-s ,call) ,wcall)
            :hints (("Goal" :in-theory ,(if rawp `(e/d (,wipe ,@enable) (nth update-nth)) `(e/d ,enable (,wipe nth update-nth)))
                     ,@(and rawp `(:use ((:instance fn2-dh-wipe-commutes (cols ',cols) (okc ,okc) (s dh-s) (f ,j)
                                                    (v ,(subst `(,wipe k dh-s ,stobj) stobj inner))
                                                    (x ,stobj)))))))))))))))
(defun fn2-dh-updater-events (us stobj spec skip world)
  (declare (xargs :mode :program))
  (if (atom us) nil
    (let ((shape (fn2-dh-updater-shape (car us) stobj world)))
      (append (and shape
                   (fn2-dh-setter-lemmas (car us) (formals (car us) world) (car shape) (cadr shape) (caddr shape)
                                         stobj spec skip (list (car us) 'update-nth-array) t))
              (fn2-dh-updater-events (cdr us) stobj spec skip world)))))
;; The column setters (fn2-ops-set-X i v fn2-ops), each its column's raw updater.
(defun fn2-dh-column-setter-events (names k stobj spec skip world)
  (declare (xargs :mode :program))
  (if (atom names) nil
    (let* ((set (fn2-columns-col-name stobj (fn2-columns-pre "SET-" (car names)))))
      (append
       (and (function-symbolp set world)
            (fn2-dh-setter-lemmas set (list 'i 'v stobj) k nil 'i stobj spec skip (list set) nil))
       (fn2-dh-column-setter-events (cdr names) (+ 1 k) stobj spec skip world)))))
(defun fn2-dh-specs ()
  (declare (xargs :mode :program))
  (list (list 'fn2-ops (list 'fn2-dh-ops-obs 'fn2-dh-op-held 'fn2-dh-op-wipe *fn2-dh-op-cols* *fn2-ops-rows*
                             *fn2-ops-owner-kind$ai* 'ops nil)
              nil)
        (list 'fn2-pool (list 'fn2-dh-pool-obs 'fn2-dh-pool-held 'fn2-dh-pool-wipe *fn2-dh-pool-cols* *fn2-pool-rows*
                              *fn2-pool-owner-kind$ai* 'pool (list *fn2-pool-datai*))
              (list *fn2-pool-datai* *fn2-pool-base$ai* *fn2-pool-cap$ai*))))
(defun fn2-dh-setter-events (specs rawp world)
  (declare (xargs :mode :program))
  (if (atom specs) nil
    (let* ((stobj (caar specs)) (spec (cadar specs)) (skip (caddar specs)))
      (append (if rawp
                  (fn2-dh-updater-events (fn2-dh-updaters (caddr (getpropc stobj 'stobj nil world)) stobj) stobj spec skip world)
                (fn2-dh-column-setter-events (strip-cars (fn2-view-layout stobj world)) 0 stobj spec skip world))
              (fn2-dh-setter-events (cdr specs) rawp world)))))
(defmacro fn2-dh-setters ()
  '(progn (make-event (value (cons 'progn (fn2-dh-setter-events (fn2-dh-specs) t (w state)))))
          (make-event (value (cons 'progn (fn2-dh-setter-events (fn2-dh-specs) nil (w state)))))))
(fn2-dh-setters)

;; An octet written inside a row the observation does not hold, when the
;; extents are ordered: no held row's octets change.
;; the ordering at one row: its extent is natural and ends at or before the next row's
(defthm fn2-dh-ordered-at
  (implies (and (fn2-dh-ordered n pool) (natp j) (< j (nfix n)))
           (and (natp (nth j (nth *fn2-pool-base$ai* pool))) (natp (nth j (nth *fn2-pool-cap$ai* pool)))
                (implies (< 0 j)
                         (<= (+ (nth (1- j) (nth *fn2-pool-base$ai* pool)) (nth (1- j) (nth *fn2-pool-cap$ai* pool)))
                             (nth j (nth *fn2-pool-base$ai* pool))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dh-ordered n pool))))
(defun fn2-dh-down (j) (if (zp j) 0 (fn2-dh-down (1- j))))
(defthm fn2-dh-ordered-below
  (implies (and (fn2-dh-ordered n pool) (natp i) (natp j) (< i j) (< j (nfix n)))
           (<= (+ (nth i (nth *fn2-pool-base$ai* pool)) (nth i (nth *fn2-pool-cap$ai* pool)))
               (nth j (nth *fn2-pool-base$ai* pool))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-dh-down j) :in-theory (disable fn2-dh-ordered))
          ("Subgoal *1/2" :use ((:instance fn2-dh-ordered-at (j j)) (:instance fn2-dh-ordered-at (j (1- j)))))))
(defthm fn2-dh-ordered-natp
  (implies (and (fn2-dh-ordered n pool) (natp i) (< i (nfix n)))
           (and (natp (nth i (nth *fn2-pool-base$ai* pool))) (natp (nth i (nth *fn2-pool-cap$ai* pool)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-dh-ordered-at (j i))))))
(defthm fn2-dh-octets-of-data-write
  (implies (and (fn2-dh-ordered n pool) (natp r) (< r (nfix n)) (<= (nfix m) (nfix n))
                (not (fn2-dh-pool-held k r pool)) (natp x)
                (<= (nth r (nth *fn2-pool-base$ai* pool)) x)
                (< x (+ (nth r (nth *fn2-pool-base$ai* pool)) (nth r (nth *fn2-pool-cap$ai* pool)))))
           (equal (fn2-dh-octets k m (update-fn2-pool-datai x v pool)) (fn2-dh-octets k m pool)))
  :hints (("Goal" :induct (fn2-dh-octets k m pool) :in-theory (disable fn2-pool-logical-octets))
          ("Subgoal *1/2" :use ((:instance fn2-dh-ordered-below (i r) (j (1- m)))
                                (:instance fn2-dh-ordered-below (i (1- m)) (j r))
                                (:instance fn2-dh-ordered-natp (i r))
                                (:instance fn2-dh-ordered-natp (i (1- m)))
                                (:instance fn2-pool-logical-octets-of-update-datai
                                           (k x) (fn2-pool pool) (n (nth (1- m) (nth *fn2-pool-cap$ai* pool)))
                                           (b (nth (1- m) (nth *fn2-pool-base$ai* pool))))))))
(defthm fn2-dh-pool-obs-zp
  (implies (zp n) (and (equal (fn2-dh-octets k n pool) nil) (equal (fn2-dh-pool-rows k n pool) nil)
                       (equal (fn2-dh-extents n pool) nil) (equal (fn2-dh-ordered n pool) t))))
(defthm fn2-dh-pool-held-of-update-datai
  (equal (fn2-dh-pool-held k r (update-fn2-pool-datai x v pool)) (fn2-dh-pool-held k r pool)))
(defthm fn2-dh-pool-parts-of-update-datai
  (and (equal (fn2-dh-extents n (update-fn2-pool-datai x v pool)) (fn2-dh-extents n pool))
       (equal (fn2-dh-ordered n (update-fn2-pool-datai x v pool)) (fn2-dh-ordered n pool))
       (equal (fn2-dh-pool-rows k n (update-fn2-pool-datai x v pool)) (fn2-dh-pool-rows k n pool)))
  :hints (("Goal" :in-theory (e/d (update-fn2-pool-datai update-nth-array)
                                  (fn2-dh-extents fn2-dh-ordered fn2-dh-pool-rows)))))
(defthm fn2-dh-pool-obs-of-data-write
  (implies (and (natp r) (< r (nth *fn2-pool-rows* pool)) (not (fn2-dh-pool-held k r pool))
                (implies (integerp (nth r (nth *fn2-pool-base$ai* pool))) (integerp x))
                (<= (nth r (nth *fn2-pool-base$ai* pool)) x)
                (< x (+ (nth r (nth *fn2-pool-base$ai* pool)) (nth r (nth *fn2-pool-cap$ai* pool))))
                (< x (len (nth *fn2-pool-datai* pool))))
           (equal (fn2-dh-pool-obs k (update-fn2-pool-datai x v pool)) (fn2-dh-pool-obs k pool)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn2-dh-pool-held fn2-dh-octets fn2-dh-extents fn2-dh-ordered fn2-dh-pool-rows)
           :use ((:instance fn2-dh-octets-of-data-write (n (nfix (nth *fn2-pool-rows* pool)))
                            (m (nfix (nth *fn2-pool-rows* pool))))
                 (:instance fn2-dh-ordered-natp (i r) (n (nfix (nth *fn2-pool-rows* pool))))))))
;; A copy loop writing [DST, DST+N) inside a row the observation does not hold.
(defthm fn2-dh-pool-obs-of-copy-up
  (implies (and (natp r) (< r (nth *fn2-pool-rows* pool)) (not (fn2-dh-pool-held k r pool))
                (implies (integerp (nth r (nth *fn2-pool-base$ai* pool))) (integerp dst))
                (<= (nth r (nth *fn2-pool-base$ai* pool)) dst)
                (<= (+ dst (nfix n)) (+ (nth r (nth *fn2-pool-base$ai* pool)) (nth r (nth *fn2-pool-cap$ai* pool))))
                (<= (+ dst (nfix n)) (len (nth *fn2-pool-datai* pool))))
           (equal (fn2-dh-pool-obs k (fn2-pool-copy-up src dst n pool)) (fn2-dh-pool-obs k pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pool-copy-up src dst n pool) :in-theory (e/d (fn2-pool-copy-up) (fn2-dh-pool-obs fn2-dh-pool-held)))
          ("Subgoal *1/2" :use ((:instance fn2-dh-pool-obs-of-data-write (x dst) (v (fn2-pool-datai src pool)))))))
(defthm fn2-dh-pool-obs-of-copy-down
  (implies (and (natp r) (< r (nth *fn2-pool-rows* pool)) (not (fn2-dh-pool-held k r pool))
                (implies (integerp (nth r (nth *fn2-pool-base$ai* pool))) (integerp dst))
                (<= (nth r (nth *fn2-pool-base$ai* pool)) dst)
                (<= (+ dst (nfix n)) (+ (nth r (nth *fn2-pool-base$ai* pool)) (nth r (nth *fn2-pool-cap$ai* pool))))
                (<= (+ dst (nfix n)) (len (nth *fn2-pool-datai* pool))))
           (equal (fn2-dh-pool-obs k (fn2-pool-copy-down src dst n pool)) (fn2-dh-pool-obs k pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-pool-copy-down src dst n pool) :in-theory (e/d (fn2-pool-copy-down) (fn2-dh-pool-obs fn2-dh-pool-held)))
          ("Subgoal *1/2" :use ((:instance fn2-dh-pool-obs-of-data-write (x (+ dst n -1))
                                           (v (fn2-pool-datai (+ src n -1) pool)))))))

;; ---------------------------------------------------------------------------
;; THE PRIMITIVES: each pool and operation write keeps the observation of
;; every kind K but the owner it writes as (OKIND, or the accepting TKIND):
;; the owner check names the row, a reserve takes a free one, an accept a
;; handed one. Recorded in the table fn2-dh-keeps (fn -> ((obs position
;; stobj hyps) ...)) for the chain (machines.lisp fn2-dh-chain-*).
(defun fn2-dh-keeps-name (obs fn) (declare (xargs :mode :program)) (fn2-columns-sym obs (concatenate 'string "-OF-" (symbol-name fn))))
(defmacro fn2-dh-keeps (fn obs pos stobj hyps &key enable use)
  (let* ((formals-call `(,fn ,@(car hyps)))
         (out (if pos `(mv-nth ,pos ,formals-call) formals-call)))
    `(progn
       (defthm ,(fn2-dh-keeps-name obs fn)
         (implies (and ,@(cdr hyps)) (equal (,obs fn2-dh-k ,out) (,obs fn2-dh-k ,stobj)))
         :hints (("Goal" :in-theory (e/d (,fn ,@enable) (,obs nth update-nth)) ,@(and use `(:use ,use)))))
       (table fn2-dh-keeps ',fn (cons '(,obs ,pos ,stobj ,(pairlis$ (cdr hyps) nil))
                                      (cdr (assoc-eq ',fn (table-alist 'fn2-dh-keeps world))))))))
(defconst *fn2-dh-pool-codes*
  '(fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-reserve fn2-dh-pool-obs 3 fn2-pool
  ((class okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))))
(fn2-dh-keeps fn2-pool-release fn2-dh-pool-obs 1 fn2-pool
  ((slot gen okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-lease-in fn2-dh-pool-obs 2 fn2-pool
  ((slot gen len opslot opgen okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-lease-out fn2-dh-pool-obs 1 fn2-pool
  ((slot gen off len okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-hand fn2-dh-pool-obs 1 fn2-pool
  ((slot gen okind oslot ogen tkind tslot tgen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-accept-hand fn2-dh-pool-obs 1 fn2-pool
  ((slot gen tkind tslot tgen fn2-pool) (not (equal tkind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-accept-own fn2-dh-pool-obs 1 fn2-pool
  ((slot gen okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))))
(fn2-dh-keeps fn2-pool-reset fn2-dh-pool-obs 1 fn2-pool
  ((slot gen okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-truncate fn2-dh-pool-obs 1 fn2-pool
  ((slot gen n okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in))
(fn2-dh-keeps fn2-pool-write fn2-dh-pool-obs 1 fn2-pool
  ((slot gen idx byte okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in)
  :use ((:instance fn2-dh-pool-obs-of-data-write (k fn2-dh-k) (pool fn2-pool) (r slot) (v byte)
                   (x (+ (fn2-pool-base slot fn2-pool) idx)))))
(fn2-dh-keeps fn2-pool-copy-range fn2-dh-pool-obs 1 fn2-pool
  ((src sgen soff dst dgen doff len okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))) :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in)
  :use ((:instance fn2-dh-pool-obs-of-copy-up (k fn2-dh-k) (pool fn2-pool) (r dst) (n len)
                   (src (+ (fn2-pool-base src fn2-pool) soff)) (dst (+ (fn2-pool-base dst fn2-pool) doff)))
        (:instance fn2-dh-pool-obs-of-copy-down (k fn2-dh-k) (pool fn2-pool) (r dst) (n len)
                   (src (+ (fn2-pool-base src fn2-pool) soff)) (dst (+ (fn2-pool-base dst fn2-pool) doff)))))
(fn2-dh-keeps fn2-pool-drop-prefix fn2-dh-pool-obs 2 fn2-pool
  ((slot gen k0 cursor limit okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k)))
  :enable (fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp fn2-pool-readable-code fn2-pool-range-in)
  :use ((:instance fn2-dh-pool-obs-of-copy-up (k fn2-dh-k) (pool fn2-pool) (r slot)
                   (n (if (< limit (- (- (fn2-pool-fill slot fn2-pool) k0) cursor)) limit
                        (- (- (fn2-pool-fill slot fn2-pool) k0) cursor)))
                   (src (+ (fn2-pool-base slot fn2-pool) k0 cursor)) (dst (+ (fn2-pool-base slot fn2-pool) cursor)))))
(fn2-dh-keeps fn2-core-lease fn2-dh-pool-obs 2 fn2-pool
  ((kind slot gen off len opslot opgen okind oslot ogen fn2-pool) (not (equal okind fn2-dh-k))))
(fn2-dh-keeps fn2-core-release-children fn2-dh-pool-obs 1 fn2-pool
  ((slot gen okind oslot ogen fn2-pool fn2-control) (not (equal okind fn2-dh-k))))
(fn2-dh-keeps fn2-op-reserve fn2-dh-ops-obs 3 fn2-ops
  ((kind okind oslot ogen principal may-release fn2-ops) (not (equal okind fn2-dh-k)))
  :enable (fn2-ops-clear-row fn2-op-slotp))
;; An issue reserves a free row as OKIND's, then fills and queues that row.
(fn2-dh-keeps fn2-issue-children fn2-dh-ops-obs 4 fn2-ops
  ((kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen
         okind oslot ogen principal fn2-pool fn2-ops fn2-control)
   (not (equal okind fn2-dh-k)))
  :enable (fn2-op-reserve fn2-op-unreserve fn2-op-set-range fn2-op-set-capability fn2-op-set-storage
           fn2-op-set-cancel-target fn2-op-enqueue fn2-op-phase-code fn2-op-handle-code fn2-ops-clear-row
           fn2-op-slotp))
(fn2-dh-keeps fn2-issue-children fn2-dh-pool-obs 3 fn2-pool
  ((kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen
         okind oslot ogen principal fn2-pool fn2-ops fn2-control)
   (not (equal okind fn2-dh-k))))

;; The chain's theory: this book's rules (the observation's functions off,
;; the held predicates on), the readers of the operation table and the pool,
;; and the core's read-over-write; a chain proof adds its function and the
;; core's child updaters' rules.
(in-theory (disable fn2-dh-ops-obs fn2-dh-pool-obs fn2-dh-op-rows fn2-dh-pool-rows fn2-dh-octets
                    fn2-dh-extents fn2-dh-ordered fn2-dh-row))
(defun fn2-dh-readers (names world)
  (declare (xargs :mode :program))
  (cond ((atom names) nil)
        ((or (not (function-symbolp (car names) world)) (fn2-dh-name-prefix-p "UPDATE-" (car names)) (fn2-dh-name-prefix-p "RESIZE-" (car names))
             (let ((n (symbol-name (car names)))) (equal (char n (1- (length n))) #\P)))
         (fn2-dh-readers (cdr names) world))
        (t (cons (car names) (fn2-dh-readers (cdr names) world)))))
(defun fn2-dh-column-readers (stobj cols)
  (declare (xargs :mode :program))
  (if (atom cols) nil (cons (fn2-columns-col-name stobj (car cols)) (fn2-dh-column-readers stobj (cdr cols)))))
(make-event
 (value `(deftheory fn2-dh-base
           (union-theories
            (set-difference-theories (current-theory :here) (current-theory 'fn2-dh-start))
            (union-theories
             '(mv-nth car-cons cdr-cons nth-update-nth len-update-nth
               ,@(fn2-dh-readers (caddr (getpropc 'fn2-ops 'stobj nil (w state))) (w state))
               ,@(fn2-dh-readers (caddr (getpropc 'fn2-pool 'stobj nil (w state))) (w state))
               ,@(fn2-dh-column-readers 'fn2-ops (strip-cars (fn2-view-layout 'fn2-ops (w state))))
               ,@(fn2-dh-column-readers 'fn2-pool (strip-cars (fn2-view-layout 'fn2-pool (w state)))))
             (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

;; ---------------------------------------------------------------------------
;; THE CHAIN (fn2-dh-chain-forms): for each function under a closure that
;; returns the operation table, the pool or the core, callees first, its
;; observation lemmas -- of the child it returns, or of the core's two
;; children -- each under the hypotheses its callees' lemmas need of its own
;; arguments (an owner kind is not K), recorded in fn2-dh-keeps. A core
;; function whose KIDS contract leaves both children has them from it; any
;; other opens its body once over its callees' lemmas (by its own induction
;; when it recurs). A function the chain cannot prove is refused by name.
(defun fn2-dh-facts (fn world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq fn (table-alist 'fn2-dh-keeps world))))
;; FN has its lemmas: the chain's or a primitive's (fn2-dh-keeps), a setter's
;; rewrite rules, or it is a stobj primitive (its updater's rules)
(defun fn2-dh-known (fn world)
  (declare (xargs :mode :program))
  (or (fn2-dh-facts fn world) (getpropc fn 'stobj-function nil world)
      (getpropc (fn2-columns-sym 'fn2-dh-ops-obs (concatenate 'string "-OF-" (symbol-name fn))) 'theorem nil world)
      (getpropc (fn2-columns-sym 'fn2-dh-pool-obs (concatenate 'string "-OF-" (symbol-name fn))) 'theorem nil world)))
(defun fn2-dh-outs (fn world)
  ; (obs position stobj) of each lemma FN owes
  (declare (xargs :mode :program))
  (let* ((outs (getpropc fn 'stobjs-out nil world)) (ins (getpropc fn 'stobjs-in nil world)))
    (append (and (member-eq 'fn2-ops outs) (member-eq 'fn2-ops ins)
                 (list (list 'fn2-dh-ops-obs (if (equal (len outs) 1) nil (position-eq 'fn2-ops outs)) 'fn2-ops)))
            (and (member-eq 'fn2-pool outs) (member-eq 'fn2-pool ins)
                 (list (list 'fn2-dh-pool-obs (if (equal (len outs) 1) nil (position-eq 'fn2-pool outs)) 'fn2-pool)))
            (and (member-eq 'fn2-core outs) (member-eq 'fn2-core ins)
                 (let ((p (if (equal (len outs) 1) nil (position-eq 'fn2-core outs))))
                   (list (list 'fn2-dh-ops-obs p 'fn2-core) (list 'fn2-dh-pool-obs p 'fn2-core)))))))
(defun fn2-dh-sel (obs stobj x)
  (declare (xargs :mode :program))
  (cond ((not (eq stobj 'fn2-core)) x)
        ((eq obs 'fn2-dh-ops-obs) `(fn2-core-ops ,x))
        (t `(fn2-core-pool ,x))))
(defun fn2-dh-out (pos call) (declare (xargs :mode :program)) (if pos `(mv-nth ,pos ,call) call))
;; the hypotheses FACTS (of G with FORMALS) need of ACTUALS
;; each hypothesis with the path of callees it comes from, down to the primitive
(defun fn2-dh-add-hyps (hyps g alist acc)
  (declare (xargs :mode :program))
  (if (atom hyps) acc
    (let ((h (sublis-var alist (caar hyps))))
      (fn2-dh-add-hyps (cdr hyps) g alist
                       (if (assoc-equal h acc) acc (cons (cons h (cons g (cdar hyps))) acc))))))
(defun fn2-dh-inst-hyps (facts g formals actuals acc)
  (declare (xargs :mode :program))
  (if (atom facts) acc
    (fn2-dh-inst-hyps (cdr facts) g formals actuals
                      (fn2-dh-add-hyps (nth 3 (car facts)) g (pairlis$ formals actuals) acc))))
(mutual-recursion
 (defun fn2-dh-walk (x alist fn world acc)
   (declare (xargs :mode :program))
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         ((consp (car x))
          (let ((acc (fn2-dh-walk-list (cdr x) alist fn world acc)))
            (fn2-dh-walk (caddr (car x)) (pairlis$ (cadr (car x)) (sublis-var-lst alist (cdr x))) fn world acc)))
         (t (let ((acc (fn2-dh-walk-list (cdr x) alist fn world acc)))
              (if (eq (car x) fn) acc
                (let ((facts (fn2-dh-facts (car x) world)))
                  (if facts (fn2-dh-inst-hyps facts (car x) (formals (car x) world) (sublis-var-lst alist (cdr x)) acc) acc)))))))
 (defun fn2-dh-walk-list (xs alist fn world acc)
   (declare (xargs :mode :program))
   (if (atom xs) acc (fn2-dh-walk-list (cdr xs) alist fn world (fn2-dh-walk (car xs) alist fn world acc)))))
(defun fn2-dh-name (obs fn) (declare (xargs :mode :program)) (fn2-columns-sym obs (concatenate 'string "-OF-" (symbol-name fn))))
(defun fn2-dh-writes-p (fns world)
  ; some callee writes the operation table, the pool or the core
  (declare (xargs :mode :program))
  (and (consp fns) (or (fn2-dh-outs (car fns) world) (fn2-dh-writes-p (cdr fns) world))))
;; The callees of FN (its body's functions with lemmas owed), callees first.
(defun fn2-dh-postorder (fns world seen fuel)
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) seen)
        ((or (member-eq (car fns) seen) (not (fn2-dh-outs (car fns) world)) (fn2-dh-known (car fns) world))
         (fn2-dh-postorder (cdr fns) world seen fuel))
        (t (fn2-dh-postorder (cdr fns) world
             (append (fn2-dh-postorder (remove-eq (car fns) (all-fnnames (getpropc (car fns) 'unnormalized-body nil world)))
                                       world seen (1- fuel))
                     (list (car fns)))
             fuel))))
(defun fn2-dh-postorder-new (fns world)
  (declare (xargs :mode :program))
  (remove-duplicates-eq (reverse (remove-duplicates-eq (reverse (fn2-dh-postorder fns world nil 64))))))
(defun fn2-dh-kids-uses (fn kind world)
  ; a KIDS contract of FN leaving both children: the hint instances
  (declare (xargs :mode :program))
  (let ((d (fn2-dc-entry fn kind world))
        (ks (fn2-arm-frame-indices '(fn2-core-ops fn2-core-pool) world))
        (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
    (and d (not (intersectp-equal ks (car d)))
         `((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 fn2-core))
           (:instance fn2-arm-kids-refl (i 0) (free ',(car d)) (a fn2-core))
           (:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',(car d)) (a fn2-core) (b ,out))
           (:instance fn2-arm-kids-nth (i 0) (k ,(cadr ks)) (free ',(car d)) (a fn2-core) (b ,out))))))
(defun fn2-dh-lemmas (outs fn call hyps hints)
  (declare (xargs :mode :program))
  (if (atom outs) nil
    (let* ((obs (car (car outs))) (pos (cadr (car outs))) (stobj (caddr (car outs))))
      (cons `(defthm ,(fn2-dh-name obs fn)
               (implies (and ,@hyps)
                        (equal (,obs fn2-dh-k ,(fn2-dh-sel obs stobj (fn2-dh-out pos call))) (,obs fn2-dh-k ,(fn2-dh-sel obs stobj stobj))))
               :hints ,hints)
            (fn2-dh-lemmas (cdr outs) fn call hyps hints)))))
(defun fn2-dh-facts-of (outs hyps)
  (declare (xargs :mode :program))
  (if (atom outs) nil (cons (append (car outs) (list hyps)) (fn2-dh-facts-of (cdr outs) hyps))))
(defun fn2-dh-core-runes (children)
  ; the ops' and the pool's reads through every core child's update
  (declare (xargs :mode :program))
  (if (atom children) nil
    (let ((update (fn2-columns-pre "UPDATE-" (caar children))))
      (list* (fn2-columns-sym 'fn2-core-ops (concatenate 'string "-OF-" (symbol-name update)))
             (fn2-columns-sym 'fn2-core-pool (concatenate 'string "-OF-" (symbol-name update)))
             (fn2-dh-core-runes (cdr children))))))
(defun fn2-dh-fact-names (facts fn)
  (declare (xargs :mode :program))
  (if (atom facts) nil (cons (fn2-dh-name (car (car facts)) fn) (fn2-dh-fact-names (cdr facts) fn))))
(defun fn2-dh-callee-runes (gs world)
  ; the lemmas of FN's callees (their names are a fact's observation and the callee)
  (declare (xargs :mode :program))
  (if (atom gs) nil
    (append (fn2-dh-fact-names (fn2-dh-facts (car gs) world) (car gs))
            (fn2-dh-callee-runes (cdr gs) world))))
(defun fn2-dh-chain-event (fn kind world)
  (declare (xargs :mode :program))
  (let* ((outs (fn2-dh-outs fn world))
         (formals (formals fn world))
         (call (cons fn formals))
         (body (getpropc fn 'unnormalized-body nil world))
         (kids (and (member-eq 'fn2-core (getpropc fn 'stobjs-out nil world)) (fn2-dh-kids-uses fn kind world)))
         (hyps (if kids nil (reverse (fn2-dh-walk body nil fn world nil))))
         (recp (getpropc fn 'recursivep nil world)))
    (cond
     ((or (null outs) (fn2-dh-known fn world)) '(value-triple :known))
     ((and (null body) (null kids))
      `(make-event (er soft 'fn2-dispatch-held "~x0 is constrained without a held-frame contract." ',fn)))
     ((and recp (not (equal recp (list fn))))
      `(make-event (er soft 'fn2-dispatch-held "~x0 is mutually recursive (~x1): no held-frame chain." ',fn ',recp)))
     (t
      `(progn
         ,@(fn2-dh-lemmas outs fn call (strip-cars hyps)
                          (if kids
                              `(("Goal" :in-theory (union-theories '(fn2-core-ops fn2-core-pool) (theory 'fn2-arm-frame-base))
                                 :use ,kids))
                            `(("Goal" :in-theory (union-theories
                                                  '(,fn ,@(fn2-dh-callee-runes (remove-eq fn (all-fnnames body)) world)
                                                        ,@(and (member-eq 'fn2-core (getpropc fn 'stobjs-in nil world))
                                                               (let ((cs (unquote (getpropc '*fn2-core-children* 'const nil world))))
                                                                 (fn2-dh-core-runes cs))))
                                                  (theory 'fn2-dh-base))
                                      ,@(and recp `(:induct ,call))))))
         (table fn2-dh-keeps ',fn ',(fn2-dh-facts-of outs hyps)))))))
(defun fn2-dh-chain-forms (fns kind)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (fn2-dh-chain-event ',(car fns) ',kind (w state))))
          (fn2-dh-chain-forms (cdr fns) kind))))

;; THE CLAIM of a dispatch's attachment FN (its core result at POS, in the
;; held view at the commit kind, assembly-dispatch fn2-dispatch-held): every
;; hypothesis of FN's chain at K the commit kind must be an owner kind that
;; is a constant other than K; else refused, naming each hypothesis with the
;; callees it comes from, down to the primitive.
(defun fn2-dh-hyp-ok (h kv)
  (declare (xargs :mode :program))
  (and (consp h) (eq (car h) 'not) (consp (cadr h)) (eq (car (cadr h)) 'equal)
       (let ((a (cadr (cadr h))) (b (caddr (cadr h))))
         (or (and (eq b 'fn2-dh-k) (quotep a) (not (equal (unquote a) kv)))
             (and (eq a 'fn2-dh-k) (quotep b) (not (equal (unquote b) kv)))))))
(defun fn2-dh-bad-hyps (hyps kv)
  (declare (xargs :mode :program))
  (cond ((atom hyps) nil)
        ((fn2-dh-hyp-ok (caar hyps) kv) (fn2-dh-bad-hyps (cdr hyps) kv))
        (t (cons (car hyps) (fn2-dh-bad-hyps (cdr hyps) kv)))))
(defun fn2-dh-all-hyps (facts)
  (declare (xargs :mode :program))
  (if (atom facts) nil (union-equal (nth 3 (car facts)) (fn2-dh-all-hyps (cdr facts)))))
(defun fn2-dh-claim-form (who fn pos world)
  (declare (xargs :mode :program))
  (let* ((facts (fn2-dh-facts fn world))
         (kv (unquote (getpropc '*fn2-commit-kind* 'const nil world)))
         (bad (fn2-dh-bad-hyps (fn2-dh-all-hyps facts) kv))
         (out `(mv-nth ,pos (,fn ,@(formals fn world)))))
    (cond ((null facts)
           `(make-event (er soft 'fn2-dispatch-held "The attachment ~x0 of ~x1 has no held-frame chain." ',fn ',who)))
          (bad
           `(make-event (er soft 'fn2-dispatch-held
                            "The attachment ~x0 of ~x1 may write rows the commit kind ~x2 holds: its chain needs ~x3 (each with the callees it comes from)."
                            ',fn ',who ',kv ',bad)))
          (t `(defthm ,(fn2-columns-sym fn "-DISPATCH-HELD")
                (fn2-dispatch-held ,out fn2-core)
                :hints (("Goal" :in-theory (union-theories '(fn2-dispatch-held fn2-dispatch-held-obs fn2-dh-obs (:e equal) (:e not)
                                                             ,@(fn2-dh-fact-names facts fn))
                                                           (theory 'minimal-theory)))))))))
