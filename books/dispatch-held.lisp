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
