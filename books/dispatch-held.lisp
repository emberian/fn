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

;; ---------------------------------------------------------------------------
;; STORED OWNERS. Some tables keep, per row, the owner kind its writes go out
;; as (the cursor's conn-kind, an overlay's okind). FN2-DH-COL-OK K C X: no
;; row of column C of X holds K (and K is not nil, the value of a row past
;; the end). A write of such a read is then K's only when the column is.
(defun fn2-dh-avoids (k l)
  (declare (xargs :guard t))
  (if (atom l) (if k t nil) (and (not (equal (car l) k)) (fn2-dh-avoids k (cdr l)))))
(defthm fn2-dh-avoids-nth
  (implies (fn2-dh-avoids k l) (not (equal (nth i l) k))))
(defthm fn2-dh-avoids-update-nth
  (implies (and (fn2-dh-avoids k l) (not (equal v k))) (fn2-dh-avoids k (update-nth i v l))))
(defthm fn2-dh-avoids-resize-list
  (implies (and (fn2-dh-avoids k l) (not (equal d k))) (fn2-dh-avoids k (resize-list l n d))))
(defthm fn2-dh-resize-list-0 (equal (resize-list l 0 d) nil))
(defun-nx fn2-dh-col-ok (k c x) (fn2-dh-avoids k (nth c x)))
(defthm fn2-dh-col-ok-of-update-nth
  (equal (fn2-dh-col-ok k c (update-nth j v x))
         (if (equal (nfix j) (nfix c)) (fn2-dh-avoids k v) (fn2-dh-col-ok k c x)))
  :hints (("Goal" :in-theory (disable fn2-dh-avoids))))
(defthm fn2-dh-col-ok-avoids
  (implies (fn2-dh-col-ok k c x) (fn2-dh-avoids k (nth c x))))
(defthm fn2-dh-col-ok-nth
  (implies (fn2-dh-col-ok k c x) (not (equal (nth i (nth c x)) k)))
  :hints (("Goal" :in-theory '(fn2-dh-col-ok) :use ((:instance fn2-dh-avoids-nth (l (nth c x)))))))
(in-theory (disable fn2-dh-col-ok fn2-dh-avoids))

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
;; returns the operation table, the pool, an owner table (below) or the core,
;; callees first, ONE lemma: the observations of the children it returns (of
;; the core's two) kept, under the hypotheses its callees' lemmas need of its
;; own arguments (an owner kind is not K); and the stored owners of every
;; owner table it returns (at the core, FN2-DH-OWNERS-OK) still avoiding K,
;; under its callees' owner hypotheses alone. Recorded in fn2-dh-keeps. An
;; owner kind read from a row of an owner table is asked of the function's
;; own table (or core): its stored owners avoid K (FN2-DH-COL-OK, or
;; FN2-DH-OWNERS-OK). A core function whose KIDS contract leaves every
;; observed child has its lemma from it; any other opens its body once over
;; its callees' lemmas (by its own induction when it recurs). A function the
;; chain cannot prove is refused by name.
;;
;; THE OWNER TABLES (table fn2-dh-owners, machines.lisp's held view form):
;; stobj -> (C READERS ACC FNS): the owner column's index, its readers, the
;; core's accessor of the table, and the table's writers the chain opens
;; (its raw updaters and column setters).
(defun fn2-dh-owners (world) (declare (xargs :mode :program)) (table-alist 'fn2-dh-owners world))
(defun fn2-dh-owner-obs-p (obs) (declare (xargs :mode :program)) (member-eq obs '(fn2-dh-col-ok fn2-dh-owners-ok)))
(defun fn2-dh-owner-fn-p (fn owners)
  (declare (xargs :mode :program))
  (and (consp owners) (or (member-eq fn (nth 4 (car owners))) (fn2-dh-owner-fn-p fn (cdr owners)))))
(defun fn2-dh-owner-accs (owners)
  (declare (xargs :mode :program))
  (if (atom owners) nil (cons (nth 3 (car owners)) (fn2-dh-owner-accs (cdr owners)))))
(defun fn2-dh-owner-theory (owners)
  ; the writers the chain opens and the owner columns' readers
  (declare (xargs :mode :program))
  (if (atom owners) nil (append (nth 2 (car owners)) (nth 4 (car owners)) (fn2-dh-owner-theory (cdr owners)))))
(defun fn2-dh-owner-comps (owners x)
  ; the stored owners of core X avoid K
  (declare (xargs :mode :program))
  (if (atom owners) nil
    (cons `(fn2-dh-col-ok fn2-dh-k ',(nth 1 (car owners)) (,(nth 3 (car owners)) ,x))
          (fn2-dh-owner-comps (cdr owners) x))))
(defun fn2-dh-owner-comps-at (owners x acc v)
  ; the comps of core X with the table at ACC replaced by V
  (declare (xargs :mode :program))
  (if (atom owners) nil
    (cons `(fn2-dh-col-ok fn2-dh-k ',(nth 1 (car owners))
                          ,(if (eq (nth 3 (car owners)) acc) v `(,(nth 3 (car owners)) ,x)))
          (fn2-dh-owner-comps-at (cdr owners) x acc v))))
(defun fn2-dh-owner-of-col (c owners)
  (declare (xargs :mode :program))
  (cond ((atom owners) nil) ((equal (nth 1 (car owners)) c) (caar owners)) (t (fn2-dh-owner-of-col c (cdr owners)))))
(defun fn2-dh-owner-of-reader (r owners)
  (declare (xargs :mode :program))
  (cond ((atom owners) nil) ((member-eq r (nth 2 (car owners))) (caar owners)) (t (fn2-dh-owner-of-reader r (cdr owners)))))

(defun fn2-dh-facts (fn world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq fn (table-alist 'fn2-dh-keeps world))))
;; FN has its lemmas: a primitive's (fn2-dh-keeps), a setter's rewrite rules,
;; a stobj primitive (its updater's rules), an owner table's writer the chain
;; opens, or the chain's, covering every conclusion it owes in MODE
(defun fn2-dh-covers (o facts)
  (declare (xargs :mode :program))
  (and (consp facts) (or (and (eq (car o) (car (car facts))) (eq (caddr o) (caddr (car facts))))
                         (fn2-dh-covers o (cdr facts)))))
(defun fn2-dh-covered (outs facts)
  (declare (xargs :mode :program))
  (or (atom outs)
      (and (fn2-dh-covers (car outs) facts) (fn2-dh-covered (cdr outs) facts))))
(defun fn2-dh-prim-known (fn world)
  (declare (xargs :mode :program))
  (or (getpropc fn 'stobj-function nil world)
      (fn2-dh-owner-fn-p fn (fn2-dh-owners world))
      (let ((facts (fn2-dh-facts fn world))) (and facts (not (nth 4 (car facts)))))
      (getpropc (fn2-columns-sym 'fn2-dh-ops-obs (concatenate 'string "-OF-" (symbol-name fn))) 'theorem nil world)
      (getpropc (fn2-columns-sym 'fn2-dh-pool-obs (concatenate 'string "-OF-" (symbol-name fn))) 'theorem nil world)))
(defun fn2-dh-pos (s outs) (declare (xargs :mode :program)) (if (equal (len outs) 1) nil (position-eq s outs)))
(defun fn2-dh-owner-outs (owners outs ins)
  (declare (xargs :mode :program))
  (cond ((atom owners) nil)
        ((and (member-eq (caar owners) outs) (member-eq (caar owners) ins))
         (cons (list 'fn2-dh-col-ok (fn2-dh-pos (caar owners) outs) (caar owners)) (fn2-dh-owner-outs (cdr owners) outs ins)))
        (t (fn2-dh-owner-outs (cdr owners) outs ins))))
(defun fn2-dh-outs-m (fn mode world)
  ; (obs position stobj) of each conclusion FN owes; MODE :owners, the owner ones alone
  (declare (xargs :mode :program))
  (let* ((outs (getpropc fn 'stobjs-out nil world)) (ins (getpropc fn 'stobjs-in nil world))
         (owners (fn2-dh-owners world)))
    (append (and (not mode) (member-eq 'fn2-ops outs) (member-eq 'fn2-ops ins)
                 (list (list 'fn2-dh-ops-obs (fn2-dh-pos 'fn2-ops outs) 'fn2-ops)))
            (and (not mode) (member-eq 'fn2-pool outs) (member-eq 'fn2-pool ins)
                 (list (list 'fn2-dh-pool-obs (fn2-dh-pos 'fn2-pool outs) 'fn2-pool)))
            (fn2-dh-owner-outs owners outs ins)
            (and (member-eq 'fn2-core outs) (member-eq 'fn2-core ins)
                 (let ((p (fn2-dh-pos 'fn2-core outs)))
                   (append (and (not mode) (list (list 'fn2-dh-ops-obs p 'fn2-core) (list 'fn2-dh-pool-obs p 'fn2-core)))
                           (and owners (list (list 'fn2-dh-owners-ok p 'fn2-core)))))))))
(defun fn2-dh-outs (fn world) (declare (xargs :mode :program)) (fn2-dh-outs-m fn nil world))
(defun fn2-dh-known-m (fn mode world)
  (declare (xargs :mode :program))
  (or (fn2-dh-prim-known fn world) (fn2-dh-covered (fn2-dh-outs-m fn mode world) (fn2-dh-facts fn world))))
(defun fn2-dh-known (fn world) (declare (xargs :mode :program)) (fn2-dh-known-m fn nil world))
(defun fn2-dh-sel (obs stobj x)
  (declare (xargs :mode :program))
  (cond ((not (eq stobj 'fn2-core)) x)
        ((eq obs 'fn2-dh-ops-obs) `(fn2-core-ops ,x))
        (t `(fn2-core-pool ,x))))
(defun fn2-dh-out (pos call) (declare (xargs :mode :program)) (if pos `(mv-nth ,pos ,call) call))
;; An owner kind asked of a stored owner (a reader of an owner table at X),
;; of an owner table's stored owners or of the core's, is asked of FORMALS'
;; table of that stobj, else of the core: H's root form there, else H.
(defun fn2-dh-root-hyp (h formals owners)
  (declare (xargs :mode :program))
  (let* ((s (and (consp h)
                 (cond ((and (eq (car h) 'not) (consp (cadr h)) (eq (car (cadr h)) 'equal))
                        (let* ((a (cadr (cadr h))) (b (caddr (cadr h)))
                               (r (cond ((eq b 'fn2-dh-k) a) ((eq a 'fn2-dh-k) b))))
                          (and (consp r) (symbolp (car r)) (fn2-dh-owner-of-reader (car r) owners))))
                       ((and (eq (car h) 'fn2-dh-col-ok) (eq (cadr h) 'fn2-dh-k) (quotep (caddr h)))
                        (fn2-dh-owner-of-col (unquote (caddr h)) owners))
                       ((and (eq (car h) 'fn2-dh-owners-ok) (eq (cadr h) 'fn2-dh-k)) :core)))))
    (cond ((null s) h)
          ((and (not (eq s :core)) (member-eq s formals))
           `(fn2-dh-col-ok fn2-dh-k ',(nth 1 (assoc-eq s owners)) ,s))
          ((member-eq 'fn2-core formals) '(fn2-dh-owners-ok fn2-dh-k fn2-core))
          (t h))))
;; the hypotheses FACTS (of G with FORMALS) need of ACTUALS, in the caller's
;; root form; each with the path of callees it comes from, down to the primitive
(defun fn2-dh-add-hyps (hyps g alist cformals owners acc)
  (declare (xargs :mode :program))
  (if (atom hyps) acc
    (let ((h (fn2-dh-root-hyp (sublis-var alist (caar hyps)) cformals owners)))
      (fn2-dh-add-hyps (cdr hyps) g alist cformals owners
                       (if (assoc-equal h acc) acc (cons (cons h (cons g (cdar hyps))) acc))))))
;; OWNERP: only the facts of the owner conclusions; :HELD, of the others
(defun fn2-dh-inst-hyps (facts g formals actuals cformals owners ownerp acc)
  (declare (xargs :mode :program))
  (if (atom facts) acc
    (fn2-dh-inst-hyps (cdr facts) g formals actuals cformals owners ownerp
                      (if (cond ((eq ownerp :held) (not (fn2-dh-owner-obs-p (car (car facts)))))
                                (ownerp (fn2-dh-owner-obs-p (car (car facts))))
                                (t t))
                          (fn2-dh-add-hyps (nth 3 (car facts)) g (pairlis$ formals actuals) cformals owners acc)
                        acc))))
(mutual-recursion
 (defun fn2-dh-walk (x alist fn ownerp world acc)
   (declare (xargs :mode :program))
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         ((consp (car x))
          (let ((acc (fn2-dh-walk-list (cdr x) alist fn ownerp world acc)))
            (fn2-dh-walk (caddr (car x)) (pairlis$ (cadr (car x)) (sublis-var-lst alist (cdr x))) fn ownerp world acc)))
         (t (let ((acc (fn2-dh-walk-list (cdr x) alist fn ownerp world acc)))
              (if (eq (car x) fn) acc
                (let ((facts (fn2-dh-facts (car x) world)))
                  (if facts
                      (fn2-dh-inst-hyps facts (car x) (formals (car x) world) (sublis-var-lst alist (cdr x))
                                        (formals fn world) (fn2-dh-owners world) ownerp acc)
                    acc)))))))
 (defun fn2-dh-walk-list (xs alist fn ownerp world acc)
   (declare (xargs :mode :program))
   (if (atom xs) acc (fn2-dh-walk-list (cdr xs) alist fn ownerp world (fn2-dh-walk (car xs) alist fn ownerp world acc)))))
(defun fn2-dh-name (fn) (declare (xargs :mode :program)) (fn2-columns-pre "FN2-DH-OF-" fn))
(defun fn2-dh-name-m (fn mode) (declare (xargs :mode :program)) (if mode (fn2-columns-pre "FN2-DH-OWNERS-OF-" fn) (fn2-dh-name fn)))
(defun fn2-dh-writes-p (fns world)
  ; some callee writes the operation table, the pool, an owner table or the core
  (declare (xargs :mode :program))
  (and (consp fns) (or (fn2-dh-outs (car fns) world) (fn2-dh-writes-p (cdr fns) world))))
;; The callees of FN (its body's functions with lemmas owed in MODE), callees first.
(defun fn2-dh-postorder (fns mode world seen fuel)
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) seen)
        ((or (member-eq (car fns) seen) (not (fn2-dh-outs-m (car fns) mode world)) (fn2-dh-known-m (car fns) mode world))
         (fn2-dh-postorder (cdr fns) mode world seen fuel))
        (t (fn2-dh-postorder (cdr fns) mode world
             (append (fn2-dh-postorder (remove-eq (car fns) (all-fnnames (getpropc (car fns) 'unnormalized-body nil world)))
                                       mode world seen (1- fuel))
                     (list (car fns)))
             fuel))))
(defun fn2-dh-postorder-m (fns mode world)
  (declare (xargs :mode :program))
  (remove-duplicates-eq (reverse (remove-duplicates-eq (reverse (fn2-dh-postorder fns mode world nil 64))))))
(defun fn2-dh-postorder-new (fns world) (declare (xargs :mode :program)) (fn2-dh-postorder-m fns nil world))
(defun fn2-dh-kids-nths (ks d out)
  (declare (xargs :mode :program))
  (if (atom ks) nil
    (cons `(:instance fn2-arm-kids-nth (i 0) (k ,(car ks)) (free ',(car d)) (a fn2-core) (b ,out))
          (fn2-dh-kids-nths (cdr ks) d out))))
(defun fn2-dh-kids-uses (fn kind mode world)
  ; a KIDS contract of FN leaving every observed child (in MODE): the hint instances
  (declare (xargs :mode :program))
  (let ((d (fn2-dc-entry fn kind world))
        (ks (fn2-arm-frame-indices (append (and (not mode) '(fn2-core-ops fn2-core-pool)) (fn2-dh-owner-accs (fn2-dh-owners world))) world))
        (out (fn2-arm-frame-out-term fn (cons fn (formals fn world)) world)))
    (and d (not (intersectp-equal ks (car d)))
         `((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 fn2-core))
           (:instance fn2-arm-kids-refl (i 0) (free ',(car d)) (a fn2-core))
           ,@(fn2-dh-kids-nths ks d out)))))
(defun fn2-dh-concl (o call world)
  (declare (xargs :mode :program))
  (let* ((obs (car o)) (stobj (caddr o)) (out (fn2-dh-out (cadr o) call)))
    (cond ((eq obs 'fn2-dh-col-ok)
           (let ((c (nth 1 (assoc-eq stobj (fn2-dh-owners world)))))
             `(implies (fn2-dh-col-ok fn2-dh-k ',c ,stobj) (fn2-dh-col-ok fn2-dh-k ',c ,out))))
          ((eq obs 'fn2-dh-owners-ok)
           `(implies (fn2-dh-owners-ok fn2-dh-k fn2-core) (fn2-dh-owners-ok fn2-dh-k ,out)))
          (t `(equal (,obs fn2-dh-k ,(fn2-dh-sel obs stobj out)) (,obs fn2-dh-k ,(fn2-dh-sel obs stobj stobj)))))))
(defun fn2-dh-concls (outs ownerp call world)
  (declare (xargs :mode :program))
  (cond ((atom outs) nil)
        ((iff ownerp (fn2-dh-owner-obs-p (car (car outs))))
         (cons (fn2-dh-concl (car outs) call world) (fn2-dh-concls (cdr outs) ownerp call world)))
        (t (fn2-dh-concls (cdr outs) ownerp call world))))
(defun fn2-dh-lemma (name outs call hyps ohyps hints world)
  ; one lemma: the observations under HYPS, the stored owners under OHYPS
  (declare (xargs :mode :program))
  (let ((held (fn2-dh-concls outs nil call world)) (owned (fn2-dh-concls outs t call world)))
    `(defthm ,name
       (and ,@(and held `((implies (and ,@hyps) (and ,@held))))
            ,@(and owned `((implies (and ,@ohyps) (and ,@owned)))))
       :hints ,hints)))
(defun fn2-dh-facts-of (outs hyps ohyps name)
  (declare (xargs :mode :program))
  (if (atom outs) nil
    (cons (append (car outs) (list (if (fn2-dh-owner-obs-p (car (car outs))) ohyps hyps) name))
          (fn2-dh-facts-of (cdr outs) hyps ohyps name))))
(defun fn2-dh-core-reads (accs update)
  (declare (xargs :mode :program))
  (if (atom accs) nil
    (cons (fn2-columns-sym (car accs) (concatenate 'string "-OF-" (symbol-name update)))
          (fn2-dh-core-reads (cdr accs) update))))
(defun fn2-dh-core-runes (children accs)
  ; the reads of the ops, the pool and the owner tables through every core child's update
  (declare (xargs :mode :program))
  (if (atom children) nil
    (let ((update (fn2-columns-pre "UPDATE-" (caar children))))
      (append (fn2-dh-core-reads (list* 'fn2-core-ops 'fn2-core-pool accs) update)
              (fn2-dh-core-runes (cdr children) accs)))))
(defun fn2-dh-fact-names (facts fn world)
  ; the lemma of each fact (a primitive's per observation, the chain's one)
  (declare (xargs :mode :program))
  (if (atom facts) nil
    (let ((name (or (nth 4 (car facts)) (fn2-dh-keeps-name (car (car facts)) fn))))
      (if (getpropc name 'theorem nil world)
          (add-to-set-eq name (fn2-dh-fact-names (cdr facts) fn world))
        (fn2-dh-fact-names (cdr facts) fn world)))))
(defun fn2-dh-callee-runes (gs world)
  ; the lemmas of FN's callees
  (declare (xargs :mode :program))
  (if (atom gs) nil
    (union-eq (fn2-dh-fact-names (fn2-dh-facts (car gs) world) (car gs) world)
              (fn2-dh-callee-runes (cdr gs) world))))
(defun fn2-dh-chain-hints (fn call body kids recp checked touches owners world)
  (declare (xargs :mode :program))
  (cond (kids
         `(("Goal" :in-theory (union-theories '(fn2-core-ops fn2-core-pool
                                                ,@(and owners (cons 'fn2-dh-owners-ok (fn2-dh-owner-accs owners))))
                                              (theory 'fn2-arm-frame-base))
            :use ,kids)))
        (checked
         ;; as a primitive's (fn2-dh-keeps): the current theory
         `(("Goal" :in-theory (e/d (,fn ,@*fn2-dh-pool-codes* ,@(fn2-dh-callee-runes (remove-eq fn (all-fnnames body)) world))
                                   (fn2-dh-ops-obs fn2-dh-pool-obs nth update-nth))
            ,@(and recp `(:induct ,call)))))
        (t
         `(("Goal" :in-theory (union-theories
                               '(,fn ,@(fn2-dh-callee-runes (remove-eq fn (all-fnnames body)) world)
                                     ,@(and touches (list* 'update-nth-array (fn2-dh-owner-theory owners)))
                                     ,@(and (member-eq 'fn2-core (getpropc fn 'stobjs-in nil world))
                                            (let ((cs (unquote (getpropc '*fn2-core-children* 'const nil world))))
                                              (fn2-dh-core-runes cs (fn2-dh-owner-accs owners)))))
                               ,(if touches
                                    '(union-theories (theory 'fn2-dh-owners-rules) (theory 'fn2-dh-base))
                                  '(theory 'fn2-dh-base)))
            ,@(and recp `(:induct ,call)))))))
(defun fn2-dh-owner-state-hyp-p (h owners)
  ; H asks of stored owners: an owner table's or the core's, or a stored owner read
  (declare (xargs :mode :program))
  (and (consp h)
       (or (fn2-dh-owner-obs-p (car h))
           (and (eq (car h) 'not) (consp (cadr h)) (eq (car (cadr h)) 'equal)
                (let ((a (cadr (cadr h))) (b (caddr (cadr h))))
                  (or (and (consp a) (symbolp (car a)) (fn2-dh-owner-of-reader (car a) owners))
                      (and (consp b) (symbolp (car b)) (fn2-dh-owner-of-reader (car b) owners))))))))
(defun fn2-dh-owner-state-hyps-p (hyps owners)
  (declare (xargs :mode :program))
  (and (consp hyps) (or (fn2-dh-owner-state-hyp-p (caar hyps) owners)
                        (fn2-dh-owner-state-hyps-p (cdr hyps) owners))))
(defun fn2-dh-union-hyps (a b)
  (declare (xargs :mode :program))
  (cond ((atom b) a)
        ((assoc-equal (caar b) a) (fn2-dh-union-hyps a (cdr b)))
        (t (fn2-dh-union-hyps (append a (list (car b))) (cdr b)))))
(mutual-recursion
 (defun fn2-dh-eq-binds (x formals acc)
   ; (V . TERM) for each (EQUAL TERM V) or (EQUAL V TERM) of X with V a formal
   ; and TERM a non-constant term without V
   (declare (xargs :mode :program))
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         (t (let ((acc (fn2-dh-eq-binds-list (cdr x) formals acc)))
              (if (and (eq (car x) 'equal) (consp (cdr x)) (consp (cddr x)))
                  (let ((a (cadr x)) (b (caddr x)))
                    (cond ((and (member-eq b formals) (consp a) (not (quotep a)) (not (member-eq b (all-vars a))))
                           (add-to-set-equal (cons b a) acc))
                          ((and (member-eq a formals) (consp b) (not (quotep b)) (not (member-eq a (all-vars b))))
                           (add-to-set-equal (cons a b) acc))
                          (t acc)))
                acc)))))
 (defun fn2-dh-eq-binds-list (xs formals acc)
   (declare (xargs :mode :program))
   (if (atom xs) acc (fn2-dh-eq-binds-list (cdr xs) formals (fn2-dh-eq-binds (car xs) formals acc)))))
(defun fn2-dh-eq-calls (binds call)
  (declare (xargs :mode :program))
  (if (atom binds) nil
    (cons (cons (car call) (sublis-var-lst (list (car binds)) (cdr call)))
          (fn2-dh-eq-calls (cdr binds) call))))
;; The call expanded, and as the induction step meets it once an equality of
;; the body has replaced a formal by the term it is compared with.
(defun fn2-dh-hints-expand (hints call body)
  (declare (xargs :mode :program))
  (cons (append (car hints)
                (list :expand (cons call (fn2-dh-eq-calls (fn2-dh-eq-binds body (cdr call) nil) call))))
        (cdr hints)))
(defun fn2-dh-chain-event (fn kind mode world)
  (declare (xargs :mode :program))
  (let* ((outs (fn2-dh-outs-m fn mode world))
         (name (fn2-dh-name-m fn mode))
         (formals (formals fn world))
         (call (cons fn formals))
         (body (getpropc fn 'unnormalized-body nil world))
         (owners (fn2-dh-owners world))
         (kids (and (member-eq 'fn2-core (getpropc fn 'stobjs-out nil world)) (fn2-dh-kids-uses fn kind mode world)))
         (ohyps (if kids nil (reverse (fn2-dh-walk body nil fn t world nil))))
         ;; the held conclusions need the callees' held facts, and their
         ;; owner facts only when a held hypothesis asks of stored owners
         (hyps0 (if (or kids mode) nil (reverse (fn2-dh-walk body nil fn :held world nil))))
         (hyps (if (fn2-dh-owner-state-hyps-p hyps0 owners) (fn2-dh-union-hyps hyps0 ohyps) hyps0))
         ;; a pool writer checking a row's owner (a code of *fn2-dh-pool-codes*)
         ;; against its own OKIND, when its callees' lemmas do not prove it:
         ;; it writes as OKIND
         (checkp (and (not kids) (not mode) (member-eq 'okind formals) (intersectp-eq *fn2-dh-pool-codes* (all-fnnames body))))
         (chyps (append hyps (list (list '(not (equal okind fn2-dh-k)) fn :owner-check))))
         (touches (and owners (intersectp-eq (getpropc fn 'stobjs-in nil world) (cons 'fn2-core (strip-cars owners)))))
         (recp (getpropc fn 'recursivep nil world))
         (old (fn2-dh-facts fn world)))
    (cond
     ((or (null outs) (fn2-dh-known-m fn mode world)) '(value-triple :known))
     ((and (null body) (null kids))
      `(make-event (er soft 'fn2-dispatch-held "~x0 is constrained without a held-frame contract." ',fn)))
     ((and recp (not (equal recp (list fn))))
      `(make-event (er soft 'fn2-dispatch-held "~x0 is mutually recursive (~x1): no held-frame chain." ',fn ',recp)))
     (t
      (let ((plain `(progn
                      ,(fn2-dh-lemma name outs call (strip-cars hyps) (strip-cars ohyps)
                                     (fn2-dh-chain-hints fn call body kids recp nil touches owners world) world)
                      (table fn2-dh-keeps ',fn ',(append (fn2-dh-facts-of outs hyps ohyps name) old)))))
        (cond
         ((and recp (not checkp))
          ;; a recursive function whose definition the induction step does
          ;; not open on its own: the same lemma with the call expanded
          `(make-event
            '(:or ,plain
                  (progn
                    ,(fn2-dh-lemma name outs call (strip-cars hyps) (strip-cars ohyps)
                                   (fn2-dh-hints-expand (fn2-dh-chain-hints fn call body kids recp nil touches owners world) call body)
                                   world)
                    (table fn2-dh-keeps ',fn ',(append (fn2-dh-facts-of outs hyps ohyps name) old))))))
         ((not checkp) plain)
         (t
          `(make-event
            '(:or ,plain
                  (progn
                    ,(fn2-dh-lemma name outs call (strip-cars chyps) (strip-cars ohyps)
                                   (fn2-dh-chain-hints fn call body kids recp t touches owners world) world)
                    (table fn2-dh-keeps ',fn ',(append (fn2-dh-facts-of outs chyps ohyps name) old))))))))))))
(defun fn2-dh-chain-forms-m (fns kind mode)
  (declare (xargs :mode :program))
  (if (atom fns) nil
    (cons `(make-event (value (fn2-dh-chain-event ',(car fns) ',kind ',mode (w state))))
          (fn2-dh-chain-forms-m (cdr fns) kind mode))))
(defun fn2-dh-chain-forms (fns kind) (declare (xargs :mode :program)) (fn2-dh-chain-forms-m fns kind nil))

;; An owner table S (its owner column COL, the core's accessor ACC): its
;; entry, and the facts of the column's two writers (their value is not K).
(defun fn2-dh-setters-of (s cols world)
  (declare (xargs :mode :program))
  (if (atom cols) nil
    (let ((set (fn2-columns-col-name s (fn2-columns-pre "SET-" (car cols)))))
      (if (function-symbolp set world) (cons set (fn2-dh-setters-of s (cdr cols) world)) (fn2-dh-setters-of s (cdr cols) world)))))
(defun fn2-dh-owner-events (s col acc world)
  (declare (xargs :mode :program))
  (let* ((reader (fn2-columns-col-name s col))
         (raw-reader (fn2-columns-sym reader "$AI"))
         (c (unquote (getpropc (fn2-columns-pre "*" (fn2-columns-sym raw-reader "*")) 'const nil world)))
         (cset (fn2-columns-col-name s (fn2-columns-pre "SET-" col)))
         (craw (fn2-columns-pre "UPDATE-" raw-reader)))
    `((table fn2-dh-owners ',s '(,c (,reader ,raw-reader) ,acc
                                    (,@(fn2-dh-setters-of s (strip-cars (fn2-view-layout s world)) world)
                                     ,@(fn2-dh-updaters (caddr (getpropc s 'stobj nil world)) s))))
      (table fn2-dh-keeps ',cset '((fn2-dh-col-ok nil ,s (((not (equal v fn2-dh-k)))) :open)))
      (table fn2-dh-keeps ',craw '((fn2-dh-col-ok nil ,s (((not (equal v fn2-dh-k)))) :open))))))
(defun fn2-dh-owner-events-all (tables world)
  (declare (xargs :mode :program))
  (if (atom tables) nil
    (append (fn2-dh-owner-events (nth 0 (car tables)) (nth 1 (car tables)) (nth 2 (car tables)) world)
            (fn2-dh-owner-events-all (cdr tables) world))))
;; FN2-DH-OWNERS-OK K CORE: every owner table's stored owners avoid K.
(defun fn2-dh-owners-ok-form (world)
  (declare (xargs :mode :program))
  `(defun-nx fn2-dh-owners-ok (fn2-dh-k fn2-core) (and ,@(fn2-dh-owner-comps (fn2-dh-owners world) 'fn2-core))))

;; Whether FN's closure writes an owner table of the core (calls the core
;; updater of one): only then is the owners claim of an attachment owed a chain.
(defun fn2-dh-owner-writes-any (fns seen)
  (declare (xargs :mode :program))
  (and (consp fns) (or (cdr (assoc-eq (car fns) seen)) (fn2-dh-owner-writes-any (cdr fns) seen))))
(defun fn2-dh-core-updaters (accs)
  (declare (xargs :mode :program))
  (if (atom accs) nil (cons (fn2-columns-pre "UPDATE-" (car accs)) (fn2-dh-core-updaters (cdr accs)))))

(defun fn2-dh-owner-writes (fns targets world seen fuel)
  ; SEEN: an alist fn -> writes-p, extended over FNS's closure
  (declare (xargs :mode :program))
  (cond ((or (zp fuel) (atom fns)) seen)
        ((assoc-eq (car fns) seen) (fn2-dh-owner-writes (cdr fns) targets world seen fuel))
        (t (let* ((callees (all-fnnames (getpropc (car fns) 'unnormalized-body nil world)))
                  (seen (fn2-dh-owner-writes callees targets world (acons (car fns) nil seen) (1- fuel))))
             (fn2-dh-owner-writes (cdr fns) targets world
                                  (put-assoc-eq (car fns) (or (intersectp-eq callees targets) (fn2-dh-owner-writes-any callees seen)) seen)
                                  fuel)))))
(defun fn2-dh-owner-writes-p (fn world)
  (declare (xargs :mode :program))
  (let ((targets (fn2-dh-core-updaters (fn2-dh-owner-accs (fn2-dh-owners world)))))
    (cdr (assoc-eq fn (fn2-dh-owner-writes (list fn) targets world nil 100000)))))
;; FN2-DH-OWNERS-OK through the core: each table's part of it (-COL), and
;; its value after each core field's update (-OF-UPDATE-X), for the chain
;; (theory fn2-dh-owners-rules), so a chain lemma's owner conclusion is the
;; whole invariant of its result, from the whole invariant of its argument.
(defun fn2-dh-owner-col-rules (owners)
  (declare (xargs :mode :program))
  (if (atom owners) nil
    (cons `(defthm ,(fn2-columns-sym 'fn2-dh-owners-ok (concatenate 'string "-" (symbol-name (nth 3 (car owners)))))
             (implies (fn2-dh-owners-ok k c) (fn2-dh-col-ok k ',(nth 1 (car owners)) (,(nth 3 (car owners)) c)))
             :hints (("Goal" :in-theory '(fn2-dh-owners-ok))))
          (fn2-dh-owner-col-rules (cdr owners)))))
(defun fn2-dh-owner-update-rules (fields owners)
  (declare (xargs :mode :program))
  (if (atom fields) nil
    (let* ((acc (car fields)) (update (fn2-columns-pre "UPDATE-" acc))
           (e (assoc-eq acc (pairlis$ (fn2-dh-owner-accs owners) owners)))
           (rhs (if e
                    `(and ,@(fn2-dh-owner-comps-at owners 'c acc 'v))
                  '(fn2-dh-owners-ok k c))))
      (cons `(defthm ,(fn2-columns-sym 'fn2-dh-owners-ok (concatenate 'string "-OF-" (symbol-name update)))
               (equal (fn2-dh-owners-ok k (,update v c)) ,(subst 'k 'fn2-dh-k rhs))
               :hints (("Goal" :in-theory (enable fn2-dh-owners-ok))))
            (fn2-dh-owner-update-rules (cdr fields) owners)))))
(defun fn2-dh-owners-rules-forms (world)
  (declare (xargs :mode :program))
  (let ((owners (fn2-dh-owners world))
        (fields (strip-cars (unquote (getpropc '*fn2-core-children* 'const nil world)))))
    `((deflabel fn2-dh-owners-rules-start)
      ,@(fn2-dh-owner-col-rules owners)
      ,@(fn2-dh-owner-update-rules fields owners)
      (deftheory fn2-dh-owners-rules
        (set-difference-theories (current-theory :here) (current-theory 'fn2-dh-owners-rules-start))))))

;; THE CLAIMS of a dispatch's attachment FN (its core result at POS):
;; - held (in the held view at the commit kind, assembly-dispatch
;;   fn2-dispatch-held): every hypothesis of FN's chain at K the commit kind
;;   must be an owner kind that is a constant other than K, or -- for a stub
;;   whose claim assumes it (OWNERSP) -- the core's stored owners avoiding K;
;; - owners: the core's stored owners avoiding the commit kind stay so, from
;;   a KIDS contract leaving the owner tables or from FN's chain, whose owner
;;   hypotheses must be constants other than K.
;; Else refused, naming each hypothesis with the callees it comes from, down
;; to the primitive.
(defun fn2-dh-hyp-ok (h kv ownersp)
  (declare (xargs :mode :program))
  (or (and ownersp (equal h '(fn2-dh-owners-ok fn2-dh-k fn2-core)))
      (and (consp h) (eq (car h) 'not) (consp (cadr h)) (eq (car (cadr h)) 'equal)
           (let ((a (cadr (cadr h))) (b (caddr (cadr h))))
             (or (and (eq b 'fn2-dh-k) (quotep a) (not (equal (unquote a) kv)))
                 (and (eq a 'fn2-dh-k) (quotep b) (not (equal (unquote b) kv))))))))
(defun fn2-dh-bad-hyps (hyps kv ownersp)
  (declare (xargs :mode :program))
  (cond ((atom hyps) nil)
        ((fn2-dh-hyp-ok (caar hyps) kv ownersp) (fn2-dh-bad-hyps (cdr hyps) kv ownersp))
        (t (cons (car hyps) (fn2-dh-bad-hyps (cdr hyps) kv ownersp)))))
(defun fn2-dh-all-hyps (facts ownerp)
  (declare (xargs :mode :program))
  (cond ((atom facts) nil)
        ((or (not ownerp) (fn2-dh-owner-obs-p (car (car facts))))
         (union-equal (nth 3 (car facts)) (fn2-dh-all-hyps (cdr facts) ownerp)))
        (t (fn2-dh-all-hyps (cdr facts) ownerp))))
(defun fn2-dh-claim-form (who fn pos ownersp world)
  (declare (xargs :mode :program))
  (let* ((facts (fn2-dh-facts fn world))
         (kv (unquote (getpropc '*fn2-commit-kind* 'const nil world)))
         (bad (fn2-dh-bad-hyps (fn2-dh-all-hyps facts nil) kv ownersp))
         (out `(mv-nth ,pos (,fn ,@(formals fn world)))))
    (cond ((null facts)
           `(make-event (er soft 'fn2-dispatch-held "The attachment ~x0 of ~x1 has no held-frame chain." ',fn ',who)))
          (bad
           `(make-event (er soft 'fn2-dispatch-held
                            "The attachment ~x0 of ~x1 may write rows the commit kind ~x2 holds: its chain needs ~x3 (each with the callees it comes from)."
                            ',fn ',who ',kv ',bad)))
          (t `(defthm ,(fn2-columns-sym fn "-DISPATCH-HELD")
                ,(if ownersp
                     `(implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core) (fn2-dispatch-held ,out fn2-core))
                   `(fn2-dispatch-held ,out fn2-core))
                :hints (("Goal" :in-theory (union-theories '(fn2-dispatch-held fn2-dispatch-held-obs fn2-dh-obs (:e equal) (:e not)
                                                             ,@(fn2-dh-fact-names facts fn world))
                                                           (theory 'minimal-theory)))))))))
(defun fn2-dh-owners-claim-form (who fn pos kind world)
  (declare (xargs :mode :program))
  (let* ((d (fn2-dc-entry fn kind world))
         (ks (fn2-arm-frame-indices (fn2-dh-owner-accs (fn2-dh-owners world)) world))
         (call `(,fn ,@(formals fn world)))
         (out `(mv-nth ,pos ,call))
         (name (fn2-columns-sym fn "-DISPATCH-OWNERS"))
         (stmt `(implies (fn2-dh-owners-ok *fn2-commit-kind* fn2-core) (fn2-dh-owners-ok *fn2-commit-kind* ,out))))
    (if (and d (not (intersectp-equal ks (car d))))
        `(defthm ,name ,stmt
           :hints (("Goal" :in-theory (union-theories '(fn2-dh-owners-ok ,@(fn2-dh-owner-accs (fn2-dh-owners world)))
                                                      (theory 'fn2-arm-frame-base))
                    :use ((:instance ,(cdr d) (fn2-arm-free ',(car d)) (fn2-arm-c0 fn2-core))
                          (:instance fn2-arm-kids-refl (i 0) (free ',(car d)) (a fn2-core))
                          ,@(fn2-dh-kids-nths ks d out)))))
      (let* ((facts (fn2-dh-facts fn world))
             (kv (unquote (getpropc '*fn2-commit-kind* 'const nil world)))
             (bad (fn2-dh-bad-hyps (fn2-dh-all-hyps facts t) kv t)))
        (cond ((null facts)
               `(make-event (er soft 'fn2-dispatch-held
                                "The attachment ~x0 of ~x1 writes an owner table (~x2) and has no held-frame chain."
                                ',fn ',who ',(car d))))
              (bad
               `(make-event (er soft 'fn2-dispatch-held
                                "The attachment ~x0 of ~x1 may store the commit kind ~x2 as an owner: its chain needs ~x3 (each with the callees it comes from)."
                                ',fn ',who ',kv ',bad)))
              (t `(defthm ,name ,stmt
                    :hints (("Goal" :in-theory (union-theories '((:e equal) (:e not) ,@(fn2-dh-fact-names facts fn world))
                                                               (theory 'minimal-theory)))))))))))
