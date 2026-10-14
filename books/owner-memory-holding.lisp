; The owner carries the union of logical readers and physical disposal debt.
; Gates read COUNT without walking the connections or another actor's roster.
(in-package "ACL2")
(include-book "public-exposure")
(include-book "admission-memory")
(include-book "owner-open-carried")
(include-book "acceptance-alloc")
(include-book "defrecord")
(include-book "state-globals")

(local (in-theory (disable (tau-system))))

(def-loop fn-adm-hh-drop (id rows)
 :shape :map :over rows :elt row
 :stop (and (consp row) (equal (car row) id))
 :stop-value (cdr rows) :body row)
(defun fn-adm-hh-put (id logical physical rows)
 (declare (xargs :guard t))
 (cons (list id logical physical) (fn-adm-hh-drop id rows)))

(def-loop fn-adm-hh-row-errors (rows)
 :shape :sum :over rows :elt row
 :body (if (and (true-listp row) (equal (len row) 3) (natp (car row))) 0 1))

(fn-defrecord fn-adm-hh
 :constructor (fn-adm-hh-make count rows)
 :fields ((fn-adm-hh-count natp) (fn-adm-hh-rows true-listp))
 :extra ((equal (fn-adm-hh-row-errors (fn-adm-hh-rows x)) 0)
         (equal (fn-adm-hh-count x) (len (fn-adm-hh-rows x)))))

(defun fn-adm-hh-initial ()
 (declare (xargs :guard t))
 (fn-adm-hh-make 0 nil))

; The three-cell rows use the generated exposure map operations: identity,
; logical presence, physical presence. Updates run only at lifecycle edges.
(defun fn-adm-hh-update (bank id logical physical)
 (declare (xargs :guard t))
 (if (not (natp id)) bank
  (let* ((rows (fn-adm-hh-rows bank))
         (old (fn-exp-lookup id rows))
         (alive (or logical physical))
         (count (nfix (fn-adm-hh-count bank))))
   (fn-adm-hh-make
    (cond ((and old (not alive)) (nfix (1- count)))
          ((and (not old) alive) (1+ count))
          (t count))
    (if alive (fn-adm-hh-put id (and logical t) (and physical t) rows)
      (fn-adm-hh-drop id rows))))))

(defun fn-adm-hh-open (bank id physical)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id t
  (or physical (fn-exp-at 2 (fn-exp-lookup id (fn-adm-hh-rows bank))))))

(defun fn-adm-hh-close (bank id)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id nil
  (fn-exp-at 2 (fn-exp-lookup id (fn-adm-hh-rows bank)))))

(defun fn-adm-hh-return (bank id)
 (declare (xargs :guard t))
 (fn-adm-hh-update bank id
  (fn-exp-at 1 (fn-exp-lookup id (fn-adm-hh-rows bank))) nil))

; A persistent HTTP transport transfers its physical identity to its next
; logical reader only after the preceding reader ended, under the owner.
(defun fn-adm-hh-rearm (bank old-id new-id)
 (declare (xargs :guard t))
 (let ((old (fn-exp-lookup old-id (fn-adm-hh-rows bank)))
       (new (fn-exp-lookup new-id (fn-adm-hh-rows bank))))
  (if (and (not (equal old-id new-id))
           (not (fn-exp-at 1 old)) (fn-exp-at 2 old) (fn-exp-at 1 new))
   (fn-adm-hh-open (fn-adm-hh-return bank old-id) new-id t)
   bank)))

(defun fn-owner-memory-held-bank (state)
 (declare (xargs :stobjs state :guard t))
 (if (boundp-global 'fn-owner-memory-held-bank state)
  (f-get-global 'fn-owner-memory-held-bank state)
  (fn-adm-hh-initial)))

(defun fn-owner-memory-held (state)
 (declare (xargs :stobjs state :guard t))
 (nfix (fn-adm-hh-count (fn-owner-memory-held-bank state))))

(defun fn-owner-memory-held-open (id physical state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-open (fn-owner-memory-held-bank state) id physical) state))

(defun fn-adm-operator-close (bank operator-id id)
  (declare (xargs :guard t))
  (list (fn-adm-hh-close bank id)
        (if (equal id operator-id) nil operator-id)))



(defun fn-owner-memory-held-return (id state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank
  (fn-adm-hh-return (fn-owner-memory-held-bank state) id) state))



(local (defthm m22-lookup-implies-consp-by-definition
 (implies (fn-exp-lookup id rows) (< 0 (len rows)))
 :hints (("Goal" :induct (fn-exp-lookup id rows) :in-theory (enable fn-exp-lookup)))))

(local (defthm m22-drop-count-by-definition
 (implies (equal (fn-adm-hh-row-errors rows) 0)
  (equal (len (fn-adm-hh-drop id rows))
        (if (fn-exp-lookup id rows) (1- (len rows)) (len rows))))
 :hints (("Goal" :induct (fn-exp-lookup id rows)
          :in-theory (enable fn-adm-hh-drop fn-exp-lookup fn-adm-hh-row-errors)))))

(local (defthm m22-drop-is-true-list-by-definition
 (implies (true-listp rows) (true-listp (fn-adm-hh-drop id rows)))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows) :in-theory (enable fn-adm-hh-drop true-listp)))))

(local (defthm m22-drop-preserves-rows-by-definition
 (implies (equal (fn-adm-hh-row-errors rows) 0)
          (equal (fn-adm-hh-row-errors (fn-adm-hh-drop id rows)) 0))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-row-errors)))))

(local (defthm m22-put-preserves-rows-by-definition
 (implies (and (natp id) (equal (fn-adm-hh-row-errors rows) 0))
          (equal (fn-adm-hh-row-errors (fn-adm-hh-put id logical physical rows)) 0))
 :hints (("Goal" :in-theory (enable fn-adm-hh-put fn-adm-hh-row-errors)))))

(local (defthm m22-initial-bank-is-valid-by-definition
 (fn-adm-hhp (fn-adm-hh-initial))
 :hints (("Goal" :in-theory (enable fn-adm-hh-initial fn-adm-hhp)))))

(defthm fn-adm-hh-update-preserves-validity
 (implies (fn-adm-hhp bank) (fn-adm-hhp (fn-adm-hh-update bank id logical physical)))
 :hints (("Goal" :use ((:instance m22-lookup-implies-consp-by-definition (rows (fn-adm-hh-rows bank)))) :in-theory (e/d (fn-adm-hhp fn-adm-hh-update fn-adm-hh-put)
   (fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup fn-adm-hh-drop)))))

; Cached cardinality refines the union of logical and physical custody.
(def-loop fn-adm-hh-ids (rows)
 :shape :map :over rows :elt row :body (fn-exp-at 0 row))
(def-loop fn-adm-hh-dead (rows)
 :shape :sum :over rows :elt row :body (if (or (fn-exp-at 1 row) (fn-exp-at 2 row)) 0 1))
(defun fn-adm-hh-representsp (bank)
 (declare (xargs :guard t))
 (and (fn-adm-hhp bank)
      (no-duplicatesp-equal (fn-adm-hh-ids (fn-adm-hh-rows bank)))
      (equal (fn-adm-hh-dead (fn-adm-hh-rows bank)) 0)))
(local (defthm m22-drop-ids-subset
 (implies (not (member-equal key (fn-adm-hh-ids rows)))
          (not (member-equal key (fn-adm-hh-ids (fn-adm-hh-drop id rows)))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids)))))
(local (defthm m22-drop-preserves-unique-ids
 (implies (no-duplicatesp-equal (fn-adm-hh-ids rows))
          (no-duplicatesp-equal (fn-adm-hh-ids (fn-adm-hh-drop id rows))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids)))))
(local (defthm m22-drop-removes-id
 (implies (and (no-duplicatesp-equal (fn-adm-hh-ids rows))
               (equal (fn-adm-hh-row-errors rows) 0))
          (not (member-equal id (fn-adm-hh-ids (fn-adm-hh-drop id rows)))))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-ids fn-adm-hh-row-errors)))))
(local (defthm m22-drop-preserves-live-rows
 (implies (equal (fn-adm-hh-dead rows) 0)
          (equal (fn-adm-hh-dead (fn-adm-hh-drop id rows)) 0))
 :hints (("Goal" :induct (fn-adm-hh-drop id rows)
          :in-theory (enable fn-adm-hh-drop fn-adm-hh-dead)))))
(defthm fn-adm-hh-initial-represents-the-empty-union
 (fn-adm-hh-representsp (fn-adm-hh-initial))
 :hints (("Goal" :in-theory (enable fn-adm-hh-representsp fn-adm-hh-initial fn-adm-hhp))))
(defthm fn-adm-hh-update-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
          (fn-adm-hh-representsp (fn-adm-hh-update bank id logical physical)))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-hh-representsp fn-adm-hhp fn-adm-hh-update fn-adm-hh-put fn-adm-hh-ids fn-adm-hh-dead)
 (fn-adm-hh-drop fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup))
 :use (fn-adm-hh-update-preserves-validity))))

(def-loop fn-adm-hh-present-ids (rows)
 :shape :map :over rows :elt row
 :keep (or (fn-exp-at 1 row) (fn-exp-at 2 row)) :body (fn-exp-at 0 row))
(local (defthm m22-ids-length-by-definition
 (equal (len (fn-adm-hh-ids rows)) (len rows))
 :hints (("Goal" :induct (fn-adm-hh-ids rows) :in-theory (enable fn-adm-hh-ids)))))
(local (defthm m22-live-union-is-all-ids
 (implies (equal (fn-adm-hh-dead rows) 0)
          (equal (fn-adm-hh-present-ids rows) (fn-adm-hh-ids rows)))
 :hints (("Goal" :induct (fn-adm-hh-dead rows)
          :in-theory (enable fn-adm-hh-dead fn-adm-hh-present-ids fn-adm-hh-ids)))))
(defthm fn-adm-hh-cached-count-is-the-union-cardinality
 (implies (fn-adm-hh-representsp bank)
  (and (no-duplicatesp-equal (fn-adm-hh-present-ids (fn-adm-hh-rows bank)))
       (equal (fn-adm-hh-count bank) (len (fn-adm-hh-present-ids (fn-adm-hh-rows bank))))))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-representsp fn-adm-hhp)
                               (fn-adm-hh-rows fn-adm-hh-count fn-adm-hh-present-ids fn-adm-hh-ids)))))
(defthm fn-adm-hh-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-open bank id physical)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-open) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-close-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-close bank id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-close) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-return-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-return bank id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-return) (fn-adm-hh-update fn-adm-hh-representsp)))))
(defthm fn-adm-hh-rearm-preserves-identity-union
 (implies (fn-adm-hh-representsp bank) (fn-adm-hh-representsp (fn-adm-hh-rearm bank old-id new-id)))
 :hints (("Goal" :in-theory (e/d (fn-adm-hh-rearm) (fn-adm-hh-open fn-adm-hh-return fn-adm-hh-update fn-adm-hh-representsp)))))

; M24 held admission and same-step persistent-transport transfer.
(defun fn-adm-admission-held (result)
  (declare (xargs :guard t))
  (nfix (fn-adm-hh-count (fn-exp-at 2 result))))

(defun fn-adm-held-open-roomp (bank configured capacity id)
  (declare (xargs :guard t))
  (and (< (nfix (fn-adm-hh-count bank))
          (fn-adm-reader-count configured capacity))
       (natp id)
       (not (fn-exp-lookup id (fn-adm-hh-rows bank)))))

(defun fn-adm-held-open-refusal (kind oc xs decision now bank)
  (declare (xargs :guard t))
  (list :refuse
    (if (equal kind :exposure)
      (list nil oc
        (fn-exp-with xs (fn-exp-conns xs) (fn-exp-rates xs)
          (fn-exp-fails xs) (fn-exp-posts xs)
          (fn-exp-counters-bump (nfix (fn-exp-at 2 decision)) now
                                (fn-exp-counters xs)))
        nil (fn-exp-line (fn-exp-at 1 decision)))
      (cons nil oc))
    bank (nfix (fn-adm-hh-count bank)) nil))

(defun fn-adm-held-open
  (kind oc xs lim acfg peer address now bank configured capacity)
  (declare (xargs :guard t))
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (busy (list :refuse *fn-exp-busy-line* 1))
         (policy (if (equal kind :exposure)
                   (fn-exp-admit-decision xs lim held address now)
                   (list :admit))))
    (cond
      ((not (member-eq kind '(:exposure :peer :reader)))
       (fn-adm-held-open-refusal kind oc xs busy now bank))
      ((not (fn-adm-held-open-roomp bank configured capacity id))
       (fn-adm-held-open-refusal kind oc xs busy now bank))
      ((not (equal (car policy) :admit))
       (fn-adm-held-open-refusal kind oc xs policy now bank))
      (t
       (let* ((opened
                (case kind
                  (:exposure (fn-ocar-exp-open oc xs lim acfg peer address now))
                  (:peer (fn-ocfg-open-peer oc peer acfg))
                  (otherwise (fn-ocar-ocfg-open oc acfg))))
              (actual-id
                (if (equal kind :exposure)
                  (fn-exp-open-id opened)
                  (and (fn-own-find-conn id
                         (fn-own-conns (fn-ocfg-owner (cdr opened)))) id))))
         (if (and (natp actual-id) (equal actual-id id))
           (list :admit opened
             (fn-adm-hh-open bank id (not (equal kind :reader)))
             (1+ held) id)
           (list :refuse opened bank held nil)))))))

(defun fn-adm-exposure-open
  (oc xs lim acfg peer address now bank configured capacity)
  (declare (xargs :guard t))
  (fn-adm-held-open :exposure oc xs lim acfg peer address now
                    bank configured capacity))

(defun fn-adm-peer-open (oc peer acfg bank configured capacity)
  (declare (xargs :guard t))
  (fn-adm-held-open :peer oc nil nil acfg peer nil 0 bank configured capacity))

(defun fn-adm-reader-open (oc acfg bank configured capacity)
  (declare (xargs :guard t))
  (fn-adm-held-open :reader oc nil nil acfg nil nil 0 bank configured capacity))

(defun fn-adm-transport-rearm
  (kind oc xs lim acfg peer address now bank old-id configured capacity)
  (declare (xargs :guard t))
  (let ((old (fn-exp-lookup old-id (fn-adm-hh-rows bank))))
    (if (and (member-eq kind '(:exposure :peer))
             (natp old-id) (not (fn-exp-at 1 old)) (fn-exp-at 2 old))
      (let ((r (fn-adm-held-open kind oc xs lim acfg peer address now
                                (fn-adm-hh-return bank old-id) configured capacity)))
        (if (equal (car r) :admit)
          r
          (update-nth 3 (nfix (fn-adm-hh-count bank)) (update-nth 2 bank r))))
      (fn-adm-held-open-refusal kind oc xs
        (list :refuse *fn-exp-busy-line* 1) now bank))))

(local (defthm m24-held-refusal-selectors-by-definition
 (let ((r (fn-adm-held-open-refusal kind oc xs decision now bank)))
  (and (equal (car r) :refuse) (equal (fn-exp-at 2 r) bank)
       (equal (fn-exp-at 3 r) (nfix (fn-adm-hh-count bank)))))
 :hints (("Goal" :in-theory (union-theories
   '(fn-adm-held-open-refusal fn-exp-at nth nfix natp car-cons cdr-cons)
   (theory 'minimal-theory))))))

(local (defthm m23-bank-count-of-make-by-definition
 (equal (fn-adm-hh-count (fn-adm-hh-make count rows)) count)
 :hints (("Goal" :in-theory (enable fn-adm-hh-count fn-adm-hh-make)))))

(local (defthm m23-held-open-admission-by-definition
 (let ((r (fn-adm-held-open kind oc xs lim acfg peer address now bank configured capacity)))
  (implies (equal (car r) :admit)
   (and (< (nfix (fn-adm-hh-count bank)) (fn-adm-reader-count configured capacity))
        (equal (fn-exp-at 3 r) (1+ (nfix (fn-adm-hh-count bank))))
        (equal (fn-adm-admission-held r) (1+ (nfix (fn-adm-hh-count bank)))))))
 :hints (("Goal" :in-theory (e/d
  (fn-adm-held-open fn-adm-held-open-roomp fn-adm-held-open-refusal
   fn-adm-admission-held fn-adm-hh-open fn-adm-hh-update fn-exp-at)
  (fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop
   fn-ocar-exp-open fn-ocfg-open-peer fn-ocar-ocfg-open fn-exp-open-id
   fn-own-find-conn fn-ocfg-owner fn-own-conns fn-own-next-id fn-exp-admit-decision
   fn-adm-reader-count))))))

(local (defthm m23-lookup-implies-positive-length-by-definition
 (implies (fn-exp-lookup id rows) (< 0 (len rows)))
 :hints (("Goal" :induct (fn-exp-lookup id rows) :in-theory (enable fn-exp-lookup)))))

(local (defthm m23-return-ended-held-count-by-definition
 (implies (and (fn-adm-hhp bank) (natp old-id)
               (not (fn-exp-at 1 (fn-exp-lookup old-id (fn-adm-hh-rows bank))))
               (fn-exp-at 2 (fn-exp-lookup old-id (fn-adm-hh-rows bank))))
  (equal (1+ (nfix (fn-adm-hh-count (fn-adm-hh-return bank old-id))))
         (nfix (fn-adm-hh-count bank))))
 :hints (("Goal" :use ((:instance m23-lookup-implies-positive-length-by-definition
                             (id old-id) (rows (fn-adm-hh-rows bank))))
  :in-theory (e/d (fn-adm-hhp fn-adm-hh-return fn-adm-hh-update fn-exp-at)
                 (fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop))))))

(defthm fn-adm-exposure-open-admits-below-held-reader-bound
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-exposure-open oc xs lim acfg peer address now
                                  bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
  :rule-classes nil :hints (("Goal"
 :use ((:instance m23-held-open-admission-by-definition (kind :exposure))
       (:instance m23-held-open-admission-by-definition (kind :peer)
          (xs nil) (lim nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition (kind :reader)
          (xs nil) (lim nil) (peer nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition
          (bank (fn-adm-hh-return bank old-id)))
       m23-return-ended-held-count-by-definition)
 :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count
  fn-adm-hh-rows fn-exp-lookup fn-adm-reader-count fn-adm-hhp
  m23-held-open-admission-by-definition nfix fn-adm-held-open-refusal)))))

(defthm fn-adm-peer-open-admits-below-held-reader-bound
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-peer-open oc peer acfg bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
  :rule-classes nil :hints (("Goal"
 :use ((:instance m23-held-open-admission-by-definition (kind :exposure))
       (:instance m23-held-open-admission-by-definition (kind :peer)
          (xs nil) (lim nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition (kind :reader)
          (xs nil) (lim nil) (peer nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition
          (bank (fn-adm-hh-return bank old-id)))
       m23-return-ended-held-count-by-definition)
 :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count
  fn-adm-hh-rows fn-exp-lookup fn-adm-reader-count fn-adm-hhp
  m23-held-open-admission-by-definition nfix fn-adm-held-open-refusal)))))

(defthm fn-adm-transport-rearm-admits-below-held-reader-bound
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-transport-rearm kind oc xs lim acfg peer address now
                                    bank old-id configured capacity)))
    (implies (and (fn-adm-hhp bank) (equal (car r) :admit))
      (and (< (nfix (fn-adm-hh-count (fn-adm-hh-return bank old-id)))
              (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) held)
           (equal (fn-adm-admission-held r) held))))
  :rule-classes nil :hints (("Goal"
 :use ((:instance m23-held-open-admission-by-definition (kind :exposure))
       (:instance m23-held-open-admission-by-definition (kind :peer)
          (xs nil) (lim nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition (kind :reader)
          (xs nil) (lim nil) (peer nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition
          (bank (fn-adm-hh-return bank old-id)))
       m23-return-ended-held-count-by-definition)
 :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count
  fn-adm-hh-rows fn-exp-lookup fn-adm-reader-count fn-adm-hhp
  m23-held-open-admission-by-definition nfix fn-adm-held-open-refusal)))))

(defthm fn-adm-reader-open-admits-below-held-reader-bound
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (r (fn-adm-reader-open oc acfg bank configured capacity)))
    (implies (equal (car r) :admit)
      (and (< held (fn-adm-reader-count configured capacity))
           (equal (fn-exp-at 3 r) (1+ held))
           (equal (fn-adm-admission-held r) (1+ held)))))
  :rule-classes nil :hints (("Goal"
 :use ((:instance m23-held-open-admission-by-definition (kind :exposure))
       (:instance m23-held-open-admission-by-definition (kind :peer)
          (xs nil) (lim nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition (kind :reader)
          (xs nil) (lim nil) (peer nil) (address nil) (now 0))
       (:instance m23-held-open-admission-by-definition
          (bank (fn-adm-hh-return bank old-id)))
       m23-return-ended-held-count-by-definition)
 :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count
  fn-adm-hh-rows fn-exp-lookup fn-adm-reader-count fn-adm-hhp
  m23-held-open-admission-by-definition nfix fn-adm-held-open-refusal)))))

(local (defthm m24-fix-update-by-definition
 (equal (true-list-fix (update-nth n v xs)) (update-nth n v (true-list-fix xs)))
 :hints (("Goal" :induct (update-nth n v xs)
                 :in-theory (enable update-nth true-list-fix)))))

(local (defthm m24-repeat-update-by-definition
 (equal (update-nth n a (update-nth n b xs)) (update-nth n a xs))
 :hints (("Goal" :induct (update-nth n a xs) :in-theory (enable update-nth)))))

(local (defthm m24-priced-installed-gate-by-definition
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg)))
        (configured (fn-mm-cfg-connections run-cfg))
        (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)))
  (implies (and (< 0 capacity) (<= (nfix held) (fn-adm-reader-count configured capacity)))
   (and (equal (fn-adm-priced-connections held configured capacity)
               (fn-adm-reader-count configured capacity))
        (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg held capacity) limit tot))))
 :hints (("Goal"
  :use ((:instance fn-adm-installed-capacity-is-proved-or-zero
         (cfg (update-nth 10 nil (true-list-fix cfg))))
        (:instance fn-adm-gate-antitone-in-the-connections
         (cfg (update-nth 10 nil (true-list-fix cfg)))
         (j (fn-adm-installed-capacity profile img (update-nth 10 nil (true-list-fix cfg)) limit tot))
         (k (1+ (fn-adm-installed-capacity profile img (update-nth 10 nil (true-list-fix cfg)) limit tot)))))
  :in-theory (e/d (fn-adm-public-readers-cfg fn-adm-reader-count fn-adm-priced-connections fn-adm-priced-cfg
                  fn-adm-cfg-at)
                 (fn-adm-installed-capacity fn-adm-capacity fn-mm-gate-p
                  fn-mm-cfg-connections))))))

(local (defthm m24-held-open-composes-with-installed-capacity
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg)))
        (configured (fn-mm-cfg-connections run-cfg))
        (capacity (fn-adm-installed-capacity profile img run-cfg limit tot))
        (r (fn-adm-held-open kind oc xs lim acfg peer address now bank configured capacity)))
  (implies (equal (car r) :admit)
   (and (<= (fn-exp-at 3 r) (fn-adm-reader-count configured capacity))
        (<= (fn-adm-admission-held r) (fn-adm-reader-count configured capacity))
        (equal (fn-adm-priced-connections (fn-adm-admission-held r) configured capacity)
               (fn-adm-reader-count configured capacity))
        (fn-mm-gate-p profile img
         (fn-adm-priced-cfg run-cfg (fn-adm-admission-held r) capacity) limit tot))))
 :hints (("Goal"
  :use ((:instance m23-held-open-admission-by-definition
           (configured (fn-mm-cfg-connections (update-nth 10 nil (true-list-fix cfg))))
           (capacity (fn-adm-installed-capacity profile img
                      (update-nth 10 nil (true-list-fix cfg)) limit tot)))
        (:instance m24-priced-installed-gate-by-definition
         (held (1+ (nfix (fn-adm-hh-count bank))))))
  :in-theory (e/d (fn-adm-reader-count)
   (fn-adm-installed-capacity fn-adm-capacity fn-mm-gate-p fn-adm-priced-cfg
    fn-adm-priced-connections fn-mm-cfg-connections fn-adm-admission-held
    fn-adm-held-open fn-adm-hh-count fn-exp-at
    m23-held-open-admission-by-definition m24-priced-installed-gate-by-definition))))))

(local (defthm m24-exposure-admission-composes
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (exposure (fn-adm-exposure-open oc xs lim acfg peer address now
                                         bank configured capacity))) (implies (equal (car exposure) :admit)
        (and (<= (fn-exp-at 3 exposure) reader-count)
             (<= (fn-adm-admission-held exposure) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held exposure) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held exposure) capacity)
               limit tot))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance m24-held-open-composes-with-installed-capacity (kind :exposure)))
  :in-theory (e/d
   (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm fn-exp-at)
   (fn-adm-held-open fn-adm-installed-capacity fn-mm-cfg-connections fn-adm-reader-count
    fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
    fn-adm-priced-connections fn-adm-priced-cfg fn-mm-gate-p fn-adm-held-open-refusal nfix
    m23-held-open-admission-by-definition m24-held-open-composes-with-installed-capacity))))))

(local (defthm m24-peer-admission-composes
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (peer-open (fn-adm-peer-open oc peer acfg bank configured capacity))) (implies (equal (car peer-open) :admit)
        (and (<= (fn-exp-at 3 peer-open) reader-count)
             (<= (fn-adm-admission-held peer-open) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held peer-open) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held peer-open) capacity)
               limit tot))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance m24-held-open-composes-with-installed-capacity (kind :peer) (xs nil) (lim nil) (address nil) (now 0)))
  :in-theory (e/d
   (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm fn-exp-at)
   (fn-adm-held-open fn-adm-installed-capacity fn-mm-cfg-connections fn-adm-reader-count
    fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
    fn-adm-priced-connections fn-adm-priced-cfg fn-mm-gate-p fn-adm-held-open-refusal nfix
    m23-held-open-admission-by-definition m24-held-open-composes-with-installed-capacity))))))

(local (defthm m24-rearm-admission-composes
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (rearm (fn-adm-transport-rearm kind oc xs lim acfg peer address now
                                        bank old-id configured capacity))) (implies (equal (car rearm) :admit)
        (and (<= (fn-exp-at 3 rearm) reader-count)
             (<= (fn-adm-admission-held rearm) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held rearm) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held rearm) capacity)
               limit tot))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance m24-held-open-composes-with-installed-capacity (bank (fn-adm-hh-return bank old-id))))
  :in-theory (e/d
   (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm fn-exp-at)
   (fn-adm-held-open fn-adm-installed-capacity fn-mm-cfg-connections fn-adm-reader-count
    fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
    fn-adm-priced-connections fn-adm-priced-cfg fn-mm-gate-p fn-adm-held-open-refusal nfix
    m23-held-open-admission-by-definition m24-held-open-composes-with-installed-capacity))))))

(local (defthm m24-reader-admission-composes
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (reader (fn-adm-reader-open oc acfg bank configured capacity))) (implies (equal (car reader) :admit)
        (and (<= (fn-exp-at 3 reader) reader-count)
             (<= (fn-adm-admission-held reader) reader-count)
             (equal (fn-adm-priced-connections
                      (fn-adm-admission-held reader) configured capacity) reader-count)
             (fn-mm-gate-p profile img
               (fn-adm-priced-cfg run-cfg (fn-adm-admission-held reader) capacity)
               limit tot))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance m24-held-open-composes-with-installed-capacity (kind :reader) (xs nil) (lim nil) (peer nil) (address nil) (now 0)))
  :in-theory (e/d
   (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm fn-exp-at)
   (fn-adm-held-open fn-adm-installed-capacity fn-mm-cfg-connections fn-adm-reader-count
    fn-adm-admission-held fn-adm-hh-return fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
    fn-adm-priced-connections fn-adm-priced-cfg fn-mm-gate-p fn-adm-held-open-refusal nfix
    m23-held-open-admission-by-definition m24-held-open-composes-with-installed-capacity))))))

(defun fn-adm-operator-slot-freep (operator-id)
  (declare (xargs :guard t))
  (not (natp operator-id)))

(defun fn-adm-operator-open-refusal (oc bank operator-id reason)
  (declare (xargs :guard t))
  (list :refuse (cons nil oc) bank (nfix (fn-adm-hh-count bank)) nil reason operator-id))

(defun fn-adm-operator-open
  (oc acfg bank configured capacity operator-id profile img cfg limit tot)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((held (nfix (fn-adm-hh-count bank)))
         (id (fn-own-next-id (fn-ocfg-owner oc)))
         (priced (fn-adm-priced-cfg cfg (1+ held) capacity)))
    (cond
      ((< held (fn-adm-reader-count configured capacity))
       (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
         (if (equal (car r) :admit)
           (list :admit (fn-exp-at 1 r) (fn-exp-at 2 r) (fn-exp-at 3 r) (fn-exp-at 4 r) nil operator-id)
           (list :refuse (fn-exp-at 1 r) bank held nil :operator-owner-bound operator-id))))
      ((not (fn-adm-operator-slot-freep operator-id))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-held))
      ((not (equal (fn-mm-cfg-connections cfg) (nfix configured)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-cfg-stale))
      ((or (not (natp id))
           (fn-exp-lookup id (fn-adm-hh-rows bank))
           (not (fn-adm-operator-fundedp profile img cfg limit tot capacity))
           (not (fn-mm-gate-p profile img priced limit tot)))
       (fn-adm-operator-open-refusal oc bank operator-id :operator-slot-memory))
      (t
       (let ((opened (fn-ocar-ocfg-open oc acfg)))
         (if (and (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))))
           (list :admit opened (fn-adm-hh-open bank id nil) (1+ held) id nil id)
           (fn-adm-operator-open-refusal oc bank operator-id :operator-owner-bound)))))))



(defun fn-adm-operator-open-word (result)
  (declare (xargs :guard t))
  (if (equal (fn-exp-at 0 result) :admit) :admitted :refused))

(defun fn-adm-operator-open-reason (result)
  (declare (xargs :guard t))
  (if (equal (fn-exp-at 0 result) :admit) nil (fn-exp-at 5 result)))

(defun fn-adm-operator-statep (bank operator-id)
 (declare (xargs :guard t))
 (and (fn-adm-hh-representsp bank)
      (or (null operator-id)
          (and (natp operator-id)
               (fn-exp-at 1 (fn-exp-lookup operator-id (fn-adm-hh-rows bank)))
               (not (fn-exp-at 2 (fn-exp-lookup operator-id (fn-adm-hh-rows bank))))))))

(defthm fn-adm-operator-statep-with-no-operator
  (implies (fn-adm-hh-representsp bank) (fn-adm-operator-statep bank nil))
  :hints (("Goal" :in-theory (e/d (fn-adm-operator-statep)
                                 (fn-adm-hh-representsp)))))

; The host install initializes this bank and run field 11 to NIL.
(defthm fn-adm-initial-bank-has-no-operator
 (fn-adm-operator-statep (fn-adm-hh-initial) nil)
 :hints (("Goal"
  :use ((:instance fn-adm-operator-statep-with-no-operator (bank (fn-adm-hh-initial)))
        fn-adm-hh-initial-represents-the-empty-union)
  :in-theory (theory 'minimal-theory))))

(defun fn-adm-operator-open-id (result)
 (declare (xargs :guard t))
 (if (equal (fn-exp-at 0 result) :admit) (fn-exp-at 4 result) nil))



(local (defthm m24-refused-rearm-bank-selector-by-definition
 (equal (fn-exp-at 2 (update-nth 3 peak (update-nth 2 bank r))) bank)
 :hints (("Goal" :expand ((update-nth 3 peak (update-nth 2 bank r))
                          (update-nth 2 bank r))
                  :in-theory (enable fn-exp-at update-nth)))))

(local (defthm m24-held-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
  (fn-adm-hh-representsp (fn-exp-at 2
   (fn-adm-held-open kind oc xs lim acfg peer address now bank configured capacity))))
 :hints (("Goal" :in-theory (e/d
  (fn-adm-held-open fn-exp-at)
  (fn-adm-hh-representsp fn-adm-hh-open fn-adm-held-open-roomp fn-exp-admit-decision
   fn-ocar-exp-open fn-ocar-ocfg-open fn-ocfg-open-peer fn-exp-open-id
   fn-own-find-conn fn-ocfg-owner fn-own-conns fn-own-next-id fn-adm-held-open-refusal))))))

(defthm fn-adm-exposure-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
  (fn-adm-hh-representsp (fn-exp-at 2 (fn-adm-exposure-open oc xs lim acfg peer address now bank configured capacity))))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-hh-representsp fn-adm-hh-return fn-adm-hh-rows fn-exp-lookup
  fn-adm-held-open-refusal)))))

(defthm fn-adm-peer-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
  (fn-adm-hh-representsp (fn-exp-at 2 (fn-adm-peer-open oc peer acfg bank configured capacity))))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-hh-representsp fn-adm-hh-return fn-adm-hh-rows fn-exp-lookup
  fn-adm-held-open-refusal)))))

(defthm fn-adm-reader-open-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
  (fn-adm-hh-representsp (fn-exp-at 2 (fn-adm-reader-open oc acfg bank configured capacity))))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-hh-representsp fn-adm-hh-return fn-adm-hh-rows fn-exp-lookup
  fn-adm-held-open-refusal)))))

(defthm fn-adm-transport-rearm-preserves-identity-union
 (implies (fn-adm-hh-representsp bank)
  (fn-adm-hh-representsp (fn-exp-at 2 (fn-adm-transport-rearm kind oc xs lim acfg peer address now bank old-id configured capacity))))
 :hints (("Goal" :in-theory (e/d
 (fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
  fn-exp-at)
 (fn-adm-held-open fn-adm-hh-representsp fn-adm-hh-return fn-adm-hh-rows fn-exp-lookup
  fn-adm-held-open-refusal)))))

(defun fn-owner-memory-held-install (result state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-memory-held-bank (fn-exp-at 2 result) state))
(defthm fn-owner-memory-held-install-preserves-owner-bound
 (implies (boundp-global 'fn-owner state)
  (boundp-global 'fn-owner (fn-owner-memory-held-install result state)))
 :hints (("Goal" :in-theory (enable fn-owner-memory-held-install boundp-global put-global))))

(defthm fn-adm-operator-open-refuses-a-held-slot
  (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
    (implies (and (natp operator-id)
                  (<= (fn-adm-reader-count configured capacity) (nfix (fn-adm-hh-count bank))))
      (and (equal (car r) :refuse)
           (equal (fn-exp-at 2 r) bank)
           (equal (fn-adm-operator-open-reason r) :operator-slot-held)
           (equal (fn-exp-at 6 r) operator-id))))
  :rule-classes nil
 :hints (("Goal" :in-theory (e/d
 (fn-adm-operator-open fn-adm-operator-slot-freep fn-adm-operator-open-refusal
  fn-adm-operator-open-reason fn-exp-at)
 (fn-adm-reader-count fn-adm-hh-count fn-adm-reader-open fn-adm-operator-fundedp
  fn-adm-priced-cfg fn-mm-gate-p fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open fn-own-find-conn fn-own-conns)))))

(defthm fn-adm-operator-open-preserves-bank-representation
  (implies (fn-adm-hh-representsp bank)
    (fn-adm-hh-representsp (fn-exp-at 2
      (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))))
 :hints (("Goal"
 :use (fn-adm-reader-open-preserves-identity-union
       (:instance fn-adm-hh-open-preserves-identity-union
          (id (fn-own-next-id (fn-ocfg-owner oc))) (physical nil)))
 :in-theory (e/d (fn-adm-operator-open fn-adm-operator-open-refusal fn-exp-at)
 (fn-adm-hh-representsp fn-adm-hh-open fn-adm-reader-open fn-adm-operator-fundedp
  fn-adm-priced-cfg fn-mm-gate-p fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open
  fn-own-find-conn fn-own-conns fn-adm-hh-count fn-adm-reader-count)))))

(defthm fn-adm-operator-close-preserves-bank-representation
  (implies (fn-adm-hh-representsp bank)
    (fn-adm-hh-representsp (fn-exp-at 0 (fn-adm-operator-close bank operator-id id))))
 :hints (("Goal" :in-theory (e/d (fn-adm-operator-close fn-exp-at)
 (fn-adm-hh-close fn-adm-hh-representsp)))))

(defthm fn-adm-operator-open-is-a-single-priced-admission
  (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))
        (held (nfix (fn-adm-hh-count bank))))
    (implies (equal (car r) :admit)
      (and (equal (fn-adm-admission-held r) (1+ held))
           (if (< held (fn-adm-reader-count configured capacity))
             (and (equal (fn-exp-at 6 r) operator-id)
                  (<= (fn-adm-admission-held r) (fn-adm-reader-count configured capacity)))
             (and (fn-adm-operator-slot-freep operator-id)
                  (equal (fn-exp-at 6 r) (fn-exp-at 4 r))
                  (fn-adm-operator-fundedp profile img cfg limit tot capacity)
                  (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (fn-adm-admission-held r) capacity) limit tot))))))
  :rule-classes nil
 :hints (("Goal"
 :use (fn-adm-reader-open-admits-below-held-reader-bound)
 :in-theory (e/d
 (fn-adm-operator-open fn-adm-operator-open-refusal fn-adm-admission-held
  fn-adm-hh-open fn-adm-hh-update fn-exp-at)
 (fn-adm-reader-open fn-adm-reader-count fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
 fn-adm-hh-put fn-adm-hh-drop fn-adm-hh-cached-count-is-the-union-cardinality
 fn-adm-operator-fundedp fn-adm-priced-cfg fn-mm-gate-p fn-own-next-id fn-ocfg-owner
 fn-ocar-ocfg-open fn-own-find-conn fn-own-conns)))))

(local (defthm m28-reader-open-tag-and-refusal-fields
 (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
  (and (member-eq (car r) '(:admit :refuse))
       (implies (equal (car r) :refuse)
        (and (equal (fn-exp-at 2 r) bank)
             (equal (fn-exp-at 3 r) (nfix (fn-adm-hh-count bank)))
             (equal (fn-exp-at 4 r) nil)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
  (fn-adm-reader-open fn-adm-held-open fn-adm-held-open-refusal fn-exp-at)
  (fn-adm-held-open-roomp fn-adm-hh-count fn-adm-hh-open fn-exp-admit-decision
   fn-ocar-exp-open fn-ocfg-open-peer fn-ocar-ocfg-open fn-exp-open-id
   fn-own-find-conn fn-ocfg-owner fn-own-conns fn-own-next-id
   fn-adm-hh-cached-count-is-the-union-cardinality))))))

(defthm fn-adm-operator-open-below-saturation-is-the-reader-open
  (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot))
        (q (fn-adm-reader-open oc acfg bank configured capacity)))
    (implies (< (nfix (fn-adm-hh-count bank)) (fn-adm-reader-count configured capacity))
      (and (equal (car r) (car q))
           (equal (fn-exp-at 1 r) (fn-exp-at 1 q))
           (equal (fn-exp-at 2 r) (fn-exp-at 2 q))
           (equal (fn-exp-at 3 r) (fn-exp-at 3 q))
           (equal (fn-exp-at 4 r) (fn-exp-at 4 q))
           (equal (fn-exp-at 6 r) operator-id))))
  :rule-classes nil
 :hints (("Goal" :use (m28-reader-open-tag-and-refusal-fields)
 :in-theory (e/d (fn-adm-operator-open fn-adm-operator-open-refusal fn-exp-at)
  (fn-adm-reader-open fn-adm-reader-count fn-adm-hh-count fn-adm-operator-fundedp
   fn-adm-priced-cfg fn-mm-gate-p fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open
   fn-own-find-conn fn-own-conns fn-adm-hh-cached-count-is-the-union-cardinality)))))

(defthm fn-adm-operator-open-admits-exactly-a-free-funded-slot
 (let* ((held (nfix (fn-adm-hh-count bank)))
        (id (fn-own-next-id (fn-ocfg-owner oc)))
        (opened (fn-ocar-ocfg-open oc acfg))
        (r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
  (equal (equal (car r) :admit)
   (if (< held (fn-adm-reader-count configured capacity))
     (equal (car (fn-adm-reader-open oc acfg bank configured capacity)) :admit)
     (and (fn-adm-operator-slot-freep operator-id)
          (equal (fn-mm-cfg-connections cfg) (nfix configured))
          (natp id) (not (fn-exp-lookup id (fn-adm-hh-rows bank)))
          (fn-adm-operator-fundedp profile img cfg limit tot capacity)
          (fn-mm-gate-p profile img (fn-adm-priced-cfg cfg (1+ held) capacity) limit tot)
          (equal (fn-own-next-id (fn-ocfg-owner (cdr opened))) (1+ id))
          (and (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner (cdr opened)))) t)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
 (fn-adm-operator-open fn-adm-operator-open-refusal fn-adm-operator-slot-freep fn-exp-at)
 (fn-adm-reader-open fn-adm-reader-count fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
  fn-adm-operator-fundedp fn-adm-priced-cfg fn-mm-gate-p fn-mm-cfg-connections
  fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open fn-own-find-conn fn-own-conns
  fn-adm-hh-cached-count-is-the-union-cardinality)))))

(defthm fn-adm-operator-refusal-is-named
 (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
  (implies (equal (car r) :refuse)
   (member-eq (fn-adm-operator-open-reason r)
              '(:operator-slot-held :operator-slot-memory :operator-owner-bound :operator-cfg-stale))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
 (fn-adm-operator-open fn-adm-operator-open-refusal fn-adm-operator-open-reason fn-exp-at)
 (fn-adm-reader-open fn-adm-reader-count fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
  fn-adm-operator-fundedp fn-adm-priced-cfg fn-mm-gate-p fn-mm-cfg-connections
  fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open fn-own-find-conn fn-own-conns
  fn-adm-hh-cached-count-is-the-union-cardinality)))))

(local (defthm m28-lookup-after-other-drop-by-definition
  (implies (not (equal key id))
   (equal (fn-exp-lookup key (fn-adm-hh-drop id rows)) (fn-exp-lookup key rows)))
  :hints (("Goal" :induct (fn-adm-hh-drop id rows)
                   :in-theory (enable fn-adm-hh-drop fn-exp-lookup)))))

(local (defthm m28-lookup-after-put-by-definition
  (equal (fn-exp-lookup key (fn-adm-hh-put id logical physical rows))
   (if (equal key id) (list id logical physical) (fn-exp-lookup key rows)))
  :hints (("Goal" :in-theory (enable fn-adm-hh-put fn-exp-lookup)))))

(local (defthm m28-other-row-of-update-by-definition
  (implies (not (equal key id))
   (equal (fn-exp-lookup key (fn-adm-hh-rows (fn-adm-hh-update bank id logical physical)))
          (fn-exp-lookup key (fn-adm-hh-rows bank))))
  :hints (("Goal" :in-theory (e/d
   (fn-adm-hh-update fn-adm-hh-rows fn-adm-hh-make)
   (fn-adm-hh-count fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop))))))

(local (defthm m28-row-of-natural-live-update-by-definition
 (implies (and (natp id) logical)
  (equal (fn-exp-lookup id (fn-adm-hh-rows (fn-adm-hh-update bank id logical physical)))
         (list id t (and physical t))))
 :hints (("Goal" :in-theory (e/d
  (fn-adm-hh-update fn-adm-hh-rows fn-adm-hh-make)
  (fn-adm-hh-count fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop))))))

(defthm fn-adm-operator-open-preserves-slot-representation
 (implies (fn-adm-operator-statep bank operator-id)
  (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
   (fn-adm-operator-statep (fn-exp-at 2 r) (fn-exp-at 6 r))))
 :hints (("Goal"
 :cases ((equal (fn-own-next-id (fn-ocfg-owner oc)) operator-id))
 :use (fn-adm-operator-open-preserves-bank-representation)
 :in-theory (e/d
  (fn-adm-operator-statep fn-adm-operator-open fn-adm-operator-open-refusal
   fn-adm-operator-slot-freep fn-adm-reader-open fn-adm-held-open fn-adm-held-open-roomp
   fn-adm-held-open-refusal fn-adm-hh-open fn-exp-at)
  (fn-adm-hh-representsp fn-adm-hh-update fn-adm-hh-count fn-adm-hh-rows
   fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop fn-adm-reader-count
   fn-adm-operator-fundedp fn-adm-priced-cfg fn-mm-gate-p fn-mm-cfg-connections
   fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open fn-own-find-conn fn-own-conns
   fn-ocar-exp-open fn-ocfg-open-peer fn-exp-open-id fn-exp-admit-decision
   fn-adm-hh-cached-count-is-the-union-cardinality)))))

(defthm fn-adm-operator-close-preserves-slot-representation
 (implies (fn-adm-operator-statep bank operator-id)
  (let ((r (fn-adm-operator-close bank operator-id id)))
   (fn-adm-operator-statep (fn-exp-at 0 r) (fn-exp-at 1 r))))
 :hints (("Goal"
 :use (fn-adm-operator-close-preserves-bank-representation)
 :in-theory (e/d (fn-adm-operator-close fn-adm-operator-statep fn-adm-hh-close fn-exp-at)
  (fn-adm-hh-representsp fn-adm-hh-update fn-adm-hh-count fn-adm-hh-rows
   fn-exp-lookup fn-adm-hh-put fn-adm-hh-drop
   fn-adm-hh-cached-count-is-the-union-cardinality)))))

(local (defthm m28-reader-open-has-a-natural-admitted-id
 (let ((r (fn-adm-reader-open oc acfg bank configured capacity)))
  (implies (equal (car r) :admit) (natp (fn-exp-at 4 r))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
  (fn-adm-reader-open fn-adm-held-open fn-adm-held-open-roomp fn-adm-held-open-refusal fn-exp-at)
  (fn-adm-reader-count fn-adm-hh-count fn-exp-lookup fn-adm-hh-rows fn-adm-hh-open
   fn-adm-hh-cached-count-is-the-union-cardinality fn-exp-admit-decision
   fn-ocar-exp-open fn-ocfg-open-peer fn-ocar-ocfg-open fn-exp-open-id
   fn-own-find-conn fn-ocfg-owner fn-own-conns fn-own-next-id)))))
)

(defthm fn-adm-operator-admitted-id-is-the-slot-id
 (let ((r (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img cfg limit tot)))
  (implies (equal (fn-adm-operator-open-word r) :admitted)
   (and (natp (fn-adm-operator-open-id r))
        (equal (fn-exp-at 6 r)
               (if (< (nfix (fn-adm-hh-count bank)) (fn-adm-reader-count configured capacity))
                 operator-id
                 (fn-adm-operator-open-id r))))))
 :rule-classes nil
 :hints (("Goal" :use (m28-reader-open-has-a-natural-admitted-id)
 :in-theory (e/d
  (fn-adm-operator-open fn-adm-operator-open-refusal fn-adm-operator-open-word
   fn-adm-operator-open-id fn-exp-at)
  (fn-adm-reader-open fn-adm-reader-count fn-adm-hh-count fn-adm-hh-rows fn-exp-lookup
   fn-adm-operator-fundedp fn-adm-priced-cfg fn-mm-gate-p fn-mm-cfg-connections
   fn-own-next-id fn-ocfg-owner fn-ocar-ocfg-open fn-own-find-conn fn-own-conns
   fn-adm-hh-cached-count-is-the-union-cardinality)))))

; Deferred served operator decision guard verification.
(verify-guards fn-adm-operator-open)


; Composition uses the operator admission summary above.
(local (defthm m28-operator-admission-composes
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg)))
(configured (fn-mm-cfg-connections run-cfg))
(capacity (fn-adm-installed-capacity profile img run-cfg limit tot))
(reader-count (fn-adm-reader-count configured capacity))
(operator (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img run-cfg limit tot)))
(implies (equal (car operator) :admit) (and (equal (fn-adm-admission-held operator) (1+ (nfix (fn-adm-hh-count bank)))) (or (and (<= (fn-adm-admission-held operator) reader-count) (equal (fn-exp-at 6 operator) operator-id)) (and (fn-adm-operator-slot-freep operator-id) (equal (fn-exp-at 6 operator) (fn-exp-at 4 operator)) (fn-adm-operator-fundedp profile img run-cfg limit tot capacity))) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held operator) capacity) limit tot))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-adm-operator-open-is-a-single-priced-admission
          (cfg (update-nth 10 nil (true-list-fix cfg)))
          (configured (fn-mm-cfg-connections (update-nth 10 nil (true-list-fix cfg))))
          (capacity (fn-adm-installed-capacity profile img (update-nth 10 nil (true-list-fix cfg)) limit tot)))
        (:instance m24-priced-installed-gate-by-definition
          (held (fn-adm-admission-held
            (fn-adm-operator-open oc acfg bank
              (fn-mm-cfg-connections (update-nth 10 nil (true-list-fix cfg)))
              (fn-adm-installed-capacity profile img (update-nth 10 nil (true-list-fix cfg)) limit tot)
              operator-id profile img (update-nth 10 nil (true-list-fix cfg)) limit tot)))))
  :in-theory (e/d (fn-adm-reader-count fn-adm-priced-connections nfix natp)
    (m24-priced-installed-gate-by-definition fn-adm-operator-fundedp fn-adm-operator-slot-freep fn-adm-cfg-at fn-adm-public-readers-cfg fn-adm-exposure-open fn-adm-peer-open fn-adm-reader-open fn-adm-transport-rearm
     fn-adm-operator-open fn-adm-admission-held fn-adm-installed-capacity fn-adm-capacity
     fn-mm-gate-p fn-adm-priced-cfg fn-adm-priced-connections fn-mm-cfg-connections
     fn-adm-hh-count fn-exp-at))))))
(defthm fn-adm-held-admissions-compose-with-installed-capacity
 (let* ((run-cfg (update-nth 10 nil (true-list-fix cfg))) (configured (fn-mm-cfg-connections run-cfg)) (capacity (fn-adm-installed-capacity profile img run-cfg limit tot)) (reader-count (fn-adm-reader-count configured capacity)) (exposure (fn-adm-exposure-open oc xs lim acfg peer address now bank configured capacity)) (peer-open (fn-adm-peer-open oc peer acfg bank configured capacity)) (rearm (fn-adm-transport-rearm kind oc xs lim acfg peer address now bank old-id configured capacity)) (reader (fn-adm-reader-open oc acfg bank configured capacity)) (operator (fn-adm-operator-open oc acfg bank configured capacity operator-id profile img run-cfg limit tot))) (and (implies (equal (car exposure) :admit) (and (<= (fn-exp-at 3 exposure) reader-count) (<= (fn-adm-admission-held exposure) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held exposure) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held exposure) capacity) limit tot))) (implies (equal (car peer-open) :admit) (and (<= (fn-exp-at 3 peer-open) reader-count) (<= (fn-adm-admission-held peer-open) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held peer-open) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held peer-open) capacity) limit tot))) (implies (equal (car rearm) :admit) (and (<= (fn-exp-at 3 rearm) reader-count) (<= (fn-adm-admission-held rearm) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held rearm) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held rearm) capacity) limit tot))) (implies (equal (car reader) :admit) (and (<= (fn-exp-at 3 reader) reader-count) (<= (fn-adm-admission-held reader) reader-count) (equal (fn-adm-priced-connections (fn-adm-admission-held reader) configured capacity) reader-count) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held reader) capacity) limit tot))) (implies (equal (car operator) :admit) (and (equal (fn-adm-admission-held operator) (1+ (nfix (fn-adm-hh-count bank)))) (or (and (<= (fn-adm-admission-held operator) reader-count) (equal (fn-exp-at 6 operator) operator-id)) (and (fn-adm-operator-slot-freep operator-id) (equal (fn-exp-at 6 operator) (fn-exp-at 4 operator)) (fn-adm-operator-fundedp profile img run-cfg limit tot capacity))) (fn-mm-gate-p profile img (fn-adm-priced-cfg run-cfg (fn-adm-admission-held operator) capacity) limit tot)))))
 :rule-classes nil
 :hints (("Goal" :use (m24-exposure-admission-composes m24-peer-admission-composes
 m24-rearm-admission-composes m24-reader-admission-composes m28-operator-admission-composes)
 :in-theory (theory 'minimal-theory))))
