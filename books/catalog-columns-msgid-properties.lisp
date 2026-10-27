; Canonical linear-probing index refinement, including full-key confirmation.
(in-package "ACL2")
(include-book "catalog-columns-number-properties")

(local (defthm fn-lbr11-msgid-probe-members
 (implies (member-equal i (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc))
  (and (natp i) (< i (fn-lbc-count fn-lbc))
       (equal (fn-lbc-msgid i fn-lbc) msgid)
       (equal (fn-lbc-word :msgid-hash i fn-lbc) hash)))
 :hints (("Goal" :induct (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lbc-msgid-probe member-equal natp zp)) '(floor mod))))))

(defthm fn-lbc-msgid-seqs-are-confirmed
 (implies (member-equal i (fn-lbc-msgid-seqs msgid fn-lbc))
  (and (natp i) (< i (fn-lbc-count fn-lbc))
       (equal (fn-lbc-msgid i fn-lbc) msgid)
       (equal (fn-lbc-word :msgid-hash i fn-lbc) (fn-lbc-msgid-hash msgid))))
 :hints (("Goal" :use ((:instance fn-lbr11-msgid-probe-members
  (hash (fn-lbc-msgid-hash msgid))
  (slot (mod (fn-lbc-msgid-hash msgid) (max 1 (fn-lbc-slot-count fn-lbc))))
  (fuel (fn-lbc-slot-count fn-lbc))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-msgid-seqs)))))

(defthm fn-lbc-msgid-probe-is-proper
 (true-listp (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc))
 :hints (("Goal" :induct (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lbc-msgid-probe)) '(floor mod)))))

(defthm fn-lbc-msgid-seqs-are-proper
 (true-listp (fn-lbc-msgid-seqs msgid fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-msgid-seqs fn-lbc-msgid-probe-is-proper)))))

(local (defun fn-lbs-rotate (start cells)
 (declare (xargs :guard t :verify-guards nil))
 (append (nthcdr (nfix start) cells) (take (nfix start) cells))))

(local (defun fn-lbs-matchp (word msgid rows)
 (declare (xargs :guard t :verify-guards nil))
 (and (posp word) (<= word (len rows))
      (equal (fn-record-msgid (nth (- word 1) rows)) msgid))))

(local (defun fn-lbs-all-matches (cells msgid rows)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp cells)
  (if (fn-lbs-matchp (car cells) msgid rows)
   (cons (- (car cells) 1) (fn-lbs-all-matches (cdr cells) msgid rows))
   (fn-lbs-all-matches (cdr cells) msgid rows)) nil)))

(local (defun fn-lbs-scan (cells msgid rows)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (consp cells) (not (zp (car cells))))
  (if (fn-lbs-matchp (car cells) msgid rows)
   (cons (- (car cells) 1) (fn-lbs-scan (cdr cells) msgid rows))
   (fn-lbs-scan (cdr cells) msgid rows)) nil)))

(local (defun fn-lbs-layoutp (cells msgid rows last empty-seen)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp cells)
  (and (implies (fn-lbs-matchp (car cells) msgid rows)
                (and (not empty-seen) (< (nfix last) (car cells))))
       (fn-lbs-layoutp (cdr cells) msgid rows
        (if (fn-lbs-matchp (car cells) msgid rows) (car cells) last)
        (or empty-seen (zp (car cells))))) t)))

(local (defun fn-lbs-increasingp (indices lower)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp indices)
  (and (natp (car indices)) (<= lower (car indices))
       (fn-lbs-increasingp (cdr indices) (+ 1 (car indices)))) t)))

(local (defun fn-lbs-fill-first (word fuel cells)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (and (consp cells) (not (zp fuel)))
  (if (equal (car cells) 0) (cons word (cdr cells))
   (cons (car cells) (fn-lbs-fill-first word (- fuel 1) (cdr cells)))) cells)))

(local (defun fn-lbs-extends-by (before after word)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp before)
  (and (consp after)
       (or (equal (car before) (car after))
           (and (equal (car before) 0) (equal (car after) word)))
       (fn-lbs-extends-by (cdr before) (cdr after) word)) (equal after before))))

(local (defun fn-lbs-bounded-wordsp (cells bound)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp cells)
  (and (natp (car cells)) (<= (car cells) bound) (fn-lbs-bounded-wordsp (cdr cells) bound)) t)))

(local (defun fn-lbs-nonzero-count (cells)
 (declare (xargs :guard t))
 (if (consp cells) (+ (if (equal (car cells) 0) 0 1) (fn-lbs-nonzero-count (cdr cells))) 0)))

(local (defun fn-lbs-coveredp (bound cells)
 (declare (xargs :guard t :verify-guards nil :measure (nfix bound)))
 (if (zp bound) t
  (and (member-equal bound cells) (fn-lbs-coveredp (- bound 1) cells)))))

(local (defthm fn-lbs-after-empty-no-matches
 (implies (fn-lbs-layoutp cells msgid rows last t)
  (equal (fn-lbs-all-matches cells msgid rows) nil))
 :hints (("Goal" :induct (fn-lbs-layoutp cells msgid rows last t)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-layoutp fn-lbs-all-matches))))))

(local (defthm fn-lbs-scan-is-all-matches
 (implies (fn-lbs-layoutp cells msgid rows last nil)
  (equal (fn-lbs-scan cells msgid rows) (fn-lbs-all-matches cells msgid rows)))
 :hints (("Goal" :induct (fn-lbs-layoutp cells msgid rows last nil)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbs-layoutp fn-lbs-all-matches fn-lbs-scan fn-lbs-after-empty-no-matches fn-lbs-matchp posp natp zp))))))

(local (defthm fn-lbs-layout-implies-increasing
 (implies (and (natp last) (fn-lbs-layoutp cells msgid rows last empty-seen))
  (fn-lbs-increasingp (fn-lbs-all-matches cells msgid rows) last))
 :hints (("Goal" :induct (fn-lbs-layoutp cells msgid rows last empty-seen)
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbs-layoutp fn-lbs-all-matches fn-lbs-increasingp fn-lbs-matchp natp posp nfix))))))

(local (encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-lbs-next-slot-natural
 (natp (mod (+ 1 (nfix slot)) (max 1 (len table)))))
(defthm fn-lbs-next-slot-below-capacity
 (< (mod (+ 1 (nfix slot)) (max 1 (len table))) (max 1 (len table)))
 :rule-classes :linear)))

(local (defthm fn-lbs-nth-preserved-by-zero-fill
 (implies (and (natp slot) (natp j) (not (equal (nth j table) 0)))
  (equal (nth j (fn-lbc-canonical-slot-insert ordinal slot fuel table)) (nth j table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert ordinal slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lbc-canonical-slot-insert nth-update-nth natp nfix)) '(floor mod)))
 ("Subgoal *1/3" :use fn-lbs-next-slot-natural))))

(local (defthm fn-lbs-member-update-zero
 (implies (and (natp j) (equal (nth j table) 0) (member-equal word table) (not (equal word 0)))
  (member-equal word (update-nth j value table)))
 :hints (("Goal" :induct (nth j table)
 :in-theory (union-theories (theory 'ground-zero) '(nth update-nth member-equal natp zp))))))

(local (defthm fn-lbs-member-preserved-by-zero-fill
 (implies (and (natp slot) (member-equal word table) (not (equal word 0)))
  (member-equal word (fn-lbc-canonical-slot-insert ordinal slot fuel table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert ordinal slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
  '(fn-lbc-canonical-slot-insert fn-lbs-member-update-zero natp nfix)) '(floor mod)))
 ("Subgoal *1/3" :use fn-lbs-next-slot-natural))))

(local (defthm fn-lbs-extends-reflexive
 (fn-lbs-extends-by cells cells word)
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-extends-by))))))

(local (defthm fn-lbs-update-zero-extends
 (implies (and (natp j) (< j (len table)) (equal (nth j table) 0))
  (fn-lbs-extends-by table (update-nth j word table) word))
 :hints (("Goal" :induct (nth j table) :in-theory (union-theories (theory 'ground-zero) '(nth update-nth fn-lbs-extends-by fn-lbs-extends-reflexive natp zp))))))

(local (defthm fn-lbs-zero-fill-extends
 (implies (and (natp slot) (< slot (len table)))
  (fn-lbs-extends-by table (fn-lbc-canonical-slot-insert word slot fuel table) word))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert word slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-canonical-slot-insert fn-lbs-update-zero-extends fn-lbs-extends-reflexive natp nfix)) '(floor mod)))
 ("Subgoal *1/3" :use (fn-lbs-next-slot-natural fn-lbs-next-slot-below-capacity)))))

(local (defthm fn-lbs-extends-preserves-length
 (implies (fn-lbs-extends-by before after word) (equal (len after) (len before)))
 :hints (("Goal" :induct (fn-lbs-extends-by before after word) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-extends-by))))))

(local (defthm fn-lbs-zero-fill-length
 (implies (and (natp slot) (< slot (len table)))
 (equal (len (fn-lbc-canonical-slot-insert word slot fuel table)) (len table)))
 :hints (("Goal" :use ((:instance fn-lbs-extends-preserves-length (before table) (after (fn-lbc-canonical-slot-insert word slot fuel table))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-zero-fill-extends))))))

(local (defun fn-lbs-transfer-induct (before after msgid rows last old-empty new-empty)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp before)
  (fn-lbs-transfer-induct (cdr before) (cdr after) msgid rows
   (if (fn-lbs-matchp (car before) msgid rows) (car before) last)
   (or old-empty (zp (car before))) (or new-empty (zp (car after))))
  (list after msgid rows last old-empty new-empty))))

(local (defthm fn-lbs-extends-preserves-layout-general
 (implies (and (fn-lbs-extends-by before after word) (not (fn-lbs-matchp word msgid rows))
               (fn-lbs-layoutp before msgid rows last old-empty)
               (implies new-empty old-empty))
 (fn-lbs-layoutp after msgid rows last new-empty))
 :hints (("Goal" :induct (fn-lbs-transfer-induct before after msgid rows last old-empty new-empty)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-transfer-induct fn-lbs-extends-by fn-lbs-layoutp fn-lbs-matchp posp natp zp))))))

(local (defthm fn-lbs-extends-no-new-matches
 (implies (and (fn-lbs-extends-by before after word) (not (fn-lbs-matchp word msgid rows))
               (fn-lbs-layoutp before msgid rows last empty))
 (fn-lbs-layoutp after msgid rows last empty))
 :hints (("Goal" :use ((:instance fn-lbs-extends-preserves-layout-general (old-empty empty) (new-empty empty)))
 :in-theory (theory 'ground-zero)))))

(local (defun fn-lbs-pair-index-induct (n before after)
 (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
 (if (zp n) (list before after)
 (fn-lbs-pair-index-induct (- n 1) (cdr before) (cdr after)))))

(local (defthm fn-lbs-extends-nthcdr
 (implies (fn-lbs-extends-by before after word)
 (fn-lbs-extends-by (nthcdr n before) (nthcdr n after) word))
 :hints (("Goal" :induct (fn-lbs-pair-index-induct n before after) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-pair-index-induct fn-lbs-extends-by nthcdr))))))

(local (defthm fn-lbs-extends-take
 (implies (fn-lbs-extends-by before after word)
 (fn-lbs-extends-by (take n before) (take n after) word))
 :hints (("Goal" :induct (fn-lbs-pair-index-induct n before after) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-pair-index-induct fn-lbs-extends-by take))))))

(local (defthm fn-lbs-extends-append
 (implies (and (true-listp before) (fn-lbs-extends-by before after word) (fn-lbs-extends-by tail tail2 word))
 (fn-lbs-extends-by (append before tail) (append after tail2) word))
 :hints (("Goal" :induct (fn-lbs-extends-by before after word) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-extends-by binary-append true-listp))))))

(local (defthm fn-lbs-proper-nthcdr
 (implies (true-listp cells) (true-listp (nthcdr n cells)))
 :hints (("Goal" :induct (nthcdr n cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr true-listp))))))

(local (defthm fn-lbs-extends-rotate
 (implies (and (true-listp before) (fn-lbs-extends-by before after word))
 (fn-lbs-extends-by (fn-lbs-rotate start before) (fn-lbs-rotate start after) word))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-extends-append fn-lbs-extends-take fn-lbs-extends-nthcdr fn-lbs-proper-nthcdr))))))

(local (defthm fn-lbs-nthcdr-nonempty
 (implies (and (natp n) (< n (len cells))) (consp (nthcdr n cells)))
 :hints (("Goal" :induct (nthcdr n cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr natp zp))))))

(local (defthm fn-lbs-nthcdr-car
 (equal (car (nthcdr n cells)) (nth n cells))
 :hints (("Goal" :induct (nth n cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr nth))))))

(local (defthm fn-lbs-car-append-nonempty
 (implies (consp a) (equal (car (append a b)) (car a)))
 :hints (("Goal" :in-theory (enable binary-append)))))

(local (defthm fn-lbs-rotate-head
 (implies (and (natp start) (< start (len cells)))
 (equal (car (fn-lbs-rotate start cells)) (nth start cells)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbs-nthcdr-nonempty (n start)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-nthcdr-car fn-lbs-car-append-nonempty natp nfix))))))

(local (defthm fn-lbs-take-before-update
 (implies (natp n) (equal (take n (update-nth n word cells)) (take n cells)))
 :hints (("Goal" :induct (nth n cells) :in-theory (union-theories (theory 'ground-zero) '(nth take update-nth natp zp))))))

(local (defthm fn-lbs-nthcdr-at-update
 (implies (natp n) (equal (nthcdr n (update-nth n word cells)) (cons word (cdr (nthcdr n cells)))))
 :hints (("Goal" :induct (nth n cells) :in-theory (union-theories (theory 'ground-zero) '(nth nthcdr update-nth natp zp))))))

(local (defthm fn-lbs-cdr-append-nonempty
 (implies (consp a) (equal (cdr (append a b)) (append (cdr a) b)))
 :hints (("Goal" :in-theory (enable binary-append)))))

(local (defthm fn-lbs-rotate-update-head
 (implies (and (natp start) (< start (len cells)))
 (equal (fn-lbs-rotate start (update-nth start word cells))
        (cons word (cdr (fn-lbs-rotate start cells)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbs-nthcdr-nonempty (n start)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-take-before-update fn-lbs-nthcdr-at-update fn-lbs-cdr-append-nonempty binary-append natp nfix))))))

(local (defthm fn-lbs-take-at-length-append
 (implies (true-listp a) (equal (take (len a) (append a b)) a))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(take binary-append true-listp))))))

(local (defthm fn-lbs-append-associative
 (equal (append (append a b) c) (append a (append b c)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbs-proper-take
 (true-listp (take n cells))
 :hints (("Goal" :induct (take n cells) :in-theory (union-theories (theory 'ground-zero) '(take true-listp))))))

(local (defthm fn-lbs-take-successor
 (implies (natp n) (equal (take (+ 1 n) cells) (append (take n cells) (list (nth n cells)))))
 :hints (("Goal" :induct (nth n cells) :in-theory (union-theories (theory 'ground-zero) '(take nth binary-append natp zp))))))

(local (defthm fn-lbs-nthcdr-successor
 (implies (natp n) (equal (nthcdr (+ 1 n) cells) (cdr (nthcdr n cells))))
 :hints (("Goal" :induct (nth n cells) :in-theory (union-theories (theory 'ground-zero) '(nth nthcdr natp zp))))))

(local (defthm fn-lbs-rotate-successor
 (implies (and (natp start) (< start (len cells)))
 (equal (fn-lbs-rotate (+ 1 start) cells)
        (append (cdr (fn-lbs-rotate start cells)) (list (nth start cells)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbs-nthcdr-nonempty (n start)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbs-rotate fn-lbs-nthcdr-successor fn-lbs-take-successor fn-lbs-nthcdr-car fn-lbs-cdr-append-nonempty fn-lbs-append-associative natp nfix))))))

(local (defthm fn-lbs-take-len-proper
 (implies (true-listp cells) (equal (take (len cells) cells) cells))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(take true-listp zp))))))

(local (defthm fn-lbs-nthcdr-len
 (implies (true-listp cells) (equal (nthcdr (len cells) cells) nil))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr true-listp zp))))))

(local (defthm fn-lbs-rotate-end
 (implies (true-listp cells) (equal (fn-lbs-rotate (len cells) cells) cells))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-take-len-proper fn-lbs-nthcdr-len nfix))))))

(local (defthm fn-lbs-rotate-zero
 (implies (true-listp cells) (equal (fn-lbs-rotate 0 cells) cells))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate nthcdr take binary-append true-listp))))))

(local (encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-lbs-mod-below
 (implies (and (natp x) (posp y) (< x y)) (equal (mod x y) x)))
(defthm fn-lbs-mod-self
 (implies (posp y) (equal (mod y y) 0)))))

(local (defthm fn-lbs-next-slot-cases
 (implies (and (natp slot) (< slot (len table)))
 (equal (mod (+ 1 slot) (max 1 (len table)))
        (if (< (+ 1 slot) (len table)) (+ 1 slot) 0)))
 :hints (("Goal" :do-not-induct t :cases ((equal (+ 1 slot) (len table)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbs-mod-below fn-lbs-mod-self natp posp max)) '(floor mod))))))

(local (defthm fn-lbs-length-take
 (equal (len (take n cells)) (nfix n))
 :hints (("Goal" :induct (take n cells) :in-theory (union-theories (theory 'ground-zero) '(take nfix zp))))))

(local (defthm fn-lbs-length-nthcdr
 (equal (len (nthcdr n cells)) (nfix (- (len cells) (nfix n))))
 :hints (("Goal" :induct (nthcdr n cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr nfix zp))))))

(local (defthm fn-lbs-length-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append))))))

(local (defthm fn-lbs-proper-append
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append true-listp))))))

(local (defthm fn-lbs-rotate-length
 (implies (and (natp start) (<= start (len cells)))
 (equal (len (fn-lbs-rotate start cells)) (len cells)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-length-take fn-lbs-length-nthcdr fn-lbs-length-append natp nfix))))))

(local (defthm fn-lbs-rotate-proper
 (true-listp (fn-lbs-rotate start cells))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-proper-append fn-lbs-proper-take))))))

(local (defthm fn-lbs-rotate-cyclic-successor
 (implies (and (true-listp cells) (natp start) (< start (len cells)))
 (equal (fn-lbs-rotate (mod (+ 1 start) (max 1 (len cells))) cells)
        (append (cdr (fn-lbs-rotate start cells)) (list (nth start cells)))))
 :hints (("Goal" :do-not-induct t :use (fn-lbs-rotate-successor (:instance fn-lbs-next-slot-cases (slot start) (table cells)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-rotate-end fn-lbs-rotate-zero natp)) '(mod floor))))))

(local (defthm fn-lbs-rotate-cdr-step
 (implies (and (true-listp cells) (natp start) (< start (len cells)))
 (equal (take (- (len cells) 1) (fn-lbs-rotate (mod (+ 1 start) (max 1 (len cells))) cells))
        (cdr (fn-lbs-rotate start cells))))
 :hints (("Goal" :do-not-induct t :use (fn-lbs-rotate-length fn-lbs-rotate-proper fn-lbs-rotate-cyclic-successor)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-take-at-length-append natp true-listp)) '(mod floor))))))

(local (defthm fn-lbs-extends-preserves-proper
 (implies (and (true-listp before) (fn-lbs-extends-by before after word)) (true-listp after))
 :hints (("Goal" :induct (fn-lbs-extends-by before after word) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-extends-by true-listp))))))

(local (defthm fn-lbs-zero-fill-proper
 (implies (and (true-listp table) (natp slot) (< slot (len table)))
 (true-listp (fn-lbc-canonical-slot-insert word slot fuel table)))
 :hints (("Goal" :use ((:instance fn-lbs-extends-preserves-proper (before table) (after (fn-lbc-canonical-slot-insert word slot fuel table))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-zero-fill-extends))))))

(local (defun fn-lbs-prefix-fill-induct (n fuel cells)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (and (consp cells) (not (zp fuel)) (not (equal (car cells) 0)))
 (fn-lbs-prefix-fill-induct (- n 1) (- fuel 1) (cdr cells)) (list n fuel cells))))

(local (defthm fn-lbs-take-fill-first
 (implies (and (natp n) (natp fuel) (<= fuel n) (<= n (len cells)))
 (equal (take n (fn-lbs-fill-first word fuel cells))
        (fn-lbs-fill-first word fuel (take n cells))))
 :hints (("Goal" :induct (fn-lbs-prefix-fill-induct n fuel cells)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-prefix-fill-induct fn-lbs-fill-first take natp zp))))))

(local (defthm fn-lbs-fill-first-fuel-zero
 (implies (zp fuel) (equal (fn-lbs-fill-first word fuel cells) cells))
 :hints (("Goal" :in-theory (enable fn-lbs-fill-first)))))

(local (defthm fn-lbs-rotate-nonempty
 (implies (and (natp start) (< start (len cells))) (consp (fn-lbs-rotate start cells)))
 :hints (("Goal" :do-not-induct t :use (fn-lbs-rotate-length)
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbs-occupied-rotation-reconstruct
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (not (equal (nth slot table) 0)))
 (equal (fn-lbs-rotate slot (fn-lbc-canonical-slot-insert word slot fuel table))
 (cons (nth slot table)
  (take (- (len table) 1)
   (fn-lbs-rotate (mod (+ 1 slot) (max 1 (len table)))
     (fn-lbc-canonical-slot-insert word slot fuel table))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-rotate-head (start slot) (cells (fn-lbc-canonical-slot-insert word slot fuel table)))
       (:instance fn-lbs-rotate-cdr-step (start slot) (cells (fn-lbc-canonical-slot-insert word slot fuel table)))
       (:instance fn-lbs-rotate-nonempty (start slot) (cells (fn-lbc-canonical-slot-insert word slot fuel table)))
       (:instance fn-lbs-nth-preserved-by-zero-fill (ordinal word) (j slot)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-zero-fill-length fn-lbs-zero-fill-proper natp)) '(mod floor))))))

(local (defthm fn-lbs-canonical-insert-is-rotated-fill
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (natp fuel) (<= fuel (len table)))
  (equal (fn-lbs-rotate slot (fn-lbc-canonical-slot-insert word slot fuel table))
         (fn-lbs-fill-first word fuel (fn-lbs-rotate slot table))))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert word slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slot-insert fn-lbs-fill-first fn-lbs-rotate-update-head
 fn-lbs-take-fill-first fn-lbs-rotate-length natp nfix zp)) '(floor mod)))
 ("Subgoal *1/3" :use (fn-lbs-next-slot-natural fn-lbs-next-slot-below-capacity
 fn-lbs-occupied-rotation-reconstruct
 (:instance fn-lbs-rotate-head (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table))
 (:instance fn-lbs-rotate-cdr-step (start slot) (cells table))))
 ("Subgoal *1/2" :use ((:instance fn-lbs-rotate-head (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table)))))))

(local (defthm fn-lbs-no-matches-layout
 (implies (equal (fn-lbs-all-matches cells msgid rows) nil)
  (fn-lbs-layoutp cells msgid rows last empty))
 :hints (("Goal" :induct (fn-lbs-layoutp cells msgid rows last empty)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-layoutp fn-lbs-all-matches))))))

(local (defun fn-lbs-matching-fill-induct (word fuel cells msgid rows last)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (and (consp cells) (not (zp fuel)) (not (equal (car cells) 0)))
 (fn-lbs-matching-fill-induct word (- fuel 1) (cdr cells) msgid rows
 (if (fn-lbs-matchp (car cells) msgid rows) (car cells) last))
 (list word fuel cells msgid rows last))))

(local (defthm fn-lbs-matching-fill-preserves-layout
 (implies (and (posp word) (natp last) (< last word)
 (fn-lbs-matchp word msgid rows)
 (fn-lbs-bounded-wordsp cells (- word 1))
 (fn-lbs-layoutp cells msgid rows last nil))
 (fn-lbs-layoutp (fn-lbs-fill-first word fuel cells) msgid rows last nil))
 :hints (("Goal" :induct (fn-lbs-matching-fill-induct word fuel cells msgid rows last)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbs-matching-fill-induct fn-lbs-fill-first fn-lbs-layoutp fn-lbs-bounded-wordsp
 fn-lbs-after-empty-no-matches fn-lbs-no-matches-layout posp natp zp nfix))))))

(local (defthm fn-lbs-bounded-monotone
 (implies (and (fn-lbs-bounded-wordsp cells old) (<= old new)) (fn-lbs-bounded-wordsp cells new))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-bounded-wordsp))))))

(local (defthm fn-lbs-extends-bounded
 (implies (and (fn-lbs-extends-by before after word) (fn-lbs-bounded-wordsp before bound) (natp word) (<= word bound))
 (fn-lbs-bounded-wordsp after bound))
 :hints (("Goal" :induct (fn-lbs-extends-by before after word) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-extends-by fn-lbs-bounded-wordsp))))))

(local (defthm fn-lbs-bounded-nthcdr
 (implies (fn-lbs-bounded-wordsp cells bound) (fn-lbs-bounded-wordsp (nthcdr n cells) bound))
 :hints (("Goal" :induct (nthcdr n cells) :in-theory (union-theories (theory 'ground-zero) '(nthcdr fn-lbs-bounded-wordsp))))))

(local (defthm fn-lbs-bounded-take
 (implies (and (natp n) (<= n (len cells)) (fn-lbs-bounded-wordsp cells bound)) (fn-lbs-bounded-wordsp (take n cells) bound))
 :hints (("Goal" :induct (take n cells) :in-theory (union-theories (theory 'ground-zero) '(take fn-lbs-bounded-wordsp natp zp))))))

(local (defthm fn-lbs-bounded-append
 (implies (and (fn-lbs-bounded-wordsp a bound) (fn-lbs-bounded-wordsp b bound)) (fn-lbs-bounded-wordsp (append a b) bound))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append fn-lbs-bounded-wordsp))))))

(local (defthm fn-lbs-bounded-rotate
 (implies (and (natp start) (<= start (len cells)) (fn-lbs-bounded-wordsp cells bound))
 (fn-lbs-bounded-wordsp (fn-lbs-rotate start cells) bound))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-bounded-append fn-lbs-bounded-nthcdr fn-lbs-bounded-take natp nfix))))))

(local (defthm fn-lbs-count-bound
 (<= (fn-lbs-nonzero-count cells) (len cells)) :rule-classes :linear
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-nonzero-count))))))

(local (defthm fn-lbs-count-room-has-zero
 (implies (< (fn-lbs-nonzero-count cells) (len cells)) (member-equal 0 cells))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-nonzero-count member-equal fn-lbs-count-bound))))))

(local (defthm fn-lbs-count-update-zero
 (implies (and (natp j) (< j (len cells)) (equal (nth j cells) 0))
 (<= (fn-lbs-nonzero-count (update-nth j word cells)) (+ 1 (fn-lbs-nonzero-count cells))))
 :hints (("Goal" :induct (nth j cells) :in-theory (union-theories (theory 'ground-zero) '(nth update-nth fn-lbs-nonzero-count natp zp))))))

(local (defthm fn-lbs-count-canonical-insert
 (implies (and (natp slot) (< slot (len table)))
 (<= (fn-lbs-nonzero-count (fn-lbc-canonical-slot-insert word slot fuel table)) (+ 1 (fn-lbs-nonzero-count table))))
 :hints (("Goal" :induct (fn-lbc-canonical-slot-insert word slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-canonical-slot-insert fn-lbs-count-update-zero natp nfix)) '(floor mod)))
 ("Subgoal *1/3" :use (fn-lbs-next-slot-natural fn-lbs-next-slot-below-capacity)))))

(local (defthm fn-lbs-member-append
 (iff (member-equal word (append a b)) (or (member-equal word a) (member-equal word b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(binary-append member-equal))))))

(local (defthm fn-lbs-take-nthcdr-split
 (implies (and (true-listp cells) (natp start) (<= start (len cells)))
 (equal (append (take start cells) (nthcdr start cells)) cells))
 :hints (("Goal" :induct (nth start cells) :in-theory (union-theories (theory 'ground-zero) '(take nthcdr nth binary-append true-listp natp zp))))))

(local (defthm fn-lbs-rotate-members
 (implies (and (true-listp cells) (natp start) (<= start (len cells)))
 (iff (member-equal word (fn-lbs-rotate start cells)) (member-equal word cells)))
 :hints (("Goal" :do-not-induct t :use (fn-lbs-take-nthcdr-split
 (:instance fn-lbs-member-append (a (take start cells)) (b (nthcdr start cells))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-rotate fn-lbs-member-append natp nfix))))))

(local (defthm fn-lbs-fill-finds
 (implies (and (natp fuel) (<= (len cells) fuel) (member-equal 0 cells))
 (member-equal word (fn-lbs-fill-first word fuel cells)))
 :hints (("Goal" :induct (fn-lbs-fill-first word fuel cells)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-fill-first member-equal natp zp))))))

(local (defthm fn-lbs-canonical-insert-finds
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (member-equal 0 table))
 (member-equal word (fn-lbc-canonical-slot-insert word slot (len table) table)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-fill-finds (cells (fn-lbs-rotate slot table)) (fuel (len table)))
 (:instance fn-lbs-rotate-members (start slot) (cells (fn-lbc-canonical-slot-insert word slot (len table) table))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-canonical-insert-is-rotated-fill fn-lbs-rotate-members fn-lbs-rotate-length fn-lbs-zero-fill-length fn-lbs-zero-fill-proper))))))

(local (defthm fn-lbs-hash-octets-natural
 (natp (fn-lbc-msgid-hash-octets bytes hash))
 :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-lbc-msgid-hash-octets bytes hash)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-msgid-hash-octets nfix natp)) '(mod floor))))))

(local (defthm fn-lbs-hash-natural
 (natp (fn-lbc-msgid-hash msgid)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-msgid-hash fn-lbs-hash-octets-natural))))))

(local (encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-lbs-mod-natural
 (implies (and (natp x) (posp y)) (natp (mod x y))) :rule-classes :type-prescription)
(defthm fn-lbs-mod-positive-below
 (implies (and (natp x) (posp y)) (< (mod x y) y)) :rule-classes :linear)))

(local (defthm fn-lbs-slot-hash-natural
 (natp (mod (fn-lbc-msgid-hash msgid) (max 1 (len table))))
 :hints (("Goal" :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbs-hash-natural fn-lbs-mod-natural natp posp)) '(mod floor))))))

(local (defthm fn-lbs-insert-preserves-query-layout
 (implies (and (true-listp table) (natp slot) (< slot (len table))
 (natp query-slot) (< query-slot (len table)) (posp word)
 (fn-lbs-bounded-wordsp table (- word 1))
 (fn-lbs-layoutp (fn-lbs-rotate query-slot table) msgid rows 0 nil)
 (implies (fn-lbs-matchp word msgid rows) (equal slot query-slot)))
 (fn-lbs-layoutp (fn-lbs-rotate query-slot (fn-lbc-canonical-slot-insert word slot (len table) table)) msgid rows 0 nil))
 :hints (("Goal" :do-not-induct t :cases ((fn-lbs-matchp word msgid rows))
 :use ((:instance fn-lbs-extends-no-new-matches
  (before (fn-lbs-rotate query-slot table))
  (after (fn-lbs-rotate query-slot (fn-lbc-canonical-slot-insert word slot (len table) table)))
  (last 0) (empty nil))
  (:instance fn-lbs-extends-rotate (before table) (after (fn-lbc-canonical-slot-insert word slot (len table) table)) (start query-slot))
  (:instance fn-lbs-zero-fill-extends (fuel (len table)))
  (:instance fn-lbs-matching-fill-preserves-layout (cells (fn-lbs-rotate query-slot table)) (last 0) (fuel (len table))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbs-canonical-insert-is-rotated-fill fn-lbs-bounded-rotate posp natp))))))

(local (defthm fn-lbs-covered-zero-fill
 (implies (and (natp slot) (fn-lbs-coveredp i table))
 (fn-lbs-coveredp i (fn-lbc-canonical-slot-insert word slot fuel table)))
 :hints (("Goal" :induct (fn-lbs-coveredp i table)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-coveredp fn-lbs-member-preserved-by-zero-fill zp))))))

(local (defthm fn-lbs-covered-next-insert
 (implies (and (true-listp table) (natp i) (natp slot) (< slot (len table))
 (fn-lbs-coveredp i table) (< (fn-lbs-nonzero-count table) (len table)))
 (fn-lbs-coveredp (+ 1 i) (fn-lbc-canonical-slot-insert (+ 1 i) slot (len table) table)))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-coveredp fn-lbs-covered-zero-fill fn-lbs-count-room-has-zero fn-lbs-canonical-insert-finds natp zp))))))

(local (defthm fn-lbs-nonempty-length-positive
 (implies (consp cells) (< 0 (len cells))) :rule-classes :linear
 :hints (("Goal" :in-theory (enable len)))))

(local (defthm fn-lbs-slot-hash-below
 (implies (consp table) (< (mod (fn-lbc-msgid-hash msgid) (max 1 (len table))) (len table)))
 :rule-classes :linear
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbs-mod-positive-below (x (fn-lbc-msgid-hash msgid)) (y (max 1 (len table)))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbs-hash-natural fn-lbs-nonempty-length-positive natp posp)) '(mod floor))))))

(local (defthm fn-lbs-insert-next-bounded
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (natp i) (fn-lbs-bounded-wordsp table i))
 (fn-lbs-bounded-wordsp (fn-lbc-canonical-slot-insert (+ 1 i) slot (len table) table) (+ 1 i)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-extends-bounded (before table) (after (fn-lbc-canonical-slot-insert (+ 1 i) slot (len table) table)) (word (+ 1 i)) (bound (+ 1 i)))
       (:instance fn-lbs-bounded-monotone (cells table) (old i) (new (+ 1 i))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-zero-fill-extends natp))))))

(local (defthm fn-lbs-zero-fill-nonempty
 (implies (and (natp slot) (< slot (len table)))
 (consp (fn-lbc-canonical-slot-insert word slot fuel table)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :do-not-induct t :use (fn-lbs-zero-fill-length)
 :in-theory (union-theories (theory 'ground-zero) '(len natp))))))

(local (defthm fn-lbs-slots-from-length
 (implies (and (consp table) (true-listp table))
 (equal (len (fn-lbc-canonical-slots-from rest i table)) (len table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below posp fn-lbs-slot-hash-natural fn-lbs-slot-hash-below fn-lbs-nonempty-length-positive natp)) '(mod floor))))))

(local (defthm fn-lbs-slots-from-proper
 (implies (and (consp table) (true-listp table))
 (true-listp (fn-lbc-canonical-slots-from rest i table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below posp fn-lbs-slot-hash-natural fn-lbs-slot-hash-below fn-lbs-nonempty-length-positive natp)) '(mod floor))))))

(local (defthm fn-lbs-slots-from-bounded
 (implies (and (consp table) (true-listp table) (natp i) (fn-lbs-bounded-wordsp table i))
 (fn-lbs-bounded-wordsp (fn-lbc-canonical-slots-from rest i table) (+ i (len rest))))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-insert-next-bounded fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below posp fn-lbs-slot-hash-natural fn-lbs-slot-hash-below fn-lbs-nonempty-length-positive natp nfix len)) '(mod floor))))))

(local (defthm fn-lbs-count-insert-linear
 (implies (and (natp slot) (< slot (len table)))
 (<= (fn-lbs-nonzero-count (fn-lbc-canonical-slot-insert word slot fuel table)) (+ 1 (fn-lbs-nonzero-count table))))
 :rule-classes :linear
 :hints (("Goal" :use (fn-lbs-count-canonical-insert) :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbs-slots-from-count
 (implies (and (consp table) (true-listp table) (natp i) (<= (fn-lbs-nonzero-count table) i))
 (<= (fn-lbs-nonzero-count (fn-lbc-canonical-slots-from rest i table)) (+ i (len rest))))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-count-insert-linear fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below posp fn-lbs-slot-hash-natural fn-lbs-slot-hash-below fn-lbs-nonempty-length-positive natp nfix len)) '(mod floor))))))

(local (defthm fn-lbs-slots-from-covered
 (implies (and (consp table) (true-listp table) (natp i) (<= (fn-lbs-nonzero-count table) i)
              (fn-lbs-coveredp i table) (< (+ i (len rest)) (len table)))
 (fn-lbs-coveredp (+ i (len rest)) (fn-lbc-canonical-slots-from rest i table)))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-covered-next-insert fn-lbs-count-insert-linear fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below posp fn-lbs-slot-hash-natural fn-lbs-slot-hash-below fn-lbs-nonempty-length-positive natp nfix len)) '(mod floor))))))

(local (defthm fn-lbs-suffix-next-match
 (implies (and (natp i) (equal rest (nthcdr i full)))
 (equal (fn-lbs-matchp (+ 1 i) msgid full)
        (and (< i (len full)) (equal (fn-record-msgid (car rest)) msgid))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-matchp fn-lbs-nthcdr-car natp posp))))))

(local (defthm fn-lbs-next-row-preserves-query-layout
 (implies (and (consp table) (true-listp table) (natp i) (equal rest (nthcdr i full))
 (fn-lbs-bounded-wordsp table i)
 (fn-lbs-layoutp (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) (max 1 (len table))) table) msgid full 0 nil))
 (fn-lbs-layoutp
 (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) (max 1 (len table)))
 (fn-lbc-canonical-slot-insert (+ 1 i)
 (mod (fn-lbc-msgid-hash (fn-record-msgid (car rest))) (max 1 (len table))) (len table) table)) msgid full 0 nil))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-insert-preserves-query-layout (word (+ 1 i)) (rows full)
 (slot (mod (fn-lbc-msgid-hash (fn-record-msgid (car rest))) (max 1 (len table))))
 (query-slot (mod (fn-lbc-msgid-hash msgid) (max 1 (len table))))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-suffix-next-match fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below fn-lbs-nonempty-length-positive posp natp)) '(mod floor))))))

(local (defthm fn-lbs-slots-from-query-layout
 (implies (and (consp table) (true-listp table) (natp i) (equal rest (nthcdr i full))
 (fn-lbs-bounded-wordsp table i)
 (fn-lbs-layoutp (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) (max 1 (len table))) table) msgid full 0 nil))
 (fn-lbs-layoutp
 (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) (max 1 (len table)))
 (fn-lbc-canonical-slots-from rest i table)) msgid full 0 nil))
 :hints (("Goal" :induct (fn-lbc-canonical-slots-from rest i table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-canonical-slots-from fn-lbs-next-row-preserves-query-layout fn-lbs-insert-next-bounded
 fn-lbs-zero-fill-length fn-lbs-zero-fill-proper fn-lbs-zero-fill-nonempty fn-lbs-nthcdr-successor
 fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below fn-lbs-nonempty-length-positive natp posp nfix)) '(mod floor)))
 ("Subgoal *1/1" :use fn-lbs-next-row-preserves-query-layout))))

(local (defthm fn-lbs-make-zero-facts
 (implies (and (natp n) (true-listp acc) (fn-lbs-bounded-wordsp acc 0) (equal (fn-lbs-nonzero-count acc) 0))
 (and (true-listp (make-list-ac n 0 acc))
      (equal (len (make-list-ac n 0 acc)) (+ n (len acc)))
      (fn-lbs-bounded-wordsp (make-list-ac n 0 acc) 0)
      (equal (fn-lbs-nonzero-count (make-list-ac n 0 acc)) 0)))
 :hints (("Goal" :induct (make-list-ac n 0 acc) :in-theory (union-theories (theory 'ground-zero) '(make-list-ac fn-lbs-bounded-wordsp fn-lbs-nonzero-count true-listp natp zp len))))))

(local (defthm fn-lbs-zero-bound-no-matches
 (implies (fn-lbs-bounded-wordsp cells 0) (equal (fn-lbs-all-matches cells msgid rows) nil))
 :hints (("Goal" :induct (len cells) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-bounded-wordsp fn-lbs-all-matches fn-lbs-matchp posp natp))))))

(local (defthm fn-lbs-initial-table-facts
 (implies (posp capacity)
 (and (true-listp (make-list capacity :initial-element 0))
      (equal (len (make-list capacity :initial-element 0)) capacity)
      (consp (make-list capacity :initial-element 0))
      (fn-lbs-bounded-wordsp (make-list capacity :initial-element 0) 0)
      (equal (fn-lbs-nonzero-count (make-list capacity :initial-element 0)) 0)
      (fn-lbs-coveredp 0 (make-list capacity :initial-element 0))
      (fn-lbs-layoutp
       (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) capacity) (make-list capacity :initial-element 0))
       msgid rows 0 nil)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbs-make-zero-facts (n capacity) (acc nil))
 (:instance fn-lbs-bounded-rotate (bound 0) (cells (make-list capacity :initial-element 0)) (start (mod (fn-lbc-msgid-hash msgid) capacity))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-no-matches-layout fn-lbs-zero-bound-no-matches fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below fn-lbs-bounded-wordsp fn-lbs-coveredp fn-lbs-nonzero-count natp posp len)) '(mod floor))))))

(local (defthm fn-lbs-canonical-table-invariants
 (implies (and (natp capacity) (< (len rows) capacity))
 (let ((table (fn-lbc-canonical-slots-from rows 0 (make-list capacity :initial-element 0))))
 (and (true-listp table) (equal (len table) capacity)
      (fn-lbs-bounded-wordsp table (len rows))
      (fn-lbs-coveredp (len rows) table)
      (fn-lbs-layoutp (fn-lbs-rotate (mod (fn-lbc-msgid-hash msgid) capacity) table) msgid rows 0 nil))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-initial-table-facts)
 (:instance fn-lbs-slots-from-length (rest rows) (i 0) (table (make-list capacity :initial-element 0)))
 (:instance fn-lbs-slots-from-proper (rest rows) (i 0) (table (make-list capacity :initial-element 0)))
 (:instance fn-lbs-slots-from-bounded (rest rows) (i 0) (table (make-list capacity :initial-element 0)))
 (:instance fn-lbs-slots-from-covered (rest rows) (i 0) (table (make-list capacity :initial-element 0)))
 (:instance fn-lbs-slots-from-query-layout (rest rows) (full rows) (i 0) (table (make-list capacity :initial-element 0))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(nthcdr fn-lbs-coveredp natp posp nfix)) '(mod floor))))))

(local (defun fn-lbs-pure-probe (msgid rows slot fuel table)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) nil
  (let ((word (nth (nfix slot) table)))
   (if (zp word) nil
    (let ((rest (fn-lbs-pure-probe msgid rows (mod (+ 1 (nfix slot)) (max 1 (len table))) (- fuel 1) table)))
    (if (fn-lbs-matchp word msgid rows) (cons (- word 1) rest) rest)))))))

(local (defun fn-lbs-scan-fuel (cells fuel msgid rows)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (and (not (zp fuel)) (consp cells) (not (zp (car cells))))
  (let ((rest (fn-lbs-scan-fuel (cdr cells) (- fuel 1) msgid rows)))
   (if (fn-lbs-matchp (car cells) msgid rows) (cons (- (car cells) 1) rest) rest)) nil)))

(local (defthm fn-lbs-scan-fuel-append
 (implies (and (natp fuel) (<= fuel (len a)))
 (equal (fn-lbs-scan-fuel (append a b) fuel msgid rows) (fn-lbs-scan-fuel a fuel msgid rows)))
 :hints (("Goal" :induct (fn-lbs-scan-fuel a fuel msgid rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-scan-fuel binary-append natp zp len))))))

(local (defthm fn-lbs-scan-fuel-full
 (implies (and (natp fuel) (<= (len cells) fuel))
 (equal (fn-lbs-scan-fuel cells fuel msgid rows) (fn-lbs-scan cells msgid rows)))
 :hints (("Goal" :induct (fn-lbs-scan-fuel cells fuel msgid rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-scan-fuel fn-lbs-scan natp zp len))))))

(local (defthm fn-lbs-increasing-member-lower
 (implies (and (fn-lbs-increasingp xs lower) (member-equal x xs))
 (and (natp x) (<= lower x)))
 :hints (("Goal" :induct (fn-lbs-increasingp xs lower)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-increasingp member-equal natp))))))

(local (defthm fn-lbs-increasing-first-is-minimum
 (implies (and (consp xs) (fn-lbs-increasingp xs lower) (member-equal x xs))
 (<= (car xs) x))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-increasing-member-lower (xs (cdr xs)) (lower (+ 1 (car xs)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-increasingp member-equal))))))

(local (defthm fn-lbs-increasing-first-not-in-tail
 (implies (and (consp xs) (fn-lbs-increasingp xs lower))
 (not (member-equal (car xs) (cdr xs))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-increasing-member-lower (x (car xs)) (xs (cdr xs)) (lower (+ 1 (car xs)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-increasingp))))))

(local (defthm fn-lbs-subset-without-head
 (implies (and (subsetp-equal a (cons x b)) (not (member-equal x a))) (subsetp-equal a b))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal member-equal))))))

(local (defthm fn-lbs-increasing-same-set-heads
 (implies (and (consp a) (consp b) (fn-lbs-increasingp a lower) (fn-lbs-increasingp b lower)
               (subsetp-equal a b) (subsetp-equal b a))
 (and (equal (car a) (car b)) (subsetp-equal (cdr a) (cdr b)) (subsetp-equal (cdr b) (cdr a))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-increasing-first-is-minimum (xs a) (x (car b)))
       (:instance fn-lbs-increasing-first-is-minimum (xs b) (x (car a)))
       (:instance fn-lbs-increasing-first-not-in-tail (xs a))
       (:instance fn-lbs-increasing-first-not-in-tail (xs b))
       (:instance fn-lbs-subset-without-head (a (cdr a)) (x (car a)) (b (cdr b)))
       (:instance fn-lbs-subset-without-head (a (cdr b)) (x (car b)) (b (cdr a))))
 :in-theory (union-theories (theory 'ground-zero) '(subsetp-equal fn-lbs-increasingp natp))))))

(local (defun fn-lbs-ordered-equal-induct (a b lower)
 (declare (xargs :guard t :verify-guards nil))
 (if (and (consp a) (consp b))
 (fn-lbs-ordered-equal-induct (cdr a) (cdr b) (+ 1 (car a))) (list a b lower))))

(local (defthm fn-lbs-scan-cyclic-tail
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (posp fuel) (<= fuel (len table)))
 (equal (fn-lbs-scan-fuel (fn-lbs-rotate (mod (+ 1 slot) (max 1 (len table))) table) (- fuel 1) msgid rows)
        (fn-lbs-scan-fuel (cdr (fn-lbs-rotate slot table)) (- fuel 1) msgid rows)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-scan-fuel-append (a (cdr (fn-lbs-rotate slot table))) (b (list (nth slot table))) (fuel (- fuel 1)))
 (:instance fn-lbs-rotate-cyclic-successor (start slot) (cells table))
 (:instance fn-lbs-rotate-length (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table)))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero) '(natp posp len)) '(mod floor))))))

(local (defthm fn-lbs-increasing-same-set-equal
 (implies (and (true-listp a) (true-listp b) (fn-lbs-increasingp a lower) (fn-lbs-increasingp b lower)
               (subsetp-equal a b) (subsetp-equal b a)) (equal a b))
  :rule-classes nil
 :hints (("Goal" :induct (fn-lbs-ordered-equal-induct a b lower)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-ordered-equal-induct fn-lbs-increasingp true-listp subsetp-equal member-equal)))
 ("Subgoal *1/1" :use fn-lbs-increasing-same-set-heads))))

(local (defthm fn-lbs-probe-is-cyclic-scan
 (implies (and (true-listp table) (natp slot) (< slot (len table)) (natp fuel) (<= fuel (len table)))
 (equal (fn-lbs-pure-probe msgid rows slot fuel table)
        (fn-lbs-scan-fuel (fn-lbs-rotate slot table) fuel msgid rows)))
 :hints (("Goal" :induct (fn-lbs-pure-probe msgid rows slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-pure-probe fn-lbs-scan-fuel fn-lbs-scan-fuel-append fn-lbs-rotate-length natp nfix zp)) '(mod floor)))
 ("Subgoal *1/4" :use (fn-lbs-next-slot-natural fn-lbs-next-slot-below-capacity fn-lbs-scan-cyclic-tail
 (:instance fn-lbs-rotate-head (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table))
 (:instance fn-lbs-rotate-cyclic-successor (start slot) (cells table))))
 ("Subgoal *1/3" :use (fn-lbs-next-slot-natural fn-lbs-next-slot-below-capacity fn-lbs-scan-cyclic-tail
 (:instance fn-lbs-rotate-head (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table))
 (:instance fn-lbs-rotate-cyclic-successor (start slot) (cells table))))
 ("Subgoal *1/2" :use ((:instance fn-lbs-rotate-head (start slot) (cells table))
 (:instance fn-lbs-rotate-nonempty (start slot) (cells table)))))))

(local (defthm fn-lbs-probe-full-is-scan
 (implies (and (true-listp table) (natp slot) (< slot (len table)))
 (equal (fn-lbs-pure-probe msgid rows slot (len table) table)
        (fn-lbs-scan (fn-lbs-rotate slot table) msgid rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-probe-is-cyclic-scan fn-lbs-scan-fuel-full fn-lbs-rotate-length))))))

(local (defthm fn-lbs-catalog-seqs-members
 (implies (natp start)
 (iff (member-equal i (fn-cat-seqs-for msgid rows start))
      (and (natp i) (<= start i) (< i (+ start (len rows)))
           (equal (fn-record-msgid (nth (- i start) rows)) msgid))))
 :hints (("Goal" :induct (fn-cat-seqs-for msgid rows start)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-seqs-for member-equal nth natp nfix zp len))))))

(local (defthm fn-lbs-all-matches-members
 (iff (member-equal i (fn-lbs-all-matches cells msgid rows))
      (and (natp i) (< i (len rows))
           (equal (fn-record-msgid (nth i rows)) msgid)
           (member-equal (+ 1 i) cells)))
 :hints (("Goal" :induct (fn-lbs-all-matches cells msgid rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-all-matches fn-lbs-matchp member-equal natp posp))))))

(local (defthm fn-lbs-all-matches-proper
 (true-listp (fn-lbs-all-matches cells msgid rows))
 :hints (("Goal" :induct (fn-lbs-all-matches cells msgid rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-all-matches true-listp))))))

(local (defthm fn-lbs-catalog-seqs-proper
 (true-listp (fn-cat-seqs-for msgid rows start))
 :hints (("Goal" :induct (fn-cat-seqs-for msgid rows start)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-seqs-for true-listp))))))

(local (defthm fn-lbs-increasing-monotone
 (implies (and (fn-lbs-increasingp xs old) (<= new old)) (fn-lbs-increasingp xs new))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-increasingp))))))

(local (defthm fn-lbs-catalog-seqs-increasing
 (implies (natp start) (fn-lbs-increasingp (fn-cat-seqs-for msgid rows start) start))
 :hints (("Goal" :induct (fn-cat-seqs-for msgid rows start)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-seqs-for fn-lbs-increasingp fn-lbs-increasing-monotone natp))))))

(local (defun fn-lbs-row-index-induct (base j rows pm)
 (declare (xargs :guard t :verify-guards nil :measure (nfix j)))
 (if (and (consp rows) (not (zp j)))
 (fn-lbs-row-index-induct (+ 1 (nfix base)) (- j 1) (cdr rows) (max (nfix pm) (nfix (fn-record-stamp (car rows)))))
 (list base pm))))

(local (defthm fn-lbs-row-corr-hash
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
 (equal (fn-lbc-word :msgid-hash i fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid row))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-row-corr))))))

(local (defthm fn-lbs-rows-corr-hash
 (implies (and (fn-lbc-rows-corr base rows pm fn-lbc log) (natp base) (natp j) (< j (len rows)))
 (equal (fn-lbc-word :msgid-hash (+ base j) fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid (nth j rows)))))
 :hints (("Goal" :induct (fn-lbs-row-index-induct base j rows pm)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-row-index-induct fn-lbc-rows-corr fn-lbs-row-corr-hash nth natp nfix zp max len))))))

(defthm fn-lbc-msgid-hash-is-row-hash
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log) (natp i) (< i (len rows)))
 (equal (fn-lbc-word :msgid-hash i fn-lbc) (fn-lbc-msgid-hash (fn-record-msgid (nth i rows)))))
 :hints (("Goal" :use ((:instance fn-lbs-rows-corr-hash (base 0) (j i) (pm 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr natp)))))

(local (defun fn-lbs-slot-index-induct (table base j)
 (declare (xargs :guard t :verify-guards nil :measure (nfix j)))
 (if (and (consp table) (not (zp j)))
 (fn-lbs-slot-index-induct (cdr table) (+ 1 (nfix base)) (- j 1)) (list table base))))

(local (defthm fn-lbs-slot-cells-corr-nth
 (implies (and (fn-lbc-slot-cells-corr table base fn-lbc) (natp base) (natp j) (< j (len table)))
 (equal (fn-lbc-slot-word (+ base j) fn-lbc) (nth j table)))
 :hints (("Goal" :induct (fn-lbs-slot-index-induct table base j)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-slot-index-induct fn-lbc-slot-cells-corr nth natp nfix zp len))))))

(local (defthm fn-lbs-slot-corr-zero-nth
 (implies (and (fn-lbc-slot-cells-corr table 0 fn-lbc) (natp slot) (< slot (len table)))
 (equal (fn-lbc-slot-word slot fn-lbc) (nth slot table)))
 :hints (("Goal" :use ((:instance fn-lbs-slot-cells-corr-nth (base 0) (j slot)))
 :in-theory (union-theories (theory 'ground-zero) '(natp))))))

(local (defthm fn-lbs-native-probe-is-pure-probe
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
 (true-listp table) (equal (len table) (fn-lbc-slot-count fn-lbc))
 (fn-lbc-slot-cells-corr table 0 fn-lbc) (natp slot) (< slot (len table)) (natp fuel))
 (equal (fn-lbc-msgid-probe msgid (fn-lbc-msgid-hash msgid) slot fuel fn-lbc)
        (fn-lbs-pure-probe msgid rows slot fuel table)))
 :hints (("Goal" :induct (fn-lbs-pure-probe msgid rows slot fuel table)
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-probe fn-lbs-pure-probe fn-lbs-slot-corr-zero-nth fn-lbs-matchp
 fn-lbc-msgid-hash-is-row-hash fn-lbc-served-fields-are-abstract fn-lbc-corr-count-is-length
 fn-lbs-mod-natural fn-lbs-mod-positive-below fn-lbs-nonempty-length-positive natp posp nfix zp)) '(mod floor))))))

(local (defthm fn-lbs-covered-member
 (implies (and (natp bound) (fn-lbs-coveredp bound cells) (posp word) (<= word bound)) (member-equal word cells))
 :hints (("Goal" :induct (fn-lbs-coveredp bound cells)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-coveredp natp posp zp))))))

(local (defthm fn-lbs-nthcdr-consp-iff
 (iff (consp (nthcdr n rows)) (< (nfix n) (len rows)))
 :hints (("Goal" :induct (nthcdr n rows) :in-theory (union-theories (theory 'ground-zero) '(nthcdr nfix zp len))))))

(local (defthm fn-lbs-filter-subset-catalog
 (subsetp-equal (fn-lbs-all-matches cells msgid rows) (fn-cat-seqs-for msgid rows 0))
 :hints (("Goal" :induct (fn-lbs-all-matches cells msgid rows)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-all-matches fn-lbs-matchp fn-lbs-catalog-seqs-members subsetp-equal posp natp))))))

(local (defthm fn-lbs-catalog-subset-filter
 (implies (and (natp start) (equal rest (nthcdr start full)) (fn-lbs-coveredp (len full) cells))
 (subsetp-equal (fn-cat-seqs-for msgid rest start) (fn-lbs-all-matches cells msgid full)))
 :hints (("Goal" :induct (fn-cat-seqs-for msgid rest start)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat-seqs-for fn-lbs-all-matches-members fn-lbs-covered-member fn-lbs-nthcdr-consp-iff
 fn-lbs-nthcdr-car fn-lbs-nthcdr-successor subsetp-equal natp posp nfix)))
 ("Subgoal *1/1" :use ((:instance fn-lbs-covered-member (word (+ 1 start)) (bound (len full))))))))

(local (defthm fn-lbs-covered-rotate
 (implies (and (true-listp cells) (natp start) (<= start (len cells)) (fn-lbs-coveredp bound cells))
 (fn-lbs-coveredp bound (fn-lbs-rotate start cells)))
 :hints (("Goal" :induct (fn-lbs-coveredp bound cells)
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbs-coveredp fn-lbs-rotate-members))))))

(local (defthm fn-lbs-probe-is-catalog-seqs
 (implies (and (true-listp table) (natp slot) (< slot (len table))
 (fn-lbs-coveredp (len rows) table)
 (fn-lbs-layoutp (fn-lbs-rotate slot table) msgid rows 0 nil))
 (equal (fn-lbs-pure-probe msgid rows slot (len table) table) (fn-cat-seqs-for msgid rows 0)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbs-increasing-same-set-equal
 (a (fn-lbs-all-matches (fn-lbs-rotate slot table) msgid rows))
 (b (fn-cat-seqs-for msgid rows 0)) (lower 0))
 (:instance fn-lbs-catalog-subset-filter (start 0) (rest rows) (full rows) (cells (fn-lbs-rotate slot table)))
 (:instance fn-lbs-layout-implies-increasing (cells (fn-lbs-rotate slot table)) (last 0) (empty-seen nil)))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbs-probe-full-is-scan fn-lbs-scan-is-all-matches fn-lbs-all-matches-proper fn-lbs-catalog-seqs-proper
 fn-lbs-catalog-seqs-increasing fn-lbs-filter-subset-catalog fn-lbs-covered-rotate nthcdr natp))))))

(local (defthm fn-lbs-slot-count-natural
 (natp (fn-lbc-slot-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-count fn-lbc-msgid-slots-count fn-lbc-msgid-slots$a-count natp))))))

(local (defthm fn-lbs-canonical-table-probe
 (implies (and (natp capacity) (< (len rows) capacity))
 (let ((table (fn-lbc-canonical-slots-from rows 0 (make-list capacity :initial-element 0))))
 (equal (fn-lbs-pure-probe msgid rows (mod (fn-lbc-msgid-hash msgid) capacity) capacity table)
        (fn-cat-seqs-for msgid rows 0))))
 :hints (("Goal" :do-not-induct t
 :use (fn-lbs-canonical-table-invariants
 (:instance fn-lbs-probe-is-catalog-seqs
 (slot (mod (fn-lbc-msgid-hash msgid) capacity))
 (table (fn-lbc-canonical-slots-from rows 0 (make-list capacity :initial-element 0)))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below natp posp)) '(mod floor))))))

(local (defthm fn-lbs-native-probe-zero
 (implies (zp fuel) (equal (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc) nil))
 :hints (("Goal" :in-theory (enable fn-lbc-msgid-probe)))))

(local (defthm fn-lbs-catalog-seqs-empty
 (implies (not (consp rows)) (equal (fn-cat-seqs-for msgid rows i) nil))
 :hints (("Goal" :in-theory (enable fn-cat-seqs-for)))))

(defthm fn-lbc-msgid-seqs-is-abstract
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
 (equal (fn-lbc-msgid-seqs msgid fn-lbc) (fn-cat-seqs-for msgid rows 0)))
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-lbc-slot-count fn-lbc) 0))
 :use ((:instance fn-lbs-canonical-table-invariants (capacity (fn-lbc-slot-count fn-lbc)))
 (:instance fn-lbs-canonical-table-probe (capacity (fn-lbc-slot-count fn-lbc)))
 (:instance fn-lbs-native-probe-is-pure-probe
 (table (fn-lbc-canonical-slots-from rows 0 (make-list (fn-lbc-slot-count fn-lbc) :initial-element 0)))
 (slot (mod (fn-lbc-msgid-hash msgid) (max 1 (fn-lbc-slot-count fn-lbc))))
 (fuel (fn-lbc-slot-count fn-lbc))))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-seqs fn-lbc-corr fn-lbc-slots-corr fn-lbs-slot-count-natural
 fn-lbs-native-probe-zero fn-lbs-catalog-seqs-empty fn-lbs-hash-natural fn-lbs-mod-natural fn-lbs-mod-positive-below natp posp)) '(mod floor)))))
