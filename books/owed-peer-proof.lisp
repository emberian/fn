; Exact discharges over the peer reference model.
(in-package "ACL2")
(include-book "owed-peer")
(include-book "owed-discharge")

; K-P6 counterexample: reclaim a name before its first acceptance.  The
; missing history entry has CADR NIL, so subject NIL satisfies the premise.
; Acceptance returns :accepted and changes allocations from 0 to 1.
(local
 (defthm fn2-pm-reclaimed-duplicate-counterexample
   (let ((st (fn2-pm-reclaim 'm (fn2-pm-node 'n 1 nil))))
     (and (not (fn2-pm-reclaimed-duplicate$owed 'm nil 'e nil st))
          (equal (mv-nth 0 (fn2-pm-accept 'm nil 'e nil st)) :accepted)
          (equal (fn2-pm-get :allocations
                             (mv-nth 1 (fn2-pm-accept 'm nil 'e nil st))) 1)))
   :rule-classes nil))

; Canonical lists are strictly lexordered. If two of them differ, their
; first unequal heads give a membership witness.
(local (in-theory (disable lexorder)))
(local (defun pm-sorted (xs)
         (if (atom xs) (null xs)
           (and (or (atom (cdr xs))
                    (and (lexorder (car xs) (cadr xs))
                         (not (equal (car xs) (cadr xs)))))
                (pm-sorted (cdr xs))))))
(local (defthm pm-insert-head
         (equal (car (fn2-pm-insert x xs))
                (if (or (atom xs) (lexorder x (car xs))) x (car xs)))))
(local (defthm pm-sorted-insert
         (implies (pm-sorted xs) (pm-sorted (fn2-pm-insert x xs)))))
(local (defthm pm-sorted-sort (pm-sorted (fn2-pm-sort-names xs))))
(local (defthm pm-member-insert
         (iff (member-equal x (fn2-pm-insert y xs))
              (or (equal x y) (member-equal x xs)))))
(local (defthm pm-member-sort
         (iff (member-equal x (fn2-pm-sort-names xs)) (member-equal x xs))))
(local (defthm pm-below-head
         (implies (and (pm-sorted xs) (lexorder x (car xs))
                       (not (equal x (car xs))))
                  (not (member-equal x xs)))))
(local (defun pm-difference (xs ys)
         (cond ((atom xs) (car ys))
               ((atom ys) (car xs))
               ((equal (car xs) (car ys)) (pm-difference (cdr xs) (cdr ys)))
               ((lexorder (car xs) (car ys)) (car xs))
               (t (car ys)))))
(local (defthm pm-difference-member
         (implies (and (pm-sorted xs) (pm-sorted ys) (not (equal xs ys)))
                  (or (member-equal (pm-difference xs ys) xs)
                      (member-equal (pm-difference xs ys) ys)))
         :rule-classes nil))
(local (defthm pm-sorted-extensional
         (implies (and (pm-sorted xs) (pm-sorted ys)
                       (iff (member-equal (pm-difference xs ys) xs)
                            (member-equal (pm-difference xs ys) ys)))
                  (equal xs ys))
         :rule-classes nil
         :hints (("Goal" :induct (pm-difference xs ys))
                 ("Subgoal *1/3" :use ((:instance pm-difference-member
                                       (xs (cdr xs)) (ys (cdr ys))))))))

(local (defun pm-evidenced (name subject facts)
         (and (consp facts)
              (or (and (equal name (fn2-pm-fname (car facts)))
                       (equal subject (fn2-pm-fsubject (car facts))))
                  (pm-evidenced name subject (cdr facts))))))
(local (defthm pm-evidenced-insert
         (equal (pm-evidenced n s (fn2-pm-insert f xs))
                (or (and (equal n (fn2-pm-fname f))
                         (equal s (fn2-pm-fsubject f)))
                    (pm-evidenced n s xs)))))
(local (defthm pm-evidenced-sort
         (equal (pm-evidenced n s (fn2-pm-sort-names xs))
                (pm-evidenced n s xs))))
(local (defthm pm-equal-evidence-pair
         (implies (equal (fn2-pm-sort-names a) (fn2-pm-sort-names b))
                  (equal (pm-evidenced n s a) (pm-evidenced n s b)))
         :rule-classes nil
         :hints (("Goal" :use ((:instance pm-evidenced-sort (xs a))
                                (:instance pm-evidenced-sort (xs b)))
                  :in-theory (disable pm-evidenced-sort)))))
(local (defthm pm-lookup-put
         (equal (assoc-equal k (put-assoc-equal key v al))
                (if (equal k key) (cons key v) (assoc-equal k al)))))
(local (defthm pm-fold-subjects
         (iff (member-equal s (cdr (assoc-equal n (fn2-pm-fold facts acc))))
              (or (pm-evidenced n s facts)
                  (member-equal s (cdr (assoc-equal n acc)))))
         :hints (("Goal" :induct (fn2-pm-fold facts acc)))))
(local (defthm pm-fold-sorted
         (implies (pm-sorted (cdr (assoc-equal n acc)))
                  (pm-sorted (cdr (assoc-equal n (fn2-pm-fold facts acc)))))
         :hints (("Goal" :induct (fn2-pm-fold facts acc)))))
(local (defthm pm-fold-same-subjects
         (implies (equal (fn2-pm-sort-names a) (fn2-pm-sort-names b))
                  (equal (cdr (assoc-equal n (fn2-pm-fold a nil)))
                         (cdr (assoc-equal n (fn2-pm-fold b nil)))))
         :rule-classes nil
         :hints (("Goal"
                  :use ((:instance pm-sorted-extensional
                         (xs (cdr (assoc-equal n (fn2-pm-fold a nil))))
                         (ys (cdr (assoc-equal n (fn2-pm-fold b nil)))))
                        (:instance pm-equal-evidence-pair
                         (s (pm-difference (cdr (assoc-equal n (fn2-pm-fold a nil)))
                                           (cdr (assoc-equal n (fn2-pm-fold b nil)))))))))))

; In a folded binding map every name occurs once and has subjects.
(local (defun pm-binding-map (al)
         (or (atom al)
             (and (consp (cdar al))
                  (not (assoc-equal (caar al) (cdr al)))
                  (pm-binding-map (cdr al))))))
(local (defthm pm-binding-map-put
         (implies (and (pm-binding-map al) (consp v))
                  (pm-binding-map (put-assoc-equal k v al)))))
(local (defthm pm-binding-map-fold
         (implies (pm-binding-map acc) (pm-binding-map (fn2-pm-fold facts acc)))))
(local (defthm pm-binding-member
         (implies (pm-binding-map al)
                  (iff (member-equal entry al)
                       (and (consp entry) (consp (cdr entry))
                            (equal (cdr entry) (cdr (assoc-equal (car entry) al))))))))
(local (defthm pm-fold-same-entry
         (implies (equal (fn2-pm-sort-names a) (fn2-pm-sort-names b))
                  (iff (member-equal entry (fn2-pm-fold a nil))
                       (member-equal entry (fn2-pm-fold b nil))))
         :rule-classes nil
         :hints (("Goal" :use ((:instance pm-fold-same-subjects (n (car entry))))))))
(local (defthm pm-canonical-bindings
         (implies (equal (fn2-pm-sort-names a) (fn2-pm-sort-names b))
                  (equal (fn2-pm-sort-names (fn2-pm-fold a nil))
                         (fn2-pm-sort-names (fn2-pm-fold b nil))))
         :rule-classes nil
         :hints (("Goal"
                  :use ((:instance pm-sorted-extensional
                         (xs (fn2-pm-sort-names (fn2-pm-fold a nil)))
                         (ys (fn2-pm-sort-names (fn2-pm-fold b nil))))
                        (:instance pm-fold-same-entry
                         (entry (pm-difference (fn2-pm-sort-names (fn2-pm-fold a nil))
                                               (fn2-pm-sort-names (fn2-pm-fold b nil))))))))))
(defthm fn2-pm-peer-claim-proved
  (fn2-pm-peer-claim$owed a b)
  :rule-classes nil
  :hints (("Goal" :use ((:instance pm-canonical-bindings
                         (a (fn2-pm-get :evidence a)) (b (fn2-pm-get :evidence b)))))))
(fn2-owed-discharge fn2-pm-peer-claim fn2-pm-peer-claim-proved)

; Read-over-write and frame rules for the fields used by the run invariants.
(local (defthm pm-get-put
         (equal (fn2-pm-get k (fn2-pm-put key v st))
                (if (equal k key) v (fn2-pm-get k st)))))
(local (in-theory (disable fn2-pm-get fn2-pm-put fn2-pm-row fn2-pm-reply-state)))
(local (defmacro pm-frame (name changed call)
         `(defthm ,name
            (implies (not (member-eq k ',changed))
                     (equal (fn2-pm-get k ,call) (fn2-pm-get k st))))))
(local (pm-frame pm-admit-frame (:budget :evidence :gaps)
                 (mv-nth 1 (fn2-pm-admit fact st))))
(local (in-theory (disable fn2-pm-admit)))
(local (pm-frame pm-admit-all-frame (:budget :evidence :gaps)
                 (fn2-pm-admit-all facts st)))
(local (in-theory (disable fn2-pm-admit-all)))
(local (pm-frame pm-accept-frame (:budget :evidence :gaps :allocations :reclaimed :history)
                 (mv-nth 1 (fn2-pm-accept n s id deps st))))
(local (pm-frame pm-import-frame (:budget :evidence :gaps :peer-history)
                 (fn2-pm-import page st)))
(local (pm-frame pm-install-frame (:feed) (fn2-pm-install peer epoch occs st)))
(local (pm-frame pm-release-frame (:pins) (mv-nth 1 (fn2-pm-release id proof st))))
(local (pm-frame pm-reply-frame (:feed :dispositions) (fn2-pm-reply id code st)))
(local (in-theory (disable fn2-pm-accept fn2-pm-import fn2-pm-install
                           fn2-pm-release fn2-pm-reply)))
(local (defthm pm-step-faults
         (equal (fn2-pm-get :faults (fn2-pm-step op st)) (fn2-pm-get :faults st))))

; Custody is an invariant of the pin list. A release changes at most one
; held pin, and the proof stored in that pin is exactly the one checked.
(local (defthm pm-custody-append
         (equal (fn2-pm-kp5-list (append xs ys))
                (and (fn2-pm-kp5-list xs) (fn2-pm-kp5-list ys)))))
(local (defthm pm-custody-release-list
         (implies (and (not (fn2-pm-get :faults st)) (fn2-pm-kp5-list os))
                  (fn2-pm-kp5-list (mv-nth 1 (fn2-pm-release-list id proof os st))))
         :hints (("Goal" :induct (fn2-pm-release-list id proof os st)))))
(local (defthm pm-custody-release
         (implies (and (not (fn2-pm-get :faults st)) (fn2-pm-kp5 st))
                  (fn2-pm-kp5 (mv-nth 1 (fn2-pm-release id proof st))))
         :hints (("Goal" :in-theory (e/d (fn2-pm-release) (fn2-pm-release-list))))))
(local (defthm pm-custody-step
         (implies (and (not (fn2-pm-get :faults st)) (fn2-pm-kp5 st))
                  (fn2-pm-kp5 (fn2-pm-step op st)))
         :hints (("Goal" :use ((:instance pm-custody-release
                                 (id (nth 1 op)) (proof (nth 2 op))))))))
(local (in-theory (disable fn2-pm-step fn2-pm-kp5)))
(local (defthm pm-custody-run
         (implies (and (not (fn2-pm-get :faults st)) (fn2-pm-kp5 st))
                  (fn2-pm-kp5 (fn2-pm-run ops st)))))
(defthm fn2-pm-custody-proved
  (fn2-pm-custody$owed ops budget)
  :rule-classes nil
  :hints (("Goal" :use ((:instance pm-custody-run (st (fn2-pm-node 'n budget nil))))
           :in-theory (enable fn2-pm-kp5 fn2-pm-get))))
(fn2-owed-discharge fn2-pm-custody fn2-pm-custody-proved)

; Installation can append another row with the same delivery identity.  Only
; the first such row can receive a reply or an offer.  Project onto one
; identity, retaining all its rows so duplicate installations are covered.
(local (defun pm-states (k rows)
         (if (atom rows) nil
           (if (equal k (caar rows))
               (cons (nth 2 (car rows)) (pm-states k (cdr rows)))
             (pm-states k (cdr rows))))))
(local (defun pm-all-pending (ss)
         (or (atom ss)
             (and (equal (car ss) :pending) (pm-all-pending (cdr ss))))))
(local (defun pm-delivery-ok (ss k ts)
         (let ((s (car ss)))
           (and (pm-all-pending (cdr ss))
                (or (atom ss) (member-eq s '(:pending :offered)) (fn2-pm-terminal-p s))
                (if (fn2-pm-terminal-p s)
                    (and (equal (fn2-pm-count k ts) 1)
                         (equal (cdr (assoc-equal k ts)) s))
                  (equal (fn2-pm-count k ts) 0))))))
(local (defun pm-delivery (k st)
         (pm-delivery-ok (pm-states k (fn2-pm-get :feed st)) k
                         (fn2-pm-get :dispositions st))))
(local (defthm pm-states-append
         (equal (pm-states k (append xs ys)) (append (pm-states k xs) (pm-states k ys)))))
(local (defthm pm-all-pending-append
         (equal (pm-all-pending (append xs ys)) (and (pm-all-pending xs) (pm-all-pending ys)))))
(local (defthm pm-delivery-add-pending
         (implies (pm-delivery-ok ss k ts)
                  (pm-delivery-ok (append ss '(:pending)) k ts))))
(local (defthm pm-states-true-list (true-listp (pm-states k rows)) :rule-classes :type-prescription))
(local (defthm pm-append-nil
         (implies (true-listp xs) (equal (append xs nil) xs))))
(local (defthm pm-delivery-install
         (implies (pm-delivery k st) (pm-delivery k (fn2-pm-install peer epoch occs st)))
         :hints (("Goal" :induct (fn2-pm-install peer epoch occs st)
                  :in-theory (e/d (fn2-pm-install) (pm-delivery-ok))))))
(local (defthm pm-row-state
         (equal (nth 2 (fn2-pm-row k rows)) (car (pm-states k rows)))
         :hints (("Goal" :in-theory (enable fn2-pm-row)))))
(local (defthm pm-states-set
         (equal (pm-states k (fn2-pm-reply-rows-set did s rows))
                (let ((ss (pm-states k rows)))
                  (if (and (equal k did) (consp ss)) (cons s (cdr ss)) ss)))))
(local (defthm pm-delivery-offer
         (implies (pm-delivery k st) (pm-delivery k (fn2-pm-offer-row did st)))))
(local (defun pm-retire-offers (ss)
         (if (atom ss) nil
           (cons (if (eq (car ss) :offered) :pending (car ss)) (pm-retire-offers (cdr ss))))))
(local (defthm pm-states-restart
         (equal (pm-states k (fn2-pm-restart-rows rows))
                (pm-retire-offers (pm-states k rows)))))
(local (defthm pm-all-pending-retire
         (implies (pm-all-pending ss) (pm-all-pending (pm-retire-offers ss)))))
(local (defthm pm-delivery-retire
         (implies (pm-delivery-ok ss k ts) (pm-delivery-ok (pm-retire-offers ss) k ts))
         :hints (("Goal" :expand (pm-retire-offers ss)))))
(local (defthm pm-delivery-restart
         (implies (pm-delivery k st) (pm-delivery k (fn2-pm-restart st)))
         :hints (("Goal" :in-theory (disable pm-delivery-ok)))))

; A reply updates the first matching row.  A terminal reply to a previously
; nonterminal row appends a disposition to a log with zero entries for it.
(local (defthm pm-reply-key
         (equal (car (fn2-pm-reply-state code row st)) (car row))
         :hints (("Goal" :in-theory (enable fn2-pm-reply-state)))))
(local (defthm pm-reply-consp
         (consp (fn2-pm-reply-state code row st))
         :hints (("Goal" :in-theory (enable fn2-pm-reply-state)
                  :cases ((consp row))))))
(local (defthm pm-reply-states
         (equal (pm-states k (fn2-pm-reply-rows did code rows st))
                (let ((ss (pm-states k rows)))
                  (if (and (equal k did) (consp ss))
                      (cons (nth 2 (fn2-pm-reply-state code (fn2-pm-row did rows) st)) (cdr ss))
                    ss)))
         :hints (("Goal" :in-theory (enable fn2-pm-row)))))
(local (defthm pm-row-after-reply
         (equal (fn2-pm-row did (fn2-pm-reply-rows did code rows st))
                (if (consp (pm-states did rows))
                    (fn2-pm-reply-state code (fn2-pm-row did rows) st)
                  nil))
         :hints (("Goal" :in-theory (enable fn2-pm-row)))))
(local (defthm pm-reply-absorbing
         (implies (and (not (fn2-pm-get :faults st)) (fn2-pm-terminal-p (nth 2 row)))
                  (equal (fn2-pm-reply-state code row st) row))
         :hints (("Goal" :in-theory (enable fn2-pm-reply-state)))))
(local (defthm pm-reply-status-range
         (let ((s (nth 2 (fn2-pm-reply-state code row st))))
           (or (fn2-pm-terminal-p s) (eq s :pending)))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable fn2-pm-reply-state)))))
(local (defthm pm-count-append
         (equal (fn2-pm-count k (append xs ys)) (+ (fn2-pm-count k xs) (fn2-pm-count k ys)))))
(local (defthm pm-assoc-append
         (equal (assoc-equal k (append xs ys)) (if (equal (fn2-pm-count k xs) 0)
                    (assoc-equal k ys) (assoc-equal k xs)))))
(local (defthm pm-no-disposition
         (implies (equal (fn2-pm-count k ts) 0) (not (assoc-equal k ts)))))
(local (defthm pm-delivery-other-log
         (implies (not (equal did k))
                  (equal (pm-delivery-ok ss k (append ts (list (cons did s))))
                         (pm-delivery-ok ss k ts)))))
(local (defthm pm-delivery-answer
         (let* ((old (car ss))
                (logp (and (fn2-pm-terminal-p s) (not (equal old s)))))
           (implies (and (consp ss) (pm-delivery-ok ss k ts)
                         (implies (fn2-pm-terminal-p old) (equal old s))
                         (or (fn2-pm-terminal-p s) (eq s :pending)))
                    (pm-delivery-ok (cons s (cdr ss)) k
                                    (if logp (append ts (list (cons k s))) ts))))))
(local (in-theory (disable pm-delivery-ok fn2-pm-terminal-p pm-states
                           fn2-pm-reply-rows fn2-pm-reply-rows-set)))
(local (defthm pm-delivery-reply
         (implies (and (not (fn2-pm-get :faults st)) (pm-delivery k st))
                  (pm-delivery k (fn2-pm-reply did code st)))
         :hints (("Goal"
                  :cases ((equal k did))
                  :use ((:instance pm-reply-status-range
                         (row (fn2-pm-row did (fn2-pm-get :feed st))))
                        (:instance pm-delivery-answer
                         (ss (pm-states did (fn2-pm-get :feed st)))
                         (k did) (ts (fn2-pm-get :dispositions st))
                         (s (nth 2 (fn2-pm-reply-state
                                    code (fn2-pm-row did (fn2-pm-get :feed st)) st)))))
                  :in-theory (enable fn2-pm-reply)))))
(local (defthm pm-delivery-step
         (implies (and (not (fn2-pm-get :faults st)) (pm-delivery k st))
                  (pm-delivery k (fn2-pm-step op st)))
         :hints (("Goal" :in-theory (e/d (fn2-pm-step)
                                         (fn2-pm-offer-row fn2-pm-restart))
                  :use ((:instance pm-delivery-install
                         (peer (nth 1 op)) (epoch (nth 2 op)) (occs (nth 3 op)))
                        (:instance pm-delivery-offer (did (nth 1 op)))
                        (:instance pm-delivery-reply (did (nth 1 op)) (code (nth 2 op)))
                        pm-delivery-restart)))))
(local (in-theory (disable pm-delivery)))
(local (defthm pm-delivery-run
         (implies (and (not (fn2-pm-get :faults st)) (pm-delivery k st))
                  (pm-delivery k (fn2-pm-run ops st)))))
(local (defthm pm-delivery-from-node
         (pm-delivery k (fn2-pm-run ops (fn2-pm-node 'n budget nil)))
         :hints (("Goal" :use ((:instance pm-delivery-run (st (fn2-pm-node 'n budget nil))))
                  :in-theory (enable pm-delivery pm-delivery-ok pm-states fn2-pm-get)))))
(local (in-theory (disable fn2-pm-run fn2-pm-node pm-delivery-from-node pm-delivery-run)))
(local (defthm pm-count-from-node
         (<= (fn2-pm-count k (fn2-pm-get :dispositions
                                        (fn2-pm-run ops (fn2-pm-node 'n budget nil)))) 1)
         :hints (("Goal" :use pm-delivery-from-node
                  :in-theory (enable pm-delivery pm-delivery-ok)))))
(local (defthm pm-kp4-from-node
         (fn2-pm-kp4-list ts (fn2-pm-get :dispositions
                                         (fn2-pm-run ops (fn2-pm-node 'n budget nil))))))
(defthm fn2-pm-one-terminal-proved
  (fn2-pm-one-terminal$owed ops budget)
  :rule-classes nil)
(fn2-owed-discharge fn2-pm-one-terminal fn2-pm-one-terminal-proved)

(local (defthm pm-states-member
         (implies (member-equal row rows)
                  (member-equal (nth 2 row) (pm-states (car row) rows)))
         :hints (("Goal" :in-theory (enable pm-states)))))
(local (defthm pm-pending-member
         (implies (and (pm-all-pending ss) (member-eq s ss)) (equal s :pending))
         :rule-classes nil))
(local (defthm pm-delivery-member
         (implies (and (pm-delivery-ok ss k ts) (member-equal s ss))
                  (if (fn2-pm-terminal-p s)
                      (equal (cdr (assoc-equal k ts)) s)
                    (member-eq s '(:pending :offered))))
         :rule-classes nil
         :hints (("Goal" :use ((:instance pm-pending-member (ss (cdr ss))))
                  :expand (member-equal s ss)
                  :in-theory (enable pm-delivery-ok)))))
(local (defthm pm-row-from-node
         (let* ((st (fn2-pm-run ops (fn2-pm-node 'n budget nil)))
                (ts (fn2-pm-get :dispositions st)) (s (nth 2 row)))
           (implies (member-equal row (fn2-pm-get :feed st))
                    (if (fn2-pm-terminal-p s)
                        (equal (cdr (assoc-equal (car row) ts)) s)
                      (member-eq s '(:pending :offered)))))
         :rule-classes nil
         :hints (("Goal"
                  :in-theory (enable pm-delivery)
                  :use ((:instance pm-delivery-from-node (k (car row)))
                        (:instance pm-delivery-member (k (car row)) (s (nth 2 row))
                         (ss (pm-states (car row) (fn2-pm-get :feed
                                (fn2-pm-run ops (fn2-pm-node 'n budget nil)))))
                         (ts (fn2-pm-get :dispositions
                                (fn2-pm-run ops (fn2-pm-node 'n budget nil))))))))))
(local (defthm pm-kp3a-from-node
         (let ((st (fn2-pm-run ops (fn2-pm-node 'n budget nil))))
           (implies (subsetp-equal rows (fn2-pm-get :feed st))
                    (fn2-pm-kp3a-rows rows (fn2-pm-get :dispositions st))))
         :hints (("Goal" :induct (len rows))
                 ("Subgoal *1/1" :use ((:instance pm-row-from-node (row (car rows))))))))
(local (defthm pm-subset-cons
         (implies (subsetp-equal xs ys) (subsetp-equal xs (cons y ys)))))
(local (defthm pm-subset-self (subsetp-equal rows rows)))
(defthm fn2-pm-feed-safety-proved
  (fn2-pm-feed-safety$owed ops budget)
  :rule-classes nil)
(fn2-owed-discharge fn2-pm-feed-safety fn2-pm-feed-safety-proved)
