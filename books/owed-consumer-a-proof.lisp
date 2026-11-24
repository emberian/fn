; Trace invariants of the fault-free consumer reference model.
(in-package "ACL2")
(include-book "owed-consumer")
(include-book "owed-discharge")

(local (in-theory (current-theory 'fn2-cns-class)))

(local (defthm cns-a-alist-put
         (implies (alistp st) (alistp (put-assoc-equal k v st)))))
(local (defthm cns-a-assoc-put
         (equal (assoc-equal key (put-assoc-equal k v st))
                (if (equal key k) (cons k v) (assoc-equal key st)))))
(local (defthm cns-a-alist-model-put
         (implies (alistp st) (alistp (fn2-cns-model-put k v st)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put)))))
(local (defthm cns-a-get-put
         (implies (alistp st)
                  (equal (fn2-cns-get key (fn2-cns-model-put k v st))
                         (if (equal key k) v (fn2-cns-get key st))))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put fn2-cns-get)))))
(local (defthm cns-a-mv-nth-cons
         (equal (mv-nth n (cons x xs))
                (if (zp n) x (mv-nth (1- n) xs)))))
(local (defthm cns-a-nth-cons
         (equal (nth n (cons x xs))
                (if (zp n) x (nth (1- n) xs)))))

(local (defun cns-a-replays-p (rows)
         (if (atom rows) t
           (and (fn2-consumer-outcome-p 'append (cadr (cdar rows)))
                (cns-a-replays-p (cdr rows))))))
(local (defthm cns-a-replay-lookup
         (implies (and (cns-a-replays-p rows) (fn2-cns-at key rows))
                  (fn2-consumer-outcome-p 'append (cadr (fn2-cns-at key rows))))
         :hints (("Goal" :in-theory (e/d (fn2-cns-at) (fn2-consumer-outcome-p))))))
(local (defthm cns-a-replay-store
         (implies (and (cns-a-replays-p rows)
                       (fn2-consumer-outcome-p 'append (cadr v)))
                  (cns-a-replays-p (fn2-cns-set key v rows)))
         :hints (("Goal" :in-theory (e/d (fn2-cns-set) (fn2-consumer-outcome-p))))))
(local (defun cns-a-store-p (st)
         (and (alistp st) (cns-a-replays-p (fn2-cns-get :outcomes st)))))
(local (defthm cns-a-store-put
         (implies (and (cns-a-store-p st)
                       (or (not (equal key :outcomes)) (cns-a-replays-p v)))
                  (cns-a-store-p (fn2-cns-model-put key v st)))))
(local (defthm cns-a-store-replays
         (implies (cns-a-store-p st) (cns-a-replays-p (fn2-cns-get :outcomes st)))))
(local (defthm cns-a-store-alist
         (implies (cns-a-store-p st) (alistp st))))
(local (in-theory (disable cns-a-store-p cns-a-replays-p fn2-consumer-outcome-p)))

(local (defthm cns-a-meter-not-shared
         (not (equal (fn2-cns-meter st p amount) :shared))
         :hints (("Goal" :in-theory (enable fn2-cns-meter)))))
(local (defthm cns-a-page-declared
         (implies (member-eq verb '(read wait))
                  (fn2-consumer-outcome-p verb (fn2-cns-page st p k limits nil)))
         :hints (("Goal" :in-theory (enable fn2-cns-page fn2-cns-scope-problem
                                            fn2-consumer-outcome-p)))))
(local (defthm cns-a-wake-declared
         (fn2-cns-answers-declared-p (mv-nth 0 (fn2-cns-wake-list waits st nil)))
         :hints (("Goal" :induct (fn2-cns-wake-list waits st nil)
                  :in-theory (enable fn2-cns-wake-list fn2-cns-wait-answer
                                     fn2-cns-answers-declared-p)))))
(local (defthm cns-a-answers-empty (fn2-cns-answers-declared-p nil)
         :hints (("Goal" :in-theory (enable fn2-cns-answers-declared-p)))))

(local (defun cns-a-refusal-frame-p (st next)
         (or (equal next st)
             (equal next (fn2-cns-model-put :evidence (fn2-cns-get :evidence next) st)))))
(local (defthm cns-a-refusal-frame-self (cns-a-refusal-frame-p st st)))
(local (defthm cns-a-refusal-frame-evidence
         (implies (alistp st)
                  (cns-a-refusal-frame-p st (fn2-cns-model-put :evidence v st)))))
(local (defthm cns-a-outcome-cons
         (equal (fn2-consumer-outcome-p verb (cons tag fields))
                (and (true-listp fields)
                     (case tag
                       (:accepted (and (equal (len fields) 1) (true-listp (car fields))
                                       (equal (len (car fields)) (fn2-consumer-verb-arity verb))))
                       (:refused (and (member (len fields) '(1 2)) (symbolp (car fields))
                                      (member-eq (car fields) (fn2-consumer-verb-reasons verb)) t))
                       (:uncertain (and (equal (len fields) 1)
                                        (eq (fn2-consumer-verb-effect verb) :durable)))
                       (otherwise nil))))
         :hints (("Goal" :in-theory (enable fn2-consumer-outcome-p)))))
(local (in-theory (e/d ((:executable-counterpart fn2-consumer-outcome-p))
                       (cns-a-refusal-frame-p nth fn2-consumer-verb-p))))
(local (in-theory (enable (:executable-counterpart fn2-consumer-verb-p)
                          (:executable-counterpart nth))))

(local
 (defmacro cns-a-check-verb (verb args &rest extra)
   (let* ((fn (packn (list 'fn2-cns- verb)))
          (call (cons fn args))
          (out `(mv-nth 0 ,call))
          (next `(mv-nth 1 ,call))
          (declared `(fn2-consumer-outcome-p ',verb ,out)))
     `(defthm ,(packn (list 'cns-a-contract- verb))
        (implies (cns-a-store-p st)
                 (and ,(if (eq verb 'wait)
                           `(implies (not (equal ,out :parked)) ,declared)
                         declared)
                      (cns-a-store-p ,next)
                      (implies (equal (fn2-cns-class ,out) :refused)
                               (cns-a-refusal-frame-p st ,next))))
        :hints (("Goal" :do-not-induct t
                 :in-theory (enable ,fn fn2-cns-admit ,@extra)))))))

(local (cns-a-check-verb register (st p c streams start nil) fn2-cns-install fn2-cns-model-charge))
(local (cns-a-check-verb rebase (st p k streams start nil) fn2-cns-install fn2-cns-model-charge fn2-cns-scope-problem))
(local (cns-a-check-verb unregister (st p k nil) fn2-cns-model-charge fn2-cns-scope-problem))
(local (cns-a-check-verb read (st p k limits nil)))
(local (cns-a-check-verb wait (st p k limits nil)))
(local (cns-a-check-verb ack (st p k nil) fn2-cns-model-charge fn2-cns-scope-problem))
(local (cns-a-check-verb position (st p c nil)))
(local (cns-a-check-verb status (st p c nil)))
(local (cns-a-check-verb fetch (st p reference nil)))
(local (cns-a-check-verb append (st p stream article op nil) fn2-cns-model-charge))

(local (in-theory (disable mv-nth fn2-cns-class)))
(local (defthm cns-a-verb-store
         (implies (cns-a-store-p st)
                  (cns-a-store-p (mv-nth 1 (fn2-cns-verb-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-verb-step fn2-cns-withdraw
                                            fn2-cns-bump-auth)))))
(local (defthm cns-a-verb-declared
         (let ((verb (fn2-cns-port-verb op))
               (o (mv-nth 0 (fn2-cns-verb-step op st nil))))
           (implies (and (cns-a-store-p st) verb
                         (not (and (equal o :parked)
                                   (equal (fn2-consumer-verb-effect verb) :park))))
                    (fn2-consumer-outcome-p verb o)))
         :hints (("Goal" :in-theory (enable fn2-cns-verb-step fn2-cns-port-verb
                                            fn2-consumer-verb-p fn2-cns-class)))))
(local (defthm cns-a-verb-refusal
         (implies (and (cns-a-store-p st) (fn2-cns-port-verb op)
                       (equal (fn2-cns-class (mv-nth 0 (fn2-cns-verb-step op st nil))) :refused))
                  (cns-a-refusal-frame-p st (mv-nth 1 (fn2-cns-verb-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-verb-step fn2-cns-port-verb
                                            fn2-consumer-verb-p fn2-cns-class)))))

(local (in-theory (disable fn2-consumer-verb-effect)))
(local (defthm cns-a-timeout-outside-port
         (implies (equal (fn2-cns-class op) :timeout)
                  (not (fn2-cns-port-verb op)))
         :hints (("Goal" :in-theory (enable fn2-cns-port-verb)))))
(local (defthm cns-a-timeout-answers
         (fn2-cns-answers-declared-p (mv-nth 0 (fn2-cns-timeout st p c nil)))
         :hints (("Goal" :in-theory (enable fn2-cns-timeout fn2-cns-wait-answer
                                            fn2-cns-answers-declared-p)))))
(local (defthm cns-a-step-store
         (implies (cns-a-store-p st)
                  (cns-a-store-p (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-timeout fn2-cns-wake)))))
(local (defthm cns-a-step-answers
         (fn2-cns-answers-declared-p (mv-nth 1 (fn2-cns-step op st nil)))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-wake)))))
(local (defthm cns-a-step-declared
         (let ((verb (fn2-cns-port-verb op))
               (o (mv-nth 0 (fn2-cns-step op st nil))))
           (implies (and (cns-a-store-p st) verb
                         (not (and (equal o :parked)
                                   (equal (fn2-consumer-verb-effect verb) :park))))
                    (fn2-consumer-outcome-p verb o)))
         :hints (("Goal" :in-theory (enable fn2-cns-step)))))
(local (defthm cns-a-run-declared
         (implies (cns-a-store-p st)
                  (fn2-cns-declared-p (mv-nth 0 (fn2-cns-model-run ops st nil))))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                  :in-theory (enable fn2-cns-model-run fn2-cns-declared-p)))))
(defthm fn2-cns-outcomes-declared-proved
  (fn2-cns-outcomes-declared$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-outcomes-declared$owed fn2-cns-trace
                                     (:e fn2-cns-model-init) cns-a-store-p
                                     (:e fn2-cns-get) (:e cns-a-replays-p)))))
(fn2-owed-discharge fn2-cns-outcomes-declared fn2-cns-outcomes-declared-proved)

;; Removing a due waiter changes the wait table. Show that every state at
;; the start of a step has already answered all its due waiters.
(local (defthm cns-a-item-frame
         (implies (and (alistp st) (member key '(:waits :evidence)))
                  (equal (fn2-cns-item e reasons through (fn2-cns-model-put key v st) limit)
                         (fn2-cns-item e reasons through st limit)))
         :hints (("Goal" :in-theory (enable fn2-cns-item)))))
(local (defthm cns-a-walk-frame
         (implies (and (alistp st) (member key '(:waits :evidence)))
                  (equal (fn2-cns-walk events pos edges grants p (fn2-cns-model-put key v st)
                                       items limit acc last nil)
                         (fn2-cns-walk events pos edges grants p st items limit acc last nil)))
         :hints (("Goal" :induct (fn2-cns-walk events pos edges grants p st items limit acc last nil)
                  :in-theory (enable fn2-cns-walk)))))
(local (defthm cns-a-page-frame
         (implies (and (alistp st) (member key '(:waits :evidence)))
                  (equal (fn2-cns-page (fn2-cns-model-put key v st) p k limits nil)
                         (fn2-cns-page st p k limits nil)))
         :hints (("Goal" :in-theory (enable fn2-cns-page fn2-cns-scope-problem fn2-cns-auth
                                            fn2-cns-reg fn2-cns-model-cursor)))))
(local (defthm cns-a-none-due-frame
         (implies (and (alistp st) (member key '(:waits :evidence)))
                  (equal (fn2-cns-none-due rows (fn2-cns-model-put key v st))
                         (fn2-cns-none-due rows st)))
         :hints (("Goal" :induct (fn2-cns-none-due rows st)
                  :in-theory (enable fn2-cns-none-due)))))
(local (defthm cns-a-none-due-remove
         (implies (fn2-cns-none-due rows st)
                  (fn2-cns-none-due (remove1-equal x rows) st))
         :hints (("Goal" :induct (remove1-equal x rows) :in-theory (enable fn2-cns-none-due)))))
(local (defthm cns-a-wake-keeps-settled
         (let ((keep (mv-nth 1 (fn2-cns-wake-list rows st nil))))
           (and (true-listp keep) (fn2-cns-none-due keep st)
                (implies (and (true-listp rows) (fn2-cns-none-due rows st))
                         (equal keep rows))))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                  :in-theory (enable fn2-cns-wake-list fn2-cns-none-due)))))

(local (defthm cns-a-put-back
         (implies (and (alistp st) (assoc-equal k st))
                  (equal (put-assoc-equal k (cdr (assoc-equal k st)) st) st))))
(local (defthm cns-a-put-over-put
         (equal (put-assoc-equal k v (put-assoc-equal k w st))
                (put-assoc-equal k v st))))
(local (defun cns-a-settled-p (st)
         (let ((rows (fn2-cns-get :waits st)))
           (and (assoc-equal :waits st) (true-listp rows) (fn2-cns-none-due rows st)))))
(local (defthm cns-a-model-put-assoc
         (equal (assoc-equal key (fn2-cns-model-put k v st))
                (if (equal key k) (cons k v) (assoc-equal key st)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put)))))
(local (defthm cns-a-wake-settles
         (implies (alistp st) (cns-a-settled-p (mv-nth 1 (fn2-cns-wake st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-wake)))))
(local (defthm cns-a-wake-fixed
         (implies (and (alistp st) (cns-a-settled-p st))
                  (equal (mv-nth 1 (fn2-cns-wake st nil)) st))
         :hints (("Goal" :in-theory (enable fn2-cns-wake))
                 ("Goal'" :in-theory (enable fn2-cns-model-put fn2-cns-get)))))
(local (defthm cns-a-true-listp-remove
         (implies (true-listp rows) (true-listp (remove1-equal x rows)))))
(local (defthm cns-a-timeout-settled
         (implies (and (alistp st) (cns-a-settled-p st))
                  (cns-a-settled-p (mv-nth 1 (fn2-cns-timeout st p c nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-timeout)))))
(local (defthm cns-a-evidence-settled
         (implies (and (alistp st) (cns-a-settled-p st))
                  (cns-a-settled-p (fn2-cns-model-put :evidence v st)))))
(local (defthm cns-a-evidence-mask
         (equal (fn2-cns-model-put :evidence nil (fn2-cns-model-put :evidence v st))
                (fn2-cns-model-put :evidence nil st))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put)))))
(local (in-theory (disable cns-a-settled-p)))

(local (defthm cns-a-wake-after-evidence
         (implies (and (alistp st) (cns-a-settled-p st))
                  (equal (fn2-cns-model-put :evidence nil
                           (mv-nth 1 (fn2-cns-wake (fn2-cns-model-put :evidence v st) nil)))
                         (fn2-cns-model-put :evidence nil st)))
         :rule-classes nil))
(local (defthm cns-a-framed-wake
         (implies (and (alistp st) (cns-a-settled-p st) (cns-a-refusal-frame-p st next))
                  (equal (fn2-cns-model-put :evidence nil (mv-nth 1 (fn2-cns-wake next nil)))
                         (fn2-cns-model-put :evidence nil st)))
         :rule-classes nil
         :hints (("Goal" :in-theory (enable cns-a-refusal-frame-p)
                  :use ((:instance cns-a-wake-after-evidence (v (fn2-cns-get :evidence next))))))))
(local (defthm cns-a-step-settled
         (implies (and (cns-a-store-p st) (cns-a-settled-p st))
                  (cns-a-settled-p (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-step)))))
(local (defthm cns-a-step-refusal
         (implies (and (cns-a-store-p st) (cns-a-settled-p st) (fn2-cns-port-verb op)
                       (equal (fn2-cns-class (mv-nth 0 (fn2-cns-step op st nil))) :refused))
                  (equal (fn2-cns-model-put :evidence nil (mv-nth 2 (fn2-cns-step op st nil)))
                         (fn2-cns-model-put :evidence nil st)))
         :hints (("Goal" :in-theory (enable fn2-cns-step)
                  :use ((:instance cns-a-framed-wake (next (mv-nth 1 (fn2-cns-verb-step op st nil)))))))))
(local (defthm cns-a-run-refusal
         (implies (and (cns-a-store-p st) (cns-a-settled-p st))
                  (fn2-cns-k8 (mv-nth 0 (fn2-cns-model-run ops st nil))))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                  :in-theory (enable fn2-cns-model-run fn2-cns-k8)))))
(defthm fn2-cns-refusal-changes-nothing-proved
  (fn2-cns-refusal-changes-nothing$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-refusal-changes-nothing$owed fn2-cns-trace
                                     (:e fn2-cns-model-init) cns-a-store-p cns-a-settled-p
                                     (:e fn2-cns-get) (:e fn2-cns-none-due) (:e cns-a-replays-p)))))
(fn2-owed-discharge fn2-cns-refusal-changes-nothing fn2-cns-refusal-changes-nothing-proved)

;; An install uses the next epoch. Bound both the live registrations and
;; the historical ACK keys so that a fresh install cannot rewind an old key.
(local (defun cns-a-row-epoch (key value regs)
         (nfix (if regs (car value) (caddr key)))))
(local (defun cns-a-rows-p (rows bound regs)
         (if (atom rows) (null rows)
           (and (consp (car rows))
                (not (assoc-equal (caar rows) (cdr rows)))
                (< (cns-a-row-epoch (caar rows) (cdar rows) regs) (nfix bound))
                (cns-a-rows-p (cdr rows) bound regs)))))
(local (defthm cns-a-rows-alist
         (implies (cns-a-rows-p rows bound regs) (alistp rows))))
(local (defthm cns-a-rows-advance
         (implies (cns-a-rows-p rows bound regs)
                  (cns-a-rows-p rows (+ 1 (nfix bound)) regs))))
(local (defthm cns-a-rows-put
         (implies (and (cns-a-rows-p rows bound regs)
                       (< (cns-a-row-epoch key val regs) (nfix bound)))
                  (cns-a-rows-p (put-assoc-equal key val rows) bound regs))))
(local (defthm cns-a-rows-set
         (implies (and (cns-a-rows-p rows bound regs)
                       (< (cns-a-row-epoch key val regs) (nfix bound)))
                  (cns-a-rows-p (fn2-cns-set key val rows) bound regs))
         :hints (("Goal" :in-theory (enable fn2-cns-set)))))
(local (defthm cns-a-assoc-remove
         (implies (and (alistp rows) (not (assoc-equal key rows)))
                  (not (assoc-equal key (remove1-equal x rows))))))
(local (defthm cns-a-rows-remove
         (implies (cns-a-rows-p rows bound regs)
                  (cns-a-rows-p (remove1-equal x rows) bound regs))))
(local (defthm cns-a-lookup-epoch
         (implies (and (cns-a-rows-p rows bound regs) (assoc-equal key rows))
                  (< (cns-a-row-epoch key (cdr (assoc-equal key rows)) regs) (nfix bound)))))
(local (defthm cns-a-reg-epoch-bound
         (implies (and (cns-a-rows-p rows bound t) (fn2-cns-at key rows))
                  (< (nfix (fn2-cns-reg-epoch (fn2-cns-at key rows))) (nfix bound)))
         :hints (("Goal" :in-theory (enable fn2-cns-reg-epoch fn2-cns-at nth)
                  :use ((:instance cns-a-lookup-epoch (regs t)))))))
(local (defthm cns-a-fresh-ack
         (implies (cns-a-rows-p rows bound nil)
                  (not (fn2-cns-at (list p c (nfix bound)) rows)))
         :hints (("Goal" :in-theory (enable fn2-cns-at)
                  :use ((:instance cns-a-lookup-epoch
                                   (regs nil) (key (list p c (nfix bound)))))))))

(local (defun cns-a-ack-state-p (st)
         (let ((bound (fn2-cns-get :epoch st)))
           (and (alistp st) (cns-a-rows-p (fn2-cns-get :regs st) bound t)
                (cns-a-rows-p (fn2-cns-get :acks st) bound nil)))))
(local (defun cns-a-pos (key st)
         (nfix (fn2-cns-at key (fn2-cns-get :acks st)))))
(local (defthm cns-a-at-set
         (implies (alistp rows)
                  (equal (fn2-cns-at k (fn2-cns-set key v rows))
                         (if (equal k key) v (fn2-cns-at k rows))))
         :hints (("Goal" :in-theory (enable fn2-cns-at fn2-cns-set)))))
(local (defthm cns-a-ack-state-put
         (implies (and (cns-a-ack-state-p st) (not (member k '(:regs :acks :epoch))))
                  (cns-a-ack-state-p (fn2-cns-model-put k v st)))))
(local (defthm cns-a-pos-put
         (implies (and (alistp st) (not (equal k :acks)))
                  (equal (cns-a-pos key (fn2-cns-model-put k v st))
                         (cns-a-pos key st)))))
(local (defthm cns-a-ack-state-alist
         (implies (cns-a-ack-state-p st) (alistp st))))
(local (defthm cns-a-nfix-nat (implies (natp x) (equal (nfix x) x))))
(local (in-theory (disable nfix |(+ y x)|)))
(local (defthm cns-a-install-monotone
         (implies (cns-a-ack-state-p st)
                  (let ((next (mv-nth 1 (fn2-cns-install st p c edges pos qv))))
                    (and (cns-a-ack-state-p next)
                         (<= (cns-a-pos key st) (cns-a-pos key next)))))
         :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (fn2-cns-install fn2-cns-model-charge)
                                  (cns-a-rows-p))))))
(local (defthm cns-a-scope-needs-registration
         (implies (not (fn2-cns-reg st p (fn2-cns-cursor-consumer k)))
                  (fn2-cns-scope-problem st p k nil))
         :hints (("Goal" :in-theory (enable fn2-cns-scope-problem)))))
(local (defthm cns-a-known-epoch
         (implies (and (cns-a-ack-state-p st) (fn2-cns-reg st p c))
                  (< (nfix (fn2-cns-reg-epoch (fn2-cns-reg st p c)))
                     (nfix (fn2-cns-get :epoch st))))
         :hints (("Goal" :in-theory (enable fn2-cns-reg)))))
(local (defthm cns-a-ack-update
         (let* ((epoch (fn2-cns-reg-epoch (fn2-cns-reg st p c)))
                (id (list p c epoch))
                (next (fn2-cns-model-put :acks (fn2-cns-set id pos (fn2-cns-get :acks st)) st)))
           (implies (and (cns-a-ack-state-p st) (fn2-cns-reg st p c)
                         (<= (fn2-cns-acked st p c epoch) (nfix pos)))
                    (and (cns-a-ack-state-p next)
                         (<= (cns-a-pos key st) (cns-a-pos key next)))))
         :hints (("Goal" :do-not-induct t :in-theory (e/d (fn2-cns-acked fn2-cns-reg)
                                                           (cns-a-rows-p))))))

(local (defthm cns-a-remove-registration
         (implies (cns-a-ack-state-p st)
                  (cns-a-ack-state-p
                   (fn2-cns-model-put :regs (remove1-equal x (fn2-cns-get :regs st)) st)))))
(local (defthm cns-a-position-natural
         (natp (fn2-cns-cursor-position k))
         :rule-classes :type-prescription
         :hints (("Goal" :in-theory (enable fn2-cns-cursor-position)))))
(local (in-theory (disable cns-a-ack-state-p cns-a-pos cns-a-rows-p)))
(local
 (defmacro cns-a-check-positions (verb args &rest extra)
   (let* ((fn (packn (list 'fn2-cns- verb))) (call (cons fn args)))
     `(defthm ,(packn (list 'cns-a-positions- verb))
        (implies (cns-a-ack-state-p st)
                 (let ((next (mv-nth 1 ,call)))
                   (and (cns-a-ack-state-p next)
                        (<= (cns-a-pos key st) (cns-a-pos key next)))))
        :hints (("Goal" :do-not-induct t
                 :in-theory (enable ,fn fn2-cns-admit fn2-cns-model-charge ,@extra)))))))
(local (cns-a-check-positions register (st p c streams start nil)))
(local (cns-a-check-positions rebase (st p k streams start nil)))
(local (cns-a-check-positions unregister (st p k nil)))
(local (cns-a-check-positions read (st p k limits nil)))
(local (cns-a-check-positions wait (st p k limits nil)))
(local (cns-a-check-positions ack (st p k nil)))
(local (cns-a-check-positions position (st p c nil)))
(local (cns-a-check-positions status (st p c nil)))
(local (cns-a-check-positions fetch (st p reference nil)))
(local (cns-a-check-positions append (st p stream article op nil)))
(local (cns-a-check-positions verb-step (op st nil) fn2-cns-withdraw fn2-cns-bump-auth))

(local (defthm cns-a-positions-step
         (implies (cns-a-ack-state-p st)
                  (let ((next (mv-nth 2 (fn2-cns-step op st nil))))
                    (and (cns-a-ack-state-p next)
                         (<= (cns-a-pos key st) (cns-a-pos key next)))))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-timeout fn2-cns-wake)))))
(local (defthm cns-a-assoc-member
         (implies (and (cns-a-rows-p rows bound nil) (member-equal row rows))
                  (equal (assoc-equal (car row) rows) row))
         :hints (("Goal" :induct (member-equal row rows) :in-theory (enable cns-a-rows-p)))))
(local (defthm cns-a-pos-of-row
         (implies (and (cns-a-ack-state-p st) (member-equal row (fn2-cns-get :acks st)))
                  (equal (cns-a-pos (car row) st) (nfix (cdr row))))
         :hints (("Goal" :in-theory (enable cns-a-ack-state-p cns-a-pos fn2-cns-at)))))
(local (defthm cns-a-step-row
         (implies (and (cns-a-ack-state-p st) (member-equal row (fn2-cns-get :acks st)))
                  (<= (nfix (cdr row))
                      (nfix (fn2-cns-at (car row) (fn2-cns-get :acks (mv-nth 2 (fn2-cns-step op st nil)))))))
         :hints (("Goal" :use ((:instance cns-a-positions-step (key (car row)))
                               (:instance cns-a-pos-of-row))
                  :in-theory (e/d (cns-a-pos) (cns-a-positions-step cns-a-pos-of-row))))))
(local (defthm cns-a-step-rows
         (implies (and (cns-a-ack-state-p st) (subsetp-equal rows (fn2-cns-get :acks st)))
                  (fn2-cns-acks-ge rows (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :induct (subsetp-equal rows (fn2-cns-get :acks st))
                  :expand ((subsetp-equal rows (fn2-cns-get :acks st)))
                  :in-theory (enable fn2-cns-acks-ge)))))
(local (defthm cns-a-subset-extend
         (implies (subsetp-equal xs ys) (subsetp-equal xs (cons x ys)))))
(local (defthm cns-a-subset-self (subsetp-equal rows rows)))
(local (defthm cns-a-run-positions
         (implies (cns-a-ack-state-p st)
                  (fn2-cns-k2 (mv-nth 0 (fn2-cns-model-run ops st nil))))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                  :in-theory (enable fn2-cns-model-run fn2-cns-k2)))))
(defthm fn2-cns-ack-monotone-proved
  (fn2-cns-ack-monotone$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-ack-monotone$owed fn2-cns-trace
                                     (:e fn2-cns-model-init) cns-a-ack-state-p
                                     (:e fn2-cns-get) (:e cns-a-rows-p)))))
(fn2-owed-discharge fn2-cns-ack-monotone fn2-cns-ack-monotone-proved)
