; Consumer-model trace invariants.
(in-package "ACL2")
(include-book "owed-consumer")
(include-book "owed-discharge")

; K5 counterexample.  A retry after withdrawal returns the original accepted
; append outcome.  At that step ARTICLE already returns nil for "<m>".
; The exact ops are ((:grant p :append "room")
;                    (append p "room" ("<m>" "body" nil) request)
;                    (:withdraw p "<m>")
;                    (append p "room" ("<m>" "body" nil) request)).
(local
 (assert-event
  (let* ((post '(append p "room" ("<m>" "body" nil) request))
         (ops (list '(:grant p :append "room") post '(:withdraw p "<m>") post))
         (trace (fn2-cns-trace ops nil))
         (first-post (nth 1 trace))
         (retry (nth 3 trace)))
    (and (equal (fn2-cns-class (nth 1 first-post)) :accepted)
         (equal (nth 1 retry) (nth 1 first-post))
         (equal (fn2-cns-nntp-article (nth 4 first-post) "<m>" nil) "body")
         (equal (fn2-cns-nntp-article (nth 4 retry) "<m>" nil) nil)
         (not (fn2-cns-k5 trace nil))))))

(local (in-theory
        (union-theories (current-theory 'fn2-cns-class)
                        (intersection-theories (executable-counterpart-theory :here)
                                               (current-theory :here)))))

(local (defthm cns-b-alistp-put
         (implies (alistp st) (alistp (fn2-cns-model-put k v st)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-put)))))

(local (defthm cns-b-assoc-put
         (equal (assoc-equal j (put-assoc-equal k v st))
                (if (equal j k) (cons k v) (assoc-equal j st)))))

(local (defthm cns-b-alistp-put-assoc
         (implies (alistp st) (alistp (put-assoc-equal k v st)))))

(local (defthm cns-b-get-put
         (implies (alistp st)
                  (equal (fn2-cns-get j (fn2-cns-model-put k v st))
                         (if (equal j k) v (fn2-cns-get j st))))
         :hints (("Goal" :in-theory (enable fn2-cns-get fn2-cns-model-put)))))

; Updating the wait table leaves every input of a page read intact.
(local (defthm cns-b-item-waits
         (implies (alistp st)
                  (equal (fn2-cns-item e why through (fn2-cns-model-put :waits v st) octets)
                         (fn2-cns-item e why through st octets)))
         :hints (("Goal" :in-theory (enable fn2-cns-item)))))

(local (defthm cns-b-walk-waits
         (implies (alistp st)
                  (equal (fn2-cns-walk events p edges grants principal
                                       (fn2-cns-model-put :waits v st) items octets acc last fault)
                         (fn2-cns-walk events p edges grants principal st items octets acc last fault)))
         :hints (("Goal" :induct (fn2-cns-walk events p edges grants principal st items octets acc last fault)
                         :in-theory (enable fn2-cns-walk)))))

(local (defthm cns-b-page-waits
         (implies (alistp st)
                  (equal (fn2-cns-page (fn2-cns-model-put :waits v st) p k limits fault)
                         (fn2-cns-page st p k limits fault)))
         :hints (("Goal" :in-theory (enable fn2-cns-page fn2-cns-scope-problem
                                             fn2-cns-model-cursor fn2-cns-reg fn2-cns-auth)))))

(local (defthm cns-b-none-due-waits
         (implies (alistp st)
                  (equal (fn2-cns-none-due rows (fn2-cns-model-put :waits v st))
                         (fn2-cns-none-due rows st)))
         :hints (("Goal" :in-theory (enable fn2-cns-none-due)))))

(local (defthm cns-b-wake-keeps-idle
         (fn2-cns-none-due (mv-nth 1 (fn2-cns-wake-list rows st nil)) st)
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list fn2-cns-none-due)))))

(local (defthm cns-b-none-due-remove
         (implies (fn2-cns-none-due rows st)
                  (fn2-cns-none-due (remove1-equal row rows) st))
         :hints (("Goal" :in-theory (enable fn2-cns-none-due)))))

(local (defthm cns-b-answers-waits
         (implies (alistp st2)
                  (equal (fn2-cns-answers-are-reads answers st (fn2-cns-model-put :waits v st2))
                         (fn2-cns-answers-are-reads answers st st2)))
         :hints (("Goal" :in-theory (enable fn2-cns-answers-are-reads)))))

; Registration and wait tables have unique (principal . consumer) keys.
(local (defun cns-b-rowsp (rows)
         (if (atom rows) (null rows)
           (and (consp (car rows)) (consp (caar rows)) (cdar rows)
                (not (assoc-equal (caar rows) (cdr rows)))
                (cns-b-rowsp (cdr rows))))))

(local (defthm cns-b-rows-alistp
         (implies (cns-b-rowsp rows) (alistp rows))))

(local (defthm cns-b-rows-put
         (implies (and (cns-b-rowsp rows) (consp key) val)
                  (cns-b-rowsp (fn2-cns-set key val rows)))
         :hints (("Goal" :in-theory (enable fn2-cns-set)))))

(local (defthm cns-b-assoc-remove
         (implies (and (alistp rows) (not (assoc-equal key rows)))
                  (not (assoc-equal key (remove1-equal row rows))))))

(local (defthm cns-b-rows-remove
         (implies (cns-b-rowsp rows) (cns-b-rowsp (remove1-equal row rows)))))

(local (defthm cns-b-assoc-wake-keep
         (implies (and (alistp rows) (not (assoc-equal key rows)))
                  (not (assoc-equal key (mv-nth 1 (fn2-cns-wake-list rows st nil)))))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list)))))

(local (defthm cns-b-rows-wake-keep
         (implies (cns-b-rowsp rows) (cns-b-rowsp (mv-nth 1 (fn2-cns-wake-list rows st nil))))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list)))))

; Numbering commits as well as article and withdrawal events makes appending
; at frontier + 1 preserve both ordering and lookup by position.

(local (defun cns-b-logp (log start)
         (if (atom log) (null log)
           (let* ((e (car log)) (kind (fn2-cns-ev-kind e)) (mid (fn2-cns-ev-mid e)))
             (and (equal (fn2-cns-ev-pos e) (+ 1 (nfix start)))
                  (or (and (eq kind :article) mid)
                      (eq kind :withdraw)
                      (and (eq kind :commit) (not mid)))
                  (cns-b-logp (cdr log) (+ 1 (nfix start))))))))

(local (defthm cns-b-log-append
         (implies (and (cns-b-logp log start) (natp start))
                  (equal (cns-b-logp (append log tail) start)
                         (cns-b-logp tail (+ start (len log)))))))

(local (defthm cns-b-len-append
         (equal (len (append x y)) (+ (len x) (len y)))))

(local (defthm cns-b-pad-valid
         (implies (and (cns-b-logp log 0) (equal from (1+ (len log))))
                  (cns-b-logp (fn2-cns-pad log from to) 0))
         :hints (("Goal" :induct (fn2-cns-pad log from to)
                         :in-theory (enable fn2-cns-pad fn2-cns-ev-pos fn2-cns-ev-mid fn2-cns-ev-kind)))))

(local (defun cns-b-statep (st)
         (and (alistp st) (cns-b-logp (fn2-cns-get :log st) 0)
              (cns-b-rowsp (fn2-cns-get :regs st))
              (cns-b-rowsp (fn2-cns-get :waits st)))))

(local (defthm cns-b-state-facts
         (implies (cns-b-statep st)
                  (and (alistp st) (cns-b-logp (fn2-cns-get :log st) 0)
                       (cns-b-rowsp (fn2-cns-get :regs st))
                       (cns-b-rowsp (fn2-cns-get :waits st))))))

(local (defthm cns-b-state-put
         (implies (and (cns-b-statep st)
                       (or (not (equal k :waits)) (cns-b-rowsp val))
                       (or (not (equal k :regs)) (cns-b-rowsp val))
                       (or (not (equal k :log)) (cns-b-logp val 0)))
                  (cns-b-statep (fn2-cns-model-put k val st)))))

(local (in-theory (disable cns-b-statep cns-b-rowsp cns-b-logp)))

(local (defthm cns-b-mint-nonempty
         (stringp (fn2-cns-mint p op pos))
         :hints (("Goal" :in-theory (enable fn2-cns-mint)))
         :rule-classes :type-prescription))

(local (defun cns-b-agree (rows table)
         (if (atom rows) t
           (and (equal (cdr (assoc-equal (caar rows) table)) (cdar rows))
                (cdar rows)
                (cns-b-agree (cdr rows) table)))))

(local (defthm cns-b-agree-cons
         (implies (and (alistp rows) (not (assoc-equal key rows)))
                  (equal (cns-b-agree rows (cons (cons key val) table))
                         (cns-b-agree rows table)))))

(local (defthm cns-b-agree-self
         (implies (cns-b-rowsp rows) (cns-b-agree rows rows))
         :hints (("Goal" :induct (len rows) :in-theory (enable cns-b-rowsp)))))

(local (defthm cns-b-wake-reads
         (implies (and (alistp (fn2-cns-get :waits before))
                       (cns-b-agree rows (fn2-cns-get :waits before)))
                  (fn2-cns-answers-are-reads (mv-nth 0 (fn2-cns-wake-list rows st nil)) before st))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list fn2-cns-wait-answer
                                            fn2-cns-answers-are-reads fn2-cns-at)))))

(local (defthm cns-b-idle-set
         (implies (and (cns-b-rowsp rows) (fn2-cns-none-due rows st)
                       (equal (fn2-cns-class (fn2-cns-page st p k limits nil)) :accepted)
                       (not (fn2-cns-page-items (fn2-cns-page st p k limits nil))))
                  (fn2-cns-none-due (fn2-cns-set (cons p c) (list k limits page) rows) st))
         :hints (("Goal" :induct (len rows)
                         :in-theory (enable fn2-cns-set fn2-cns-none-due cns-b-rowsp)))))

(local (defthm cns-b-idle-no-answers
         (implies (fn2-cns-none-due rows st)
                  (equal (mv-nth 0 (fn2-cns-wake-list rows st nil)) nil))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list fn2-cns-none-due)))))

(local (defthm cns-b-admit-state
         (equal (mv-nth 1 (fn2-cns-admit verb st p ok amount nil)) st)
         :hints (("Goal" :in-theory (enable fn2-cns-admit)))))

(local (defthm cns-b-wait-keeps-idle
         (implies (and (cns-b-statep st)
                       (fn2-cns-none-due (fn2-cns-get :waits st) st))
                  (let ((after (mv-nth 1 (fn2-cns-wait st p k limits nil))))
                    (fn2-cns-none-due (fn2-cns-get :waits after) after)))
         :hints (("Goal" :in-theory (enable fn2-cns-wait)))))

(local (defthm cns-b-verb-wait-idle
         (implies (and (equal (fn2-cns-class op) 'wait) (cns-b-statep st)
                       (fn2-cns-none-due (fn2-cns-get :waits st) st))
                  (let ((after (mv-nth 1 (fn2-cns-verb-step op st nil))))
                    (fn2-cns-none-due (fn2-cns-get :waits after) after)))
         :hints (("Goal" :in-theory (enable fn2-cns-verb-step)))))

(local
 (defmacro cns-b-frame (name call returns-mv &key (waits 't) enable)
   (let ((after (if returns-mv `(mv-nth 1 ,call) call)))
     `(defthm ,name
        (implies (cns-b-statep st)
                 (and (cns-b-statep ,after)
                      ,@(and waits `((equal (fn2-cns-get :waits ,after)
                                            (fn2-cns-get :waits st))))))
        :hints (("Goal" :in-theory (enable ,(car call) ,@enable)))))))

(local (cns-b-frame cns-b-charge-frame (fn2-cns-model-charge st p amount) nil))

(local (cns-b-frame cns-b-auth-frame (fn2-cns-bump-auth p st) nil))

(local (cns-b-frame cns-b-install-frame (fn2-cns-install st p c edges pos qv) t))

(local (cns-b-frame cns-b-register-frame (fn2-cns-register st p c streams start nil) t))

(local (cns-b-frame cns-b-rebase-frame (fn2-cns-rebase st p k streams start nil) t))

(local (cns-b-frame cns-b-unregister-frame (fn2-cns-unregister st p k nil) t))

(local (cns-b-frame cns-b-read-frame (fn2-cns-read st p k limits nil) t))

(local (cns-b-frame cns-b-wait-frame (fn2-cns-wait st p k limits nil) t :waits nil))

(local (cns-b-frame cns-b-ack-frame (fn2-cns-ack st p k nil) t))

(local (cns-b-frame cns-b-position-frame (fn2-cns-position st p c nil) t))

(local (cns-b-frame cns-b-status-frame (fn2-cns-status st p c nil) t))

(local (cns-b-frame cns-b-fetch-frame (fn2-cns-fetch st p reference nil) t))

(local (cns-b-frame cns-b-append-frame (fn2-cns-append st p stream article op nil) t
                    :enable (fn2-cns-frontier cns-b-logp fn2-cns-ev-pos fn2-cns-ev-kind fn2-cns-ev-mid)))

(local (cns-b-frame cns-b-withdraw-frame (fn2-cns-withdraw st p mid) nil
                    :enable (fn2-cns-frontier cns-b-logp fn2-cns-ev-pos fn2-cns-ev-kind fn2-cns-ev-mid)))

(local (cns-b-frame cns-b-verb-valid (fn2-cns-verb-step op st nil) t :waits nil
                    :enable (fn2-cns-frontier)))

(local (defthm cns-b-verb-waits
         (implies (and (cns-b-statep st) (not (equal (fn2-cns-class op) 'wait)))
                  (equal (fn2-cns-get :waits (mv-nth 1 (fn2-cns-verb-step op st nil)))
                         (if (equal (fn2-cns-class op) :crash) nil (fn2-cns-get :waits st))))
         :hints (("Goal" :in-theory (enable fn2-cns-verb-step)))))

(local (cns-b-frame cns-b-timeout-frame (fn2-cns-timeout st p c nil) t :waits nil))

(local (cns-b-frame cns-b-wake-frame (fn2-cns-wake st nil) t :waits nil))

(local (defthm cns-b-step-valid
         (implies (cns-b-statep st) (cns-b-statep (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-step)))))

(local (defthm cns-b-step-idle
         (implies (and (cns-b-statep st) (fn2-cns-none-due (fn2-cns-get :waits st) st))
                  (let ((after (mv-nth 2 (fn2-cns-step op st nil))))
                    (fn2-cns-none-due (fn2-cns-get :waits after) after)))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-wake fn2-cns-timeout)))))

(local (defthm cns-b-wake-reads-frame
         (implies (and (cns-b-statep st) (cns-b-statep before)
                       (or (equal (fn2-cns-get :waits st) (fn2-cns-get :waits before))
                           (fn2-cns-none-due (fn2-cns-get :waits st) st)))
                  (fn2-cns-answers-are-reads (mv-nth 0 (fn2-cns-wake st nil))
                                             before (mv-nth 1 (fn2-cns-wake st nil))))
         :hints (("Goal" :use ((:instance cns-b-wake-reads (rows (fn2-cns-get :waits before))))
                         :in-theory (enable fn2-cns-wake fn2-cns-answers-are-reads)))))

(local (defthm cns-b-timeout-reads
         (implies (cns-b-statep st)
                  (fn2-cns-answers-are-reads (mv-nth 0 (fn2-cns-timeout st p c nil))
                                             st (mv-nth 1 (fn2-cns-timeout st p c nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-timeout fn2-cns-wait-answer fn2-cns-answers-are-reads)))))

(local (defthm cns-b-mv-cons
         (equal (mv-nth n (cons x xs))
                (if (zp n) x (mv-nth (1- n) xs)))))

(local (in-theory (disable mv-nth fn2-cns-class)))

(local (defthm cns-b-step-reads
         (implies (and (cns-b-statep st) (fn2-cns-none-due (fn2-cns-get :waits st) st))
                  (fn2-cns-answers-are-reads (mv-nth 1 (fn2-cns-step op st nil))
                                             st (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :cases ((equal (fn2-cns-class op) 'wait)
                                 (equal (fn2-cns-class op) :crash))
                         :in-theory (enable fn2-cns-step fn2-cns-none-due)))))

(local (defthm cns-b-run-reads
         (implies (and (cns-b-statep st) (fn2-cns-none-due (fn2-cns-get :waits st) st))
                  (let ((trace (mv-nth 0 (fn2-cns-model-run ops st nil))))
                    (and (fn2-cns-k4 trace) (fn2-cns-k4b trace))))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                         :in-theory (enable fn2-cns-model-run fn2-cns-k4 fn2-cns-k4b)))))

(defthm fn2-cns-wait-is-read-proved
  (fn2-cns-wait-is-read$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-wait-is-read$owed fn2-cns-trace))))

(fn2-owed-discharge fn2-cns-wait-is-read fn2-cns-wait-is-read-proved)

; K7. Recover the source event by position before checking its readable streams.
(local (defthm cns-b-member-position
         (implies (and (cns-b-logp log start) (member-equal e log))
                  (< (nfix start) (fn2-cns-ev-pos e)))
         :hints (("Goal" :induct (cns-b-logp log start)
                         :in-theory (enable cns-b-logp)))
         :rule-classes (:rewrite :linear)))

(local (defthm cns-b-event-at-member
         (implies (and (cns-b-logp log start) (member-equal e log))
                  (equal (fn2-cns-event-at (fn2-cns-ev-pos e) log) e))
         :hints (("Goal" :induct (cns-b-logp log start)
                         :in-theory (enable cns-b-logp fn2-cns-event-at)))))

(local (defthm cns-b-no-nil-mid
         (implies (cns-b-logp log start) (equal (fn2-cns-article-of nil log) nil))
         :hints (("Goal" :induct (cns-b-logp log start)
                         :in-theory (enable cns-b-logp fn2-cns-article-of)))))

(local (defthm cns-b-member-kind
         (implies (and (cns-b-logp log start) (member-equal e log)
                       (not (equal (fn2-cns-ev-kind e) :article))
                       (not (equal (fn2-cns-ev-kind e) :withdraw)))
                  (not (fn2-cns-ev-mid e)))
         :hints (("Goal" :induct (cns-b-logp log start)
                         :in-theory (enable cns-b-logp)))))

(local (defthm cns-b-reasons-readable
         (implies (not (fn2-cns-readable grants p streams))
                  (not (fn2-cns-article-reasons streams to edges grants p pos)))
         :hints (("Goal" :in-theory (enable fn2-cns-article-reasons fn2-cns-live-readable)))))

(local (defthm cns-b-item-position
         (and (equal (car (fn2-cns-item e reasons through st octets)) (fn2-cns-ev-pos e))
              (equal (fn2-cns-item-pos (fn2-cns-item e reasons through st octets)) (fn2-cns-ev-pos e)))
         :hints (("Goal" :in-theory (enable fn2-cns-item fn2-cns-item-pos fn2-cns-ev-pos)))))

(local (defthm cns-b-allow-item
         (implies (and (cns-b-logp (fn2-cns-get :log st) 0)
                       (member-equal e (fn2-cns-get :log st))
                       (fn2-cns-reasons e edges (fn2-cns-get :grants st) p (fn2-cns-get :log st))
                       (fn2-cns-items-allowed acc p st))
                  (fn2-cns-items-allowed
                   (cons (fn2-cns-item e reasons through st octets) acc) p st))
         :hints (("Goal" :use ((:instance cns-b-event-at-member (log (fn2-cns-get :log st)) (start 0))
                               (:instance cns-b-no-nil-mid (log (fn2-cns-get :log st)) (start 0))
                               (:instance cns-b-member-kind (log (fn2-cns-get :log st)) (start 0)))
                         :in-theory (enable fn2-cns-items-allowed fn2-cns-reasons)))))

(local (defthm cns-b-allow-revappend
         (implies (and (fn2-cns-items-allowed acc p st)
                       (fn2-cns-items-allowed tail p st))
                  (fn2-cns-items-allowed (revappend acc tail) p st))
         :hints (("Goal" :induct (revappend acc tail)
                         :in-theory (enable fn2-cns-items-allowed)))))

(local (defthm cns-b-empty-allowed
         (fn2-cns-items-allowed nil p st)
         :hints (("Goal" :in-theory (enable fn2-cns-items-allowed)))))

(local (defthm cns-b-walk-allowed
         (implies (and (cns-b-logp (fn2-cns-get :log st) 0)
                       (subsetp-equal events (fn2-cns-get :log st))
                       (true-listp acc)
                       (fn2-cns-items-allowed acc p st))
                  (fn2-cns-items-allowed
                   (mv-nth 0 (fn2-cns-walk events from edges (fn2-cns-get :grants st)
                                           p st items octets acc last nil)) p st))
         :hints (("Goal" :induct (fn2-cns-walk events from edges (fn2-cns-get :grants st)
                                               p st items octets acc last nil)
                         :in-theory (enable fn2-cns-walk)))))

(local (defthm cns-b-subset-cons
         (implies (subsetp-equal xs ys) (subsetp-equal xs (cons y ys)))))

(local (defthm cns-b-subset-self (subsetp-equal xs xs)))

(local (defthm cns-b-page-allowed
         (implies (cns-b-statep st)
                  (fn2-cns-items-allowed (fn2-cns-page-items (fn2-cns-page st p k limits nil)) p st))
         :hints (("Goal" :in-theory (enable fn2-cns-page fn2-cns-page-items fn2-cns-class
                                             fn2-cns-items-allowed)))))

(local (defthm cns-b-items-waits
         (implies (alistp st)
                  (equal (fn2-cns-items-allowed items p (fn2-cns-model-put :waits v st))
                         (fn2-cns-items-allowed items p st)))
         :hints (("Goal" :in-theory (enable fn2-cns-items-allowed)))))

(local (defthm cns-b-answers-allowed-waits
         (implies (alistp st)
                  (equal (fn2-cns-answers-allowed answers (fn2-cns-model-put :waits v st))
                         (fn2-cns-answers-allowed answers st)))
         :hints (("Goal" :in-theory (enable fn2-cns-answers-allowed)))))

(local (defthm cns-b-wake-allowed
         (implies (cns-b-statep st)
                  (fn2-cns-answers-allowed (mv-nth 0 (fn2-cns-wake-list rows st nil)) st))
         :hints (("Goal" :induct (fn2-cns-wake-list rows st nil)
                         :in-theory (enable fn2-cns-wake-list fn2-cns-wait-answer fn2-cns-answers-allowed)))))

(local (defthm cns-b-step-answers-allowed
         (implies (cns-b-statep st)
                  (fn2-cns-answers-allowed (mv-nth 1 (fn2-cns-step op st nil))
                                           (mv-nth 2 (fn2-cns-step op st nil))))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-wake fn2-cns-timeout
                                             fn2-cns-wait-answer fn2-cns-answers-allowed)))))

(local (defthm cns-b-read-wait-allowed
         (implies (and (cns-b-statep st) (member (fn2-cns-class op) '(read wait)))
                  (fn2-cns-items-allowed (fn2-cns-page-items (mv-nth 0 (fn2-cns-step op st nil)))
                                         (nth 1 op) st))
         :hints (("Goal" :in-theory (enable fn2-cns-step fn2-cns-verb-step fn2-cns-read fn2-cns-wait
                                             fn2-cns-admit fn2-consumer-admit
                                             fn2-cns-class fn2-cns-items-allowed)))))

(local (defthm cns-b-run-allowed
         (implies (cns-b-statep st)
                  (fn2-cns-k7 (mv-nth 0 (fn2-cns-model-run ops st nil))))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                         :in-theory (enable fn2-cns-model-run fn2-cns-k7)))))

(defthm fn2-cns-authority-current-proved
  (fn2-cns-authority-current$owed ops)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-authority-current$owed fn2-cns-trace))))

(fn2-owed-discharge fn2-cns-authority-current fn2-cns-authority-current-proved)

; K1. START counts the events before this suffix. FROM is the client cursor.
; The scan induction advances START and the same accumulator as the page walk.
(local (defmacro cns-b-scan ()
         '(fn2-cns-walk events from edges grants p st items octets acc (max from start) nil)))

(local (defmacro cns-b-selected (events from)
         `(fn2-cns-selected-positions ,events (fn2-cns-get :log st) edges grants p ,from)))

(local (defun cns-b-scan-induct (events start from edges grants p st items octets acc)
         (declare (xargs :verify-guards nil))
         (if (atom events) (list start from edges grants p st items octets acc)
           (let* ((e (car events))
                  (reasons (and (< (nfix from) (fn2-cns-ev-pos e))
                                (fn2-cns-reasons e edges grants p (fn2-cns-get :log st)))))
             (cond ((not reasons)
                    (cns-b-scan-induct (cdr events) (1+ (nfix start)) from edges grants p st items octets acc))
                   ((<= (nfix items) (len acc)) nil)
                   (t (cns-b-scan-induct
                       (cdr events) (1+ (nfix start)) from edges grants p st items octets
                       (cons (fn2-cns-item e reasons (fn2-cns-through e edges grants p (fn2-cns-get :log st))
                                           st octets) acc))))))))

(local (defthm cns-b-scan-bounds
         (implies (and (cns-b-logp events start) (natp start) (natp from))
                  (and (natp (mv-nth 2 (cns-b-scan)))
                       (<= (max from start) (mv-nth 2 (cns-b-scan)))
                       (implies (mv-nth 1 (cns-b-scan)) (< from (+ start (len events))))))
         :hints (("Goal" :induct (cns-b-scan-induct events start from edges grants p st items octets acc)
                         :in-theory (enable fn2-cns-walk cns-b-logp)))
         :rule-classes nil))

(local (defthm cns-b-scan-progress
         (implies (and (cns-b-logp events start) (natp start) (natp from)
                       (posp items) (or (not (consp acc)) (< from start))
                       (mv-nth 1 (cns-b-scan)))
                  (< from (mv-nth 2 (cns-b-scan))))
         :hints (("Goal" :induct (cns-b-scan-induct events start from edges grants p st items octets acc)
                         :in-theory (enable fn2-cns-walk cns-b-logp)))
         :rule-classes nil))

(local (defthm cns-b-append-assoc
         (equal (append (append x y) z) (append x (append y z)))))

(local (defthm cns-b-strips-append
         (equal (strip-cars (append x y)) (append (strip-cars x) (strip-cars y)))))

(local (defthm cns-b-revappend-append
         (equal (append (revappend xs ys) zs)
                (revappend xs (append ys zs)))
         :hints (("Goal" :induct (revappend xs ys)))))

(local (defthm cns-b-reverse-cons
         (implies (true-listp acc)
                  (equal (reverse (cons i acc)) (append (reverse acc) (list i))))))

(local (defthm cns-b-append-strip-nil
         (equal (append (strip-cars x) nil) (strip-cars x))))

(local (defun cns-b-above (events floor)
         (if (atom events) t
           (and (<= floor (fn2-cns-ev-pos (car events))) (cns-b-above (cdr events) floor)))))

(local (defthm cns-b-log-above
         (implies (and (cns-b-logp events start) (natp start) (<= floor start))
                  (cns-b-above events floor))
         :hints (("Goal" :induct (cns-b-logp events start) :in-theory (enable cns-b-logp)))))

(local (defthm cns-b-ev-pos-nat (natp (fn2-cns-ev-pos e))
         :hints (("Goal" :in-theory (enable fn2-cns-ev-pos))) :rule-classes :type-prescription))

(local (defthm cns-b-walk-floor
         (implies (and (natp last) (<= floor last)
                       (or (<= floor (nfix from)) (cns-b-above events floor)))
                  (let ((next (mv-nth 2 (fn2-cns-walk events from edges grants p st items octets acc last nil))))
                    (and (natp next) (<= floor next))))
         :hints (("Goal" :induct (fn2-cns-walk events from edges grants p st items octets acc last nil)
                         :in-theory (enable fn2-cns-walk)))
         :rule-classes nil))

(local (defthm cns-b-walk-next-bound
         (implies (and (natp last) (or (<= last (nfix from)) (cns-b-above events last)))
                  (let ((next (mv-nth 2 (fn2-cns-walk events from edges grants p st items octets acc last nil))))
                    (<= last next)))
         :hints (("Goal" :use ((:instance cns-b-walk-floor (floor last)))))
         :rule-classes (:rewrite :linear)))

(local (defthm cns-b-select-before-start
         (implies (and (cns-b-logp events start) (natp start)
                       (<= (nfix from) start) (<= (nfix other) start))
                  (equal (cns-b-selected events from) (cns-b-selected events other)))
         :hints (("Goal" :induct (cns-b-logp events start)
                         :in-theory (enable cns-b-logp fn2-cns-selected-positions)))
         :rule-classes nil))

(local (defthm cns-b-log-step
         (implies (and (cns-b-logp events start) (consp events) (natp start))
                  (and (equal (fn2-cns-ev-pos (car events)) (+ 1 start))
                       (cns-b-logp (cdr events) (+ 1 start))))
         :hints (("Goal" :in-theory (enable cns-b-logp)))))

(local (defthm cns-b-walk-next-natural
         (implies (natp last)
                  (natp (mv-nth 2 (fn2-cns-walk events from edges grants p st items octets acc last nil))))
         :hints (("Goal" :use ((:instance cns-b-walk-floor (floor 0)))))
         :rule-classes :type-prescription))

(local (defthm cns-b-select-before-zero
         (implies (and (syntaxp (not (equal from ''0)))
                       (cns-b-logp events start) (natp start) (<= (nfix from) start))
                  (equal (cns-b-selected events from) (cns-b-selected events 0)))
         :hints (("Goal" :use ((:instance cns-b-select-before-start (other 0)))))))

; The returned items and the selection after NEXT reconstruct the entire
; selection, including the items already collected on entry to this suffix.
(local (defthm cns-b-scan-partition
         (implies (and (cns-b-logp events start) (natp start) (natp from) (true-listp acc))
                  (let ((walk (cns-b-scan)))
                    (equal (append (strip-cars (mv-nth 0 walk))
                                   (if (mv-nth 1 walk) (cns-b-selected events (mv-nth 2 walk)) nil))
                           (append (strip-cars (reverse acc)) (cns-b-selected events from)))))
         :hints (("Goal" :induct (cns-b-scan-induct events start from edges grants p st items octets acc)
                         :in-theory (e/d (fn2-cns-walk fn2-cns-selected-positions cns-b-logp)
                                         (reverse revappend cns-b-above))))
         :rule-classes nil))

(local (defmacro cns-b-cursor (pos)
         `(fn2-cns-model-cursor st p c r ,pos)))

(local (defmacro cns-b-current-page ()
         '(fn2-cns-page st p (cns-b-cursor from) limits nil)))

(local (defmacro cns-b-full-walk ()
         '(fn2-cns-walk (fn2-cns-get :log st) from (fn2-cns-reg-edges r)
                        (fn2-cns-get :grants st) p st (nfix (car limits))
                        (nfix (cadr limits)) nil from nil)))

(local (defmacro cns-b-full-selection (pos)
         `(fn2-cns-selected-positions (fn2-cns-get :log st) (fn2-cns-get :log st)
                                      (fn2-cns-reg-edges r) (fn2-cns-get :grants st) p ,pos)))

(local (defmacro cns-b-current-reg ()
         '(and r (equal (fn2-cns-reg st p c) r)
               (equal (fn2-cns-reg-vv r) (fn2-cns-auth st p)))))

(local (defthm cns-b-cursor-scope
         (implies (and (cns-b-current-reg) (natp from))
                  (not (fn2-cns-scope-problem st p (cns-b-cursor from) nil)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-cursor fn2-cns-scope-problem
                                             fn2-cns-cursor-consumer)))))

(local (defthm cns-b-cursor-fields
         (and (equal (fn2-cns-cursor-consumer (cns-b-cursor pos)) c)
              (equal (fn2-cns-cursor-position (cns-b-cursor pos)) (nfix pos))
              (equal (nth 6 (cns-b-cursor pos)) (fn2-cns-reg-vv r)))
         :hints (("Goal" :in-theory (enable fn2-cns-model-cursor fn2-cns-cursor-consumer
                                             fn2-cns-cursor-position)))))

(local (defthm cns-b-page-fields
         (implies (and (cns-b-statep st) (cns-b-current-reg) (natp from))
                  (let ((page (cns-b-current-page)) (walk (cns-b-full-walk)))
                    (and (equal (fn2-cns-class page) :accepted)
                         (equal (fn2-cns-page-items page) (mv-nth 0 walk))
                         (equal (fn2-cns-page-more page) (mv-nth 1 walk))
                         (equal (fn2-cns-page-next page) (cns-b-cursor (mv-nth 2 walk))))))
         :hints (("Goal" :in-theory (enable fn2-cns-page fn2-cns-class fn2-cns-page-items
                                             fn2-cns-page-more fn2-cns-page-next)))))

(local (defun cns-b-resume (st p c r from limits)
         (declare (xargs :verify-guards nil))
         (fn2-cns-cursor-position (fn2-cns-page-next (cns-b-current-page)))))

(local (defthm cns-b-page-partition
         (implies (and (cns-b-statep st) (cns-b-current-reg) (natp from)
                       (posp (car limits)))
                  (let* ((page (cns-b-current-page)) (here (strip-cars (fn2-cns-page-items page)))
                         (resume (cns-b-resume st p c r from limits)))
                    (and (equal (fn2-cns-class page) :accepted)
                         (if (fn2-cns-page-more page)
                             (and (natp resume) (< from resume) (< from (fn2-cns-frontier st))
                                  (equal (fn2-cns-page-next page) (cns-b-cursor resume))
                                  (equal (append here (cns-b-full-selection resume))
                                         (cns-b-full-selection from)))
                           (equal here (cns-b-full-selection from))))))
         :hints (("Goal" :use ((:instance cns-b-scan-bounds (events (fn2-cns-get :log st)) (start 0)
                                (edges (fn2-cns-reg-edges r)) (grants (fn2-cns-get :grants st))
                                (items (nfix (car limits))) (octets (nfix (cadr limits))) (acc nil))
                               (:instance cns-b-scan-progress (events (fn2-cns-get :log st)) (start 0)
                                (edges (fn2-cns-reg-edges r)) (grants (fn2-cns-get :grants st))
                                (items (nfix (car limits))) (octets (nfix (cadr limits))) (acc nil))
                               (:instance cns-b-scan-partition (events (fn2-cns-get :log st)) (start 0)
                                (edges (fn2-cns-reg-edges r)) (grants (fn2-cns-get :grants st))
                                (items (nfix (car limits))) (octets (nfix (cadr limits))) (acc nil)))
                         :in-theory (enable fn2-cns-frontier)))
         :rule-classes nil))

(local (in-theory (disable cns-b-page-fields cns-b-resume cns-b-select-before-zero)))

(local (defun cns-b-drain-induct (st p c r from limits fuel)
         (declare (xargs :verify-guards nil :measure (nfix fuel)))
         (if (or (zp fuel) (not (fn2-cns-page-more (cns-b-current-page)))) from
           (cns-b-drain-induct st p c r (cns-b-resume st p c r from limits) limits (1- fuel)))))

(local (defthm cns-b-acked-natural (natp (fn2-cns-acked st p c epoch))
         :hints (("Goal" :in-theory (enable fn2-cns-acked))) :rule-classes :type-prescription))

(local (defthm cns-b-frontier-natural (natp (fn2-cns-frontier st))
         :hints (("Goal" :in-theory (enable fn2-cns-frontier))) :rule-classes :type-prescription))

; A nonterminal page advances by at least one position. Fuel greater than
; frontier minus FROM therefore suffices for the complete drain.
(local (defthm cns-b-drain-selection
         (implies (and (cns-b-statep st) (cns-b-current-reg) (natp from)
                       (posp (car limits)) (posp fuel) (< (fn2-cns-frontier st) (+ fuel from)))
                  (equal (fn2-cns-drain st p (cns-b-cursor from) limits nil fuel)
                         (list (cns-b-full-selection from) nil)))
         :hints (("Goal" :induct (cns-b-drain-induct st p c r from limits fuel))
                 ("Subgoal *1/1" :use cns-b-page-partition
                  :expand ((:free (k) (fn2-cns-drain st p k limits nil fuel))))
                 ("Subgoal *1/2" :use cns-b-page-partition
                  :expand ((:free (k) (fn2-cns-drain st p k limits nil fuel)))))))

(local (defthm cns-b-regs-deliver
         (implies (and (cns-b-statep st) (cns-b-rowsp rows)
                       (cns-b-agree rows (fn2-cns-get :regs st))
                       (posp (car limits)))
                  (fn2-cns-k1-regs rows st limits nil))
         :hints (("Goal" :induct (len rows)
                         :in-theory (enable fn2-cns-k1-regs cns-b-rowsp fn2-cns-reg fn2-cns-at)))))

(local (defthm cns-b-state-delivers
         (implies (and (cns-b-statep st) (posp (car limits)))
                  (fn2-cns-k1 st limits nil))
         :hints (("Goal" :in-theory (enable fn2-cns-k1)))))

(local (defthm cns-b-run-delivers
         (implies (and (cns-b-statep st) (posp (car limits)))
                  (fn2-cns-k1-trace (mv-nth 0 (fn2-cns-model-run ops st nil)) limits nil))
         :hints (("Goal" :induct (fn2-cns-model-run ops st nil)
                         :in-theory (enable fn2-cns-model-run fn2-cns-k1-trace)))))

(defthm fn2-cns-at-least-once-proved
  (fn2-cns-at-least-once$owed ops limits)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn2-cns-at-least-once$owed fn2-cns-limits-p fn2-cns-trace))))

(fn2-owed-discharge fn2-cns-at-least-once fn2-cns-at-least-once-proved)
