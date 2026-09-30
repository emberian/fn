; Q10d: bounded readiness of the running owner, not the full operator report.
; No feed, history, peer-name or group traversal. All observations are the
; existing scheduler and checkpoint publication values. The host supplies
; them under the owner mutex after its usual free-space observation.
(in-package "ACL2")
(include-book "owner-time-model")

(defun fn-whl-checkpoint-word (checkpoint)
  (declare (xargs :guard t))
  (cond ((null checkpoint) :clear)
        ((and (consp checkpoint) (equal (car checkpoint) :deferred)) :deferred)
        (t :unobserved)))

(defun fn-whl-observe (sched checkpoint)
  (declare (xargs :guard t))
  (list :owner (fn-otm-mode sched)
        (and (fn-otm-sp-observedp (fn-otm-space sched)) t)
        (fn-whl-checkpoint-word checkpoint)))

(defun fn-whl-word (observation)
  (declare (xargs :guard t))
  (cond ((not (and (true-listp observation) (equal (len observation) 4)
                  (equal (car observation) :owner)
                  (equal (caddr observation) t)
                  (member (cadddr observation) '(:clear :deferred))))
         :unobserved)
        ((member (cadr observation) '(:stalled :full :failed)) :disk)
        ((not (member (cadr observation) '(:ok :slow))) :unobserved)
        ((equal (cadddr observation) :deferred) :checkpoint)
        (t :ready)))

(defun fn-whl-answer (observation)
  (declare (xargs :guard t))
  (let ((word (fn-whl-word observation)))
    (list (if (equal word :ready) 200 503)
          (case word
            (:ready '(114 101 97 100 121 10))
            (:disk '(117 110 97 118 97 105 108 97 98 108 101 32 100 105 115 107 10))
            (:checkpoint '(117 110 97 118 97 105 108 97 98 108 101 32 99 104 101 99 107 112 111 105 110 116 10))
            (otherwise '(117 110 111 98 115 101 114 118 101 100 10))))))

; KEYSTONE (PRF-1100): the actual host-called answer's success requires
; observed space, the existing disk health clear verdict, and no deferred
; checkpoint. Slow barriers follow the existing operator policy (PRF-358).
(defthm fn-whl-success-requires-observed-clear-owner
  (implies (equal (car (fn-whl-answer (fn-whl-observe sched checkpoint))) 200)
           (and (fn-otm-sp-observedp (fn-otm-space sched))
                (not (equal (car (fn-otm-health-disk sched)) :held))
                (null checkpoint)))
  :hints (("Goal" :in-theory (e/d (fn-whl-answer fn-whl-word fn-whl-observe
                                    fn-whl-checkpoint-word fn-otm-health-disk)
                                   (fn-otm-mode fn-otm-space fn-otm-sp-observedp)))))

; A response has constant-size storage, even for malformed observations;
; it never copies variable-length peer names, counters or checkpoint words.
(defthm fn-whl-answer-body-is-bounded
  (and (true-listp (cadr (fn-whl-answer observation)))
       (<= (len (cadr (fn-whl-answer observation))) 23)
       (member (car (fn-whl-answer observation)) '(200 503)))
  :hints (("Goal" :in-theory (enable fn-whl-answer))))
