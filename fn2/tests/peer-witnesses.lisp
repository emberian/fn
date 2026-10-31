; The witness-to-property fixtures of fn2/docs/e-surface.md section 13.8
; over the peer reference model (books/peer-model.lisp). Each positive
; fixture asserts its keystone's full antecedent, and each keystone has a
; fault of the model that the same fixture catches. Model fixtures are
; executable obligations and checker oracles, not served acceptance evidence.
(in-package "ACL2")
(include-book "../books/peer-model")

(defmacro fn2-pmt-mv2 (form) `(mv-let (o st) ,form (list o st)))

;; W1: opposite first arrivals. A accepts a under N, B accepts b; they
;; exchange pages. Equal portable evidence, equal bindings with N in
;; conflict, and each local receipt still attributed to its own subject.
(defun fn2-pmt-w1 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pm-node 'a 10 faults)) (b (fn2-pm-node 'b 10 faults))
       ((mv oa a) (fn2-pm-accept "<n@x>" 'sa 'e1 nil a))
       ((mv ob b) (fn2-pm-accept "<n@x>" 'sb 'e2 nil b))
       (pa (fn2-pm-page a)) (pb (fn2-pm-page b))
       (a (fn2-pm-import pb a)) (b (fn2-pm-import pa b)))
    (list :premise (and (eq oa :accepted) (eq ob :accepted)
                        (equal (fn2-pm-sort-names (fn2-pm-get :evidence a)) (fn2-pm-sort-names (fn2-pm-get :evidence b)))
                        (null (fn2-pm-get :gaps a)) (null (fn2-pm-get :gaps b)))
          :kp1 (fn2-pm-kp1 a b)
          :conflict (and (fn2-pm-conflict-p "<n@x>" a) (fn2-pm-conflict-p "<n@x>" b))
          :attributed (and (equal (cadr (fn2-pm-local "<n@x>" a)) 'sa) (equal (cadr (fn2-pm-local "<n@x>" b)) 'sb)
                           (member-equal '(b "<n@x>" sb 1) (fn2-pm-get :foreign a))))))

;; W2: two candidate sets meet with B's funded capacity exhausted. B imports
;; part, records gaps, claims no incorporation; funded later, it repairs and
;; then agrees with A.
(defun fn2-pmt-accept-many (names subject i st)
  (declare (xargs :verify-guards nil))
  (if (atom names) st
    (mv-let (o st) (fn2-pm-accept (car names) subject (list 'e subject i) nil st)
      (declare (ignore o))
      (fn2-pmt-accept-many (cdr names) subject (+ 1 i) st))))
(defun fn2-pmt-w2 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((names '("<1@x>" "<2@x>" "<3@x>" "<4@x>" "<5@x>"))
       (a (fn2-pmt-accept-many names 'sa 0 (fn2-pm-node 'a 100 faults)))
       (b (fn2-pmt-accept-many names 'sb 0 (fn2-pm-node 'b 7 faults)))
       (b1 (fn2-pm-import (fn2-pm-page a) b))
       (short (and (consp (fn2-pm-get :gaps b1)) (not (fn2-pm-complete-p b1))))
       (b2 (fn2-pm-import (fn2-pm-page a) (fn2-pm-fund 10 b1)))
       (a2 (fn2-pm-import (fn2-pm-page b2) a)))
    (list :premise (and (null (fn2-pm-get :gaps b2)) (null (fn2-pm-get :gaps a2)))
          :honest-short short
          :complete-after-repair (fn2-pm-complete-p b2)
          :kp1 (fn2-pm-kp1 a2 b2)
          :equal (equal (fn2-pm-bindings a2) (fn2-pm-bindings b2)))))

;; W3: identical content arrives with new evidence: the evidence is learned,
;; nothing is allocated.
(defun fn2-pmt-w3 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pm-node 'a 10 faults))
       ((mv o1 a) (fn2-pm-accept "<n@x>" 'sa 'e1 nil a))
       (alloc (fn2-pm-get :allocations a))
       ((mv o2 a) (fn2-pm-accept "<n@x>" 'sa 'e2 nil a)))
    (list :premise (and (eq o1 :accepted) (eq o2 :duplicate))
          :no-allocation (equal (fn2-pm-get :allocations a) alloc)
          :learned (fn2-pm-has-eid 'e2 (fn2-pm-get :evidence a)))))

;; W7 with K-P5 and K-P6: a held body under a custody obligation is
;; reclaimed; a reoffer is a duplicate, allocates nothing and discharges no
;; obligation; then only the obligation's own receipt from its authority
;; releases it (a transport ack, another obligation's receipt, a receipt from
;; another issuer do not).
(defun fn2-pmt-w7 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pm-node 'a 10 faults))
       ((mv & a) (fn2-pm-accept "<n@x>" 'sa 'e1 nil a))
       (a (fn2-pm-oblige 'o1 "<n@x>" 'dest a))
       (a (fn2-pm-oblige 'o2 "<m@x>" 'dest a))
       (a (fn2-pm-reclaim "<n@x>" a))
       (alloc (fn2-pm-get :allocations a))
       ((mv re a) (fn2-pm-accept "<n@x>" 'sa 'e1 nil a))
       (held (equal (cadddr (assoc-equal 'o1 (fn2-pm-get :obligations a))) :held))
       ((mv r1 a) (fn2-pm-release 'o1 '(:ack o1) a))
       ((mv r2 a) (fn2-pm-release 'o1 '(:receipt o2 dest) a))
       ((mv r3 a) (fn2-pm-release 'o1 '(:receipt o1 elsewhere) a))
       ((mv r4 a) (fn2-pm-release 'o1 '(:receipt o1 dest) a))
       ((mv r5 a) (fn2-pm-release 'o1 '(:receipt o1 dest) a)))
    (list :kp6 (and (eq re :duplicate) (equal (fn2-pm-get :allocations a) alloc) held)
          :kp5-refusals (and (eq r1 :refused) (eq r2 :refused) (eq r3 :refused))
          :kp5-release (and (eq r4 :released) (eq r5 :refused))
          :o2-untouched (equal (cadddr (assoc-equal 'o2 (fn2-pm-get :obligations a))) :held))))

;; Offers are suppressed only by local acceptance history: evidence alone
;; (here a foreign binding learned by import) never makes a node decline.
(defun fn2-pmt-offer (faults)
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pm-node 'a 10 faults)) (b (fn2-pm-node 'b 10 faults))
       ((mv & a) (fn2-pm-accept "<n@x>" 'sa 'e1 nil a))
       (b (fn2-pm-import (fn2-pm-page a) b)))
    (list :premise (consp (assoc-equal "<n@x>" (fn2-pm-bindings b)))
          :wants (eq (fn2-pm-offer "<n@x>" b) :want)
          :has (eq (fn2-pm-offer "<n@x>" a) :have))))

(defun fn2-pmt-rows-for (peer rows)
  (declare (xargs :verify-guards nil))
  (cond ((atom rows) nil) ((equal (nth 1 (car rows)) peer) (cons (car rows) (fn2-pmt-rows-for peer (cdr rows))))
        (t (fn2-pmt-rows-for peer (cdr rows)))))
;; F1: A originates; B and C relay along a ring, each Path naming every
;; relaying node. A's own identity in the Path keeps C from installing work
;; back to A.
(defun fn2-pmt-f1 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((c (fn2-pm-node 'c 10 faults))
       (c (fn2-pm-install 'a 1 '((7 . (b a))) c))
       (c (fn2-pm-install 'd 1 '((7 . (b a))) c)))
    (list :premise (equal (len (fn2-pm-get :work c)) 1)
          :no-loop (not (assoc-equal '(1 . 7) (fn2-pmt-rows-for 'a (fn2-pm-get :work c)))))))


;; F2: a deferred head while later work succeeds; mixed phases; a stale reply
;; after a terminal outcome; a restart with an attempt unresolved; losses in
;; flight reaching the bound. K-P3a and K-P4 hold; the head never blocks.
(defun fn2-pmt-f2 (faults)
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pm-node 'a 10 faults))
       (a (fn2-pm-install 'p 1 '((1 . nil) (2 . nil) (3 . nil) (4 . nil)) a))
       (a (fn2-pm-offer-row '(1 . 1) a)) (a (fn2-pm-reply '(1 . 1) 431 a))
       (a (fn2-pm-offer-row '(1 . 1) a)) (a (fn2-pm-reply '(1 . 1) 436 a))
       (a (fn2-pm-offer-row '(1 . 1) a)) (a (fn2-pm-reply '(1 . 1) 431 a))
       (next (fn2-pm-next (fn2-pm-get :work a)))
       (a (fn2-pm-offer-row '(1 . 2) a)) (a (fn2-pm-reply '(1 . 2) 239 a))
       (a (fn2-pm-reply '(1 . 2) 439 a))                 ; stale reply after the terminal
       (a (fn2-pm-offer-row '(1 . 3) a))                 ; unresolved at the restart
       (a (fn2-pm-restart a))
       (a (fn2-pm-offer-row '(1 . 3) a)) (a (fn2-pm-reply '(1 . 3) 438 a))
       (a (fn2-pm-offer-row '(1 . 4) a)) (a (fn2-pm-reply '(1 . 4) :lost a))
       (a (fn2-pm-offer-row '(1 . 4) a)) (a (fn2-pm-reply '(1 . 4) :lost a))
       (a (fn2-pm-offer-row '(1 . 4) a)) (a (fn2-pm-reply '(1 . 4) :lost a))
       (rows (fn2-pm-get :work a)))
    (list :premise (equal (len (fn2-pm-get :terminals a)) 3)
          :head-pending (eq (nth 2 (fn2-pm-row '(1 . 1) rows)) :pending)
          :not-blocked (equal next '(1 . 2))
          :states (list (nth 2 (fn2-pm-row '(1 . 2) rows)) (nth 2 (fn2-pm-row '(1 . 3) rows))
                        (nth 2 (fn2-pm-row '(1 . 4) rows)))
          :kp3a (fn2-pm-kp3a 4 a)
          :kp4 (fn2-pm-kp4 a))))

(defun fn2-pmt-all-true (plist)
  (declare (xargs :verify-guards nil))
  (or (atom plist) (and (cadr plist) (fn2-pmt-all-true (cddr plist)))))

;; The positive runs: every claim holds, premises included.
(assert-event (fn2-pmt-all-true (fn2-pmt-w1 nil)))
(assert-event (fn2-pmt-all-true (fn2-pmt-w2 nil)))
(assert-event (fn2-pmt-all-true (fn2-pmt-w3 nil)))
(assert-event (fn2-pmt-all-true (fn2-pmt-w7 nil)))
(assert-event (fn2-pmt-all-true (fn2-pmt-offer nil)))
(assert-event (fn2-pmt-all-true (fn2-pmt-f1 nil)))
(assert-event (let ((r (fn2-pmt-f2 nil)))
                (and (fn2-pmt-all-true r)
                     (equal (cadr (member-eq :states r)) '(:accepted :not-wanted :dropped)))))

;; The teeth: each fault is caught by its fixture, with the premise intact.
(defun fn2-pmt-caught (r key)
  (declare (xargs :verify-guards nil))
  (and (cadr (member-eq :premise r)) (not (cadr (member-eq key r)))))
(assert-event (fn2-pmt-caught (fn2-pmt-w1 '(:first-arrival)) :kp1))
(assert-event (not (cadr (member-eq :honest-short (fn2-pmt-w2 '(:false-complete))))))
(assert-event (not (cadr (member-eq :kp6 (fn2-pmt-w7 '(:resurrect))))))
(assert-event (not (cadr (member-eq :kp5-refusals (fn2-pmt-w7 '(:ack-releases))))))
(assert-event (fn2-pmt-caught (fn2-pmt-offer '(:evidence-suppresses)) :wants))
(assert-event (not (cadr (member-eq :no-loop (fn2-pmt-f1 '(:no-loop-check))))))
(assert-event (not (cadr (member-eq :kp4 (fn2-pmt-f2 '(:double-terminal))))))
(assert-event (not (equal (cadr (member-eq :head-pending (fn2-pmt-f2 '(:count-deferrals)))) t)))

;; The named teeth the owed keystones cite.
(defun fn2-pmt-positive () (declare (xargs :verify-guards nil))
  (and (fn2-pmt-all-true (fn2-pmt-w1 nil)) (fn2-pmt-all-true (fn2-pmt-w2 nil)) (fn2-pmt-all-true (fn2-pmt-w3 nil))
       (fn2-pmt-all-true (fn2-pmt-w7 nil)) (fn2-pmt-all-true (fn2-pmt-offer nil)) (fn2-pmt-all-true (fn2-pmt-f1 nil))
       (fn2-pmt-all-true (fn2-pmt-f2 nil))))
(defun fn2-pmt-negative () (declare (xargs :verify-guards nil))
  (and (fn2-pmt-caught (fn2-pmt-w1 '(:first-arrival)) :kp1)
       (not (cadr (member-eq :kp6 (fn2-pmt-w7 '(:resurrect)))))
       (not (cadr (member-eq :kp5-refusals (fn2-pmt-w7 '(:ack-releases)))))
       (not (cadr (member-eq :no-loop (fn2-pmt-f1 '(:no-loop-check)))))
       (not (cadr (member-eq :kp4 (fn2-pmt-f2 '(:double-terminal)))))))
