(in-package "ACL2")
(include-book "../../books/newnews-matching-selector")

; Test-only drain: production retains exactly one selector/matcher step.
(defun nnmt-next (s)
  (declare (xargs :guard t))
  (mv-let (decided matched next) (fn-nnm-one s)
    (declare (ignore decided matched)) next))
(defun nnmt-drain (s fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (zp fuel) s
    (mv-let (decided matched next) (fn-nnm-one s)
      (declare (ignore matched))
      (if decided next (nnmt-drain next (1- fuel))))))
(defconst *nnmt-patterns*
  (fn-wildmat-result-value (fn-wildmat-parse (fn-nntp-string-octets "fn.*,!fn.block"))))
(defconst *nnmt-article*
  (fn-make-article "<a@x>" nil '("fn.good")
                   '(("fn.block" . 1) ("fn.good" . 7)) 1 1))
(defconst *nnmt-start* (fn-nnm-start *nnmt-patterns* '("fn.good") *nnmt-article*))
(defconst *nnmt-member* (nnmt-next (nnmt-next *nnmt-start*)))
(defconst *nnmt-match* (nnmt-next *nnmt-member*))
(defconst *nnmt-mid* (nnmt-next *nnmt-match*))

(defthm nnmt-entry-and-first-membership-positive
  (and (fn-nnm-statep *nnmt-start*)
       (equal (fn-nnm-value *nnmt-start*)
              (fn-nntp-newnews-candidatep
               (fn-nntp-filter-groups-by-wildmat *nnmt-patterns* '("fn.good"))
               *nnmt-article*))
       (fn-nnm-needs-matchp (fn-nnw-select-at 1 *nnmt-member*))
       (fn-nnm-matchp *nnmt-match*)
       (fn-nnm-statep *nnmt-match*)
       (equal (fn-nnm-entry-visits *nnmt-member*) 1)
       (equal (fn-nnm-entry-visits *nnmt-match*) 0)
       (< (fn-nnm-group-remaining *nnmt-match*) (fn-nnm-group-remaining *nnmt-member*))
       (equal (fn-nnm-value *nnmt-match*) (fn-nnm-value *nnmt-member*))))

(defthm nnmt-matcher-quantum-positive
  (let ((next (nnmt-next *nnmt-mid*)))
    (and (fn-nnm-statep *nnmt-mid*) (fn-nnm-matchp *nnmt-mid*)
         (posp (fn-nnm-work-remaining *nnmt-mid*))
         (not (fn-wmc-decidedp (fn-nnw-select-at 1 *nnmt-mid*)))
         (equal (fn-nnm-entry-visits *nnmt-mid*) 0)
         (equal (fn-nnm-work *nnmt-mid*) 1)
         (<= (fn-nnm-engine-cons *nnmt-mid*)
             (fn-wmc-demand (fn-nnw-select-at 1 *nnmt-mid*)))
         (fn-nnm-statep next)
         (equal (fn-nnm-group-remaining next) (fn-nnm-group-remaining *nnmt-mid*))
         (< (fn-nnm-work-remaining next) (fn-nnm-work-remaining *nnmt-mid*))
         (equal (fn-nnm-value next) (fn-nnm-value *nnmt-mid*)))))

(defthm nnmt-match-settles-exactly
  (let* ((done (nnmt-drain *nnmt-start* 2000)) (answer (fn-nnm-one done)))
    (and (fn-nnm-statep done) (not (fn-nnm-matchp done))
         (equal (fn-nnm-group-remaining done) 0) (equal (fn-nnm-work-remaining done) 0)
         (mv-nth 0 answer) (mv-nth 1 answer)
         (equal (mv-nth 1 answer) (fn-nnm-value done))
         (equal (fn-nnm-value done) (fn-nnm-value *nnmt-start*)))))

(defthm nnmt-exclusion-then-match-keeps-exact-selection
  (let* ((start (fn-nnm-start *nnmt-patterns* '("fn.miss" "fn.block" "fn.good")
                            *nnmt-article*))
         (done (nnmt-drain start 3000)))
    (and (fn-nnm-statep start) (fn-nnm-statep done)
         (equal (fn-nnm-value start) (fn-nnm-value done))
         (mv-nth 0 (fn-nnm-one done)) (mv-nth 1 (fn-nnm-one done)))))

(defthm nnmt-invalid-first-duplicate-does-not-start-matcher
  (let* ((article (fn-make-article "<a@x>" nil '("fn.good")
                                  '(("fn.good" . 0) ("fn.good" . 7)) 1 1))
         (start (fn-nnm-start *nnmt-patterns* '("fn.good") article))
         (member (nnmt-next start)) (next (nnmt-next member))
         (done (nnmt-drain start 20)))
    (and (fn-nnm-statep member) (not (fn-nnm-needs-matchp (fn-nnw-select-at 1 member)))
         (not (fn-nnm-matchp next)) (equal (fn-nnm-work next) 0)
         (mv-nth 0 (fn-nnm-one done)) (not (mv-nth 1 (fn-nnm-one done)))
         (not (fn-nnm-value done)))))

(defthm nnmt-positive-remainder-is-necessary
  (let ((s (fn-nnm-start *nnmt-patterns* nil *nnmt-article*)))
    (and (fn-nnm-statep s)
         (not (posp (fn-nnm-group-remaining s)))
         (not (posp (fn-nnm-work-remaining s)))
         (mv-nth 0 (fn-nnm-one s))
         (not (< (fn-nnm-group-remaining (nnmt-next s)) (fn-nnm-group-remaining s)))
         (not (< (fn-nnm-work-remaining (nnmt-next s)) (fn-nnm-work-remaining s))))))
