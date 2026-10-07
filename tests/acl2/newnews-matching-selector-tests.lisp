(in-package "ACL2")
(include-book "../../books/newnews-matching-selector")
(include-book "../../books/defkeystone")

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
       (fn-nnm-statep *nnmt-member*)
       (posp (fn-nnm-group-remaining *nnmt-member*))
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

; Corrupted-state hypothesis removal: UTF entry has pending frames, forbidden
; by the carried state. Its invalid byte returns to that frame; the production
; factory never builds this state, and the logical work rank need not shrink.
(defthm nnmt-progress-needs-carried-state
  (let* ((following (fn-nnw-select-start nil nil nil))
         (s (fn-nnm-match
             (fn-wmc-state (fn-wmc-node :utf8 nil
                            (coerce (list (code-char 128)) 'string) 0 nil)
                           (list (fn-wmc-node :cons 42 nil nil nil))) following))
         (next (nnmt-next s)))
    (and (not (fn-nnm-statep s))
         (or (posp (fn-nnm-group-remaining s)) (posp (fn-nnm-work-remaining s)))
         (not (or (< (fn-nnm-group-remaining next) (fn-nnm-group-remaining s))
                  (and (equal (fn-nnm-group-remaining next) (fn-nnm-group-remaining s))
                       (< (fn-nnm-work-remaining next) (fn-nnm-work-remaining s))))))))

; ---------------------------------------------------------------------------
; PRF-1257 keystones of books/newnews-matching-selector.lisp with their teeth
; (TEETH CONTRACT v1).  The three over fn-nnm-one's (mv decided matched next)
; are not here: a defteeth witness is an assert-event over the literal claim,
; and (mv-nth 0 (fn-nnm-one s)) is no executable term.
(defconst *nnmt-blocked-article*
  (fn-make-article "<b@x>" nil '("fn.block") '(("fn.block" . 1)) 1 1))

(defteeth fn-nnm-start-value
  :claim (() (equal (fn-nnm-value (fn-nnm-start patterns groups article))
                    (fn-nntp-newnews-candidatep
                     (fn-nntp-filter-groups-by-wildmat patterns groups) article)))
  :subject fn-nnm-start
  :witness ((patterns *nnmt-patterns*) (groups '("fn.good")) (article *nnmt-article*))
  :mutations ((wildmat-unfiltered
               (:conclusion (equal (fn-nnm-value (fn-nnm-start patterns groups article))
                                   (fn-nntp-newnews-candidatep groups article)))
               ((patterns *nnmt-patterns*) (groups '("fn.block")) (article *nnmt-blocked-article*))
               :fault "the NEWNEWS groups not filtered by the wildmat (!fn.block admitted)")))

(defteeth fn-nnm-entry-visits-at-most-one
  :claim (() (<= (fn-nnm-entry-visits s) 1))
  :subject fn-nnm-one
  :witness ((s *nnmt-start*))
  :mutations ((entry-visits-nothing
               (:conclusion (<= (fn-nnm-entry-visits s) 0))
               ((s *nnmt-start*))
               :fault "a membership step charged no entry visit")))

(defteeth fn-nnm-engine-cons-at-most-demand
  :claim (() (<= (fn-nnm-engine-cons s)
                 (if (fn-nnm-matchp s) (fn-wmc-demand (fn-nnw-select-at 1 s)) 0)))
  :subject fn-nnm-one
  :witness ((s *nnmt-match*))
  :mutations ((matcher-free
               (:conclusion (<= (fn-nnm-engine-cons s) 0))
               ((s *nnmt-match*))
               :fault "a matcher microstep charged no cons cells")))

; ---------------------------------------------------------------------------
; fn-nnm-one-preserves-value (TEETH CONTRACT v1).  fn-nnm-one returns several
; values, and defteeth's executable witnesses cannot evaluate (mv-nth K (F ..)),
; so the witnesses are ground theorems (:witness-lemma, :lemma): each states
; the conjunction the entry would assert, at the entry's bindings, and is
; proved by evaluation.  They are lemma debt (TEETH-OWED-MV-CLAIM), not
; executed witnesses.
(defthm nnmt-preserves-value-witness
  (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one *nnmt-mid*))) (fn-nnm-value *nnmt-mid*)))
(defthm nnmt-preserves-value-mutant-witness
  (and (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one *nnmt-mid*))) (fn-nnm-value *nnmt-mid*))
       (not (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one *nnmt-mid*))) (not (fn-nnm-value *nnmt-mid*))))))
(defteeth fn-nnm-one-preserves-value
  :claim (() (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one s))) (fn-nnm-value s)))
  :subject fn-nnm-one
  :witness-lemma nnmt-preserves-value-witness
  :witness ((s *nnmt-mid*))
  :mutations ((value-negated
               (:conclusion (equal (fn-nnm-value (mv-nth 2 (fn-nnm-one s))) (not (fn-nnm-value s))))
               ((s *nnmt-mid*))
               :fault "a step that flips the selection value"
               :lemma nnmt-preserves-value-mutant-witness)))
