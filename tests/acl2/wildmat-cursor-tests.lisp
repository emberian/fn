(in-package "ACL2")
(include-book "../../books/wildmat-cursor")
(include-book "../../books/defkeystone")

; TEST ONLY: decrement BOTH budgets after every accepted engine microstep.
; The served caller retains a cursor, never invokes this drain.
(defun wmct-drain (s work grant)
  (declare (xargs :guard (and (natp work) (natp grant)) :measure (nfix work)))
  (if (fn-wmc-acceptedp s work grant)
      (wmct-drain (fn-wmc-step s work grant)
                  (fn-wmc-work-left s work grant) (fn-wmc-cons-left s work grant)) s))
(defconst *wmct-patterns*
  (fn-wildmat-result-value
   (fn-wildmat-parse (fn-nntp-string-octets "fn.*,!fn.block,fn.block.good"))))
(defconst *wmct-start* (fn-wmc-start *wmct-patterns* "fn.block.good"))
(defconst *wmct-mid* (wmct-drain *wmct-start* 35 525))
(defconst *wmct-done* (wmct-drain *wmct-mid* 1000 13000))

; Literal entry keystones: full safe-name antecedent, model equality and profile.
(defthm wmct-entry-positive
  (and (fn-nntp-safe-group-namep "fn.block.good")
       (fn-wmc-shapedp *wmct-start*)
       (equal (fn-wmc-value *wmct-start*)
              (fn-nntp-group-matches-parsed-wildmatp *wmct-patterns* "fn.block.good"))
       (stringp "fn.block.good")
       (fn-wmc-ascii-octetsp (fn-nntp-string-octets "fn.block.good"))
       (<= (len (fn-nntp-string-octets "fn.block.good")) *fn-nntp-max-group-octets*)
       (< *fn-nntp-max-group-octets* *fn-wildmat-max-octets*))
  :rule-classes nil)
(defthm wmct-codepoint-entry-positive
  (equal (fn-wmc-result (fn-wmc-start-codepoints *wmct-patterns* '(102 110 46 97)))
         (fn-wm-match-codepoints-work *wmct-patterns* '(102 110 46 97)))
  :rule-classes nil)

; Midstate is actually reached through charged steps, not a fabricated branch.
(defthm wmct-step-residual-positive
  (let ((next (fn-wmc-step *wmct-mid* 1 13)))
    (and (fn-wmc-shapedp *wmct-mid*) (not (fn-wmc-decidedp *wmct-mid*))
         (fn-wmc-acceptedp *wmct-mid* 1 13)
         (or (not (eq (fn-wmc-at 0 (fn-wmc-at 0 *wmct-mid*)) :decode))
             (natp (fn-wmc-at 3 (fn-wmc-at 0 *wmct-mid*))))
         (fn-wmc-shapedp next)
         (equal (fn-wmc-result next) (fn-wmc-result *wmct-mid*))
         (equal (fn-wmc-value next) (fn-wmc-value *wmct-mid*))
         (equal (fn-wmc-remaining next) (1- (fn-wmc-remaining *wmct-mid*)))
         (equal (fn-wmc-consumed-work *wmct-mid* 1 13) 1)
         (equal (fn-wmc-consumed-cons *wmct-mid* 1 13) 13)
         (<= (fn-wmc-one-cons-cells *wmct-mid*) (fn-wmc-demand *wmct-mid*))
         (<= (fn-wmc-one-cons-cells *wmct-mid*) (fn-wmc-consumed-cons *wmct-mid* 1 13))
         (<= (fn-wmc-consumed-work *wmct-mid* 1 13) 1)
         (<= (fn-wmc-consumed-cons *wmct-mid* 1 13) 13)))
  :rule-classes nil)
(defthm wmct-receipt-positive
  (and (fn-wmc-shapedp *wmct-done*) (fn-wmc-decidedp *wmct-done*)
       (fn-wmc-matchedp *wmct-done*)
       (equal (fn-wmc-matchedp *wmct-done*) (if (fn-wmc-value *wmct-done*) t nil))
       (equal (fn-wmc-result *wmct-done*) (fn-wmc-result *wmct-start*))
       (equal (fn-wmc-remaining *wmct-done*) 0)
       (equal (fn-wmc-demand *wmct-done*) 0))
  :rule-classes nil)
(defthm wmct-unfunded-positive
  (and (not (fn-wmc-acceptedp *wmct-mid* 0 13))
       (not (fn-wmc-acceptedp *wmct-mid* 1 12))
       (equal (fn-wmc-step *wmct-mid* 0 13) *wmct-mid*)
       (equal (fn-wmc-step *wmct-mid* 1 12) *wmct-mid*)
       (equal (fn-wmc-consumed-work *wmct-mid* 0 13) 0)
       (equal (fn-wmc-consumed-cons *wmct-mid* 1 12) 0))
  :rule-classes nil)
(defthm wmct-budget-does-not-reuse-grant
  (and (equal (wmct-drain *wmct-start* 1000 15)
              (fn-wmc-step *wmct-start* 1 15))
       (not (fn-wmc-decidedp (wmct-drain *wmct-start* 1000 15)))
       (equal (wmct-drain *wmct-start* 1000 0) *wmct-start*)
       (fn-wmc-decidedp *wmct-done*))
  :rule-classes nil)
(defthm wmct-work-bounds-positive
  (and (natp (fn-wmc-remaining *wmct-mid*))
       (fn-wmc-shapedp *wmct-mid*) (not (fn-wmc-decidedp *wmct-mid*))
       (< 0 (fn-wmc-remaining *wmct-mid*))
       (stringp "fn.block.good")
       (<= (fn-wmc-remaining *wmct-start*)
           (+ 5 (* 2 (length "fn.block.good")) (* 12 (len *wmct-patterns*))
              (* 4 (len *wmct-patterns*) (len (fn-nntp-string-octets "fn.block.good")))
              (* (fn-wm-total-items *wmct-patterns*)
                 (+ 6 (* 2 (len (fn-nntp-string-octets "fn.block.good"))))))))
  :rule-classes nil)
(defthm wmct-codepoint-work-bounds-positive
  (<= (fn-wmc-remaining (fn-wmc-start-codepoints *wmct-patterns* '(102 110 46 97)))
      (+ 3 (* 12 (len *wmct-patterns*)) (* 4 (len *wmct-patterns*) 4)
         (* (fn-wm-total-items *wmct-patterns*) (+ 6 (* 2 4)))))
  :rule-classes nil)
(defthm wmct-ascii-decoder-positive
  (and (fn-wmc-ascii-octetsp '(102 110 46 97))
       (true-listp '(102 110 46 97)) (<= 4 *fn-wildmat-max-octets*)
       (equal (fn-wildmat-decode '(102 110 46 97)) (fn-wildmat-ok '(102 110 46 97))))
  :rule-classes nil)

; Rightmost inclusion/exclusion ordering survives all suspension points.
(defthm wmct-exclusion-and-empty-target
  (let ((excluded (wmct-drain (fn-wmc-start *wmct-patterns* "fn.block") 1000 13000))
        (star (wmct-drain (fn-wmc-start-codepoints '((:positive (42))) nil) 100 1300)))
    (and (fn-wmc-decidedp excluded) (not (fn-wmc-matchedp excluded))
         (fn-wmc-decidedp star) (fn-wmc-matchedp star)))
  :rule-classes nil)

 ; The old safe-name/index hypotheses are removed by proved total refinement.
(defthm wmct-unsafe-name-total-positive
  (let* ((name (coerce (list (code-char 128)) 'string))
         (patterns '((:positive (128)))) (s (fn-wmc-start patterns name)))
    (and (not (fn-nntp-safe-group-namep name))
         (fn-wmc-shapedp s)
         (equal (fn-wmc-value s) (fn-nntp-group-matches-parsed-wildmatp patterns name))
         (fn-wmc-decidedp (wmct-drain s 10 150))
         (not (fn-wmc-matchedp (wmct-drain s 10 150))))) :rule-classes nil)
(defthm wmct-corrupted-decode-index-total-positive
  (let ((s (fn-wmc-state (fn-wmc-node :decode '((:positive (102))) "f" -1 nil) nil)))
    (and (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode)
         (not (natp (fn-wmc-at 3 (fn-wmc-at 0 s))))
         (not (fn-wmc-shapedp s))
         (equal (fn-wmc-result (fn-wmc-one s)) (fn-wmc-result s)))) :rule-classes nil)

(defthm wmct-grant-ledger-positive
  (and (fn-wmc-acceptedp *wmct-mid* 1 13)
       (natp (fn-wmc-work-left *wmct-mid* 1 13))
       (natp (fn-wmc-cons-left *wmct-mid* 1 13))
       (equal (+ (fn-wmc-consumed-work *wmct-mid* 1 13)
                 (fn-wmc-work-left *wmct-mid* 1 13)) 1)
       (equal (+ (fn-wmc-consumed-cons *wmct-mid* 1 13)
                 (fn-wmc-cons-left *wmct-mid* 1 13)) 13)
       (<= (fn-wmc-run-cons *wmct-start* 1000 15) 15)
       (equal (fn-wmc-run-cons *wmct-start* 1000 15) 15)
       (<= (fn-wmc-run-cons *wmct-start* 1000 15000) 13000))
  :rule-classes nil)

(defthm wmct-total-utf8-two-three-four
  (let* ((name (coerce (list (code-char 195) (code-char 169)
                            (code-char 226) (code-char 130) (code-char 172)
                            (code-char 244) (code-char 143) (code-char 191) (code-char 191)) 'string))
         (patterns '((:positive (233 8364 1114111)))) (s (fn-wmc-start patterns name))
         (next (fn-wmc-step s 1 15)) (done (wmct-drain s 1000 15000)))
    (and (not (fn-nntp-safe-group-namep name)) (fn-wmc-shapedp s)
         (equal (fn-wmc-value s) (fn-nntp-group-matches-parsed-wildmatp patterns name))
         (equal (fn-wmc-at 3 (fn-wmc-at 0 next)) 2)
         (equal (fn-wmc-result next) (fn-wmc-result s))
         (equal (fn-wmc-remaining next) (1- (fn-wmc-remaining s)))
         (fn-wmc-decidedp done) (fn-wmc-matchedp done))) :rule-classes nil)
(defthm wmct-total-nonstring-and-limit
  (let* ((p '((:positive (42))))
         (long (coerce (make-list 498 :initial-element #\f) 'string))
         (non (fn-wmc-start p '(invalid name))) (limit (fn-wmc-start p long)))
    (and (equal (fn-wmc-value non) (fn-nntp-group-matches-parsed-wildmatp p '(invalid name)))
         (fn-wmc-matchedp (wmct-drain non 100 1500))
         (equal (length long) 498) (fn-wmc-decidedp limit) (not (fn-wmc-matchedp limit))
         (equal (fn-wmc-value limit) (fn-nntp-group-matches-parsed-wildmatp p long)))) :rule-classes nil)
(defthm wmct-total-malformed-utf8-refuses
  (let* ((bad (coerce (list (code-char 237) (code-char 160) (code-char 128)) 'string))
         (s (fn-wmc-start '((:positive (42))) bad))
         (done (fn-wmc-step s 1 15)))
    (and (equal (fn-wmc-demand s) 15)
         (not (fn-wmc-acceptedp s 1 14)) (equal (fn-wmc-step s 1 14) s)
         (fn-wmc-acceptedp s 1 15) (fn-wmc-decidedp done) (not (fn-wmc-matchedp done))
         (equal (fn-wmc-result done) (fn-wmc-result s))
         (equal (fn-wmc-remaining done) (1- (fn-wmc-remaining s))))) :rule-classes nil)
(defthm wmct-corrupted-utf8-accumulator-frames-total
  (let* ((s (fn-wmc-state (fn-wmc-node :utf8 '((:positive (102))) "f" -2 "bad")
                           (list (fn-wmc-node :cons nil nil nil nil))))
         (next (fn-wmc-step s 1 15)))
    (and (not (fn-wmc-shapedp s))
         (equal (fn-wmc-result next) (fn-wmc-result s)))) :rule-classes nil)

; ---------------------------------------------------------------------------
; The PRF-1261 keystones of books/wildmat-cursor.lisp with their teeth
; (TEETH CONTRACT v1), over the fixtures above: the start, the reached
; midstate and the drained receipt.  A UTF-8 task with matcher frames already
; pending is a state no start builds (the corrupted shape).
(defconst *wmct-utf8-with-frames*
  (list (list :utf8 *wmct-patterns* "fn.block.good" 13 nil) (fn-wmc-at 1 *wmct-mid*)))

(defteeth fn-wmc-start-value-is-group-match
  :claim (() (equal (fn-wmc-value (fn-wmc-start patterns group))
                    (fn-nntp-group-matches-parsed-wildmatp patterns group)))
  :subject fn-wmc-start
  :witness ((patterns *wmct-patterns*) (group "fn.block"))
  :mutations ((first-match-decides
               (:conclusion (equal (fn-wmc-value (fn-wmc-start patterns group))
                                   (fn-nntp-group-matches-parsed-wildmatp (list (car patterns)) group)))
               ((patterns *wmct-patterns*) (group "fn.block"))
               :fault "the first matching pattern decides, not the rightmost (fn.* before !fn.block)")))

(defteeth fn-wmc-one-preserves-result
  :claim (() (equal (fn-wmc-result (fn-wmc-one s)) (fn-wmc-result s)))
  :subject fn-wmc-one
  :witness ((s *wmct-mid*))
  :mutations ((microstep-idle
               (:conclusion (equal (fn-wmc-one s) s))
               ((s *wmct-mid*))
               :fault "a microstep that leaves the cursor where it was")))

(defteeth fn-wmc-step-preserves-value
  :claim (() (equal (fn-wmc-value (fn-wmc-step s work cons-grant)) (fn-wmc-value s)))
  :subject fn-wmc-step
  :witness ((s *wmct-mid*) (work 1) (cons-grant 13))
  :mutations ((funded-step-idle
               (:conclusion (equal (fn-wmc-step s work cons-grant) s))
               ((s *wmct-mid*) (work 1) (cons-grant 13))
               :fault "a funded step that does not advance the cursor")))

(defteeth fn-wmc-cumulative-cons-bound
  :claim (() (<= (fn-wmc-run-cons s work cons-grant) (nfix cons-grant)))
  :subject fn-wmc-step
  :witness ((s *wmct-start*) (work 1000) (cons-grant 13000))
  :mutations ((cons-against-work
               (:conclusion (<= (fn-wmc-run-cons s work cons-grant) (nfix work)))
               ((s *wmct-start*) (work 1000) (cons-grant 13000))
               :fault "the run's cons cells bounded by the work grant instead of the cons grant")))

(defteeth fn-wmc-funded-step-progress
  :claim (((shaped (fn-wmc-shapedp s)))
          (equal (fn-wmc-remaining (fn-wmc-step s work cons-grant))
                 (- (fn-wmc-remaining s) (fn-wmc-consumed-work s work cons-grant))))
  :subject fn-wmc-step
  :witness ((s *wmct-mid*) (work 1) (cons-grant 13))
  :breaks ((shaped ((s *wmct-utf8-with-frames*) (work 1) (cons-grant 100))))
  :mutations ((unfunded-step-charged
               (:conclusion (equal (fn-wmc-remaining (fn-wmc-step s work cons-grant))
                                   (- (fn-wmc-remaining s) 1)))
               ((s *wmct-mid*) (work 1) (cons-grant 12))
               :fault "a step charged its unit of work when the cons grant did not fund it")))

(defteeth fn-wmc-accepted-cons-cells-covered
  :claim (((accepted (fn-wmc-acceptedp s work cons-grant)))
          (<= (fn-wmc-one-cons-cells s) (fn-wmc-consumed-cons s work cons-grant)))
  :subject fn-wmc-step
  :witness ((s *wmct-mid*) (work 1) (cons-grant 13))
  :breaks ((accepted ((s *wmct-mid*) (work 1) (cons-grant 12))))
  :mutations ((one-cell-charged
               (:conclusion (<= (fn-wmc-one-cons-cells s) 1))
               ((s *wmct-mid*) (work 1) (cons-grant 13))
               :fault "an accepted microstep charged one cons cell for the thirteen it allocates")))
