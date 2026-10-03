(in-package "ACL2")
(include-book "../../books/wildmat-cursor")

; TEST ONLY: decrement BOTH budgets after every accepted engine microstep.
; The served caller retains a cursor, never invokes this drain.
(defun wmct-drain (s work grant)
  (declare (xargs :guard (and (natp work) (natp grant)) :measure (nfix work)))
  (if (or (zp work) (< grant 13) (fn-wmc-decidedp s)) s
    (wmct-drain (fn-wmc-step s work grant) (1- work) (- grant 13))))
(defconst *wmct-patterns*
  (fn-wildmat-result-value
   (fn-wildmat-parse (fn-nntp-string-octets "fn.*,!fn.block,fn.block.good"))))
(defconst *wmct-start* (fn-wmc-start *wmct-patterns* "fn.block.good"))
(defconst *wmct-mid* (wmct-drain *wmct-start* 35 455))
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
  (and (equal (wmct-drain *wmct-start* 1000 13)
              (fn-wmc-step *wmct-start* 1 13))
       (not (fn-wmc-decidedp (wmct-drain *wmct-start* 1000 13)))
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

; Hypothesis removal: unsafe stored name lies outside the shared decoder seam.
(defthm wmct-safe-name-hypothesis-removal
  (let* ((name (coerce (list (code-char 128)) 'string))
         (patterns '((:positive (128)))) (s (fn-wmc-start patterns name)))
    (and (not (fn-nntp-safe-group-namep name))
         (fn-wmc-shapedp s)
         (not (equal (fn-wmc-value s)
                     (fn-nntp-group-matches-parsed-wildmatp patterns name)))))
  :rule-classes nil)
; Corrupted state, not external input: invalid decode offset breaks residual.
(defthm wmct-decode-index-hypothesis-removal
  (let ((s (fn-wmc-state (fn-wmc-node :decode '((:positive (102))) "f" -1 nil) nil)))
    (and (eq (fn-wmc-at 0 (fn-wmc-at 0 s)) :decode)
         (not (natp (fn-wmc-at 3 (fn-wmc-at 0 s))))
         (not (fn-wmc-shapedp s))
         (not (equal (fn-wmc-result (fn-wmc-one s)) (fn-wmc-result s)))))
  :rule-classes nil)

(defthm wmct-grant-ledger-positive
  (and (fn-wmc-acceptedp *wmct-mid* 1 13)
       (natp (fn-wmc-work-left *wmct-mid* 1 13))
       (natp (fn-wmc-cons-left *wmct-mid* 1 13))
       (equal (+ (fn-wmc-consumed-work *wmct-mid* 1 13)
                 (fn-wmc-work-left *wmct-mid* 1 13)) 1)
       (equal (+ (fn-wmc-consumed-cons *wmct-mid* 1 13)
                 (fn-wmc-cons-left *wmct-mid* 1 13)) 13)
       (<= (fn-wmc-run-cons *wmct-start* 1000 13) 13)
       (equal (fn-wmc-run-cons *wmct-start* 1000 13) 13)
       (<= (fn-wmc-run-cons *wmct-start* 1000 13000) 13000))
  :rule-classes nil)
