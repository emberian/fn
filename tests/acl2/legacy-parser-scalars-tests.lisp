(in-package "ACL2")
(include-book "../../books/legacy-parser-scalars")

(defconst *lps-bytes* '(83 58 32 120 13 10 13 10 13 10))
(defconst *lps-arena* (list *lps-bytes*))
(defconst *lps-begin* (fn-lpc-begin 0 10 :pin))

(defthm lps-initialization-positive
 (fn-lps-scalars-p *lps-begin*) :rule-classes nil)
(defthm lps-header-positive
 (let ((s (fn-lpc-header-begin)) (pos 0))
  (and (fn-lps-header-count-p s pos)
       (fn-lps-header-count-p (fn-lpc-header-byte s 83 pos 0 :pin) (+ 1 pos))))
 :rule-classes nil)
(defthm lps-body-positive
 (let ((s '(:cr 1)) (pos 1))
  (and (fn-lps-body-count-p s pos)
       (fn-lps-body-count-p (fn-lpc-body-byte s 10) (+ 1 pos))))
 :rule-classes nil)
(defthm lps-byte-positive
 (and (fn-lps-scalars-p *lps-begin*)
      (fn-lps-scalars-p (fn-lpc-byte *lps-begin* 83))) :rule-classes nil)
(defthm lps-tick-positive
 (and (fn-lps-scalars-p *lps-begin*)
      (fn-lps-scalars-p (mv-nth 0 (fn-lpc-tick *lps-begin* 10 *lps-arena*))))
 :rule-classes nil)

; Literal complete width conclusion; the article reaches the body counter.
(defthm lps-source-width-positive
 (let* ((s *lps-begin*) (limit 10)
        (out (mv-nth 0 (fn-lpc-tick s 10 *lps-arena*)))
        (header (fn-lpc-at 4 out)) (body (fn-lpc-at 6 out)))
  (and (fn-lps-scalars-p s) (fn-lpc-ready-p s *lps-arena*)
       (<= (fn-lpc-at 1 s) limit)
       (natp (fn-lpc-at 3 out)) (<= (fn-lpc-at 3 out) limit)
       (natp (fn-lpc-at 1 header)) (<= (fn-lpc-at 1 header) limit)
       (natp (fn-lpc-at 4 header)) (<= (fn-lpc-at 4 header) limit)
       (natp (fn-lpc-at 5 header)) (<= (fn-lpc-at 5 header) limit)
       (natp (fn-lpc-at 1 body)) (<= (fn-lpc-at 1 body) limit)))
 :rule-classes nil)
(defthm lps-quantum-width-positive
 (let ((fuel 3) (quantum-limit 4))
  (and (natp fuel) (<= fuel quantum-limit)
       (natp (mv-nth 1 (fn-lpc-tick *lps-begin* fuel *lps-arena*)))
       (natp (mv-nth 2 (fn-lpc-tick *lps-begin* fuel *lps-arena*)))
       (<= (mv-nth 1 (fn-lpc-tick *lps-begin* fuel *lps-arena*)) quantum-limit)
       (<= (mv-nth 2 (fn-lpc-tick *lps-begin* fuel *lps-arena*)) quantum-limit)))
 :rule-classes nil)

; Hypothesis removals: deliberately corrupted state, not external grammar.
(defthm lps-header-without-carried-count
 (let ((s '(:bad nil)) (pos 0))
  (and (not (fn-lps-header-count-p s pos))
       (not (fn-lps-header-count-p (fn-lpc-header-byte s 83 pos 0 :pin) (+ 1 pos)))))
 :rule-classes nil)
(defthm lps-body-without-carried-count
 (let ((s '(:bad nil)) (pos 0))
  (and (not (fn-lps-body-count-p s pos))
       (not (fn-lps-body-count-p (fn-lpc-body-byte s 83) (+ 1 pos)))))
 :rule-classes nil)
(defconst *lps-corrupt* (fn-lpc-put 6 '(:bad 20) *lps-begin*))
(defthm lps-byte-without-carried-scalars
 (and (not (fn-lps-scalars-p *lps-corrupt*))
      (not (fn-lps-scalars-p (fn-lpc-byte *lps-corrupt* 83)))) :rule-classes nil)
(defthm lps-tick-without-carried-scalars
 (and (not (fn-lps-scalars-p *lps-corrupt*))
      (not (fn-lps-scalars-p (mv-nth 0 (fn-lpc-tick *lps-corrupt* 1 *lps-arena*)))))
 :rule-classes nil)
(defthm lps-width-without-carried-scalars
 (let* ((s *lps-corrupt*) (limit 10)
        (out (mv-nth 0 (fn-lpc-tick s 0 *lps-arena*))))
  (and (not (fn-lps-scalars-p s)) (fn-lpc-ready-p s *lps-arena*)
       (<= (fn-lpc-at 1 s) limit)
       (not (<= (fn-lpc-at 1 (fn-lpc-at 6 out)) limit)))) :rule-classes nil)
(defthm lps-width-without-ready
 (let* ((s (fn-lpc-byte (fn-lpc-begin 0 0 :pin) 83)) (limit 0)
        (out (mv-nth 0 (fn-lpc-tick s 0 '(nil)))))
  (and (fn-lps-scalars-p s) (not (fn-lpc-ready-p s '(nil)))
       (<= (fn-lpc-at 1 s) limit) (not (<= (fn-lpc-at 3 out) limit))))
 :rule-classes nil)
(defthm lps-width-without-source-bound
 (let* ((s *lps-begin*) (limit 0)
        (out (mv-nth 0 (fn-lpc-tick s 1 *lps-arena*))))
  (and (fn-lps-scalars-p s) (fn-lpc-ready-p s *lps-arena*)
       (not (<= (fn-lpc-at 1 s) limit)) (not (<= (fn-lpc-at 3 out) limit))))
 :rule-classes nil)
(defthm lps-quantum-without-natural-fuel
 (let ((fuel -1) (limit -1))
  (and (not (natp fuel)) (<= fuel limit)
       (not (<= (mv-nth 2 (fn-lpc-tick *lps-begin* fuel *lps-arena*)) limit))))
 :rule-classes nil)
(defthm lps-quantum-without-fuel-bound
 (let ((fuel 1) (limit 0))
  (and (natp fuel) (not (<= fuel limit))
       (not (<= (mv-nth 2 (fn-lpc-tick *lps-begin* fuel *lps-arena*)) limit))))
 :rule-classes nil)

; MUTATION: dropping the body carry admits a counter larger than source.
(defthm lps-body-carry-mutation
 (and (fn-lpc-ready-p *lps-corrupt* *lps-arena*)
      (fn-lpc-cursor-bounds-p *lps-corrupt*)
      (not (fn-lps-scalars-p *lps-corrupt*))) :rule-classes nil)

(defun lps-exec-case (bytes fuel fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((fn-arena (fn-arena-clear fn-arena))
        (fn-arena (fn-arena-seal-list bytes fn-arena))
        (s (fn-lpc-begin 0 (len bytes) :pin)))
  (mv-let (out consumed work verdict) (fn-lpc-tick s fuel fn-arena)
   (declare (ignore verdict))
   (mv (and (fn-lps-scalars-p s) (fn-lpc-ready-p s fn-arena)
            (fn-lps-scalars-p out) (fn-lpc-ready-p out fn-arena)
            (<= (fn-lpc-at 3 out) (len bytes))
            (natp consumed) (natp work) (<= consumed fuel) (<= work fuel))
       fn-arena))))
(defun lps-exec (bytes fuel)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-arena
  (mv-let (result fn-arena) (lps-exec-case bytes fuel fn-arena) result)))
(assert-event
 (and (lps-exec *lps-bytes* 1) (lps-exec *lps-bytes* 3)
      (lps-exec *lps-bytes* 10) (lps-exec '(0 13 10 13 10 13 10) 7)))
