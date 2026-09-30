; Full execution-trace reference over ACTUAL ONE calls. Logical only;
; native scheduling still saves every returned paid quantum separately.
(in-package "ACL2")
(include-book "over-byte-semantic-carry")

(defun-nx fn-obc-source-run (s steps fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix steps)
                 :verify-guards nil))
 (if (or (zp steps) (not s)) (mv nil s)
  (mv-let (out next) (fn-obc-one s fn-arena fn-cat)
   (mv-let (tail final) (fn-obc-source-run next (1- steps) fn-arena fn-cat)
    (mv (append out tail) final)))))

(local
 (defthm fn-obrun-append-associative
  (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-obc-source-run-complete-old-reply-and-carried-state
 (implies (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
               (fn-cat-p fn-cat)
               (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat))
  (let ((result (fn-obc-source-run s steps fn-arena fn-cat)))
   (and (true-listp (mv-nth 0 result))
        (fn-obc-semantic-ready-p (mv-nth 1 result) fn-arena fn-cat)
        (equal (append (mv-nth 0 result)
                       (fn-obc-actual-old-residual (mv-nth 1 result) fn-arena fn-cat))
               (fn-obc-actual-old-residual s fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-obc-source-run s steps fn-arena fn-cat)
  :in-theory (e/d (fn-obc-source-run)
   (fn-obc-one fn-obc-semantic-ready-p fn-obc-actual-old-residual fn-cat-p
    fn-cat-handles-inp fn-scol-okp fn-cat-count)))
  ("Subgoal *1/2" :use
   (fn-obc-one-preserves-carried-semantic-ready-from-columns
    fn-obc-one-carried-full-output-and-old-residual
    fn-obc-one-output-true-list))))

; Completion is separate from a finite quantum yielding with an exact
; residual. This corollary cites the induction above, not a new keystone.
(defthm fn-obc-source-run-completed-output-is-whole-old-reply
 (implies (and (fn-obc-semantic-ready-p s fn-arena fn-cat)
               (fn-cat-p fn-cat)
               (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat)
               (not (mv-nth 1 (fn-obc-source-run s steps fn-arena fn-cat))))
  (equal (mv-nth 0 (fn-obc-source-run s steps fn-arena fn-cat))
         (fn-obc-actual-old-residual s fn-arena fn-cat)))
 :rule-classes nil
 :hints (("Goal" :use fn-obc-source-run-complete-old-reply-and-carried-state
  :in-theory (e/d (fn-obc-actual-old-residual fn-obc-old-range-reply)
    (fn-obc-source-run fn-obc-semantic-ready-p fn-cat-p fn-cat-count
     fn-cat-handles-inp fn-scol-okp fn-ovw-lines fn-ovw-reply fn-npw-remaining)))))

(defun-nx fn-obc-quantum-old-reply (q fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (append (revappend (nth 2 q) nil)
         (fn-obc-actual-old-residual (nth 0 q) fn-arena fn-cat)))

(local
 (defthm fn-obrun-reverse-saved-extension
  (implies (true-listp out)
   (equal (revappend (revappend out prefix) nil)
          (append (revappend prefix nil) out)))
  :hints (("Goal" :induct (revappend out prefix)))))

; Concrete quantum adapter subject: FINISH of every returned quantum retains
; exactly the accumulated prefix plus the complete old reply continuation.
(defthm fn-obc-quantum-one-carried-complete-old-reply
 (implies (and (fn-obc-semantic-ready-p (nth 0 q) fn-arena fn-cat)
               (fn-scol-okp fn-arena fn-cat))
  (equal (fn-obc-quantum-old-reply (fn-obc-quantum-one q fn-arena fn-cat)
                                 fn-arena fn-cat)
         (fn-obc-quantum-old-reply q fn-arena fn-cat)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-obc-quantum-status q) :continue))
  :use ((:instance fn-obc-one-output-true-list (s (nth 0 q)))
        (:instance fn-obc-one-carried-full-output-and-old-residual (s (nth 0 q))))
  :in-theory
   (e/d (fn-obc-quantum-old-reply fn-obc-quantum-one fn-obc-quantum-status
         fn-obc-semantic-ready-p)
        (fn-obc-one fn-obc-statep fn-obc-parser-prefix-p fn-obc-parse-selection-p
         fn-obc-actual-old-residual fn-scol-okp nth revappend)))))
