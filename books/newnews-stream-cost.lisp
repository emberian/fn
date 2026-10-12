; NEWNEWS run cost: a configured cursor finishes in calls linear in its
; candidates. Every step of the stream either finishes or lowers an explicit
; calls potential by one: render (renderer micro-steps), select (nnm selector
; plus matcher microsteps), configured (eligibility, then the selector).
(in-package "ACL2")
(include-book "newnews-stream-cursor")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-nnw-sl-calls (work bytes)
  (declare (xargs :guard (and (natp work) (natp bytes)) :measure (nfix work)))
  (if (or (zp work) (zp bytes))
      0
    (+ 1 (fn-nnw-sl-calls (nfix (- work bytes)) bytes))))

(defthm fn-nnw-sl-calls-natp
  (natp (fn-nnw-sl-calls work bytes)) :rule-classes :type-prescription)

(local
 (defun fn-nnw-sl-calls-ind (a b bytes)
   (declare (xargs :measure (nfix b)))
   (if (or (zp b) (zp bytes))
       a
     (fn-nnw-sl-calls-ind (nfix (- a bytes)) (nfix (- b bytes)) bytes))))

(defthm fn-nnw-sl-calls-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (fn-nnw-sl-calls a bytes) (fn-nnw-sl-calls b bytes)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nnw-sl-calls-ind a b bytes))))

(defthm fn-nnw-sl-calls-positive
  (implies (and (posp work) (posp bytes)) (< 0 (fn-nnw-sl-calls work bytes)))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-nnw-sl-calls work bytes)))))

(defthm fn-nnw-sl-calls-step
  (implies (and (posp work) (posp bytes))
           (equal (fn-nnw-sl-calls work bytes)
                  (+ 1 (fn-nnw-sl-calls (nfix (- work bytes)) bytes))))
  :hints (("Goal" :expand ((fn-nnw-sl-calls work bytes)))))

; The renderer's remaining micro-steps: each fn-sl-one emits at most one octet.
(defun fn-nnw-line-work (cur)
  (declare (xargs :guard t))
  (let* ((text (fn-cur-at 0 cur)) (position (fn-cur-at 1 cur)) (phase (fn-cur-at 2 cur))
         (left (if (stringp text) (nfix (- (length text) (nfix position))) 0)))
    (cond ((not cur) 0)
          ((eq phase :stuff) (+ 3 left))
          ((eq phase :text) (+ 2 left))
          ((eq phase :cr) 2)
          ((eq phase :lf) 1)
          (t 0))))

(defun fn-nnw-linep (cur)
  (declare (xargs :guard t))
  (or (not cur)
      (let ((text (fn-cur-at 0 cur)) (position (fn-cur-at 1 cur)) (phase (fn-cur-at 2 cur)))
        (and (true-listp cur) (equal (len cur) 3) (natp position)
             (member-eq phase '(:stuff :text :cr :lf))
             (implies (member-eq phase '(:stuff :text))
                      (and (stringp text) (< position (length text))))))))

(defthm fn-nnw-line-work-positive
  (implies (and (fn-nnw-linep cur) cur)
           (< 0 (fn-nnw-line-work cur)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nnw-line-work fn-nnw-linep))))

(defthm fn-nnw-line-one
  (implies (and (fn-nnw-linep cur) cur)
           (and (fn-nnw-linep (mv-nth 1 (fn-sl-one cur)))
                (equal (fn-nnw-line-work (mv-nth 1 (fn-sl-one cur)))
                       (1- (fn-nnw-line-work cur)))))
  :hints (("Goal" :in-theory (enable fn-nnw-line-work fn-nnw-linep fn-sl-one fn-sl-make))))

(defthm fn-nnw-line-loop
  (implies (fn-nnw-linep cur)
           (and (fn-nnw-linep (mv-nth 1 (fn-sl-loop cur bytes acc)))
                (equal (fn-nnw-line-work (mv-nth 1 (fn-sl-loop cur bytes acc)))
                       (nfix (- (fn-nnw-line-work cur) (nfix bytes))))))
  :hints (("Goal" :induct (fn-sl-loop cur bytes acc)
           :in-theory (e/d ((:induction fn-sl-loop) fn-sl-loop)
                           (fn-nnw-line-work fn-nnw-linep fn-sl-one)))
          ("Subgoal *1/2" :use fn-nnw-line-one
           :in-theory (e/d (fn-sl-loop) (fn-nnw-line-one fn-nnw-line-work fn-nnw-linep fn-sl-one)))))

(defthm fn-nnw-line-start
  (and (fn-nnw-linep (fn-sl-start text))
       (<= (fn-nnw-line-work (fn-sl-start text)) (+ 3 (length text))))
  :hints (("Goal" :in-theory (enable fn-nnw-line-work fn-nnw-linep fn-sl-start fn-sl-make))))

; Selector potential: an upper bound on the nnm microsteps still to come,
; counting each configured group visit, each membership visit, and the matcher
; work of every group that can still start one.
(defun fn-nnw-match-work (patterns group)
  (declare (xargs :guard t :verify-guards nil))
  (fn-wmc-remaining (fn-wmc-start patterns group)))

(defun fn-nnw-match-sum (patterns groups)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp groups)
      (+ 1 (fn-nnw-match-work patterns (car groups))
         (fn-nnw-match-sum patterns (cdr groups)))
    0))

(defun fn-nnw-select-potential (ss)
  (declare (xargs :guard t :verify-guards nil))
  (+ (fn-nnw-select-remaining ss)
     (fn-nnw-match-sum (fn-nnw-select-at 1 ss) (fn-nnw-select-at 2 ss))
     (if (eq (fn-nnw-select-at 6 ss) :member)
         (+ 1 (fn-nnw-match-work (fn-nnw-select-at 1 ss) (fn-nnw-select-at 5 ss)))
       0)))

(defthm fn-nnw-select-potential-natp
  (natp (fn-nnw-select-potential ss)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-nnw-select-potential))))

(defthm fn-nnw-match-sum-natp
  (natp (fn-nnw-match-sum patterns groups)) :rule-classes :type-prescription)

(defthm fn-nnw-match-work-natp
  (natp (fn-nnw-match-work patterns group)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-nnw-match-work))))

(defthm fn-nnw-select-one-potential
  (implies (and (fn-nnw-select-statep ss)
                (not (mv-nth 0 (fn-nnw-select-one ss))))
           (<= (+ 1 (fn-nnw-select-potential (mv-nth 2 (fn-nnw-select-one ss))))
               (fn-nnw-select-potential ss)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-nnw-select-one fn-nnw-select-potential
                                   fn-nnw-select-remaining fn-nnw-select-state
                                   fn-nnw-select-statep fn-nnw-select-valid-numberp)
                                  (fn-nnw-match-work fn-wmc-remaining fn-wmc-start)))))

(defun fn-nnm-potential (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-nnm-matchp s)
      (+ (fn-nnw-select-potential (fn-nnw-select-at 2 s)) 1
         (fn-wmc-remaining (fn-nnw-select-at 1 s)))
    (fn-nnw-select-potential (fn-nnw-select-at 1 s))))

(defthm fn-nnm-potential-natp
  (natp (fn-nnm-potential s)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-nnm-potential))))

(local
 (defthm fn-nnw-after-membership-fields
   (and (equal (fn-nnw-select-at 1 (fn-nnm-after-membership sel matched)) (fn-nnw-select-at 1 sel))
        (equal (fn-nnw-select-at 2 (fn-nnm-after-membership sel matched)) (fn-nnw-select-at 2 sel))
        (equal (fn-nnw-select-at 3 (fn-nnm-after-membership sel matched)) (fn-nnw-select-at 3 sel))
        (equal (fn-nnw-select-at 6 (fn-nnm-after-membership sel nil)) :group))
   :hints (("Goal" :in-theory (enable fn-nnm-after-membership fn-nnw-select-state)))))

(local
 (defthm fn-nnw-after-membership-potential
   (implies (and (fn-nnw-select-statep sel) (fn-nnm-needs-matchp sel))
            (<= (+ 2 (fn-nnw-select-potential (fn-nnm-after-membership sel nil))
                   (fn-nnw-match-work (fn-nnw-select-at 1 sel) (fn-nnw-select-at 5 sel)))
                (fn-nnw-select-potential sel)))
   :rule-classes nil
   :hints (("Goal" :use (:instance fn-nnm-after-membership-progress (selector sel))
            :in-theory (e/d (fn-nnw-select-potential fn-nnm-needs-matchp)
                            (fn-nnm-after-membership-progress fn-nnm-after-membership
                             fn-nnw-match-work fn-nnw-select-remaining
                             fn-nnw-select-statep fn-nnw-select-valid-numberp))))))

(defthm fn-nnm-one-potential
  (implies (and (fn-nnm-statep s)
                (not (mv-nth 0 (fn-nnm-one s))))
           (<= (+ 1 (fn-nnm-potential (mv-nth 2 (fn-nnm-one s))))
               (fn-nnm-potential s)))
  :rule-classes :linear
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nnm-one fn-nnm-potential fn-nnm-matchp fn-nnm-match fn-nnm-entry
                            fn-nnm-statep fn-nnw-match-work)
                           (fn-nnw-select-one fn-wmc-start fn-wmc-step fn-wmc-shapedp
                            fn-wmc-remaining fn-nnm-after-membership fn-nnm-done
                            fn-nnm-needs-matchp fn-nnw-select-potential fn-wmc-decidedp
                            fn-wmc-matchedp fn-wmc-demand))
           :use ((:instance fn-nnw-select-one-potential (ss (fn-nnw-select-at 1 s)))
                 (:instance fn-nnw-after-membership-potential (sel (fn-nnw-select-at 1 s)))))))

; One candidate: the eligibility call, the nnm selector and matcher microsteps
; (including the deciding call), and the render calls of its Message-ID line.
(defun fn-nnw-candidate-calls (groups patterns article bytes)
  (declare (xargs :guard t :verify-guards nil))
  (+ 2
     (* (+ 2 (len (fn-article-memberships article))) (len groups))
     (fn-nnw-match-sum patterns groups)
     (fn-nnw-sl-calls (+ 3 (length (fn-article-msgid article))) bytes)))

; SOURCE is the cursor's group source (:configured patterns groups).
(defun fn-nnw-candidate-calls-sum (source tail bytes)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp tail)
      (+ (fn-nnw-candidate-calls (fn-cur-at 2 source) (fn-cur-at 1 source)
                                 (fn-ag-car tail) bytes)
         (fn-nnw-candidate-calls-sum source (fn-ag-cdr tail) bytes))
    0))

(defun fn-nnw-cfg-calls (progress bytes)
  (declare (xargs :guard t :verify-guards nil))
  (+ 1 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress) (fn-nnw-tail progress) bytes)))

; The calls owed once the current candidate is finished.
(defun fn-nnw-cfg-after (current bytes)
  (declare (xargs :guard t :verify-guards nil))
  (+ 1 (fn-nnw-candidate-calls-sum (fn-nnw-groups current)
                                   (fn-ag-cdr (fn-nnw-tail current)) bytes)))

(defun fn-nnw-stream-calls (progress bytes)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((not progress) 0)
        ((fn-nnw-stream-renderp progress)
         (+ (fn-nnw-sl-calls (fn-nnw-line-work (fn-cur-at 1 progress)) bytes)
            (if (fn-cur-at 2 progress) (fn-nnw-cfg-calls (fn-cur-at 2 progress) bytes) 1)))
        ((equal progress '(:terminator)) 1)
        ((fn-nnw-stream-selectp progress)
         (let ((current (fn-cur-at 2 progress)))
           (+ (fn-nnm-potential (fn-cur-at 1 progress)) 1
              (fn-nnw-sl-calls
               (+ 3 (length (fn-article-msgid (fn-ag-car (fn-nnw-tail current))))) bytes)
              (fn-nnw-cfg-after current bytes))))
        (t (fn-nnw-cfg-calls progress bytes))))

(defun fn-nnw-stream-goodp (p)
  (declare (xargs :guard t :verify-guards nil))
  (or (not p) (equal p '(:terminator)) (fn-nnw-configured-cursorp p)
      (and (fn-nnw-stream-selectp p)
           (fn-nnm-statep (fn-cur-at 1 p))
           (fn-nnw-configured-cursorp (fn-cur-at 2 p)))
      (and (fn-nnw-stream-renderp p)
           (fn-cur-at 1 p) (fn-nnw-linep (fn-cur-at 1 p))
           (or (not (fn-cur-at 2 p)) (fn-nnw-configured-cursorp (fn-cur-at 2 p))))))

(defthm fn-nnw-candidate-calls-sum-natp
  (natp (fn-nnw-candidate-calls-sum source tail bytes)) :rule-classes :type-prescription)

(defthm fn-nnw-candidate-calls-natp
  (natp (fn-nnw-candidate-calls groups patterns article bytes)) :rule-classes :type-prescription)

(defthm fn-nnw-candidate-calls-positive
  (<= 2 (fn-nnw-candidate-calls groups patterns article bytes)) :rule-classes :linear)

(defthm fn-nnw-candidate-calls-sum-of-atom
  (implies (not (consp tail))
           (equal (fn-nnw-candidate-calls-sum source tail bytes) 0)))

; The following cursor of a candidate owes exactly the after-calls.
(defthm fn-nnw-following-calls
  (equal (if (fn-nnw-stream-following current)
             (fn-nnw-cfg-calls (fn-nnw-stream-following current) bytes)
           1)
         (fn-nnw-cfg-after current bytes))
  :hints (("Goal" :in-theory (e/d (fn-nnw-stream-following fn-nnw-stream-scan-cursor
                                    fn-nnw-cfg-calls fn-nnw-cfg-after fn-nnw-groups
                                    fn-nnw-tail fn-nnw-at fn-ag-cdr)
                                   (fn-nnw-candidate-calls-sum)))))

(defthm fn-nnw-following-goodp
  (implies (fn-nnw-configured-cursorp current)
           (or (not (fn-nnw-stream-following current))
               (fn-nnw-configured-cursorp (fn-nnw-stream-following current))))
  :hints (("Goal" :in-theory (enable fn-nnw-stream-following fn-nnw-stream-scan-cursor
                                     fn-nnw-configured-cursorp fn-nnw-configuredp))))

(defthm fn-nnw-step-render
  (implies (and (posp bytes) (fn-nnw-stream-renderp p) (fn-nnw-stream-goodp p))
           (let ((q (mv-nth 1 (fn-nnw-stream-one p bytes fn-arena fn-cat))))
             (and (fn-nnw-stream-goodp q)
                  (<= (+ 1 (fn-nnw-stream-calls q bytes))
                      (fn-nnw-stream-calls p bytes)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nnw-line-loop (cur (fn-cur-at 1 p)) (acc nil))
                 (:instance fn-nnw-line-work-positive (cur (fn-cur-at 1 p)))
                 (:instance fn-nnw-sl-calls-step (work (fn-nnw-line-work (fn-cur-at 1 p)))))
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                            fn-nnw-stream-render fn-sl-step fn-nnw-stream-renderp
                            fn-nnw-stream-selectp fn-nnw-configuredp
                            fn-nnw-configured-cursorp)
                           (fn-sl-loop fn-nnw-line-loop fn-nnw-line-work-positive
                            fn-nnw-sl-calls-step fn-nnw-line-work fn-nnw-linep
                            fn-nnw-cfg-calls fn-nnw-sl-calls)))))
(defthm fn-nnw-step-terminator
  (implies (equal p '(:terminator))
           (let ((q (mv-nth 1 (fn-nnw-stream-one p bytes fn-arena fn-cat))))
             (and (fn-nnw-stream-goodp q)
                  (<= (+ 1 (fn-nnw-stream-calls q bytes))
                      (fn-nnw-stream-calls p bytes)))))
  :hints (("Goal" :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                                    fn-nnw-stream-renderp)
                                   ()))))

(defthm fn-nnw-step-select
  (implies (and (posp bytes) (fn-nnw-stream-selectp p)
                (fn-nnw-stream-goodp p))
           (let ((q (mv-nth 1 (fn-nnw-stream-one p bytes fn-arena fn-cat))))
             (and (fn-nnw-stream-goodp q)
                  (<= (+ 1 (fn-nnw-stream-calls q bytes))
                      (fn-nnw-stream-calls p bytes)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nnm-one-potential (s (fn-cur-at 1 p)))
                 (:instance fn-nnm-one-statep (s (fn-cur-at 1 p)))
                 (:instance fn-nnw-line-start (text (fn-article-msgid (fn-ag-car (fn-nnw-tail (fn-cur-at 2 p))))))
                 (:instance fn-nnw-following-calls (current (fn-cur-at 2 p)))
                 (:instance fn-nnw-following-goodp (current (fn-cur-at 2 p)))
                 (:instance fn-nnw-sl-calls-monotone
                            (a (fn-nnw-line-work (fn-sl-start (fn-article-msgid (fn-ag-car (fn-nnw-tail (fn-cur-at 2 p)))))))
                            (b (+ 3 (length (fn-article-msgid (fn-ag-car (fn-nnw-tail (fn-cur-at 2 p))))))))
                 (:instance fn-nnw-line-work-positive
                            (cur (fn-sl-start (fn-article-msgid (fn-ag-car (fn-nnw-tail (fn-cur-at 2 p))))))))
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                            fn-nnw-stream-selected fn-nnw-stream-select fn-nnw-stream-render
                            fn-nnw-stream-selectp fn-nnw-stream-renderp fn-nnw-configuredp
                            fn-nnw-configured-cursorp)
                           (fn-nnm-one fn-nnm-one-potential fn-nnm-one-statep fn-nnw-line-start
                            fn-nnw-following-calls fn-nnw-following-goodp fn-nnw-sl-calls-monotone
                            fn-nnw-line-work-positive fn-nnw-stream-following fn-nnw-stream-eligiblep
                            fn-nnw-sl-calls fn-nnw-line-work fn-nnw-linep fn-nnw-cfg-calls
                            fn-nnw-cfg-after fn-nnm-potential fn-sl-start fn-nnm-statep)))))
(defthm fn-nnm-start-potential
  (equal (fn-nnm-potential (fn-nnm-start patterns groups article))
         (+ (* (+ 2 (len (fn-article-memberships article))) (len groups))
            (fn-nnw-match-sum patterns groups)))
  :hints (("Goal" :in-theory (enable fn-nnm-start fn-nnm-entry fn-nnm-potential
                                     fn-nnm-matchp fn-nnw-select-start fn-nnw-select-state
                                     fn-nnw-select-potential fn-nnw-select-remaining))))

(defthm fn-nnw-step-configured
  (implies (and (posp bytes) (fn-nnw-configured-cursorp p))
           (let ((q (mv-nth 1 (fn-nnw-stream-one p bytes fn-arena fn-cat))))
             (and (fn-nnw-stream-goodp q)
                  (<= (+ 1 (fn-nnw-stream-calls q bytes))
                      (fn-nnw-stream-calls p bytes)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nnm-start-statep
                            (patterns (fn-cur-at 1 (fn-nnw-groups p)))
                            (groups (fn-cur-at 2 (fn-nnw-groups p)))
                            (article (fn-ag-car (fn-nnw-tail p))))
                 (:instance fn-nnm-start-potential
                            (patterns (fn-cur-at 1 (fn-nnw-groups p)))
                            (groups (fn-cur-at 2 (fn-nnw-groups p)))
                            (article (fn-ag-car (fn-nnw-tail p))))
                 (:instance fn-nnw-following-calls (current p))
                 (:instance fn-nnw-following-goodp (current p)))
           :in-theory (e/d (fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                            fn-nnw-stream-selected fn-nnw-stream-select fn-nnw-stream-render
                            fn-nnw-stream-selectp fn-nnw-stream-renderp fn-nnw-configuredp
                            fn-nnw-cfg-calls fn-nnw-cfg-after fn-nnw-candidate-calls-sum
                            fn-nnw-candidate-calls fn-ag-cdr fn-ag-car)
                           (fn-nnm-start-statep fn-nnm-start-potential fn-nnm-start
                            fn-nnw-following-calls fn-nnw-following-goodp
                            fn-nnw-stream-following fn-nnw-stream-eligiblep
                            fn-nnm-potential fn-nnm-statep fn-nnw-sl-calls
                            fn-nnw-candidate-calls-sum-of-atom)))))
(defthm fn-nnw-step-good
  (implies (and (posp bytes) p (fn-nnw-stream-goodp p))
           (let ((q (mv-nth 1 (fn-nnw-stream-one p bytes fn-arena fn-cat))))
             (and (fn-nnw-stream-goodp q)
                  (<= (+ 1 (fn-nnw-stream-calls q bytes))
                      (fn-nnw-stream-calls p bytes)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-nnw-step-render fn-nnw-step-terminator fn-nnw-step-select
                 fn-nnw-step-configured)
           :in-theory (e/d (fn-nnw-stream-goodp fn-nnw-configured-cursorp fn-nnw-configuredp
                            fn-nnw-stream-selectp fn-nnw-stream-renderp)
                           (fn-nnw-step-render fn-nnw-step-terminator fn-nnw-step-select
                            fn-nnw-step-configured fn-nnw-stream-one fn-nnw-stream-calls)))))

; Apply fn-nnw-stream-one to PROGRESS up to N times, stopping when the next
; progress is NIL; answers the progress left (NIL when the run finished).
(defun fn-nnw-stream-run (progress bytes n fn-arena fn-cat)
  (declare (xargs :guard (and (natp bytes) (natp n)) :stobjs (fn-arena fn-cat) :measure (nfix n)
                  :verify-guards nil))
  (if (or (zp n) (null progress))
      progress
    (mv-let (octets next) (fn-nnw-stream-one progress bytes fn-arena fn-cat)
      (declare (ignore octets))
      (fn-nnw-stream-run next bytes (1- n) fn-arena fn-cat))))

(defthm fn-nnw-stream-calls-natp
  (natp (fn-nnw-stream-calls progress bytes)) :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-nnw-stream-calls fn-nnw-cfg-calls fn-nnw-cfg-after))))

(defthm fn-nnw-stream-calls-positive
  (implies (and (posp bytes) progress (fn-nnw-stream-goodp progress))
           (<= 1 (fn-nnw-stream-calls progress bytes)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-nnw-step-good (p progress))
                        (:instance fn-nnw-stream-calls-natp
                                   (progress (mv-nth 1 (fn-nnw-stream-one progress bytes fn-arena fn-cat)))))
           :in-theory (disable fn-nnw-step-good fn-nnw-stream-calls-natp fn-nnw-stream-one
                               fn-nnw-stream-calls fn-nnw-stream-goodp))))

(defthm fn-nnw-stream-run-finishes
  (implies (and (posp bytes) (natp n) (fn-nnw-stream-goodp progress)
                (<= (fn-nnw-stream-calls progress bytes) n))
           (null (fn-nnw-stream-run progress bytes n fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-nnw-stream-run progress bytes n fn-arena fn-cat)
           :in-theory (disable fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                               fn-nnw-step-good))
          ("Subgoal *1/2" :use ((:instance fn-nnw-step-good (p progress)))
           :in-theory (disable fn-nnw-stream-one fn-nnw-stream-goodp fn-nnw-stream-calls
                               fn-nnw-step-good))))

(defthm fn-nnw-stream-run-is-linear-in-candidates
  (implies (and (posp bytes) (fn-nnw-configured-cursorp progress))
           (null (fn-nnw-stream-run
                  progress bytes
                  (+ 2 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress)
                                                   (fn-nnw-tail progress) bytes))
                  fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-nnw-stream-run-finishes
                                   (n (+ 2 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress)
                                                                       (fn-nnw-tail progress) bytes)))))
           :in-theory (e/d (fn-nnw-stream-goodp fn-nnw-stream-calls fn-nnw-cfg-calls
                            fn-nnw-configured-cursorp fn-nnw-configuredp fn-nnw-stream-selectp
                            fn-nnw-stream-renderp)
                           (fn-nnw-stream-run-finishes fn-nnw-stream-run)))))
(local
 (defthm fn-nnw-utf8-rest-shorter
   (implies (fn-wildmat-result-okp (fn-wildmat-utf8-next xs))
            (< (len (fn-wildmat-utf8-rest (fn-wildmat-utf8-next xs))) (len xs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-wildmat-utf8-next fn-wildmat-result-okp
                                      fn-wildmat-utf8-rest fn-wildmat-utf8-ok fn-wildmat-error)))))

(local
 (defthm fn-nnw-utf8-count-bound
   (<= (fn-wmc-utf8-count xs) (+ 1 (len xs)))
   :rule-classes nil
   :hints (("Goal" :induct (fn-wmc-utf8-count xs)
            :in-theory (e/d (fn-wmc-utf8-count) (fn-wildmat-utf8-next fn-wildmat-utf8-rest
                                                  fn-wildmat-result-okp))))))

(local
 (defthm fn-nnw-decode-length-bound
   (implies (and (true-listp acc) (fn-wildmat-result-okp (fn-wildmat-decode-aux xs acc)))
            (<= (len (fn-wildmat-result-value (fn-wildmat-decode-aux xs acc)))
                (+ (len xs) (len acc))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-wildmat-decode-aux xs acc)
            :in-theory (e/d (fn-wildmat-decode-aux)
                            (fn-wildmat-utf8-next fn-wildmat-utf8-rest))))))
(local
 (defthm fn-nnw-times-monotone
   (implies (and (natp a) (natp b) (natp c) (<= a b))
            (<= (* c a) (* c b)))
   :rule-classes nil))

(defthm fn-nnw-match-steps-bound
  (implies (<= (len target) 497)
           (<= (fn-wmc-match-steps patterns target)
               (+ 3 (* 12 (len patterns)) (* 1988 (len patterns))
                  (* 1000 (fn-wm-total-items patterns)))))
  :hints (("Goal" :use ((:instance fn-wmc-right-steps-bound)
                        (:instance fn-nnw-times-monotone (a (len target)) (b 497) (c (len patterns)))
                        (:instance fn-nnw-times-monotone (a (len target)) (b 497)
                                   (c (fn-wm-total-items patterns))))
           :in-theory (e/d (fn-wmc-match-steps) (fn-wmc-right-steps fn-wmc-right-steps-bound)))))
(local
 (defthm fn-nnw-match-work-non-string
   (<= (fn-wmc-remaining (fn-wmc-start-codepoints patterns nil))
       (+ 1000 (* 2000 (len patterns)) (* 1000 (fn-wm-total-items patterns))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-wmc-core-codepoint-start-work-bound (target nil)))
            :in-theory (e/d (fn-wmc-remaining fn-wmc-start-codepoints fn-wmc-state fn-wmc-node fn-wmc-at)
                            (fn-wmc-core-codepoint-start-work-bound fn-wmc-core-remaining))))))

(local
 (defthm fn-nnw-match-work-return
   (equal (fn-wmc-remaining (fn-wmc-state (fn-wmc-return nil 0) nil)) 0)
   :hints (("Goal" :in-theory (e/d (fn-wmc-remaining fn-wmc-core-remaining fn-wmc-task-steps
                                     fn-wmc-stack-steps fn-wmc-return fn-wmc-node fn-wmc-state
                                     fn-wmc-at))))))
(local
 (defthm fn-nnw-octets-aux-len
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-nnw-match-work-utf8
   (implies (and (stringp group) (<= (length group) 497))
            (<= (fn-wmc-remaining (fn-wmc-state (fn-wmc-node :utf8 patterns group 0 nil) nil))
                (+ 1000 (* 2000 (len patterns)) (* 1000 (fn-wm-total-items patterns)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-nnw-utf8-count-bound
                             (xs (fn-nntp-string-octets-aux (coerce group 'list))))
                  (:instance fn-nnw-decode-length-bound (acc nil)
                             (xs (fn-nntp-string-octets-aux (coerce group 'list))))
                  (:instance fn-nnw-match-steps-bound
                             (target (fn-wildmat-result-value
                                      (fn-wildmat-decode-aux
                                       (fn-nntp-string-octets-aux (coerce group 'list)) nil)))))
            :in-theory (e/d (fn-wmc-remaining fn-wmc-state fn-wmc-node fn-wmc-at length)
                            (fn-wmc-utf8-count fn-wildmat-decode-aux fn-wmc-match-steps
                             fn-nnw-match-steps-bound fn-nntp-string-octets-aux))))))
; The matcher work of any group name, closed form in the parsed patterns.
(defun fn-nnw-match-bound (patterns)
  (declare (xargs :guard t :verify-guards nil))
  (+ 1000 (* 2000 (len patterns)) (* 1000 (fn-wm-total-items patterns))))

(defthm fn-nnw-match-work-bound
  (<= (fn-nnw-match-work patterns group) (fn-nnw-match-bound patterns))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-nnw-match-work fn-nnw-match-bound fn-wmc-start)
                                  (fn-wmc-remaining fn-wmc-start-codepoints fn-wmc-state
                                   fn-wmc-node fn-wmc-return))
           :use (fn-nnw-match-work-non-string fn-nnw-match-work-return
                 (:instance fn-nnw-match-work-utf8)))))

(defthm fn-nnw-match-sum-bound
  (<= (fn-nnw-match-sum patterns groups)
      (* (len groups) (+ 1 (fn-nnw-match-bound patterns))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nnw-match-sum patterns groups)
           :in-theory (disable fn-nnw-match-work fn-nnw-match-bound fn-nnw-match-work-bound)
           :do-not-induct nil)
          ("Subgoal *1/1" :use ((:instance fn-nnw-match-work-bound (group (car groups))))
           :in-theory (disable fn-nnw-match-work fn-nnw-match-bound fn-nnw-match-work-bound))))

(defthm fn-nnw-sl-calls-at-most-work
  (implies (and (posp bytes) (natp work))
           (<= (fn-nnw-sl-calls work bytes) work))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nnw-sl-calls work bytes))))

; The uniform bound: with BYTES >= 1 one candidate takes at most
;   5 + |msgid| + |configured groups| * (|memberships| + 3 + B(patterns))
; calls, B(patterns) = 1000 + 2000 |patterns| + 1000 (total pattern items).
(defthm fn-nnw-candidate-calls-uniform
  (implies (posp bytes)
           (<= (fn-nnw-candidate-calls groups patterns article bytes)
               (+ 5 (length (fn-article-msgid article))
                  (* (len groups)
                     (+ 3 (len (fn-article-memberships article))
                        (fn-nnw-match-bound patterns))))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-nnw-sl-calls-at-most-work
                                   (work (+ 3 (length (fn-article-msgid article)))))
                        (:instance fn-nnw-match-sum-bound))
           :in-theory (e/d (fn-nnw-candidate-calls)
                           (fn-nnw-sl-calls-at-most-work fn-nnw-match-sum-bound
                            fn-nnw-match-bound fn-nnw-sl-calls)))))

; The host's factory establishes the keystone's one state hypothesis: whenever
; it answers a NEWNEWS cursor effect, that cursor's progress is a configured
; cursor. Nothing else about the cursor is assumed by the keystone.
(defthm fn-nntp-newnews-response-stream-cursor-configured
  (let* ((result (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat))
         (effect (car (cdr result))))
    (implies (fn-nnw-meta-effectp effect)
             (fn-nnw-configured-cursorp (fn-cur-progress (car (cdr effect))))))
  :hints (("Goal" :in-theory (enable fn-nntp-newnews-response-stream fn-nntp-make-result
                                     fn-nntp-single fn-nnw-meta-effect fn-nnw-meta-effectp
                                     fn-nntp-reply-effect fn-cur-make fn-cur-progress fn-cur-at
                                     fn-nnw-stream-scan-cursor fn-nnw-configured-cursorp
                                     fn-nnw-configuredp))))

; The host's cursor, run at any positive quantum, finishes within two calls
; plus the sum of its candidates' calls.
(defthm fn-nntp-newnews-response-stream-run-is-linear
  (let* ((result (fn-nntp-newnews-response-stream session archive env args fn-arena fn-cat))
         (effect (car (cdr result)))
         (progress (fn-cur-progress (car (cdr effect)))))
    (implies (and (posp bytes) (fn-nnw-meta-effectp effect))
             (null (fn-nnw-stream-run
                    progress bytes
                    (+ 2 (fn-nnw-candidate-calls-sum (fn-nnw-groups progress)
                                                     (fn-nnw-tail progress) bytes))
                    fn-arena fn-cat))))
  :hints (("Goal" :use ((:instance fn-nntp-newnews-response-stream-cursor-configured)
                        (:instance fn-nnw-stream-run-is-linear-in-candidates
                                   (progress (fn-cur-progress
                                              (car (cdr (car (cdr (fn-nntp-newnews-response-stream
                                                                   session archive env args fn-arena fn-cat)))))))))
           :in-theory (disable fn-nnw-stream-run-is-linear-in-candidates
                               fn-nntp-newnews-response-stream-cursor-configured
                               fn-nnw-stream-run fn-nnw-candidate-calls-sum))))
