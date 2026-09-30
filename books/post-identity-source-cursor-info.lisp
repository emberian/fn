; Proof-only exact Injection-Info agent span and paid cursor trace.
(in-package "ACL2")
(include-book "post-identity-source-cursor-msgid")
(local (include-book "arithmetic/top" :dir :system))

(local (defthm fn-psc-param-rest-first-line
 (implies (true-listp xs)
  (equal (fn-inj-param-rest (fn-pb-line xs))
         (if (equal (fn-inj-param-rest xs) :no) :no nil)))
 :hints (("Goal" :induct (fn-inj-param-rest xs)
          :in-theory (enable fn-inj-param-rest fn-pb-line true-listp)))))

(local (defthm fn-psc-semicolon-absent-is-no-member
 (equal (equal (fn-pb-upto-semicolon xs) :no)
        (not (member-equal 59 xs)))
 :hints (("Goal" :induct (fn-pb-upto-semicolon xs)
          :in-theory (enable fn-pb-upto-semicolon member-equal)))))

(local (defthm fn-psc-semicolon-prefix-is-proper
 (implies (not (equal (fn-pb-upto-semicolon xs) :no))
  (true-listp (fn-pb-upto-semicolon xs)))
 :hints (("Goal" :induct (fn-pb-upto-semicolon xs)
          :in-theory (enable fn-pb-upto-semicolon)))))

(local (defthm fn-psc-semicolon-prefix-span
 (implies (not (equal (fn-pb-upto-semicolon xs) :no))
  (let* ((prefix (fn-pb-upto-semicolon xs)) (count (len prefix)) (tail (nthcdr count xs)))
   (and (< count (len xs))
        (not (member-equal 59 prefix))
        (equal (fn-inj-take count xs) prefix)
        (equal (fn-inj-strip prefix xs) tail)
        (consp tail) (equal (car tail) 59))))
 :hints (("Goal" :induct (fn-pb-upto-semicolon xs)
  :in-theory (enable fn-pb-upto-semicolon fn-inj-take fn-inj-strip nthcdr len nfix member-equal)))))

(local (defthm fn-psc-strip-success-reconstructs
 (implies (and (true-listp prefix) (true-listp xs)
               (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (append prefix (fn-inj-strip prefix xs)) xs))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip append true-listp)))))

(local (defthm fn-psc-strip-append-prefix
 (implies (true-listp a)
  (equal (fn-inj-strip (append a b) xs)
         (fn-inj-strip b (fn-inj-strip a xs))))
 :hints (("Goal" :induct (fn-inj-strip a xs)
  :in-theory (enable fn-inj-strip append true-listp)))))

(local (defthm fn-psc-append-prefix-cancels
 (implies (true-listp prefix)
  (equal (equal (append prefix a) (append prefix b)) (equal a b)))
 :hints (("Goal" :induct (len prefix) :in-theory (enable append len true-listp)))))

(local (defthm fn-psc-strip-take-is-drop
 (implies (true-listp xs)
  (equal (fn-inj-strip (fn-inj-take k xs) xs) (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-take k xs)
  :in-theory (enable fn-inj-take fn-inj-drop fn-inj-strip true-listp)))))

(local (defthm fn-psc-take-and-fixed-tail-equality
 (implies (true-listp xs)
  (equal (equal (append (fn-inj-take k xs) tail) xs)
         (equal tail (fn-inj-drop k xs))))
 :hints (("Goal" :induct (fn-inj-take k xs)
  :in-theory (enable fn-inj-take fn-inj-drop append true-listp)))))

(local (defthm fn-psc-inj-append-is-append
 (equal (fn-inj-append xs ys) (append xs ys))
 :hints (("Goal" :induct (len xs) :in-theory (enable fn-inj-append append len)))))

(local (defthm fn-psc-first-line-true-list
 (true-listp (fn-pb-line xs))
 :hints (("Goal" :induct (fn-pb-line xs) :in-theory (enable fn-pb-line)))))

(local (defthm fn-psc-drop-preserves-true-list
 (implies (true-listp xs) (true-listp (fn-inj-drop k xs)))
 :hints (("Goal" :induct (fn-inj-drop k xs) :in-theory (enable fn-inj-drop)))))

(local (defthm fn-psc-info-agent-plain-normal-form
 (equal (fn-pb-info-line-agent xs)
  (let* ((line (fn-pb-line xs)) (r (fn-inj-strip *fn-inj-injection-info-field* line))
         (count (- (len r) 2)) (agent (fn-inj-take count r)))
   (or (if (and (true-listp r) (< 2 (len r))
                (equal (fn-inj-drop count r) '(13 10))
                (not (member-equal 59 agent))) agent nil)
       (fn-pb-params-line-agent line))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-strip-success-reconstructs
         (prefix *fn-inj-injection-info-field*) (xs (fn-pb-line xs)))
        (:instance fn-psc-take-and-fixed-tail-equality
         (xs (fn-inj-strip *fn-inj-injection-info-field* (fn-pb-line xs)))
         (k (- (len (fn-inj-strip *fn-inj-injection-info-field* (fn-pb-line xs))) 2))
         (tail '(13 10))))
  :in-theory (e/d (fn-pb-info-line-agent fn-inj-injection-info-line)
   (fn-pb-line fn-inj-strip fn-inj-take fn-inj-drop len binary-append
    fn-pb-params-line-agent fn-psc-strip-success-reconstructs fn-psc-take-and-fixed-tail-equality))))))

(local (defthm fn-psc-semicolon-prefix-cannot-be-plain-line
 (implies (not (equal (fn-pb-upto-semicolon xs) :no))
  (equal (fn-inj-strip (append (fn-pb-upto-semicolon xs) '(13 10)) xs) :no))
 :hints (("Goal" :induct (fn-pb-upto-semicolon xs)
          :in-theory (enable fn-pb-upto-semicolon fn-inj-strip binary-append)))))

(local (defthm fn-psc-info-parameter-strip-is-first-semicolon-tail
 (implies (and (true-listp xs)
               (consp (fn-pb-upto-semicolon (fn-inj-strip *fn-inj-injection-info-field* xs))))
  (let* ((r (fn-inj-strip *fn-inj-injection-info-field* xs))
         (prefix (fn-pb-upto-semicolon r)))
   (equal (fn-inj-strip-info prefix xs)
          (fn-inj-param-rest (nthcdr (len prefix) r)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-semicolon-prefix-is-proper (xs (fn-inj-strip *fn-inj-injection-info-field* xs)))
        (:instance fn-psc-semicolon-prefix-span (xs (fn-inj-strip *fn-inj-injection-info-field* xs)))
        (:instance fn-psc-strip-append-prefix
         (a *fn-inj-injection-info-field*)
         (b (append (fn-pb-upto-semicolon (fn-inj-strip *fn-inj-injection-info-field* xs)) '(13 10))))
        (:instance fn-psc-strip-append-prefix
         (a (fn-pb-upto-semicolon (fn-inj-strip *fn-inj-injection-info-field* xs)))
         (b '(13 10)) (xs (fn-inj-strip *fn-inj-injection-info-field* xs)))
        (:instance fn-psc-strip-append-prefix
         (a *fn-inj-injection-info-field*)
         (b (fn-pb-upto-semicolon (fn-inj-strip *fn-inj-injection-info-field* xs)))))
  :expand ((fn-inj-strip '(13 10)
             (nthcdr (len (fn-pb-upto-semicolon (fn-inj-strip *fn-inj-injection-info-field* xs)))
                     (fn-inj-strip *fn-inj-injection-info-field* xs))))
  :in-theory (e/d (fn-inj-strip-info fn-inj-injection-info-line)
   (fn-inj-strip fn-inj-param-rest fn-pb-upto-semicolon nth nthcdr len binary-append
    fn-psc-semicolon-absent-is-no-member fn-psc-strip-append-prefix fn-psc-semicolon-prefix-span))))))

(local (defthm fn-psc-info-params-agent-normal-form
 (equal (fn-pb-params-line-agent (fn-pb-line xs))
  (let* ((r (fn-inj-strip *fn-inj-injection-info-field* (fn-pb-line xs)))
         (prefix (fn-pb-upto-semicolon r)))
   (if (and (consp prefix)
            (equal (fn-inj-param-rest (nthcdr (len prefix) r)) nil)) prefix nil)))
 :hints (("Goal" :in-theory (e/d (fn-pb-params-line-agent)
   (fn-pb-line fn-inj-strip fn-inj-strip-info fn-inj-param-rest fn-pb-upto-semicolon nthcdr len))))))

(local (defthm fn-psc-line-step-preserves-slot
 (implies (and (equal (fn-psc-get phase c) :line) (natp slot)
               (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-step c byte)) (nth slot c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-return nfix)
                               (nth update-nth len))))))

(local (defthm fn-psc-line-complete-preserves-slot
 (implies (and (natp slot) (not (member-equal slot '(0 7 15 21 22))))
  (equal (nth slot (fn-psc-model-line-complete c incoming held)) (nth slot c)))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-preserves-state
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (fn-psc-line-statep (fn-psc-model-line-complete c incoming held) incoming held))
 :hints (("Goal" :induct (fn-psc-model-line-complete c incoming held)
  :in-theory (e/d (fn-psc-model-line-complete)
                  (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(local (defthm fn-psc-line-complete-exact-position
 (implies (and (fn-psc-line-statep c incoming held)
               (equal (fn-psc-get phase c) :line))
  (equal (fn-psc-get pos (fn-psc-model-line-complete c incoming held))
         (+ (fn-psc-get pos c)
            (len (fn-pb-line (nthcdr (fn-psc-get pos c) (fn-psc-model-source c incoming held)))))))
 :hints (("Goal" :use (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state)
  :in-theory (e/d (fn-psc-model-line-end fn-psc-line-statep nfix)
   (fn-psc-line-complete-preserves-value fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state
    fn-psc-model-line-complete nth nthcdr len))))))

(defun fn-psc-info-agent-statep (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-psc-get mode c) :agent) (equal (fn-psc-get phase c) :control)
      (equal (fn-psc-get resume c) :agent-info-field) (fn-psc-get ok c)
      (true-listp incoming) (equal (fn-psc-get n c) (len incoming))
      (natp (fn-psc-get pos c)) (<= (fn-psc-get pos c) (len incoming))
      (natp (fn-psc-get base c)) (equal (fn-psc-get pos c) (+ 16 (fn-psc-get base c)))
      (not (equal (fn-inj-strip *fn-inj-injection-info-field* (nthcdr (fn-psc-get base c) incoming)) :no))))

(defun fn-psc-model-info-agent-scan (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (fn-psc-model-line-complete (fn-psc-step c nil) incoming nil))

(defun fn-psc-model-info-agent-complete (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)))
  (if (equal (fn-psc-get phase d) :params)
      (fn-psc-step (fn-psc-model-param-complete d incoming nil) nil) d)))

(local (defthm fn-psc-info-field-starts-content-line-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-info-field) (fn-psc-get ok c)
               (natp (fn-psc-get pos c)))
  (equal (fn-psc-step c byte)
   (fn-psc-set phase :line (fn-psc-set resume :agent-info-line
    (fn-psc-set agent-start (fn-psc-get pos c) (fn-psc-set semi nil (fn-psc-set prev nil c)))))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix) (nth len update-nth))))))

(defthm fn-psc-info-agent-scan-frame
 (implies (fn-psc-info-agent-statep c incoming)
  (let* ((d (fn-psc-model-info-agent-scan c incoming))
         (a (fn-psc-get pos c)) (line (fn-pb-line (nthcdr a incoming)))
         (prefix (fn-pb-upto-semicolon line)))
   (and (equal (fn-psc-get phase d) :control)
        (equal (fn-psc-get resume d) :agent-info-line)
        (equal (fn-psc-get mode d) :agent)
        (equal (fn-psc-get agent-start d) a)
        (equal (fn-psc-get n d) (len incoming))
        (equal (fn-psc-get pos d) (+ a (len line)))
        (natp (fn-psc-get pos d)) (<= (fn-psc-get pos d) (len incoming))
        (equal (fn-psc-get prev d) (fn-psc-model-line-last line nil))
        (equal (fn-psc-get semi d) (if (equal prefix :no) nil (+ a (len prefix))))
        (equal (if (fn-psc-get ok d) t nil) (if (member-equal 10 line) t nil)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-line-complete-returns-control (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-preserves-state (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-exact-position (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-exact-prev (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-exact-first-semicolon (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-line-complete-exact-ok (c (fn-psc-step c nil)) (held nil)))
  :in-theory (e/d (fn-psc-info-agent-statep fn-psc-model-info-agent-scan
                   fn-psc-line-statep fn-psc-model-source fn-psc-model-line-prev
                   fn-psc-model-line-semi fn-psc-model-line-ok nfix)
   (fn-psc-model-line-complete fn-psc-step fn-psc-model-line-last fn-pb-line
    fn-inj-strip fn-pb-upto-semicolon nth nthcdr len update-nth
    fn-psc-line-complete-returns-control fn-psc-line-complete-preserves-state
    fn-psc-line-complete-exact-position fn-psc-line-complete-exact-prev
    fn-psc-line-complete-exact-first-semicolon fn-psc-line-complete-exact-ok)))))

(local (defthm fn-psc-info-line-control-unfolds
 (implies (and (equal (fn-psc-get phase c) :control)
               (equal (fn-psc-get resume c) :agent-info-line)
               (natp (fn-psc-get pos c)) (natp (fn-psc-get agent-start c)))
  (equal (fn-psc-step c byte)
   (let ((a (fn-psc-get agent-start c)) (p (fn-psc-get pos c)) (semi (fn-psc-get semi c)))
    (if (and (fn-psc-get ok c) (equal (fn-psc-get prev c) 13) (< (+ a 2) p))
        (if semi
            (if (< a (nfix semi))
                (fn-psc-set phase :params (fn-psc-set pos (nfix semi)
                 (fn-psc-set agent-end semi (fn-psc-set resume :agent-params c))))
              (fn-psc-finish :no-source c))
          (fn-psc-finish (list :agent a (- p 2)) c))
      (fn-psc-finish :no-source c)))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-control nfix)
                                (nth len update-nth))))))

(local (defthm fn-psc-consp-has-positive-length
 (implies (consp x) (< 0 (len x)))
 :hints (("Goal" :in-theory (enable len)))
 :rule-classes :linear))

(defthm fn-psc-info-agent-complete-result
 (implies (fn-psc-info-agent-statep c incoming)
  (let* ((a (fn-psc-get pos c)) (line (fn-pb-line (nthcdr a incoming)))
         (prefix (fn-pb-upto-semicolon line))
         (valid (and (member-equal 10 line) (equal (fn-psc-model-line-last line nil) 13) (< 2 (len line)))))
   (equal (fn-psc-result (fn-psc-model-info-agent-complete c incoming))
    (if valid
        (if (equal prefix :no)
            (list :agent a (+ a (len line) -2))
          (if (and (consp prefix)
                   (not (equal (fn-inj-param-rest (nthcdr (+ a (len prefix)) incoming)) :no)))
              (list :agent a (+ a (len prefix))) :no-source)) :no-source))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-consp-has-positive-length (x (fn-pb-upto-semicolon (fn-pb-line (nthcdr (fn-psc-get pos c) incoming)))))
        fn-psc-info-agent-scan-frame
        (:instance fn-psc-semicolon-prefix-span (xs (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))))
        (:instance fn-psc-semicolon-prefix-is-proper (xs (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))))
        (:instance fn-psc-agent-parameter-result
         (c (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)) (held nil)))
  :in-theory (e/d (fn-psc-info-agent-statep fn-psc-model-info-agent-complete
                   fn-psc-finish fn-psc-result fn-psc-line-statep fn-psc-model-source nfix)
   (fn-psc-step fn-psc-control fn-psc-model-info-agent-scan fn-psc-model-param-complete fn-psc-agent-parameter-result
    fn-psc-info-agent-scan-frame fn-psc-semicolon-prefix-span fn-psc-semicolon-prefix-is-proper
    fn-psc-semicolon-absent-is-no-member fn-pb-line fn-pb-upto-semicolon fn-inj-strip
    fn-inj-param-rest fn-psc-model-line-last nth nthcdr len update-nth)))))

(local (defthm fn-psc-first-line-one-byte
 (implies (equal (len (fn-pb-line xs)) 1)
  (equal (fn-pb-line xs) (list (car xs))))
 :hints (("Goal" :induct (fn-pb-line xs) :in-theory (enable fn-pb-line len)))))

(local (defthm fn-psc-first-line-crlf-tail
 (implies (< 1 (len (fn-pb-line xs)))
  (equal (equal (fn-inj-drop (- (len (fn-pb-line xs)) 2) (fn-pb-line xs)) '(13 10))
         (and (member-equal 10 (fn-pb-line xs))
              (equal (fn-psc-model-line-last (fn-pb-line xs) prev) 13))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-psc-model-line-last xs prev)
  :in-theory (enable fn-pb-line fn-inj-drop fn-psc-model-line-last len member-equal nfix zp))
 ("Subgoal *1/2" :cases ((< 1 (len (fn-pb-line (cdr xs)))))))))

(local (defthm fn-psc-semicolon-append-crlf
 (implies (true-listp agent)
  (equal (fn-pb-upto-semicolon (append agent '(13 10)))
         (fn-pb-upto-semicolon agent)))
 :hints (("Goal" :induct (len agent)
  :in-theory (enable fn-pb-upto-semicolon append len true-listp)))))

(local (defthm fn-psc-plain-agent-semicolon-criterion
 (implies (and (true-listp line) (< 2 (len line))
               (equal (fn-inj-drop (- (len line) 2) line) '(13 10)))
  (equal (not (member-equal 59 (fn-inj-take (- (len line) 2) line)))
         (equal (fn-pb-upto-semicolon line) :no)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-take-and-fixed-tail-equality (xs line) (k (- (len line) 2)) (tail '(13 10)))
        (:instance fn-psc-semicolon-append-crlf (agent (fn-inj-take (- (len line) 2) line)))
        (:instance fn-psc-semicolon-absent-is-no-member (xs (fn-inj-take (- (len line) 2) line))))
  :in-theory (disable fn-inj-take fn-inj-drop fn-pb-upto-semicolon len binary-append
                      fn-psc-take-and-fixed-tail-equality fn-psc-semicolon-append-crlf
                      fn-psc-semicolon-absent-is-no-member)))))

(local (defthm fn-psc-successful-params-line-is-crlf
 (implies (not (equal (fn-inj-param-rest xs) :no))
  (and (member-equal 10 (fn-pb-line xs))
       (equal (fn-psc-model-line-last (fn-pb-line xs) prev) 13)
       (< 1 (len (fn-pb-line xs)))))
 :hints (("Goal" :induct (fn-psc-model-line-last xs prev)
  :in-theory (enable fn-inj-param-rest fn-pb-line fn-psc-model-line-last len member-equal)))))

(local (defthm fn-psc-semicolon-prefix-before-first-lf
 (implies (not (equal (fn-pb-upto-semicolon (fn-pb-line xs)) :no))
  (not (member-equal 10 (fn-pb-upto-semicolon (fn-pb-line xs)))))
 :hints (("Goal" :induct (fn-pb-line xs)
  :in-theory (enable fn-pb-line fn-pb-upto-semicolon member-equal)))))

(local (defthm fn-psc-line-of-prefix-without-lf
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)))
  (equal (fn-pb-line (append prefix xs)) (append prefix (fn-pb-line xs))))
 :hints (("Goal" :induct (len prefix)
  :in-theory (enable fn-pb-line append len true-listp member-equal)))))

(local (defthm fn-psc-line-last-of-prefix-without-lf
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)) (consp xs)
               (not (equal (car xs) 10)))
  (equal (fn-psc-model-line-last (append prefix xs) prev)
         (fn-psc-model-line-last xs other)))
 :hints (("Goal" :induct (fn-psc-model-line-last prefix prev)
  :in-theory (enable fn-psc-model-line-last append len true-listp member-equal)))))

(local (defthm fn-psc-line-idempotent
 (equal (fn-pb-line (fn-pb-line xs)) (fn-pb-line xs))
 :hints (("Goal" :induct (fn-pb-line xs) :in-theory (enable fn-pb-line)))))

(local (defthm fn-psc-member-of-append
 (iff (member-equal x (append a b)) (or (member-equal x a) (member-equal x b)))
 :hints (("Goal" :induct (len a) :in-theory (enable append member-equal len)))))

(local (defthm fn-psc-length-of-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable append len)))))

(local (defthm fn-psc-parameter-agent-line-is-valid
 (implies (and (true-listp xs)
               (consp (fn-pb-upto-semicolon (fn-pb-line xs)))
               (not (equal (fn-inj-param-rest
                  (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs))) :no)))
  (and (member-equal 10 (fn-pb-line xs))
       (equal (fn-psc-model-line-last (fn-pb-line xs) nil) 13)
       (< 2 (len (fn-pb-line xs)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-member-of-append (x 10)
         (a (fn-pb-upto-semicolon (fn-pb-line xs)))
         (b (fn-pb-line (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs)))))
        (:instance fn-psc-length-of-append
         (a (fn-pb-upto-semicolon (fn-pb-line xs)))
         (b (fn-pb-line (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs)))))
        (:instance fn-psc-consp-has-positive-length (x (fn-pb-upto-semicolon (fn-pb-line xs))))
        (:instance fn-psc-semicolon-prefix-span (xs (fn-pb-line xs)))
        (:instance fn-psc-semicolon-prefix-is-proper (xs (fn-pb-line xs)))
        (:instance fn-psc-semicolon-prefix-before-first-lf)
        (:instance fn-psc-strip-success-reconstructs
         (prefix (fn-pb-upto-semicolon (fn-pb-line xs))) (xs (fn-pb-line xs)))
        (:instance fn-psc-line-of-prefix-without-lf
         (prefix (fn-pb-upto-semicolon (fn-pb-line xs)))
         (xs (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs))))
        (:instance fn-psc-line-last-of-prefix-without-lf
         (prefix (fn-pb-upto-semicolon (fn-pb-line xs)))
         (xs (fn-pb-line (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs))))
         (prev nil) (other nil))
        (:instance fn-psc-successful-params-line-is-crlf
         (xs (nthcdr (len (fn-pb-upto-semicolon (fn-pb-line xs))) (fn-pb-line xs))) (prev nil)))
  :in-theory (disable fn-pb-line fn-pb-upto-semicolon fn-inj-strip fn-inj-param-rest
                    nthcdr len binary-append fn-psc-semicolon-prefix-span
                    fn-psc-semicolon-prefix-is-proper fn-psc-strip-success-reconstructs
                    fn-psc-semicolon-absent-is-no-member fn-psc-strip-take-is-drop
                    fn-psc-take-and-fixed-tail-equality fn-psc-successful-params-line-is-crlf
                    fn-psc-semicolon-prefix-before-first-lf
                    fn-psc-line-last-of-prefix-without-lf fn-psc-line-of-prefix-without-lf
                    fn-psc-member-of-append fn-psc-length-of-append)))))

(local (defthm fn-psc-strip-field-from-first-line
 (implies (and (true-listp prefix) (not (member-equal 10 prefix)) (true-listp xs))
  (equal (fn-inj-strip prefix (fn-pb-line xs))
   (if (equal (fn-inj-strip prefix xs) :no) :no
     (fn-pb-line (fn-inj-strip prefix xs)))))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip fn-pb-line member-equal true-listp)))))

(local (defthm fn-psc-strip-preserves-proper-list-or-fails
 (implies (and (true-listp xs) (not (equal (fn-inj-strip prefix xs) :no)))
  (true-listp (fn-inj-strip prefix xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs) :in-theory (enable fn-inj-strip)))))

(local (defthm fn-psc-info-reference-from-content-residual
 (implies (and (true-listp xs)
               (not (equal (fn-inj-strip *fn-inj-injection-info-field* xs) :no)))
  (let* ((r (fn-inj-strip *fn-inj-injection-info-field* xs))
         (line (fn-pb-line r)) (prefix (fn-pb-upto-semicolon line))
         (valid (and (< 2 (len line)) (member-equal 10 line)
                     (equal (fn-psc-model-line-last line nil) 13))))
   (equal (fn-pb-info-line-agent xs)
          (if valid
              (if (equal prefix :no) (fn-inj-take (- (len line) 2) line)
                (if (and (consp prefix)
                         (equal (fn-inj-param-rest (nthcdr (len prefix) line)) nil)) prefix nil)) nil))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-info-agent-plain-normal-form)
        (:instance fn-psc-info-params-agent-normal-form)
        (:instance fn-psc-strip-field-from-first-line (prefix *fn-inj-injection-info-field*))
        (:instance fn-psc-first-line-crlf-tail
         (xs (fn-inj-strip *fn-inj-injection-info-field* xs)) (prev nil))
        (:instance fn-psc-plain-agent-semicolon-criterion
         (line (fn-pb-line (fn-inj-strip *fn-inj-injection-info-field* xs))))
        (:instance fn-psc-parameter-agent-line-is-valid
         (xs (fn-inj-strip *fn-inj-injection-info-field* xs))))
  :in-theory (disable fn-pb-info-line-agent fn-pb-params-line-agent fn-pb-line fn-inj-strip
    fn-inj-take fn-inj-drop fn-inj-param-rest fn-pb-upto-semicolon fn-psc-model-line-last len nthcdr
    fn-psc-info-agent-plain-normal-form fn-psc-info-params-agent-normal-form
    fn-psc-strip-field-from-first-line fn-psc-plain-agent-semicolon-criterion
    fn-psc-parameter-agent-line-is-valid fn-psc-strip-take-is-drop
    fn-psc-take-and-fixed-tail-equality fn-psc-semicolon-absent-is-no-member)))))

(local (defthm fn-psc-strip-success-is-exact-drop
 (implies (and (true-listp prefix) (not (equal (fn-inj-strip prefix xs) :no)))
  (equal (fn-inj-strip prefix xs) (nthcdr (len prefix) xs)))
 :hints (("Goal" :induct (fn-inj-strip prefix xs)
  :in-theory (enable fn-inj-strip nthcdr len true-listp)))))

(local (defthm fn-psc-nthcdr-composes-offsets
 (implies (and (natp a) (natp b))
  (equal (nthcdr b (nthcdr a xs)) (nthcdr (+ a b) xs)))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr)))))

(local (defthm fn-psc-line-take-within-first-line
 (implies (and (natp count) (<= count (len (fn-pb-line xs))))
  (equal (fn-inj-take count (fn-pb-line xs)) (fn-inj-take count xs)))
 :hints (("Goal" :induct (fn-inj-take count xs)
  :in-theory (enable fn-inj-take fn-pb-line len nfix)))))

(local (defthm fn-psc-line-drop-within-first-line
 (implies (and (natp off) (< off (len (fn-pb-line xs))))
  (equal (fn-pb-line (nthcdr off xs)) (fn-inj-drop off (fn-pb-line xs))))
 :hints (("Goal" :induct (nthcdr off xs)
  :in-theory (enable nthcdr fn-pb-line fn-inj-drop len nfix)))))

(local (defthm fn-psc-info-drop-is-nthcdr
 (implies (true-listp xs) (equal (fn-inj-drop off xs) (nthcdr (nfix off) xs)))
 :hints (("Goal" :induct (fn-inj-drop off xs) :in-theory (enable fn-inj-drop nthcdr nfix true-listp)))))

(local (defthm fn-psc-info-parameter-tail-equivalence
 (implies (and (true-listp xs) (natp off) (< off (len (fn-pb-line xs))))
  (equal (equal (fn-inj-param-rest (nthcdr off (fn-pb-line xs))) nil)
         (not (equal (fn-inj-param-rest (nthcdr off xs)) :no))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-line-drop-within-first-line)
        (:instance fn-psc-param-rest-first-line (xs (nthcdr off xs))))
  :in-theory (disable fn-pb-line fn-inj-param-rest nthcdr len
                    fn-psc-line-drop-within-first-line fn-psc-param-rest-first-line)))))

(local (defthm fn-psc-info-reference-from-indices
 (implies (and (true-listp xs) (natp start) (natp a)
               (equal a (+ start 16)) (<= a (len xs))
               (not (equal (fn-inj-strip *fn-inj-injection-info-field* (nthcdr start xs)) :no)))
  (let* ((r (nthcdr a xs)) (line (fn-pb-line r)) (prefix (fn-pb-upto-semicolon line))
         (valid (and (< 2 (len line)) (member-equal 10 line)
                     (equal (fn-psc-model-line-last line nil) 13))))
   (equal (fn-pb-info-line-agent (nthcdr start xs))
          (if valid
              (if (equal prefix :no) (fn-inj-take (- (len line) 2) r)
                (if (and (consp prefix)
                         (not (equal (fn-inj-param-rest (nthcdr (+ a (len prefix)) xs)) :no))) prefix nil)) nil))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-info-reference-from-content-residual (xs (nthcdr start xs)))
        (:instance fn-psc-strip-success-is-exact-drop
         (prefix *fn-inj-injection-info-field*) (xs (nthcdr start xs)))
        (:instance fn-psc-nthcdr-composes-offsets (a start) (b 16))
        (:instance fn-psc-nthcdr-composes-offsets (b (len (fn-pb-upto-semicolon (fn-pb-line (nthcdr a xs))))))
        (:instance fn-psc-line-take-within-first-line
         (xs (nthcdr a xs)) (count (- (len (fn-pb-line (nthcdr a xs))) 2)))
        (:instance fn-psc-semicolon-prefix-span (xs (fn-pb-line (nthcdr a xs))))
        (:instance fn-psc-info-parameter-tail-equivalence
         (xs (nthcdr a xs)) (off (len (fn-pb-upto-semicolon (fn-pb-line (nthcdr a xs)))))))
  :in-theory (disable fn-pb-info-line-agent fn-inj-strip fn-pb-line fn-inj-take fn-inj-drop
    fn-inj-param-rest fn-pb-upto-semicolon fn-psc-model-line-last nthcdr len
    fn-psc-info-reference-from-content-residual fn-psc-strip-success-is-exact-drop
    fn-psc-nthcdr-composes-offsets fn-psc-line-take-within-first-line
    fn-psc-semicolon-prefix-span fn-psc-info-parameter-tail-equivalence
    fn-psc-info-agent-plain-normal-form fn-psc-semicolon-absent-is-no-member)))))

(local (defthm fn-psc-take-positive-first-line-nonempty
 (implies (and (natp k) (< 0 k) (<= k (len (fn-pb-line xs))))
          (consp (fn-inj-take k xs)))
 :hints (("Goal" :in-theory (enable fn-inj-take fn-pb-line)))))

(defthm fn-psc-info-agent-result-is-current-info-agent
 (implies (fn-psc-info-agent-statep c incoming)
  (let* ((a (fn-psc-get pos c)) (line (fn-pb-line (nthcdr a incoming)))
         (prefix (fn-pb-upto-semicolon line))
         (end (+ a (if (equal prefix :no) (- (len line) 2) (len prefix))))
         (agent (fn-pb-info-line-agent (nthcdr (fn-psc-get base c) incoming))))
   (and (equal (fn-psc-result (fn-psc-model-info-agent-complete c incoming))
               (if agent (list :agent a end) :no-source))
        (implies agent (equal (fn-inj-take (- end a) (nthcdr a incoming)) agent)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-info-reference-from-indices
         (xs incoming) (start (fn-psc-get base c)) (a (fn-psc-get pos c)))
        (:instance fn-psc-info-agent-complete-result)
        (:instance fn-psc-semicolon-prefix-span (xs (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))))
        (:instance fn-psc-line-take-within-first-line
         (xs (nthcdr (fn-psc-get pos c) incoming))
         (count (len (fn-pb-upto-semicolon (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))))))
        (:instance fn-psc-take-positive-first-line-nonempty
         (xs (nthcdr (fn-psc-get pos c) incoming))
         (k (- (len (fn-pb-line (nthcdr (fn-psc-get pos c) incoming))) 2))))
  :in-theory (e/d (fn-psc-info-agent-statep)
   (fn-psc-info-reference-from-indices fn-psc-info-agent-complete-result
    fn-psc-model-info-agent-complete fn-psc-semicolon-prefix-span fn-psc-line-take-within-first-line
    fn-pb-info-line-agent fn-psc-info-agent-plain-normal-form fn-psc-info-reference-from-content-residual
    fn-inj-take fn-pb-line fn-pb-upto-semicolon nthcdr len fn-inj-strip
    fn-psc-semicolon-absent-is-no-member)))))

(local (defthm fn-psc-byte-run-addition
 (implies (and (natp a) (natp b))
  (equal (fn-psc-model-byte-run (+ a b) c incoming held)
         (fn-psc-model-byte-run b (fn-psc-model-byte-run a c incoming held) incoming held)))
 :hints (("Goal" :induct (fn-psc-model-byte-run a c incoming held)
          :in-theory (e/d (fn-psc-model-byte-run)
                         (nth nfix len fn-psc-step fn-psc-model-demanded-byte))))))

(defthm fn-psc-info-agent-scan-is-actual-steps
 (implies (fn-psc-info-agent-statep c incoming)
  (equal (fn-psc-model-info-agent-scan c incoming)
         (fn-psc-model-byte-run
          (+ 1 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil))
          c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-psc-line-complete-is-actual-steps
         (c (fn-psc-step c nil)) (held nil))
        (:instance fn-psc-byte-run-addition (a 1)
         (b (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)) (held nil)))
  :expand ((fn-psc-model-byte-run 1 c incoming nil)
           (:free (c) (fn-psc-model-byte-run 0 c incoming nil)))
  :in-theory (e/d (fn-psc-info-agent-statep fn-psc-model-info-agent-scan
                   fn-psc-model-demanded-byte fn-psc-demand)
    (fn-psc-step fn-psc-model-byte-run fn-psc-model-line-complete
     fn-psc-model-line-cost fn-psc-byte-run-addition fn-psc-line-complete-is-actual-steps
     nth len nfix update-nth)))))

(local (defthm fn-psc-params-and-control-is-paid-trace
 (implies (and (equal (fn-psc-get phase c) :params) (fn-psc-line-statep c incoming held))
  (equal (fn-psc-step (fn-psc-model-param-complete c incoming held) nil)
         (fn-psc-model-byte-run (+ 1 (fn-psc-model-param-cost c incoming held)) c incoming held)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-param-complete-returns-control fn-psc-param-complete-is-actual-steps
        (:instance fn-psc-byte-run-addition (a (fn-psc-model-param-cost c incoming held)) (b 1)))
  :expand ((:free (c) (fn-psc-model-byte-run 1 c incoming held))
           (:free (c) (fn-psc-model-byte-run 0 c incoming held)))
  :in-theory (e/d (fn-psc-demand fn-psc-model-demanded-byte)
   (fn-psc-step fn-psc-model-byte-run fn-psc-model-param-complete fn-psc-model-param-cost
    fn-psc-param-complete-returns-control fn-psc-param-complete-is-actual-steps fn-psc-byte-run-addition))))))

(local (defthm fn-psc-info-agent-after-line-frame
 (implies (fn-psc-info-agent-statep c incoming)
  (let ((d (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)))
   (and (member-eq (fn-psc-get phase d) '(:done :params))
        (implies (equal (fn-psc-get phase d) :params) (fn-psc-line-statep d incoming nil)))))
 :hints (("Goal" :do-not-induct t :use (fn-psc-info-agent-scan-frame
  (:instance fn-psc-semicolon-prefix-span (xs (fn-pb-line (nthcdr (fn-psc-get pos c) incoming)))))
  :in-theory (e/d (fn-psc-info-agent-statep fn-psc-line-statep fn-psc-model-source fn-psc-finish nfix)
   (fn-psc-step fn-psc-control fn-psc-model-info-agent-scan fn-psc-info-agent-scan-frame
    fn-pb-line fn-pb-upto-semicolon nth nthcdr len update-nth fn-inj-strip
    fn-psc-semicolon-prefix-span fn-psc-semicolon-absent-is-no-member))))))

(defun fn-psc-model-info-agent-cost (c incoming)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)))
  (+ 2 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)
     (if (equal (fn-psc-get phase d) :params)
         (+ 1 (fn-psc-model-param-cost d incoming nil)) 0))))

(defthm fn-psc-info-agent-complete-is-actual-paid-steps
 (implies (fn-psc-info-agent-statep c incoming)
  (equal (fn-psc-model-info-agent-complete c incoming)
         (fn-psc-model-byte-run (fn-psc-model-info-agent-cost c incoming) c incoming nil)))
 :hints (("Goal" :do-not-induct t
  :use (fn-psc-info-agent-scan-frame fn-psc-info-agent-after-line-frame
        fn-psc-info-agent-scan-is-actual-steps
        (:instance fn-psc-params-and-control-is-paid-trace
         (c (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)) (held nil))
        (:instance fn-psc-byte-run-addition (held nil)
         (a (+ 1 (fn-psc-model-line-cost (fn-psc-step c nil) incoming nil)))
         (b (+ 1 (if (equal (fn-psc-get phase (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil)) :params)
                       (+ 1 (fn-psc-model-param-cost (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil) incoming nil)) 0))))
        (:instance fn-psc-byte-run-addition (held nil) (a 1)
         (c (fn-psc-model-info-agent-scan c incoming))
         (b (+ 1 (fn-psc-model-param-cost (fn-psc-step (fn-psc-model-info-agent-scan c incoming) nil) incoming nil)))))
  :expand ((:free (c) (fn-psc-model-byte-run 0 c incoming nil))
           (:free (c) (fn-psc-model-byte-run 1 c incoming nil)))
  :in-theory (e/d (fn-psc-model-info-agent-complete fn-psc-model-info-agent-cost
                   fn-psc-model-demanded-byte fn-psc-demand)
   (fn-psc-model-info-agent-scan fn-psc-model-line-cost fn-psc-model-param-cost
    fn-psc-model-param-complete fn-psc-step fn-psc-byte-run-addition
    fn-psc-model-byte-run fn-psc-info-agent-scan-is-actual-steps
    fn-psc-info-agent-after-line-frame fn-psc-params-and-control-is-paid-trace
    fn-psc-info-agent-scan-frame fn-psc-info-line-control-unfolds
    nth len nfix update-nth)))))

(defun fn-psc-agent-resultp (r n)
 (declare (xargs :guard t))
 (or (equal r :no-source)
     (and (true-listp r) (equal (len r) 3) (equal (car r) :agent)
          (natp (cadr r)) (natp (caddr r)) (<= (cadr r) (caddr r)) (<= (caddr r) (nfix n)))))
(defthm fn-psc-no-source-is-agent-result-by-definition
 (fn-psc-agent-resultp :no-source n)
 :hints (("Goal" :in-theory (enable fn-psc-agent-resultp))))

(defthm fn-psc-semicolon-prefix-length-bound
 (<= (len (fn-pb-upto-semicolon xs)) (len xs))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-pb-upto-semicolon xs) :in-theory (enable fn-pb-upto-semicolon len))))
(defthm fn-psc-info-agent-result-is-bounded
 (implies (fn-psc-info-agent-statep c incoming)
  (fn-psc-agent-resultp (fn-psc-result (fn-psc-model-info-agent-complete c incoming)) (len incoming)))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (a end) (len (list :agent a end))) (:free (a end) (len (list a end))) (:free (end) (len (list end))))
  :use (fn-psc-info-agent-complete-result fn-psc-info-agent-scan-frame
        (:instance fn-psc-semicolon-prefix-length-bound (xs (fn-pb-line (nthcdr (fn-psc-get pos c) incoming)))))
  :in-theory (e/d (fn-psc-agent-resultp fn-psc-info-agent-statep)
   (fn-psc-info-agent-result-is-current-info-agent fn-pb-info-line-agent fn-pb-params-line-agent fn-psc-info-agent-complete-is-actual-paid-steps fn-psc-result fn-psc-done-result-is-stored fn-psc-model-info-agent-complete fn-psc-info-agent-complete-result
    fn-psc-info-agent-scan-frame fn-psc-model-info-agent-scan fn-psc-model-line-last
    fn-pb-line fn-pb-upto-semicolon fn-inj-param-rest nth len nthcdr)))))

(in-theory (disable fn-psc-info-agent-statep fn-psc-model-info-agent-scan fn-psc-model-info-agent-complete fn-psc-model-info-agent-cost))
