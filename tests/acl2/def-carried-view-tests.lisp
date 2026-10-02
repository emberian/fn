; Teeth for books/def-carried-view.lisp: the generator on two fixture views,
; one of each kind, and a reader over the :set one.
;
;   1. A :set view with two indexes (as the withdrawal index has): the
;      generated carry, its refresh on the same list (the outer cell rebased),
;      on a prepended delta (the walk found the carried tail) and on an
;      unrelated list (rebuilt); the keystones evaluated at those carries.
;   2. An :exact view with one index (as NEWNEWS's suffix maxima): the fold
;      is oldest-first, nil carries, the delta refresh is the rebuild's value.
;   3. A reader over the :set view: the fast arm on a fresh negative probe,
;      the reference on a positive probe and on a stale carry, the keystone.
;   4. Refusals, each by name.

(in-package "ACL2")
(include-book "../../books/def-carried-view")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. A :set view: records (TARGET . CAUSE), two string sets kept as lists.

(defun cvt-target (e) (declare (xargs :guard t)) (if (consp e) (car e) nil))
(defun cvt-cause (e) (declare (xargs :guard t)) (if (consp e) (cdr e) nil))
(defun cvt-key (x) (declare (xargs :guard t)) (if (stringp x) x nil))
(defun cvt-has (k set)
  (declare (xargs :guard t))
  (if (consp set) (or (equal k (car set)) (cvt-has k (cdr set))) nil))
(defun cvt-add (x set) (declare (xargs :guard t)) (if (stringp x) (cons x set) set))

(defthm cvt-has-of-add
  (implies (cvt-has k set) (cvt-has k (cvt-add x set))))

(defthm cvt-add-has-it
  (implies (stringp x) (cvt-has x (cvt-add x set))))

(def-carried-view cvt
  :key ws
  :indexes ((tset :kind :set
                  :key-fn (lambda (e) (cvt-key (cvt-target e)))
                  :put (lambda (e idx) (cvt-add (cvt-target e) idx))
                  :hasp (lambda (k idx) (cvt-has k idx))
                  :empty nil
                  :lemmas (cvt-has-of-add cvt-add-has-it))
            (cset :kind :set
                  :key-fn (lambda (e) (cvt-key (cvt-cause e)))
                  :put (lambda (e idx) (cvt-add (cvt-cause e) idx))
                  :hasp (lambda (k idx) (cvt-has k idx))
                  :empty nil
                  :lemmas (cvt-has-of-add cvt-add-has-it))))

(defconst *cvt-ws0* '(("t1" . "c1") ("t2" . "c1") ("t3" . "c2")))
(defconst *cvt-ws1* (cons '("t4" . "c3") *cvt-ws0*))
(defconst *cvt-c0* (cvt-refresh nil *cvt-ws0*))
(defconst *cvt-c1* (cvt-refresh *cvt-c0* *cvt-ws1*))

(assert-event (cvt-carryp nil))
(assert-event (and (cvt-carryp *cvt-c0*) (equal (cvt-ws *cvt-c0*) *cvt-ws0*)))
(assert-event (equal (cvt-tset *cvt-c0*) '("t1" "t2" "t3")))
(assert-event (equal (cvt-cset *cvt-c0*) '("c1" "c1" "c2")))
; the delta walk: one element consumed, the carried indexes extended
(assert-event (equal (fn-cv-walk-steps *cvt-ws1* *cvt-ws0*) 1))
(assert-event (and (cvt-carryp *cvt-c1*) (equal (cvt-tset *cvt-c1*) '("t4" "t1" "t2" "t3"))))
; the same list: the carry's cell is rebased, the indexes kept
(assert-event (equal (cvt-refresh *cvt-c1* *cvt-ws1*) *cvt-c1*))
; an unrelated list: rebuilt
(defconst *cvt-ws2* '(("t9" . "c9")))
(assert-event (equal (cvt-refresh *cvt-c1* *cvt-ws2*) (cons *cvt-ws2* (cvt-build *cvt-ws2*))))
; an element with no string target has no key and the index is still complete
(assert-event (cvt-carryp (cvt-refresh nil (cons '(7 . "c7") *cvt-ws0*))))

(defteeth cvt-carryp-of-refresh
  :claim (((carried (cvt-carryp carry))) (cvt-carryp (cvt-refresh carry ws)))
  :subject cvt-refresh
  :witness ((carry *cvt-c0*) (ws *cvt-ws1*))
  :breaks ((carried ((carry (cons *cvt-ws0* '(nil nil))))))
  :mutations ((old-index (:conclusion (cvt-carryp (cons ws (cdr carry))))
                         ((carry *cvt-c0*) (ws *cvt-ws1*))
                         :fault "a refresh that installs the new list over the old indexes")))

(defteeth-check)

; ---------------------------------------------------------------------------
; 2. An :exact view: the suffix maxima of a list of naturals.

(defun cvx-top (idx) (declare (xargs :guard t)) (if (consp idx) (nfix (car idx)) 0))

(def-carried-view cvx
  :key arts
  :indexes ((maxes :kind :exact
                   :put (lambda (e idx) (cons (max (nfix e) (cvx-top idx)) idx))
                   :empty nil)))

(assert-event (cvx-carryp nil))
(assert-event (equal (cvx-build '(3 9 2)) '(9 9 2)))
(defconst *cvx-c* (cvx-refresh nil '(3 9 2)))
(assert-event (and (cvx-carryp *cvx-c*) (equal (cvx-maxes *cvx-c*) '(9 9 2))))
; the delta refresh folds the prefix oldest-first onto the carried maxima
(assert-event (equal (cvx-refresh *cvx-c* '(1 20 3 9 2)) (cons '(1 20 3 9 2) '(20 20 9 9 2))))
(assert-event (equal (cvx-maxes (cvx-refresh *cvx-c* '(1 20 3 9 2))) (cvx-build '(1 20 3 9 2))))
(assert-event (not (cvx-carryp (cons '(3 9 2) '(9 9 3)))))

(defteeth cvx-carryp-of-refresh
  :claim (((carried (cvx-carryp carry))) (cvx-carryp (cvx-refresh carry arts)))
  :subject cvx-refresh
  :witness ((carry *cvx-c*) (arts '(1 20 3 9 2)))
  :breaks ((carried ((carry (cons '(3 9 2) '(9 9 3))))))
  :mutations ((old-index (:conclusion (cvx-carryp (cons arts (cdr carry))))
                         ((carry *cvx-c*) (arts '(1 20 3 9 2)))
                         :fault "a refresh that installs the new list over the old maxima")))

; ---------------------------------------------------------------------------
; 3. A reader over the :set view: "is X a target?", the reference a walk.

(defun cvt-targetedp (x ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (or (equal x (cvt-target (car ws))) (cvt-targetedp x (cdr ws)))
    nil))

(defthm cvt-absent-target-is-untargeted
  (implies (and (cvt-tset-okp ws idxs) (stringp x) (not (cvt-has x (cvt-tset-of idxs))))
           (equal (cvt-targetedp x ws) nil))
  :hints (("Goal" :in-theory (enable cvt-tset-okp cvt-tset-of))))

(def-carried-reader cvt-targetedp-fast (x ws carry)
  :of cvt :carry carry :list ws
  :when (stringp x)
  :probe (tset x)
  :fast nil
  :reference (cvt-targetedp x ws)
  :by cvt-absent-target-is-untargeted)

; fresh negative: the fast arm; positive: the walk; stale carry: the walk
(assert-event (equal (cvt-targetedp-fast "n" *cvt-ws0* *cvt-c0*) nil))
(assert-event (equal (cvt-targetedp-fast "t2" *cvt-ws0* *cvt-c0*) t))
(assert-event (equal (cvt-targetedp-fast "t4" *cvt-ws1* *cvt-c0*) t))
(assert-event (equal (cvt-targetedp-fast "n" *cvt-ws0* *cvt-c0*) (cvt-targetedp "n" *cvt-ws0*)))

(defteeth cvt-targetedp-fast-is-cvt-targetedp
  :claim (((carried (cvt-carryp carry))) (equal (cvt-targetedp-fast x ws carry) (cvt-targetedp x ws)))
  :subject cvt-targetedp-fast
  :witness ((x "n") (ws *cvt-ws0*) (carry *cvt-c0*))
  :breaks ((carried ((x "t1") (carry (cons *cvt-ws0* '(nil nil))))))
  ; a complete carry whose target set holds an extra key: the probe is a
  ; false positive, the walk answers, a reader trusting the probe would not
  :mutations ((positive-trusted (:conclusion (equal (cvt-targetedp-fast x ws carry)
                                                    (cvt-has x (cvt-tset carry))))
                                ((x "n") (ws *cvt-ws0*)
                                 (carry (list *cvt-ws0* '("n" "t1" "t2" "t3") '("c1" "c2"))))
                                :fault "a reader that trusts a positive probe")))

(defteeth-check)

; ---------------------------------------------------------------------------
; 4. Refusals.

(assert-event (equal (fn-cv-refusal 'v '(:indexes ((i :kind :set)))) '(:no-key v)))
(assert-event (equal (fn-cv-refusal 'v '(:key ws)) '(:no-indexes v)))
(assert-event (equal (fn-cv-refusal 'v '(:key ws :indexes ((i :kind :fuzzy :put (lambda (e idx) idx) :empty nil))))
                     '(:bad-kind i :fuzzy)))
(assert-event (equal (fn-cv-refusal 'v '(:key ws :indexes ((i :kind :set :put (lambda (e idx) idx) :empty nil
                                                               :hasp (lambda (k idx) t)))))
                     '(:bad-key-fn i)))
(assert-event (equal (fn-cv-refusal 'v '(:key ws :indexes ((i :kind :exact :put (lambda (e idx) idx) :empty nil
                                                               :hasp (lambda (k idx) t)))))
                     '(:exact-has-no-probe i)))
(assert-event (equal (fn-cv-refusal 'v '(:key ws :indexes ((i :kind :exact :put (lambda (e idx) idx) :empty nil)
                                                            (j :kind :set :put (lambda (e idx) idx) :empty nil
                                                               :key-fn (lambda (e) e) :hasp (lambda (k idx) t)))))
                     '(:mixed-kinds v)))
(assert-event (equal (fn-cv-world-problem 'cvt '(:key ws :indexes ((i :kind :exact :put (lambda (e idx) idx) :empty nil)))
                                          (w state))
                     '(:declared-twice cvt)))
(assert-event (equal (fn-cv-reader-refusal 'r '(x ws carry) '(:of cvt :carry carry :list ws :probe (tset x) :fast nil
                                                             :reference (cvt-targetedp x ws)))
                     '(:no-by r)))
(assert-event (equal (fn-cv-reader-world-problem 'r '(:of cvx :carry carry :list ws :probe (maxes x) :fast nil
                                                      :reference (cvt-targetedp x ws) :by car-cons)
                                                 (w state))
                     '(:not-a-set-view r cvx)))
(must-fail-checked
 (def-carried-view cvt :key ws :indexes ((i :kind :exact :put (lambda (e idx) idx) :empty nil)))
 :unchecked "refused by name at expansion (:declared-twice), before any event")
