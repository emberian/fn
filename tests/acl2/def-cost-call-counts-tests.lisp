; def-cost call coordinates over its shared executed-body walker.
(in-package "ACL2")
(include-book "../../books/def-cost")

(defun fn-cctcall-leaf (x) (declare (xargs :guard t)) x)

(defun fn-cctcall-branch (flag x) (declare (xargs :guard t)) (if flag (fn-cctcall-leaf x) x))

(defun fn-cctcall-walk (xs)
 (declare (xargs :guard t))
 (if (consp xs) (cons (fn-cctcall-leaf (car xs)) (fn-cctcall-walk (cdr xs))) nil))

(defun fn-cctcall-nested (x) (declare (xargs :guard t)) (fn-cctcall-leaf (fn-cctcall-leaf x)))

(defun fn-cctcall-mbe (x)
 (declare (xargs :guard t))
 (mbe :logic (fn-cctcall-leaf (fn-cctcall-leaf x)) :exec (fn-cctcall-leaf x)))

(encapsulate (((fn-cctcall-opaque *) => *))
 (local (defun fn-cctcall-opaque (x) (declare (ignore x)) nil)))

(defun fn-cctcall-opaque-user (x) (declare (xargs :guard t)) (fn-cctcall-opaque x))

(def-cost fn-cctcall-branch :calls ((leaf-calls (fn-cctcall-leaf))))

(def-cost fn-cctcall-walk :calls ((leaf-calls (fn-cctcall-leaf))))

(def-cost fn-cctcall-nested :calls ((leaf-calls (fn-cctcall-leaf))))

(def-cost fn-cctcall-mbe :calls ((leaf-calls (fn-cctcall-leaf))))

(def-cost fn-cctcall-opaque-user :unaccounted (fn-cctcall-opaque)
 :calls ((leaf-calls (fn-cctcall-leaf) :unaccounted (fn-cctcall-opaque))))

(defthm fn-cctcall-branch-is-controlled
 (equal (fn-cctcall-branch-leaf-calls flag x) (if flag 1 0))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-cctcall-branch-leaf-calls)))))

(defthm fn-cctcall-walk-count-is-length
 (equal (fn-cctcall-walk-leaf-calls xs) (len xs))
 :hints (("Goal" :induct (fn-cctcall-walk-leaf-calls xs)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cctcall-walk-leaf-calls len)))))

(assert-event (equal (fn-cctcall-nested-leaf-calls 7) 2))

(assert-event (equal (fn-cctcall-mbe-leaf-calls 7) 1))

(defthm fn-cctcall-opaque-count-is-natural
 (natp (fn-cctcall-opaque-user-leaf-calls x))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cctcall-opaque-user-leaf-calls fn-cost-unaccounted-natp)))))

(make-event
 (let ((row (cdr (assoc-equal '(fn-cctcall-opaque-user leaf-calls)
                             (table-alist 'fn-cost-call-counts (w state))))))
  (if (and (equal (fn-cost-get :unaccounted row) '(fn-cctcall-opaque))
           (not (equal (fn-cost-get :body-cost row) ''0)))
   (value '(value-triple :opaque-cost-not-silently-zero))
   (er soft 'lb6 "Opaque call was silently zeroed: ~x0" row))))

(def-cost-check fn-cctcall-branch)

(def-cost-check fn-cctcall-walk)

(def-cost-check fn-cctcall-nested)

(def-cost-check fn-cctcall-mbe)

(def-cost-check fn-cctcall-opaque-user)

(local (encapsulate ()
 (make-event
  (value `(table fn-cost-call-counts '(fn-cctcall-branch leaf-calls)
    '(:targets (fn-cctcall-leaf) :twin fn-cctcall-branch-leaf-calls :body-cost '0
      :unaccounted nil :formals (flag x)
      :source-body ,(getpropc 'fn-cctcall-branch 'unnormalized-body nil (w state))))))
 (make-event
  (if (fn-cost-call-check-rows 'fn-cctcall-branch (table-alist 'fn-cost-call-counts (w state)) (w state))
   (value '(value-triple :stale-count-rejected))
   (er soft 'lb6 "Stale count unexpectedly accepted")))))

(defun fn-cctcall-pair (x) (declare (xargs :guard t)) (cons x nil))

(def-cost fn-cctcall-pair :conses 1
 :calls ((leaf-calls (fn-cctcall-leaf)) (cons-calls (cons))))

(assert-event (equal (fn-cctcall-pair-leaf-calls 7) 0))

(assert-event (equal (fn-cctcall-pair-cons-calls 7) 1))

(assert-event (equal (fn-cctcall-pair-conses 7) 1))

(def-cost-check fn-cctcall-pair)

(defun fn-cctcall-misuse (x) (declare (xargs :guard t)) (fn-cctcall-leaf x))

(make-event
 (mv-let (bad events)
  (fn-cost-call-events 'fn-cctcall-misuse
    '((duplicate-candidate (fn-cctcall-leaf)) (duplicate-candidate (fn-cctcall-leaf))) (w state))
  (declare (ignore events))
  (if bad (value '(value-triple :duplicate-tags-refused))
   (er soft 'lb6 "Duplicate tags accepted"))))

(make-event
 (mv-let (bad events)
  (fn-cost-call-events 'fn-cctcall-misuse
    '((unknown-key-candidate (fn-cctcall-leaf) :imaginary-bound 0)) (w state))
  (declare (ignore events))
  (if bad (value '(value-triple :unknown-key-refused))
   (er soft 'lb6 "Unknown count option accepted"))))

(make-event
 (mv-let (bad events)
  (fn-cost-call-events 'fn-cctcall-misuse '((empty-candidate nil)) (w state))
  (declare (ignore events))
  (if bad (value '(value-triple :empty-targets-refused))
   (er soft 'lb6 "Empty targets accepted"))))

; Concrete field accesses and a marked callee compose without a model stobj escape.
(defstobj fn-cctcall-store (fn-cctcall-word :type integer :initially 0))
(defun fn-cctcall-read-mark (fn-cctcall-store)
 (declare (xargs :stobjs fn-cctcall-store :guard t))
 (fn-cctcall-leaf (fn-cctcall-word fn-cctcall-store)))
(def-cost fn-cctcall-read-mark
 :calls ((leaf-calls (fn-cctcall-leaf)) (word-reads (fn-cctcall-word))))
(defthm fn-cctcall-read-mark-one-leaf
 (equal (fn-cctcall-read-mark-leaf-calls fn-cctcall-store-v) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
   '(fn-cctcall-read-mark-leaf-calls)))))
(defthm fn-cctcall-read-mark-one-word
 (equal (fn-cctcall-read-mark-word-reads fn-cctcall-store-v) 1)
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
   '(fn-cctcall-read-mark-word-reads)))))
(def-cost-check fn-cctcall-read-mark)


; Separately accounted boundaries exclude their bodies, never their argument evaluation.
(defun fn-cctcall-entry-boundary (x) (declare (xargs :guard t)) (fn-cctcall-leaf x))
(defun fn-cctcall-with-entry (x) (declare (xargs :guard t))
 (fn-cctcall-entry-boundary (fn-cctcall-leaf x)))
(def-cost fn-cctcall-with-entry
 :calls ((section-calls (fn-cctcall-leaf) :stop-at (fn-cctcall-entry-boundary))
         (entry-calls (fn-cctcall-entry-boundary))))
(assert-event (equal (fn-cctcall-with-entry-section-calls 9) 1))
(assert-event (equal (fn-cctcall-with-entry-entry-calls 9) 1))
(def-cost-check fn-cctcall-with-entry)
(make-event
 (mv-let (bad events)
  (fn-cost-call-events 'fn-cctcall-misuse
    '((overlap-candidate (fn-cctcall-leaf) :stop-at (fn-cctcall-leaf))) (w state))
  (declare (ignore events))
  (if bad (value '(value-triple :target-boundary-overlap-refused))
   (er soft 'cost-tests "A marked target was also accepted as a stopped boundary"))))

; Weighted coordinates are derived from the selected actual call argument.
(defun fn-cctcall-send (offset bytes) (declare (xargs :guard t)) (cons offset bytes))
(defun fn-cctcall-sends (flag offset bytes) (declare (xargs :guard t))
 (if flag (fn-cctcall-send offset bytes) nil))
(def-cost fn-cctcall-sends
 :calls ((sent-bytes (fn-cctcall-send) :argument 1)
         (sent-offsets (fn-cctcall-send) :argument 0)))
(assert-event (equal (fn-cctcall-sends-sent-bytes t 19 23) 23))
(assert-event (equal (fn-cctcall-sends-sent-offsets t 19 23) 19))
(assert-event (equal (fn-cctcall-sends-sent-bytes nil 19 23) 0))
(assert-event (equal (fn-cctcall-sends-sent-bytes t 19 -1) 0))
(def-cost-check fn-cctcall-sends)
(make-event (mv-let (bad events)
 (fn-cost-call-events 'fn-cctcall-misuse
   '((out-of-arity (fn-cctcall-send) :argument 2)) (w state))
 (declare (ignore events))
 (if bad (value '(value-triple :out-of-arity-refused))
  (er soft 'cost-tests "Argument outside target arity accepted"))))
(make-event (mv-let (bad events)
 (fn-cost-call-events 'fn-cctcall-misuse
   '((bad-argument-index (fn-cctcall-send) :argument -1)) (w state))
 (declare (ignore events))
 (if bad (value '(value-triple :bad-argument-index-refused))
  (er soft 'cost-tests "Negative argument index accepted"))))

; A zero coordinate of a recursive worker is non-recursive and needs no measure.
(defun fn-cctcall-zero-walk (xs)
 (declare (xargs :guard t))
 (if (consp xs) (fn-cctcall-zero-walk (cdr xs)) nil))
(def-cost fn-cctcall-zero-walk :calls ((zero-leaf-calls (fn-cctcall-leaf))))
(assert-event (equal (fn-cctcall-zero-walk-zero-leaf-calls '(a b c)) 0))
(def-cost-check fn-cctcall-zero-walk)

; The logic arm may recur while the executed arm and its cost do not.
(defun fn-cctcall-mbe-zero-walk (xs)
 (declare (xargs :guard t :verify-guards nil))
 (mbe :logic (if (consp xs) (fn-cctcall-mbe-zero-walk (cdr xs)) nil)
      :exec nil))
(def-cost fn-cctcall-mbe-zero-walk :calls ((mbe-zero-leaf-calls (fn-cctcall-leaf))))
(assert-event (equal (fn-cctcall-mbe-zero-walk-visits '(a b c)) 0))
(assert-event (equal (fn-cctcall-mbe-zero-walk-mbe-zero-leaf-calls '(a b c)) 0))
(def-cost-check fn-cctcall-mbe-zero-walk)

; The intrinsic intern operation cannot invoke a marked logical callee.
; Its ordinary visit cost remains explicitly unaccounted.
(defun fn-cctcall-intern-user (name)
 (declare (xargs :guard (stringp name)))
 (intern-in-package-of-symbol name 'acl2::fn-cost-intrinsic-control))
(def-cost fn-cctcall-intern-user :unaccounted (intern-in-package-of-symbol)
 :calls ((intrinsic-leaf-calls (fn-cctcall-leaf))))
(assert-event (equal (fn-cctcall-intern-user-intrinsic-leaf-calls "FN-COST-INTRINSIC-CONTROL") 0))
(assert-event (symbolp (fn-cctcall-intern-user "FN-COST-INTRINSIC-CONTROL")))
(def-cost-check fn-cctcall-intern-user)
