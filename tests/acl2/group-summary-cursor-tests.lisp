; Literal residual/progress/shape teeth and actual sparse metadata summary.
(in-package "ACL2")
(include-book "../../books/group-summary-cursor")
(include-book "catalog-available-readers-tests")

(defun gsct-walk (cur n fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (if (zp n) cur (gsct-walk (fn-gsc-one cur fn-cat) (- n 1) fn-cat)))

(defun gsct-run (survivors fn-cat)
  (declare (xargs :mode :program :stobjs fn-cat))
  (let* ((fn-cat (fn-cat-clear fn-cat))
         (fn-cat (cav-reader-fill 0 34 survivors fn-cat))
         (cur (fn-gsc-start "fn.available" 34 35 34))
         (one (fn-gsc-one cur fn-cat))
         (after8 (gsct-walk cur 8 fn-cat))
         (done (gsct-walk after8 26 fn-cat))
         (archive (fn-make-state '("fn.available") '(("fn.available" . 35)) nil 0 nil nil)))
    (mv (and (fn-gsc-statep cur) (fn-gsc-statep one) (fn-gsc-statep after8)
             (equal (fn-gsc-remaining one) 33)
             (equal (fn-gsc-remaining after8) 26)
             (equal (fn-gsc-remaining done) 0)
             (equal (fn-gsc-one done fn-cat) done)
             (equal (fn-gsc-summary done)
                    (fn-scat-available-summary archive "fn.available" 34 fn-cat))
             (equal (len one) 9)) fn-cat)))

(defun gsct-local (survivors)
  (declare (xargs :mode :program))
  (with-local-stobj fn-cat
    (mv-let (answer fn-cat) (gsct-run survivors fn-cat) answer)))

(assert-event (gsct-local '(1 34)))
(assert-event (gsct-local nil))
(assert-event (gsct-local '(1)))
(assert-event (gsct-local '(33 34)))

; Progress premise removal: a settled state remains settled, rather than -1.
(defun gsct-progress-premise-removal ()
 (declare (xargs :mode :program))
 (with-local-stobj fn-cat
   (mv-let (answer fn-cat)
     (let ((cur (fn-gsc-start "fn.available" 0 1 0)))
       (mv (and (not (posp (fn-gsc-remaining cur)))
                (not (equal (fn-gsc-remaining (fn-gsc-one cur fn-cat))
                            (- (fn-gsc-remaining cur) 1)))) fn-cat)) answer)))

; Shape premise removal; label corrupted state, not an operator capture.
(defun gsct-shape-premise-removal ()
 (declare (xargs :mode :program))
 (with-local-stobj fn-cat
   (mv-let (answer fn-cat)
     (let ((cur '(:group-summary "fn.available" 0 1 0 1)))
       (mv (and (not (fn-gsc-statep cur))
                (not (equal (len (fn-gsc-one cur fn-cat)) 9))) fn-cat)) answer)))

; Literal residual witness: the theorem has no retained antecedent.
(defthm gsct-literal-one-residual
  (equal (fn-gsc-reference
          (fn-gsc-one (fn-gsc-start "fn.available" 34 35 34) fn-cat) fn-cat)
         (fn-gsc-reference (fn-gsc-start "fn.available" 34 35 34) fn-cat))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-gsc-one-preserves-reference
                                  (cur (fn-gsc-start "fn.available" 34 35 34)))))))

(defthm gsct-literal-settled-reference
  (let ((cur '(:group-summary "fn.available" 34 35 34 35 2 1 34)))
    (and (zp (fn-gsc-remaining cur))
         (equal (fn-gsc-reference cur fn-cat) (fn-gsc-summary cur))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-gsc-terminal-reference
                           (cur '(:group-summary "fn.available" 34 35 34 35 2 1 34))))
            :in-theory (enable fn-gsc-remaining fn-gsc-at fn-cur-at))))

(assert-event (gsct-progress-premise-removal))
(assert-event (gsct-shape-premise-removal))
