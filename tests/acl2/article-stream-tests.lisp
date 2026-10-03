; Actual guard-verified selector: valid inputs and reference outcomes.
(in-package "ACL2")
(include-book "../../books/article-stream")

(defconst *astq-one*
  (fn-make-article "<one@query.example>" 0 '("fn.a" "fn.other")
                   '(("fn.a" . 1) ("fn.other" . 3)) t 0))
(defconst *astq-two*
  (fn-make-article "<two@query.example>" 1 '("fn.a" "fn.other")
                   '(("fn.a" . 2) ("fn.other" . 7)) t 0))
(defconst *astq-articles* (list *astq-one* *astq-two*))

(assert-event
 (let* ((root (fn-make-state '("fn.a" "fn.other") '(("fn.a" . 3) ("fn.other" . 8))
                            *astq-articles* 0 nil nil))
        (it (fn-ast-select-state :number "fn.a" 2 *astq-articles* nil nil nil 0 :next))
        (done (fn-ast-select-step it 512)))
   (and (fn-statep root)
        (fn-ast-select-donep done)
        (equal (fn-ast-at 9 done) :selected)
        (equal (fn-ast-at 5 done) *astq-two*)
        (equal (fn-ast-at 5 done) (fn-nntp-find-group-number "fn.a" 2 *astq-articles*))
        (equal (fn-ast-select-step (fn-ast-select-step it 1) 511) done))))

(assert-event
 (let* ((it (fn-ast-select-state :current "fn.a" 2 *astq-articles* nil nil nil 0 :next))
        (done (fn-ast-select-step it 512)))
   (and (fn-ast-select-donep done)
        (equal (fn-ast-at 9 done) :selected)
        (equal (fn-ast-at 5 done) (fn-nntp-available-article "fn.a" 2 *astq-articles*)))))

(assert-event
 (let ((done (fn-ast-select-step
              (fn-ast-select-state :number "fn.a" 3 *astq-articles* nil nil nil 0 :next) 512)))
   (and (equal (fn-ast-at 9 done) :missing)
        (not (fn-nntp-find-group-number "fn.a" 3 *astq-articles*)))))

; Corrupted-state witness: malformed comparison row/phase is total under the
; executable guard, without scanning or revalidating the retained archive.
(assert-event
 (let ((done (fn-ast-select-step
              (fn-ast-select-state :number "fn.a" 1 nil nil 77 '(9 . 1) 0 :compare) 2)))
   (and (equal (fn-ast-at 9 done) :missing)
        (equal (fn-ast-at 5 done) nil))))

; Reachable Message-ID archive selection retains the first ID match, settles
; its available local number, and permits no group to report zero.
(assert-event
 (let ((start (fn-ast-select-state :msgid "fn.a" "<two@query.example>"
                                  *astq-articles* nil nil nil 0 :msgid-next)))
   (let ((done (fn-ast-select-step start 512)))
     (and (eq (fn-ast-at 9 done) :selected)
          (equal (fn-ast-at 5 done) (fn-find-article "<two@query.example>" *astq-articles*))
          (equal (fn-ast-at 3 done) (fn-nntp-article-number "fn.a" *astq-two*))
          (equal (fn-ast-at 3 (fn-ast-select-step (fn-ast-msgid-local-start nil *astq-two*) 512)) 0)))))

; Literal unconditional fuel-composition witness; changing the second budget
; actually changes this unfinished retained cursor.
(assert-event
 (let ((start (fn-ast-select-state :msgid "fn.a" "<two@query.example>"
                                  *astq-articles* nil nil nil 0 :msgid-next)))
   (and (equal (fn-ast-select-step (fn-ast-select-step start 1) 2)
               (fn-ast-select-step start (+ (nfix 1) (nfix 2))))
        (not (equal (fn-ast-select-step (fn-ast-select-step start 1) 2)
                    (fn-ast-select-step start 4))))))
