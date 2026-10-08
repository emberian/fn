; What `def-generic' generates (books/def-representation-generic.lisp), proved
; once here.
;
; 1. The payload arena's generic is EQUAL to the hand-written one it
;    replaced: the abstract stobj's recorded interface (foundation,
;    recognizer, creator, and for every export its name, :logic and :exec
;    function, in order) is the list below, captured from dev 9a9fa4bab
;    (books/payload-arena.lisp before the hand forms were deleted).  The
;    attachment `(attach-stobj fn-arena fn-arena-extent)' matches the export
;    lists positionally, so the order is part of the statement.  The :protect
;    set is the ten updaters (seal-list seal-buffer clear seal-range
;    seal-extent reseat-extent release seal-lz-extent reseat-lz-extent
;    forget).

(in-package "ACL2")
(include-book "../../books/payload-arena")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *dgt-hand-fn-arena-interface*
  '(FN-ARENA$L
    (FN-ARENA-P FN-ARENA$AP FN-ARENA$LP)
    (CREATE-FN-ARENA CREATE-FN-ARENA$A CREATE-FN-ARENA$L)
    (FN-ARENA-COUNT FN-ARENA$A-COUNT FN-ARENA$L-COUNT)
    (FN-ARENA-PAYLOAD-LEN FN-ARENA$A-PAYLOAD-LEN FN-ARENA$L-PAYLOAD-LEN)
    (FN-ARENA-GET FN-ARENA$A-GET FN-ARENA$L-GET)
    (FN-ARENA-GET-SPAN FN-ARENA$A-GET-SPAN FN-ARENA$L-GET-SPAN)
    (FN-ARENA-PAYLOAD FN-ARENA$A-PAYLOAD FN-ARENA$L-PAYLOAD)
    (FN-ARENA-SEAL-LIST FN-ARENA$A-SEAL-LIST FN-ARENA$L-SEAL-LIST)
    (FN-ARENA-SEAL-BUFFER FN-ARENA$A-SEAL-BUFFER FN-ARENA$L-SEAL-BUFFER)
    (FN-ARENA-CLEAR FN-ARENA$A-CLEAR FN-ARENA$L-CLEAR)
    (FN-ARENA-SEAL-RANGE FN-ARENA$A-SEAL-RANGE FN-ARENA$L-SEAL-RANGE)
    (FN-ARENA-SEAL-EXTENT FN-ARENA$A-SEAL-EXTENT FN-ARENA$L-SEAL-EXTENT)
    (FN-ARENA-RESEAT-EXTENT FN-ARENA$A-RESEAT-EXTENT FN-ARENA$L-RESEAT-EXTENT)
    (FN-ARENA-RELEASE FN-ARENA$A-RELEASE FN-ARENA$L-RELEASE)
    (FN-ARENA-SEAL-LZ-EXTENT FN-ARENA$A-SEAL-LZ-EXTENT FN-ARENA$L-SEAL-LZ-EXTENT)
    (FN-ARENA-RESEAT-LZ-EXTENT FN-ARENA$A-RESEAT-LZ-EXTENT FN-ARENA$L-RESEAT-LZ-EXTENT)
    (FN-ARENA-FORGET FN-ARENA$A-FORGET FN-ARENA$L-FORGET)))

(assert-event
 (equal (getprop 'fn-arena 'absstobj-info nil 'current-acl2-world (w state))
        *dgt-hand-fn-arena-interface*))

; The tooth of 1: a different export order is a different interface (the
; attachment would match positionally).
(must-fail-checked
 (assert-event
  (equal (getprop 'fn-arena 'absstobj-info nil 'current-acl2-world (w state))
         (list* (car *dgt-hand-fn-arena-interface*)
                (cadr *dgt-hand-fn-arena-interface*)
                (caddr *dgt-hand-fn-arena-interface*)
                (nth 4 *dgt-hand-fn-arena-interface*)
                (nth 3 *dgt-hand-fn-arena-interface*)
                (nthcdr 5 *dgt-hand-fn-arena-interface*))))
 :unchecked "the passing assert above with two exports swapped")

; -----------------------------------------------------------------------------
; 2. A generic over a toy model, declared and executed; the real arena's
;    unattached reference executed.

(defun dgt-ap (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (natp (car x)) (dgt-ap (cdr x)))
    (null x)))

(defun create-dgt-a () (declare (xargs :guard t)) nil)

(defun dgt-a-count (a) (declare (xargs :guard t)) (len a))

(defun dgt-a-push (x a)
  (declare (xargs :guard (and (natp x) (dgt-ap a))))
  (append a (list x)))

(defun dgt-a-at (i a)
  (declare (xargs :guard (and (dgt-ap a) (natp i) (< i (dgt-a-count a)))))
  (nth i a))

(defun dgt-a-clear (a) (declare (xargs :guard t) (ignore a)) nil)

(defthmd dgt-ap-of-push
  (implies (and (dgt-ap a) (natp x)) (dgt-ap (dgt-a-push x a)))
  :hints (("Goal" :in-theory (enable dgt-a-push))))

(defthm dgt-ap-of-create (dgt-ap (create-dgt-a)))

(def-generic dgt-g
  :model (:recognizer dgt-ap :creator create-dgt-a)
  :lemmas (dgt-ap-of-push)
  :exports ((:read dgt-g-count :logic dgt-a-count)
            (:read dgt-g-at :logic dgt-a-at)
            (:update dgt-g-push :logic dgt-a-push)
            (:update dgt-g-clear :logic dgt-a-clear)))

(defun dgt-g-run ()
  (declare (xargs :guard t))
  (with-local-stobj dgt-g
    (mv-let (out dgt-g)
      (let* ((dgt-g (dgt-g-push 7 dgt-g))
             (dgt-g (dgt-g-push 9 dgt-g))
             (before (list (dgt-g-count dgt-g) (dgt-g-at 0 dgt-g) (dgt-g-at 1 dgt-g)))
             (dgt-g (dgt-g-clear dgt-g)))
        (mv (list before (dgt-g-count dgt-g)) dgt-g))
      out)))

(assert! (equal (dgt-g-run) '((2 7 9) 0)))

; The real generic, unattached: its reference foundation answers what the
; logical side answers.
(defun dgt-arena-run ()
  (declare (xargs :guard t))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (let* ((fn-arena (fn-arena-seal-list '(1 2 3) fn-arena))
             (fn-arena (fn-arena-seal-list '(4 5) fn-arena))
             (fn-arena (fn-arena-forget 0 fn-arena)))
        (mv (list (fn-arena-count fn-arena) (fn-arena-payload 0 fn-arena)
                  (fn-arena-payload 1 fn-arena) (fn-arena-get 1 1 fn-arena))
            fn-arena))
      out)))

(assert! (equal (dgt-arena-run) '(2 nil (4 5) 5)))

; -----------------------------------------------------------------------------
; 3. Teeth.  Each declaration below is refused or fails for the one reason
;    named; the witness above is the same shape with that reason removed.

; The model's content is that an update keeps the recognizer: an update
; that does not is refused, by its {preserved} obligation.
(defun dgt-a-bad (x a)
  (declare (xargs :guard (and (natp x) (dgt-ap a))))
  (cons (list x) a))

(must-fail-checked
 (def-generic dgt-g2
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :lemmas (dgt-ap-of-push)
   :exports ((:update dgt-g2-bad :logic dgt-a-bad)))
 :unchecked "dgt-a-bad conses a list into a list of naturals")

(defun dgt-a-two (a) (declare (xargs :guard t)) (mv a a))

(must-fail-checked
 (def-generic dgt-g3
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :exports ((:read dgt-g3-two :logic dgt-a-two)))
 :unchecked "refused at expansion: the logic function returns two values")

(must-fail-checked
 (def-generic dgt-g4
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :exports ((:read dgt-g4-count :logic dgt-a-no-such-function)))
 :unchecked "refused at expansion: the logic function is not in the world")

(must-fail-checked
 (def-generic dgt-g5
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :exports ((:read dgt-other-count :logic dgt-a-count)))
 :unchecked "refused at expansion: the export is not named NAME-SUFFIX")

(must-fail-checked
 (def-generic dgt-g6
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :exports ((:read dgt-g6-count :logic dgt-a-count) (:read dgt-g6-count :logic dgt-a-count)))
 :unchecked "refused at expansion: an export is named twice")

(must-fail-checked
 (def-generic dgt-g7
   :model (:recognizer dgt-ap :creator create-dgt-a)
   :lemmas (dgt-no-such-lemma)
   :exports ((:read dgt-g7-count :logic dgt-a-count)))
 :unchecked "refused at expansion: a lemma is not in the world")

;; Strengthening retains the exact ACL2 guard obligation under a companion
;; name and proves the public correspondence without the unused mark guard.
(defun dgt-a-push-marked (x mark a)
 (declare (ignore mark) (xargs :guard (and (natp x) (natp mark) (dgt-ap a))))
 (dgt-a-push x a))
(def-generic dgt-gs
 :model (:recognizer dgt-ap :creator create-dgt-a)
 :lemmas (dgt-ap-of-push)
 :omit-hypotheses ((dgt-gs-push (natp mark)))
 :exports ((:update dgt-gs-push :logic dgt-a-push-marked)))
(assert-event
 (and (getpropc 'dgt-gs-push{guarded-correspondence} 'theorem nil (w state))
      (getpropc 'dgt-gs-push{correspondence} 'theorem nil (w state))
      (not (member-equal '(natp mark)
            (cdr (cadr (untranslate (getpropc 'dgt-gs-push{correspondence} 'theorem nil (w state)) t (w state))))))))
;; A missing premise is refused, rather than silently ignored.
(must-fail-checked
 (def-generic dgt-gs-bad
  :model (:recognizer dgt-ap :creator create-dgt-a)
  :lemmas (dgt-ap-of-push)
  :omit-hypotheses ((dgt-gs-bad-push (stringp mark)))
  :exports ((:update dgt-gs-bad-push :logic dgt-a-push-marked)))
 :unchecked "stringp mark is not an original correspondence premise")
;; Dropping the payload's naturalness loses model preservation and fails.
(must-fail-checked
 (def-generic dgt-gs-unsound
  :model (:recognizer dgt-ap :creator create-dgt-a)
  :lemmas (dgt-ap-of-push)
  :omit-hypotheses ((dgt-gs-unsound-push (natp x)))
  :exports ((:update dgt-gs-unsound-push :logic dgt-a-push-marked)))
 :unchecked "appending a non-natural does not preserve the model recognizer")
