; Witnesses and teeth for books/store-replay-bound (the recovery input bound,
; PKT-686's addition): the small preset's figures, the defect's witness (a
; store the budget admitted, over H in encoded octets, now within the bound),
; the keystone's reachable witness and per hypothesis a counterexample and a
; must-fail of the keystone without it.
(in-package "ACL2")
(include-book "../../books/store-replay-bound")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

; The small preset (books/heap-figure.lisp *fn-heap-small-request*, the same
; fields; heap-figure is not included: its closure was most of this book's
; certification time, 11.4 s at 2 jobs; lane reservation-figure).
(defconst *srt-small*
  (fn-bs-profile-resolve
   '(:development ((1 . 16384) (2 . 8388608) (3 . 196608) (5 . 16) (7 . 128))) nil))
(defconst *srt-h* 8388608)
(defconst *srt-o* (fn-srb-record-overhead *srt-small*))

; The small preset: T 16,384, H 8 MiB, G 16; per-record overhead 1,083 +
; 16 x 261 = 5,259; the bound 8,388,608 + 16,384 x 5,259.
(assert! (equal *srt-o* 5259))
(assert! (equal (fn-srb-replay-input-bound *srt-small*) (+ 8388608 (* 16384 5259))))
; The defect: 3,500 records of 2,048 payload octets and about 500 of fields
; (9,000,000 encoded octets, 7,168,000 in the budget) were refused by H and
; are within the bound.
(assert! (not (fn-profile-replay-within-boundp *srt-small* 9000000)))
(assert! (fn-srb-replay-within-boundp *srt-small* 9000000))
(assert! (<= (* 3500 2048) *srt-h*))
; Past the bound: refused.
(assert! (not (fn-srb-replay-within-boundp *srt-small*
                                           (+ 1 (fn-srb-replay-input-bound *srt-small*)))))
(assert! (not (fn-srb-replay-within-boundp nil 0)))

(defun srt-hyps (profile encoded stored)
  (declare (xargs :mode :program))
  (list (fn-bs-profile-admittedp profile)
        (<= (len encoded) (fn-bs-profile-max-transactions profile))
        (<= (fn-srb-sum stored) (fn-bs-profile-max-history-octets profile))
        (fn-srb-pointwise-within encoded stored (fn-srb-record-overhead profile))))

(defun srt-conclusion (profile encoded)
  (declare (xargs :mode :program))
  (fn-srb-replay-within-boundp profile (fn-srb-sum encoded)))

(defmacro srt-must-fail (name &rest hyps)
  `(must-fail-checked
    (defthm ,name
      (implies (and ,@hyps)
               (fn-srb-replay-within-boundp profile (fn-srb-sum encoded)))
      :hints (("Goal" :do-not-induct t
               :in-theory (disable fn-srb-record-overhead fn-bs-profile-admittedp))))))

; The witness: two articles of 2,048 payload octets encoded at 2,600.
(assert! (equal (srt-hyps *srt-small* '(2600 2600) '(2048 2048)) '(t t t t)))
(assert! (srt-conclusion *srt-small* '(2600 2600)))
; Every record at the full overhead and the budget full: exactly the bound.
(assert! (equal (fn-srb-sum (cons (+ *srt-h* *srt-o*) (make-list 16383 :initial-element *srt-o*)))
                (fn-srb-replay-input-bound *srt-small*)))

; Without the admitted profile: no profile admits nothing.
(assert! (equal (srt-hyps nil nil nil) '(nil t t t)))
(assert! (not (srt-conclusion nil nil)))
(srt-must-fail srt-without-admitted
               (<= (len encoded) (fn-bs-profile-max-transactions profile))
               (<= (fn-srb-sum stored) (fn-bs-profile-max-history-octets profile))
               (fn-srb-pointwise-within encoded stored (fn-srb-record-overhead profile)))

; Without at most T records: T + 1 records at the full overhead.
(defconst *srt-long-stored* (cons *srt-h* (make-list 16384 :initial-element 0)))
(defconst *srt-long-encoded* (cons (+ *srt-h* *srt-o*) (make-list 16384 :initial-element *srt-o*)))
(assert! (equal (srt-hyps *srt-small* *srt-long-encoded* *srt-long-stored*) '(t nil t t)))
(assert! (not (srt-conclusion *srt-small* *srt-long-encoded*)))
(srt-must-fail srt-without-count
               (fn-bs-profile-admittedp profile)
               (<= (fn-srb-sum stored) (fn-bs-profile-max-history-octets profile))
               (fn-srb-pointwise-within encoded stored (fn-srb-record-overhead profile)))

; Without the stored octets within H: twice H in one record.
(defconst *srt-over-stored* (cons (* 2 *srt-h*) (make-list 16383 :initial-element 0)))
(defconst *srt-over-encoded* (cons (+ (* 2 *srt-h*) *srt-o*) (make-list 16383 :initial-element *srt-o*)))
(assert! (equal (srt-hyps *srt-small* *srt-over-encoded* *srt-over-stored*) '(t t nil t)))
(assert! (not (srt-conclusion *srt-small* *srt-over-encoded*)))
(srt-must-fail srt-without-history
               (fn-bs-profile-admittedp profile)
               (<= (len encoded) (fn-bs-profile-max-transactions profile))
               (fn-srb-pointwise-within encoded stored (fn-srb-record-overhead profile)))

; Without each encoding within its stored octets plus the overhead: one
; record of nothing stored encoded past the bound.
(defconst *srt-big* (list (+ 1 (fn-srb-replay-input-bound *srt-small*))))
(assert! (equal (srt-hyps *srt-small* *srt-big* '(0)) '(t t t nil)))
(assert! (not (srt-conclusion *srt-small* *srt-big*)))
(srt-must-fail srt-without-pointwise
               (fn-bs-profile-admittedp profile)
               (<= (len encoded) (fn-bs-profile-max-transactions profile))
               (<= (fn-srb-sum stored) (fn-bs-profile-max-history-octets profile)))

; -----------------------------------------------------------------------------
; Lane keystone-audit (2026-09-27).  fn-srb-within-h-is-within-the-bound:
; the reachable witness (a history of H octets under the small preset: the
; hypothesis and the conclusion), and without the hypothesis (a history one
; octet past the derived bound, which H does not admit) the conclusion fails.
(assert! (fn-profile-replay-within-boundp *srt-small* (fn-bs-profile-max-history-octets *srt-small*)))
(assert! (fn-srb-replay-within-boundp *srt-small* (fn-bs-profile-max-history-octets *srt-small*)))
(assert! (not (fn-profile-replay-within-boundp *srt-small*
                                               (+ 1 (fn-srb-replay-input-bound *srt-small*)))))
(assert! (not (fn-srb-replay-within-boundp *srt-small*
                                           (+ 1 (fn-srb-replay-input-bound *srt-small*)))))
