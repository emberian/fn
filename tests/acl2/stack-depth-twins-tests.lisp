; Teeth for the two constant-stack twins of large-article (2026-09-25):
; `fn-frame-split-acc' under `fn-frame-split' (books/frame-octets.lisp) and
; `fn-ag-append-exec' under `fn-ag-append' (books/acceptance-alloc.lisp).
;
; Both keystones are hypothesis-free equalities, so there is no hypothesis to
; drop.  What can be dropped is the accumulator's starting value: the general
; lemma behind each keystone carries ACC, and the keystone holds only at
; ACC = nil.  The counterexamples below show the statement fails at any other
; accumulator, and the witnesses run the executable path at a depth the old
; per-octet recursion could not reach inside the image's 64 MB control stack
; (it exhausted between 2 and 3 million frames: a 3 MiB record in
; `store inspect' and at owner recovery, and a 3 MiB ARTICLE reply).

(in-package "ACL2")
(include-book "../../books/frame-octets")
(include-book "../../books/acceptance-alloc")

; -----------------------------------------------------------------------------
; The splitter

; Small witnesses: an exact split, a short input, n = 0, a non-natural n.
(assert-event (equal (fn-frame-split 2 '(1 2 3)) '((1 2) 3)))
(assert-event (equal (fn-frame-split-acc 2 '(1 2 3) nil) '((1 2) 3)))
(assert-event (equal (fn-frame-split-acc 4 '(1 2 3) nil) nil))
(assert-event (equal (fn-frame-split-acc 0 '(1 2 3) nil) '(nil 1 2 3)))
; Off the guard (a negative count, an improper list) the two still agree:
; the keystone has no hypothesis.  Proved, not evaluated, since evaluation
; would check the guard.
(defthm fn-frame-test-split-acc-off-guard
  (and (equal (fn-frame-split-acc -1 '(1 2) nil)
              (fn-frame-split -1 '(1 2)))
       (equal (fn-frame-split-acc 1 '(1 . 2) nil)
              (fn-frame-split 1 '(1 . 2)))
       (equal (fn-frame-split-acc 2 '(1 . 2) nil) nil))
  :rule-classes nil)

; The accumulator matters: at ACC = (9) the twin answers ((9 5)), not ((5)).
(assert-event (not (equal (fn-frame-split-acc 1 '(5) '(9))
                          (fn-frame-split 1 '(5)))))

; Depth: three million octets split through the executable path.
(defconst *fn-frame-test-deep* (make-list 3000001 :initial-element 120))
(assert-event (equal (len (car (fn-frame-split 3000000 *fn-frame-test-deep*))) 3000000))
(assert-event (equal (cdr (fn-frame-split 3000000 *fn-frame-test-deep*)) '(120)))
(assert-event (equal (fn-frame-split 3000002 *fn-frame-test-deep*) nil))

; -----------------------------------------------------------------------------
; The append

(assert-event (equal (fn-ag-append '(1 2) '(3)) '(1 2 3)))
(assert-event (equal (fn-ag-append-exec nil '(3)) '(3)))
; A non-list tail is dropped, as `append' drops it.
(assert-event (equal (fn-ag-append-exec '(1 2 . 7) '(3)) '(1 2 3)))
(defthm fn-ag-test-append-exec-improper
  (equal (fn-ag-append-exec '(1 2 . 7) '(3)) (append '(1 2 . 7) '(3)))
  :rule-classes nil)
(assert-event (equal (fn-ag-append-exec 7 8) 8))

; The accumulator matters: onto (9), the reversal carries 9 in front.
(assert-event (not (equal (revappend (fn-ag-rev-onto '(1 2) '(9)) '(3))
                          (append '(1 2) '(3)))))

; Depth: three million elements appended through the executable path.
(assert-event (equal (len (fn-ag-append *fn-frame-test-deep* '(1 2))) 3000003))
(assert-event (equal (nth 3000001 (fn-ag-append *fn-frame-test-deep* '(1 2))) 1))
