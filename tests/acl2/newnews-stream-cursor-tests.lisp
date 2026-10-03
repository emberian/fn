(in-package "ACL2")
(include-book "../../books/newnews-stream-cursor")
(include-book "newnews-metadata-cursor-tests")

(defthm nnsct-line-wider-than-quantum
  (let* ((cur (fn-sl-start "..abc"))
         (first (fn-sl-step cur 2))
         (next (mv-nth 1 first))
         (last (fn-sl-step next 6)))
    (and (fn-sl-okp cur) (fn-sl-okp next)
         (fn-sl-shapedp cur) (fn-sl-shapedp next)
         (equal (len next) 3)
         (equal (fn-sl-step-cons-cells cur 2) 18)
         (equal (car first) '(46 46))
         (equal (fn-cur-at 0 next) "..abc")
         (equal (fn-cur-at 1 next) 1)
         (not (mv-nth 1 last))
         (equal (append (car first) (car last)) '(46 46 46 97 98 99 13 10))
         (equal (append (car first) (fn-sl-remaining next))
                (fn-sl-remaining cur)))))

(defthm nnsct-render-does-not-revisit-candidate
  (let* ((context (fn-cur-context *nnmt-cur*))
         (cur (fn-cur-make context
                           (fn-nnw-stream-render (fn-sl-start "<a@x>") nil) nil nil))
         (step (fn-nnw-stream-step cur 0 2 nil nil)))
    (and (fn-nnw-stream-okp cur)
         (fn-nnw-stream-outputp (fn-cur-progress cur))
         (equal (car step) '(60 97))
         (equal (mv-nth 2 step) 0)
         (equal (mv-nth 3 step) :output)
         (equal (fn-cur-context (mv-nth 1 step)) context)
         (equal (- (len (fn-nnw-stream-tail (fn-cur-progress cur)))
                   (len (fn-nnw-stream-tail (fn-cur-progress (mv-nth 1 step))))) 0)
         (fn-nnw-meta-livep (mv-nth 1 step))
         (equal (append (car step) (fn-nnw-stream-remaining (mv-nth 1 step) nil nil))
                (fn-nnw-stream-remaining cur nil nil)))))

(defthm nnsct-sparse-scan-retains-renderer
  (let* ((one (fn-nnw-stream-step *nnmt-cur* 1 1 nil nil))
         (two (fn-nnw-stream-step (mv-nth 1 one) 1 1 nil nil)))
    (and (not (car one)) (not (car two))
         (equal (mv-nth 2 one) 1) (equal (mv-nth 2 two) 1)
         (fn-nnw-stream-renderp (fn-cur-progress (mv-nth 1 two)))
         (equal (append (car one) (car two)
                        (fn-nnw-stream-remaining (mv-nth 1 two) nil nil))
                (fn-nnw-stream-remaining *nnmt-cur* nil nil)))))

(defthm nnsct-literal-candidate-progress
  (let* ((progress (fn-cur-progress *nnmt-cur*))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (not (fn-nnw-stream-outputp progress))
         (consp (fn-nnw-tail progress))
         (not (car (fn-nnw-stream-one progress 1 nil nil)))
         (equal (len (fn-nnw-stream-tail next))
                (1- (len (fn-nnw-tail progress))))
         (<= (- (len (fn-nnw-stream-tail progress))
                (len (fn-nnw-stream-tail next))) 1))))

(defconst *nnsct-patterns* (fn-wildmat-result-value
                          (fn-wildmat-parse (fn-nntp-string-octets "fn.*"))))
(defconst *nnsct-select-progress*
  (fn-nnw-stream-select
   (fn-nnm-start *nnsct-patterns* '("fn.test") *nnmt-a*)
   (fn-nnw-stream-scan-cursor
    (fn-nnw-group-source *nnsct-patterns* '("fn.test")) 0 (list *nnmt-a*) 7 t)))

(defthm nnsct-literal-selector-progress
  (let ((next (mv-nth 1 (fn-nnw-stream-one *nnsct-select-progress* 1 nil nil))))
    (and (fn-nnw-stream-selectp *nnsct-select-progress*)
         (fn-nnm-statep (fn-cur-at 1 *nnsct-select-progress*))
         (posp (fn-nnm-group-remaining (fn-cur-at 1 *nnsct-select-progress*)))
         (fn-nnw-stream-progress-okp *nnsct-select-progress*)
         (fn-nnw-stream-selectp next)
         (< (fn-nnm-group-remaining (fn-cur-at 1 next))
            (fn-nnm-group-remaining (fn-cur-at 1 *nnsct-select-progress*)))
         (equal (fn-nnw-stream-tail next) (fn-nnw-stream-tail *nnsct-select-progress*)))))

; Removing positive remaining: an empty but valid selector settles. It
; cannot supply a strict decrease below zero.
(defthm nnsct-selector-progress-needs-positive-remaining
  (let* ((progress (fn-nnw-stream-select
                    (fn-nnm-start *nnsct-patterns* nil *nnmt-a*)
                    (fn-cur-at 2 *nnsct-select-progress*)))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (fn-nnw-stream-selectp progress)
         (fn-nnm-statep (fn-cur-at 1 progress))
         (not (posp (fn-nnm-group-remaining (fn-cur-at 1 progress))))
         (not (< (if (fn-nnw-stream-selectp next)
                     (fn-nnm-group-remaining (fn-cur-at 1 next)) 0)
                 (fn-nnm-group-remaining (fn-cur-at 1 progress)))))))

; Phase distinction witness: starting a new configured candidate may
; introduce selection work, so ordinary article scanning is a different phase.
(defthm nnsct-selector-progress-needs-selection-phase
  (let* ((progress (fn-nnw-stream-scan-cursor
                    (fn-nnw-group-source *nnsct-patterns* '("fn.test"))
                    0 (list *nnmt-a*) 7 t))
         (next (mv-nth 1 (fn-nnw-stream-one progress 1 nil nil))))
    (and (not (fn-nnw-stream-selectp progress))
         (fn-nnw-stream-selectp next)
         (posp (fn-nnm-group-remaining (fn-cur-at 1 next))))))
